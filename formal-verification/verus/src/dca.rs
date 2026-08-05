//! Verified port of the swapping pallet's DCA chunk accounting.
//!
//! Source: state-chain/pallets/cf-swapping/src/lib.rs
//!   - `DcaState`                         (~line 419)
//!   - `DcaState::new`                    (~line 429)
//!   - `DcaState::calculate_next_chunk`   (~line 443)
//!   - `DcaState::record_scheduled_chunk` (~line 457)
//!   - `DcaState::record_chunk_completion`(~line 471)
//!
//! Port deviations (documented; see also ../conformance/):
//!   - `scheduled_chunks: BTreeSet<SwapId>` is represented as a
//!     duplicate-free `Vec<u64>` (Verus has no verified BTreeSet); insertion
//!     order is irrelevant to the verified properties.
//!   - Ghost state (`initial_input`, `chunk_inputs`, `executed_input`) tracks
//!     where every unit of input is, enabling the conservation proof. Ghost
//!     fields are proof-only and erased at compile time.
//!
//! Verified properties:
//!   1. Conservation (`wf`): at all times
//!      `initial_input == remaining_input + sum(scheduled chunk inputs)
//!                        + executed_input`.
//!      No unit of deposited input can be dropped or double-spent by the
//!      chunking logic.
//!   2. `calculate_next_chunk` never exceeds `remaining_input_amount`, and
//!      when exactly one chunk remains it returns the entire remainder: the
//!      floor division `remaining / remaining_chunks` strands no dust.
//!   3. When all chunks have been scheduled (`remaining_chunks == 0`),
//!      `remaining_input_amount == 0` - mechanizing the `debug_assert!` in
//!      `process_swap_outcome` (~line 2568).
//!   4. Panic-freedom of the ported operations under the stated
//!      preconditions. The `accumulated_output_amount +=` in the original
//!      can overflow if total output exceeds u128::MAX (unreachable for real
//!      asset amounts); the port makes that an explicit precondition.

use vstd::prelude::*;

verus! {

/// Sum of the ghost per-chunk input amounts of the currently scheduled ids.
pub open spec fn scheduled_input_sum(ids: Seq<u64>, amounts: Map<u64, nat>) -> nat
    decreases ids.len(),
{
    if ids.len() == 0 {
        0
    } else {
        amounts[ids[0]] + scheduled_input_sum(ids.skip(1), amounts)
    }
}

/// Port of `DcaState` with ghost accounting.
pub struct DcaState {
    /// `scheduled_chunks`, as a duplicate-free vector of swap ids.
    pub scheduled_chunks: Vec<u64>,
    pub remaining_input_amount: u128,
    pub remaining_chunks: u32,
    pub chunk_interval: u32,
    pub accumulated_output_amount: u128,
    /// Ghost: the total input this DCA state was created with.
    pub ghost initial_input: nat,
    /// Ghost: input amount of each scheduled chunk, by swap id.
    pub ghost chunk_inputs: Map<u64, nat>,
    /// Ghost: total input consumed by completed chunks.
    pub ghost executed_input: nat,
}

impl DcaState {
    /// Conservation invariant + structural well-formedness.
    pub open spec fn wf(&self) -> bool {
        &&& self.scheduled_chunks@.no_duplicates()
        &&& (forall|i: int|
            0 <= i < self.scheduled_chunks@.len()
                ==> self.chunk_inputs.dom().contains(#[trigger] self.scheduled_chunks@[i]))
        &&& self.initial_input == self.remaining_input_amount
            + scheduled_input_sum(self.scheduled_chunks@, self.chunk_inputs)
            + self.executed_input
        // Once all chunks are allocated, all input is allocated
        // (the debug_assert! in process_swap_outcome).
        &&& (self.remaining_chunks == 0 ==> self.remaining_input_amount == 0)
    }

    /// Port of `DcaState::new` (dca_params normalised to `number_of_chunks
    /// >= 1` by init_swap_request; `chunk_interval` defaulting is irrelevant
    /// to the verified properties).
    pub fn new(input_amount: u128, number_of_chunks: u32, chunk_interval: u32) -> (r: Self)
        requires
            number_of_chunks >= 1,
        ensures
            r.wf(),
            r.remaining_input_amount == input_amount,
            r.remaining_chunks == number_of_chunks,
            r.accumulated_output_amount == 0,
            r.scheduled_chunks@.len() == 0,
            r.initial_input == input_amount,
            r.executed_input == 0,
    {
        DcaState {
            scheduled_chunks: Vec::new(),
            remaining_input_amount: input_amount,
            remaining_chunks: number_of_chunks,
            chunk_interval,
            accumulated_output_amount: 0,
            initial_input: input_amount as nat,
            chunk_inputs: Map::empty(),
            executed_input: 0,
        }
    }

    /// Port of `DcaState::calculate_next_chunk`.
    ///
    /// Note the checked_div(..).unwrap_or(0): the divisor is only zero when
    /// `remaining_chunks == 0`, in which case the original returns None
    /// before dividing.
    pub fn calculate_next_chunk(&self) -> (r: Option<u128>)
        ensures
            r is Some <==> self.remaining_chunks > 0,
            r is Some ==> {
                let amount = r->Some_0;
                // Floor division: the chunk never exceeds what remains...
                &&& amount == self.remaining_input_amount as int / self.remaining_chunks as int
                &&& amount <= self.remaining_input_amount
                // ...and the final chunk takes the entire remainder (no dust).
                &&& (self.remaining_chunks == 1 ==> amount == self.remaining_input_amount)
            },
    {
        if self.remaining_chunks > 0 {
            let chunk = self.remaining_input_amount / (self.remaining_chunks as u128);
            proof {
                vstd::arithmetic::div_mod::lemma_fundamental_div_mod(
                    self.remaining_input_amount as int,
                    self.remaining_chunks as int,
                );
                vstd::arithmetic::div_mod::lemma_div_is_ordered_by_denominator(
                    self.remaining_input_amount as int,
                    1,
                    self.remaining_chunks as int,
                );
            }
            Some(chunk)
        } else {
            None
        }
    }

    /// Port of `DcaState::record_scheduled_chunk`.
    ///
    /// Preconditions mirror the only call sites (init_swap_request and
    /// process_swap_outcome): the amount is what `calculate_next_chunk`
    /// returned, and the swap id is freshly allocated (SwapIdCounter is
    /// strictly increasing, so it cannot collide with a scheduled chunk).
    /// Under these preconditions the `saturating_reduce` calls in the
    /// original cannot saturate, so exact arithmetic is proven equivalent.
    pub fn record_scheduled_chunk(
        &mut self,
        scheduled_chunk_swap_id: u64,
        scheduled_chunk_amount: u128,
    )
        requires
            old(self).wf(),
            old(self).remaining_chunks >= 1,
            scheduled_chunk_amount
                == old(self).remaining_input_amount as int / old(self).remaining_chunks as int,
            !old(self).scheduled_chunks@.contains(scheduled_chunk_swap_id),
        ensures
            final(self).wf(),
            final(self).remaining_chunks == old(self).remaining_chunks - 1,
            final(self).remaining_input_amount
                == old(self).remaining_input_amount - scheduled_chunk_amount,
            final(self).scheduled_chunks@
                == old(self).scheduled_chunks@.push(scheduled_chunk_swap_id),
            final(self).chunk_inputs
                == old(self).chunk_inputs.insert(
                    scheduled_chunk_swap_id,
                    scheduled_chunk_amount as nat,
                ),
            final(self).executed_input == old(self).executed_input,
            final(self).initial_input == old(self).initial_input,
            final(self).accumulated_output_amount == old(self).accumulated_output_amount,
    {
        proof {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(
                self.remaining_input_amount as int,
                self.remaining_chunks as int,
            );
            vstd::arithmetic::div_mod::lemma_div_is_ordered_by_denominator(
                self.remaining_input_amount as int,
                1,
                self.remaining_chunks as int,
            );
        }
        // Add the new chunk to the scheduled swaps.
        self.scheduled_chunks.push(scheduled_chunk_swap_id);
        proof {
            self.chunk_inputs = self.chunk_inputs.insert(
                scheduled_chunk_swap_id,
                scheduled_chunk_amount as nat,
            );
            lemma_sum_push(
                old(self).scheduled_chunks@,
                old(self).chunk_inputs,
                scheduled_chunk_swap_id,
                scheduled_chunk_amount as nat,
            );
        }
        // Update the remaining values (saturating_reduce cannot saturate here).
        self.remaining_chunks = self.remaining_chunks - 1;
        self.remaining_input_amount = self.remaining_input_amount - scheduled_chunk_amount;
    }

    /// Port of `DcaState::record_chunk_completion`.
    ///
    /// The precondition that the completed swap id is a scheduled chunk makes
    /// the `log_or_panic!` branch of the original unreachable; the swap
    /// execution protocol (modelled in ../tla/SwapDcaFok.tla) only completes
    /// swaps it previously scheduled.
    pub fn record_chunk_completion(
        &mut self,
        completed_chunk_swap_id: u64,
        completed_chunk_output_amount: u128,
    )
        requires
            old(self).wf(),
            old(self).scheduled_chunks@.contains(completed_chunk_swap_id),
            // The += in the original assumes no output overflow (unreachable
            // for real asset amounts, but not enforced by the code).
            old(self).accumulated_output_amount + completed_chunk_output_amount <= u128::MAX,
        ensures
            final(self).wf(),
            final(self).accumulated_output_amount
                == old(self).accumulated_output_amount + completed_chunk_output_amount,
            final(self).scheduled_chunks@.to_multiset()
                == old(self).scheduled_chunks@.to_multiset().remove(completed_chunk_swap_id),
            final(self).executed_input
                == old(self).executed_input + old(self).chunk_inputs[completed_chunk_swap_id],
            final(self).remaining_input_amount == old(self).remaining_input_amount,
            final(self).remaining_chunks == old(self).remaining_chunks,
            final(self).initial_input == old(self).initial_input,
    {
        // BTreeSet::remove, as position lookup + removal on the Vec-set.
        let mut i: usize = 0;
        let n = self.scheduled_chunks.len();
        while i < n
            invariant
                0 <= i <= n,
                n == self.scheduled_chunks.len(),
                forall|j: int| 0 <= j < i ==> self.scheduled_chunks@[j] != completed_chunk_swap_id,
                self.scheduled_chunks@.contains(completed_chunk_swap_id),
                *self == *old(self),
            decreases n - i,
        {
            if *self.scheduled_chunks.index(i) == completed_chunk_swap_id {
                break;
            }
            i = i + 1;
        }
        proof {
            assert(i < n && self.scheduled_chunks@[i as int] == completed_chunk_swap_id) by {
                if i == n {
                    let w = choose|w: int|
                        0 <= w < n && self.scheduled_chunks@[w] == completed_chunk_swap_id;
                    assert(self.scheduled_chunks@[w] != completed_chunk_swap_id);
                }
            }
        }
        self.scheduled_chunks.remove(i);
        proof {
            self.executed_input =
                self.executed_input + old(self).chunk_inputs[completed_chunk_swap_id];
            lemma_sum_remove(old(self).scheduled_chunks@, old(self).chunk_inputs, i as int);
            assert(old(self).scheduled_chunks@.remove(i as int).no_duplicates());
            assert(old(self).scheduled_chunks@.remove(i as int).to_multiset()
                == old(self).scheduled_chunks@.to_multiset().remove(completed_chunk_swap_id)) by {
                old(self).scheduled_chunks@.lemma_remove_to_multiset(i as int);
            }
        }
        self.accumulated_output_amount =
            self.accumulated_output_amount + completed_chunk_output_amount;
    }
}

/// Appending a fresh id adds its amount to the scheduled sum.
proof fn lemma_sum_push(ids: Seq<u64>, amounts: Map<u64, nat>, id: u64, amount: nat)
    ensures
        scheduled_input_sum(ids.push(id), amounts.insert(id, amount))
            == scheduled_input_sum(ids, amounts.insert(id, amount)) + amount,
        !ids.contains(id) ==> scheduled_input_sum(ids, amounts.insert(id, amount))
            == scheduled_input_sum(ids, amounts),
    decreases ids.len(),
{
    let amounts1 = amounts.insert(id, amount);
    if ids.len() == 0 {
        assert(ids.push(id) =~= seq![id]);
        assert(seq![id].skip(1) =~= Seq::<u64>::empty());
    } else {
        assert(ids.push(id).skip(1) =~= ids.skip(1).push(id));
        assert(ids.push(id)[0] == ids[0]);
        lemma_sum_push(ids.skip(1), amounts, id, amount);
        if !ids.contains(id) {
            assert(ids[0] != id);
            assert(!ids.skip(1).contains(id)) by {
                if ids.skip(1).contains(id) {
                    let w = choose|w: int|
                        0 <= w < ids.skip(1).len() && ids.skip(1)[w] == id;
                    assert(ids[w + 1] == id);
                }
            }
        }
    }
}

/// Removing index i subtracts that chunk's amount from the scheduled sum.
proof fn lemma_sum_remove(ids: Seq<u64>, amounts: Map<u64, nat>, i: int)
    requires
        0 <= i < ids.len(),
        forall|j: int| 0 <= j < ids.len() ==> amounts.dom().contains(#[trigger] ids[j]),
    ensures
        scheduled_input_sum(ids.remove(i), amounts) + amounts[ids[i]]
            == scheduled_input_sum(ids, amounts),
    decreases ids.len(),
{
    if i == 0 {
        assert(ids.remove(0) =~= ids.skip(1));
    } else {
        assert(ids.remove(i)[0] == ids[0]);
        assert(ids.remove(i).skip(1) =~= ids.skip(1).remove(i - 1));
        lemma_sum_remove(ids.skip(1), amounts, i - 1);
        assert(ids.skip(1)[i - 1] == ids[i]);
    }
}

} // verus!
