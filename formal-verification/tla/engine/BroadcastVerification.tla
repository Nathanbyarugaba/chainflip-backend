----------------------- MODULE BroadcastVerification -----------------------
(***************************************************************************)
(* Model of verify_broadcasts (broadcast_verification.rs ~100-183).        *)
(*                                                                         *)
(* threshold = n / 2                                                       *)
(* A value is agreed for party i iff some value appears in > threshold of  *)
(* the verification messages for slot i.                                   *)
(*                                                                         *)
(* FINDING: when |submitters| ≤ threshold, Rust returns                    *)
(*   Err((empty set, InsufficientVerificationMessages))                    *)
(* i.e. blames nobody (TODO in source ~131).                               *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Parties   \* {p1,p2,p3}

Values == {"A","B"}
Payloads == Values \union {"None"}

VARIABLES
    submitters,   \* SUBSET Parties who sent verification messages
    \* For each (submitter, subject): claimed payload (or None)
    claim,        \* function (Parties \X Parties) -> Payloads
    outcome,      \* after Evaluate
    agreed,       \* Parties -> Payloads \union {"Unresolved"}
    reported

vars == <<submitters, claim, outcome, agreed, reported>>

n == Cardinality(Parties)
threshold == n \div 2

CountFor(subject, payload) ==
    Cardinality({s \in submitters : claim[<<s, subject>>] = payload})

MajorityOf(subject) ==
    IF \E v \in Payloads : CountFor(subject, v) > threshold
    THEN CHOOSE v \in Payloads : CountFor(subject, v) > threshold
    ELSE "Unresolved"

Init ==
    /\ submitters \in SUBSET Parties
    /\ claim \in [Parties \X Parties -> Payloads]
    /\ outcome = "Unset"
    /\ agreed = [p \in Parties |-> "Unresolved"]
    /\ reported = {}

Evaluate ==
    /\ outcome = "Unset"
    /\ IF Cardinality(submitters) <= threshold
       THEN /\ outcome' = "FailInsufficientVerif"
            /\ reported' = {}
            /\ UNCHANGED agreed
       ELSE
         LET maj == [p \in Parties |-> MajorityOf(p)]
             reps == {p \in Parties : maj[p] \in {"Unresolved", "None"}}
             insuff ==
                \E p \in Parties :
                   Cardinality({s \in submitters : claim[<<s, p>>] # "None"})
                     <= threshold
         IN IF reps = {}
            THEN /\ outcome' = "Ok"
                 /\ agreed' = maj
                 /\ reported' = {}
            ELSE /\ outcome' = IF insuff
                               THEN "FailInsufficientMsg"
                               ELSE "FailInconsistency"
                 /\ agreed' = maj
                 /\ reported' = reps
    /\ UNCHANGED <<submitters, claim>>

Next == Evaluate
Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ submitters \subseteq Parties
    /\ outcome \in {"Unset","Ok","FailInsufficientVerif",
                    "FailInsufficientMsg","FailInconsistency"}
    /\ reported \subseteq Parties

OkImpliesAllAgreed ==
    outcome = "Ok" => \A p \in Parties : agreed[p] \in Values

\* Documented Rust behaviour: insufficient verification messages ⇒ empty blame.
InsufficientVerifBlamesNobody ==
    outcome = "FailInsufficientVerif" => reported = {}

\* Honest-agreement safety: if every submitter consistently reports the same
\* non-None payload for every party, and |submitters| > threshold, outcome=Ok.
ConsistentQuorumSucceeds ==
    (/\ Cardinality(submitters) > threshold
     /\ \A s1, s2 \in submitters : \A p \in Parties :
            claim[<<s1, p>>] = claim[<<s2, p>>]
     /\ \A s \in submitters : \A p \in Parties : claim[<<s, p>>] \in Values
    ) => (outcome = "Unset" \/ outcome = "Ok")

\* Probe (EXPECTED TO FAIL): when verification fails for insufficient
\* messages, *someone* should be reportable. Rust returns {} instead.
BlameSomeoneOnInsufficientVerif ==
    ~(outcome = "FailInsufficientVerif" /\ submitters # {})

=============================================================================
