# F* verification for Chainflip arithmetic models.
# Requires: fstar.exe on PATH (F* v2026.07.24 or compatible) with bundled Z3.

FSTAR ?= fstar.exe
SRCS  := Chainflip.Threshold.fst Chainflip.Amounts.fst

.PHONY: all verify clean

all: verify

verify: $(SRCS)
	@for f in $(SRCS); do \
	  echo "==> verifying $$f"; \
	  $(FSTAR) $$f || exit 1; \
	done
	@echo "All F* modules verified."

clean:
	rm -f *.checked *.hints
