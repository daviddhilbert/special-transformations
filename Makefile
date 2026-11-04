# Lean 4 + Mathlib project. `make` builds the library; `make check FILE=...`
# elaborates a single file against the built library.

.PHONY: all build check sorry milestone0 milestones accepted qe enc clean

all: build

build:
	lake build

# Elaborate a single file with the project's lean path, e.g.
# make check FILE=SpecialTransformations/Basic.lean
check:
	@test -n '$(FILE)' || { echo 'usage: make check FILE=SpecialTransformations/Basic.lean' >&2; exit 2; }
	lake env lean '$(FILE)'

# Fail if a source still contains a whole-word sorry or admit.
sorry:
	@if grep -rnwE --include='*.lean' 'sorry|admit' $(SOURCES); then \
		echo 'error: sorry/admit found (see above)' >&2; exit 1; \
	else echo 'no sorry/admit'; fi

# `Milestone0/Saturation.lean` and most of `QE/` import `Enc`, a compiled
# `Milestone0/Encoding.lean`; it is built here so that the targets below run with the
# project as it actually is.  (`import Enc` stops working the moment Lean is called
# without a search path that contains the olean, which is how these targets silently
# stopped running.)
ENCDIR := .scratch2/sec3

$(ENCDIR)/Enc.olean: Milestone0/Encoding.lean
	@mkdir -p $(ENCDIR)
	@cp Milestone0/Encoding.lean $(ENCDIR)/Enc.lean
	@cd $(ENCDIR) && lean -o Enc.olean Enc.lean

enc: $(ENCDIR)/Enc.olean

# Milestone 0 artifacts are standalone files, not part of the Lake library, so they are
# elaborated one by one.
milestone0: enc
	@for f in Milestone0/*.lean; do echo "== $$f"; \
		LEAN_PATH=$(CURDIR)/$(ENCDIR):$$LEAN_PATH lean "$$f" || exit 1; done

# Like `milestone0`, with the error/sorry counts the milestone check quotes.
milestones: enc
	@for f in Milestone0/*.lean Milestone0/accepted/*.lean QE/*.lean; do \
		out=$$(LEAN_PATH=$(CURDIR)/$(ENCDIR):$$LEAN_PATH lean "$$f" 2>&1); st=$$?; \
		e=$$(printf '%s' "$$out" | grep -c error); \
		s=$$(printf '%s' "$$out" | grep -c 'uses .sorry'); \
		printf '%-46s exit=%s errors=%s sorries=%s\n' "$$f" "$$st" "$$e" "$$s"; \
	done

# The accepted model-building artifacts are standalone snapshots (`import Mathlib` only).
accepted:
	@for f in Milestone0/accepted/*.lean; do echo "== $$f"; lean "$$f" || exit 1; done

# Quantifier-elimination artifacts are standalone snapshots as well (they need `Enc`).
qe: enc
	@for f in QE/*.lean; do echo "== $$f"; \
		LEAN_PATH=$(CURDIR)/$(ENCDIR):$$LEAN_PATH lean "$$f" || exit 1; done

clean:
	lake clean
	rm -rf .scratch

SOURCES := SpecialTransformations SpecialTransformations.lean
