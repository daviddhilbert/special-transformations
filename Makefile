# Lean 4 + Mathlib project. `make` builds the library; `make check FILE=...`
# elaborates a single file against the built library.

.PHONY: all build check sorry milestone0 accepted qe clean

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

# Milestone 0 artifacts are standalone files (`import Mathlib` only), not part of
# the Lake library, so they are elaborated one by one.
milestone0:
	@for f in Milestone0/*.lean; do echo "== $$f"; lean "$$f" || exit 1; done

# The accepted model-building artifacts are standalone snapshots (`import Mathlib` only).
accepted:
	@for f in Milestone0/accepted/*.lean; do echo "== $$f"; lean "$$f" || exit 1; done

# Quantifier-elimination artifacts are standalone snapshots as well.
qe:
	@for f in QE/*.lean; do echo "== $$f"; lean "$$f" || exit 1; done

clean:
	lake clean
	rm -rf .scratch

SOURCES := SpecialTransformations SpecialTransformations.lean
