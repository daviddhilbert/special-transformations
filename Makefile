# Lean 4 + Mathlib project. `make` builds the library; `make check FILE=...`
# elaborates a single file without going through Lake.

.PHONY: all build check sorry clean

all: build

build:
	lake build

# Fast single-file check using the ambient LEAN_PATH (Mathlib is prebuilt at
# /opt/mathlib), e.g. make check FILE=Project/Basic.lean
check:
	@test -n '$(FILE)' || { echo 'usage: make check FILE=Project/Basic.lean' >&2; exit 2; }
	lean '$(FILE)'

# Fail if a source still contains a whole-word sorry or admit.
sorry:
	@if grep -rnwE --include='*.lean' 'sorry|admit' $(SOURCES); then \
		echo 'error: sorry/admit found (see above)' >&2; exit 1; \
	else echo 'no sorry/admit'; fi

clean:
	lake clean
	rm -rf .scratch

SOURCES := SpecialTransformations SpecialTransformations.lean Project Project.lean
