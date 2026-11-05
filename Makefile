.PHONY: all build check legacy-plan legacy-inventory check-moves clean

all: build

build:
	lake build

check:
	@test -n '$(FILE)' || { echo 'usage: make check FILE=Section3/YourModule.lean' >&2; exit 2; }
	lake env lean '$(FILE)'

legacy-plan:
	@test -n '$(FILE)' || { echo 'usage: make legacy-plan FILE=Section3/Sec3Count.lean' >&2; exit 2; }
	python3 Archive/inspect_legacy.py --plan '$(FILE)'

legacy-inventory:
	python3 Archive/inspect_legacy.py --inventory

check-moves:
	python3 Archive/inspect_legacy.py --check-moves

clean:
	lake clean
