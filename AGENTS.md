# Working agreement with Yimu (read this first)

These are standing instructions from the author of the paper. They apply to **every** session
that works in this repository. Follow them without being asked again.

## 1. Do not stop until told to stop

> "You really should write it down somewhere that you don't stop working until I tell you so."

* Keep working continuously. Do **not** end a turn to report progress, ask whether to continue,
  or summarise where things stand. End a turn only when
  * the requested theorem is actually proved and landed, **or**
  * you are genuinely stuck on the mathematics after trying several approaches, **or**
  * a decision is needed that is only his to make (e.g. changing the frozen encoding).
* When you must pause for one of those reasons, say which one it is in one line, then continue
  with whatever is next.
* Chain sessions: set a `conversation_remind` for yourself before ending a turn, so the next turn
  picks up the same thread, with the concrete next step in the reminder text.
* "if you are stuck on something, try at least three more approaches before you stop and consult
  with me."
* "I hate to come back to check whether you have stopped every 15 minutes."

## 2. Honesty about state

* A file is green only if `lean FILE.lean` exits 0. Count **all** errors: `grep -c "error"`,
  never `grep "error("` — Lean's parse errors and "unsolved goals" carry no error code and slip
  through that pattern. This exact mistake produced a false "all 47 files compile" claim once.
* Never report a theorem as proved unless it compiles with no `sorry` and
  `#print axioms ⊆ {propext, Classical.choice, Quot.sound}`.
* When a claim in a header, README or plan is falsified (e.g. a file that "compiles" but does
  not), fix the claim in the same commit that establishes the truth. `QE-PLAN.md`,
  `QE/README.md` and file headers have all been wrong before.

## 3. The mathematics

* The target is Theorem 2.3 of *Special transformations in algebraically closed valued fields*
  (APAL 2010): quantifier elimination for `ACVF` in the language `L_RV`, as frozen in
  `Milestone0/Encoding.lean` (`theorem_2_3_quantifier_elimination`).
* `RV = rv(VF^×) ∪ {0}` — the paper's `0` and `∞` are one element, `rv(0)`, the absorbing one.
  Axiom (2) forces this (`RV^× = RV ∖ {∞}` must be a group). Settled; do not re-litigate.
* `pK` (`t ≠ ∞`) is `RV ∖ {0}` = the multiplicative group, **not** the residue field. The
  residue field is `pInK` (which contains the absorbing element).
* Note the two order conventions, which are **reversed** and cost a wrong turn once already:
  Mathlib's `Valuation` is the absolute-value convention (`v (x+y) ≤ max (v x) (v y)`,
  `v 0 = 0` minimal) and `IsValPred` is stated in it; the frozen encoding's `vv = vrv ∘ rv` is
  the paper's value-group order (`vv (x+y) ≥ min`, `O = rv⁻¹(RV^{≥ 1})`). So
  `v x ≤ v y` in `L_val` is `vv y ≤ vv x` in `L_RV`.

## 4. Housekeeping

* Every `.lean` file here is a **standalone snapshot**: `import Mathlib` only, private copies of
  the definitions it needs. Two files' copies of a language are *different* types, so any
  cross-file theorem needs a file that carries one copy of each.
* The main assembly file is `QE/Assembly_val.lean`; `QE-PLAN.md` records the state and the plan.
  Keep both current in the commit that changes the state.
* Scratch work goes in `.scratch/` (or `.scratch2/`), never committed, never in `/tmp`.
* Do not run `make` in the background while editing files.
