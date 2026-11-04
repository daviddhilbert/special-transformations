/-
**Mathlib feasibility inventory for the two Prestel–Engler inequalities (direction `d4`, m3).**

What this file is: a *compiling* inventory of every Mathlib 4.33.1 declaration that the two
inequalities of Lemma 3.6 / Lemma 3.4 touch, plus machine-checked instances of the ones the
statements in `EPQuotes.lean` need.  Its `#check` output is pasted into `LEDGER.md`; the file
itself is a check that the inventory is real (each `#check` is elaborated, not quoted from
memory).

## Result of the inventory

* The *vocabulary* exists and is complete enough to state both inequalities:
  `Valuation`, `Valuation.HasExtension`, `Valuation.integer` (`= 𝒪`), `IsLocalRing.ResidueField`
  (`= k`), `MonoidWithZeroHom.ValueGroup₀` (`= Γ ∪ {0}`), `Transcendental`, `IntermediateField.adjoin`,
  `Module.finrank`, `Module.rank`, `HenselianLocalRing`.
* The *content* does not exist: Mathlib has **no** Abhyankar/dimension inequality, **no**
  fundamental inequality, **no** rational rank, **no** residue degree, **no** ramification index
  for extensions of valued fields.  Greps (`grep -rli` over `Mathlib/`):
  `Abhyankar` → nothing; `rational rank` → nothing; `dimension inequality` → nothing;
  `residue degree` → nothing; `Module.rank` inside `Mathlib/RingTheory/Valuation/` → nothing;
  `Ostrowski` → only Ostrowski's theorem on absolute values of `ℚ`
  (`NumberTheory/Ostrowski.lean`) and Gelfand–Mazur, not Ostrowski's lemma on value extensions;
  `ramification` → only Dedekind-domain ideal ramification, not valuation-theoretic indices.
  Hence both inequalities must stay **quoted** (author ruling) — they are not re-derivable here.
* What *is* usable and is used by `EPQuotes.lean`: the residue field of an extension is an
  algebra over the base's residue field (`Valuation.HasExtension.instAlgebra_...` /
  `algebraMap_residue_eq_residue_algebraMap`), so a residue degree `Module.finrank k_K k_L` is
  statable; and `Valuation.isIntegral_iff_v_le_one` / `Valuation.isIntegrallyClosed` give the
  `𝒪`-side facts.
-/
import Mathlib

open Polynomial

set_option autoImplicit false

/-! ## §1 The valuation vocabulary -/

#check @Valuation
#check @Valuation.map_add
#check @Valuation.Integers
#check @Valuation.map_mul
#check @Valuation.integer
#check @Valuation.valuationSubring
#check @Valuation.integer.integers
#check @Valuation.mem_integer_iff
#check @Valuation.Integers.isIntegral_iff_v_le_one
#check @Valuation.Integers.isIntegrallyClosed
#check @Valuation.HasExtension
#check @Valuation.HasExtension.val_map_le_iff
#check @Valuation.HasExtension.val_map_eq_one_iff
#check @Valuation.HasExtension.algebraMap_mem_valuationSubring
#check @Valuation.HasExtension.instIsLocalHomValuationInteger
#check @Valuation.HasExtension.algebraMap_residue_eq_residue_algebraMap
#check @Valuation.restrict
#check @Valuation.IsNontrivial
#check @Valuation.RankOne

/-! ## §2 Residue fields and value groups -/

#check @IsLocalRing.ResidueField
#check @IsLocalRing.residue
#check @IsLocalRing.ResidueField.map
#check @MonoidWithZeroHom.ValueGroup₀
#check @MonoidWithZeroHom.valueGroup
#check @MonoidWithZeroHom.ValueGroup₀.embedding

/-! ## §3 The field-theoretic side: transcendence, degrees, henselianity -/

#check @Transcendental
#check @IntermediateField.adjoin
#check @IntermediateField.mem_adjoin_simple_iff
#check @Module.finrank
#check @Module.rank
#check @FiniteDimensional
#check @HenselianLocalRing
#check @IsAlgClosed.lift

/-! ## §4 Machine-checked availability of the two things `EPQuotes.lean` states -/

section Availability

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  {Γ₀ Γ₁ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [LinearOrderedCommGroupWithZero Γ₁]
  (vK : Valuation K Γ₀) (vL : Valuation L Γ₁) [vK.HasExtension vL]

/-- **EP334's residue degree is statable**: the residue field of `L` is an algebra over the
residue field of `K`, so `Module.finrank (ResidueField vK.integer) (ResidueField vL.integer)`
elaborates.  This is the only Mathlib ingredient `EP334_fundamental_inequality` needs beyond
`Module.finrank`. -/
example : Algebra (IsLocalRing.ResidueField vK.integer)
    (IsLocalRing.ResidueField vL.integer) := inferInstance

/-- The residue map used is the canonical one (Mathlib's `HasExtension` supplies it). -/
example (x : vK.integer) :
    (algebraMap (IsLocalRing.ResidueField vK.integer) (IsLocalRing.ResidueField vL.integer))
        (IsLocalRing.residue vK.integer x)
      = IsLocalRing.residue vL.integer (algebraMap vK.integer vL.integer x) :=
  Valuation.HasExtension.algebraMap_residue_eq_residue_algebraMap vK vL x

/-- **EP343's hypotheses are statable**: `Transcendental ↥K e` with `K : Subfield L` is the
vocabulary the tree's Lemma-3.7/3.8 files already use
(`QE/Lemma37_transcendental.lean`, `QE/Case38Value.lean`), so `EPQuotes.lean`'s quotes instantiate
wherever those files' hypotheses are available. -/
example {e : L} (h : Transcendental (↥(⊤ : Subfield L)) e) :
    ¬ IsAlgebraic (↥(⊤ : Subfield L)) e := h

end Availability

/-! ## §5 What is *not* in Mathlib (the gap list, machine-checked as far as it can be)

The following are *absent*; each was searched for by name and by concept, and none of the
statements below has a Mathlib proof to import (see `LEDGER.md` for the grep commands and their
output):

* the fundamental inequality `[L:K] ≥ [k_L:k_K]·e·ratrank(Γ_L/Γ_K)` (EP Thm 3.3.4);
* the dimension/Abyankar inequality `trdeg(L/K) ≥ ratrank(Γ_L/Γ_K) + trdeg(k_L/k_K)`
  (EP Thm 3.4.3);
* rational rank, residue degree, ramification index of a valued-field extension;
* "the residue field of an algebraic extension is algebraic", "the value group of an algebraic
  extension is torsion over the base" (EP 3.2.x) — these are the two facts behind the paper's
  "clearly `e` is transcendental over `VF(Ŝ)`".

Consequence for the project: Lemma 3.6's transcendental input and Lemma 3.4's inequality must
enter `CaseSeparated` as **named quoted hypotheses** (`EPQuotes.EP343_dimension_inequality`,
`EPQuotes.EP334_fundamental_inequality`), exactly as the author ruling prescribes; nothing in
Mathlib can discharge them.
-/
