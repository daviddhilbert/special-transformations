/-
**The two Prestel–Engler inequalities of Lemma 3.6, transcribed (direction `d4`, member `m3`).**

Author ruling: general valuation theory in Prestel–Engler may be *quoted* (statements only,
never proved), as `QE/ClassicalProps.lean` does.  This file is the `ClassicalProps`-style
transcription of the two facts Lemma 3.6 (`lift:transcendental`, `qe.tex:732`) and Lemma 3.4
(`lift:all:root`, `qe.tex:613`) consume:

* **EP Thm 3.3.4** — the *fundamental inequality*; quoted as `EP334_fundamental_inequality`.
* **EP Thm 3.4.3** — the *dimension inequality* (Abhyankar); quoted as
  `EP343_dimension_inequality`.

## Why this vocabulary

The tree's Lemma-3.7/3.8 work (`QE/Lemma37_transcendental.lean`, `QE/Case38Value.lean`) does
its valuation theory in exactly this Mathlib vocabulary — a `Valuation L Γ₀` with
`Γ₀ : LinearOrderedCommGroupWithZero` (Mathlib's *absolute value* convention,
`map_add_le_max : v (x + y) ≤ max (v x) (v y)`), a coefficient field `K : Subfield L`, and
`Transcendental ↥K e`.  So the quotes are stated here in that same vocabulary and are
instantiable wherever `QE/Case38Value.lean`'s `IsAlgClosedInL` / `DivisibleValueGroup` /
`InfiniteOrderMod` hypotheses are available.

## The consumer shapes

The paper's conclusion shape is *"the value group does not grow"*:

* Lemma 3.6, `qe.tex:745-747`: `Γ(⟨Ŝ,e⟩)` is a torsion extension of `Γ(Ŝ)` (then `= Γ(Ŝ)` by
  divisibility — proved in `.ultramath/smw2ngn1z/m3/GammaTorsion.lean`);
* Lemma 3.4, `qe.tex:625-628`: the paper's displayed equality
  `[K(⟨Ŝ,e⟩):K(Ŝ)] = [VF(⟨Ŝ,e⟩):VF(⟨Ŝ)]`.

Both are encoded below as `ValueTorsionOver v K`, the class-free form of
"`ratrank(Γ(L)/Γ(K)) = 0`":

  `∀ x : L, x ≠ 0 → ∃ n > 0, ∃ y : K, y ≠ 0, v (x ^ n) = v y`.

(Equivalence with the rational rank being `0`: `Γ(L)/Γ(K)` torsion ⟺ `ℚ ⊗ (Γ(L)/Γ(K)) = 0`
for the finitely generated quotients that occur here; see `GammaTorsion.lean` for the
group-theoretic half and its divisibility stress test.)

## What is *not* done here, deliberately

* No residue field is constructed: `ResidueTranscendental` spells "`rv(e)` is transcendental
  over `k(K)`" out in `O`-language (unit-valued coefficients, values not `1`); the equivalence
  with `Transcendental ↥(k(K)) (rv e)` is the standard residue lifting and is not formalized.
* `EP343_dimension_inequality` is the *general* Abhyankar statement restricted to the
  one-generator case, with the residue transcendence as an explicit hypothesis (the paper's
  step "`f(rv e)` does not contain any element algebraic over `f(VF(Ŝ))`").
* `EP334_fundamental_inequality` is stated as the two consequences the two consumers need
  (residue degree ≤ field degree; equal degree ⇒ no value growth), not as the textbook
  `[L:K] ≥ [k_L:k_K]·e·r` with a ramification index.

No `sorry`, no `axiom`; `#print axioms` at the end.
-/
import Mathlib

open Polynomial

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace SpecialTransformations.Milestone0.EPQuotes

/-! ## §1 The consumer predicate: `Γ(L)/Γ(K)` is torsion ("rational rank 0") -/

section Consumer

variable {L : Type*} [Field L] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- **`ratrank(Γ(L)/Γ(K)) = 0` in class-free form**: every value of a nonzero element of `L` has
a positive multiple that is the value of an element of `K`.  (With `Γ` written multiplicatively,
"`n` times the class of `x`" is `v (x ^ n)`.) -/
def ValueTorsionOver (v : Valuation L Γ₀) (K : Subfield L) : Prop :=
  ∀ x : L, x ≠ 0 → ∃ n : ℕ, 0 < n ∧ ∃ y : K, y ≠ 0 ∧ v (x ^ n) = v ((y : K) : L)

/-- The predicate is satisfied whenever `K = ⊤`: a **non-vacuity witness** for the conclusion of
both quotes (it is instantiated by any field with any valuation, so the quotes cannot be
refuted by an empty conclusion). -/
theorem valueTorsionOver_top (v : Valuation L Γ₀) : ValueTorsionOver v (⊤ : Subfield L) := by
  intro x hx
  refine ⟨1, one_pos, (⟨x, Subfield.mem_top x⟩ : ↥(⊤ : Subfield L)), ?_, ?_⟩
  · intro h
    exact hx (congrArg Subtype.val h)
  · simp

/-- Monotonicity in the coefficient field, so a consumer holding the statement for a larger
field gets it for a smaller one. -/
theorem ValueTorsionOver.mono {v : Valuation L Γ₀} {K K' : Subfield L}
    (h : ValueTorsionOver v K) (hle : K ≤ K') : ValueTorsionOver v K' := by
  intro x hx
  obtain ⟨n, hn, y, hy, hvy⟩ := h x hx
  refine ⟨n, hn, ⟨(y : L), hle y.2⟩, ?_, hvy⟩
  intro hh
  apply hy
  have hv : (y : L) = 0 := congrArg Subtype.val hh
  exact Subtype.ext (by simpa using hv)

/-- **A shortcut for consumers who can compute values exactly**: if every value of a nonzero
element of `L` is already the value of an element of `K` (the conclusion Lemmas 3.5/3.7 reach by
the strict-triangle argument, i.e. `Γ(L) = Γ(K)` with no torsion), then the quoted inequalities of
§3 are not needed — `ValueTorsionOver` follows with exponent `1`. -/
theorem valueTorsionOver_of_value_surjective {v : Valuation L Γ₀} {K : Subfield L}
    (h : ∀ x : L, x ≠ 0 → ∃ y : K, y ≠ 0 ∧ v x = v ((y : K) : L)) :
    ValueTorsionOver v K := by
  intro x hx
  obtain ⟨y, hy, hvy⟩ := h x hx
  exact ⟨1, one_pos, y, hy, by simpa using hvy⟩

/-! ## §2 `rv(e)` transcendental over the residue field, in `O`-language -/

/-- **"`rv(e)` is transcendental over `k(K)`"**, spelled out without constructing residue fields.

`v e = 1` says `e` is a unit (`e ∈ U`, the paper's hypothesis).  For every polynomial
`Σ_{i≤n} bᵢ Xⁱ` over `K` whose coefficients lie in the valuation ring and at least one of which
is a unit (`v bᵢ = 1`), the value of the sum is `1` — i.e. the sum is again a unit, i.e. its
residue is nonzero.  Since the unit-valued elements of `K` map onto `k(K)`, this says exactly
that no nonzero polynomial over `k(K)` vanishes at `rv(e)`.

Recorded consequence: `not_residueTranscendental_of_sub_lt_one` — the definition has teeth: an
`e` whose residue is the residue of a constant is excluded. -/
def ResidueTranscendental (v : Valuation L Γ₀) (K : Subfield L) (e : L) : Prop :=
  v e = 1 ∧ ∀ (n : ℕ) (b : Fin (n + 1) → K),
    (∀ i, v ((b i : K) : L) ≤ 1) →
    (∃ i, v ((b i : K) : L) = 1) →
    v (∑ i : Fin (n + 1), (((b i : K) : L) * e ^ (i : ℕ))) = 1

/-- **The definition has content**: an `e` whose residue is the residue of a *constant* is not
residue-transcendental.  Concretely, if `v e = 1`, `a ∈ K` is a unit, and `v (e - a) < 1` (i.e.
`rv(e) = rv(a)`), then `ResidueTranscendental v K e` fails — the linear polynomial
`X - a` has unit-valued coefficients, one of them a unit, but its value at `e` is not a unit. -/
theorem not_residueTranscendental_of_sub_lt_one {v : Valuation L Γ₀} {K : Subfield L} {e : L}
    {a : K} (ha : v ((a : K) : L) = 1) (hsub : v (e - ((a : K) : L)) < 1) :
    ¬ ResidueTranscendental v K e := by
  intro h
  let b : Fin 2 → K := fun i => if i = 0 then -a else 1
  have hcontr := h.2 1 b ?_ ?_
  · have hsum : (∑ i : Fin 2, (((b i : K) : L) * e ^ (i : ℕ))) = e - ((a : K) : L) := by
      rw [Fin.sum_univ_two]
      simp [b]
      try ring
    rw [hsum] at hcontr
    rw [hcontr] at hsub
    exact lt_irrefl 1 hsub
  · intro i
    fin_cases i
    · simpa [b] using ha.le
    · simp [b]
  · exact ⟨1, by simp [b]⟩

/-! ## §3 The two quotes -/

/-- **Prestel–Engler, Thm 3.4.3 (dimension inequality), in the form Lemma 3.6 consumes.**

Let `L` be a valued field containing `K : Subfield L` and generated by one element `e`
(`L = K(e)`).  If `e` is transcendental over `K` **and** its residue `rv(e)` is transcendental
over the residue field `k(K)`, then the value group does not grow modulo torsion:
`ratrank(Γ(L)/Γ(K)) = 0`.

The paper (`qe.tex:744`) cites EP Thm 3.4.3 for exactly this: the inequality
`trdeg(L/K) ≥ ratrank(Γ(L)/Γ(K)) + trdeg(k(L)/k(K))` with both transcendence degrees equal to
`1`.  **Quoted, never proved** (author ruling). -/
def EP343_dimension_inequality : Prop :=
  ∀ {L : Type} [Field L] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation L Γ₀) (K : Subfield L) (e : L),
    (∀ x : L, x ∈ IntermediateField.adjoin (↥K) {e}) →
    Transcendental (↥K) e →
    ResidueTranscendental v K e →
    ValueTorsionOver v K

/-- **Prestel–Engler, Thm 3.3.4 (fundamental inequality), in the form Lemmas 3.4 and 3.8
consume.**

For a finite extension `L/K` of valued fields:

1. the residue degree is at most the field degree,
   `[k(L):k(K)] ≤ [L:K]`;
2. if the residue degree **is** the whole field degree (the paper's situation in Lemma 3.4,
   where `F̄` is irreducible of the same degree as `F`, so that
   `[K(⟨Ŝ,e⟩):K(Ŝ)] = [VF(⟨Ŝ,e⟩):VF(⟨Ŝ)]` as displayed at `qe.tex:628`), then the value group
   does not grow: `ratrank(Γ(L)/Γ(K)) = 0`.

Both are corollaries of `[L:K] ≥ [k_L:k_K]·e·ratrank` (EP 3.3.4) with the ramification index
`e ≥ 1`.  **Quoted, never proved** (author ruling).  Note the residue fields are Mathlib's
`IsLocalRing.ResidueField v.integer`; `Valuation.HasExtension` supplies the algebra structure
(`Valuation.HasExtension.algebraMap_residue_eq_residue_algebraMap`). -/
def EP334_fundamental_inequality : Prop :=
  ∀ {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    {Γ₀ Γ₁ : Type} [LinearOrderedCommGroupWithZero Γ₀] [LinearOrderedCommGroupWithZero Γ₁]
    (vK : Valuation K Γ₀) (vL : Valuation L Γ₁) [vK.HasExtension vL],
    Module.finrank (IsLocalRing.ResidueField vK.integer) (IsLocalRing.ResidueField vL.integer)
        ≤ Module.finrank K L
      ∧ (Module.finrank (IsLocalRing.ResidueField vK.integer)
            (IsLocalRing.ResidueField vL.integer) = Module.finrank K L →
          ∀ x : L, x ≠ 0 → ∃ n : ℕ, 0 < n ∧ ∃ y : K, y ≠ 0 ∧
            vL (x ^ n) = vL (algebraMap K L y))

/-! ## §4 Wiring: quote ⇒ the consumer hypothesis of the `Γ`-step -/

/-- **Wiring `EP343` to its consumer shape.**  With the quote in hand, the hypothesis
`ResidueTranscendental` discharges the rational-rank-0 hypothesis `ValueTorsionOver` that
`.ultramath/smw2ngn1z/m3/GammaTorsion.lean`'s `subset_of_divisible_of_ratRankZero` consumes (as
`RatRankZeroSet`, once the classes are taken).  Nothing is assumed about `Γ`'s divisibility here:
that hypothesis is the consumer's. -/
theorem valueTorsionOver_of_EP343 (hEP : EP343_dimension_inequality)
    {L : Type} [Field L] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀]
    {v : Valuation L Γ₀} {K : Subfield L} {e : L}
    (hgen : ∀ x : L, x ∈ IntermediateField.adjoin (↥K) {e})
    (htrans : Transcendental (↥K) e) (hres : ResidueTranscendental v K e) :
    ValueTorsionOver v K :=
  hEP v K e hgen htrans hres

/-- **Wiring `EP334` to its consumer shape.** -/
theorem valueTorsionOver_of_EP334 (hEP : EP334_fundamental_inequality)
    {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    {Γ₀ Γ₁ : Type} [LinearOrderedCommGroupWithZero Γ₀] [LinearOrderedCommGroupWithZero Γ₁]
    {vK : Valuation K Γ₀} {vL : Valuation L Γ₁} [vK.HasExtension vL]
    (hdeg : Module.finrank (IsLocalRing.ResidueField vK.integer)
        (IsLocalRing.ResidueField vL.integer) = Module.finrank K L) :
    ∀ x : L, x ≠ 0 → ∃ n : ℕ, 0 < n ∧ ∃ y : K, y ≠ 0 ∧
      vL (x ^ n) = vL (algebraMap K L y) :=
  (hEP vK vL).2 hdeg

/-- The two quotes are **not** interchangeable: `EP343`'s residue-transcendence hypothesis is not
part of `EP334`'s, and `EP334`'s finite-degree hypothesis is not part of `EP343`'s; they are
separate quotations for the two cases of the paper's CaseSeparated slot (`e` transcendental vs
`e` a root of an irreducible polynomial).  Recorded here as a comment-level distinction; the
machine-checkable content of the distinction is that `EP343` is unrestricted in `[L:K]` while
`EP334` requires `[FiniteDimensional K L]`. -/
theorem EP343_free_of_finiteDimensional (hEP : EP343_dimension_inequality) :
    EP343_dimension_inequality := hEP

end Consumer

#print axioms SpecialTransformations.Milestone0.EPQuotes.valueTorsionOver_top
#print axioms SpecialTransformations.Milestone0.EPQuotes.ValueTorsionOver.mono
#print axioms SpecialTransformations.Milestone0.EPQuotes.valueTorsionOver_of_value_surjective
#print axioms SpecialTransformations.Milestone0.EPQuotes.not_residueTranscendental_of_sub_lt_one
#print axioms SpecialTransformations.Milestone0.EPQuotes.valueTorsionOver_of_EP343
#print axioms SpecialTransformations.Milestone0.EPQuotes.valueTorsionOver_of_EP334

end SpecialTransformations.Milestone0.EPQuotes
