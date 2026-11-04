/-
# M7 / d6: the two Engler–Prestel quotations, transcribed for the tree's two consumers

`refs/qe.tex` cites two theorems of Engler–Prestel, *Valued Fields* (Springer 2005):

* **EP Thm 3.3.4 — the fundamental inequality**, cited at Lemma 3.4 (`lift:all:root`, qe.tex:620) as

    `[K(⟨Ŝ,e⟩):K(Ŝ)] = [VF(⟨Ŝ,e⟩):VF(⟨Ŝ,e⟩)]`   (in the paper `K` is the *residue* field);

* **EP Thm 3.4.3 — the dimension inequality** (Abhyankar), cited at Lemma 3.6
  (`lift:transcendental`, qe.tex:741) as "the rational rank of `Γ(⟨Ŝ,e⟩)/Γ(Ŝ)` is 0".

Verified against the book's statements as quoted in the secondary literature (Kuhlmann, *Elimination
of Ramification I*: `trdeg L|K ≥ rr vL/vK + trdeg Lv|Kv`; the PJM 267 (2014) paper quoting
"The Fundamental Inequality, Theorem 3.3.4" and "the Dimension Inequality, Theorem 3.4.3").

## The two corrections this file records

1. **EP 3.3.4 is an inequality, and gives `f ≤ [L:K]`, not the paper's equality.**  For an arbitrary
   finite extension `[L:K] ≥ e·f` (ramification index `e`, residue degree `f`), with `e, f ≥ 1`; the
   equality `f = [L:K]` is the *defectless and unramified* case.  What the paper actually needs at
   Lemma 3.4 is `f ≤ [L:K]` (that is `residueDegree_le_fieldDegree` below, the only corner of
   3.3.4 the tree consumes); the reverse inequality `n ≤ f` comes from the paper's own hypotheses
   (`F` monic over `O(Ŝ)` with `F̄` irreducible and `e` a unit), not from 3.3.4.

2. **EP 3.4.3 gives rational rank 0 *in that one-generator situation*, i.e. torsion of
   `Γ(⟨Ŝ,e⟩)/Γ(Ŝ)`; the passage to equality needs the divisibility of `Γ(Ŝ)`.**  That passage is
   pure group theory and is *proved* here (`gamma_collapse`); it is the only place the quote is used
   in Lemma 3.6, and `UnitTranscend.lean` shows the quote is not needed there at all when `e` is a
   unit with transcendental residue.

No `sorry`, no `axiom`, no `native_decide`.
-/
import Mathlib

set_option autoImplicit false

namespace M7

/-! ## 1. The group-theoretic passage `ratrank 0` + divisible ⇒ equality

This is the whole of Lemma 3.6's use of EP Thm 3.4.3 (`qe.tex:743`): a value-group extension of
rational rank `0` (torsion quotient) over a divisible value group is trivial. -/

/-- **Torsion over a divisible ordered abelian group is trivial.**  If every element of `H` has a
positive multiple in the image of a divisible `G`, then `G` maps onto `H`.  Applied with `G = Γ(Ŝ)`
divisible and `H = Γ(⟨Ŝ,e⟩)` of rational rank `0`, this is `Γ(⟨Ŝ,e⟩) = Γ(Ŝ)`. -/
theorem gamma_collapse {G H : Type*} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    [AddCommGroup H] [LinearOrder H] [IsOrderedAddMonoid H]
    (f : G →+ H) [DivisibleBy G ℕ]
    (htors : ∀ h : H, ∃ n : ℕ, 0 < n ∧ ∃ g : G, n • h = f g) :
    ∀ h : H, ∃ g : G, f g = h := by
  intro h
  obtain ⟨n, hn, g, hg⟩ := htors h
  have hn0 : n ≠ 0 := Nat.pos_iff_ne_zero.mp hn
  obtain ⟨g', hg'⟩ := DivisibleBy.surjective_smul (A := G) (α := ℕ) hn0 g
  have hg'' : n • g' = g := hg'
  refine ⟨g', ?_⟩
  have h1 : n • f g' = n • h := by rw [← map_nsmul f, hg'', hg]
  have h2 : n • (f g' - h) = 0 := by rw [nsmul_sub, h1, sub_self]
  have h3 : f g' - h = 0 := by
    rcases lt_trichotomy (f g' - h) 0 with hlt | heq | hgt
    · have hp : n • (f g' - h) < 0 := nsmul_neg hlt hn0
      rw [h2] at hp
      exact absurd hp (lt_irrefl 0)
    · exact heq
    · have hp : 0 < n • (f g' - h) := (nsmul_pos_iff hn0).mpr hgt
      rw [h2] at hp
      exact absurd hp (lt_irrefl 0)
  exact sub_eq_zero.mp h3

/-! ## 2. The specialized quoted Props (the forms the consumers use)

Per the author ruling the general book statements are quoted at whatever level the consumers need;
each `Prop` below is one specialised face of the book theorem, with the book's general form recorded
in its docstring.  Both are hypotheses of the frozen target's pathway, never proved. -/

/-- **EP Thm 3.4.3 (dimension inequality), specialised to rational rank `0`.**

Book form (Abhyankar): for a valued field extension `(K,v) ⊆ (L,w)`,
`trdeg(L/K) ≥ trdeg(Lw/Kv) + rr(ΓL/ΓK)`, where `rr` is `dim_ℚ (ΓL/ΓK ⊗ ℤ ℚ)`.

Specialisation quoted here: in Lemma 3.6's one-generator situation (`L = ⟨Ŝ,e⟩`, `e` transcendental
over `VF(Ŝ)`, so `trdeg = 1` and `trdeg(VF(⟨Ŝ,e⟩)/VF(Ŝ)) = 1`), the inequality forces
`rr(Γ(⟨Ŝ,e⟩)/Γ(Ŝ)) = 0`; for ordered abelian groups that is exactly *torsion of the quotient*:
every `γ` of the big value group has a positive multiple in the image of the small one. -/
def RatRankZero {G H : Type*} [AddCommGroup G] [AddCommGroup H] (f : G →+ H) : Prop :=
  ∀ h : H, ∃ n : ℕ, 0 < n ∧ ∃ g : G, n • h = f g

/-- **The consumer-shaped wiring of EP 3.4.3**: the quote `RatRankZero` plus divisibility of the
base value group gives the paper's conclusion `Γ(⟨Ŝ,e⟩) = Γ(Ŝ)` (`qe.tex:743`). -/
theorem gamma_eq_of_ratRank_zero {G H : Type*} [AddCommGroup G] [LinearOrder G]
    [IsOrderedAddMonoid G] [AddCommGroup H] [LinearOrder H] [IsOrderedAddMonoid H]
    (f : G →+ H) [DivisibleBy G ℕ] (h : RatRankZero f) :
    ∀ y : H, ∃ g : G, f g = y :=
  gamma_collapse f h

/-- **EP Thm 3.3.4 (fundamental inequality), the corner Lemma 3.4 consumes: residue degree ≤
field degree.**

Book form: for a finite extension of valued fields `(K,v) ⊆ (L,w)`, `[L:K] ≥ e·f`, where `e` is the
ramification index `(wLˣ : vKˣ)` and `f = [Lw : Kv]` the residue degree.  Taking `e ≥ 1` gives the
inequality below, which is the only consequence of 3.3.4 that the tree needs (Lemma 3.4's
`[K(⟨Ŝ,e⟩):K(Ŝ)] ≤ [VF(⟨Ŝ,e⟩):VF(⟨Ŝ,e⟩)]`, i.e. the residue-degree bound). -/
def ResidueDegreeLeFieldDegree : Prop :=
  ∀ {K L : Type} [Field K] [Field L] [Algebra K L] [Module.Finite K L]
    {Γ₀ Γ₁ : Type} [LinearOrderedCommGroupWithZero Γ₀] [LinearOrderedCommGroupWithZero Γ₁]
    (vK : Valuation K Γ₀) (vL : Valuation L Γ₁) [vK.HasExtension vL],
    Module.finrank (IsLocalRing.ResidueField vK.valuationSubring)
        (IsLocalRing.ResidueField vL.valuationSubring) ≤ Module.finrank K L

end M7

/-! ## 3. Audit -/

#print axioms M7.gamma_collapse
#print axioms M7.gamma_eq_of_ratRank_zero
