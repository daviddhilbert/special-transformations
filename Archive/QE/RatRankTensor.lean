/-
Copyright: none.  Ultramath swarm smw2ngn1z, member m2 (direction d3).

# `rational rank = 0` in the literature form: `ℚ ⊗ (K/H)` is trivial iff `K/H` is torsion

`RatRank.lean` formalises the paper's "the rational rank of `Γ(⟨Ŝ,e⟩)/Γ(Ŝ)` is 0" in the
elementary form `RatRankZero H K` — *every element of `K` has a positive power in `H`*, i.e.
`K/H` is a torsion group.  The literature (and Prestel–Engel, Thm 3.4.3) defines the rational
rank as

  `ratrank(K/H) = dim_ℚ (ℚ ⊗_ℤ (K/H))`,

so a quote of the inequality produces `(ℚ ⊗ (K/H)) = 0`, not torsion directly.  This file proves
the two are the same, so that a quoted rational-rank-0 statement can be fed to
`RatRank.eq_of_divisible_of_ratRankZero` without a gap:

* `rationalRank A := Module.rank ℚ (ℚ ⊗[ℤ] A)`;
* `subsingleton_tensor_iff_isTorsion : Subsingleton (ℚ ⊗[ℤ] A) ↔ Module.IsTorsion ℤ A`;
* `rationalRank_eq_zero_iff_torsion : rationalRank A = 0 ↔ Module.IsTorsion ℤ A`.

The proofs use Mathlib's localization-of-modules API: `ℚ ⊗[ℤ] A` is the localization of `A` at
the nonzero integers (`IsLocalization.tensorProduct_isLocalizedModule`,
`IsLocalizedModule.eq_zero_iff`, `IsLocalizedModule.mk'_surjective`) — i.e. exactly the filtered
colimit `A → A → A → …` along multiplication by `n`, whose kernel is the torsion subgroup.

* `ratRankZeroAdd_of_rationalRank_eq_zero` — **the consumer bridge**: `rationalRank (K ⧸ H) = 0`
  gives `RatRankZeroAdd H K`, i.e. a quotation of EP Thm 3.4.3 in the tensor form feeds
  `RatRank.eq_of_divisible_of_ratRankZeroAdd` directly.
-/
import RatRank

set_option autoImplicit false
set_option linter.unusedSectionVars false

open TensorProduct

namespace Ultramath.M2RR

/-- **Rational rank** of an abelian group: `dim_ℚ (ℚ ⊗_ℤ A)` (the paper's
`rational rank of Γ'/Γ = 0` when `A = Γ'/Γ`). -/
noncomputable def rationalRank (A : Type*) [AddCommGroup A] : Cardinal :=
  Module.rank ℚ (ℚ ⊗[ℤ] A)

/-- **The tensor product with `ℚ` is trivial iff the group is torsion.** -/
theorem subsingleton_tensor_iff_isTorsion (A : Type*) [AddCommGroup A] :
    Subsingleton (ℚ ⊗[ℤ] A) ↔ Module.IsTorsion ℤ A := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · -- a vanishing localization has torsion kernel
    intro x
    have h0 : (TensorProduct.mk ℤ ℚ A 1) x = 0 := Subsingleton.elim _ _
    obtain ⟨s, hs⟩ :=
      (IsLocalizedModule.eq_zero_iff (S := nonZeroDivisors ℤ) (f := (TensorProduct.mk ℤ ℚ A 1))).mp h0
    exact ⟨s, hs⟩
  · -- the localization of a torsion group is trivial
    have hzero : ∀ u : ℚ ⊗[ℤ] A, u = 0 := by
      intro u
      obtain ⟨⟨m, s⟩, rfl⟩ :=
        IsLocalizedModule.mk'_surjective (S := nonZeroDivisors ℤ) (f := (TensorProduct.mk ℤ ℚ A 1)) u
      change IsLocalizedModule.mk' ((TensorProduct.mk ℤ ℚ A 1)) m s = 0
      rw [IsLocalizedModule.mk'_eq_zero]
      obtain ⟨a, ha⟩ := h (x := m)
      exact (IsLocalizedModule.eq_zero_iff (S := nonZeroDivisors ℤ) (f := (TensorProduct.mk ℤ ℚ A 1))).mpr
        ⟨a, ha⟩
    exact ⟨fun u v => by rw [hzero u, hzero v]⟩

/-- **The rational rank vanishes iff the group is torsion**: the form in which the paper's
dimension inequality (EP Thm 3.4.3) delivers its conclusion. -/
theorem rationalRank_eq_zero_iff_torsion (A : Type*) [AddCommGroup A] :
    rationalRank A = 0 ↔ Module.IsTorsion ℤ A := by
  rw [rationalRank, rank_zero_iff]
  exact subsingleton_tensor_iff_isTorsion A

/-- The direction the paper's quote supplies: rational rank `0` ⟹ torsion. -/
theorem isTorsion_of_rationalRank_eq_zero (A : Type*) [AddCommGroup A]
    (h : rationalRank A = 0) : Module.IsTorsion ℤ A :=
  (rationalRank_eq_zero_iff_torsion A).mp h

/-- Torsion in the `Module.IsTorsion` sense gives the elementwise `ℕ`-multiple form used by
`RatRank.RatRankZero` for an additive subgroup: a quotient `K/H` of torsion therefore satisfies
`RatRankZeroAdd H K` (see `RatRank.lean`). -/
theorem exists_nsmul_mem_of_zsmul_mem {G : Type*} [AddCommGroup G] {H : AddSubgroup G} {x : G}
    {a : ℤ} (ha : a ≠ 0) (h : a • x ∈ H) : ∃ n : ℕ, 1 ≤ n ∧ n • x ∈ H := by
  have h' : (a.natAbs : ℤ) • x ∈ H := by
    rcases Int.natAbs_eq a with hn | hn
    · rwa [hn] at h
    · rw [hn, neg_smul] at h
      simpa using H.neg_mem h
  refine ⟨a.natAbs, ?_, ?_⟩
  · have : a.natAbs ≠ 0 := by
      rintro h0
      exact ha (by rw [Int.natAbs_eq_zero] at h0; exact h0)
    omega
  · rwa [Nat.cast_smul_eq_nsmul ℤ] at h'

/-- **The consumer bridge**: if the rational rank of `K/H` is `0` in the tensor sense, then
`RatRankZeroAdd H K` (every element of `K` has a positive multiple in `H`).  This is what turns a
quotation of EP Thm 3.4.3 (`rational rank of Γ(⟨Ŝ,e⟩)/Γ(Ŝ)` is `0`) into the hypothesis of
`RatRank.eq_of_divisible_of_ratRankZeroAdd`. -/
theorem ratRankZeroAdd_of_rationalRank_eq_zero {G : Type*} [AddCommGroup G] {H K : AddSubgroup G}
    (h : rationalRank (K ⧸ H.addSubgroupOf K) = 0) : RatRankZeroAdd H K := by
  intro x hx
  have htor : Module.IsTorsion ℤ (K ⧸ H.addSubgroupOf K) :=
    isTorsion_of_rationalRank_eq_zero _ h
  obtain ⟨a, ha⟩ := htor (x := (QuotientAddGroup.mk ⟨x, hx⟩ : K ⧸ H.addSubgroupOf K))
  have ha' : (a : ℤ) • (QuotientAddGroup.mk ⟨x, hx⟩ : K ⧸ H.addSubgroupOf K) = 0 := by
    simpa only [Submonoid.smul_def] using ha
  have hmem : ((a : ℤ) • (⟨x, hx⟩ : K)) ∈ H.addSubgroupOf K := by
    rw [← QuotientAddGroup.eq_zero_iff]
    rw [QuotientAddGroup.mk_zsmul, ha']
  have hxH : (a : ℤ) • x ∈ H := by
    have h1 := AddSubgroup.mem_addSubgroupOf.mp hmem
    rwa [AddSubgroup.coe_zsmul] at h1
  exact exists_nsmul_mem_of_zsmul_mem (nonZeroDivisors.ne_zero a.2) hxH

/-- **End to end in the paper's own vocabulary**: if `H` is divisible and the rational rank of
`K/H` is `0` (tensor form), then `K = H`.  This is Lemma 3.6's value-group step with the
dimension-inequality quote stated exactly as Prestel–Engel state it (rational rank, not torsion),
so a transcription of EP Thm 3.4.3 in the `ClassicalProps` style can be wired to it verbatim. -/
theorem eq_of_divisible_of_rationalRank_eq_zero {G : Type*} [AddCommGroup G] [LinearOrder G]
    [IsOrderedAddMonoid G] {H K : AddSubgroup G} (hHK : H ≤ K) (hdiv : DivisibleAddSubgroup H)
    (h : rationalRank (K ⧸ H.addSubgroupOf K) = 0) : K = H :=
  eq_of_divisible_of_ratRankZeroAdd hHK hdiv (ratRankZeroAdd_of_rationalRank_eq_zero h)

end Ultramath.M2RR

/-! ## Axiom check -/

#print axioms Ultramath.M2RR.subsingleton_tensor_iff_isTorsion
#print axioms Ultramath.M2RR.rationalRank_eq_zero_iff_torsion
#print axioms Ultramath.M2RR.isTorsion_of_rationalRank_eq_zero
#print axioms Ultramath.M2RR.exists_nsmul_mem_of_zsmul_mem
#print axioms Ultramath.M2RR.ratRankZeroAdd_of_rationalRank_eq_zero
#print axioms Ultramath.M2RR.eq_of_divisible_of_rationalRank_eq_zero
