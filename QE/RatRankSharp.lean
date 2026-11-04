/-
Copyright: none.  Ultramath swarm smw2ngn1z, member m2 (direction d3).

# Sharpness of the value-group step of Lemma 3.6: both hypotheses are necessary

`RatRank.lean` proves (for `H ≤ K ≤ G`, `G` an ordered commutative group)

  `H` divisible + `RatRankZero H K` (`K/H` torsion) ⟹ `K = H`.

In the application `G = Γ(M)` for `M ⊨ ACVF`, and `Γ(M)` is moreover **divisible**
(`QE/GammaDiv.lean`, `gamma_divisible`).  The two examples here are the stress tests:

* §1 — in `(ℚ,+)`, which *is* a divisible ordered abelian group of the same abstract shape as
  `Γ(M)`, the subgroup `ℤ` is not divisible, has `RatRankZero ℤ ⊤`, and `⊤ ≠ ℤ`.  So the
  conclusion genuinely fails if the divisibility hypothesis is dropped, even inside a divisible
  group: `divisibility_hypothesis_necessary`.  In fact the root closure of `ℤ` is all of `ℚ`
  (`divHullAdd_intAddSubgroup_eq_top`), i.e. the failure is as large as it can be.
* §2 — in `(ℚ × ℚ,+)` the subgroup `ℚ × {0}` *is* divisible but is not root-closed, so
  `RatRankZero (ℚ × {0}) ⊤` fails and again `⊤ ≠ ℚ × {0}`: divisibility alone never forces
  `K = H`, the rational-rank hypothesis is needed: `rational_rank_hypothesis_necessary`.

Both examples are additive value groups of honest ordered abelian groups, so they refute the
tempting strengthenings of the paper's step *as group theory*; they do not by themselves exhibit
an `ACVF` model (that is direction d2's audit).
-/
import RatRank

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Ultramath.M2RR

/-! ### A computation rule for `ℕ`-multiples in `ℚ` -/

theorem nsmul_rat_eq (n : ℕ) (q : ℚ) : n • q = (n : ℚ) * q := by
  induction n with
  | zero => simp
  | succ k ih => rw [succ_nsmul, ih]; push_cast; ring

/-! ## §1 `ℤ ⊆ ℚ`: divisibility cannot be dropped -/

/-- `ℤ` as an additive subgroup of `ℚ`. -/
def intAddSubgroup : AddSubgroup ℚ := (Int.castAddHom ℚ).range

theorem mem_intAddSubgroup_iff {q : ℚ} : q ∈ intAddSubgroup ↔ ∃ k : ℤ, (k : ℚ) = q :=
  AddMonoidHom.mem_range

theorem intAddSubgroup_ne_top : intAddSubgroup ≠ ⊤ := by
  intro h
  have h' : (1 / 2 : ℚ) ∈ intAddSubgroup := by rw [h]; exact trivial
  obtain ⟨k, hk⟩ := mem_intAddSubgroup_iff.mp h'
  have h2 : ((2 * k : ℤ) : ℚ) = 1 := by
    push_cast
    rw [hk]
    norm_num
  have h3 : 2 * k = 1 := Int.cast_injective h2
  omega

/-- `ℤ` is **not** divisible: `1` has no square root in `ℤ`. -/
theorem not_divisibleAddSubgroup_intAddSubgroup : ¬ DivisibleAddSubgroup intAddSubgroup := by
  intro hdiv
  obtain ⟨y, hy, hy2⟩ :=
    hdiv 1 (mem_intAddSubgroup_iff.mpr ⟨1, by norm_num⟩) 2 (by norm_num)
  obtain ⟨k, hk⟩ := mem_intAddSubgroup_iff.mp hy
  rw [← hk, nsmul_rat_eq] at hy2
  have h2 : ((2 * k : ℤ) : ℚ) = 1 := by
    push_cast
    exact hy2
  have h3 : 2 * k = 1 := Int.cast_injective h2
  omega

/-- **Every rational has a positive integer multiple in `ℤ`**: the rational rank of `ℤ` inside
`ℚ` is `1`, its root closure is everything. -/
theorem rat_den_smul (q : ℚ) : q.den • q = (q.num : ℚ) := by
  have hq : ((q.den : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr q.den_nz
  rw [nsmul_rat_eq, mul_comm]
  conv_lhs => enter [1]; rw [← Rat.num_div_den q]
  exact div_mul_cancel₀ (G₀ := ℚ) _ hq

theorem ratRankZeroAdd_intAddSubgroup_top : RatRankZeroAdd intAddSubgroup ⊤ := by
  intro q _
  exact ⟨q.den, q.den_pos, mem_intAddSubgroup_iff.mpr ⟨q.num, (rat_den_smul q).symm⟩⟩

/-- The root closure of `ℤ` in `ℚ` is `ℚ` itself. -/
theorem divHullAdd_intAddSubgroup_eq_top : divHullAdd intAddSubgroup = ⊤ := by
  refine le_antisymm le_top ?_
  rw [← ratRankZeroAdd_iff_le_divHullAdd]
  exact ratRankZeroAdd_intAddSubgroup_top

/-- **Sharpness 1: the divisibility hypothesis cannot be dropped.**  In the divisible ordered
group `(ℚ,+)` — the abstract shape of `Γ(M)` — there is a proper subgroup `H` with
`RatRankZero H ⊤` for which the conclusion `⊤ = H` of the paper's step fails. -/
theorem divisibility_hypothesis_necessary :
    ∃ H : AddSubgroup ℚ, RatRankZeroAdd H ⊤ ∧ ¬ DivisibleAddSubgroup H ∧ H ≠ ⊤ :=
  ⟨intAddSubgroup, ratRankZeroAdd_intAddSubgroup_top, not_divisibleAddSubgroup_intAddSubgroup,
    intAddSubgroup_ne_top⟩

/-! ## §2 `ℚ × {0} ⊆ ℚ × ℚ`: the rational-rank hypothesis cannot be dropped -/

/-- **Sharpness 2.**  In `(ℚ × ℚ,+)` the subgroup `ℚ × {0}` is divisible but not root-closed:
`(0,1)` has no nonzero multiple in it, so `RatRankZero (ℚ × {0}) ⊤` fails.  Divisibility of `H`
alone therefore never forces `K = H`. -/
theorem rational_rank_hypothesis_necessary :
    ∃ H : AddSubgroup (ℚ × ℚ), DivisibleAddSubgroup H ∧ ¬ RatRankZeroAdd H ⊤ ∧ H ≠ ⊤ := by
  refine ⟨AddSubgroup.prod ⊤ ⊥, ?_, ?_, ?_⟩
  · rintro ⟨a, b⟩ ⟨-, hb⟩ n hn
    simp only [AddSubgroup.mem_bot] at hb
    subst hb
    have hn0 : ((n : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    refine ⟨⟨((n : ℚ))⁻¹ * a, 0⟩, ⟨trivial, by simp⟩, ?_⟩
    ext
    · show n • ((n : ℚ)⁻¹ * a) = a
      rw [nsmul_rat_eq, ← mul_assoc, mul_inv_cancel₀ hn0, one_mul]
    · show n • (0 : ℚ) = 0
      rw [nsmul_rat_eq]; ring
  · intro h
    obtain ⟨n, hn, hmem⟩ := h ((0, 1) : ℚ × ℚ) trivial
    have h1 : (n : ℚ) ∈ (⊥ : AddSubgroup ℚ) := by
      have h2 : (n • ((0, 1) : ℚ × ℚ)).2 ∈ (⊥ : AddSubgroup ℚ) := hmem.2
      have h3 : (n • ((0, 1) : ℚ × ℚ)).2 = (n : ℚ) := by
        have h4 : n • ((0, 1) : ℚ × ℚ) = (0, (n : ℚ)) := by
          ext
          · show n • (0 : ℚ) = 0
            rw [nsmul_rat_eq]; ring
          · show n • (1 : ℚ) = (n : ℚ)
            rw [nsmul_rat_eq, mul_one]
        rw [h4]
      rwa [h3] at h2
    simp only [AddSubgroup.mem_bot] at h1
    have hn0 : n = 0 := by exact_mod_cast h1
    omega
  · intro h
    have hmem : ((0, 1) : ℚ × ℚ) ∈ AddSubgroup.prod (⊤ : AddSubgroup ℚ) ⊥ := by
      rw [h]
      exact trivial
    have h1 : (1 : ℚ) ∈ (⊥ : AddSubgroup ℚ) := hmem.2
    simp only [AddSubgroup.mem_bot] at h1
    exact one_ne_zero h1

/-! ## §3 The converse needs roots in `G`: sharpness for `divHull_eq_self_iff` -/

/-- **Sharpness 3.**  `divHull_eq_self_iff` needs its hypothesis that `n`-th roots exist in the
ambient group `G`.  In `(ℤ,+)` there are no roots, the root closure of `⊤` is `⊤`
(`divHullAdd_top`), and yet `⊤` is not divisible: `2 • y = 1` has no solution.  So "root closure
collapses" alone does not imply divisibility — in `Γ(M)`, which *is* divisible, the two are
equivalent. -/
theorem rootClosure_collapse_not_divisible :
    divHullAdd (⊤ : AddSubgroup ℤ) = ⊤ ∧ ¬ DivisibleAddSubgroup (⊤ : AddSubgroup ℤ) := by
  refine ⟨divHullAdd_top, ?_⟩
  intro hdiv
  obtain ⟨y, -, hy2⟩ := hdiv 1 trivial 2 (by norm_num)
  rw [two_nsmul] at hy2
  omega

/-! ## §4 Non-vacuity at the group level

`(ℚ,+)` is a divisible ordered abelian group of the abstract shape of `Γ(M)`, is not trivial, and
the paper's step fires there for `H = ⊤` — so §1–§3 of `RatRank.lean` have non-vacuous content.
(The `ACVF`-level ⊤-witness is direction d2's audit.) -/

theorem divisibleAddSubgroup_top_rat : DivisibleAddSubgroup (⊤ : AddSubgroup ℚ) := by
  intro x _ n hn
  have hn0 : ((n : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  refine ⟨((n : ℚ))⁻¹ * x, trivial, ?_⟩
  rw [nsmul_rat_eq, ← mul_assoc, mul_inv_cancel₀ hn0, one_mul]

/-- The paper's step fires at `H = ⊤` in `ℚ`: a divisible value group cannot grow. -/
theorem paper_step_fires_rat {K : AddSubgroup ℚ} (hK : (⊤ : AddSubgroup ℚ) ≤ K)
    (hrank : RatRankZeroAdd ⊤ K) : K = ⊤ :=
  eq_of_divisible_of_ratRankZeroAdd hK divisibleAddSubgroup_top_rat hrank

end Ultramath.M2RR

/-! ## Axiom check -/

#print axioms Ultramath.M2RR.nsmul_rat_eq
#print axioms Ultramath.M2RR.intAddSubgroup_ne_top
#print axioms Ultramath.M2RR.not_divisibleAddSubgroup_intAddSubgroup
#print axioms Ultramath.M2RR.ratRankZeroAdd_intAddSubgroup_top
#print axioms Ultramath.M2RR.divHullAdd_intAddSubgroup_eq_top
#print axioms Ultramath.M2RR.divisibility_hypothesis_necessary
#print axioms Ultramath.M2RR.rational_rank_hypothesis_necessary
#print axioms Ultramath.M2RR.paper_step_fires_rat
#print axioms Ultramath.M2RR.rootClosure_collapse_not_divisible
