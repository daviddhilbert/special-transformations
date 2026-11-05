 /-
Johnson §2.3 over a *subfield*: an independent formalisation of Lemmas 2.3.3 and 2.3.8.

This file is the snapshot of `QE/Johnson23_valuation.lean` (with its `IsValBall`, `cell`,
`mem_cell`, comparability and 2.3.4/2.3.6/2.3.7 material) followed by a second, independent
proof of the K ⊆ L half of §2.3 in a different framework from the one in
`QE/Johnson23_valuation.lean`: here the base is a `Subfield L` (and a valuation-preserving
`φ : K →+* L` with possibly *different* value groups Γ and Γ′, related only by
`vK x ≤ vK y ↔ vL (φ x) ≤ vL (φ y)`), which is the shape an `L_val`-embedding has.

Two independent proofs of 2.3.3 and 2.3.8 agreeing is stronger evidence than either alone, and
`exists_mem_image_of_isBoolCombOfBalls` (nonempty Boolean combination of K-balls contains a
point of the image of φ) is the form `OneECIn` needs.  From swarm `smw0c60wk` member m8,
compiled and axiom-checked by the reviewer; not edited.

Only import: Mathlib.
-/

import Mathlib

/-!
# The value group of an algebraically closed valued field (Johnson, Lemma 2.3.6, first half)

If `K` is algebraically closed and `v : Valuation K Γ₀` is nontrivially valued, then the
value group `vK` is divisible (every element has an `n`-th root), hence a dense linear order
without endpoints.
-/

namespace Johnson

open Polynomial

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- From a strict inequality of squares in a linearly ordered commutative monoid with zero. -/
theorem lt_of_mul_self_lt_mul_self {x y : Γ₀} (h : x * x < y * y) : x < y := by
  by_contra hle
  push Not at hle
  exact absurd h (not_lt.mpr (mul_le_mul' hle hle))

/-- **Divisibility of the value group.**  In an algebraically closed field every element has an
`n`-th root, so every value has an `n`-th root as well. -/
theorem exists_pow_val_eq [IsAlgClosed K] (v : Valuation K Γ₀) (a : K) {n : ℕ} (hn : 0 < n) :
    ∃ b : K, v b ^ n = v a := by
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq a hn
  exact ⟨b, by rw [← map_pow, hb]⟩

/-- **Density.**  Between two nonzero values there is a third one. -/
theorem exists_val_between [IsAlgClosed K] (v : Valuation K Γ₀) {a c : K} (ha : a ≠ 0)
    (hc : c ≠ 0) (h : v a < v c) : ∃ b : K, b ≠ 0 ∧ v a < v b ∧ v b < v c := by
  obtain ⟨b, hb⟩ := exists_pow_val_eq v (a * c) (n := 2) (by norm_num)
  have hb' : v b * v b = v a * v c := by rw [← pow_two, hb, map_mul]
  have ha0 : 0 < v a := pos_iff_ne_zero.mpr (v.ne_zero_iff.mpr ha)
  have hc0 : 0 < v c := pos_iff_ne_zero.mpr (v.ne_zero_iff.mpr hc)
  have hb0 : v b ≠ 0 := by
    intro h0
    have hne : v a * v c ≠ 0 :=
      mul_ne_zero (v.ne_zero_iff.mpr ha) (v.ne_zero_iff.mpr hc)
    apply hne
    rw [← hb', h0]
    simp
  refine ⟨b, v.ne_zero_iff.mp hb0, ?_, ?_⟩
  · exact lt_of_mul_self_lt_mul_self (by rw [hb']; exact mul_lt_mul_of_pos_left h ha0)
  · exact lt_of_mul_self_lt_mul_self (by rw [hb']; exact mul_lt_mul_of_pos_right h hc0)

/-- The value group has no greatest element. -/
theorem exists_val_lt_val (v : Valuation K Γ₀) (hnt : ∃ x : K, x ≠ 0 ∧ v x < 1) {a : K}
    (ha : a ≠ 0) : ∃ b : K, b ≠ 0 ∧ v a < v b := by
  obtain ⟨x, hx0, hx⟩ := hnt
  have hxpos : 0 < v x := pos_iff_ne_zero.mpr (v.ne_zero_iff.mpr hx0)
  have hinv : 0 < (v x)⁻¹ := pos_iff_ne_zero.mpr (inv_ne_zero (ne_of_gt hxpos))
  have hxv : 1 < (v x)⁻¹ := by
    have h : (v x)⁻¹ * v x < (v x)⁻¹ * 1 := mul_lt_mul_of_pos_left hx hinv
    rw [inv_mul_cancel₀ (ne_of_gt hxpos), mul_one] at h
    exact h
  have ha0 : 0 < v a := pos_iff_ne_zero.mpr (v.ne_zero_iff.mpr ha)
  refine ⟨a * x⁻¹, mul_ne_zero ha (inv_ne_zero hx0), ?_⟩
  rw [map_mul, Valuation.map_inv]
  simpa using mul_lt_mul_of_pos_left hxv ha0

/-- The value group has no least element. -/
theorem exists_val_lt_val' (v : Valuation K Γ₀) (hnt : ∃ x : K, x ≠ 0 ∧ v x < 1) {a : K}
    (ha : a ≠ 0) : ∃ b : K, b ≠ 0 ∧ v b < v a := by
  obtain ⟨x, hx0, hx⟩ := hnt
  have ha0 : 0 < v a := pos_iff_ne_zero.mpr (v.ne_zero_iff.mpr ha)
  refine ⟨a * x, mul_ne_zero ha hx0, ?_⟩
  rw [map_mul]
  simpa using mul_lt_mul_of_pos_left hx ha0

/-- **Johnson, Lemma 2.3.6 (first half).**  The value group of a nontrivially valued
algebraically closed field is a dense linear order without endpoints. -/
theorem valueGroup_dlo [IsAlgClosed K] (v : Valuation K Γ₀)
    (hnt : ∃ x : K, x ≠ 0 ∧ v x < 1) :
    (∀ a : K, a ≠ 0 → ∃ b : K, b ≠ 0 ∧ v a < v b) ∧
    (∀ a : K, a ≠ 0 → ∃ b : K, b ≠ 0 ∧ v b < v a) ∧
    (∀ a c : K, a ≠ 0 → c ≠ 0 → v a < v c → ∃ b : K, b ≠ 0 ∧ v a < v b ∧ v b < v c) :=
  ⟨fun _ ha => exists_val_lt_val v hnt ha,
   fun _ ha => exists_val_lt_val' v hnt ha,
   fun _ _ ha hc h => exists_val_between v ha hc h⟩





/-!
# The residue field of an algebraically closed valued field

Johnson, *Fun with Fields*, Lemma 2.3.6 (second half), in the strengthened form: the residue
field of an algebraically closed valued field is itself algebraically closed, hence infinite.

The proof is the root-product argument: lift a monic `q` over the residue field `𝓀 = O/m` to a
monic `f` over `O`; over the algebraically closed `K = Frac O`, `f` splits as `∏ (X - aᵢ)`, and
`v (f.coeff 0) = ∏ v aᵢ ≤ 1` forces some `v aᵢ ≤ 1`, i.e. some root lies in `O`, and it reduces
to a root of `q`.
-/



variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-! ## Two elementary lemmas -/

/-- A nonempty product of elements `> 1` in a linearly ordered commutative monoid with zero
is `> 1`. -/
theorem one_lt_multiset_prod {α : Type*} [LinearOrderedCommMonoidWithZero α] (m : Multiset α)
    (h : ∀ a ∈ m, 1 < a) (hm : m ≠ 0) : 1 < m.prod := by
  revert h hm
  refine Multiset.induction_on m ?_ ?_
  · intro _ hm; exact absurd rfl hm
  · intro a s ih h hs
    rw [Multiset.prod_cons]
    have ha : 1 < a := h a (Multiset.mem_cons_self a s)
    rcases eq_or_ne s 0 with rfl | hne
    · simpa using ha
    · have hs' : 1 < s.prod := ih (fun b hb => h b (Multiset.mem_cons_of_mem hb)) hne
      exact one_lt_mul_of_lt_of_le ha hs'.le

/-- A polynomial is monic as soon as its degree is at most `n` and its `n`-th coefficient
is `1`. -/
theorem monic_of_natDegree_le_of_coeff_eq_one {R : Type*} [Semiring R] [Nontrivial R] {p : R[X]}
    {n : ℕ}
    (h : p.natDegree ≤ n) (h1 : p.coeff n = 1) : p.Monic := by
  have hn : p.natDegree = n := by
    rcases lt_or_eq_of_le h with hlt | heq
    · exfalso
      rw [coeff_eq_zero_of_natDegree_lt hlt] at h1
      exact zero_ne_one h1
    · exact heq
  rw [Monic, leadingCoeff, hn]
  exact h1

/-! ## Lifting a monic polynomial along a surjective ring homomorphism -/

/-- Every monic polynomial over a quotient lifts to a monic polynomial. -/
theorem exists_monic_map_eq {R S : Type*} [CommRing R] [Nontrivial R] [CommRing S] (φ : R →+* S)
    (hφ : Function.Surjective φ) {q : S[X]} (hq : q.Monic) :
    ∃ f : R[X], f.Monic ∧ f.map φ = q := by
  classical
  choose s hs using hφ
  set s' : S → R := fun c => if c = 1 then 1 else s c with hs'
  have hs'1 : s' 1 = 1 := by simp [hs']
  have hs'spec : ∀ c, φ (s' c) = c := by
    intro c
    by_cases hc : c = 1
    · rw [hc, hs'1, map_one]
    · simp only [hs', if_neg hc]; exact hs c
  refine ⟨X ^ q.natDegree + ∑ i ∈ Finset.range q.natDegree, C (s' (q.coeff i)) * X ^ i,
    ?_, ?_⟩
  · refine monic_of_natDegree_le_of_coeff_eq_one (n := q.natDegree) ?_ ?_
    · refine le_trans (natDegree_add_le _ _) (max_le (le_of_eq (natDegree_X_pow _)) ?_)
      refine natDegree_sum_le_of_forall_le (s := Finset.range q.natDegree)
        (f := fun i => C (s' (q.coeff i)) * X ^ i) (n := q.natDegree) (fun i hi => ?_)
      rw [Finset.mem_range] at hi
      exact le_trans (natDegree_C_mul_X_pow_le _ _) (le_of_lt hi)
    · rw [coeff_add, coeff_X_pow_self, finsetSum_coeff]
      have hzero : ∀ i ∈ Finset.range q.natDegree,
          (C (s' (q.coeff i)) * X ^ i).coeff q.natDegree = 0 := by
        intro i hi
        rw [Finset.mem_range] at hi
        rw [coeff_C_mul, coeff_X_pow, if_neg (Ne.symm (ne_of_lt hi)), mul_zero]
      rw [Finset.sum_eq_zero hzero, add_zero]
  · rw [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sum]
    simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X, hs'spec]
    conv_rhs => rw [hq.as_sum]

/-! ## The root-product argument -/

/-- A monic polynomial of positive degree over a valuation ring of an algebraically closed
field has a root modulo the maximal ideal. -/
theorem exists_residue_root [IsAlgClosed K] (v : Valuation K Γ₀)
    {f : (↥v.valuationSubring)[X]} (hf : f.Monic) (hd : 1 ≤ f.natDegree) :
    ∃ x : IsLocalRing.ResidueField ↥v.valuationSubring,
      (f.map (IsLocalRing.residue ↥v.valuationSubring)).eval x = 0 := by
  classical
  set F : K[X] := f.map v.valuationSubring.subtype with hF
  have hFmonic : F.Monic := hf.map _
  have hFn : F.natDegree = f.natDegree := by rw [hF, Monic.natDegree_map hf]
  have hcard : F.roots.card = F.natDegree := ((IsAlgClosed.splits F).natDegree_eq_card_roots).symm
  have hroots_ne : F.roots ≠ 0 := by
    intro h0
    have hc : F.roots.card = 0 := by rw [h0]; simp
    rw [hcard, hFn] at hc
    omega
  -- `v` turns a product into a product of values
  have hkey : ∀ m : Multiset K, v m.prod = (m.map v).prod := by
    intro m
    induction m using Multiset.induction_on with
    | empty => simp
    | cons a s ih => simp [Multiset.prod_cons, map_mul, ih]
  -- the value of a root product
  have hval : (F.roots.map v).prod ≤ 1 := by
    have h1 : (F.roots.map v).prod = v (F.eval 0) := by
      rw [(IsAlgClosed.splits F).eval_eq_prod_roots_of_monic hFmonic, hkey]
      congr 1
      rw [Multiset.map_map]
      congr 1
      funext r
      simp
    rw [h1, ← coeff_zero_eq_eval_zero]
    have hc0 : F.coeff 0 = v.valuationSubring.subtype (f.coeff 0) := by
      rw [hF, coeff_map]
    rw [hc0]
    exact (Valuation.mem_valuationSubring_iff v _).mp (f.coeff 0).2
  -- some root has value `≤ 1`
  obtain ⟨r, hr, hrv⟩ : ∃ r ∈ F.roots, v r ≤ 1 := by
    by_contra h
    push Not at h
    have hm : ∀ a ∈ F.roots.map v, 1 < a := by
      intro a ha
      obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.mp ha
      exact h b hb
    have hne : F.roots.map v ≠ 0 := by
      intro h0
      have hc : (F.roots.map v).card = 0 := by rw [h0]; simp
      rw [Multiset.card_map, hcard, hFn] at hc
      omega
    exact absurd (one_lt_multiset_prod _ hm hne) (not_lt.mpr hval)
  -- reduce the root
  set y : ↥v.valuationSubring := ⟨r, (Valuation.mem_valuationSubring_iff v r).mpr hrv⟩ with hy
  have hgen : ∀ (g : (↥v.valuationSubring)[X]) (z : ↥v.valuationSubring),
      (g.map v.valuationSubring.subtype).eval (v.valuationSubring.subtype z)
        = v.valuationSubring.subtype (g.eval z) := by
    intro g z
    rw [← eval₂_eq_eval_map]
    exact Polynomial.eval₂_hom v.valuationSubring.subtype z
  have hfev : f.eval y = 0 := by
    have h1 : v.valuationSubring.subtype (f.eval y) = 0 := by
      rw [← hgen f y, hy]
      exact isRoot_of_mem_roots (p := F) hr
    exact v.valuationSubring.subtype_injective (by rw [h1, map_zero])
  refine ⟨IsLocalRing.residue ↥v.valuationSubring y, ?_⟩
  have h2 : (f.map (IsLocalRing.residue ↥v.valuationSubring)).eval
      (IsLocalRing.residue ↥v.valuationSubring y)
        = IsLocalRing.residue ↥v.valuationSubring (f.eval y) := by
    rw [← eval₂_eq_eval_map]
    exact Polynomial.eval₂_hom (IsLocalRing.residue ↥v.valuationSubring) y
  rw [h2, hfev, map_zero]

/-! ## The residue field is algebraically closed -/

/-- **Johnson, Lemma 2.3.6 (second half).**  The residue field of an algebraically closed
valued field is algebraically closed. -/
theorem isAlgClosed_residueField [IsAlgClosed K] (v : Valuation K Γ₀) :
    IsAlgClosed (IsLocalRing.ResidueField ↥v.valuationSubring) := by
  refine IsAlgClosed.of_exists_root
    (k := IsLocalRing.ResidueField ↥v.valuationSubring) (fun p hp hpi => ?_)
  haveI : Nontrivial ↥v.valuationSubring :=
    ⟨0, 1, fun h => zero_ne_one (congrArg Subtype.val h)⟩
  have hne0 : p ≠ 0 := hp.ne_zero
  have hd : 1 ≤ p.natDegree := by
    rcases Nat.eq_zero_or_pos p.natDegree with h | h
    · exfalso
      have hC : p = C (p.coeff 0) := eq_C_of_natDegree_eq_zero h
      have hc0 : p.coeff 0 ≠ 0 := by
        rw [hC] at hne0
        simpa using hne0
      rw [hC] at hpi
      exact hpi.not_isUnit (isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc0))
    · exact h
  obtain ⟨f, hfmonic, hfmap⟩ :=
    exists_monic_map_eq (IsLocalRing.residue ↥v.valuationSubring)
      Ideal.Quotient.mk_surjective hp
  have hfdeg : 1 ≤ f.natDegree := by
    rw [← Monic.natDegree_map hfmonic (IsLocalRing.residue ↥v.valuationSubring), hfmap]
    exact hd
  obtain ⟨x, hx⟩ := exists_residue_root v hfmonic hfdeg
  exact ⟨x, by rw [← hfmap]; exact hx⟩

/-- **Johnson, Lemma 2.3.6 (second half), conclusion.**  The residue field of an algebraically
closed valued field is infinite. -/
theorem infinite_residueField [IsAlgClosed K] (v : Valuation K Γ₀) :
    Infinite (IsLocalRing.ResidueField ↥v.valuationSubring) := by
  haveI := isAlgClosed_residueField v
  exact inferInstance





/-!
# Balls in a valued field, and Johnson's Lemma 2.3.5

Johnson, *Fun with Fields*, §2.3.  A ball is `{x : v (x - c) ≤ γ}` (closed), `{x : v (x - c) < γ}`
(open), a singleton, or the whole field.  We prove that intersecting closed balls (resp. open
balls) are comparable, and Lemma 2.3.5: every proper subball of the valuation ring `O` is
contained in a residue class, i.e. in `{x : v (x - c) < 1}` for some `c`.

The multiplicative convention is used throughout: `v 0 = 0` is the bottom of `Γ₀`, so `v x ≤ γ`
is the additive `v x ≥ γ` and closed balls are the `≤` ones.
-/


variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- The closed ball of radius `γ` about `c`. -/
def closedBall (v : Valuation K Γ₀) (c : K) (γ : Γ₀) : Set K := {x | v (x - c) ≤ γ}

/-- The open ball of radius `γ` about `c`. -/
def openBall (v : Valuation K Γ₀) (c : K) (γ : Γ₀) : Set K := {x | v (x - c) < γ}

@[simp]
theorem mem_closedBall {v : Valuation K Γ₀} {c x : K} {γ : Γ₀} :
    x ∈ closedBall v c γ ↔ v (x - c) ≤ γ := Iff.rfl

@[simp]
theorem mem_openBall {v : Valuation K Γ₀} {c x : K} {γ : Γ₀} :
    x ∈ openBall v c γ ↔ v (x - c) < γ := Iff.rfl

theorem closedBall_self_mem (v : Valuation K Γ₀) (c : K) (γ : Γ₀) : c ∈ closedBall v c γ := by
  simp

theorem openBall_self_mem {v : Valuation K Γ₀} {c : K} {γ : Γ₀} (h : γ ≠ 0) :
    c ∈ openBall v c γ := by
  have hpos : (0 : Γ₀) < γ := pos_iff_ne_zero.mpr h
  simpa using hpos

/-- The value of a difference is bounded by the maximum of two others. -/
theorem val_sub_le_max (v : Valuation K Γ₀) (a b c : K) :
    v (a - c) ≤ max (v (a - b)) (v (b - c)) := by
  have h : a - c = (a - b) + (b - c) := by ring
  rw [h]
  exact map_add_le_max _ _ _

/-- The value of `x - c` is at most the maximum of `v x` and `v c`. -/
theorem val_sub_le_max_of (v : Valuation K Γ₀) (x c : K) :
    v (x - c) ≤ max (v x) (v c) := by
  have h : x - c = x + -c := by ring
  rw [h]
  refine le_trans (map_add_le_max (f := v) x (-c)) ?_
  rw [Valuation.map_neg]

/-- A closed ball grows when the radius grows. -/
theorem closedBall_mono (v : Valuation K Γ₀) {c₁ c₂ : K} {γ₁ γ₂ : Γ₀}
    (h : v (c₁ - c₂) ≤ γ₂) (hγ : γ₁ ≤ γ₂) :
    closedBall v c₁ γ₁ ⊆ closedBall v c₂ γ₂ := by
  intro x hx
  rw [mem_closedBall] at hx ⊢
  exact le_trans (val_sub_le_max v x c₁ c₂) (max_le (le_trans hx hγ) h)

/-- An open ball grows when the radius grows. -/
theorem openBall_mono (v : Valuation K Γ₀) {c₁ c₂ : K} {γ₁ γ₂ : Γ₀}
    (h : v (c₁ - c₂) < γ₂) (hγ : γ₁ ≤ γ₂) :
    openBall v c₁ γ₁ ⊆ openBall v c₂ γ₂ := by
  intro x hx
  rw [mem_openBall] at hx ⊢
  refine lt_of_le_of_lt (val_sub_le_max v x c₁ c₂) (max_lt ?_ h)
  exact lt_of_lt_of_le hx hγ

/-- **Intersecting closed balls are comparable.**  (Johnson's (2.3).) -/
theorem closedBall_subset_or_subset (v : Valuation K Γ₀) {c₁ c₂ : K} {γ₁ γ₂ : Γ₀}
    (h : (closedBall v c₁ γ₁ ∩ closedBall v c₂ γ₂).Nonempty) :
    closedBall v c₁ γ₁ ⊆ closedBall v c₂ γ₂ ∨ closedBall v c₂ γ₂ ⊆ closedBall v c₁ γ₁ := by
  obtain ⟨z, hz₁, hz₂⟩ := h
  rw [mem_closedBall] at hz₁ hz₂
  have hz₁' : v (c₁ - z) ≤ γ₁ := by
    rw [show c₁ - z = -(z - c₁) by ring, Valuation.map_neg]; exact hz₁
  have hz₂' : v (c₂ - z) ≤ γ₂ := by
    rw [show c₂ - z = -(z - c₂) by ring, Valuation.map_neg]; exact hz₂
  have h12 : v (c₁ - c₂) ≤ max γ₁ γ₂ :=
    le_trans (val_sub_le_max v c₁ z c₂) (max_le_max hz₁' hz₂)
  have h21 : v (c₂ - c₁) ≤ max γ₂ γ₁ :=
    le_trans (val_sub_le_max v c₂ z c₁) (max_le_max hz₂' hz₁)
  rcases le_total γ₁ γ₂ with hγ | hγ
  · left
    refine closedBall_mono v ?_ hγ
    rwa [max_eq_right hγ] at h12
  · right
    refine closedBall_mono v ?_ hγ
    rwa [max_eq_right hγ] at h21

/-- **Intersecting open balls are comparable.** -/
theorem openBall_subset_or_subset (v : Valuation K Γ₀) {c₁ c₂ : K} {γ₁ γ₂ : Γ₀}
    (h : (openBall v c₁ γ₁ ∩ openBall v c₂ γ₂).Nonempty) :
    openBall v c₁ γ₁ ⊆ openBall v c₂ γ₂ ∨ openBall v c₂ γ₂ ⊆ openBall v c₁ γ₁ := by
  obtain ⟨z, hz₁, hz₂⟩ := h
  rw [mem_openBall] at hz₁ hz₂
  have hz₁' : v (c₁ - z) < γ₁ := by
    rw [show c₁ - z = -(z - c₁) by ring, Valuation.map_neg]; exact hz₁
  have hz₂' : v (c₂ - z) < γ₂ := by
    rw [show c₂ - z = -(z - c₂) by ring, Valuation.map_neg]; exact hz₂
  have h12 : v (c₁ - c₂) < max γ₁ γ₂ :=
    lt_of_le_of_lt (val_sub_le_max v c₁ z c₂) (max_lt_max hz₁' hz₂)
  have h21 : v (c₂ - c₁) < max γ₂ γ₁ :=
    lt_of_le_of_lt (val_sub_le_max v c₂ z c₁) (max_lt_max hz₂' hz₁)
  rcases le_total γ₁ γ₂ with hγ | hγ
  · left
    refine openBall_mono v ?_ hγ
    rwa [max_eq_right hγ] at h12
  · right
    refine openBall_mono v ?_ hγ
    rwa [max_eq_right hγ] at h21

/-! ## Lemma 2.3.5: proper subballs of the valuation ring lie in a residue class -/

/-- The balls of a valued field: closed balls, open balls, singletons, and the whole field. -/
inductive IsBall (v : Valuation K Γ₀) : Set K → Prop
  | closed (c : K) (γ : Γ₀) : IsBall v (closedBall v c γ)
  | openball (c : K) (γ : Γ₀) : IsBall v (openBall v c γ)
  | singleton (c : K) : IsBall v {c}
  | univ : IsBall v Set.univ

/-- **Johnson, Lemma 2.3.5.**  Every proper subball of the valuation ring `O` is contained in a
residue class `{x : v (x - c) < 1}`.  (Nontriviality of the valuation is needed exactly to
exclude the ball `K`.) -/
theorem subset_residueClass_of_isBall (v : Valuation K Γ₀) (hnt : ∃ x : K, 1 < v x)
    {B : Set K} (hB : IsBall v B) (hsub : B ⊆ (v.valuationSubring : Set K))
    (hne : B ≠ (v.valuationSubring : Set K)) :
    ∃ c : ↥v.valuationSubring, B ⊆ openBall v (c : K) 1 := by
  cases hB with
  | univ =>
    obtain ⟨x, hx⟩ := hnt
    have hxO : v x ≤ 1 := (Valuation.mem_valuationSubring_iff v x).mp (hsub trivial)
    exact absurd hxO (not_le.mpr hx)
  | singleton c =>
    refine ⟨⟨c, hsub (Set.mem_singleton c)⟩, ?_⟩
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    simpa using zero_lt_one (α := Γ₀)
  | closed c γ =>
    -- the centre of a ball lies in the ball, hence in `O`
    have hcO : c ∈ v.valuationSubring := hsub (closedBall_self_mem v c γ)
    have hc : v c ≤ 1 := (Valuation.mem_valuationSubring_iff v c).mp hcO
    by_cases hγ : γ < 1
    · refine ⟨⟨c, hcO⟩, ?_⟩
      intro x hx
      rw [mem_closedBall] at hx
      rw [mem_openBall]
      exact lt_of_le_of_lt hx hγ
    · -- otherwise the ball swallows `O`, contradicting properness
      exfalso
      apply hne
      refine Set.Subset.antisymm hsub ?_
      intro x hx
      have hx1 : v x ≤ 1 := (Valuation.mem_valuationSubring_iff v x).mp hx
      rw [mem_closedBall]
      refine le_trans (val_sub_le_max_of v x c) (max_le ?_ ?_)
      · exact le_trans hx1 (not_lt.mp hγ)
      · exact le_trans hc (not_lt.mp hγ)
  | openball c γ =>
    by_cases hγ0 : γ = 0
    · subst hγ0
      refine ⟨⟨0, v.valuationSubring.zero_mem⟩, ?_⟩
      intro x hx
      rw [mem_openBall] at hx
      exact absurd hx (not_lt.mpr zero_le)
    have hcO : c ∈ v.valuationSubring := hsub (openBall_self_mem hγ0)
    have hc : v c ≤ 1 := (Valuation.mem_valuationSubring_iff v c).mp hcO
    by_cases hγ : γ ≤ 1
    · refine ⟨⟨c, hcO⟩, ?_⟩
      intro x hx
      rw [mem_openBall] at hx ⊢
      exact lt_of_lt_of_le hx hγ
    · exfalso
      apply hne
      refine Set.Subset.antisymm hsub ?_
      intro x hx
      have hx1 : v x ≤ 1 := (Valuation.mem_valuationSubring_iff v x).mp hx
      rw [mem_openBall]
      refine lt_of_le_of_lt (val_sub_le_max_of v x c) (max_lt ?_ ?_)
      · exact lt_of_le_of_lt hx1 (not_le.mp hγ)
      · exact lt_of_le_of_lt hc (not_le.mp hγ)






/-! ## The valuation ring is not a finite union of proper subballs (Johnson 2.3.7, `B = O`) -/

/-- **Johnson, Lemma 2.3.7, the case `B = O`.**  The valuation ring of an algebraically closed,
nontrivially valued field is not a finite union of proper subballs.  The inputs are Lemma 2.3.5
(proper subballs lie in residue classes) and the infinitude of the residue field, Lemma 2.3.6. -/
theorem valuationSubring_not_finite_union_isBall [IsAlgClosed K] (v : Valuation K Γ₀)
    (hnt : ∃ x : K, 1 < v x) {ι : Type*} (s : Finset ι) (B : ι → Set K)
    (hball : ∀ i ∈ s, IsBall v (B i))
    (hsub : ∀ i ∈ s, B i ⊆ (v.valuationSubring : Set K))
    (hne : ∀ i ∈ s, B i ≠ (v.valuationSubring : Set K)) :
    (v.valuationSubring : Set K) ≠ ⋃ i ∈ s, B i := by
  intro hcover
  classical
  have hex : ∀ i ∈ s, ∃ c : ↥v.valuationSubring, B i ⊆ openBall v (c : K) 1 :=
    fun i hi => subset_residueClass_of_isBall v hnt (hball i hi) (hsub i hi) (hne i hi)
  choose c hc using hex
  -- every element of `O` reduces to one of finitely many residues
  have key : ∀ x : ↥v.valuationSubring, ∃ (i : ι) (hi : i ∈ s),
      IsLocalRing.residue ↥v.valuationSubring x = IsLocalRing.residue _ (c i hi) := by
    intro x
    have hx : (x : K) ∈ ⋃ i ∈ s, B i := by rw [← hcover]; exact x.2
    simp only [Set.mem_iUnion] at hx
    obtain ⟨i, hi, hxB⟩ := hx
    refine ⟨i, hi, ?_⟩
    have h1 : v ((x : K) - ((c i hi : ↥v.valuationSubring) : K)) < 1 := hc i hi hxB
    have hmem : x - c i hi ∈ IsLocalRing.maximalIdeal ↥v.valuationSubring := by
      rw [Valuation.mem_maximalIdeal_iff (v := v)]
      simpa using h1
    have h2 : IsLocalRing.residue ↥v.valuationSubring (x - c i hi) = 0 :=
      (IsLocalRing.residue_eq_zero_iff (x - c i hi)).mpr hmem
    rw [map_sub, sub_eq_zero] at h2
    exact h2
  have hsurj : Function.Surjective
      (fun i : ↥s => IsLocalRing.residue ↥v.valuationSubring (c i.1 i.2)) := by
    intro y
    obtain ⟨x, rfl⟩ :=
      Ideal.Quotient.mk_surjective (I := IsLocalRing.maximalIdeal ↥v.valuationSubring) y
    obtain ⟨i, hi, hres⟩ := key x
    exact ⟨⟨i, hi⟩, hres.symm⟩
  haveI : Fintype ↥s := inferInstance
  have hfin : Finite (IsLocalRing.ResidueField ↥v.valuationSubring) :=
    Finite.of_surjective _ hsurj
  exact (not_finite_iff_infinite.mpr (infinite_residueField v)) hfin

/-! ## The `B = m` and `B = K` cases of Johnson 2.3.7 -/

/-- A finite union of closed balls about `0` is a single one, of the largest radius. -/
theorem exists_closedBall_zero_union (v : Valuation K Γ₀) {ι : Type*} {s : Finset ι}
    {γ : ι → Γ₀} (hne : s.Nonempty) :
    ∃ γm : Γ₀, (∃ i ∈ s, γm = γ i) ∧ (∀ i ∈ s, γ i ≤ γm) ∧
      (⋃ i ∈ s, closedBall v 0 (γ i)) = closedBall v 0 γm := by
  classical
  obtain ⟨i₀, hi₀, hmax⟩ := Finset.exists_mem_eq_sup s hne γ
  refine ⟨γ i₀, ⟨i₀, hi₀, rfl⟩, fun i hi => ?_, ?_⟩
  · rw [← hmax]; exact Finset.le_sup (f := γ) hi
  · ext x
    simp only [Set.mem_iUnion, mem_closedBall, sub_zero]
    constructor
    · rintro ⟨i, hi, hx⟩
      rw [← hmax]
      exact le_trans hx (Finset.le_sup (f := γ) hi)
    · intro hx
      exact ⟨i₀, hi₀, hx⟩

/-- **Johnson 2.3.7, the case `B = K`** (after the normalisation of Lemma 2.3.4): the whole
field is not a finite union of closed balls about `0` with radii in `vK`. -/
theorem univ_ne_finite_union_closedBall (v : Valuation K Γ₀)
    (hnt : ∃ x : K, x ≠ 0 ∧ v x < 1) {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (γ : ι → Γ₀)
    (hγ : ∀ i ∈ s, ∃ a : K, v a = γ i) :
    (Set.univ : Set K) ≠ ⋃ i ∈ s, closedBall v 0 (γ i) := by
  obtain ⟨γm, ⟨i₀, hi₀, rfl⟩, -, hunion⟩ := exists_closedBall_zero_union v hs (γ := γ)
  obtain ⟨a, ha⟩ := hγ i₀ hi₀
  -- an element of value strictly above `γ i₀`
  have hgt : ∃ b : K, γ i₀ < v b := by
    rcases eq_or_ne (γ i₀) 0 with h0 | h0
    · refine ⟨1, ?_⟩
      rw [h0, map_one]
      exact zero_lt_one
    · obtain ⟨b, -, hb⟩ := exists_val_lt_val v hnt (v.ne_zero_iff.mp (by rw [ha]; exact h0))
      exact ⟨b, by rwa [← ha]⟩
  obtain ⟨b, hb⟩ := hgt
  intro hcover
  have hmem : b ∈ ⋃ i ∈ s, closedBall v 0 (γ i) := by rw [← hcover]; trivial
  rw [hunion] at hmem
  rw [mem_closedBall] at hmem
  simp only [sub_zero] at hmem
  exact absurd hmem (not_le.mpr hb)

/-- **Johnson 2.3.7, the case `B = m`** (after the normalisation of Lemma 2.3.4): the maximal
ideal is not a finite union of closed balls about `0` of radius `< 1` with radii in `vK`.
This is where density of the value group is used. -/
theorem openBall_zero_ne_finite_union_closedBall [IsAlgClosed K] (v : Valuation K Γ₀)
    (hnt : ∃ x : K, x ≠ 0 ∧ v x < 1) {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (γ : ι → Γ₀) (hγ : ∀ i ∈ s, ∃ a : K, v a = γ i) (hlt : ∀ i ∈ s, γ i < 1) :
    openBall v 0 1 ≠ ⋃ i ∈ s, closedBall v 0 (γ i) := by
  obtain ⟨γm, ⟨i₀, hi₀, rfl⟩, -, hunion⟩ := exists_closedBall_zero_union v hs (γ := γ)
  obtain ⟨a, ha⟩ := hγ i₀ hi₀
  have hγlt : γ i₀ < 1 := hlt i₀ hi₀
  -- an element of the open ball of radius `1` lying strictly outside the closed ball
  have hgt : ∃ b : K, γ i₀ < v b ∧ v b < 1 := by
    rcases eq_or_ne (γ i₀) 0 with h0 | h0
    · obtain ⟨x, hx0, hx⟩ := hnt
      exact ⟨x, by rw [h0]; exact pos_iff_ne_zero.mpr (v.ne_zero_iff.mpr hx0), hx⟩
    · have ha0 : a ≠ 0 := v.ne_zero_iff.mp (by rw [ha]; exact h0)
      obtain ⟨b, -, h1, h2⟩ :=
        exists_val_between v ha0 (one_ne_zero) (by rw [ha, map_one]; exact hγlt)
      exact ⟨b, by rwa [ha] at h1, by rwa [map_one] at h2⟩
  obtain ⟨b, hb1, hb2⟩ := hgt
  intro hcover
  have hmem : b ∈ ⋃ i ∈ s, closedBall v 0 (γ i) := by
    rw [← hcover]
    simpa using hb2
  rw [hunion] at hmem
  rw [mem_closedBall] at hmem
  simp only [sub_zero] at hmem
  exact absurd hmem (not_le.mpr hb1)

/-- **Johnson, Lemma 2.3.6.**  For an algebraically closed field with a nontrivial valuation, the
value group is a dense linear order without endpoints and the residue field is infinite. -/
theorem lemma_2_3_6 [IsAlgClosed K] (v : Valuation K Γ₀)
    (hnt : ∃ x : K, x ≠ 0 ∧ v x < 1) :
    (∀ a : K, a ≠ 0 → ∃ b : K, b ≠ 0 ∧ v a < v b) ∧
    (∀ a : K, a ≠ 0 → ∃ b : K, b ≠ 0 ∧ v b < v a) ∧
    (∀ a c : K, a ≠ 0 → c ≠ 0 → v a < v c → ∃ b : K, b ≠ 0 ∧ v a < v b ∧ v b < v c) ∧
    Infinite (IsLocalRing.ResidueField ↥v.valuationSubring) :=
  ⟨(valueGroup_dlo v hnt).1, (valueGroup_dlo v hnt).2.1, (valueGroup_dlo v hnt).2.2,
   infinite_residueField v⟩


/-! ## Affine normalisation of balls

Johnson normalises a ball to one of `{0}`, `m`, `O` or `K` by an affine transformation
`x ↦ c + b x`; the lemmas here are that normalisation for closed and open balls, and the
identification of the closed unit ball with the valuation ring. -/

/-- A closed ball of radius zero is a point. -/
theorem closedBall_zero_eq_singleton (v : Valuation K Γ₀) (c : K) :
    closedBall v c 0 = {c} := by
  ext x
  rw [mem_closedBall, Set.mem_singleton_iff]
  constructor
  · intro h
    have h' : v (x - c) = 0 := le_antisymm h zero_le
    exact sub_eq_zero.mp (v.zero_iff.mp h')
  · rintro rfl
    rw [sub_self, map_zero]

/-- An open ball of radius zero is empty. -/
theorem openBall_zero_eq_empty (v : Valuation K Γ₀) (c : K) :
    openBall v c 0 = ∅ := by
  ext x
  rw [mem_openBall, Set.mem_empty_iff_false, iff_false]
  exact not_lt.mpr zero_le

/-- The closed unit ball about `0` is the valuation ring. -/
theorem closedBall_zero_one_eq_valuationSubring (v : Valuation K Γ₀) :
    closedBall v 0 1 = (v.valuationSubring : Set K) := by
  ext x
  rw [mem_closedBall, sub_zero]
  rfl

/-- An affine map with nonzero linear part sends the closed ball of radius `γ` about `d` to the
closed ball of radius `v b * γ` about `c + b * d`. -/
theorem affine_image_closedBall (v : Valuation K Γ₀) {b : K} (hb : b ≠ 0) (c d : K) (γ : Γ₀) :
    (fun y : K => c + b * y) '' closedBall v d γ = closedBall v (c + b * d) (v b * γ) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [mem_closedBall] at hy ⊢
    have h : c + b * y - (c + b * d) = b * (y - d) := by ring
    rw [h, map_mul]
    exact mul_le_mul_right hy _
  · intro hx
    rw [mem_closedBall] at hx
    refine ⟨d + b⁻¹ * (x - (c + b * d)), ?_, ?_⟩
    · rw [mem_closedBall]
      have h : d + b⁻¹ * (x - (c + b * d)) - d = b⁻¹ * (x - (c + b * d)) := by ring
      rw [h, map_mul, Valuation.map_inv]
      have h2 : (v b)⁻¹ * v (x - (c + b * d)) ≤ (v b)⁻¹ * (v b * γ) := mul_le_mul_right hx _
      rwa [← mul_assoc, inv_mul_cancel₀ (v.ne_zero_iff.mpr hb), one_mul] at h2
    · show c + b * (d + b⁻¹ * (x - (c + b * d))) = x
      have h : b * (b⁻¹ * (x - (c + b * d))) = x - (c + b * d) := by
        rw [← mul_assoc, mul_inv_cancel₀ hb, one_mul]
      rw [mul_add, h]; ring

/-- The same for open balls. -/
theorem affine_image_openBall (v : Valuation K Γ₀) {b : K} (hb : b ≠ 0) (c d : K) (γ : Γ₀) :
    (fun y : K => c + b * y) '' openBall v d γ = openBall v (c + b * d) (v b * γ) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [mem_openBall] at hy ⊢
    have h : c + b * y - (c + b * d) = b * (y - d) := by ring
    rw [h, map_mul]
    exact mul_lt_mul_of_pos_left hy (pos_iff_ne_zero.mpr (v.ne_zero_iff.mpr hb))
  · intro hx
    rw [mem_openBall] at hx
    refine ⟨d + b⁻¹ * (x - (c + b * d)), ?_, ?_⟩
    · rw [mem_openBall]
      have h : d + b⁻¹ * (x - (c + b * d)) - d = b⁻¹ * (x - (c + b * d)) := by ring
      rw [h, map_mul, Valuation.map_inv]
      have h2 : (v b)⁻¹ * v (x - (c + b * d)) < (v b)⁻¹ * (v b * γ) :=
        mul_lt_mul_of_pos_left hx (pos_iff_ne_zero.mpr (inv_ne_zero (v.ne_zero_iff.mpr hb)))
      rwa [← mul_assoc, inv_mul_cancel₀ (v.ne_zero_iff.mpr hb), one_mul] at h2
    · show c + b * (d + b⁻¹ * (x - (c + b * d))) = x
      have h : b * (b⁻¹ * (x - (c + b * d))) = x - (c + b * d) := by
        rw [← mul_assoc, mul_inv_cancel₀ hb, one_mul]
      rw [mul_add, h]; ring

/-- Every closed ball whose radius is a value is an affine image of the valuation ring. -/
theorem closedBall_eq_affine_image (v : Valuation K Γ₀) {b : K} (hb : b ≠ 0) (c : K) :
    closedBall v c (v b) = (fun y : K => c + b * y) '' (v.valuationSubring : Set K) := by
  rw [← closedBall_zero_one_eq_valuationSubring v]
  simpa using (affine_image_closedBall v hb c 0 1).symm

/-- Every open ball whose radius is a nonzero value is an affine image of the open unit ball. -/
theorem openBall_eq_affine_image (v : Valuation K Γ₀) {b : K} (hb : b ≠ 0) (c : K) :
    openBall v c (v b) = (fun y : K => c + b * y) '' openBall v 0 1 := by
  simpa using (affine_image_openBall v hb c 0 1).symm

/-- An affine map with nonzero linear part sends balls to balls. -/
theorem isBall_affine_image (v : Valuation K Γ₀) {b : K} (hb : b ≠ 0) (c : K) {D : Set K}
    (hD : IsBall v D) : IsBall v ((fun y : K => c + b * y) '' D) := by
  cases hD with
  | closed d γ =>
    exact (affine_image_closedBall v hb c d γ).symm ▸ IsBall.closed (c + b * d) (v b * γ)
  | openball d γ =>
    exact (affine_image_openBall v hb c d γ).symm ▸ IsBall.openball (c + b * d) (v b * γ)
  | singleton d =>
    exact (Set.image_singleton (f := fun y : K => c + b * y) (a := d)).symm ▸
      IsBall.singleton (c + b * d)
  | univ =>
    have h : (fun y : K => c + b * y) '' Set.univ = Set.univ := by
      rw [Set.image_univ, Set.range_eq_univ]
      intro x
      exact ⟨b⁻¹ * (x - c), by
        show c + b * (b⁻¹ * (x - c)) = x
        rw [← mul_assoc, mul_inv_cancel₀ hb, one_mul]; ring⟩
    exact h.symm ▸ IsBall.univ

/-! ## Balls with radii in `vK`, and Lemma 2.3.4

Johnson's balls of a valued field have centre and radius in the *value group*: the closed balls
`{x : v (x - c) ≤ v b}` and open balls `{x : v (x - c) < v b}` for `b : K`, the singletons and the
whole field.  (`IsBall` above allows an arbitrary `γ : Γ₀`; the lemmas of 2.3.4 and 2.3.7 are
stated for radii in `vK`, which is the form in which the paper uses them.) -/

/-- The balls of a valued field with radii in the value group: `B = {x : v (x - c) ≤ v b}`,
`B = {x : v (x - c) < v b}`, `B = {c}`, `B = K`. -/
inductive IsValBall (v : Valuation K Γ₀) : Set K → Prop
  | closed (c b : K) : IsValBall v (closedBall v c (v b))
  | openball (c b : K) : IsValBall v (openBall v c (v b))
  | singleton (c : K) : IsValBall v {c}
  | univ : IsValBall v Set.univ

theorem IsValBall.isBall {v : Valuation K Γ₀} {D : Set K} (h : IsValBall v D) : IsBall v D := by
  cases h with
  | closed c b => exact IsBall.closed c (v b)
  | openball c b => exact IsBall.openball c (v b)
  | singleton c => exact IsBall.singleton c
  | univ => exact IsBall.univ

/-- Nontriviality of the valuation, in the two equivalent forms used below. -/
theorem exists_ne_zero_val_lt_one_iff (v : Valuation K Γ₀) :
    (∃ x : K, x ≠ 0 ∧ v x < 1) ↔ (∃ x : K, 1 < v x) := by
  constructor
  · rintro ⟨x, hx0, hx⟩
    refine ⟨x⁻¹, ?_⟩
    rw [Valuation.map_inv]
    exact one_lt_inv_iff₀.mpr ⟨pos_iff_ne_zero.mpr (v.ne_zero_iff.mpr hx0), hx⟩
  · rintro ⟨x, hx⟩
    refine ⟨x⁻¹, inv_ne_zero (v.ne_zero_iff.mp (ne_of_gt (zero_lt_one.trans hx))), ?_⟩
    rw [Valuation.map_inv]
    exact inv_lt_one_of_one_lt₀ hx

/-- Some element whose value dominates both `v a` and `v c`. -/
theorem exists_val_gt_max (v : Valuation K Γ₀) (hnt : ∃ x : K, x ≠ 0 ∧ v x < 1) (a c : K) :
    ∃ b : K, b ≠ 0 ∧ v a < v b ∧ v c < v b := by
  rcases le_total (v a) (v c) with h | h
  · rcases eq_or_ne c 0 with rfl | hc
    · have hz : v a = 0 := le_antisymm (by simpa using h) zero_le
      obtain ⟨x, hx0, hx⟩ := hnt
      refine ⟨x, hx0, ?_, ?_⟩
      · rw [hz]; exact pos_iff_ne_zero.mpr (v.ne_zero_iff.mpr hx0)
      · rw [map_zero]; exact pos_iff_ne_zero.mpr (v.ne_zero_iff.mpr hx0)
    · obtain ⟨b, hb0, hb⟩ := exists_val_lt_val v hnt hc
      exact ⟨b, hb0, lt_of_le_of_lt h hb, hb⟩
  · rcases eq_or_ne a 0 with rfl | ha
    · have hz : v c = 0 := le_antisymm (by simpa using h) zero_le
      obtain ⟨x, hx0, hx⟩ := hnt
      refine ⟨x, hx0, ?_, ?_⟩
      · rw [map_zero]; exact pos_iff_ne_zero.mpr (v.ne_zero_iff.mpr hx0)
      · rw [hz]; exact pos_iff_ne_zero.mpr (v.ne_zero_iff.mpr hx0)
    · obtain ⟨b, hb0, hb⟩ := exists_val_lt_val v hnt ha
      exact ⟨b, hb0, hb, lt_of_le_of_lt h hb⟩

/-- Given two values below `1` there is one value above both and still below `1`. -/
theorem exists_val_between_max_one [IsAlgClosed K] (v : Valuation K Γ₀)
    (hnt : ∃ x : K, x ≠ 0 ∧ v x < 1) {a c : K} (ha : v a < 1) (hc : v c < 1) :
    ∃ b : K, b ≠ 0 ∧ v a ≤ v b ∧ v c ≤ v b ∧ v b < 1 := by
  rcases le_total (v a) (v c) with h | h
  · rcases eq_or_ne (v c) 0 with h0 | h0
    · have hz : v a = 0 := le_antisymm (by rw [h0] at h; exact h) zero_le
      obtain ⟨x, hx0, hx⟩ := hnt
      exact ⟨x, hx0, by rw [hz]; exact zero_le, by rw [h0]; exact zero_le, hx⟩
    · obtain ⟨b, hb0, hb1, hb2⟩ :=
        exists_val_between v (v.ne_zero_iff.mp h0) one_ne_zero (by rwa [map_one])
      exact ⟨b, hb0, le_of_lt (lt_of_le_of_lt h hb1), le_of_lt hb1, by rwa [map_one] at hb2⟩
  · rcases eq_or_ne (v a) 0 with h0 | h0
    · have hz : v c = 0 := le_antisymm (by rw [h0] at h; exact h) zero_le
      obtain ⟨x, hx0, hx⟩ := hnt
      exact ⟨x, hx0, by rw [h0]; exact zero_le, by rw [hz]; exact zero_le, hx⟩
    · obtain ⟨b, hb0, hb1, hb2⟩ :=
        exists_val_between v (v.ne_zero_iff.mp h0) one_ne_zero (by rwa [map_one])
      exact ⟨b, hb0, le_of_lt hb1, le_of_lt (lt_of_le_of_lt h hb1), by rwa [map_one] at hb2⟩

/-- An open ball of radius `1` about a centre inside the maximal ideal is the maximal ideal. -/
theorem openBall_one_eq_of_val_lt_one (v : Valuation K Γ₀) {c : K} (hc : v c < 1) :
    openBall v c 1 = openBall v 0 1 := by
  ext x
  simp only [mem_openBall, sub_zero]
  constructor
  · intro hx
    have h1 : v x ≤ max (v (x - c)) (v c) := by simpa using val_sub_le_max v x c 0
    exact lt_of_le_of_lt h1 (max_lt hx hc)
  · intro hx
    have h1 : v (x - c) ≤ max (v x) (v c) := by simpa using val_sub_le_max v x 0 c
    exact lt_of_le_of_lt h1 (max_lt hx hc)

/-- **Johnson, Lemma 2.3.4, the `m` case.** A ball properly contained in the maximal ideal is
contained in a closed ball about `0` of radius `v b < 1`. -/
theorem exists_closedBall_zero_of_isValBall_subset_openBall [IsAlgClosed K]
    (v : Valuation K Γ₀) (hnt : ∃ x : K, x ≠ 0 ∧ v x < 1) {D : Set K} (hD : IsValBall v D)
    (hsub : D ⊆ openBall v 0 1) (hne : D ≠ openBall v 0 1) :
    ∃ b : K, b ≠ 0 ∧ v b < 1 ∧ D ⊆ closedBall v 0 (v b) := by
  cases hD with
  | closed c a =>
    have hc : v c < 1 := by
      have h := hsub (closedBall_self_mem v c (v a))
      rwa [mem_openBall, sub_zero] at h
    have ha : v a < 1 := by
      by_contra hcon
      have h1 : (1 : K) ∈ closedBall v c (v a) := by
        rw [mem_closedBall]
        refine le_trans (val_sub_le_max_of v 1 c) (max_le ?_ ?_)
        · rw [map_one]; exact le_of_not_gt hcon
        · exact le_trans hc.le (le_of_not_gt hcon)
      have h2 := hsub h1
      rw [mem_openBall, sub_zero, map_one] at h2
      exact absurd h2 (lt_irrefl 1)
    obtain ⟨b, hb0, hba, hbc, hb1⟩ := exists_val_between_max_one v hnt ha hc
    refine ⟨b, hb0, hb1, ?_⟩
    intro x hx
    simp only [mem_closedBall, sub_zero] at hx ⊢
    have h1 : v x ≤ max (v (x - c)) (v c) := by simpa using val_sub_le_max v x c 0
    exact le_trans h1 (max_le (le_trans hx hba) hbc)
  | openball c a =>
    rcases eq_or_ne (v a) 0 with ha0 | ha0
    · obtain ⟨b, hb0, hb1⟩ := hnt
      refine ⟨b, hb0, hb1, ?_⟩
      rw [ha0, openBall_zero_eq_empty]
      exact Set.empty_subset _
    · have hc : v c < 1 := by
        have h := hsub (openBall_self_mem (v := v) ha0)
        rwa [mem_openBall, sub_zero] at h
      have ha : v a ≤ 1 := by
        by_contra hcon
        have h1 : (1 : K) ∈ openBall v c (v a) := by
          rw [mem_openBall]
          refine lt_of_le_of_lt (val_sub_le_max_of v 1 c) (max_lt ?_ ?_)
          · rw [map_one]; exact lt_of_not_ge hcon
          · exact lt_of_le_of_lt hc.le (lt_of_not_ge hcon)
        have h2 := hsub h1
        rw [mem_openBall, sub_zero, map_one] at h2
        exact absurd h2 (lt_irrefl 1)
      rcases lt_or_eq_of_le ha with ha' | ha'
      · obtain ⟨b, hb0, hba, hbc, hb1⟩ := exists_val_between_max_one v hnt ha' hc
        refine ⟨b, hb0, hb1, ?_⟩
        intro x hx
        simp only [mem_openBall, mem_closedBall, sub_zero] at hx ⊢
        have h1 : v x ≤ max (v (x - c)) (v c) := by simpa using val_sub_le_max v x c 0
        exact le_trans h1 (max_le (le_of_lt (lt_of_lt_of_le hx hba)) hbc)
      · rw [ha'] at hne
        exact absurd (openBall_one_eq_of_val_lt_one v hc) hne
  | singleton c =>
    have hc : v c < 1 := by
      have h := hsub (Set.mem_singleton c)
      rwa [mem_openBall, sub_zero] at h
    obtain ⟨b, hb0, hbc, -, hb1⟩ :=
      exists_val_between_max_one v hnt hc (by rw [map_zero]; exact zero_lt_one)
    refine ⟨b, hb0, hb1, ?_⟩
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    simpa using hbc
  | univ =>
    exfalso
    have h2 := hsub (Set.mem_univ (1 : K))
    rw [mem_openBall, sub_zero, map_one] at h2
    exact absurd h2 (lt_irrefl 1)

/-- **Johnson, Lemma 2.3.4, the `K` case.** A ball other than the whole field is contained in a
closed ball about `0`. -/
theorem exists_closedBall_zero_of_isValBall_of_ne_univ (v : Valuation K Γ₀)
    (hnt : ∃ x : K, x ≠ 0 ∧ v x < 1) {D : Set K} (hD : IsValBall v D) (hne : D ≠ Set.univ) :
    ∃ b : K, b ≠ 0 ∧ D ⊆ closedBall v 0 (v b) := by
  cases hD with
  | closed c a =>
    obtain ⟨b, hb0, hba, hbc⟩ := exists_val_gt_max v hnt a c
    refine ⟨b, hb0, ?_⟩
    intro x hx
    simp only [mem_closedBall, sub_zero] at hx ⊢
    have h1 : v x ≤ max (v (x - c)) (v c) := by simpa using val_sub_le_max v x c 0
    exact le_trans h1 (max_le (le_of_lt (lt_of_le_of_lt hx hba)) (le_of_lt hbc))
  | openball c a =>
    obtain ⟨b, hb0, hba, hbc⟩ := exists_val_gt_max v hnt a c
    refine ⟨b, hb0, ?_⟩
    intro x hx
    simp only [mem_openBall, mem_closedBall, sub_zero] at hx ⊢
    have h1 : v x ≤ max (v (x - c)) (v c) := by simpa using val_sub_le_max v x c 0
    exact le_trans h1 (max_le (le_of_lt (lt_trans hx hba)) (le_of_lt hbc))
  | singleton c =>
    obtain ⟨b, hb0, hbc, -⟩ := exists_val_gt_max v hnt c 0
    refine ⟨b, hb0, ?_⟩
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    simpa using le_of_lt hbc
  | univ => exact absurd rfl hne

/-- An affine map with nonzero linear part sends balls with radii in `vK` to such balls. -/
theorem isValBall_affine_image (v : Valuation K Γ₀) {b : K} (hb : b ≠ 0) (c : K) {D : Set K}
    (hD : IsValBall v D) : IsValBall v ((fun y : K => c + b * y) '' D) := by
  cases hD with
  | closed d a =>
    have h : (fun y : K => c + b * y) '' closedBall v d (v a)
        = closedBall v (c + b * d) (v (b * a)) := by
      rw [map_mul, affine_image_closedBall v hb c d (v a)]
    exact h ▸ IsValBall.closed (c + b * d) (b * a)
  | openball d a =>
    have h : (fun y : K => c + b * y) '' openBall v d (v a)
        = openBall v (c + b * d) (v (b * a)) := by
      rw [map_mul, affine_image_openBall v hb c d (v a)]
    exact h ▸ IsValBall.openball (c + b * d) (b * a)
  | singleton d =>
    have h : (fun y : K => c + b * y) '' ({d} : Set K) = {c + b * d} := by
      rw [Set.image_singleton]
    exact h ▸ IsValBall.singleton (c + b * d)
  | univ =>
    have h : (fun y : K => c + b * y) '' Set.univ = Set.univ := by
      rw [Set.image_univ, Set.range_eq_univ]
      intro x
      exact ⟨b⁻¹ * (x - c), by
        show c + b * (b⁻¹ * (x - c)) = x
        rw [← mul_assoc, mul_inv_cancel₀ hb, one_mul]; ring⟩
    rw [h]; exact IsValBall.univ

/-- **Johnson, Lemma 2.3.7, the `m` case** in general form: a finite union of balls properly
contained in the maximal ideal does not exhaust it. -/
theorem openBall_zero_ne_finite_union_of_isValBall [IsAlgClosed K] (v : Valuation K Γ₀)
    (hnt : ∃ x : K, x ≠ 0 ∧ v x < 1) {ι : Type*} (s : Finset ι) (D : ι → Set K)
    (hD : ∀ i ∈ s, IsValBall v (D i)) (hsub : ∀ i ∈ s, D i ⊆ openBall v 0 1)
    (hne : ∀ i ∈ s, D i ≠ openBall v 0 1) :
    openBall v 0 1 ≠ ⋃ i ∈ s, D i := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | hs
  · intro hcover
    have h0 : (0 : K) ∈ openBall v 0 1 := by simp
    rw [hcover] at h0
    simpa using h0
  · have hex : ∀ i ∈ s, ∃ b : K, b ≠ 0 ∧ v b < 1 ∧ D i ⊆ closedBall v 0 (v b) :=
      fun i hi => exists_closedBall_zero_of_isValBall_subset_openBall v hnt (hD i hi) (hsub i hi)
        (hne i hi)
    choose b hb0 hb1 hbsub using hex
    let γ : ι → Γ₀ := fun i => if h : i ∈ s then v (b i h) else 1
    have hγ : ∀ i ∈ s, ∃ a : K, v a = γ i := by
      intro i hi
      refine ⟨b i hi, ?_⟩
      show v (b i hi) = if h : i ∈ s then v (b i h) else 1
      rw [dif_pos hi]
    have hlt : ∀ i ∈ s, γ i < 1 := by
      intro i hi
      show (if h : i ∈ s then v (b i h) else 1) < 1
      rw [dif_pos hi]
      exact hb1 i hi
    have hkey := openBall_zero_ne_finite_union_closedBall v hnt s hs γ hγ hlt
    intro hcover
    apply hkey
    refine Set.Subset.antisymm ?_ ?_
    · rw [hcover]
      intro x hx
      simp only [Set.mem_iUnion] at hx ⊢
      obtain ⟨i, hi, hxi⟩ := hx
      refine ⟨i, hi, ?_⟩
      rw [show γ i = v (b i hi) from by
        show (if h : i ∈ s then v (b i h) else 1) = v (b i hi)
        rw [dif_pos hi]]
      exact hbsub i hi hxi
    · intro x hx
      simp only [Set.mem_iUnion] at hx
      obtain ⟨i, hi, hxi⟩ := hx
      simp only [mem_closedBall, sub_zero] at hxi
      simp only [mem_openBall, sub_zero]
      refine lt_of_le_of_lt hxi ?_
      show (if h : i ∈ s then v (b i h) else 1) < 1
      rw [dif_pos hi]
      exact hb1 i hi

/-- **Johnson, Lemma 2.3.7, the `K` case** in general form: a finite union of balls properly
contained in the whole field does not exhaust it. -/
theorem univ_ne_finite_union_of_isValBall (v : Valuation K Γ₀)
    (hnt : ∃ x : K, x ≠ 0 ∧ v x < 1) {ι : Type*} (s : Finset ι) (D : ι → Set K)
    (hD : ∀ i ∈ s, IsValBall v (D i)) (hne : ∀ i ∈ s, D i ≠ Set.univ) :
    Set.univ ≠ ⋃ i ∈ s, D i := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | hs
  · intro hcover
    have h0 : (0 : K) ∈ (Set.univ : Set K) := Set.mem_univ 0
    rw [hcover] at h0
    simpa using h0
  · have hex : ∀ i ∈ s, ∃ b : K, b ≠ 0 ∧ D i ⊆ closedBall v 0 (v b) :=
      fun i hi => exists_closedBall_zero_of_isValBall_of_ne_univ v hnt (hD i hi) (hne i hi)
    choose b hb0 hbsub using hex
    let γ : ι → Γ₀ := fun i => if h : i ∈ s then v (b i h) else 1
    have hγ : ∀ i ∈ s, ∃ a : K, v a = γ i := by
      intro i hi
      refine ⟨b i hi, ?_⟩
      show v (b i hi) = if h : i ∈ s then v (b i h) else 1
      rw [dif_pos hi]
    have hkey := univ_ne_finite_union_closedBall v hnt s hs γ hγ
    intro hcover
    apply hkey
    rw [hcover]
    refine Set.Subset.antisymm ?_ ?_
    · intro x hx
      simp only [Set.mem_iUnion] at hx ⊢
      obtain ⟨i, hi, hxi⟩ := hx
      exact ⟨i, hi, by
        rw [show γ i = v (b i hi) from by
          show (if h : i ∈ s then v (b i h) else 1) = v (b i hi)
          rw [dif_pos hi]]
        exact hbsub i hi hxi⟩
    · rw [← hcover]
      exact Set.subset_univ _

/-- A cover transfers across an affine bijection of the field. -/
theorem cover_transfer {b c : K} (hb : b ≠ 0) {B₀ : Set K} {ι : Type*} (s : Finset ι)
    (D : ι → Set K) (hcover : (fun y : K => c + b * y) '' B₀ = ⋃ i ∈ s, D i) :
    B₀ = ⋃ i ∈ s, (fun y : K => (y - c) * b⁻¹) '' D i := by
  have hφψ : (fun y : K => (c + b * y - c) * b⁻¹) = id := by
    funext y
    have h1 : c + b * y - c = b * y := by ring
    rw [h1]
    show (b * y) * b⁻¹ = y
    rw [mul_comm b y, mul_assoc, mul_inv_cancel₀ hb, mul_one]
  have himg : (fun y : K => (y - c) * b⁻¹) ''
      ((fun y : K => c + b * y) '' B₀) = B₀ := by
    rw [Set.image_image, hφψ]
    exact Set.image_id B₀
  rw [← himg, hcover]
  simp only [Set.image_iUnion]

/-- **Johnson, Lemma 2.3.7.** No nonempty ball of an algebraically closed field with a nontrivial
valuation is a finite union of proper subballs. -/
theorem ne_finite_union_of_proper_subballs [IsAlgClosed K] (v : Valuation K Γ₀)
    (hnt : ∃ x : K, 1 < v x) {B : Set K} (hB : IsValBall v B) (hBne : B.Nonempty)
    {ι : Type*} (s : Finset ι) (D : ι → Set K)
    (hD : ∀ i ∈ s, IsValBall v (D i)) (hDsub : ∀ i ∈ s, D i ⊆ B)
    (hDne : ∀ i ∈ s, D i ≠ B) :
    B ≠ ⋃ i ∈ s, D i := by
  classical
  have hnt' : ∃ x : K, x ≠ 0 ∧ v x < 1 := (exists_ne_zero_val_lt_one_iff v).mpr hnt
  have hpsi : ∀ b c : K, (fun y : K => (y - c) * b⁻¹) = fun y => (-(c * b⁻¹)) + b⁻¹ * y := by
    intro b c; funext y; ring
  have hcomp : ∀ (b c : K), b ≠ 0 → (fun x : K => c + b * ((x - c) * b⁻¹)) = id := by
    intro b c hb
    funext x
    have h1 : b * ((x - c) * b⁻¹) = x - c := by
      rw [mul_comm b ((x - c) * b⁻¹), mul_assoc, inv_mul_cancel₀ hb, mul_one]
    rw [h1]
    show c + (x - c) = x
    ring
  cases hB with
  | univ => exact univ_ne_finite_union_of_isValBall v hnt' s D hD hDne
  | singleton c =>
    intro hcover
    have hDempty : ∀ i ∈ s, D i = ∅ := by
      intro i hi
      rcases Set.subset_singleton_iff_eq.mp (hDsub i hi) with h | h
      · exact h
      · exact absurd h (hDne i hi)
    have hc : c ∈ ⋃ i ∈ s, D i := by rw [← hcover]; exact Set.mem_singleton c
    simp only [Set.mem_iUnion] at hc
    obtain ⟨i, hi, hx⟩ := hc
    rw [hDempty i hi] at hx
    exact hx
  | closed c b =>
    rcases eq_or_ne (v b) 0 with hb0 | hb0
    · rw [hb0, closedBall_zero_eq_singleton] at hDsub hDne ⊢
      intro hcover
      have hDempty : ∀ i ∈ s, D i = ∅ := by
        intro i hi
        rcases Set.subset_singleton_iff_eq.mp (hDsub i hi) with h | h
        · exact h
        · exact absurd h (hDne i hi)
      have hc : c ∈ ⋃ i ∈ s, D i := by rw [← hcover]; exact Set.mem_singleton c
      simp only [Set.mem_iUnion] at hc
      obtain ⟨i, hi, hx⟩ := hc
      rw [hDempty i hi] at hx
      exact hx
    · have hbne : b ≠ 0 := v.ne_zero_iff.mp hb0
      rw [closedBall_eq_affine_image v hbne c] at hDsub hDne ⊢
      intro hcover
      have hcover' := cover_transfer hbne s D hcover
      have himg : (fun y : K => (y - c) * b⁻¹) ''
          ((fun y : K => c + b * y) '' (v.valuationSubring : Set K))
            = (v.valuationSubring : Set K) := by
        rw [Set.image_image]
        have hφψ : (fun y : K => (c + b * y - c) * b⁻¹) = id := by
          funext y
          have h1 : c + b * y - c = b * y := by ring
          rw [h1]
          show (b * y) * b⁻¹ = y
          rw [mul_comm b y, mul_assoc, mul_inv_cancel₀ hbne, mul_one]
        rw [hφψ]
        exact Set.image_id _
      have hball : ∀ i ∈ s, IsBall v ((fun y : K => (y - c) * b⁻¹) '' D i) := by
        intro i hi
        rw [hpsi b c]
        exact (isValBall_affine_image v (inv_ne_zero hbne) (-(c * b⁻¹)) (hD i hi)).isBall
      have hsubO : ∀ i ∈ s, ((fun y : K => (y - c) * b⁻¹) '' D i) ⊆ (v.valuationSubring : Set K) := by
        intro i hi
        rw [← himg]
        exact Set.image_mono (hDsub i hi)
      have hneO : ∀ i ∈ s, ((fun y : K => (y - c) * b⁻¹) '' D i) ≠ (v.valuationSubring : Set K) := by
        intro i hi hcon
        apply hDne i hi
        have hthis : (fun y : K => c + b * y) '' ((fun y : K => (y - c) * b⁻¹) '' D i)
            = (fun y : K => c + b * y) '' (v.valuationSubring : Set K) := by rw [hcon]
        rw [Set.image_image, hcomp b c hbne, Set.image_id] at hthis
        exact hthis
      exact valuationSubring_not_finite_union_isBall v hnt s _ hball hsubO hneO hcover'
  | openball c b =>
    rcases eq_or_ne (v b) 0 with hb0 | hb0
    · rw [hb0, openBall_zero_eq_empty] at hBne
      exact absurd hBne (Set.not_nonempty_empty)
    · have hbne : b ≠ 0 := v.ne_zero_iff.mp hb0
      rw [openBall_eq_affine_image v hbne c] at hDsub hDne ⊢
      intro hcover
      have hcover' := cover_transfer hbne s D hcover
      have himg : (fun y : K => (y - c) * b⁻¹) ''
          ((fun y : K => c + b * y) '' openBall v 0 1) = openBall v 0 1 := by
        rw [Set.image_image]
        have hφψ : (fun y : K => (c + b * y - c) * b⁻¹) = id := by
          funext y
          have h1 : c + b * y - c = b * y := by ring
          rw [h1]
          show (b * y) * b⁻¹ = y
          rw [mul_comm b y, mul_assoc, mul_inv_cancel₀ hbne, mul_one]
        rw [hφψ]
        exact Set.image_id _
      have hval : ∀ i ∈ s, IsValBall v ((fun y : K => (y - c) * b⁻¹) '' D i) := by
        intro i hi
        rw [hpsi b c]
        exact isValBall_affine_image v (inv_ne_zero hbne) (-(c * b⁻¹)) (hD i hi)
      have hsubm : ∀ i ∈ s, ((fun y : K => (y - c) * b⁻¹) '' D i) ⊆ openBall v 0 1 := by
        intro i hi
        rw [← himg]
        exact Set.image_mono (hDsub i hi)
      have hnem : ∀ i ∈ s, ((fun y : K => (y - c) * b⁻¹) '' D i) ≠ openBall v 0 1 := by
        intro i hi hcon
        apply hDne i hi
        have hthis : (fun y : K => c + b * y) '' ((fun y : K => (y - c) * b⁻¹) '' D i)
            = (fun y : K => c + b * y) '' openBall v 0 1 := by rw [hcon]
        rw [Set.image_image, hcomp b c hbne, Set.image_id] at hthis
        exact hthis
      exact openBall_zero_ne_finite_union_of_isValBall v hnt' s _ hval hsubm hnem hcover'



/-! ## Comparability of balls (Johnson's (2.3)), including the mixed radius cases

Johnson uses "any two balls which intersect are comparable" in the proof of Lemma 2.3.2.  The
closed/closed and open/open cases are `closedBall_subset_or_subset` and
`openBall_subset_or_subset` above; the mixed cases are proved here.  Which of the two balls is
the smaller one is decided by the comparison of the two radii. -/

/-- A closed ball of smaller radius inside an open ball. -/
theorem closedBall_subset_openBall (v : Valuation K Γ₀) {c d : K} {a b : K}
    (hcd : v (c - d) < v b) (ha : v a < v b) :
    closedBall v c (v a) ⊆ openBall v d (v b) := by
  intro x hx
  simp only [mem_closedBall] at hx
  simp only [mem_openBall]
  exact lt_of_le_of_lt (val_sub_le_max v x c d) (max_lt (lt_of_le_of_lt hx ha) hcd)

/-- An open ball inside a closed ball. -/
theorem openBall_subset_closedBall (v : Valuation K Γ₀) {c d : K} {a b : K}
    (hcd : v (c - d) ≤ v b) (ha : v a ≤ v b) :
    openBall v c (v a) ⊆ closedBall v d (v b) := by
  intro x hx
  simp only [mem_openBall] at hx
  simp only [mem_closedBall]
  exact le_trans (val_sub_le_max v x c d) (max_le (le_of_lt (lt_of_lt_of_le hx ha)) hcd)

/-- The value of `c - d` is at most the larger of two radii, given a common point `z`. -/
theorem val_sub_le_max_of_mem (v : Valuation K Γ₀) {z c d : K} {a b : K}
    (hz₁ : v (z - c) ≤ v a) (hz₂ : v (z - d) ≤ v b) :
    v (c - d) ≤ max (v a) (v b) := by
  have h1 : v (c - z) ≤ v a := by
    rw [show c - z = -(z - c) by ring, Valuation.map_neg]; exact hz₁
  exact le_trans (val_sub_le_max v c z d) (max_le_max h1 hz₂)

/-- **Johnson (2.3).** Two balls with radii in `vK` that meet are comparable. -/
theorem isValBall_subset_or_subset (v : Valuation K Γ₀) {B₁ B₂ : Set K}
    (h₁ : IsValBall v B₁) (h₂ : IsValBall v B₂) (h : (B₁ ∩ B₂).Nonempty) :
    B₁ ⊆ B₂ ∨ B₂ ⊆ B₁ := by
  obtain ⟨z, hz₁, hz₂⟩ := h
  cases h₁ with
  | univ => exact Or.inr (Set.subset_univ _)
  | singleton c =>
    rw [Set.mem_singleton_iff] at hz₁
    subst hz₁
    cases h₂ with
    | univ => exact Or.inl (Set.subset_univ _)
    | singleton d => exact Or.inl (Set.singleton_subset_iff.mpr hz₂)
    | closed d b => exact Or.inl (Set.singleton_subset_iff.mpr hz₂)
    | openball d b => exact Or.inl (Set.singleton_subset_iff.mpr hz₂)
  | closed c a =>
    cases h₂ with
    | univ => exact Or.inl (Set.subset_univ _)
    | singleton d =>
      rw [Set.mem_singleton_iff] at hz₂
      subst hz₂
      exact Or.inr (Set.singleton_subset_iff.mpr hz₁)
    | closed d b => exact closedBall_subset_or_subset v ⟨z, hz₁, hz₂⟩
    | openball d b =>
      simp only [mem_closedBall] at hz₁
      simp only [mem_openBall] at hz₂
      rcases lt_or_ge (v a) (v b) with hab | hab
      · left
        have h2 : v (z - d) < v b := hz₂
        refine closedBall_subset_openBall v ?_ hab
        have h3 : v (c - z) < v b := by
          rw [show c - z = -(z - c) by ring, Valuation.map_neg]
          exact lt_of_le_of_lt hz₁ hab
        exact lt_of_le_of_lt (val_sub_le_max v c z d) (max_lt h3 h2)
      · right
        have h2 : v (z - d) < v b := hz₂
        refine openBall_subset_closedBall (v := v) (c := d) (d := c) (a := b) (b := a) ?_ hab
        have h1 : v (d - z) ≤ v a := by
          rw [show d - z = -(z - d) by ring, Valuation.map_neg]
          exact le_trans h2.le hab
        have h3 : v (z - c) ≤ v a := hz₁
        exact le_trans (val_sub_le_max v d z c) (max_le h1 h3)
  | openball c a =>
    simp only [mem_openBall] at hz₁
    cases h₂ with
    | univ => exact Or.inl (Set.subset_univ _)
    | singleton d =>
      rw [Set.mem_singleton_iff] at hz₂
      subst hz₂
      exact Or.inr (Set.singleton_subset_iff.mpr hz₁)
    | closed d b =>
      simp only [mem_closedBall] at hz₂
      rcases le_or_gt (v a) (v b) with hab | hab
      · left
        refine openBall_subset_closedBall (v := v) ?_ hab
        have h := val_sub_le_max_of_mem v (z := z) hz₁.le hz₂
        rwa [max_eq_right hab] at h
      · right
        refine closedBall_subset_openBall (v := v) (c := d) (d := c) (a := b) (b := a) ?_ hab
        have h1 : v (d - z) < v a := by
          rw [show d - z = -(z - d) by ring, Valuation.map_neg]
          exact lt_of_le_of_lt hz₂ hab
        have h2 : v (z - c) < v a := hz₁
        exact lt_of_le_of_lt (val_sub_le_max v d z c) (max_lt h1 h2)
    | openball d b => exact openBall_subset_or_subset v ⟨z, hz₁, hz₂⟩



/-! ## Johnson, Lemma 2.3.2: Boolean combinations of balls are unions of swiss cheeses

A *swiss cheese* is `B₀ \ ⋃_{j} B j` with each `B j` a subball of `B₀`.  Johnson's Lemma 2.3.2
says that a Boolean combination of balls is a finite union of swiss cheeses.  The proof goes
through the cells of the pattern of balls containing a point: each cell is an intersection of
balls minus a union of the remaining balls, and by comparability (2.3) it collapses to a swiss
cheese (or is empty). -/

section Lemma232

variable {ι : Type*}

/-- Membership in a finite intersection of sets. -/
theorem mem_iInter_finset (b : ι → Set K) (S : Finset ι) (x : K) :
    x ∈ (⋂ i ∈ S, b i) ↔ ∀ i ∈ S, x ∈ b i := by
  simp

/-- Membership in a finite union of sets. -/
theorem mem_iUnion_finset (b : ι → Set K) (S : Finset ι) (x : K) :
    x ∈ (⋃ i ∈ S, b i) ↔ ∃ i ∈ S, x ∈ b i := by
  simp

/-- A nonempty finite intersection of balls of `vK`-radius is one of them. -/
theorem exists_mem_of_iInter_finset [DecidableEq ι] (v : Valuation K Γ₀)
    {b : ι → Set K} (hb : ∀ i, IsValBall v (b i)) {S : Finset ι} (hS : S.Nonempty)
    (hne : (⋂ i ∈ S, b i).Nonempty) :
    ∃ j ∈ S, (⋂ i ∈ S, b i) = b j := by
  classical
  revert hS hne
  induction S using Finset.induction_on with
  | empty => intro hS; exact absurd hS Finset.not_nonempty_empty
  | insert i S hiS ih =>
    intro hS hne
    by_cases hS' : S.Nonempty
    · have hne' : (⋂ k ∈ S, b k).Nonempty := by
        obtain ⟨x, hx⟩ := hne
        have hx' : ∀ k : ι, k ∈ insert i S → x ∈ b k := by
          simpa only [Set.mem_iInter] using hx
        exact ⟨x, (mem_iInter_finset b S x).mpr fun k hk =>
          hx' k (Finset.mem_insert_of_mem hk)⟩
      obtain ⟨j, hjS, hj⟩ := ih hS' hne'
      have hinter : (⋂ k ∈ insert i S, b k) = b i ∩ b j := by
        rw [show (⋂ k ∈ insert i S, b k) = b i ∩ (⋂ k ∈ S, b k) from by
          ext x; simp [Finset.mem_insert], hj]
      have hne2 : (b i ∩ b j).Nonempty := hinter ▸ hne
      rcases isValBall_subset_or_subset v (hb i) (hb j) hne2 with h | h
      · exact ⟨i, Finset.mem_insert_self i S, by rw [hinter, Set.inter_eq_left.mpr h]⟩
      · exact ⟨j, Finset.mem_insert_of_mem hjS, by rw [hinter, Set.inter_eq_right.mpr h]⟩
    · have hSe : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS'
      subst hSe
      refine ⟨i, Finset.mem_singleton_self i, ?_⟩
      simp

/-- `D` is a finite Boolean combination of balls of `vK`-radius: a Boolean function of the
pattern of balls containing a point. -/
def IsBoolCombOfBalls (v : Valuation K Γ₀) (D : Set K) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (b : ι → Set K) (t : Set ι → Bool),
    (∀ i, IsValBall v (b i)) ∧ ∀ x : K, (x ∈ D ↔ t {i | x ∈ b i} = true)

/-- The cell of a finite set of balls: the points lying in exactly the balls indexed by `S`. -/
def cell [Fintype ι] [DecidableEq ι] (b : ι → Set K) (S : Finset ι) : Set K :=
  (⋂ i ∈ S, b i) \ (⋃ i ∈ Sᶜ, b i)

/-- The cell of `S`, when the Boolean function accepts the pattern `S`, and `∅` otherwise. -/
noncomputable def cellIf [Fintype ι] [DecidableEq ι] (b : ι → Set K) (t : Set ι → Bool)
    (S : Finset ι) : Set K := by
  classical
  exact if t (S : Set ι) = true then cell b S else ∅

theorem mem_cell [Fintype ι] [DecidableEq ι] {b : ι → Set K} {S : Finset ι} {x : K} :
    x ∈ cell b S ↔ ∀ i, (x ∈ b i ↔ i ∈ S) := by
  classical
  constructor
  · intro h
    have h1 : ∀ k ∈ S, x ∈ b k := (mem_iInter_finset b S x).mp h.1
    have h2 : ∀ k, k ∉ S → x ∉ b k := by
      intro k hk hx
      exact h.2 ((mem_iUnion_finset b (Sᶜ) x).mpr ⟨k, by simpa using hk, hx⟩)
    exact fun i => ⟨fun hx => by_contra fun hcon => h2 i hcon hx, fun hi => h1 i hi⟩
  · intro h
    refine ⟨(mem_iInter_finset b S x).mpr fun k hk => (h k).mpr hk, ?_⟩
    intro hx
    obtain ⟨k, hk, hkx⟩ := (mem_iUnion_finset b (Sᶜ) x).mp hx
    have hk' : k ∉ S := by simpa using hk
    exact hk' ((h k).mp hkx)

/-- **The cell decomposition behind Lemma 2.3.2.** A Boolean combination of the balls `b` is the
union of the cells whose pattern the Boolean function accepts. -/
theorem eq_iUnion_cell [Fintype ι] [DecidableEq ι] (b : ι → Set K) (t : Set ι → Bool) :
    {x : K | t {i | x ∈ b i} = true} = ⋃ S : Finset ι, cellIf b t S := by
  classical
  ext x
  constructor
  · intro hx
    refine Set.mem_iUnion.mpr ⟨Finset.univ.filter (fun i => x ∈ b i), ?_⟩
    have hcoe : ((Finset.univ.filter (fun i => x ∈ b i) : Finset ι) : Set ι) = {i | x ∈ b i} := by
      ext i; simp
    have ht : t ((Finset.univ.filter (fun i => x ∈ b i) : Finset ι) : Set ι) = true := by
      rw [hcoe]; exact hx
    show x ∈ cellIf b t (Finset.univ.filter (fun i => x ∈ b i))
    rw [cellIf, if_pos ht]
    rw [mem_cell]
    intro i
    simp
  · intro hx
    obtain ⟨S, hS⟩ := Set.mem_iUnion.mp hx
    by_cases ht : t (S : Set ι) = true
    · rw [cellIf, if_pos ht] at hS
      have hpat : (S : Set ι) = {i | x ∈ b i} := by
        ext i
        exact (mem_cell.mp hS i).symm
      show t {i | x ∈ b i} = true
      rw [← hpat]
      exact ht
    · rw [cellIf, if_neg ht] at hS
      exact absurd hS (Set.notMem_empty x)

end Lemma232


end Johnson


/-!
# Johnson §2.3, Lemmas 2.3.3 and 2.3.8, in the `Valuation` framework

This section adds to `QE/Johnson23_valuation.lean` (copied verbatim above) the two-field part of
Johnson's §2.3 that the 1-existential-closedness proof needs.

`K` is a subfield of a valued field `L` (`v : Valuation L Γ₀`).  A *`K`-ball in `L`* is one of
`{x : v (x - c) ≤ v b}`, `{x : v (x - c) < v b}` with `c, b ∈ K`, a singleton `{c}` with `c ∈ K`,
or `L` itself: `IsValBallIn v K B`.

* `ValueGroupDLO v K` says the value group of `K` is a dense linear order without endpoints
  (a hypothesis, discharged in `valueGroupDLO_of_isAlgClosed` for `K` algebraically closed and
  nontrivially valued).
* `lemma_2_3_3` : `B₁ ⊊ B₂` for `K`-balls implies `B₁ ∩ K ⊊ B₂ ∩ K` (needs `ValueGroupDLO`).
* `lemma_2_3_8` : a nonempty swiss cheese `B₀ \ ⋃ᵢ Bᵢ` of `K`-balls with `Bᵢ ⊆ B₀` meets `K`
  (needs `K` algebraically closed and nontrivially valued, via Lemma 2.3.7
  `ne_finite_union_of_proper_subballs` for `K`).

These are the ingredients that combine with the swiss-cheese decomposition of a Boolean
combination of `K`-balls (Lemma 2.3.2) and with Lemma 2.3.1 to show that models of ACVF are
1-existentially closed in every valued field extension.
-/

namespace Johnson

open Set

variable {L : Type*} [Field L] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- The value group of `K`, seen inside `L`, is a dense linear order without endpoints. -/
def ValueGroupDLO (v : Valuation L Γ₀) (K : Subfield L) : Prop :=
  (∀ a ∈ K, a ≠ 0 → ∃ b ∈ K, b ≠ 0 ∧ v a < v b) ∧
  (∀ a ∈ K, a ≠ 0 → ∃ b ∈ K, b ≠ 0 ∧ v b < v a) ∧
  (∀ a ∈ K, ∀ c ∈ K, a ≠ 0 → c ≠ 0 → v a < v c →
    ∃ b ∈ K, b ≠ 0 ∧ v a < v b ∧ v b < v c)

/-! ## Elementary consequences of density

For a subfield `K ⊆ L` with dense value group, we produce elements of `K` with prescribed value
bounds.  All the witnesses are in `K`, which is what Lemma 2.3.3 needs. -/

/-- Nonvanishing of an element of a subfield, seen in the ambient field. -/
theorem subfield_coe_ne_zero_iff {K : Subfield L} {x : ↥K} : (x : L) ≠ 0 ↔ x ≠ 0 := by
  constructor
  · intro h h0
    exact h (by rw [h0]; rfl)
  · intro h h0
    exact h (Subtype.ext h0)

/-- Some nonzero element of `K` has value below `1`. -/
theorem exists_val_lt_one (v : Valuation L Γ₀) (K : Subfield L) (hDLO : ValueGroupDLO v K) :
    ∃ u ∈ K, u ≠ 0 ∧ v u < 1 := by
  obtain ⟨b, hbK, hb0, hb⟩ := hDLO.2.1 1 K.one_mem one_ne_zero
  rw [map_one] at hb
  exact ⟨b, hbK, hb0, hb⟩

/-- Some element of `K` has value above `v a`. -/
theorem exists_val_gt (v : Valuation L Γ₀) (K : Subfield L) (hDLO : ValueGroupDLO v K)
    {a : L} (ha : a ∈ K) : ∃ t ∈ K, t ≠ 0 ∧ v a < v t := by
  rcases eq_or_ne a 0 with rfl | ha0
  · exact ⟨1, K.one_mem, one_ne_zero, by rw [map_zero, map_one]; exact zero_lt_one⟩
  · exact hDLO.1 a ha ha0

/-- Between the values of two elements of `K` there is the value of an element of `K`. -/
theorem exists_val_strict_between (v : Valuation L Γ₀) (K : Subfield L)
    (hDLO : ValueGroupDLO v K) {a b : L} (ha : a ∈ K) (hb : b ∈ K) (h : v a < v b) :
    ∃ t ∈ K, t ≠ 0 ∧ v a < v t ∧ v t < v b := by
  rcases eq_or_ne a 0 with rfl | ha0
  · obtain ⟨u, huK, hu0, hu⟩ := exists_val_lt_one v K hDLO
    have hb0 : b ≠ 0 := by
      rintro rfl
      rw [map_zero] at h
      exact absurd h (not_lt.mpr zero_le)
    have hvb : 0 < v b := pos_iff_ne_zero.mpr (v.ne_zero_iff.mpr hb0)
    have hvu : 0 < v u := pos_iff_ne_zero.mpr (v.ne_zero_iff.mpr hu0)
    refine ⟨b * u, K.mul_mem hb huK, mul_ne_zero hb0 hu0, ?_, ?_⟩
    · rw [map_mul, map_zero]
      exact pos_iff_ne_zero.mpr (mul_ne_zero (ne_of_gt hvb) (ne_of_gt hvu))
    · rw [map_mul]
      calc v b * v u < v b * 1 := mul_lt_mul_of_pos_left hu hvb
        _ = v b := mul_one _
  · have hb0 : b ≠ 0 := by
      rintro rfl
      rw [map_zero] at h
      exact absurd h (not_lt.mpr zero_le)
    exact hDLO.2.2 a ha b hb ha0 hb0 h

/-- A value above both `v a` and `v a'`, realised in `K`. -/
theorem exists_val_gt_both (v : Valuation L Γ₀) (K : Subfield L) (hDLO : ValueGroupDLO v K)
    {a a' : L} (ha : a ∈ K) (ha' : a' ∈ K) :
    ∃ t ∈ K, t ≠ 0 ∧ v a < v t ∧ v a' < v t := by
  rcases le_total (v a) (v a') with h | h
  · obtain ⟨t, htK, ht0, ht⟩ := exists_val_gt v K hDLO ha'
    exact ⟨t, htK, ht0, lt_of_le_of_lt h ht, ht⟩
  · obtain ⟨t, htK, ht0, ht⟩ := exists_val_gt v K hDLO ha
    exact ⟨t, htK, ht0, ht, lt_of_le_of_lt h ht⟩

/-- A value above both `v a`, `v a'` and below `v b`, realised in `K`. -/
theorem exists_val_between_gt_both (v : Valuation L Γ₀) (K : Subfield L)
    (hDLO : ValueGroupDLO v K) {a a' b : L} (ha : a ∈ K) (ha' : a' ∈ K) (hb : b ∈ K)
    (h : v a < v b) (h' : v a' < v b) :
    ∃ t ∈ K, t ≠ 0 ∧ v a < v t ∧ v a' < v t ∧ v t < v b := by
  rcases le_total (v a) (v a') with hle | hle
  · obtain ⟨t, htK, ht0, ht1, ht2⟩ := exists_val_strict_between v K hDLO ha' hb h'
    exact ⟨t, htK, ht0, lt_of_le_of_lt hle ht1, ht1, ht2⟩
  · obtain ⟨t, htK, ht0, ht1, ht2⟩ := exists_val_strict_between v K hDLO ha hb h
    exact ⟨t, htK, ht0, ht1, lt_of_le_of_lt hle ht1, ht2⟩

/-- There is an element of `K` with value in `(0, v b)` and different from `d`. -/
theorem exists_val_pos_lt_avoid (v : Valuation L Γ₀) (K : Subfield L)
    (hDLO : ValueGroupDLO v K) {b : L} (hb : b ∈ K) (hvb : 0 < v b) {d : Γ₀} :
    ∃ t ∈ K, t ≠ 0 ∧ 0 < v t ∧ v t < v b ∧ v t ≠ d := by
  obtain ⟨t, htK, ht0, ht1, ht2⟩ := exists_val_strict_between v K hDLO (a := 0) K.zero_mem hb
    (by rwa [map_zero])
  rw [map_zero] at ht1
  rcases eq_or_ne (v t) d with htd | htd
  · obtain ⟨t', ht'K, ht'0, ht'1, ht'2⟩ := exists_val_strict_between v K hDLO htK hb ht2
    exact ⟨t', ht'K, ht'0, lt_trans ht1 ht'1, ht'2, by rw [← htd]; exact ne_of_gt ht'1⟩
  · exact ⟨t, htK, ht0, ht1, ht2, htd⟩

/-- **No cancellation.**  If `v a < v b` then `v (a + b) = v b`. -/
theorem val_add_eq_right (v : Valuation L Γ₀) {a b : L} (h : v a < v b) : v (a + b) = v b := by
  have hle : v (a + b) ≤ v b := le_trans (map_add_le_max v a b) (max_le h.le le_rfl)
  refine le_antisymm hle (le_of_not_gt ?_)
  intro hlt
  have h1 : v b ≤ max (v (a + b)) (v a) := by
    have h3 : b = (a + b) + -a := by ring
    rw [h3]
    simpa using map_add_le_max (f := v) (a + b) (-a)
  exact absurd (max_lt hlt h) (not_lt.mpr h1)

/-! ## `K`-balls in `L` -/

/-- The balls in `L` with centre and radius in `K`: `{x : v (x - c) ≤ v b}`,
`{x : v (x - c) < v b}` for `c, b ∈ K`, the singletons `{c}` with `c ∈ K`, and `L` itself. -/
inductive IsValBallIn (v : Valuation L Γ₀) (K : Subfield L) : Set L → Prop
  | closed (c b : L) (hc : c ∈ K) (hb : b ∈ K) : IsValBallIn v K (closedBall v c (v b))
  | openball (c b : L) (hc : c ∈ K) (hb : b ∈ K) : IsValBallIn v K (openBall v c (v b))
  | singleton (c : L) (hc : c ∈ K) : IsValBallIn v K {c}
  | univ : IsValBallIn v K Set.univ

/-- A nonempty `K`-ball has a point in `K`. -/
theorem IsValBallIn.exists_mem_of_nonempty {K : Subfield L} {B : Set L}
    (h : IsValBallIn (Γ₀ := Γ₀) v K B) (hne : B.Nonempty) : ∃ x ∈ K, x ∈ B := by
  cases h with
  | closed c b hc _ => exact ⟨c, hc, closedBall_self_mem v c (v b)⟩
  | openball c b hc _ =>
    rcases eq_or_ne (v b) 0 with h0 | h0
    · rw [h0, openBall_zero_eq_empty] at hne
      exact absurd hne Set.not_nonempty_empty
    · exact ⟨c, hc, openBall_self_mem h0⟩
  | singleton c hc => exact ⟨c, hc, rfl⟩
  | univ => exact ⟨0, K.zero_mem, Set.mem_univ 0⟩

/-- The trace of a `K`-ball on `K` is a ball of the valued field `K`. -/
theorem IsValBallIn.preimage_subtype {K : Subfield L} {B : Set L}
    (h : IsValBallIn (Γ₀ := Γ₀) v K B) :
    IsValBall (Γ₀ := Γ₀) (v.comap K.subtype) (K.subtype ⁻¹' B) := by
  cases h with
  | closed c b hc hb =>
    have h1 : K.subtype ⁻¹' closedBall v c (v b)
        = closedBall (v.comap K.subtype) ⟨c, hc⟩ ((v.comap K.subtype) ⟨b, hb⟩) := by
      ext x
      simp [mem_closedBall, Valuation.comap_apply]
    rw [h1]
    exact IsValBall.closed (Γ₀ := Γ₀) (K := ↥K) ⟨c, hc⟩ ⟨b, hb⟩
  | openball c b hc hb =>
    have h1 : K.subtype ⁻¹' openBall v c (v b)
        = openBall (v.comap K.subtype) ⟨c, hc⟩ ((v.comap K.subtype) ⟨b, hb⟩) := by
      ext x
      simp [mem_openBall, Valuation.comap_apply]
    rw [h1]
    exact IsValBall.openball (Γ₀ := Γ₀) (K := ↥K) ⟨c, hc⟩ ⟨b, hb⟩
  | singleton c hc =>
    have h1 : K.subtype ⁻¹' ({c} : Set L) = {⟨c, hc⟩} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
    rw [h1]
    exact IsValBall.singleton (Γ₀ := Γ₀) (K := ↥K) ⟨c, hc⟩
  | univ => exact IsValBall.univ

/-- A `K`-ball that strictly contains a `K`-point has another `K`-point. -/
theorem IsValBallIn.exists_mem_ne_of_singleton_subset (v : Valuation L Γ₀) (K : Subfield L)
    (hDLO : ValueGroupDLO v K) {B : Set L} (hB : IsValBallIn (Γ₀ := Γ₀) v K B) {c : L} (hc : c ∈ K)
    (hsub : ({c} : Set L) ⊆ B) (hne : ({c} : Set L) ≠ B) :
    ∃ x ∈ K, x ∈ B ∧ x ≠ c := by
  cases hB with
  | univ => exact ⟨c + 1, K.add_mem hc K.one_mem, Set.mem_univ _, by simp⟩
  | closed c₂ b₂ hc₂ hb₂ =>
    have hvb : v b₂ ≠ 0 := by
      intro h0
      apply hne
      have hmem : c ∈ closedBall v c₂ (v b₂) := hsub (Set.mem_singleton c)
      rw [h0, closedBall_zero_eq_singleton, Set.mem_singleton_iff] at hmem
      rw [h0, closedBall_zero_eq_singleton, ← hmem]
    have hb₂0 : b₂ ≠ 0 := v.ne_zero_iff.mp hvb
    rcases eq_or_ne c₂ c with hce | hne'
    · subst hce
      refine ⟨c₂ + b₂, K.add_mem hc₂ hb₂, ?_, ?_⟩
      · rw [mem_closedBall, show c₂ + b₂ - c₂ = b₂ by ring]
      · intro hcon
        exact hb₂0 (by simpa using hcon)
    · exact ⟨c₂, hc₂, closedBall_self_mem v c₂ (v b₂), hne'⟩
  | openball c₂ b₂ hc₂ hb₂ =>
    have hvb : v b₂ ≠ 0 := by
      intro h0
      have h1 := hsub (Set.mem_singleton c)
      rw [h0, openBall_zero_eq_empty] at h1
      exact absurd h1 (notMem_empty c)
    rcases eq_or_ne c₂ c with hce | hne'
    · subst hce
      obtain ⟨t, htK, ht0, -, ht2, -⟩ :=
        exists_val_pos_lt_avoid v K hDLO hb₂ (pos_iff_ne_zero.mpr hvb) (d := (0 : Γ₀))
      refine ⟨c₂ + t, K.add_mem hc₂ htK, ?_, ?_⟩
      · rw [mem_openBall, show c₂ + t - c₂ = t by ring]
        exact ht2
      · intro hcon
        exact ht0 (by simpa using hcon)
    · exact ⟨c₂, hc₂, openBall_self_mem hvb, hne'⟩
  | singleton c₂ hc₂ =>
    exfalso
    apply hne
    have h1 : c = c₂ := by simpa using hsub (Set.mem_singleton c)
    rw [← h1]

/-! ## Lemma 2.3.3: strict containment is detected on `K`

The proof is the case analysis of the four possible shapes of the two balls; in each case we
either use the centre of the bigger ball, or the centre of the smaller ball moved by an element of
`K` whose value we choose in a suitable interval (here density of the value group of `K` is used).
-/

/-- **Johnson (2.3.3), closed ball inside closed ball.** -/
theorem diff_closed_closed (v : Valuation L Γ₀) (K : Subfield L)
    (hDLO : ValueGroupDLO v K) {c₁ b₁ c₂ b₂ : L} (h1c : c₁ ∈ K) (h1b : b₁ ∈ K)
    (h2c : c₂ ∈ K) (h2b : b₂ ∈ K)
    (hsub : closedBall v c₁ (v b₁) ⊆ closedBall v c₂ (v b₂))
    (hne : closedBall v c₁ (v b₁) ≠ closedBall v c₂ (v b₂)) :
    ∃ x ∈ K, x ∈ closedBall v c₂ (v b₂) ∧ x ∉ closedBall v c₁ (v b₁) := by
  rcases lt_or_ge (v b₁) (v (c₁ - c₂)) with hd | hd
  · refine ⟨c₂, h2c, closedBall_self_mem v c₂ (v b₂), ?_⟩
    rw [mem_closedBall, show c₂ - c₁ = -(c₁ - c₂) by ring, Valuation.map_neg]
    exact not_le.mpr hd
  · have hR : v b₁ < v b₂ := by
      by_contra hcon
      push Not at hcon
      apply hne
      refine Subset.antisymm hsub ?_
      intro y hy
      rw [mem_closedBall] at hy ⊢
      refine le_trans (val_sub_le_max v y c₂ c₁) (max_le ?_ ?_)
      · exact le_trans hy hcon
      · rw [show c₂ - c₁ = -(c₁ - c₂) by ring, Valuation.map_neg]; exact hd
    obtain ⟨t, htK, -, ht1, ht2, ht3⟩ :=
      exists_val_between_gt_both v K hDLO (a := b₁) (a' := c₁ - c₂) h1b (K.sub_mem h1c h2c) h2b
        hR (lt_of_le_of_lt hd hR)
    refine ⟨c₁ + t, K.add_mem h1c htK, ?_, ?_⟩
    · rw [mem_closedBall]
      refine le_trans (val_sub_le_max v (c₁ + t) c₁ c₂)
        (max_le (le_of_lt ?_) (le_of_lt (lt_trans ht2 ht3)))
      rw [show c₁ + t - c₁ = t by ring]
      exact ht3
    · rw [mem_closedBall, not_le, show c₁ + t - c₁ = t by ring]
      exact ht1

/-- **Johnson (2.3.3), closed ball inside open ball.** -/
theorem diff_closed_open (v : Valuation L Γ₀) (K : Subfield L)
    (hDLO : ValueGroupDLO v K) {c₁ b₁ c₂ b₂ : L} (h1c : c₁ ∈ K) (h1b : b₁ ∈ K)
    (h2c : c₂ ∈ K) (h2b : b₂ ∈ K)
    (hsub : closedBall v c₁ (v b₁) ⊆ openBall v c₂ (v b₂))
    (_hne : closedBall v c₁ (v b₁) ≠ openBall v c₂ (v b₂)) :
    ∃ x ∈ K, x ∈ openBall v c₂ (v b₂) ∧ x ∉ closedBall v c₁ (v b₁) := by
  have hb₂0 : v b₂ ≠ 0 := by
    intro h0
    rw [h0, openBall_zero_eq_empty] at hsub
    have : c₁ ∈ (∅ : Set L) := hsub (closedBall_self_mem v c₁ (v b₁))
    exact absurd this (notMem_empty c₁)
  rcases lt_or_ge (v b₁) (v (c₁ - c₂)) with hd | hd
  · refine ⟨c₂, h2c, openBall_self_mem hb₂0, ?_⟩
    rw [mem_closedBall, not_le, show c₂ - c₁ = -(c₁ - c₂) by ring, Valuation.map_neg]
    exact hd
  · have hR : v b₁ < v b₂ := by
      by_contra hcon
      push Not at hcon
      apply _hne
      refine Subset.antisymm hsub ?_
      intro y hy
      rw [mem_openBall] at hy
      rw [mem_closedBall]
      refine le_trans (val_sub_le_max v y c₂ c₁) (max_le ?_ ?_)
      · exact le_trans hy.le hcon
      · rw [show c₂ - c₁ = -(c₁ - c₂) by ring, Valuation.map_neg]; exact hd
    obtain ⟨t, htK, -, ht1, ht2, ht3⟩ :=
      exists_val_between_gt_both v K hDLO (a := b₁) (a' := c₁ - c₂) h1b (K.sub_mem h1c h2c) h2b
        hR (lt_of_le_of_lt hd hR)
    refine ⟨c₁ + t, K.add_mem h1c htK, ?_, ?_⟩
    · rw [mem_openBall]
      refine lt_of_le_of_lt (val_sub_le_max v (c₁ + t) c₁ c₂)
        (max_lt (by rw [show c₁ + t - c₁ = t by ring]; exact ht3) (lt_trans ht2 ht3))
    · rw [mem_closedBall, not_le, show c₁ + t - c₁ = t by ring]
      exact ht1

/-- **Johnson (2.3.3), open ball inside closed ball.** -/
theorem diff_open_closed (v : Valuation L Γ₀) (K : Subfield L)
    (hDLO : ValueGroupDLO v K) {c₁ b₁ c₂ b₂ : L} (h1c : c₁ ∈ K) (h1b : b₁ ∈ K)
    (h2c : c₂ ∈ K) (h2b : b₂ ∈ K)
    (hsub : openBall v c₁ (v b₁) ⊆ closedBall v c₂ (v b₂))
    (_hne : openBall v c₁ (v b₁) ≠ closedBall v c₂ (v b₂)) :
    ∃ x ∈ K, x ∈ closedBall v c₂ (v b₂) ∧ x ∉ openBall v c₁ (v b₁) := by
  rcases eq_or_ne (v b₁) 0 with hb₁ | hb₁
  · refine ⟨c₂, h2c, closedBall_self_mem v c₂ (v b₂), ?_⟩
    rw [hb₁, openBall_zero_eq_empty]
    exact notMem_empty c₂
  · rcases le_or_gt (v b₁) (v (c₁ - c₂)) with hd | hd
    · refine ⟨c₂, h2c, closedBall_self_mem v c₂ (v b₂), ?_⟩
      rw [mem_openBall, not_lt, show c₂ - c₁ = -(c₁ - c₂) by ring, Valuation.map_neg]
      exact hd
    · have hR : v b₁ ≤ v b₂ := by
        by_contra hcon
        push Not at hcon
        obtain ⟨t, htK, -, ht1, ht2, ht3⟩ :=
          exists_val_between_gt_both v K hDLO (a := b₂) (a' := c₁ - c₂) h2b (K.sub_mem h1c h2c)
            h1b hcon hd
        have hy1 : c₁ + t ∈ openBall v c₁ (v b₁) := by
          rw [mem_openBall, show c₁ + t - c₁ = t by ring]
          exact ht3
        have hy2 : c₁ + t ∉ closedBall v c₂ (v b₂) := by
          rw [mem_closedBall, not_le, show c₁ + t - c₂ = (c₁ - c₂) + t by ring,
            val_add_eq_right v ht2]
          exact ht1
        exact hy2 (hsub hy1)
      refine ⟨c₁ + b₁, K.add_mem h1c h1b, ?_, ?_⟩
      · rw [mem_closedBall]
        refine le_trans (val_sub_le_max v (c₁ + b₁) c₁ c₂) (max_le ?_ ?_)
        · rw [show c₁ + b₁ - c₁ = b₁ by ring]
          exact hR
        · exact le_trans hd.le hR
      · rw [mem_openBall, not_lt, show c₁ + b₁ - c₁ = b₁ by ring]

/-- **Johnson (2.3.3), open ball inside open ball.** -/
theorem diff_open_open (v : Valuation L Γ₀) (K : Subfield L)
    (hDLO : ValueGroupDLO v K) {c₁ b₁ c₂ b₂ : L} (h1c : c₁ ∈ K) (h1b : b₁ ∈ K)
    (h2c : c₂ ∈ K) (h2b : b₂ ∈ K)
    (hsub : openBall v c₁ (v b₁) ⊆ openBall v c₂ (v b₂))
    (hne : openBall v c₁ (v b₁) ≠ openBall v c₂ (v b₂)) :
    ∃ x ∈ K, x ∈ openBall v c₂ (v b₂) ∧ x ∉ openBall v c₁ (v b₁) := by
  rcases eq_or_ne (v b₁) 0 with hb₁ | hb₁
  · have hb₂0 : v b₂ ≠ 0 := by
      intro h0
      exact hne (by simp [hb₁, h0, openBall_zero_eq_empty])
    refine ⟨c₂, h2c, openBall_self_mem hb₂0, ?_⟩
    rw [hb₁, openBall_zero_eq_empty]
    exact notMem_empty c₂
  · rcases le_or_gt (v b₁) (v (c₁ - c₂)) with hd | hd
    · have hb₂0 : v b₂ ≠ 0 := by
        intro h0
        rw [h0, openBall_zero_eq_empty] at hsub
        have : c₁ ∈ (∅ : Set L) := hsub (openBall_self_mem hb₁)
        exact absurd this (notMem_empty c₁)
      refine ⟨c₂, h2c, openBall_self_mem hb₂0, ?_⟩
      rw [mem_openBall, not_lt, show c₂ - c₁ = -(c₁ - c₂) by ring, Valuation.map_neg]
      exact hd
    · have hR : v b₁ < v b₂ := by
        by_contra hcon
        push Not at hcon
        apply hne
        refine Subset.antisymm hsub ?_
        intro y hy
        rw [mem_openBall] at hy ⊢
        refine lt_of_le_of_lt (val_sub_le_max v y c₂ c₁) (max_lt ?_ ?_)
        · exact lt_of_lt_of_le hy hcon
        · rw [show c₂ - c₁ = -(c₁ - c₂) by ring, Valuation.map_neg]; exact hd
      obtain ⟨t, htK, -, ht1, ht2, ht3⟩ :=
        exists_val_between_gt_both v K hDLO (a := b₁) (a' := c₁ - c₂) h1b (K.sub_mem h1c h2c) h2b
          hR (lt_trans hd hR)
      refine ⟨c₁ + t, K.add_mem h1c htK, ?_, ?_⟩
      · rw [mem_openBall]
        refine lt_of_le_of_lt (val_sub_le_max v (c₁ + t) c₁ c₂)
          (max_lt (by rw [show c₁ + t - c₁ = t by ring]; exact ht3) (lt_trans ht2 ht3))
      · rw [mem_openBall, not_lt, show c₁ + t - c₁ = t by ring]
        exact le_of_lt ht1

/-- **Johnson, Lemma 2.3.3.**  If a `K`-ball is strictly contained in another `K`-ball and the
value group of `K` is a dense linear order without endpoints, then there is a `K`-point of the
bigger ball outside the smaller one: `B₁ ⊊ B₂ → B₁ ∩ K ⊊ B₂ ∩ K`. -/
theorem lemma_2_3_3 (v : Valuation L Γ₀) (K : Subfield L) (hDLO : ValueGroupDLO v K)
    {B₁ B₂ : Set L} (h₁ : IsValBallIn (Γ₀ := Γ₀) v K B₁)
    (h₂ : IsValBallIn (Γ₀ := Γ₀) v K B₂)
    (hsub : B₁ ⊆ B₂) (hne : B₁ ≠ B₂) :
    ∃ x ∈ K, x ∈ B₂ ∧ x ∉ B₁ := by
  cases h₂ with
  | univ =>
    cases h₁ with
    | univ => exact absurd rfl hne
    | closed c b hc hb =>
      obtain ⟨t, htK, -, ht⟩ := exists_val_gt v K hDLO hb
      exact ⟨c + t, K.add_mem hc htK, Set.mem_univ _, by
        rw [mem_closedBall, not_le, show c + t - c = t by ring]; exact ht⟩
    | openball c b hc hb =>
      obtain ⟨t, htK, -, ht⟩ := exists_val_gt v K hDLO hb
      exact ⟨c + t, K.add_mem hc htK, Set.mem_univ _, by
        rw [mem_openBall, not_lt, show c + t - c = t by ring]; exact le_of_lt ht⟩
    | singleton c hc => exact ⟨c + 1, K.add_mem hc K.one_mem, Set.mem_univ _, by simp⟩
  | closed c₂ b₂ hc₂ hb₂ =>
    cases h₁ with
    | univ =>
      exfalso
      obtain ⟨t, htK, -, ht⟩ := exists_val_gt v K hDLO hb₂
      have h1 : c₂ + t ∈ closedBall v c₂ (v b₂) := hsub (Set.mem_univ _)
      rw [mem_closedBall, show c₂ + t - c₂ = t by ring] at h1
      exact absurd h1 (not_le.mpr ht)
    | closed c₁ b₁ hc₁ hb₁ => exact diff_closed_closed v K hDLO hc₁ hb₁ hc₂ hb₂ hsub hne
    | openball c₁ b₁ hc₁ hb₁ => exact diff_open_closed v K hDLO hc₁ hb₁ hc₂ hb₂ hsub hne
    | singleton c₁ hc₁ =>
      obtain ⟨x, hxK, hx2, hx1⟩ :=
        IsValBallIn.exists_mem_ne_of_singleton_subset v K hDLO
          (IsValBallIn.closed (Γ₀ := Γ₀) c₂ b₂ hc₂ hb₂) hc₁ hsub hne
      exact ⟨x, hxK, hx2, hx1⟩
  | openball c₂ b₂ hc₂ hb₂ =>
    cases h₁ with
    | univ =>
      exfalso
      obtain ⟨t, htK, -, ht⟩ := exists_val_gt v K hDLO hb₂
      have h1 : c₂ + t ∈ openBall v c₂ (v b₂) := hsub (Set.mem_univ _)
      rw [mem_openBall, show c₂ + t - c₂ = t by ring] at h1
      exact absurd h1 (not_lt.mpr (le_of_lt ht))
    | closed c₁ b₁ hc₁ hb₁ => exact diff_closed_open v K hDLO hc₁ hb₁ hc₂ hb₂ hsub hne
    | openball c₁ b₁ hc₁ hb₁ => exact diff_open_open v K hDLO hc₁ hb₁ hc₂ hb₂ hsub hne
    | singleton c₁ hc₁ =>
      obtain ⟨x, hxK, hx2, hx1⟩ :=
        IsValBallIn.exists_mem_ne_of_singleton_subset v K hDLO
          (IsValBallIn.openball (Γ₀ := Γ₀) c₂ b₂ hc₂ hb₂) hc₁ hsub hne
      exact ⟨x, hxK, hx2, hx1⟩
  | singleton c₂ hc₂ =>
    cases h₁ with
    | univ =>
      exfalso
      have h1 : c₂ + 1 ∈ ({c₂} : Set L) := hsub (Set.mem_univ _)
      rw [Set.mem_singleton_iff] at h1
      exact absurd h1 (by simp)
    | closed c₁ b₁ hc₁ hb₁ =>
      refine ⟨c₂, hc₂, rfl, ?_⟩
      intro hmem
      exact hne (Subset.antisymm hsub (Set.singleton_subset_iff.mpr hmem))
    | openball c₁ b₁ hc₁ hb₁ =>
      refine ⟨c₂, hc₂, rfl, ?_⟩
      intro hmem
      exact hne (Subset.antisymm hsub (Set.singleton_subset_iff.mpr hmem))
    | singleton c₁ hc₁ =>
      refine ⟨c₂, hc₂, rfl, ?_⟩
      intro hmem
      exact hne (by rw [hmem])

/-- **Johnson, Lemma 2.3.3**, in the form `B₁ ∩ K ⊊ B₂ ∩ K`. -/
theorem lemma_2_3_3_inter (v : Valuation L Γ₀) (K : Subfield L) (hDLO : ValueGroupDLO v K)
    {B₁ B₂ : Set L} (h₁ : IsValBallIn (Γ₀ := Γ₀) v K B₁)
    (h₂ : IsValBallIn (Γ₀ := Γ₀) v K B₂)
    (hsub : B₁ ⊆ B₂) (hne : B₁ ≠ B₂) :
    B₁ ∩ (K : Set L) ⊂ B₂ ∩ (K : Set L) := by
  obtain ⟨x, hxK, hx2, hx1⟩ := lemma_2_3_3 v K hDLO h₁ h₂ hsub hne
  exact ⟨fun y hy => ⟨hsub hy.1, hy.2⟩, fun hcon => hx1 (hcon ⟨hx2, hxK⟩).1⟩

/-! ## Lemma 2.3.8: a nonempty swiss cheese of `K`-balls meets `K` -/

/-- The value group of an algebraically closed, nontrivially valued field `K` (as a subfield of
`L`) is a dense linear order without endpoints.  (Johnson, Lemma 2.3.6.) -/
theorem valueGroupDLO_of_isAlgClosed (v : Valuation L Γ₀) (K : Subfield L) [IsAlgClosed ↥K]
    (hnt : ∃ x : ↥K, x ≠ 0 ∧ (v.comap K.subtype) x < 1) : ValueGroupDLO v K := by
  obtain ⟨h1, h2, h3⟩ := valueGroup_dlo (v.comap K.subtype) hnt
  refine ⟨?_, ?_, ?_⟩
  · intro a ha ha0
    obtain ⟨b, hb0, hb⟩ := h1 ⟨a, ha⟩ (fun hh => ha0 (congrArg Subtype.val hh))
    exact ⟨b, b.2, subfield_coe_ne_zero_iff.mpr hb0, by simpa using hb⟩
  · intro a ha ha0
    obtain ⟨b, hb0, hb⟩ := h2 ⟨a, ha⟩ (fun hh => ha0 (congrArg Subtype.val hh))
    exact ⟨b, b.2, subfield_coe_ne_zero_iff.mpr hb0, by simpa using hb⟩
  · intro a ha c hc ha0 hc0 h
    obtain ⟨b, hb0, hb1, hb2⟩ := h3 ⟨a, ha⟩ ⟨c, hc⟩ (fun hh => ha0 (congrArg Subtype.val hh))
      (fun hh => hc0 (congrArg Subtype.val hh)) (by simpa using h)
    exact ⟨b, b.2, subfield_coe_ne_zero_iff.mpr hb0, by simpa using hb1,
      by simpa using hb2⟩

/-- **Johnson, Lemma 2.3.8.**  Let `K` be an algebraically closed, nontrivially valued subfield of
the valued field `L`, and let `B₀`, `Bᵢ` be `K`-balls in `L` with `Bᵢ ⊆ B₀`.  If
`B₀ \ ⋃ᵢ Bᵢ` is nonempty, it meets `K`. -/
theorem lemma_2_3_8 (v : Valuation L Γ₀) (K : Subfield L) [IsAlgClosed ↥K]
    (hnt : ∃ x : ↥K, x ≠ 0 ∧ (v.comap K.subtype) x < 1)
    {ι : Type*} (s : Finset ι) (B : ι → Set L) (B₀ : Set L)
    (hB₀ : IsValBallIn (Γ₀ := Γ₀) v K B₀) (hB : ∀ i ∈ s, IsValBallIn (Γ₀ := Γ₀) v K (B i))
    (hsub : ∀ i ∈ s, B i ⊆ B₀) (hC : (B₀ \ ⋃ i ∈ s, B i).Nonempty) :
    ∃ x ∈ K, x ∈ B₀ ∧ ∀ i ∈ s, x ∉ B i := by
  have hDLO : ValueGroupDLO v K := valueGroupDLO_of_isAlgClosed v K hnt
  have hB₀ne : B₀.Nonempty := ⟨hC.choose, hC.choose_spec.1⟩
  obtain ⟨x₀, hx₀K, hx₀⟩ := hB₀.exists_mem_of_nonempty hB₀ne
  have hproper : ∀ i ∈ s, B i ≠ B₀ := by
    intro i hi heq
    obtain ⟨y, hy1, hy2⟩ := hC
    exact hy2 (Set.mem_iUnion₂.mpr ⟨i, hi, heq.symm ▸ hy1⟩)
  have hne_trace : ∀ i ∈ s, K.subtype ⁻¹' B i ≠ K.subtype ⁻¹' B₀ := by
    intro i hi heq
    obtain ⟨x, hxK, hx2, hx1⟩ := lemma_2_3_3 v K hDLO (hB i hi) hB₀ (hsub i hi) (hproper i hi)
    have hxmem : (⟨x, hxK⟩ : ↥K) ∈ K.subtype ⁻¹' B₀ := hx2
    rw [← heq] at hxmem
    exact hx1 hxmem
  have hnt' : ∃ x : ↥K, 1 < (v.comap K.subtype) x :=
    (exists_ne_zero_val_lt_one_iff (v.comap K.subtype)).mp hnt
  have hnotcover := ne_finite_union_of_proper_subballs (v.comap K.subtype) hnt'
    (IsValBallIn.preimage_subtype hB₀) ⟨⟨x₀, hx₀K⟩, hx₀⟩ s (fun i => K.subtype ⁻¹' B i)
    (fun i hi => IsValBallIn.preimage_subtype (hB i hi))
    (fun i hi y hy => hsub i hi hy) hne_trace
  have hnonempty : (K.subtype ⁻¹' B₀ \ ⋃ i ∈ s, K.subtype ⁻¹' B i).Nonempty := by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    apply hnotcover
    refine Subset.antisymm (Set.sdiff_eq_empty.mp hcon) ?_
    intro y hy
    obtain ⟨i, hi, hyi⟩ := Set.mem_iUnion₂.mp hy
    exact hsub i hi hyi
  obtain ⟨x, hx1, hx2⟩ := hnonempty
  exact ⟨x, x.2, hx1, fun i hi hmem => hx2 (Set.mem_iUnion₂.mpr ⟨i, hi, hmem⟩)⟩

end Johnson







/-!
# Johnson §2.3, Lemmas 2.3.2 + 2.3.8 combined: Boolean combinations of `K`-balls meet `K`

Continues the two-field development above (`K : Subfield L`, `v : Valuation L Γ₀`,
`IsValBallIn v K B` = `K`-ball in `L`).

* `IsValBallIn.subset_or_subset` : two `K`-balls that meet are comparable (Johnson's (2.3)).
* `IsValBallIn.exists_eq_iInter_of_ne` : a nonempty finite intersection of `K`-balls is one of them.
* `cell_eq_swissCheese` : the cell of a finite family of `K`-balls is a swiss cheese of `K`-balls
  (Lemma 2.3.2, cell by cell).
* `exists_mem_K_of_isBoolCombOfKBalls` : a nonempty Boolean combination of `K`-balls in `L` meets
  `K`, for `K` algebraically closed and nontrivially valued (Lemmas 2.3.2 + 2.3.8).  Together with
  Johnson's Lemma 2.3.1 (quantifier-free `K`-definable sets are Boolean combinations of `K`-balls)
  this is precisely 1-existential-closedness of a model of ACVF in every valued field extension.
-/

namespace Johnson

open Set

variable {L : Type*} [Field L] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- A `K`-ball in `L` is a ball in `L`. -/
theorem IsValBallIn.isValBall {K : Subfield L} {B : Set L}
    (h : IsValBallIn (Γ₀ := Γ₀) v K B) : IsValBall (Γ₀ := Γ₀) v B := by
  cases h with
  | closed c b _ _ => exact IsValBall.closed (Γ₀ := Γ₀) (K := L) c b
  | openball c b _ _ => exact IsValBall.openball (Γ₀ := Γ₀) (K := L) c b
  | singleton c _ => exact IsValBall.singleton (Γ₀ := Γ₀) (K := L) c
  | univ => exact IsValBall.univ (Γ₀ := Γ₀) (K := L)

/-- **Johnson (2.3)**: two `K`-balls that meet are comparable. -/
theorem IsValBallIn.subset_or_subset {K : Subfield L} {B₁ B₂ : Set L}
    (h₁ : IsValBallIn (Γ₀ := Γ₀) v K B₁) (h₂ : IsValBallIn (Γ₀ := Γ₀) v K B₂)
    (h : (B₁ ∩ B₂).Nonempty) : B₁ ⊆ B₂ ∨ B₂ ⊆ B₁ :=
  isValBall_subset_or_subset v h₁.isValBall h₂.isValBall h

/-- A nonempty finite intersection of `K`-balls is one of them. -/
theorem IsValBallIn.exists_eq_iInter_of_ne {ι : Type*} [DecidableEq ι] (v : Valuation L Γ₀)
    (K : Subfield L) {b : ι → Set L} (hb : ∀ i, IsValBallIn (Γ₀ := Γ₀) v K (b i))
    {S : Finset ι} (hS : S.Nonempty) (hne : (⋂ i ∈ S, b i).Nonempty) :
    ∃ j ∈ S, (⋂ i ∈ S, b i) = b j := by
  classical
  revert hS hne
  induction S using Finset.induction_on with
  | empty => intro hS; exact absurd hS Finset.not_nonempty_empty
  | insert i S hiS ih =>
    intro hS hne
    by_cases hS' : S.Nonempty
    · have hne' : (⋂ k ∈ S, b k).Nonempty := by
        obtain ⟨x, hx⟩ := hne
        have hx' : ∀ k : ι, k ∈ insert i S → x ∈ b k := by
          simpa only [Set.mem_iInter] using hx
        exact ⟨x, (mem_iInter_finset b S x).mpr fun k hk =>
          hx' k (Finset.mem_insert_of_mem hk)⟩
      obtain ⟨j, hjS, hj⟩ := ih hS' hne'
      have hinter : (⋂ k ∈ insert i S, b k) = b i ∩ b j := by
        rw [show (⋂ k ∈ insert i S, b k) = b i ∩ (⋂ k ∈ S, b k) from by
          ext x; simp [Finset.mem_insert], hj]
      have hne2 : (b i ∩ b j).Nonempty := hinter ▸ hne
      rcases IsValBallIn.subset_or_subset (hb i) (hb j) hne2 with h | h
      · exact ⟨i, Finset.mem_insert_self i S, by rw [hinter, Set.inter_eq_left.mpr h]⟩
      · exact ⟨j, Finset.mem_insert_of_mem hjS, by rw [hinter, Set.inter_eq_right.mpr h]⟩
    · have hSe : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS'
      subst hSe
      refine ⟨i, Finset.mem_singleton_self i, ?_⟩
      simp

/-- **Johnson, Lemma 2.3.2, cell by cell.**  The cell of a finite family of `K`-balls (the points
lying in exactly the balls indexed by `S`) is a swiss cheese of `K`-balls: `B₀ \ ⋃_{i ∈ T} b i`
with `T` a finite set of indices and every `b i ⊆ B₀`. -/
theorem cell_eq_swissCheese {ι : Type*} [Fintype ι] [DecidableEq ι] (v : Valuation L Γ₀)
    (K : Subfield L) {b : ι → Set L} (hb : ∀ i, IsValBallIn (Γ₀ := Γ₀) v K (b i))
    (S : Finset ι) :
    ∃ (B₀ : Set L) (T : Finset ι), IsValBallIn (Γ₀ := Γ₀) v K B₀ ∧
      (∀ i ∈ T, b i ⊆ B₀) ∧ cell b S = B₀ \ ⋃ i ∈ T, b i := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | hS
  · refine ⟨Set.univ, Finset.univ, IsValBallIn.univ, fun i _ => Set.subset_univ _, ?_⟩
    rw [cell]
    ext x
    simp
  · by_cases hint : (⋂ i ∈ S, b i).Nonempty
    · obtain ⟨j, hjS, hj⟩ := IsValBallIn.exists_eq_iInter_of_ne v K hb hS hint
      have hcell : cell b S = b j \ ⋃ i ∈ Sᶜ, b i := by
        rw [cell, hj]
      by_cases hcover : ∃ i ∈ Sᶜ, b j ⊆ b i
      · -- a hole covers `b j`: the cell is empty
        obtain ⟨i₀, hi₀, hi₀'⟩ := hcover
        have hempty : cell b S = (∅ : Set L) := by
          rw [hcell]
          ext x
          constructor
          · rintro ⟨hx, hxn⟩
            exact hxn ((mem_iUnion_finset b Sᶜ x).mpr ⟨i₀, hi₀, hi₀' hx⟩)
          · intro h; exact absurd h (notMem_empty x)
        refine ⟨b j, {j}, hb j, fun i hi => ?_, ?_⟩
        · rw [Finset.mem_singleton] at hi
          rw [hi]
        · rw [hempty]
          ext x
          simp
      · push Not at hcover
        -- every hole meeting `b j` is a subball of it
        refine ⟨b j, Sᶜ.filter (fun i => b i ⊆ b j), hb j, fun i hi =>
          (Finset.mem_filter.mp hi).2, ?_⟩
        have hiff : ∀ x ∈ b j,
            (x ∈ ⋃ i ∈ Sᶜ.filter (fun i => b i ⊆ b j), b i)
              ↔ (x ∈ ⋃ i ∈ Sᶜ, b i) := by
          intro x hxj
          constructor
          · intro hx
            obtain ⟨i, hi, hxi⟩ := (mem_iUnion_finset b _ x).mp hx
            exact (mem_iUnion_finset b Sᶜ x).mpr ⟨i, (Finset.mem_filter.mp hi).1, hxi⟩
          · intro hx
            obtain ⟨i, hi, hxi⟩ := (mem_iUnion_finset b Sᶜ x).mp hx
            have hinter : (b i ∩ b j).Nonempty := ⟨x, hxi, hxj⟩
            rcases IsValBallIn.subset_or_subset (hb i) (hb j) hinter with h | h
            · exact (mem_iUnion_finset b _ x).mpr ⟨i, Finset.mem_filter.mpr ⟨hi, h⟩, hxi⟩
            · exact absurd h (hcover i hi)
        rw [hcell]
        ext x
        exact ⟨fun ⟨h1, h2⟩ => ⟨h1, fun h3 => h2 ((hiff x h1).mp h3)⟩,
               fun ⟨h1, h2⟩ => ⟨h1, fun h3 => h2 ((hiff x h1).mpr h3)⟩⟩
    · -- the intersection is empty, so the cell is empty
      have hempty : cell b S = (∅ : Set L) := by
        by_contra hcon
        apply hint
        obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hcon
        exact ⟨x, Set.sdiff_subset hx⟩
      obtain ⟨j, hjS⟩ := hS
      refine ⟨b j, {j}, hb j, fun i hi => ?_, ?_⟩
      · rw [Finset.mem_singleton] at hi
        rw [hi]
      · rw [hempty]
        ext x
        simp

/-- `D` is a finite Boolean combination of `K`-balls in `L`. -/
def IsBoolCombOfKBalls (v : Valuation L Γ₀) (K : Subfield L) (D : Set L) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (b : ι → Set L) (t : Set ι → Bool),
    (∀ i, IsValBallIn (Γ₀ := Γ₀) v K (b i)) ∧ ∀ x : L, (x ∈ D ↔ t {i | x ∈ b i} = true)

/-- **Johnson, Lemmas 2.3.2 + 2.3.8.**  A nonempty Boolean combination of `K`-balls in `L` meets
`K`, for `K` an algebraically closed, nontrivially valued subfield of the valued field `L`. -/
theorem exists_mem_K_of_isBoolCombOfKBalls {K : Subfield L} [IsAlgClosed ↥K]
    (hnt : ∃ x : ↥K, x ≠ 0 ∧ (v.comap K.subtype) x < 1) {D : Set L}
    (hD : IsBoolCombOfKBalls (Γ₀ := Γ₀) v K D) (hne : D.Nonempty) :
    ∃ x ∈ K, x ∈ D := by
  classical
  obtain ⟨ι, hF, b, t, hb, hD⟩ := hD
  obtain ⟨x, hx⟩ := hne
  -- `x` lies in the cell of its own pattern
  set S : Finset ι := Finset.univ.filter (fun i => x ∈ b i) with hSdef
  have hScoe : ((S : Finset ι) : Set ι) = {i | x ∈ b i} := by
    ext i; simp [hSdef]
  have hxcell : x ∈ cell b S := by
    rw [mem_cell]
    intro i
    simp [hSdef]
  have htS : t (S : Set ι) = true := by
    have h1 : t {i | x ∈ b i} = true := (hD x).mp hx
    rwa [← hScoe] at h1
  obtain ⟨B₀, T, hB₀, hTsub, hcell⟩ := cell_eq_swissCheese v K hb S
  have hnecell : (B₀ \ ⋃ i ∈ T, b i).Nonempty := hcell ▸ ⟨x, hxcell⟩
  obtain ⟨y, hyK, hyB, hyT⟩ :=
    lemma_2_3_8 v K hnt T b B₀ hB₀ (fun i _ => hb i) hTsub hnecell
  refine ⟨y, hyK, ?_⟩
  rw [hD y]
  have hyT' : y ∉ ⋃ i ∈ T, b i := by
    intro hx
    obtain ⟨i, hi, hyi⟩ := (mem_iUnion_finset b T y).mp hx
    exact hyT i hi hyi
  have hSet : {i | y ∈ b i} = (S : Set ι) := by
    ext i
    exact mem_cell.mp (hcell ▸ ⟨hyB, hyT'⟩) i
  rw [hSet]
  exact htS

end Johnson




/-!
# The §2.3 result in the form of a valuation-preserving ring hom `K →+* L`

A `Language.val` embedding `K ↪[val] L` of valued fields is (on the field sort) an injective ring
hom `φ : K →+* L` preserving the valuation predicate: `v x ≤ v y ↔ v' (φ x) ≤ v' (φ y)`.  The
corollary below is the §2.3 end-to-end statement (Johnson 2.3.2 + 2.3.8: a nonempty Boolean
combination of `K`-balls meets `K`) stated directly in those terms, with `K`-balls in `L` being
the balls `{x : v' (x - φ c) ≤ v' (φ b)}` etc., i.e. `IsValBallIn v' φ.fieldRange`.
-/

namespace Johnson

open Set

universe u

/-- **Johnson, Lemmas 2.3.2 + 2.3.8**, for a valuation-preserving ring hom `φ : K →+* L` with `K`
algebraically closed and nontrivially valued: a nonempty Boolean combination of `K`-balls in `L`
meets the image of `K`. -/
theorem exists_mem_image_of_isBoolCombOfBalls {K : Type u} [Field K] {L : Type u} [Field L]
    {Γ Γ' : Type*} [LinearOrderedCommGroupWithZero Γ] [LinearOrderedCommGroupWithZero Γ']
    (φ : K →+* L) (vK : Valuation K Γ) (vL : Valuation L Γ')
    [IsAlgClosed K] (hnt : ∃ x : K, x ≠ 0 ∧ vK x < 1)
    (hφ : ∀ x y : K, vK x ≤ vK y ↔ vL (φ x) ≤ vL (φ y))
    {D : Set L} (hD : IsBoolCombOfKBalls (Γ₀ := Γ') vL φ.fieldRange D)
    (hne : D.Nonempty) : ∃ x : K, φ x ∈ D := by
  haveI : IsAlgClosed ↥φ.fieldRange :=
    IsAlgClosed.of_ringEquiv K ↥φ.fieldRange φ.rangeRestrictFieldEquiv
  have hnt' : ∃ y : ↥φ.fieldRange, y ≠ 0 ∧ (vL.comap (φ.fieldRange).subtype) y < 1 := by
    obtain ⟨x, hx0, hx⟩ := hnt
    refine ⟨⟨φ x, φ.mem_fieldRange_self x⟩, ?_, ?_⟩
    · intro h
      exact hx0 (φ.injective (by simpa using congrArg Subtype.val h))
    · have h1 : ¬ (vL (φ 1) ≤ vL (φ x)) := by
        rw [← hφ 1 x]
        simpa using not_le.mpr hx
      have h2 : vL (φ x) < vL (φ 1) := not_le.mp h1
      simpa using h2
  obtain ⟨y, hyK, hyD⟩ :=
    exists_mem_K_of_isBoolCombOfKBalls (v := vL) (K := φ.fieldRange) hnt' hD hne
  obtain ⟨x, hx⟩ := RingHom.mem_fieldRange.mp hyK
  exact ⟨x, by rw [hx]; exact hyD⟩

end Johnson


/-! ## Axiom audit of the results of this file -/

#print axioms Johnson.exists_pow_val_eq
#print axioms Johnson.lemma_2_3_6
#print axioms Johnson.ne_finite_union_of_proper_subballs
#print axioms Johnson.isValBall_subset_or_subset
#print axioms Johnson.exists_mem_of_iInter_finset
#print axioms Johnson.eq_iUnion_cell
#print axioms Johnson.mem_cell

#print axioms Johnson.lemma_2_3_3
#print axioms Johnson.lemma_2_3_3_inter
#print axioms Johnson.lemma_2_3_8
#print axioms Johnson.valueGroupDLO_of_isAlgClosed
#print axioms Johnson.IsValBallIn.preimage_subtype
#print axioms Johnson.IsValBallIn.subset_or_subset
#print axioms Johnson.IsValBallIn.exists_eq_iInter_of_ne
#print axioms Johnson.cell_eq_swissCheese
#print axioms Johnson.exists_mem_K_of_isBoolCombOfKBalls
#print axioms Johnson.exists_mem_image_of_isBoolCombOfBalls
