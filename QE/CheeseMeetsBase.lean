/-
# Johnson, Lemma 2.3.8 (`CheeseMeetsBase`) in the `IsKBall` framework of `QE/OneEC_val.lean`

A standalone snapshot: it contains private copies of the framework of `QE/OneEC_val.lean`
(`closedBall`, `openBall`, `IsKBall`, `SwissCheese`, `CheeseMeetsBase`) and the ball machinery of
`QE/Johnson23_valuation.lean` (Johnson 2.3.3, 2.3.7, `valueGroup_dlo`, `infinite_residueField`),
and proves

  `cheeseMeetsBase : [IsAlgClosed K] → (f : K →+* N) → (w : Valuation N Γ') →
     (∃ x : K, x ≠ 0 ∧ w (f x) < 1) → CheeseMeetsBase f w`

by transporting Johnson's proof of 2.3.8 from `IsValBallK` to `IsKBall`: every `IsKBall` is an
`IsValBallK` (same constructors), its trace on `K` is an `IsValBall` for `w.comap f`, a proper
inclusion of `K`-balls gives a `K`-point of the difference (2.3.3), and no `K`-ball is a finite
union of proper `K`-subballs (2.3.7).
-/
import Mathlib

namespace ValOneEC

/-! ## Private copy of the framework of `QE/OneEC_val.lean` -/

section Balls

variable {N : Type} [Field N] {Γ' : Type*} [LinearOrderedCommGroupWithZero Γ']

/-- The closed ball of radius `γ` about `c`. -/
def closedBall (w : Valuation N Γ') (c : N) (γ : Γ') : Set N := {x | w (x - c) ≤ γ}

/-- The open ball of radius `γ` about `c`. -/
def openBall (w : Valuation N Γ') (c : N) (γ : Γ') : Set N := {x | w (x - c) < γ}

theorem mem_closedBall {w : Valuation N Γ'} {c x : N} {γ : Γ'} :
    x ∈ closedBall w c γ ↔ w (x - c) ≤ γ := Iff.rfl

theorem mem_openBall {w : Valuation N Γ'} {c x : N} {γ : Γ'} :
    x ∈ openBall w c γ ↔ w (x - c) < γ := Iff.rfl

/-- The closed ball of radius zero is a point. -/
theorem closedBall_zero_radius (w : Valuation N Γ') (c : N) : closedBall w c 0 = {c} := by
  ext x
  rw [mem_closedBall, Set.mem_singleton_iff]
  exact ⟨fun h => sub_eq_zero.mp (w.zero_iff.mp (le_antisymm h zero_le)),
    fun h => h ▸ by simp⟩

end Balls

section Good

variable {K : Type} [Field K] {N : Type} [Field N]
variable {Γ' : Type*} [LinearOrderedCommGroupWithZero Γ']

/-- A ball of `N` with centre and radius in the image of the base field `K`. -/
inductive IsKBall (f : K →+* N) (w : Valuation N Γ') : Set N → Prop
  | closed (c b : K) : IsKBall f w (closedBall w (f c) (w (f b)))
  | openball (c b : K) : IsKBall f w (openBall w (f c) (w (f b)))
  | univ : IsKBall f w Set.univ

end Good

section Formula

variable {K : Type} [Field K] {N : Type} [Field N]
variable {Γ' : Type*} [LinearOrderedCommGroupWithZero Γ']

/-- A **swiss cheese**: a ball `B₀` with centre and radius in `K`, with finitely many balls
`Bᵢ ⊆ B₀` (also with centre and radius in `K`) removed.  (Johnson §2.3.) -/
def SwissCheese (f : K →+* N) (w : Valuation N Γ') (D : Set N) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (B₀ : Set N) (B : ι → Set N),
    IsKBall f w B₀ ∧ (∀ i, IsKBall f w (B i)) ∧ (∀ i, B i ⊆ B₀)
      ∧ D = B₀ \ ⋃ i, B i

/-- **Johnson, Lemma 2.3.8**: a nonempty swiss cheese meets the image of `K`. -/
def CheeseMeetsBase (f : K →+* N) (w : Valuation N Γ') : Prop :=
  ∀ D : Set N, SwissCheese f w D → D.Nonempty → ∃ c : K, f c ∈ D

end Formula

end ValOneEC
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


/-! ## Johnson, Lemma 2.3.2: Boolean combinations of balls are finite unions of swiss cheeses

The content added here is:

* `Johnson.iUnion_equiv_reindex`, `Johnson.iUnion_finset_eq_iUnion_subtype` (index bookkeeping);
* `Johnson.diff_iUnion_swissCheese` — the normalisation step of Johnson's proof of 2.3.2: for a
  ball `B₀` and finitely many balls `bᵢ`, the set `B₀ \ ⋃ᵢ bᵢ` is `B₀ \ ⋃ⱼ Cⱼ` with every `Cⱼ` a
  ball *contained in* `B₀` (balls meeting `B₀` are comparable with it; balls disjoint from `B₀`
  contribute nothing);
* `Johnson.cell_eq_swissCheese` — each cell of the pattern of a finite family of balls is a swiss
  cheese;
* `Johnson.isBoolCombOfBalls_eq_iUnion_swissCheese` — **Lemma 2.3.2**: every Boolean combination
  of balls of `vK`-radius is a finite union of swiss cheeses `B₀ \ ⋃ⱼ Bⱼ` with `Bⱼ ⊆ B₀`.

Everything is proved in the framework of `QE/Johnson23_valuation.lean` (`Valuation K Γ₀`, `Γ₀` a
`LinearOrderedCommGroupWithZero`, `IsValBall` = closed balls / open balls of radius in `vK`,
singletons and `K`), using only the comparability of balls `isValBall_subset_or_subset`.
-/

namespace Johnson

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- Reindexing a union along an equivalence. -/
theorem iUnion_equiv_reindex {α β : Type*} (e : α ≃ β) (f : β → Set K) :
    (⋃ i : α, f (e i)) = ⋃ j : β, f j := by
  ext x
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨i, hi⟩; exact ⟨e i, hi⟩
  · rintro ⟨j, hj⟩; exact ⟨e.symm j, by simpa using hj⟩

/-- A union over a `Finset` is a union over the corresponding subtype. -/
theorem iUnion_finset_eq_iUnion_subtype {ι : Type*} (b : ι → Set K) (s : Finset ι) :
    (⋃ i ∈ s, b i) = ⋃ i : {i : ι // i ∈ s}, b i := by
  ext x; simp

/-- **The normalisation behind Johnson's Lemma 2.3.2.**  Given a ball `B₀` and finitely many
balls `bᵢ`, the set `B₀ \ ⋃ᵢ bᵢ` can be written as `B₀ \ ⋃ⱼ Cⱼ` with every `Cⱼ` a ball
contained in `B₀`. -/
theorem diff_iUnion_swissCheese (v : Valuation K Γ₀) {ι : Type*} [Fintype ι]
    {B₀ : Set K} (hB₀ : IsValBall v B₀) (b : ι → Set K) (hb : ∀ i, IsValBall v (b i)) :
    ∃ (m : ℕ) (C : Fin m → Set K), (∀ j, IsValBall v (C j)) ∧
      (∀ j, C j ⊆ B₀) ∧ B₀ \ (⋃ i, b i) = B₀ \ (⋃ j, C j) := by
  classical
  by_cases hP : ∃ i, B₀ ⊆ b i
  · -- some `bᵢ` swallows `B₀`, so both sides are empty
    obtain ⟨i₀, hi₀⟩ := hP
    refine ⟨1, fun _ => B₀, fun _ => hB₀, fun _ => subset_rfl, ?_⟩
    have hcover : B₀ ⊆ ⋃ i, b i := (hi₀.trans (Set.subset_iUnion b i₀))
    have h1 : B₀ \ (⋃ i, b i) = ∅ := Set.sdiff_eq_empty.mpr hcover
    have h2 : (⋃ _j : Fin 1, (B₀ : Set K)) = B₀ := by
      refine Set.Subset.antisymm (Set.iUnion_subset fun _ => subset_rfl) ?_
      intro x hx
      exact Set.mem_iUnion.mpr ⟨0, hx⟩
    rw [h1, h2, Set.sdiff_self]
  · -- keep exactly the balls contained in `B₀`
    push_neg at hP
    let κ := {i : ι // b i ⊆ B₀}
    haveI : Fintype κ := inferInstance
    let e := Fintype.equivFin κ
    refine ⟨Fintype.card κ, fun j => b (e.symm j).1, fun j => hb _,
      fun j => (e.symm j).2, ?_⟩
    rw [iUnion_equiv_reindex (e := e.symm) (f := fun i : κ => b i.1)]
    have hEq : B₀ ∩ (⋃ i : ι, b i) = B₀ ∩ (⋃ i : κ, b i.1) := by
      refine Set.Subset.antisymm ?_ ?_
      · rintro x ⟨hx, hxU⟩
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxU
        have hsub : b i ⊆ B₀ := by
          rcases isValBall_subset_or_subset v (hb i) hB₀ ⟨x, hi, hx⟩ with h | h
          · exact h
          · exact absurd h (hP i)
        exact ⟨hx, Set.mem_iUnion.mpr ⟨⟨i, hsub⟩, hi⟩⟩
      · rintro x ⟨hx, hxU⟩
        obtain ⟨⟨i, _⟩, hi⟩ := Set.mem_iUnion.mp hxU
        exact ⟨hx, Set.mem_iUnion.mpr ⟨i, hi⟩⟩
    ext x
    simp only [Set.mem_sdiff]
    constructor
    · rintro ⟨hx, hxU⟩
      refine ⟨hx, ?_⟩
      intro hxV
      have hmem : x ∈ B₀ ∩ (⋃ i : κ, b i.1) := ⟨hx, hxV⟩
      rw [← hEq] at hmem
      exact hxU hmem.2
    · rintro ⟨hx, hxV⟩
      refine ⟨hx, ?_⟩
      intro hxU
      have hmem : x ∈ B₀ ∩ (⋃ i : ι, b i) := ⟨hx, hxU⟩
      rw [hEq] at hmem
      exact hxV hmem.2

/-- The empty set as a swiss cheese (needed for the cells the Boolean function rejects). -/
theorem empty_swissCheese : (∅ : Set K) = Set.univ \ (⋃ _j : Fin 1, (Set.univ : Set K)) := by
  have hone : (⋃ _j : Fin 1, (Set.univ : Set K)) = Set.univ :=
    Set.eq_univ_iff_forall.mpr fun x => Set.mem_iUnion.mpr ⟨0, Set.mem_univ x⟩
  rw [hone, Set.sdiff_self]

/-- **Johnson, Lemma 2.3.2, one cell.**  The cell of a pattern `S` in a finite family of balls is
a swiss cheese (or empty). -/
theorem cell_eq_swissCheese (v : Valuation K Γ₀) {ι : Type*} [Fintype ι] [DecidableEq ι]
    {b : ι → Set K} (hb : ∀ i, IsValBall v (b i)) (S : Finset ι) :
    ∃ (m : ℕ) (B₀ : Set K) (C : Fin m → Set K),
      IsValBall v B₀ ∧ (∀ j, IsValBall v (C j)) ∧ (∀ j, C j ⊆ B₀) ∧
      cell b S = B₀ \ (⋃ j, C j) := by
  classical
  rcases eq_or_ne S ∅ with hS | hS
  · subst hS
    have hcell : cell b (∅ : Finset ι) = Set.univ \ (⋃ i : ι, b i) := by
      have h1 : (⋂ i ∈ (∅ : Finset ι), b i) = Set.univ := by ext x; simp
      have h2 : (⋃ i ∈ (∅ : Finset ι)ᶜ, b i) = ⋃ i : ι, b i := by
        rw [Finset.compl_empty]
        ext x; simp
      rw [cell, h1, h2]
    obtain ⟨m, C, hC, hCsub, heq⟩ :=
      diff_iUnion_swissCheese v (B₀ := Set.univ) IsValBall.univ b hb
    exact ⟨m, Set.univ, C, IsValBall.univ, hC, fun j => Set.subset_univ _,
      by rw [hcell, heq]⟩
  · by_cases hne : (⋂ i ∈ S, b i).Nonempty
    · -- the intersection of the balls of the pattern is one of them
      obtain ⟨j, hjS, hjeq⟩ :=
        exists_mem_of_iInter_finset v hb (Finset.nonempty_iff_ne_empty.mpr hS) hne
      have hcell : cell b S = b j \ (⋃ i : {i : ι // i ∈ Sᶜ}, b i.1) := by
        rw [cell, hjeq, iUnion_finset_eq_iUnion_subtype]
      obtain ⟨m, C, hC, hCsub, heq⟩ :=
        diff_iUnion_swissCheese v (B₀ := b j) (hb j) (fun i : {i : ι // i ∈ Sᶜ} => b i.1)
          (fun i => hb i.1)
      exact ⟨m, b j, C, hb j, hC, hCsub, by rw [hcell, heq]⟩
    · -- the cell is empty
      have hcell : cell b S = ∅ := by
        rw [cell, Set.not_nonempty_iff_eq_empty.mp hne, Set.empty_sdiff]
      refine ⟨1, Set.univ, fun _ => Set.univ, IsValBall.univ, fun _ => IsValBall.univ,
        fun _ => subset_rfl, ?_⟩
      rw [hcell]
      exact empty_swissCheese (K := K)

/-- **Johnson, Lemma 2.3.2.**  Every Boolean combination of balls of `vK`-radius is a finite union
of swiss cheeses: `⋃ᵢ (B₀ᵢ \ ⋃ⱼ Bᵢⱼ)` with each `Bᵢⱼ` a ball contained in `B₀ᵢ`. -/
theorem isBoolCombOfBalls_eq_iUnion_swissCheese (v : Valuation K Γ₀) {D : Set K}
    (hD : IsBoolCombOfBalls v D) :
    ∃ (n : ℕ) (B₀ : Fin n → Set K) (m : Fin n → ℕ) (C : ∀ i, Fin (m i) → Set K),
      (∀ i, IsValBall v (B₀ i)) ∧ (∀ i j, IsValBall v (C i j)) ∧
      (∀ i j, C i j ⊆ B₀ i) ∧ D = ⋃ i, (B₀ i \ (⋃ j, C i j)) := by
  classical
  obtain ⟨ι, hι, b, t, hb, hDdef⟩ := hD
  haveI := hι
  have key : ∀ S : Finset ι, ∃ (m : ℕ) (B₀ : Set K) (C : Fin m → Set K),
      IsValBall v B₀ ∧ (∀ j, IsValBall v (C j)) ∧ (∀ j, C j ⊆ B₀) ∧
      cellIf b t S = B₀ \ (⋃ j, C j) := by
    intro S
    by_cases ht : t (S : Set ι) = true
    · rw [cellIf, if_pos ht]
      exact cell_eq_swissCheese v hb S
    · refine ⟨1, Set.univ, fun _ => Set.univ, IsValBall.univ, fun _ => IsValBall.univ,
        fun _ => subset_rfl, ?_⟩
      rw [cellIf, if_neg ht]
      exact empty_swissCheese (K := K)
  choose m B₀ C hP using key
  have hB₀ : ∀ S, IsValBall v (B₀ S) := fun S => (hP S).1
  have hC : ∀ S j, IsValBall v (C S j) := fun S => (hP S).2.1
  have hCsub : ∀ S j, C S j ⊆ B₀ S := fun S => (hP S).2.2.1
  have hEq : ∀ S, cellIf b t S = B₀ S \ (⋃ j, C S j) := fun S => (hP S).2.2.2
  let e : Finset ι ≃ Fin (Fintype.card (Finset ι)) := Fintype.equivFin (Finset ι)
  let m' : Fin (Fintype.card (Finset ι)) → ℕ := fun i => m (e.symm i)
  refine ⟨Fintype.card (Finset ι), fun i => B₀ (e.symm i), m',
    fun i => C (e.symm i), fun i => hB₀ _, fun i j => hC _ _, fun i j => hCsub _ _, ?_⟩
  have hD' : D = ⋃ S : Finset ι, (B₀ S \ (⋃ j, C S j)) := by
    rw [show D = {x : K | t {i | x ∈ b i} = true} from Set.ext hDdef, eq_iUnion_cell b t]
    simp only [hEq]
  rw [hD']
  exact (iUnion_equiv_reindex (e := e.symm)
    (f := fun S : Finset ι => B₀ S \ (⋃ j, C S j))).symm


end Johnson

/-! ## Johnson, Lemmas 2.3.3 and 2.3.8: points of `K` in `K`-balls

`K` is a valued field embedded in a valued field `L` by `φ : K →+* L`; the valuation of `K` is
`v.comap φ`.  A *K-ball* of `L` is a ball of `L` whose centre and radius come from `K`.

* `isValBallK_trace`: the trace on `K` of a K-ball is a ball of `K`;
* `lemma_2_3_3`: if `B₁ ⊊ B₂` are K-balls and `vK` is a dense linear order (true when
  `K ⊨ ACVF`), then `B₂ \ B₁` contains a point of `K`;
* `lemma_2_3_8`: if `C = B₀ \ ⋃ᵢ Bᵢ` is nonempty, with `B₀` a K-ball and the `Bᵢ` subballs of
  `B₀` with centre and radius in `K`, then `C` contains a point of `K`.
-/

namespace Johnson

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
variable {L : Type*} [Field L]

/-- The closed ball of radius `0` is a singleton. -/
theorem closedBall_eq_singleton_zero (v : Valuation K Γ₀) (c : K) :
    closedBall v c 0 = {c} := by
  ext x
  rw [mem_closedBall, Set.mem_singleton_iff]
  constructor
  · intro h
    by_contra hx
    have hne : v (x - c) ≠ 0 := v.ne_zero_iff.mpr (sub_ne_zero.mpr hx)
    exact absurd h (not_le.mpr (pos_iff_ne_zero.mpr hne))
  · rintro rfl
    simp

/-- The open ball of radius `0` is empty. -/
theorem openBall_eq_empty_zero (v : Valuation K Γ₀) (c : K) :
    openBall v c 0 = ∅ := by
  ext x
  rw [mem_openBall, Set.mem_empty_iff_false, iff_false]
  exact not_lt.mpr zero_le

/-- Two closed balls of the same radius that meet are equal. -/
theorem closedBall_eq_of_val_sub_le (v : Valuation K Γ₀) {c₁ c₂ : K} {γ : Γ₀}
    (h : v (c₁ - c₂) ≤ γ) : closedBall v c₁ γ = closedBall v c₂ γ := by
  refine Set.Subset.antisymm (closedBall_mono v h le_rfl) ?_
  refine closedBall_mono v ?_ le_rfl
  rwa [show c₂ - c₁ = -(c₁ - c₂) by ring, Valuation.map_neg]

/-- Some element of value strictly between `0` and `1`. -/
theorem exists_val_between_zero_one (w : Valuation K Γ₀)
    (hnt : ∃ x : K, x ≠ 0 ∧ w x < 1) : ∃ u : K, 0 < w u ∧ w u < 1 := by
  obtain ⟨x, hx0, hx1⟩ := hnt
  exact ⟨x, pos_iff_ne_zero.mpr (w.ne_zero_iff.mpr hx0), hx1⟩

/-- Between two values, the lower one possibly `0`, there is a third one. -/
theorem exists_val_between' [IsAlgClosed K] (w : Valuation K Γ₀)
    (hnt : ∃ x : K, x ≠ 0 ∧ w x < 1) {a c : K} (h : w a < w c) :
    ∃ t : K, w a < w t ∧ w t < w c := by
  have hc0 : 0 < w c := lt_of_le_of_lt zero_le h
  have hc : c ≠ 0 := fun hc => by rw [hc, map_zero] at hc0; exact lt_irrefl _ hc0
  rcases eq_or_lt_of_le (zero_le (a := w a)) with ha | ha
  · obtain ⟨u, hu0, hu1⟩ := exists_val_between_zero_one w hnt
    refine ⟨c * u, ?_, ?_⟩
    · rw [map_mul, ← ha]
      exact mul_pos hc0 hu0
    · rw [map_mul]
      simpa using mul_lt_mul_of_pos_left hu1 hc0
  · have ha0 : a ≠ 0 := fun h => by rw [h, map_zero] at ha; exact lt_irrefl _ ha
    obtain ⟨t, -, h1, h2⟩ := exists_val_between w ha0 hc h
    exact ⟨t, h1, h2⟩

/-- Above finitely many values there is another one. -/
theorem exists_val_gt_finset [IsAlgClosed K] (w : Valuation K Γ₀)
    (hnt : ∃ x : K, x ≠ 0 ∧ w x < 1) (s : Finset K) :
    ∃ x : K, ∀ a ∈ s, w a < w x := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by simp⟩
  | insert a₀ s ha ih =>
    obtain ⟨x₀, hx₀⟩ := ih
    rcases le_or_gt (w a₀) (w x₀) with hle | hlt
    · rcases eq_or_lt_of_le (zero_le (a := w x₀)) with h0 | hpos
      · refine ⟨1, ?_⟩
        intro a ha'
        have h1 : w a ≤ w x₀ := by
          rcases Finset.mem_insert.mp ha' with rfl | hmem
          · exact hle
          · exact le_of_lt (hx₀ a hmem)
        have h2 : w a = 0 := by rw [← h0] at h1; exact le_antisymm h1 zero_le
        rw [h2, Valuation.map_one]
        exact zero_lt_one
      · have hx0ne : x₀ ≠ 0 := fun h => by
          rw [h, map_zero] at hpos; exact lt_irrefl _ hpos
        obtain ⟨x, -, hx⟩ := exists_val_lt_val w hnt hx0ne
        refine ⟨x, ?_⟩
        intro a ha'
        rcases Finset.mem_insert.mp ha' with rfl | hmem
        · exact lt_of_le_of_lt hle hx
        · exact lt_trans (hx₀ a hmem) hx
    · have ha0 : a₀ ≠ 0 := fun h => by
        rw [h, map_zero] at hlt; exact absurd hlt (not_lt_of_ge zero_le)
      obtain ⟨x, -, hx⟩ := exists_val_lt_val w hnt ha0
      refine ⟨x, ?_⟩
      intro a ha'
      rcases Finset.mem_insert.mp ha' with rfl | hmem
      · exact hx
      · exact lt_trans (lt_trans (hx₀ a hmem) hlt) hx

/-- K-balls of `L`: balls with centre and radius coming from `K`. -/
inductive IsValBallK (v : Valuation L Γ₀) (φ : K →+* L) : Set L → Prop
  | closed (c b : K) : IsValBallK v φ (closedBall v (φ c) ((v.comap φ) b))
  | openball (c b : K) : IsValBallK v φ (openBall v (φ c) ((v.comap φ) b))
  | singleton (c : K) : IsValBallK v φ {φ c}
  | univ : IsValBallK v φ Set.univ

/-- The trace on `K` of a K-ball is a ball of `K`. -/
theorem isValBallK_trace (v : Valuation L Γ₀) (φ : K →+* L) {B : Set L}
    (hB : IsValBallK v φ B) : IsValBall (v.comap φ) {x : K | φ x ∈ B} := by
  cases hB with
  | closed c b =>
    have h : {x : K | φ x ∈ closedBall v (φ c) ((v.comap φ) b)}
        = closedBall (v.comap φ) c ((v.comap φ) b) := by
      ext x
      simp only [Set.mem_setOf_eq, mem_closedBall, Valuation.comap_apply, map_sub]
    rw [h]; exact IsValBall.closed c b
  | openball c b =>
    have h : {x : K | φ x ∈ openBall v (φ c) ((v.comap φ) b)}
        = openBall (v.comap φ) c ((v.comap φ) b) := by
      ext x
      simp only [Set.mem_setOf_eq, mem_openBall, Valuation.comap_apply, map_sub]
    rw [h]; exact IsValBall.openball c b
  | singleton c =>
    have h : {x : K | φ x ∈ ({φ c} : Set L)} = {c} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      exact ⟨fun h => φ.injective h, fun h => by rw [h]⟩
    rw [h]; exact IsValBall.singleton c
  | univ =>
    have h : {x : K | φ x ∈ (Set.univ : Set L)} = Set.univ := by
      ext x; simp
    rw [h]; exact IsValBall.univ

/-- A nonempty K-ball has a point of `K`. -/
theorem isValBallK_exists_point (v : Valuation L Γ₀) (φ : K →+* L) {B : Set L}
    (hB : IsValBallK v φ B) (hne : B.Nonempty) : ∃ x : K, φ x ∈ B := by
  cases hB with
  | closed c b => exact ⟨c, closedBall_self_mem v (φ c) ((v.comap φ) b)⟩
  | openball c b =>
    rcases eq_or_ne b 0 with hb | hb
    · rw [hb, map_zero, openBall_eq_empty_zero] at hne ⊢
      obtain ⟨y, hy⟩ := hne
      exact absurd hy (by simp)
    · refine ⟨c, openBall_self_mem (v := v) ?_⟩
      rw [Valuation.comap_apply, v.ne_zero_iff]
      exact fun h => hb (φ.injective (by simpa using h))
  | singleton c => exact ⟨c, Set.mem_singleton _⟩
  | univ => exact ⟨0, Set.mem_univ _⟩

/-! ## Johnson, Lemma 2.3.3

If `B₁ ⊊ B₂` are K-balls of `L` and `vK` is a dense linear order (which holds when `K ⊨ ACVF`),
then `B₂ \ B₁` contains a point of `K`.
-/

/-- `c + 1 ≠ c` in a field. -/
theorem add_one_ne_self (c : K) : c + 1 ≠ c := by
  intro h
  exact one_ne_zero (add_left_cancel (a := c) (b := 1) (c := 0) (by rw [add_zero]; exact h))

/-- The value of `x - c` in `K` is the value of `φ x - φ c` in `L`. -/
theorem comap_apply_sub (v : Valuation L Γ₀) (φ : K →+* L) (x c : K) :
    (v.comap φ) (x - c) = v (φ x - φ c) := by
  rw [Valuation.comap_apply, map_sub φ x c]

/-- `v (φ c₂ - φ c₁)` is the value of `c₁ - c₂` in `K`. -/
theorem comap_sub_swap (v : Valuation L Γ₀) (φ : K →+* L) (c₁ c₂ : K) :
    v (φ c₂ - φ c₁) = (v.comap φ) (c₁ - c₂) := by
  rw [show φ c₂ - φ c₁ = -(φ c₁ - φ c₂) by ring, Valuation.map_neg, Valuation.comap_apply,
    map_sub φ c₁ c₂]

/-- A closed K-ball of positive radius contains points of `K` other than any prescribed one. -/
theorem exists_mem_closedBall_ne [IsAlgClosed K] (v : Valuation L Γ₀) (φ : K →+* L)
    (hnt : ∃ x : K, x ≠ 0 ∧ (v.comap φ) x < 1) {c b : K} (hb : b ≠ 0) (c' : K) :
    ∃ x : K, (v.comap φ) (x - c) ≤ (v.comap φ) b ∧ x ≠ c' := by
  classical
  obtain ⟨u, hu0, hu1⟩ := exists_val_between_zero_one (v.comap φ) hnt
  have hu : (v.comap φ) (1 + u) ≤ 1 := by
    have h := map_add_le_max (f := v.comap φ) (1 : K) u
    rw [(v.comap φ).map_one] at h
    exact le_trans h (max_le le_rfl hu1.le)
  by_cases h : c' - c = b
  · refine ⟨c + b * (1 + u), ?_, ?_⟩
    · rw [show c + b * (1 + u) - c = b * (1 + u) by ring, map_mul]
      calc (v.comap φ) b * (v.comap φ) (1 + u) ≤ (v.comap φ) b * 1 :=
            mul_le_mul_of_nonneg_left hu zero_le
        _ = (v.comap φ) b := mul_one _
    · intro hx
      have h1 : b * (1 + u) = c' - c := by rw [← hx]; ring
      rw [h] at h1
      have h2 : b * (1 + u) = b * 1 := by rw [mul_one]; exact h1
      have h3 : 1 + u = 1 := mul_left_cancel₀ hb h2
      have h4 : u = 0 := add_left_cancel (a := 1) (b := u) (c := 0) (by rw [add_zero]; exact h3)
      rw [h4, map_zero] at hu0
      exact absurd hu0 (lt_irrefl 0)
  · refine ⟨c + b, ?_, ?_⟩
    · rw [show c + b - c = b by ring]
    · intro hx
      exact h (by rw [← hx]; ring)

/-- An open K-ball of positive radius contains points of `K` other than any prescribed one. -/
theorem exists_mem_openBall_ne [IsAlgClosed K] (v : Valuation L Γ₀) (φ : K →+* L)
    (hnt : ∃ x : K, x ≠ 0 ∧ (v.comap φ) x < 1) {c b : K} (hb : 0 < (v.comap φ) b) (c' : K) :
    ∃ x : K, (v.comap φ) (x - c) < (v.comap φ) b ∧ x ≠ c' := by
  classical
  by_cases h : c = c'
  · subst h
    obtain ⟨u, hu0, hu1⟩ := exists_val_between_zero_one (v.comap φ) hnt
    refine ⟨c + b * u, ?_, ?_⟩
    · rw [show c + b * u - c = b * u by ring, map_mul]
      simpa using mul_lt_mul_of_pos_left hu1 hb
    · intro hx
      have h1 : b * u = 0 :=
        add_left_cancel (a := c) (b := b * u) (c := 0) (by rw [add_zero]; exact hx)
      rcases mul_eq_zero.mp h1 with h2 | h2
      · exact absurd h2 ((v.comap φ).ne_zero_iff.mp (ne_of_gt hb))
      · rw [h2, map_zero] at hu0
        exact absurd hu0 (lt_irrefl 0)
  · exact ⟨c, by rw [show c - c = 0 by ring, map_zero]; exact hb, h⟩

/-- **Johnson, Lemma 2.3.3.**  If `B₁ ⊊ B₂` are K-balls of `L`, then `B₂ \ B₁` contains a point
of `K`.  (`K` algebraically closed and nontrivially valued is used through the density of the
value group and the unboundedness of the values.) -/
theorem lemma_2_3_3 [IsAlgClosed K] (v : Valuation L Γ₀) (φ : K →+* L)
    (hnt : ∃ x : K, x ≠ 0 ∧ (v.comap φ) x < 1)
    {B₁ B₂ : Set L} (h₁ : IsValBallK v φ B₁) (h₂ : IsValBallK v φ B₂)
    (hsub : B₁ ⊆ B₂) (hne : B₁ ≠ B₂) :
    ∃ x : K, φ x ∈ B₂ ∧ φ x ∉ B₁ := by
  classical
  have hmem : ∀ (y c : K) (γ : Γ₀),
      φ y ∈ closedBall v (φ c) γ ↔ (v.comap φ) (y - c) ≤ γ := by
    intro y c γ
    rw [mem_closedBall, comap_apply_sub]
  have hmemO : ∀ (y c : K) (γ : Γ₀),
      φ y ∈ openBall v (φ c) γ ↔ (v.comap φ) (y - c) < γ := by
    intro y c γ
    rw [mem_openBall, comap_apply_sub]
  have hmemS : ∀ (y c : K), φ y ∈ ({φ c} : Set L) ↔ y = c := by
    intro y c
    rw [Set.mem_singleton_iff]
    exact ⟨fun h => φ.injective h, fun h => by rw [h]⟩
  revert hsub hne
  cases h₂ with
  | univ =>
    intro _ hne
    cases h₁ with
    | univ => exact absurd rfl hne
    | singleton c =>
      exact ⟨c + 1, Set.mem_univ _, by rw [hmemS]; exact add_one_ne_self c⟩
    | closed c b =>
      rcases eq_or_ne b 0 with hb | hb
      · rw [hb, map_zero, closedBall_eq_singleton_zero]
        exact ⟨c + 1, Set.mem_univ _, by rw [hmemS]; exact add_one_ne_self c⟩
      · obtain ⟨b', -, hb'⟩ := exists_val_lt_val (v.comap φ) hnt hb
        refine ⟨c + b', Set.mem_univ _, ?_⟩
        rw [hmem, show c + b' - c = b' by ring]
        exact not_le.mpr hb'
    | openball c b =>
      rcases eq_or_ne b 0 with hb | hb
      · rw [hb, map_zero, openBall_eq_empty_zero]
        exact ⟨0, Set.mem_univ _, Set.notMem_empty _⟩
      · obtain ⟨b', -, hb'⟩ := exists_val_lt_val (v.comap φ) hnt hb
        refine ⟨c + b', Set.mem_univ _, ?_⟩
        rw [hmemO, show c + b' - c = b' by ring]
        exact not_lt.mpr hb'.le
  | singleton c₂ =>
    intro hsub hne
    rcases Set.subset_singleton_iff_eq.mp hsub with h | h
    · exact ⟨c₂, Set.mem_singleton _, by rw [h]; exact Set.notMem_empty _⟩
    · exact absurd h hne
  | closed c₂ b₂ =>
    intro hsub hne
    rcases eq_or_ne b₂ 0 with hb₂ | hb₂
    · rw [hb₂, map_zero, closedBall_eq_singleton_zero] at hsub hne ⊢
      rcases Set.subset_singleton_iff_eq.mp hsub with h | h
      · exact ⟨c₂, Set.mem_singleton _, by rw [h]; exact Set.notMem_empty _⟩
      · exact absurd h hne
    · have hβpos : 0 < (v.comap φ) b₂ :=
        pos_iff_ne_zero.mpr ((v.comap φ).ne_zero_iff.mpr hb₂)
      cases h₁ with
      | univ =>
        exfalso
        obtain ⟨b', -, hb'⟩ := exists_val_lt_val (v.comap φ) hnt hb₂
        have hmem' : φ (c₂ + b') ∈ closedBall v (φ c₂) ((v.comap φ) b₂) :=
          hsub (Set.mem_univ _)
        rw [hmem, show c₂ + b' - c₂ = b' by ring] at hmem'
        exact absurd hmem' (not_le.mpr hb')
      | singleton c₁ =>
        obtain ⟨x, hx1, hx2⟩ := exists_mem_closedBall_ne v φ hnt hb₂ c₁
        exact ⟨x, by rw [hmem]; exact hx1, by rw [hmemS]; exact hx2⟩
      | closed c₁ b₁ =>
        have hc₁ : (v.comap φ) (c₁ - c₂) ≤ (v.comap φ) b₂ := by
          have h := hsub (closedBall_self_mem v (φ c₁) ((v.comap φ) b₁))
          rwa [hmem] at h
        have hγ : (v.comap φ) b₁ < (v.comap φ) b₂ := by
          by_contra hcon
          push Not at hcon
          have hEq : closedBall v (φ c₁) ((v.comap φ) b₁)
              = closedBall v (φ c₂) ((v.comap φ) b₂) := by
            refine Set.Subset.antisymm hsub ?_
            refine closedBall_mono v ?_ hcon
            rw [comap_sub_swap]
            exact le_trans hc₁ hcon
          exact hne hEq
        obtain ⟨t, ht1, ht2⟩ := exists_val_between' (v.comap φ) hnt hγ
        refine ⟨c₁ + t, ?_, ?_⟩
        · rw [hmem, show c₁ + t - c₂ = (c₁ - c₂) + t by ring]
          exact le_trans (map_add_le_max (f := v.comap φ) (c₁ - c₂) t)
            (max_le hc₁ ht2.le)
        · rw [hmem, show c₁ + t - c₁ = t by ring]
          exact not_le.mpr ht1
      | openball c₁ b₁ =>
        rcases eq_or_ne b₁ 0 with hb₁ | hb₁
        · rw [hb₁, map_zero, openBall_eq_empty_zero]
          refine ⟨c₂, ?_, Set.notMem_empty _⟩
          rw [hmem, show c₂ - c₂ = 0 by ring, map_zero]
          exact zero_le
        · have hc₁ : (v.comap φ) (c₁ - c₂) ≤ (v.comap φ) b₂ := by
            have h := hsub (openBall_self_mem (v := v) (c := φ c₁) (γ := (v.comap φ) b₁)
              ((v.comap φ).ne_zero_iff.mpr hb₁))
            rwa [hmem] at h
          have hγ : (v.comap φ) b₁ ≤ (v.comap φ) b₂ := by
            by_contra hcon
            push Not at hcon
            obtain ⟨t, ht1, ht2⟩ := exists_val_between' (v.comap φ) hnt hcon
            have hmemB₁ : φ (c₁ + t) ∈ openBall v (φ c₁) ((v.comap φ) b₁) := by
              rw [hmemO, show c₁ + t - c₁ = t by ring]; exact ht2
            have hmemB₂ := hsub hmemB₁
            rw [hmem, show c₁ + t - c₂ = (c₁ - c₂) + t by ring] at hmemB₂
            have hlt : (v.comap φ) t ≤
                max ((v.comap φ) ((c₁ - c₂) + t)) ((v.comap φ) (c₁ - c₂)) := by
              have hh := val_sub_le_max (v.comap φ) ((c₁ - c₂) + t) 0 (c₁ - c₂)
              rw [sub_zero, zero_sub, Valuation.map_neg,
                show ((c₁ - c₂) + t) - (c₁ - c₂) = t by ring] at hh
              exact hh
            exact absurd (le_trans hlt (max_le hmemB₂ hc₁)) (not_le.mpr ht1)
          rcases eq_or_lt_of_le hγ with hγ' | hγ'
          · refine ⟨c₁ + b₂, ?_, ?_⟩
            · rw [hmem, show c₁ + b₂ - c₂ = (c₁ - c₂) + b₂ by ring]
              exact le_trans (map_add_le_max (f := v.comap φ) (c₁ - c₂) b₂)
                (max_le hc₁ le_rfl)
            · rw [hmemO, show c₁ + b₂ - c₁ = b₂ by ring]
              exact not_lt.mpr hγ'.le
          · obtain ⟨t, ht1, ht2⟩ := exists_val_between' (v.comap φ) hnt hγ'
            refine ⟨c₁ + t, ?_, ?_⟩
            · rw [hmem, show c₁ + t - c₂ = (c₁ - c₂) + t by ring]
              exact le_trans (map_add_le_max (f := v.comap φ) (c₁ - c₂) t)
                (max_le hc₁ ht2.le)
            · rw [hmemO, show c₁ + t - c₁ = t by ring]
              exact not_lt.mpr ht1.le
  | openball c₂ b₂ =>
    intro hsub hne
    rcases eq_or_ne b₂ 0 with hb₂ | hb₂
    · rw [hb₂, map_zero, openBall_eq_empty_zero] at hsub hne ⊢
      exact absurd (Set.subset_empty_iff.mp hsub) hne
    · have hβpos : 0 < (v.comap φ) b₂ :=
        pos_iff_ne_zero.mpr ((v.comap φ).ne_zero_iff.mpr hb₂)
      cases h₁ with
      | univ =>
        exfalso
        have hmem' : φ (c₂ + b₂) ∈ openBall v (φ c₂) ((v.comap φ) b₂) := hsub (Set.mem_univ _)
        rw [hmemO, show c₂ + b₂ - c₂ = b₂ by ring] at hmem'
        exact absurd hmem' (not_lt.mpr le_rfl)
      | singleton c₁ =>
        obtain ⟨x, hx1, hx2⟩ := exists_mem_openBall_ne v φ hnt hβpos c₁
        exact ⟨x, by rw [hmemO]; exact hx1, by rw [hmemS]; exact hx2⟩
      | closed c₁ b₁ =>
        have hc₁lt : (v.comap φ) (c₁ - c₂) < (v.comap φ) b₂ := by
          have h := hsub (closedBall_self_mem v (φ c₁) ((v.comap φ) b₁))
          rwa [hmemO] at h
        have hγ : (v.comap φ) b₁ < (v.comap φ) b₂ := by
          by_contra hcon
          push Not at hcon
          have hmemB₁ : φ (c₁ + b₂) ∈ closedBall v (φ c₁) ((v.comap φ) b₁) := by
            rw [hmem, show c₁ + b₂ - c₁ = b₂ by ring]; exact hcon
          have hmemB₂ := hsub hmemB₁
          rw [hmemO, show c₁ + b₂ - c₂ = (c₁ - c₂) + b₂ by ring] at hmemB₂
          have hh : (v.comap φ) b₂ ≤
              max ((v.comap φ) ((c₁ - c₂) + b₂)) ((v.comap φ) (c₁ - c₂)) := by
            have hvv := val_sub_le_max (v.comap φ) ((c₁ - c₂) + b₂) 0 (c₁ - c₂)
            rw [sub_zero, zero_sub, Valuation.map_neg,
              show ((c₁ - c₂) + b₂) - (c₁ - c₂) = b₂ by ring] at hvv
            exact hvv
          exact absurd (lt_of_le_of_lt hh (max_lt hmemB₂ hc₁lt)) (lt_irrefl _)
        obtain ⟨t, ht1, ht2⟩ := exists_val_between' (v.comap φ) hnt hγ
        refine ⟨c₁ + t, ?_, ?_⟩
        · rw [hmemO, show c₁ + t - c₂ = (c₁ - c₂) + t by ring]
          exact lt_of_le_of_lt (map_add_le_max (f := v.comap φ) (c₁ - c₂) t)
            (max_lt hc₁lt ht2)
        · rw [hmem, show c₁ + t - c₁ = t by ring]
          exact not_le.mpr ht1
      | openball c₁ b₁ =>
        rcases eq_or_ne b₁ 0 with hb₁ | hb₁
        · rw [hb₁, map_zero, openBall_eq_empty_zero]
          refine ⟨c₂, ?_, Set.notMem_empty _⟩
          rw [hmemO, show c₂ - c₂ = 0 by ring, map_zero]
          exact hβpos
        · have hc₁lt : (v.comap φ) (c₁ - c₂) < (v.comap φ) b₂ := by
            have h := hsub (openBall_self_mem (v := v) (c := φ c₁) (γ := (v.comap φ) b₁)
              ((v.comap φ).ne_zero_iff.mpr hb₁))
            rwa [hmemO] at h
          have hγ : (v.comap φ) b₁ < (v.comap φ) b₂ := by
            rcases lt_trichotomy ((v.comap φ) b₁) ((v.comap φ) b₂) with h | h | h
            · exact h
            · exfalso
              apply hne
              have hsub' : openBall v (φ c₁) ((v.comap φ) b₂) ⊆
                  openBall v (φ c₂) ((v.comap φ) b₂) := by
                have hh2 := hsub
                rw [h] at hh2
                exact hh2
              rw [h]
              refine Set.Subset.antisymm hsub' ?_
              intro z hz
              rw [mem_openBall] at hz ⊢
              refine lt_of_le_of_lt (val_sub_le_max v z (φ c₂) (φ c₁)) (max_lt hz ?_)
              rw [comap_sub_swap]
              exact hc₁lt
            · obtain ⟨t, ht1, ht2⟩ := exists_val_between' (v.comap φ) hnt h
              have hmemB₁ : φ (c₁ + t) ∈ openBall v (φ c₁) ((v.comap φ) b₁) := by
                rw [hmemO, show c₁ + t - c₁ = t by ring]; exact ht2
              have hmemB₂ := hsub hmemB₁
              rw [hmemO, show c₁ + t - c₂ = (c₁ - c₂) + t by ring] at hmemB₂
              have hh : (v.comap φ) t ≤
                  max ((v.comap φ) ((c₁ - c₂) + t)) ((v.comap φ) (c₁ - c₂)) := by
                have hvv := val_sub_le_max (v.comap φ) ((c₁ - c₂) + t) 0 (c₁ - c₂)
                rw [sub_zero, zero_sub, Valuation.map_neg,
                  show ((c₁ - c₂) + t) - (c₁ - c₂) = t by ring] at hvv
                exact hvv
              exact absurd (lt_of_le_of_lt hh (max_lt hmemB₂ hc₁lt)) (not_lt.mpr ht1.le)
          obtain ⟨t, ht1, ht2⟩ := exists_val_between' (v.comap φ) hnt hγ
          refine ⟨c₁ + t, ?_, ?_⟩
          · rw [hmemO, show c₁ + t - c₂ = (c₁ - c₂) + t by ring]
            exact lt_of_le_of_lt (map_add_le_max (f := v.comap φ) (c₁ - c₂) t)
              (max_lt hc₁lt ht2)
          · rw [hmemO, show c₁ + t - c₁ = t by ring]
            exact not_lt.mpr ht1.le


/-! ## Johnson, Lemma 2.3.8

A nonempty swiss cheese cut out by K-balls meets `K`.
-/

/-- **Johnson, Lemma 2.3.8.**  Let `B₀` be a K-ball of `L` and `B₁, …, B_{n-1}` K-balls contained
in `B₀`.  If `B₀ \ ⋃ᵢ Bᵢ` is nonempty, then it contains a point of `K`. -/
theorem lemma_2_3_8 [IsAlgClosed K] (v : Valuation L Γ₀) (φ : K →+* L)
    (hnt : ∃ x : K, x ≠ 0 ∧ (v.comap φ) x < 1)
    {B₀ : Set L} (h₀ : IsValBallK v φ B₀) {n : ℕ} (B : Fin n → Set L)
    (hB : ∀ i, IsValBallK v φ (B i)) (hBsub : ∀ i, B i ⊆ B₀)
    (hne : (B₀ \ ⋃ i, B i).Nonempty) :
    ∃ x : K, φ x ∈ B₀ ∧ ∀ i, φ x ∉ B i := by
  classical
  obtain ⟨z, hz₀, hzU⟩ := hne
  have hzU' : ∀ i, z ∉ B i := fun i h => hzU (Set.mem_iUnion.mpr ⟨i, h⟩)
  -- every `Bᵢ` is strictly smaller than `B₀`
  have hproper : ∀ i, B i ≠ B₀ := by
    intro i hi
    exact hzU' i (hi ▸ hz₀)
  -- the traces on `K`
  set T : Fin n → Set K := fun i => {x : K | φ x ∈ B i} with hT
  set T₀ : Set K := {x : K | φ x ∈ B₀} with hT₀
  have hTball : ∀ i, IsValBall (v.comap φ) (T i) := fun i => isValBallK_trace v φ (hB i)
  have hT₀ball : IsValBall (v.comap φ) T₀ := isValBallK_trace v φ h₀
  have hTsub : ∀ i, T i ⊆ T₀ := fun i x hx => hBsub i hx
  -- each trace is properly contained in the trace of `B₀` (Lemma 2.3.3)
  have hTne : ∀ i, T i ≠ T₀ := by
    intro i hi
    obtain ⟨x, hx₀, hxi⟩ := lemma_2_3_3 v φ hnt (hB i) h₀ (hBsub i) (hproper i)
    have hxT₀ : x ∈ T₀ := hx₀
    rw [← hi] at hxT₀
    exact hxi hxT₀
  have hT₀ne : T₀.Nonempty := by
    obtain ⟨x, hx⟩ := isValBallK_exists_point v φ h₀ ⟨z, hz₀⟩
    exact ⟨x, hx⟩
  have hnt' : ∃ x : K, 1 < (v.comap φ) x := (exists_ne_zero_val_lt_one_iff (v.comap φ)).mp hnt
  -- Lemma 2.3.7 in `K`
  have hcover : T₀ ≠ ⋃ i ∈ (Finset.univ : Finset (Fin n)), T i :=
    ne_finite_union_of_proper_subballs (v.comap φ) hnt' hT₀ball hT₀ne Finset.univ T
      (fun i _ => hTball i) (fun i _ => hTsub i) (fun i _ => hTne i)
  have hwit : ∃ x : K, x ∈ T₀ ∧ x ∉ ⋃ i ∈ (Finset.univ : Finset (Fin n)), T i := by
    by_contra hcon
    push Not at hcon
    refine hcover (Set.Subset.antisymm hcon ?_)
    intro x hx
    have hx' : ∃ i : Fin n, x ∈ T i := by simpa using hx
    obtain ⟨i, hxi⟩ := hx'
    exact hTsub i hxi
  obtain ⟨x, hx₀, hxU⟩ := hwit
  refine ⟨x, hx₀, ?_⟩
  intro i hxi
  exact hxU (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨Finset.mem_univ i, hxi⟩⟩)


/-! ## The combination of 2.3.2 and 2.3.8: a nonempty Boolean combination of K-balls meets `K`

This is the geometric heart of Johnson's Lemma 2.3.9: a nonempty quantifier-free `K`-definable
subset of `L¹` is a Boolean combination of `K`-balls (Lemma 2.3.1, not formalised here), hence a
finite union of swiss cheeses (Lemma 2.3.2), and each nonempty swiss cheese meets `K`
(Lemma 2.3.8).  So only Lemma 2.3.1 is missing from the 1-ec step.
-/

/-- A K-ball of `L` is a ball of `L`. -/
theorem IsValBallK.toIsValBall {v : Valuation L Γ₀} {φ : K →+* L} {B : Set L}
    (h : IsValBallK v φ B) : IsValBall v B := by
  cases h with
  | closed c b => exact IsValBall.closed (φ c) (φ b)
  | openball c b => exact IsValBall.openball (φ c) (φ b)
  | singleton c => exact IsValBall.singleton (φ c)
  | univ => exact IsValBall.univ

/-- Two K-balls of `L` that meet are comparable. -/
theorem isValBallK_subset_or_subset (v : Valuation L Γ₀) (φ : K →+* L) {B₁ B₂ : Set L}
    (h₁ : IsValBallK v φ B₁) (h₂ : IsValBallK v φ B₂) (h : (B₁ ∩ B₂).Nonempty) :
    B₁ ⊆ B₂ ∨ B₂ ⊆ B₁ :=
  isValBall_subset_or_subset v h₁.toIsValBall h₂.toIsValBall h

/-- A nonempty finite intersection of K-balls is one of them. -/
theorem exists_mem_of_iInter_finsetK [DecidableEq ι] (v : Valuation L Γ₀) (φ : K →+* L)
    {b : ι → Set L} (hb : ∀ i, IsValBallK v φ (b i)) {S : Finset ι} (hS : S.Nonempty)
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
      rcases isValBallK_subset_or_subset v φ (hb i) (hb j) hne2 with h | h
      · exact ⟨i, Finset.mem_insert_self i S, by rw [hinter, Set.inter_eq_left.mpr h]⟩
      · exact ⟨j, Finset.mem_insert_of_mem hjS, by rw [hinter, Set.inter_eq_right.mpr h]⟩
    · have hSe : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS'
      subst hSe
      refine ⟨i, Finset.mem_singleton_self i, ?_⟩
      simp

/-- The normalisation behind Lemma 2.3.2 for K-balls. -/
theorem diff_iUnion_swissCheeseK (v : Valuation L Γ₀) (φ : K →+* L) {ι : Type*} [Fintype ι]
    {B₀ : Set L} (hB₀ : IsValBallK v φ B₀) (b : ι → Set L)
    (hb : ∀ i, IsValBallK v φ (b i)) :
    ∃ (m : ℕ) (C : Fin m → Set L), (∀ j, IsValBallK v φ (C j)) ∧
      (∀ j, C j ⊆ B₀) ∧ B₀ \ (⋃ i, b i) = B₀ \ (⋃ j, C j) := by
  classical
  by_cases hP : ∃ i, B₀ ⊆ b i
  · obtain ⟨i₀, hi₀⟩ := hP
    refine ⟨1, fun _ => B₀, fun _ => hB₀, fun _ => subset_rfl, ?_⟩
    have hcover : B₀ ⊆ ⋃ i, b i := (hi₀.trans (Set.subset_iUnion b i₀))
    have h1 : B₀ \ (⋃ i, b i) = ∅ := Set.sdiff_eq_empty.mpr hcover
    have h2 : (⋃ _j : Fin 1, (B₀ : Set L)) = B₀ := by
      refine Set.Subset.antisymm (Set.iUnion_subset fun _ => subset_rfl) ?_
      intro x hx
      exact Set.mem_iUnion.mpr ⟨0, hx⟩
    rw [h1, h2, Set.sdiff_self]
  · push Not at hP
    let κ := {i : ι // b i ⊆ B₀}
    haveI : Fintype κ := inferInstance
    let e := Fintype.equivFin κ
    refine ⟨Fintype.card κ, fun j => b (e.symm j).1, fun j => hb _,
      fun j => (e.symm j).2, ?_⟩
    rw [iUnion_equiv_reindex (e := e.symm) (f := fun i : κ => b i.1)]
    have hEq : B₀ ∩ (⋃ i : ι, b i) = B₀ ∩ (⋃ i : κ, b i.1) := by
      refine Set.Subset.antisymm ?_ ?_
      · rintro x ⟨hx, hxU⟩
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxU
        have hsub : b i ⊆ B₀ := by
          rcases isValBallK_subset_or_subset v φ (hb i) hB₀ ⟨x, hi, hx⟩ with h | h
          · exact h
          · exact absurd h (hP i)
        exact ⟨hx, Set.mem_iUnion.mpr ⟨⟨i, hsub⟩, hi⟩⟩
      · rintro x ⟨hx, hxU⟩
        obtain ⟨⟨i, _⟩, hi⟩ := Set.mem_iUnion.mp hxU
        exact ⟨hx, Set.mem_iUnion.mpr ⟨i, hi⟩⟩
    ext x
    simp only [Set.mem_sdiff]
    constructor
    · rintro ⟨hx, hxU⟩
      refine ⟨hx, ?_⟩
      intro hxV
      have hmem : x ∈ B₀ ∩ (⋃ i : κ, b i.1) := ⟨hx, hxV⟩
      rw [← hEq] at hmem
      exact hxU hmem.2
    · rintro ⟨hx, hxV⟩
      refine ⟨hx, ?_⟩
      intro hxU
      have hmem : x ∈ B₀ ∩ (⋃ i : ι, b i) := ⟨hx, hxU⟩
      rw [hEq] at hmem
      exact hxV hmem.2

/-- Lemma 2.3.2 for one cell of a family of K-balls. -/
theorem cell_eq_swissCheeseK (v : Valuation L Γ₀) (φ : K →+* L) {ι : Type*} [Fintype ι]
    [DecidableEq ι] {b : ι → Set L} (hb : ∀ i, IsValBallK v φ (b i)) (S : Finset ι) :
    ∃ (m : ℕ) (B₀ : Set L) (C : Fin m → Set L),
      IsValBallK v φ B₀ ∧ (∀ j, IsValBallK v φ (C j)) ∧ (∀ j, C j ⊆ B₀) ∧
      cell b S = B₀ \ (⋃ j, C j) := by
  classical
  rcases eq_or_ne S ∅ with hS | hS
  · subst hS
    have hcell : cell b (∅ : Finset ι) = Set.univ \ (⋃ i : ι, b i) := by
      have h1 : (⋂ i ∈ (∅ : Finset ι), b i) = Set.univ := by ext x; simp
      have h2 : (⋃ i ∈ (∅ : Finset ι)ᶜ, b i) = ⋃ i : ι, b i := by
        rw [Finset.compl_empty]
        ext x; simp
      rw [cell, h1, h2]
    obtain ⟨m, C, hC, hCsub, heq⟩ :=
      diff_iUnion_swissCheeseK v φ (B₀ := Set.univ) IsValBallK.univ b hb
    exact ⟨m, Set.univ, C, IsValBallK.univ, hC, fun j => Set.subset_univ _,
      by rw [hcell, heq]⟩
  · by_cases hne : (⋂ i ∈ S, b i).Nonempty
    · obtain ⟨j, hjS, hjeq⟩ :=
        exists_mem_of_iInter_finsetK v φ hb (Finset.nonempty_iff_ne_empty.mpr hS) hne
      have hcell : cell b S = b j \ (⋃ i : {i : ι // i ∈ Sᶜ}, b i.1) := by
        rw [cell, hjeq, iUnion_finset_eq_iUnion_subtype]
      obtain ⟨m, C, hC, hCsub, heq⟩ :=
        diff_iUnion_swissCheeseK v φ (B₀ := b j) (hb j) (fun i : {i : ι // i ∈ Sᶜ} => b i.1)
          (fun i => hb i.1)
      exact ⟨m, b j, C, hb j, hC, hCsub, by rw [hcell, heq]⟩
    · have hcell : cell b S = ∅ := by
        rw [cell, Set.not_nonempty_iff_eq_empty.mp hne, Set.empty_sdiff]
      refine ⟨1, Set.univ, fun _ => Set.univ, IsValBallK.univ, fun _ => IsValBallK.univ,
        fun _ => subset_rfl, ?_⟩
      rw [hcell]
      exact empty_swissCheese (K := L)

/-- `D` is a Boolean combination of K-balls: a Boolean function of the pattern of K-balls
containing a point. -/
def IsBoolCombOfBallsK (v : Valuation L Γ₀) (φ : K →+* L) (D : Set L) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (b : ι → Set L) (t : Set ι → Bool),
    (∀ i, IsValBallK v φ (b i)) ∧ ∀ x : L, (x ∈ D ↔ t {i | x ∈ b i} = true)

/-- **Johnson, Lemma 2.3.2 for K-balls.**  A Boolean combination of K-balls is a finite union of
swiss cheeses `B₀ \ ⋃ⱼ Bⱼ` with `Bⱼ ⊆ B₀` K-balls. -/
theorem isBoolCombOfBallsK_eq_iUnion_swissCheese (v : Valuation L Γ₀) (φ : K →+* L)
    {D : Set L} (hD : IsBoolCombOfBallsK v φ D) :
    ∃ (n : ℕ) (B₀ : Fin n → Set L) (m : Fin n → ℕ) (C : ∀ i, Fin (m i) → Set L),
      (∀ i, IsValBallK v φ (B₀ i)) ∧ (∀ i j, IsValBallK v φ (C i j)) ∧
      (∀ i j, C i j ⊆ B₀ i) ∧ D = ⋃ i, (B₀ i \ (⋃ j, C i j)) := by
  classical
  obtain ⟨ι, hι, b, t, hb, hDdef⟩ := hD
  haveI := hι
  have key : ∀ S : Finset ι, ∃ (m : ℕ) (B₀ : Set L) (C : Fin m → Set L),
      IsValBallK v φ B₀ ∧ (∀ j, IsValBallK v φ (C j)) ∧ (∀ j, C j ⊆ B₀) ∧
      cellIf b t S = B₀ \ (⋃ j, C j) := by
    intro S
    by_cases ht : t (S : Set ι) = true
    · rw [cellIf, if_pos ht]
      exact cell_eq_swissCheeseK v φ hb S
    · refine ⟨1, Set.univ, fun _ => Set.univ, IsValBallK.univ, fun _ => IsValBallK.univ,
        fun _ => subset_rfl, ?_⟩
      rw [cellIf, if_neg ht]
      exact empty_swissCheese (K := L)
  choose m B₀ C hP using key
  have hB₀ : ∀ S, IsValBallK v φ (B₀ S) := fun S => (hP S).1
  have hC : ∀ S j, IsValBallK v φ (C S j) := fun S => (hP S).2.1
  have hCsub : ∀ S j, C S j ⊆ B₀ S := fun S => (hP S).2.2.1
  have hEq : ∀ S, cellIf b t S = B₀ S \ (⋃ j, C S j) := fun S => (hP S).2.2.2
  let e : Finset ι ≃ Fin (Fintype.card (Finset ι)) := Fintype.equivFin (Finset ι)
  let m' : Fin (Fintype.card (Finset ι)) → ℕ := fun i => m (e.symm i)
  refine ⟨Fintype.card (Finset ι), fun i => B₀ (e.symm i), m',
    fun i => C (e.symm i), fun i => hB₀ _, fun i j => hC _ _, fun i j => hCsub _ _, ?_⟩
  have hD' : D = ⋃ S : Finset ι, (B₀ S \ (⋃ j, C S j)) := by
    rw [show D = {x : L | t {i | x ∈ b i} = true} from Set.ext hDdef, eq_iUnion_cell b t]
    simp only [hEq]
  rw [hD']
  exact (iUnion_equiv_reindex (e := e.symm)
    (f := fun S : Finset ι => B₀ S \ (⋃ j, C S j))).symm

/-- **The geometric heart of Johnson, Lemma 2.3.9.**  If `K` is algebraically closed and
nontrivially valued and `D ⊆ L` is a nonempty Boolean combination of K-balls, then `D` contains a
point of `K`.  (Up to Lemma 2.3.1, which converts quantifier-free formulas into Boolean
combinations of balls, this is 1-existential closedness of `K` in `L`.) -/
theorem exists_point_of_isBoolCombOfBallsK [IsAlgClosed K] (v : Valuation L Γ₀) (φ : K →+* L)
    (hnt : ∃ x : K, x ≠ 0 ∧ (v.comap φ) x < 1) {D : Set L}
    (hD : IsBoolCombOfBallsK v φ D) (hne : D.Nonempty) :
    ∃ x : K, φ x ∈ D := by
  classical
  obtain ⟨n, B₀, m, C, hB₀, hC, hCsub, hDeq⟩ := isBoolCombOfBallsK_eq_iUnion_swissCheese v φ hD
  obtain ⟨z, hz⟩ := hne
  rw [hDeq] at hz
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
  obtain ⟨x, hx₀, hxU⟩ := lemma_2_3_8 v φ hnt (hB₀ i) (C i) (hC i) (hCsub i) ⟨z, hi⟩
  refine ⟨x, ?_⟩
  rw [hDeq]
  refine Set.mem_iUnion.mpr ⟨i, hx₀, ?_⟩
  intro hc
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hc
  exact hxU j hj


/-! ## Johnson, Lemma 2.3.3 in the trace form stated by Johnson

Johnson states 2.3.3 as: if `B₁ ⊊ B₂` are K-balls of `L` then `B₁ ∩ K ⊊ B₂ ∩ K`.
-/

/-- **Johnson, Lemma 2.3.3** (the form stated in the paper): for K-balls `B₁ ⊆ B₂` with
`B₁ ≠ B₂`, the traces on `K` satisfy `B₁ ∩ K ⊊ B₂ ∩ K`. -/
theorem lemma_2_3_3_trace [IsAlgClosed K] (v : Valuation L Γ₀) (φ : K →+* L)
    (hnt : ∃ x : K, x ≠ 0 ∧ (v.comap φ) x < 1)
    {B₁ B₂ : Set L} (h₁ : IsValBallK v φ B₁) (h₂ : IsValBallK v φ B₂)
    (hsub : B₁ ⊆ B₂) (hne : B₁ ≠ B₂) :
    {x : K | φ x ∈ B₁} ⊂ {x : K | φ x ∈ B₂} := by
  obtain ⟨x, hx₂, hx₁⟩ := lemma_2_3_3 v φ hnt h₁ h₂ hsub hne
  refine ⟨fun y hy => hsub hy, ?_⟩
  intro hBA
  exact hx₁ (hBA hx₂)

end Johnson
namespace ValOneEC

variable {K : Type} [Field K] {N : Type} [Field N]
variable {Γ' : Type*} [LinearOrderedCommGroupWithZero Γ']

/-! ## The bridge: `IsKBall` is Johnson's `IsValBallK`

`IsKBall f w` is `IsValBallK w f` with the `singleton` constructor dropped (it is the closed ball
of radius `w (f 0) = 0`), so every `IsKBall` is an `IsValBallK` and Johnson's trace lemma applies
to it: the trace on `K` of an `IsKBall` of `N` is an `IsValBall` for `w.comap f`. -/

/-- A `K`-ball in the sense of `IsKBall` is a `K`-ball in Johnson's sense. -/
theorem isValBallK_of_isKBall {f : K →+* N} {w : Valuation N Γ'} {B : Set N}
    (hB : IsKBall f w B) : Johnson.IsValBallK w f B := by
  cases hB with
  | closed c b => exact Johnson.IsValBallK.closed c b
  | openball c b => exact Johnson.IsValBallK.openball c b
  | univ => exact Johnson.IsValBallK.univ

/-- The trace on `K` of an `IsKBall` of `N` is an `IsValBall` for `w.comap f`. -/
theorem isValBall_trace_of_isKBall {f : K →+* N} {w : Valuation N Γ'} {B : Set N}
    (hB : IsKBall f w B) :
    Johnson.IsValBall (w.comap f) {x : K | f x ∈ B} :=
  Johnson.isValBallK_trace w f (isValBallK_of_isKBall hB)

/-- **Johnson, Lemma 2.3.8, for an arbitrary finite index type.**  Let `B₀` be a `K`-ball of `N`
and `Bᵢ ⊆ B₀` finitely many `K`-balls.  If `B₀ \ ⋃ᵢ Bᵢ` is nonempty, it contains a point of `K`.

The proof is the one of `Johnson.lemma_2_3_8`; only the index type is general (`Fintype ι` in
place of `Fin n`), as `SwissCheese` is stated for an arbitrary finite index type. -/
theorem exists_mem_of_cheese [IsAlgClosed K] (f : K →+* N) (w : Valuation N Γ')
    (hnt : ∃ x : K, x ≠ 0 ∧ w (f x) < 1)
    {B₀ : Set N} (h₀ : IsKBall f w B₀) {ι : Type} [Fintype ι] (B : ι → Set N)
    (hB : ∀ i, IsKBall f w (B i)) (hBsub : ∀ i, B i ⊆ B₀)
    (hne : (B₀ \ ⋃ i, B i).Nonempty) :
    ∃ x : K, f x ∈ B₀ ∧ ∀ i, f x ∉ B i := by
  classical
  -- `hnt` in the form used by Johnson's 2.3.3 and 2.3.7
  have hnt' : ∃ x : K, x ≠ 0 ∧ (w.comap f) x < 1 := by
    obtain ⟨x, hx0, hx⟩ := hnt
    exact ⟨x, hx0, hx⟩
  obtain ⟨z, hz₀, hzU⟩ := hne
  have hzU' : ∀ i, z ∉ B i := fun i h => hzU (Set.mem_iUnion.mpr ⟨i, h⟩)
  -- every `Bᵢ` is strictly smaller than `B₀`
  have hproper : ∀ i, B i ≠ B₀ := by
    intro i hi
    exact hzU' i (hi ▸ hz₀)
  -- the traces on `K`
  set T : ι → Set K := fun i => {x : K | f x ∈ B i} with hT
  set T₀ : Set K := {x : K | f x ∈ B₀} with hT₀
  have hTball : ∀ i, Johnson.IsValBall (w.comap f) (T i) :=
    fun i => isValBall_trace_of_isKBall (hB i)
  have hT₀ball : Johnson.IsValBall (w.comap f) T₀ := isValBall_trace_of_isKBall h₀
  have hTsub : ∀ i, T i ⊆ T₀ := fun i x hx => hBsub i hx
  -- each trace is properly contained in the trace of `B₀` (Lemma 2.3.3)
  have hTne : ∀ i, T i ≠ T₀ := by
    intro i hi
    obtain ⟨x, hx₀, hxi⟩ :=
      Johnson.lemma_2_3_3 w f hnt' (isValBallK_of_isKBall (hB i)) (isValBallK_of_isKBall h₀)
        (hBsub i) (hproper i)
    have hxT₀ : x ∈ T₀ := hx₀
    rw [← hi] at hxT₀
    exact hxi hxT₀
  have hT₀ne : T₀.Nonempty := by
    obtain ⟨x, hx⟩ :=
      Johnson.isValBallK_exists_point w f (isValBallK_of_isKBall h₀) ⟨z, hz₀⟩
    exact ⟨x, hx⟩
  have hnt'' : ∃ x : K, 1 < (w.comap f) x :=
    (Johnson.exists_ne_zero_val_lt_one_iff (w.comap f)).mp hnt'
  -- Lemma 2.3.7 in `K`
  have hcover : T₀ ≠ ⋃ i ∈ (Finset.univ : Finset ι), T i :=
    Johnson.ne_finite_union_of_proper_subballs (w.comap f) hnt'' hT₀ball hT₀ne Finset.univ T
      (fun i _ => hTball i) (fun i _ => hTsub i) (fun i _ => hTne i)
  have hwit : ∃ x : K, x ∈ T₀ ∧ x ∉ ⋃ i ∈ (Finset.univ : Finset ι), T i := by
    by_contra hcon
    push Not at hcon
    refine hcover (Set.Subset.antisymm hcon ?_)
    intro x hx
    have hx' : ∃ i : ι, x ∈ T i := by simpa using hx
    obtain ⟨i, hxi⟩ := hx'
    exact hTsub i hxi
  obtain ⟨x, hx₀, hxU⟩ := hwit
  refine ⟨x, hx₀, ?_⟩
  intro i hxi
  exact hxU (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨Finset.mem_univ i, hxi⟩⟩)

/-- **Johnson, Lemma 2.3.8** (`CheeseMeetsBase`): a nonempty swiss cheese cut out by `K`-balls
meets the image of the base field `K`.  `K` is algebraically closed and `w ∘ f` nontrivial on
`K`; the nontriviality is essential (with `w ∘ f` trivial on `K`, the maximal ideal of `w`
punctured at `0` is a cheese with no `K`-point). -/
theorem cheeseMeetsBase [IsAlgClosed K] (f : K →+* N) (w : Valuation N Γ')
    (hnt : ∃ x : K, x ≠ 0 ∧ w (f x) < 1) : CheeseMeetsBase f w := by
  intro D hD hne
  obtain ⟨ι, hι, B₀, B, h₀, hB, hBsub, hD'⟩ := hD
  letI := hι
  have hne' : (B₀ \ ⋃ i, B i).Nonempty := by rw [← hD']; exact hne
  obtain ⟨c, hc⟩ := exists_mem_of_cheese f w hnt h₀ B hB hBsub hne'
  refine ⟨c, ?_⟩
  rw [hD']
  exact ⟨hc.1, fun h => hc.2 _ (Set.mem_iUnion.mp h).choose_spec⟩

end ValOneEC

#check @ValOneEC.cheeseMeetsBase
#print axioms ValOneEC.cheeseMeetsBase
#print axioms ValOneEC.exists_mem_of_cheese
#print axioms ValOneEC.isValBallK_of_isKBall
#print axioms ValOneEC.isValBall_trace_of_isKBall
#print axioms Johnson.lemma_2_3_3
#print axioms Johnson.ne_finite_union_of_proper_subballs
#print axioms Johnson.valueGroup_dlo
#print axioms Johnson.infinite_residueField
