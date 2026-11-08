import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.Valuation.Basic
import Section3.AlgebraicSubfieldModel
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.RingTheory.Henselian
import Section8.UniformBalls
import Section3.DefinableCompactness
import Section3.VFDefinableClosure
import Section4.FullDimension
import Section8.UnaryPolynomial
import Section3.SortedTuples
import Section3.SmallFiniteParameters

section

/-! For 8.4, evaluating at a new value below the old field's nonzero
values makes the least supported monomial determine the value. -/

set_option backward.isDefEq.respectTransparency false

open Polynomial
open scoped BigOperators

namespace SpecialTransformations.Section8

variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]

theorem polynomial_value_at_new_scale (v : Valuation K Γ) (F : Subfield K) {x : K} (hx : x ≠ 0)
    (hsmall : ∀ c : F, c ≠ 0 → v x < v c.val) (p : Polynomial F) (hp : p ≠ 0) :
    ∃ j ∈ p.support, v (p.eval₂ F.subtype x) = v (p.coeff j).val * v x ^ j := by
  classical
  obtain ⟨j, hj, hmin⟩ := Finset.exists_min_image p.support id (Polynomial.support_nonempty.mpr hp)
  let term (i : ℕ) : K := (p.coeff i).val * x ^ i
  have hj₀ := Polynomial.mem_support_iff.mp hj
  have h₁ : v x < 1 := by
    have h : v x < v (1 : K) := hsmall 1 one_ne_zero
    rwa [map_one] at h
  have hlt (i : ℕ) (hi : i ∈ p.support \ {j}) : v (term i) < v (term j) := by
    have hmem : i ∈ p.support ∧ i ≠ j := by
      simpa only [Finset.mem_sdiff, Finset.mem_singleton] using hi
    have hji : j < i := lt_of_le_of_ne (hmin i hmem.1) hmem.2.symm
    have hi₀ := Polynomial.mem_support_iff.mp hmem.1
    have hratio : v x < v (p.coeff j).val / v (p.coeff i).val := by
      have h := hsmall (p.coeff j / p.coeff i) (div_ne_zero hj₀ hi₀)
      change v x < v ((p.coeff j).val / (p.coeff i).val) at h
      rwa [map_div₀] at h
    have hiVal : 0 < v (p.coeff i).val :=
      pos_iff_ne_zero.mpr (v.ne_zero_iff.mpr (fun h => hi₀ (Subtype.ext h)))
    have hpow : v x ^ (i - j) ≤ v x := by
      obtain ⟨d, hd⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.sub_ne_zero_of_lt hji)
      rw [hd, pow_succ]
      exact mul_le_of_le_one_left zero_le (pow_le_one₀ zero_le h₁.le)
    have hco : v (p.coeff i).val * v x ^ (i - j) < v (p.coeff j).val := by
      calc
        _ ≤ v (p.coeff i).val * v x := mul_le_mul_of_nonneg_left hpow zero_le
        _ = v x * v (p.coeff i).val := mul_comm _ _
        _ < _ := (lt_div_iff₀ hiVal).mp hratio
    have he : v x ^ i = v x ^ j * v x ^ (i - j) := by
      rw [← pow_add, Nat.add_sub_of_le hji.le]
    change v ((p.coeff i).val * x ^ i) < v ((p.coeff j).val * x ^ j)
    rw [map_mul, map_mul, map_pow, map_pow, he]
    calc
      _ = (v (p.coeff i).val * v x ^ (i - j)) * v x ^ j := by ac_rfl
      _ < _ := mul_lt_mul_of_pos_right hco (pow_pos (pos_iff_ne_zero.mpr (v.ne_zero_iff.mpr hx)) _)
  have hsum : p.eval₂ F.subtype x = ∑ i ∈ p.support, term i := by
    rw [Polynomial.eval₂_eq_sum]
    rfl
  refine ⟨j, hj, ?_⟩
  rw [hsum, v.map_sum_eq_of_lt hj hlt]
  exact (map_mul v _ _).trans (congrArg (v (p.coeff j).val * ·) (map_pow v x j))

theorem rational_function_value_at_new_scale (v : Valuation K Γ) (F : Subfield K)
    {x : K} (hx : x ≠ 0) (hsmall : ∀ c : F, c ≠ 0 → v x < v c.val)
    {p q : Polynomial F} (hp : p ≠ 0) (hq : q ≠ 0) :
    ∃ c : F, c ≠ 0 ∧ ∃ j : ℤ,
      v (p.eval₂ F.subtype x / q.eval₂ F.subtype x) = v c.val * v x ^ j := by
  obtain ⟨i, hi, he₁⟩ := polynomial_value_at_new_scale v F hx hsmall p hp
  obtain ⟨j, hj, he₂⟩ := polynomial_value_at_new_scale v F hx hsmall q hq
  refine ⟨p.coeff i / q.coeff j, div_ne_zero (Polynomial.mem_support_iff.mp hi)
    (Polynomial.mem_support_iff.mp hj), (i : ℤ) - j, ?_⟩
  have he : v x ^ ((i : ℤ) - (j : ℤ)) = v x ^ i / v x ^ j := by
    rw [zpow_sub₀ (v.ne_zero_iff.mpr hx), zpow_natCast, zpow_natCast]
  change v (_ / _) = v ((p.coeff i).val / (q.coeff j).val) * _
  rw [map_div₀, map_div₀, he₁, he₂, he, mul_div_mul_comm]

theorem adjoin_simple_value_at_new_scale (v : Valuation K Γ) (F : Subfield K)
    {x y : K} (hx : x ≠ 0) (hsmall : ∀ c : F, c ≠ 0 → v x < v c.val) (hy : y ≠ 0)
    (hmem : y ∈ IntermediateField.adjoin F ({x} : Set K)) :
    ∃ c : F, c ≠ 0 ∧ ∃ j : ℤ, v y = v c.val * v x ^ j := by
  obtain ⟨p, q, he⟩ := (IntermediateField.mem_adjoin_simple_iff F y).mp hmem
  have hp : p ≠ 0 := by
    intro h
    apply hy
    simp only [h, map_zero, zero_div] at he
    exact he
  have hq : q ≠ 0 := by
    intro h
    apply hy
    simp only [h, map_zero, div_zero] at he
    exact he
  rw [he]
  exact rational_function_value_at_new_scale v F hx hsmall hp hq

theorem new_scale_zpow_ne_old (v : Valuation K Γ) (F : Subfield K) {x : K}
    (hsmall : ∀ c : F, c ≠ 0 → v x < v c.val) (c : F) (hc : c ≠ 0)
    (j : ℤ) (hj : j ≠ 0) : v x ^ j ≠ v c.val := by
  have h₁ : v x < 1 := by
    have h : v x < v (1 : K) := hsmall 1 one_ne_zero
    rwa [map_one] at h
  have hpos (d : F) (hd : d ≠ 0) (i : ℤ) (hi : 0 < i) : v x ^ i ≠ v d.val := by
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hi.le
    have hn : n ≠ 0 := by omega
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    rw [zpow_natCast, pow_succ]
    exact ne_of_lt ((mul_le_of_le_one_left zero_le (pow_le_one₀ zero_le h₁.le)).trans_lt (hsmall d hd))
  rcases lt_or_gt_of_ne hj with hj' | hj'
  · intro h
    apply hpos c⁻¹ (inv_ne_zero hc) (-j) (neg_pos.mpr hj')
    rw [zpow_neg, h]
    exact (map_inv₀ v c.val).symm
  · exact hpos c hc j hj'

theorem slope_numerator_divisible_at_new_scale (v : Valuation K Γ) (F : Subfield K)
    {x y : K} (hx : x ≠ 0) (hsmall : ∀ c : F, c ≠ 0 → v x < v c.val)
    (c d : F) (hc : c ≠ 0) (hd : d ≠ 0) (j : ℤ)
    (hy : v y = v d.val * v x ^ j) (p q : ℕ)
    (h : v y ^ q = v c.val ^ q * v x ^ p) : (p : ℤ) = (q : ℤ) * j := by
  have hX := v.ne_zero_iff.mpr hx
  let u := Units.mk0 (v x) hX
  have hpow : (v x ^ j) ^ q = v x ^ ((q : ℤ) * j) := by
    change ((u : Γ) ^ j) ^ q = (u : Γ) ^ ((q : ℤ) * j)
    calc
      _ = (↑((u ^ j) ^ q) : Γ) := by rw [Units.val_pow_eq_pow_val, Units.val_zpow_eq_zpow_val]
      _ = (↑(u ^ ((q : ℤ) * j)) : Γ) := by rw [Int.mul_comm, zpow_mul, zpow_natCast]
      _ = _ := Units.val_zpow_eq_zpow_val _ _
  have he : v d.val ^ q * v x ^ ((q : ℤ) * j) = v c.val ^ q * v x ^ p := by
    rw [hy, mul_pow, hpow] at h
    exact h
  have hd' : v x ^ ((p : ℤ) - (q : ℤ) * j) = v (((d / c) ^ q : F) : K) := by
    rw [zpow_sub₀ hX, zpow_natCast]
    apply (div_eq_iff (zpow_ne_zero _ hX)).mpr
    change v x ^ p = v ((d.val / c.val) ^ q) * v x ^ ((q : ℤ) * j)
    rw [map_pow, map_div₀, div_pow, div_mul_eq_mul_div₀]
    apply (eq_div_iff (pow_ne_zero _ (v.ne_zero_iff.mpr (fun h => hc (Subtype.ext h))))).mpr
    exact (mul_comm _ _).trans he.symm
  by_contra hne
  exact new_scale_zpow_ne_old v F hsmall ((d / c) ^ q)
    (pow_ne_zero _ (div_ne_zero hd hc)) _ (sub_ne_zero.mpr hne) hd'

end SpecialTransformations.Section8

end

section

/-! A singleton definable over a valued subfield has a value in that
subfield once its henselization is immediate. The valued-field inputs
are the immediacy of henselization and invariance of the algebraic
closure valuation under automorphisms over a henselian field. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Section3

namespace SpecialTransformations.Section8

variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]

private def valuedLanguageEquiv (v : Valuation K Γ) (σ : K ≃+* K)
    (hσ : ∀ x y, v (σ x) ≤ v (σ y) ↔ v x ≤ v y) :
    @Language.Equiv Language.val K K (FirstOrder.valStructure v) (FirstOrder.valStructure v) := by
  letI := FirstOrder.valStructure v
  refine { toEquiv := σ.toEquiv, map_fun' := ?_, map_rel' := ?_ }
  · intro arity f xs
    cases f with
    | add => exact map_add σ _ _
    | mul => exact map_mul σ _ _
    | neg => exact map_neg σ _
    | zero => exact map_zero σ
    | one => exact map_one σ
  · intro arity r xs
    cases r
    exact hσ _ _

/-- The two Engler--Prestel inputs, stated for the actual algebraic
closure inside the ambient valued field. The first records the value
part of immediacy. The second records henselian uniqueness. -/
def ImmediateHenselianExtension (v : Valuation K Γ) (F H : Subfield K) : Prop :=
  let E := algebraicClosure H K
  let w := v.comap E.toSubfield.subtype
  HenselianLocalRing (v.comap H.subtype).valuationSubring ∧
    (∀ c : H, ∃ d : F, v c.val = v d.val) ∧
    ∀ σ : E ≃ₐ[H] E, ∀ x y : E, w (σ x) ≤ w (σ y) ↔ w x ≤ w y

theorem definable_singleton_value_of_immediate_henselian
    [IsAlgClosed K] [CharZero K] (v : Valuation K Γ) (F H : Subfield K) (hFH : F ≤ H)
    (hnt : ∃ c : F, c ≠ 0 ∧ v c.val ≠ 1)
    (hH : ImmediateHenselianExtension v F H) (a : K)
    (ha : @Set.Definable₁ K (F : Set K) Language.val (FirstOrder.valStructure v) {a}) :
    ∃ d : F, v a = v d.val := by
  let E := algebraicClosure H K
  let w := v.comap E.toSubfield.subtype
  have hFE : F ≤ E.toSubfield := fun x hx =>
    (E.algebraMap_mem (⟨x, hFH hx⟩ : H))
  have hntE : ∃ c : E.toSubfield, c ≠ 0 ∧ v c.val ≠ 1 := by
    obtain ⟨c, hc, hv⟩ := hnt
    refine ⟨⟨c.val, hFE c.property⟩, ?_, hv⟩
    intro he
    apply hc
    exact Subtype.ext (congrArg (fun t : E.toSubfield => t.val) he)
  letI : IsAlgClosed E.toSubfield := IsAlgClosure.isAlgClosed H (K := E)
  letI := FirstOrder.valStructure v
  letI := FirstOrder.valStructure w
  obtain ⟨b, hb⟩ := valued_definable_nonempty_meets_subfield v E.toSubfield hntE {a}
    (ha.mono hFE) ⟨a, rfl⟩
  have hba : (b : K) = a := hb
  obtain ⟨φ, hφ⟩ := Set.definable_iff_exists_formula_sum.mp ha
  let names : F → E := fun c => ⟨c.val, hFE c.property⟩
  let j := valuedSubfieldElementary v E.toSubfield hntE
  have htest (x : E) :
      φ.Realize (Sum.elim names (fun _ : Fin 1 => x)) ↔ x.val = a := by
    have he := j.map_formula φ (Sum.elim names (fun _ : Fin 1 => x))
    have hnames : (j : E → K) ∘ Sum.elim names (fun _ : Fin 1 => x) =
        Sum.elim (Subtype.val : F → K) (fun _ : Fin 1 => x.val) := by
      funext i
      cases i <;> rfl
    rw [hnames] at he
    exact he.symm.trans ((Set.ext_iff.mp hφ (fun _ : Fin 1 => x.val)).symm)
  have hfixed (σ : E ≃ₐ[H] E) : σ b = b := by
    let e := valuedLanguageEquiv w σ.toRingEquiv (hH.2.2 σ)
    have he := e.toElementaryEmbedding.map_formula φ (Sum.elim names (fun _ : Fin 1 => b))
    have hnames : (e : E → E) ∘ Sum.elim names (fun _ : Fin 1 => b) =
        Sum.elim names (fun _ : Fin 1 => σ b) := by
      funext i
      cases i with
      | inl c =>
        change σ (algebraMap H E ⟨c.val, hFH c.property⟩) = _
        exact σ.commutes _
      | inr i => rfl
    change (φ.Realize ((e : E → E) ∘ Sum.elim names (fun _ : Fin 1 => b)) ↔
      φ.Realize (Sum.elim names (fun _ : Fin 1 => b))) at he
    rw [hnames] at he
    exact Subtype.ext ((htest _).mp (he.mpr ((htest b).mpr hba)) |>.trans hba.symm)
  obtain ⟨c, hc⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := H) (K := E) (b : E)).mpr hfixed
  obtain ⟨d, hd⟩ := hH.2.1 c
  have he : c.val = b.val := congrArg Subtype.val hc
  exact ⟨d, (congrArg v (hba.symm.trans he.symm)).trans hd⟩

end SpecialTransformations.Section8

end

section

/-! Realize a valuation smaller than every nonzero value of the field
generated by a small base. Each comparison is definable over the base,
even when that base does not name all elements of the generated field. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace SpecialTransformations.Section8

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ] [Valued (VFType (M := M)) Γ]

theorem exists_value_below_parameter_field (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) (S : Set M) (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) :
    ∃ x : VFType (M := M), x ≠ 0 ∧
      ∀ c : vfParameterField S, c ≠ 0 → Valued.v x < Valued.v c.val := by
  classical
  let v : Valuation (VFType (M := M)) Γ := Valued.v
  let F := vfParameterField S
  let F₀ := {c : F // c ≠ 0}
  let z : VFType (M := M) := 0
  have hz : DefinableClosureAt S .vf z.val :=
    vfParameterField_le_definableClosureField S F.zero_mem
  let A : Set M := {x | iVF x ∧ x ≠ z.val}
  have hA : S.Definable₁ LRV A := (definableAt_sort S .vf).raw_definable.inter hz.raw_definable.compl
  let bad (c : F₀) := (rawOpenBall z.val c.val.val.val)ᶜ
  have hbad (c : F₀) : S.Definable₁ LRV (bad c) := by
    let T := insert z.val (insert c.val.val.val S)
    have hT := rawOpenBall_definable (S := T) (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
    have hsort : ∀ x ∈ rawOpenBall z.val c.val.val.val, iVF x := fun x hx => hx.2.1
    apply (DefinableAt.eliminate_sorted_definable_params
      (raw_definable_sorted hc T _ .vf hT hsort) (S := S) ?_).raw_definable.compl
    intro x hx
    rcases hx with rfl | hx
    · exact ⟨.vf, hz⟩
    rcases hx with rfl | hx
    · exact ⟨.vf, vfParameterField_le_definableClosureField S c.val.property⟩
    · rcases TypedModelMap.sort_cover x with h | h
      · exact ⟨.vf, definableClosureAt_of_mem hx h⟩
      · exact ⟨.rv, definableClosureAt_of_mem hx h⟩
  by_contra hnone
  have hcov : ∀ x ∈ A, ∃ B ∈ Set.range bad, x ∈ B := by
    rintro x ⟨hx, hx₀⟩
    let a : VFType (M := M) := ⟨x, hx⟩
    have ha : a ≠ 0 := fun h => hx₀ (congrArg Subtype.val h)
    have he : ∃ c : F₀, ¬ v a < v c.val.val := by
      by_contra h
      exact hnone ⟨a, ha, fun c hc => not_not.mp (fun hlt => h ⟨⟨c, hc⟩, hlt⟩)⟩
    obtain ⟨c, hc⟩ := he
    refine ⟨bad c, Set.mem_range_self c, fun h => hc ?_⟩
    have hnonzero : c.val.val ≠ 0 := fun h => c.property (Subtype.ext h)
    simpa only [z, sub_zero] using (mem_rawOpenBall_iff v hv z c.val.val a hnonzero).mp h
  obtain ⟨C, hC, hsub, hCcov⟩ := hs.definable_finite_subcover S hsmall A hA (Set.range bad)
    (by rintro _ ⟨c, rfl⟩; exact hbad c) hcov
  letI : Fintype C := hC.fintype
  let c (B : C) := Classical.choose (hsub B.property)
  have he (B : C) : bad (c B) = B.val := Classical.choose_spec (hsub B.property)
  let Q := insert (1 : VFType (M := M)) (Finset.univ.image (fun B : C => (c B).val.val))
  obtain ⟨r, hr, hmin⟩ := Finset.exists_min_image Q v ⟨1, Finset.mem_insert_self _ _⟩
  have hr₀ : r ≠ 0 := by
    rcases Finset.mem_insert.mp hr with h | h
    · exact h.symm ▸ one_ne_zero
    · obtain ⟨B, _, rfl⟩ := Finset.mem_image.mp h
      exact fun hz => (c B).property (Subtype.ext hz)
  obtain ⟨e, he₀, he₁⟩ := model_valuation_nontrivial hv
  let a := e * r
  have ha₀ : a ≠ 0 := mul_ne_zero he₀ hr₀
  have haA : a.val ∈ A := ⟨a.property, fun h => ha₀ (Subtype.ext h)⟩
  have hav : v a < v r := by
    rw [show a = e * r from rfl, map_mul]
    simpa only [one_mul] using
      mul_lt_mul_of_pos_right he₁ (pos_iff_ne_zero.mpr (v.ne_zero_iff.mpr hr₀))
  obtain ⟨B, hBC, haB⟩ := hCcov a.val haA
  let B' : C := ⟨B, hBC⟩
  have hx : a.val ∈ bad (c B') := (he B').symm ▸ haB
  apply hx
  have hc₀ : (c B').val.val ≠ 0 := fun h => (c B').property (Subtype.ext h)
  apply (mem_rawOpenBall_iff v hv z (c B').val.val a hc₀).mpr
  rw [show z = 0 from rfl, sub_zero]
  exact hav.trans_le (hmin _ (Finset.mem_insert.mpr
    (Or.inr (Finset.mem_image.mpr ⟨B', Finset.mem_univ _, rfl⟩))))

end SpecialTransformations.Section8

end

section

/-! The integrality step of 8.4 in the valued-field language.
The graph point is a definable singleton over the field generated by
the original coefficient field and the input. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language

namespace SpecialTransformations.Section8

variable {K Γ : Type} [Field K] [IsAlgClosed K] [CharZero K] [LinearOrderedCommGroupWithZero Γ]

theorem definable_slope_integral_at_new_scale (v : Valuation K Γ) (F H : Subfield K)
    {x y : K} (hx : x ≠ 0) (hy : y ≠ 0)
    (hsmall : ∀ c : F, c ≠ 0 → v x < v c.val)
    (hEH : (IntermediateField.adjoin F ({x} : Set K)).toSubfield ≤ H)
    (hH : ImmediateHenselianExtension v (IntermediateField.adjoin F ({x} : Set K)).toSubfield H)
    (hdef : @Set.Definable₁ K ((IntermediateField.adjoin F ({x} : Set K)).toSubfield : Set K)
      Language.val (FirstOrder.valStructure v) {y})
    (c : F) (hc : c ≠ 0) (p q : ℕ) (h : v y ^ q = v c.val ^ q * v x ^ p) :
    ∃ j : ℤ, (p : ℤ) = (q : ℤ) * j := by
  let E := (IntermediateField.adjoin F ({x} : Set K)).toSubfield
  have hxE : x ∈ E := IntermediateField.subset_adjoin F _ (Set.mem_singleton x)
  have hnt : ∃ a : E, a ≠ 0 ∧ v a.val ≠ 1 := by
    refine ⟨⟨x, hxE⟩, fun he => hx (congrArg Subtype.val he), ?_⟩
    have h : v x < v (1 : K) := hsmall 1 one_ne_zero
    rw [map_one] at h
    exact h.ne
  obtain ⟨d, hd⟩ := definable_singleton_value_of_immediate_henselian v E H hEH hnt hH y hdef
  have hd₀ : d.val ≠ 0 := by
    intro he
    rw [he, map_zero] at hd
    exact (v.ne_zero_iff.mpr hy) hd
  obtain ⟨e, he, j, hj⟩ := adjoin_simple_value_at_new_scale v F hx hsmall hd₀ d.property
  exact ⟨j, slope_numerator_divisible_at_new_scale v F hx hsmall c e hc he j (hd.trans hj) p q h⟩

end SpecialTransformations.Section8

end

section

/-! A finite VF parameter set suffices for all values of a definable
unary function. RV parameters are named by VF representatives.
This is used internally to apply the valued-field slope argument. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3

namespace SpecialTransformations.Section8

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ]

theorem unaryScalarGraph_finite_vf_support (hc : CanonicalStructure.IsCanonical (M := M))
    {S : Set M} {f : VFType (M := M) → VFType (M := M)}
    (hf : S.Definable LRV (unaryScalarGraph f)) :
    ∃ B : Set M, B.Finite ∧ (∀ z ∈ B, iVF z) ∧ B.Definable LRV (unaryScalarGraph f) := by
  obtain ⟨A, _, hA⟩ := Set.definable_iff_finitely_definable.mp hf
  have hrep (t : A) : ∃ a : VFType (M := M),
      a.val = t.val ∨ ((CanonicalRV.encodedRv a).val = t.val) := by
    rcases TypedModelMap.sort_cover t.val with ht | ht
    · exact ⟨⟨t.val, ht⟩, Or.inl rfl⟩
    · obtain ⟨a, ha⟩ := CanonicalRV.encodedRv_surjective ⟨t.val, ht⟩
      exact ⟨a, Or.inr (congrArg Subtype.val ha)⟩
  choose a ha using hrep
  let B := Set.range (fun i : A => (a i).val)
  refine ⟨B, Set.finite_range _, ?_, ?_⟩
  · rintro _ ⟨i, rfl⟩
    exact (a i).property
  · have hs : DefinableOver (↑A : Set M) (fun _ : Fin 2 => .vf) (unaryScalarGraph f) :=
      raw_definableOver_sorted hc _ _ _ hA (by
        rintro z ⟨x, hx, hy⟩ i
        fin_cases i
        · exact hx ▸ x.property
        · exact hy ▸ (f x).property)
    apply (hs.eliminate_sorted_definable_params (S := B) ?_).raw_definable
    intro t ht
    let i : A := ⟨t, ht⟩
    have haB : DefinableClosureAt B .vf (a i).val :=
      definableClosureAt_of_mem (Set.mem_range_self i) (a i).property
    rcases ha i with he | he
    · exact ⟨.vf, by change DefinableClosureAt B .vf i.val; rwa [← he]⟩
    · have hr : DefinableClosureAt B .rv (CanonicalRV.encodedRv (a i)).val :=
        definableClosureAt_function_symbol B Fn.rvMap ![(a i).val]
          (fun j => by fin_cases j; exact (a i).property)
          (fun j => by fin_cases j; exact haB)
      exact ⟨.rv, by change DefinableClosureAt B .rv i.val; rwa [← he]⟩

theorem unaryScalarGraph_value_definable (hc : CanonicalStructure.IsCanonical (M := M))
    {S : Set M} {f : VFType (M := M) → VFType (M := M)}
    (hf : S.Definable LRV (unaryScalarGraph f)) (x : VFType (M := M)) :
    DefinableClosureAt (insert x.val S) .vf (f x).val := by
  let B := insert x.val S
  let e (z : Fin 1 → M) : Fin 2 → M := ![x.val, z 0]
  have he : B.DefinableMap LRV e := by
    intro i
    fin_cases i
    · exact LRV.definableFun_const _ (Set.mem_insert _ _)
    · exact Set.DefinableFun.proj LRV
  have h := (hf.mono (Set.subset_insert _ _)).preimage_map he
  apply raw_definable_sorted hc B {(f x).val} .vf ?_ (by
    rintro _ rfl
    exact (f x).property)
  change B.Definable LRV {z : Fin 1 → M | z 0 ∈ ({(f x).val} : Set M)}
  convert h using 1
  ext z
  change z 0 = (f x).val ↔ e z ∈ unaryScalarGraph f
  constructor
  · intro hz
    exact ⟨x, rfl, hz.symm⟩
  · rintro ⟨y, hx, hy⟩
    have hxy : y = x := Subtype.ext hx
    subst y
    exact hy.symm

theorem unaryScalarGraph_value_definable_valued (hc : CanonicalStructure.IsCanonical (M := M))
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)
    {S : Set M} {f : VFType (M := M) → VFType (M := M)}
    (hf : S.Definable LRV (unaryScalarGraph f)) (x : VFType (M := M))
    (F : Subfield (VFType (M := M)))
    (hF : insert x.val S ⊆ Subtype.val '' (F : Set (VFType (M := M)))) :
    @Set.Definable₁ _ (F : Set (VFType (M := M))) Language.val (FirstOrder.valStructure v) {f x} := by
  have h := decode_preimage_definable_over_subfield v hv F (insert x.val S) {(f x).val}
    hF .vf (unaryScalarGraph_value_definable hc hf x)
  convert h using 1
  ext a
  change a = f x ↔ a.val = (f x).val
  exact ⟨fun he => congrArg Subtype.val he, fun he => Subtype.ext he⟩

end SpecialTransformations.Section8

end

section

/-! A positive power law for a definable unary germ has integral slope.
Use the new value over a finite VF presentation of the graph and the
explicit immediate-henselization input. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3

namespace SpecialTransformations.Section8

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ] [Valued (VFType (M := M)) Γ]

theorem definable_power_germ_slope_integral [CharZero (VFType (M := M))]
    (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hEP : ∀ E : Subfield (VFType (M := M)), ∃ H, E ≤ H ∧ ImmediateHenselianExtension Valued.v E H)
    {S : Set M} {f : VFType (M := M) → VFType (M := M)} (hf : S.Definable LRV (unaryScalarGraph f))
    (c r : VFType (M := M)) (hc₀ : c ≠ 0) (hr₀ : r ≠ 0)
    {p q : ℕ} (hq : 0 < q)
    (h : ∀ x : VFType (M := M), x ≠ 0 → Valued.v x < Valued.v r →
      Valued.v (f x) ^ q = Valued.v c ^ q * Valued.v x ^ p) :
    ∃ j : ℤ, (p : ℤ) = (q : ℤ) * j := by
  let v : Valuation (VFType (M := M)) Γ := Valued.v
  obtain ⟨B, hBfin, hBvf, hB⟩ := unaryScalarGraph_finite_vf_support hc hf
  let T := insert r.val (insert c.val B)
  have hT : Cardinal.mk T < κ := (hBfin.insert c.val |>.insert r.val).lt_aleph0.trans_le hκ
  let F := vfParameterField T
  have hcF : c ∈ F := Subfield.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hrF : r ∈ F := Subfield.subset_closure (Set.mem_insert _ _)
  obtain ⟨x, hx, hsmall⟩ := exists_value_below_parameter_field hc hs T hT hv
  have hxr : v x < v r := hsmall ⟨r, hrF⟩ (fun he => hr₀ (congrArg Subtype.val he))
  have hpow := h x hx hxr
  have hfx : f x ≠ 0 := by
    intro h₀
    rw [h₀, map_zero, zero_pow hq.ne'] at hpow
    exact (mul_ne_zero (pow_ne_zero _ (v.ne_zero_iff.mpr hc₀)) (pow_ne_zero _ (v.ne_zero_iff.mpr hx)))
      hpow.symm
  let E := (IntermediateField.adjoin F ({x} : Set (VFType (M := M)))).toSubfield
  have hxE : x ∈ E := IntermediateField.subset_adjoin F _ (Set.mem_singleton x)
  have hFE : F ≤ E := fun z hz => (IntermediateField.adjoin F ({x} : Set (VFType (M := M)))).algebraMap_mem
    (⟨z, hz⟩ : F)
  have hnames : insert x.val B ⊆ Subtype.val '' (E : Set (VFType (M := M))) := by
    intro z hz
    rcases hz with rfl | hz
    · exact ⟨x, hxE, rfl⟩
    · refine ⟨⟨z, hBvf z hz⟩, hFE (Subfield.subset_closure ?_), rfl⟩
      exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ hz)
  have hdef := unaryScalarGraph_value_definable_valued hc v hv hB x E hnames
  obtain ⟨H, hEH, hH⟩ := hEP E
  letI : IsAlgClosed (VFType (M := M)) := VFAlgClosed.isAlgClosed_vfType
  exact definable_slope_integral_at_new_scale v F H hx hfx hsmall hEH hH hdef ⟨c, hcF⟩
    (fun he => hc₀ (congrArg Subtype.val he)) p q hpow

end SpecialTransformations.Section8

end
