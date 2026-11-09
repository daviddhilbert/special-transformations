import Section8.PowerEstimateCore
import Section8.IsolationRadius
import Section9.LimitGeometry
import Mathlib.Tactic.Abel

set_option backward.isDefEq.respectTransparency false

/-! Valued-field differentiation in Definition 9.6 and the chain rule in
Lemma 9.7. The estimates use the actual value quotient in the paper's
order, where the absorbing value is the greatest element. -/

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section8
open scoped BigOperators

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n m l : ℕ}

local notation "VF" => VFType (M := M)
local notation "Γ" => Values.Gamma (M := M)
local notation "Γ∞" => Values.GammaTop (M := M)
local notation "v" => Values.vfValueHom (M := M)

/-- The valuation of the first-order remainder exceeds the value of the
increment by an arbitrarily prescribed finite value. The increment is
punctured so the two values need not be subtracted at infinity. -/
def HasVFDerivativeAt (f : (Fin n → VF) → Fin m → VF) (a : Fin n → VF)
    (L : (Fin n → VF) →ₗ[VF] (Fin m → VF)) : Prop :=
  ∀ ε : Γ, ∃ δ : Γ, ∀ b : Fin n → VF,
    b ≠ 0 → δ.val < vfTupleValue b →
      ε.val * vfTupleValue b < vfTupleValue (f (a + b) - f a - L b)

/-- Existence of the valued-field derivative at a point. -/
def VFDifferentiableAt (f : (Fin n → VF) → Fin m → VF) (a : Fin n → VF) : Prop :=
  ∃ L : (Fin n → VF) →ₗ[VF] (Fin m → VF), HasVFDerivativeAt f a L

theorem vfValue_eq_zero_iff (x : VF) : v x = 0 ↔ x = 0 := by
  change Values.vrv (CanonicalRV.encodedRv x) = 0 ↔ x = 0
  rw [← Values.infinity_eq_zero, Values.vrv_eq_infinity_iff]
  exact CanonicalRV.encodedRv_zero_iff x

theorem finiteValue_ne_zero (γ : Γ) : γ.val ≠ 0 := by
  simpa only [Values.infinity_eq_zero] using γ.property

theorem value_lt_infinity {a : Γ∞} (ha : a ≠ 0) : a < 0 := by
  rw [← Values.infinity_eq_zero]
  exact lt_of_le_of_ne (Values.le_infinity a) (by simpa only [Values.infinity_eq_zero] using ha)

private theorem value_mul_lt_left {a b c : Γ∞} (h : a < b) (hc : c ≠ 0) : c * a < c * b :=
  lt_of_le_of_ne (mul_le_mul' le_rfl h.le) (fun he => h.ne (mul_left_cancel₀ hc he))

private theorem le_vfTupleValue_iff (t : Γ∞) (b : Fin n → VF) :
    t ≤ vfTupleValue b ↔ ∀ i, t ≤ v (b i) := by
  constructor
  · intro h i
    exact h.trans (vfTupleValue_le_component b i)
  · intro h
    by_cases hn : 0 < n
    · obtain ⟨i, hi⟩ := vfTupleValue_eq_component b hn
      rw [hi]
      exact h i
    · rw [vfTupleValue, dif_neg hn]
      exact Values.le_infinity t

theorem vfTupleValue_ne_zero {b : Fin n → VF} (hb : b ≠ 0) :
    vfTupleValue b ≠ 0 := by
  intro h
  apply hb
  funext i
  apply (vfValue_eq_zero_iff (b i)).mp
  apply le_antisymm
  · simpa only [Values.infinity_eq_zero] using Values.le_infinity (v (b i))
  · rw [← h]
    exact vfTupleValue_le_component b i

private theorem vfTupleValue_smul (c : VF) (b : Fin n → VF) :
    vfTupleValue (c • b) = v c * vfTupleValue b := by
  by_cases hn : 0 < n
  · apply le_antisymm
    · obtain ⟨i, hi⟩ := vfTupleValue_eq_component b hn
      calc
        vfTupleValue (c • b) ≤ v ((c • b) i) := vfTupleValue_le_component _ i
        _ = v c * vfTupleValue b := by
          rw [hi]
          change v (c * b i) = v c * v (b i)
          exact map_mul v c (b i)
    · apply (le_vfTupleValue_iff _ _).mpr
      intro i
      change v c * vfTupleValue b ≤ v (c * b i)
      rw [map_mul]
      exact mul_le_mul' le_rfl (vfTupleValue_le_component b i)
  · simp only [vfTupleValue, dif_neg hn, Values.infinity_eq_zero, mul_zero]

private theorem vfTupleValue_neg (b : Fin n → VF) : vfTupleValue (-b) = vfTupleValue b := by
  apply le_antisymm
  · apply (le_vfTupleValue_iff _ _).mpr
    intro i
    have hi : vfTupleValue (-b) ≤ v (-b i) := vfTupleValue_le_component (-b) i
    rwa [vfValue_neg] at hi
  · apply (le_vfTupleValue_iff _ _).mpr
    intro i
    change vfTupleValue b ≤ v (-b i)
    rw [vfValue_neg]
    exact vfTupleValue_le_component b i

private theorem vfValue_add_bound (x y : VF) : min (v x) (v y) ≤ v (x + y) := by
  let w := Values.presentationValuation (M := M)
  have h := w.map_add x y
  rcases le_total (w x) (w y) with hxy | hyx
  · rw [max_eq_right hxy] at h
    exact (min_le_right _ _).trans ((Values.vf_pred_iff_gamma_le _ _).mp
      ((Values.presentation_compatible _ _).mpr h))
  · rw [max_eq_left hyx] at h
    exact (min_le_left _ _).trans ((Values.vf_pred_iff_gamma_le _ _).mp
      ((Values.presentation_compatible _ _).mpr h))

private theorem vfValue_sum_bound {ι : Type} (s : Finset ι) (q : ι → VF) (t : Γ∞)
    (h : ∀ i ∈ s, t ≤ v (q i)) : t ≤ v (∑ i ∈ s, q i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, map_zero]
    rw [← Values.infinity_eq_zero]
    exact Values.le_infinity t
  | insert j s hjs ih =>
    rw [Finset.sum_insert hjs]
    exact (le_min (h j (Finset.mem_insert_self _ _))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))).trans (vfValue_add_bound _ _)

private def finiteValue (t : Γ∞) (ht : t ≠ 0) : Γ :=
  ⟨t, fun h => ht (h.trans Values.infinity_eq_zero)⟩

/-- A linear map lowers the minimum coordinate valuation by at most a
fixed finite value, uniformly on its domain. -/
theorem vfLinearMap_value_bound (L : (Fin n → VF) →ₗ[VF] (Fin m → VF)) :
    ∃ c : Γ, ∀ b : Fin n → VF, c.val * vfTupleValue b ≤ vfTupleValue (L b) := by
  classical
  let coeff (ij : Fin n × Fin m) := L (Pi.single ij.1 (1 : VF)) ij.2
  let shift (ij : Fin n × Fin m) : Γ :=
    if h : v (coeff ij) = 0 then 1 else finiteValue (v (coeff ij)) h
  let shifts : Finset Γ := insert 1 (Finset.univ.image shift)
  have hne : shifts.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  let c := shifts.min' hne
  have hcoeff (ij : Fin n × Fin m) : c.val ≤ v (coeff ij) := by
    by_cases h : v (coeff ij) = 0
    · rw [h, ← Values.infinity_eq_zero]
      exact Values.le_infinity c.val
    · have hi : shift ij ∈ shifts := Finset.mem_insert_of_mem
        (Finset.mem_image.mpr ⟨ij, Finset.mem_univ _, rfl⟩)
      have hmin : c.val ≤ (shift ij).val := Finset.min'_le shifts _ hi
      have he : shift ij = finiteValue (v (coeff ij)) h := dif_neg h
      rw [he] at hmin
      exact hmin
  refine ⟨c, fun b => (le_vfTupleValue_iff _ _).mpr ?_⟩
  intro j
  have expand : (∑ i : Fin n, b i • Pi.single i (1 : VF)) = b := by
    funext k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single k]
    · rw [Pi.single_eq_same]
      exact mul_one (b k)
    · intro i _ hik
      rw [Pi.single_eq_of_ne (Ne.symm hik)]
      exact mul_zero (b i)
    · simp
  have hsum : L b j = ∑ i : Fin n, b i * coeff (i,j) := by
    calc
      _ = L (∑ i : Fin n, b i • Pi.single i (1 : VF)) j := congrArg (fun z => L z j) expand.symm
      _ = _ := by
        rw [map_sum, Finset.sum_apply]
        apply Finset.sum_congr rfl
        intro i _
        exact congrFun (L.map_smul (b i) (Pi.single i 1)) j
  rw [hsum]
  apply vfValue_sum_bound
  intro i _
  rw [map_mul, mul_comm (v (b i))]
  exact mul_le_mul' (hcoeff (i,j)) (vfTupleValue_le_component b i)

private theorem gamma_mul_cancel (a d : Γ) :
    (a * d⁻¹).val * d.val = a.val := by
  rw [← Values.gamma_val_mul, inv_mul_cancel_right]

/-- A differentiable map has a finite lower valuation bound for its
increment on some neighbourhood. -/
private theorem HasVFDerivativeAt.increment_bound
    {f : (Fin n → VF) → Fin m → VF} {a : Fin n → VF}
    {L : (Fin n → VF) →ₗ[VF] (Fin m → VF)} (hf : HasVFDerivativeAt f a L) :
    ∃ c δ : Γ, ∀ b : Fin n → VF, b ≠ 0 → δ.val < vfTupleValue b →
      c.val * vfTupleValue b ≤ vfTupleValue (f (a + b) - f a) := by
  obtain ⟨k, hk⟩ := vfLinearMap_value_bound L
  obtain ⟨δ, hδ⟩ := hf 1
  let c := min k 1
  refine ⟨c, δ, fun b hb hsmall => ?_⟩
  let r := f (a + b) - f a - L b
  have hr : vfTupleValue b ≤ vfTupleValue r := by
    simpa only [Values.gamma_val_one, one_mul] using (hδ b hb hsmall).le
  have hc : c.val ≤ k.val := min_le_left _ _
  have hc' : c.val ≤ (1 : Γ∞) := min_le_right k (1 : Γ)
  have hc₁ : c.val * vfTupleValue b ≤ vfTupleValue b := by
    simpa only [one_mul] using mul_le_mul' hc' (le_refl (vfTupleValue b))
  calc
    c.val * vfTupleValue b ≤ min (vfTupleValue r) (vfTupleValue (L b)) := by
      exact le_min (hc₁.trans hr) ((mul_le_mul' hc le_rfl).trans (hk b))
    _ ≤ vfTupleValue (r + L b) := vfTupleValue_add_ge_min _ _
    _ = vfTupleValue (f (a + b) - f a) := by rw [show r + L b = _ from sub_add_cancel _ _]

/-- A differentiable VF map carries a sufficiently small input ball
into any prescribed output ball about its value. -/
theorem HasVFDerivativeAt.maps_vfBall
    {f : (Fin n → VF) → Fin m → VF} {a : Fin n → VF}
    {L : (Fin n → VF) →ₗ[VF] (Fin m → VF)} (hf : HasVFDerivativeAt f a L)
    (ε : Γ) : ∃ δ : Γ, Set.MapsTo f (vfBall a δ) (vfBall (f a) ε) := by
  obtain ⟨c, δ₁, h₁⟩ := hf.increment_bound
  let δ := max δ₁ (ε * c⁻¹)
  refine ⟨δ, fun x hx => ?_⟩
  by_cases he : x = a
  · rw [he]
    exact mem_vfBall_self _ _
  let b := x - a
  have hb : b ≠ 0 := sub_ne_zero.mpr he
  have hδ : δ.val < vfTupleValue b := by
    by_cases hn : 0 < n
    · obtain ⟨i, hi⟩ := vfTupleValue_eq_component b hn
      rw [hi]
      exact hx i
    · rw [vfTupleValue, dif_neg hn]
      exact (gamma_lt_value_zero δ).trans_eq (by rw [map_zero, Values.infinity_eq_zero])
  have hclose : δ₁.val < vfTupleValue b := (show δ₁.val ≤ δ.val from le_max_left _ _).trans_lt hδ
  have hsmall : (ε * c⁻¹).val < vfTupleValue b :=
    (show (ε * c⁻¹).val ≤ δ.val from le_max_right _ _).trans_lt hδ
  have hbound := h₁ b hb hclose
  rw [show a + b = x by dsimp [b]; abel] at hbound
  have hε : ε.val = c.val * (ε * c⁻¹).val := by
    rw [mul_comm]
    exact (gamma_mul_cancel ε c).symm
  intro i
  rw [show ε.val = c.val * (ε * c⁻¹).val from hε]
  exact ((value_mul_lt_left hsmall (finiteValue_ne_zero c)).trans_le hbound).trans_le
    (vfTupleValue_le_component (f x - f a) i)

/-- Lemma 9.7, with matrix multiplication written as composition of
the two VF-linear maps. -/
theorem HasVFDerivativeAt.comp
    {f : (Fin n → VF) → Fin m → VF} {g : (Fin m → VF) → Fin l → VF}
    {a : Fin n → VF} {L : (Fin n → VF) →ₗ[VF] (Fin m → VF)}
    {D : (Fin m → VF) →ₗ[VF] (Fin l → VF)}
    (hg : HasVFDerivativeAt g (f a) D) (hf : HasVFDerivativeAt f a L) :
    HasVFDerivativeAt (g ∘ f) a (D.comp L) := by
  obtain ⟨c, δ₁, h₁⟩ := hf.increment_bound
  obtain ⟨d, hd⟩ := vfLinearMap_value_bound D
  intro ε
  obtain ⟨δ₂, h₂⟩ := hf (ε * d⁻¹)
  obtain ⟨δ₃, h₃⟩ := hg (ε * c⁻¹)
  let r₃ := δ₃ * c⁻¹
  refine ⟨max δ₁ (max δ₂ r₃), fun b hb hsmall => ?_⟩
  have hb₁ : δ₁.val < vfTupleValue b :=
    (show δ₁.val ≤ (max δ₁ (max δ₂ r₃)).val from le_max_left _ _).trans_lt hsmall
  have hb₂ : δ₂.val < vfTupleValue b :=
    (show δ₂.val ≤ (max δ₁ (max δ₂ r₃)).val from
      (le_max_left _ _).trans (le_max_right _ _)).trans_lt hsmall
  have hb₃ : r₃.val < vfTupleValue b :=
    (show r₃.val ≤ (max δ₁ (max δ₂ r₃)).val from
      (le_max_right _ _).trans (le_max_right _ _)).trans_lt hsmall
  let w := f (a + b) - f a
  let u := w - L b
  have hw : c.val * vfTupleValue b ≤ vfTupleValue w := h₁ b hb hb₁
  have hd₀ : d.val ≠ 0 := finiteValue_ne_zero d
  have hc₀ : c.val ≠ 0 := finiteValue_ne_zero c
  have hDu : ε.val * vfTupleValue b < vfTupleValue (D u) := by
    calc
      ε.val * vfTupleValue b = d.val * ((ε * d⁻¹).val * vfTupleValue b) := by
        rw [← mul_assoc, mul_comm d.val, gamma_mul_cancel]
      _ < d.val * vfTupleValue u := value_mul_lt_left (h₂ b hb hb₂) hd₀
      _ ≤ vfTupleValue (D u) := hd u
  have hgw : ε.val * vfTupleValue b < vfTupleValue (g (f a + w) - g (f a) - D w) := by
    by_cases hw₀ : w = 0
    · have he : g (f a + w) - g (f a) - D w = 0 := by
        rw [hw₀, add_zero, sub_self, D.map_zero, sub_zero]
      rw [he, vfTupleValue_zero]
      exact value_lt_infinity (mul_ne_zero (finiteValue_ne_zero ε) (vfTupleValue_ne_zero hb))
    · have hclose : δ₃.val < vfTupleValue w := by
        calc
          δ₃.val = c.val * r₃.val := by rw [mul_comm]; exact (gamma_mul_cancel δ₃ c).symm
          _ < c.val * vfTupleValue b := value_mul_lt_left hb₃ hc₀
          _ ≤ vfTupleValue w := hw
      calc
        ε.val * vfTupleValue b = (ε * c⁻¹).val * (c.val * vfTupleValue b) := by
          rw [← mul_assoc, gamma_mul_cancel]
        _ ≤ (ε * c⁻¹).val * vfTupleValue w := mul_le_mul' le_rfl hw
        _ < vfTupleValue (g (f a + w) - g (f a) - D w) := h₃ w hw₀ hclose
  have he : (g ∘ f) (a + b) - (g ∘ f) a - (D.comp L) b =
      (g (f a + w) - g (f a) - D w) + D u := by
    rw [show f a + w = f (a + b) by dsimp [w]; abel]
    simp only [Function.comp_apply, LinearMap.comp_apply, u, map_sub]
    abel
  rw [he]
  exact (lt_min hgw hDu).trans_le (vfTupleValue_add_ge_min _ _)

/-- Two valued-field derivatives of the same function at the same point
agree as linear maps. -/
theorem HasVFDerivativeAt.unique
    {f : (Fin n → VF) → Fin m → VF} {a : Fin n → VF}
    {L D : (Fin n → VF) →ₗ[VF] (Fin m → VF)}
    (hL : HasVFDerivativeAt f a L) (hD : HasVFDerivativeAt f a D) : L = D := by
  apply LinearMap.ext
  intro b
  by_contra hne
  have hb : b ≠ 0 := by intro h; rw [h, map_zero, map_zero] at hne; exact hne rfl
  have hdiff : L b - D b ≠ 0 := sub_ne_zero.mpr hne
  let t := finiteValue (vfTupleValue b) (vfTupleValue_ne_zero hb)
  let ε := finiteValue (vfTupleValue (L b - D b)) (vfTupleValue_ne_zero hdiff) * t⁻¹
  have hε : ε.val * vfTupleValue b = vfTupleValue (L b - D b) := gamma_mul_cancel _ t
  obtain ⟨rL, hrL⟩ := hL ε
  obtain ⟨rD, hrD⟩ := hD ε
  obtain ⟨r, hr⟩ := exists_gt (max rL rD)
  obtain ⟨z, hz, hvz⟩ := gamma_has_vf_representative (r * t⁻¹)
  let e := z • b
  have he₀ : e ≠ 0 := smul_ne_zero hz hb
  have he : vfTupleValue e = r.val := by
    rw [show e = z • b from rfl, vfTupleValue_smul, hvz]
    exact gamma_mul_cancel r t
  have hcloseL : rL.val < vfTupleValue e := by
    rw [he]; exact (le_max_left _ _).trans_lt hr
  have hcloseD : rD.val < vfTupleValue e := by
    rw [he]; exact (le_max_right _ _).trans_lt hr
  let eL := f (a + e) - f a - L e
  let eD := f (a + e) - f a - D e
  have hminus : L e - D e = eD + -eL := by dsimp [eL, eD]; abel
  have hs : ε.val * vfTupleValue e < vfTupleValue (L e - D e) := by
    rw [hminus]
    have hsmallNeg : ε.val * vfTupleValue e < vfTupleValue (-eL) := by
      rw [vfTupleValue_neg]
      exact hrL e he₀ hcloseL
    exact (lt_min (hrD e he₀ hcloseD) hsmallNeg).trans_le (vfTupleValue_add_ge_min _ _)
  have heq : vfTupleValue (L e - D e) = ε.val * vfTupleValue e := by
    have hlin : L e - D e = z • (L b - D b) := by
      change L (z • b) - D (z • b) = _
      exact (congrArg₂ (· - ·) (L.map_smul z b) (D.map_smul z b)).trans (smul_sub z _ _).symm
    rw [hlin, show e = z • b from rfl, vfTupleValue_smul, vfTupleValue_smul, ← hε]
    ac_rfl
  exact (lt_irrefl _) (heq ▸ hs)

/-- An affine map has its linear part as its valued-field derivative. -/
theorem hasVFDerivativeAt_affine
    (L : (Fin n → VF) →ₗ[VF] (Fin m → VF)) (d : Fin m → VF) (a : Fin n → VF) :
    HasVFDerivativeAt (fun x => L x + d) a L := by
  intro ε
  refine ⟨1, fun b hb _ => ?_⟩
  have hzero : L (a + b) + d - (L a + d) - L b = 0 := by rw [map_add]; abel
  rw [hzero, vfTupleValue_zero]
  exact value_lt_infinity (mul_ne_zero (finiteValue_ne_zero ε) (vfTupleValue_ne_zero hb))

end SpecialTransformations.Section9
