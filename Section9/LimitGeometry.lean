module

public import Section9.Limits

@[expose] public section

/-! Neighbourhood geometry for Definition 9.1, including the auxiliary
point at infinity. All radii belong to the released value-group quotient.
The proofs are direct valuation arguments and use no new reference inputs. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem vfValue_neg (x : VFType (M := M)) :
    Values.vfValueHom (-x) = Values.vfValueHom x := by
  apply (Values.paperValueEquiv (M := M)).injective
  change Values.valueEquiv _ _ (Values.vrv (CanonicalRV.encodedRv (-x))) =
    Values.valueEquiv _ _ (Values.vrv (CanonicalRV.encodedRv x))
  rw [Values.valueEquiv_apply_vf, Values.valueEquiv_apply_vf,
    (Values.presentationValuation (M := M)).restrict.map_neg]

theorem vfValue_sub_comm (x y : VFType (M := M)) :
    Values.vfValueHom (x - y) = Values.vfValueHom (y - x) := by
  rw [← neg_sub y x, vfValue_neg]

theorem vfValue_min_le_sub (x y : VFType (M := M)) :
    min (Values.vfValueHom x) (Values.vfValueHom y) ≤ Values.vfValueHom (x - y) := by
  rcases le_total (Values.vfValueHom x) (Values.vfValueHom y) with h | h
  · rw [min_eq_left h]
    apply (Values.vf_pred_iff_gamma_le (x - y) x).mp
    apply (Values.presentation_compatible _ _).mpr
    have hxy := (Values.presentation_compatible y x).mp
      ((Values.vf_pred_iff_gamma_le y x).mpr h)
    simpa only [max_eq_left hxy] using Values.presentationValuation.map_sub x y
  · rw [min_eq_right h]
    apply (Values.vf_pred_iff_gamma_le (x - y) y).mp
    apply (Values.presentation_compatible _ _).mpr
    have hxy := (Values.presentation_compatible x y).mp
      ((Values.vf_pred_iff_gamma_le x y).mpr h)
    simpa only [max_eq_right hxy] using Values.presentationValuation.map_sub x y

theorem gamma_lt_value_zero (ε : Values.Gamma (M := M)) :
    ε.val < Values.vfValueHom (0 : VFType (M := M)) := by
  rw [map_zero, ← Values.infinity_eq_zero]
  exact lt_of_le_of_ne (Values.le_infinity _) ε.property

theorem memLimitBall_anti {ε δ : Values.Gamma (M := M)} (h : ε ≤ δ)
    {b : LimitPoint M} {y : VFType (M := M)}
    (hy : memLimitBall b δ y) : memLimitBall b ε y := by
  cases b with
  | none =>
    exact hy.trans_le (show (δ⁻¹).val ≤ (ε⁻¹).val from inv_le_inv' h)
  | some b => exact (show ε.val ≤ δ.val from h).trans_lt hy

/-- The typed VF form of the ordinary input neighbourhood. -/
def vfBall {n : ℕ} (a : Fin n → VFType (M := M)) (ε : Values.Gamma (M := M)) :
    Set (Fin n → VFType (M := M)) := {x | ∀ i, ε.val < Values.vfValueHom (x i - a i)}

theorem mem_vfBall_iff_gammaUniformBall {n : ℕ}
    (a x : Fin n → VFType (M := M)) (ε : Values.Gamma (M := M)) :
    x ∈ vfBall a ε ↔
      (fun i => (x i).val) ∈ Section8.gammaUniformBall (fun i => (a i).val) ε := by
  constructor
  · intro h i
    exact ⟨(a i).property, (x i).property, h i⟩
  · intro h i
    obtain ⟨ha, hx, hi⟩ := h i
    exact hi

theorem vfBall_anti {n : ℕ} {a : Fin n → VFType (M := M)}
    {ε δ : Values.Gamma (M := M)} (h : ε ≤ δ) : vfBall a δ ⊆ vfBall a ε :=
  fun _ hx i => (show ε.val ≤ δ.val from h).trans_lt (hx i)

theorem mem_vfBall_self {n : ℕ} (a : Fin n → VFType (M := M))
    (ε : Values.Gamma (M := M)) : a ∈ vfBall a ε := by
  intro i
  simpa only [sub_self] using gamma_lt_value_zero ε

theorem mem_vfBall_of_common {n : ℕ} {a b x : Fin n → VFType (M := M)}
    {ε : Values.Gamma (M := M)} (ha : x ∈ vfBall a ε) (hb : x ∈ vfBall b ε) :
    b ∈ vfBall a ε := by
  intro i
  have h := vfValue_min_le_sub (x i - a i) (x i - b i)
  rw [show x i - a i - (x i - b i) = b i - a i by abel] at h
  exact (lt_min (ha i) (hb i)).trans_le h

theorem vfBall_symm {n : ℕ} {a b : Fin n → VFType (M := M)}
    {ε : Values.Gamma (M := M)} (h : b ∈ vfBall a ε) : a ∈ vfBall b ε := by
  intro i
  rw [vfValue_sub_comm]
  exact h i

theorem mem_vfBall_of_common_center {n : ℕ} {a b x : Fin n → VFType (M := M)}
    {ε : Values.Gamma (M := M)} (hb : b ∈ vfBall a ε) (hx : x ∈ vfBall a ε) :
    x ∈ vfBall b ε :=
  mem_vfBall_of_common (vfBall_symm hb) (vfBall_symm hx)

/-- Finite VF points embedded in the auxiliary limit space. -/
def finiteLimitPoint {m : ℕ} (b : Fin m → VFType (M := M)) : Fin m → LimitPoint M :=
  fun i => some (b i)

omit [M ⊨ Axioms.ACVF] in
theorem finiteLimitPoint_injective {m : ℕ} :
    Function.Injective (finiteLimitPoint (M := M) (m := m)) := by
  intro a b h
  exact funext (fun i => Option.some.inj (congrFun h i))

/-- The neighbourhood of an extended tuple, containing only finite VF tuples. -/
def limitBall {m : ℕ} (b : Fin m → LimitPoint M) (ε : Values.Gamma (M := M)) :
    Set (Fin m → VFType (M := M)) := {y | ∀ i, memLimitBall (b i) ε (y i)}

theorem limitBall_finite {m : ℕ} (b : Fin m → VFType (M := M))
    (ε : Values.Gamma (M := M)) : limitBall (finiteLimitPoint b) ε = vfBall b ε := rfl

theorem limitBall_anti {m : ℕ} {b : Fin m → LimitPoint M}
    {ε δ : Values.Gamma (M := M)} (h : ε ≤ δ) : limitBall b δ ⊆ limitBall b ε :=
  fun _ hx i => memLimitBall_anti h (hx i)

theorem isLimitSet_iff {n m : ℕ} (A : Set (Fin n → VFType (M := M)))
    (a : Fin n → VFType (M := M))
    (f : (Fin n → VFType (M := M)) → Set (Fin m → VFType (M := M)))
    (L : Set (Fin m → LimitPoint M)) :
    IsLimitSet A a f L ↔ ∀ ε, ∃ δ, ∀ x ∈ A \ {a}, x ∈ vfBall a δ →
      ∀ y ∈ f x, ∃ b ∈ L, y ∈ limitBall b ε := by
  simp only [IsLimitSet, mem_vfBall_iff_gammaUniformBall, limitBall, Set.mem_ofPred_eq]

end SpecialTransformations.Section9
