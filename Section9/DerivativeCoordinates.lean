import Section9.Differentiation

/-! Locality and componentwise assembly for the VF derivative. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section8

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n m : ℕ}

local notation "VF" => VFType (M := M)
local notation "Γ" => Values.Gamma (M := M)
local notation "v" => Values.vfValueHom (M := M)

theorem HasVFDerivativeAt.congr_on_vfBall
    {f g : (Fin n → VF) → Fin m → VF} {a : Fin n → VF}
    {L : (Fin n → VF) →ₗ[VF] (Fin m → VF)} {ρ : Γ}
    (hf : HasVFDerivativeAt f a L) (he : Set.EqOn f g (vfBall a ρ)) :
    HasVFDerivativeAt g a L := by
  intro ε
  obtain ⟨δ, hδ⟩ := hf ε
  refine ⟨max ρ δ, fun h hn hh => ?_⟩
  have hball : a + h ∈ vfBall a ρ := by
    intro i
    change ρ.val < v ((a i + h i) - a i)
    rw [add_sub_cancel_left]
    exact ((show ρ.val ≤ (max ρ δ).val from le_max_left _ _).trans_lt hh).trans_le
      (vfTupleValue_le_component h i)
  rw [← he hball, ← he (mem_vfBall_self a ρ)]
  exact hδ h hn ((show δ.val ≤ (max ρ δ).val from le_max_right _ _).trans_lt hh)

theorem HasVFDerivativeAt.component
    {f : (Fin n → VF) → Fin m → VF} {a : Fin n → VF}
    {L : (Fin n → VF) →ₗ[VF] (Fin m → VF)} (hL : HasVFDerivativeAt f a L) (i : Fin m) :
    ∀ ε : Γ, ∃ δ : Γ, ∀ h, h ≠ 0 → δ.val < vfTupleValue h →
      ε.val * vfTupleValue h < v (f (a + h) i - f a i - L h i) := by
  intro ε
  obtain ⟨δ, hδ⟩ := hL ε
  exact ⟨δ, fun h hn hh => (hδ h hn hh).trans_le (vfTupleValue_le_component _ i)⟩

theorem hasVFDerivativeAt_of_components
    {f : (Fin n → VF) → Fin m → VF} {a : Fin n → VF}
    (L : (Fin n → VF) →ₗ[VF] (Fin m → VF))
    (hL : ∀ i : Fin m, ∀ ε : Γ, ∃ δ : Γ, ∀ h, h ≠ 0 → δ.val < vfTupleValue h →
      ε.val * vfTupleValue h < v (f (a + h) i - f a i - L h i)) :
    HasVFDerivativeAt f a L := by
  classical
  intro ε
  choose δ hδ using fun i => hL i ε
  let D : Finset Γ := insert 1 (Finset.univ.image δ)
  have hD : D.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  refine ⟨D.max' hD, fun h hn hh => ?_⟩
  by_cases hm : 0 < m
  · obtain ⟨j, hj⟩ := vfTupleValue_eq_component (f (a + h) - f a - L h) hm
    have hmem : δ j ∈ D := Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
    have hle : (δ j).val ≤ (D.max' hD).val := Finset.le_max' D _ hmem
    rw [hj]
    exact hδ j h hn (hle.trans_lt hh)
  · have he : (f (a + h) - f a - L h) = 0 :=
      funext fun j => (hm (Nat.zero_lt_of_lt j.isLt)).elim
    rw [he, vfTupleValue_zero]
    exact value_lt_infinity (mul_ne_zero (finiteValue_ne_zero ε) (vfTupleValue_ne_zero hn))

end SpecialTransformations.Section9
