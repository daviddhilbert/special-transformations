import Section9.VFJacobian

set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

/-! Pointwise Lemma 9.12 for maps between mixed VF/RV sets. A chart is
an ordinary open ball on a fixed input RV fibre with constant output
RV label. Its VF function is used only on that ball. -/

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r s t : ℕ}

local notation "VF" => VFType (M := M)
local notation "RV" => CanonicalRV.RVSort M
local notation "V" => Fin n → VF
local notation "Γ" => Values.Gamma (M := M)

variable {A : Set ((Fin n → VFType (M := M)) × (Fin r → CanonicalRV.RVSort M))}
variable {B : Set ((Fin n → VFType (M := M)) × (Fin s → CanonicalRV.RVSort M))}
variable {C : Set ((Fin n → VFType (M := M)) × (Fin t → CanonicalRV.RVSort M))}

def IsVFChartAt (f : A → B) (p : A) (F : V → V) : Prop :=
  ∃ ρ : Γ, ∀ x : V, x ∈ vfBall p.val.1 ρ → ∃ hx : (x, p.val.2) ∈ A,
    (f ⟨(x, p.val.2), hx⟩).val = (F x, (f p).val.2)

theorem IsVFChartAt.center {f : A → B} {p : A} {F : V → V}
    (hF : IsVFChartAt f p F) : F p.val.1 = (f p).val.1 := by
  obtain ⟨ρ, hρ⟩ := hF
  obtain ⟨hp, he⟩ := hρ _ (mem_vfBall_self p.val.1 ρ)
  have hp' : (⟨(p.val.1, p.val.2), hp⟩ : A) = p := Subtype.ext rfl
  rw [hp'] at he
  exact (congrArg (fun q : V × (Fin s → RV) => q.1) he).symm

theorem IsVFChartAt.comp {f : A → B} {g : B → C} {p : A} {F G : V → V}
    (hF : IsVFChartAt f p F) (hG : IsVFChartAt g (f p) G)
    {L : V →ₗ[VF] V} (hf : HasVFDerivativeAt F p.val.1 L) :
    IsVFChartAt (g ∘ f) p (G ∘ F) := by
  have he := hF.center
  obtain ⟨ρF, hρF⟩ := hF
  obtain ⟨ρG, hρG⟩ := hG
  obtain ⟨δ, hδ⟩ := hf.maps_vfBall ρG
  refine ⟨max ρF δ, fun x hx => ?_⟩
  obtain ⟨hxA, hxF⟩ := hρF x (vfBall_anti (le_max_left _ _) hx)
  have hy := hδ (vfBall_anti (le_max_right _ _) hx)
  rw [he] at hy
  obtain ⟨hyB, hyG⟩ := hρG (F x) hy
  refine ⟨hxA, ?_⟩
  have hfy : f ⟨(x, p.val.2), hxA⟩ = ⟨(F x, (f p).val.2), hyB⟩ := Subtype.ext hxF
  simpa only [Function.comp_apply, hfy] using hyG

def HasMixedVFDerivativeAt (f : A → B) (p : A) (L : V →ₗ[VF] V) : Prop :=
  ∃ F, IsVFChartAt f p F ∧ HasVFDerivativeAt F p.val.1 L

def HasMixedVFJacobianAt (f : A → B) (p : A) (J : VF) : Prop :=
  ∃ F, IsVFChartAt f p F ∧ HasVFJacobianAt F p.val.1 J

theorem hasMixedVFJacobianAt_zero_arity
    {A₀ : Set ((Fin 0 → VF) × (Fin r → RV))} {B₀ : Set ((Fin 0 → VF) × (Fin s → RV))}
    (f : A₀ → B₀) (p : A₀) : HasMixedVFJacobianAt f p 1 := by
  let F : (Fin 0 → VF) → Fin 0 → VF := fun _ => (f p).val.1
  refine ⟨F, ⟨1, fun x _ => ?_⟩, hasVFJacobianAt_zero_arity F p.val.1⟩
  have hx : x = p.val.1 := funext (fun i => Fin.elim0 i)
  subst x
  exact ⟨p.property, rfl⟩

/-- The mixed Jacobian depends only on the local VF map, independently
of how its fixed-label chart is extended to a total VF function. -/
theorem HasMixedVFJacobianAt.unique {f : A → B} {p : A} {J K : VF}
    (hJ : HasMixedVFJacobianAt f p J) (hK : HasMixedVFJacobianAt f p K) : J = K := by
  obtain ⟨F, ⟨ρF, hF⟩, hJ⟩ := hJ
  obtain ⟨G, ⟨ρG, hG⟩, hK⟩ := hK
  have he : Set.EqOn F G (vfBall p.val.1 (max ρF ρG)) := by
    intro x hx
    obtain ⟨_, hfx⟩ := hF x (vfBall_anti (le_max_left _ _) hx)
    obtain ⟨_, hgx⟩ := hG x (vfBall_anti (le_max_right _ _) hx)
    exact congrArg (fun q : V × (Fin s → RV) => q.1) (hfx.symm.trans hgx)
  exact (hJ.congr_on_vfBall he).unique hK

/-- Full differentiability in fixed-label charts gives all three
partial Jacobians, including the determinant product for the composition. -/
theorem mixedVFJacobian_comp_of_full_derivative
    {f : A → B} {g : B → C} {p : A} {L D : V →ₗ[VF] V}
    (hf : HasMixedVFDerivativeAt f p L) (hg : HasMixedVFDerivativeAt g (f p) D) :
    HasMixedVFJacobianAt f p (LinearMap.toMatrix' L).det ∧
    HasMixedVFJacobianAt g (f p) (LinearMap.toMatrix' D).det ∧
    HasMixedVFJacobianAt (g ∘ f) p ((LinearMap.toMatrix' D).det * (LinearMap.toMatrix' L).det) := by
  obtain ⟨F, hF, hf⟩ := hf
  obtain ⟨G, hG, hg⟩ := hg
  have hg' : HasVFDerivativeAt G (F p.val.1) D := hF.center.symm ▸ hg
  exact ⟨⟨F, hF, hf.hasJacobianAt⟩, ⟨G, hG, hg.hasJacobianAt⟩,
    ⟨G ∘ F, hF.comp hG hf, vfJacobian_comp_of_full_derivative hf hg'⟩⟩

end SpecialTransformations.Section9
