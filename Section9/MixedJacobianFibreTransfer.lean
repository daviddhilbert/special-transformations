import Section9.MixedJacobianValue

/-! Mixed derivatives depend only on the fixed-label fibre.

Two mixed maps whose input fibres over given labels coincide, whose VF
outputs agree on those fibres, and whose output labels are constant on the
same points, have the same charts, hence the same mixed derivatives, at
points with equal VF coordinates. Used to transfer Jacobians along a change
of Gamma codes carried as extra labels. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r s r' s' : ℕ}

local notation "VF" => VFType (M := M)
local notation "RV" => CanonicalRV.RVSort M
local notation "V" => Fin n → VF

variable {A : Set ((Fin n → VFType (M := M)) × (Fin r → CanonicalRV.RVSort M))}
variable {B : Set ((Fin n → VFType (M := M)) × (Fin s → CanonicalRV.RVSort M))}
variable {A' : Set ((Fin n → VFType (M := M)) × (Fin r' → CanonicalRV.RVSort M))}
variable {B' : Set ((Fin n → VFType (M := M)) × (Fin s' → CanonicalRV.RVSort M))}

/-- Hypotheses identifying the fixed-label fibres of `f` at `p` and of `f'` at `p'`. -/
structure FibreMatch (f : A → B) (f' : A' → B') (p : A) (p' : A') : Prop where
  vf : p.val.1 = p'.val.1
  dom : ∀ x : V, (x, p.val.2) ∈ A ↔ (x, p'.val.2) ∈ A'
  value : ∀ (x : V) (h : (x, p.val.2) ∈ A) (h' : (x, p'.val.2) ∈ A'),
    (f ⟨(x, p.val.2), h⟩).val.1 = (f' ⟨(x, p'.val.2), h'⟩).val.1
  label : ∀ (x : V) (h : (x, p.val.2) ∈ A) (h' : (x, p'.val.2) ∈ A'),
    (f ⟨(x, p.val.2), h⟩).val.2 = (f p).val.2 ↔ (f' ⟨(x, p'.val.2), h'⟩).val.2 = (f' p').val.2

theorem FibreMatch.chart {f : A → B} {f' : A' → B'} {p : A} {p' : A'}
    (h : FibreMatch f f' p p') {F : V → V} (hF : IsVFChartAt f p F) : IsVFChartAt f' p' F := by
  obtain ⟨ρ, hρ⟩ := hF
  refine ⟨ρ, fun x hx => ?_⟩
  rw [← h.vf] at hx
  obtain ⟨hxA, he⟩ := hρ x hx
  have hxA' := (h.dom x).mp hxA
  refine ⟨hxA', ?_⟩
  have hv := h.value x hxA hxA'
  have hl2 := congrArg Prod.snd he
  have hl := (h.label x hxA hxA').mp hl2
  rw [he] at hv
  exact Prod.ext hv.symm hl

theorem FibreMatch.symm {f : A → B} {f' : A' → B'} {p : A} {p' : A'}
    (h : FibreMatch f f' p p') : FibreMatch f' f p' p :=
  ⟨h.vf.symm, fun x => (h.dom x).symm, fun x h₁ h₂ => (h.value x h₂ h₁).symm,
    fun x h₁ h₂ => (h.label x h₂ h₁).symm⟩

theorem FibreMatch.derivative_iff {f : A → B} {f' : A' → B'} {p : A} {p' : A'}
    (h : FibreMatch f f' p p') (L : V →ₗ[VF] V) :
    HasMixedVFDerivativeAt f p L ↔ HasMixedVFDerivativeAt f' p' L := by
  constructor
  · rintro ⟨F, hF, hD⟩
    exact ⟨F, h.chart hF, h.vf ▸ hD⟩
  · rintro ⟨F, hF, hD⟩
    exact ⟨F, h.symm.chart hF, h.vf.symm ▸ hD⟩

end SpecialTransformations.Section9
