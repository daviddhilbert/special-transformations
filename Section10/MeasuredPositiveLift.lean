import Section10.MeasuredScissors
import Section10.RVVolumeSurjectivity
import Section10.GammaVolumeSurjectivity

/-! Corollary 10.6. Theorems 10.4 and 10.5 give surjectivity on the
generators and invariance under measured isomorphism, respectively. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section9

noncomputable section

namespace SpecialTransformations.Section10

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hB : VFGammaGeneratedBase ⟨(C.base : Set M), Ξ⟩)
variable {k : ℕ}
local notation "S" => (C.base : Set M)
local notation "RScale" => rvVolumeScale (M := M)
local notation "GScale" => gammaVolumeScale hc

def MeasuredRV.toRVVolume (U : MeasuredRV C RScale k) : RVVolumeObject S k :=
  ⟨U.underlying, U.form, U.allowed⟩

def MeasuredRV.ofRVVolume (U : RVVolumeObject (M := M) S k) : MeasuredRV C RScale k :=
  ⟨U.underlying, U.form.map, U.form.nonzero⟩

def MeasuredRV.toGammaVolume (U : MeasuredRV C GScale k) : GammaVolumeObject hc S k :=
  ⟨U.underlying, U.form⟩

def MeasuredRV.ofGammaVolume (U : GammaVolumeObject hc S k) : MeasuredRV C GScale k :=
  ⟨U.underlying, U.form, fun _ => trivial⟩

def rvMeasuredIso (U V : MeasuredRV C RScale k) : Prop :=
  Nonempty (RVVolumeIso (U.toRVVolume C) (V.toRVVolume C))

def gammaMeasuredIso (U V : MeasuredRV C GScale k) : Prop :=
  Nonempty (GammaVolumeIso (U.toGammaVolume hc C) (V.toGammaVolume hc C))

variable [CharZero (VFType (M := M))]

include Ξ hB in
private theorem rv_lift_iso (hfinite : FiniteHenselianExtensionReference)
    {U V : MeasuredRV C RScale k} (h : rvMeasuredIso C U V) :
    Nonempty (U.lift hc ≅ V.lift hc) := by
  obtain ⟨e⟩ := h
  obtain ⟨g, hg, _⟩ := theorem_10_5_rv_volume hc C Ξ hB hfinite e
  exact ⟨MeasuredVF.isoOfRepresentative ⟨g, hg⟩⟩

include Ξ hB in
private theorem gamma_lift_iso {U V : MeasuredRV C GScale k} (h : gammaMeasuredIso hc C U V) :
    Nonempty (U.lift hc ≅ V.lift hc) := by
  obtain ⟨e⟩ := h
  obtain ⟨g, hg, _⟩ := theorem_10_5_gamma_volume hc C Ξ hB e
  exact ⟨MeasuredVF.isoOfRepresentative ⟨g, hg⟩⟩

/-- The additive map on the RV-valued Grothendieck semigroups. -/
def rvMeasuredPositiveLift (hfinite : FiniteHenselianExtensionReference) :
    PositiveAdditiveGrothendieck.KPlus (MeasuredRV.presentation (rvMeasuredIso (k := k) C)) →+
      PositiveAdditiveGrothendieck.KPlus
        (MeasuredVF.presentation (C := C) (hc := hc) (d := RScale) (k := k)) :=
  MeasuredRV.liftHom hc (rvMeasuredIso C) (rv_lift_iso hc C Ξ hB hfinite)

/-- The additive map on the Gamma-valued Grothendieck semigroups. -/
def gammaMeasuredPositiveLift :
    PositiveAdditiveGrothendieck.KPlus (MeasuredRV.presentation (gammaMeasuredIso (k := k) hc C)) →+
      PositiveAdditiveGrothendieck.KPlus
        (MeasuredVF.presentation (C := C) (hc := hc) (d := GScale) (k := k)) :=
  MeasuredRV.liftHom hc (gammaMeasuredIso hc C) (gamma_lift_iso hc C Ξ hB)

theorem rvMeasuredPositiveLift_generator (hfinite : FiniteHenselianExtensionReference)
    (U : MeasuredRV C RScale k) :
    rvMeasuredPositiveLift hc C Ξ hB hfinite
      (PositiveAdditiveGrothendieck.of (MeasuredRV.presentation (rvMeasuredIso C)) U) =
      PositiveAdditiveGrothendieck.of MeasuredVF.presentation (U.lift hc) :=
  MeasuredRV.liftHom_generator hc _ _ U

theorem gammaMeasuredPositiveLift_generator (U : MeasuredRV C GScale k) :
    gammaMeasuredPositiveLift hc C Ξ hB
      (PositiveAdditiveGrothendieck.of (MeasuredRV.presentation (gammaMeasuredIso hc C)) U) =
      PositiveAdditiveGrothendieck.of MeasuredVF.presentation (U.lift hc) :=
  MeasuredRV.liftHom_generator hc _ _ U

/-- Corollary 10.6 for RV-valued forms in positive degree. -/
theorem corollary_10_6_rv (hfinite : FiniteHenselianExtensionReference) :
    Function.Surjective (rvMeasuredPositiveLift (k := k) hc C Ξ hB hfinite) := by
  apply MeasuredRV.liftHom_surjective
  intro A
  obtain ⟨U, g, hg⟩ := theorem_10_4_rv_volume hc C Ξ hB A.domain A.finite ⟨A.form, A.allowed⟩
  exact ⟨MeasuredRV.ofRVVolume C U, ⟨MeasuredVF.isoOfRepresentative ⟨g, hg⟩⟩⟩

/-- Corollary 10.6 for Gamma-valued forms in positive degree. -/
theorem corollary_10_6_gamma :
    Function.Surjective (gammaMeasuredPositiveLift (k := k) hc C Ξ hB) := by
  apply MeasuredRV.liftHom_surjective
  intro A
  obtain ⟨U, g, hg⟩ := theorem_10_4_gamma_volume hc C Ξ hB A.domain A.finite A.form
  exact ⟨MeasuredRV.ofGammaVolume hc C U, ⟨MeasuredVF.isoOfRepresentative ⟨g, hg⟩⟩⟩

end SpecialTransformations.Section10
