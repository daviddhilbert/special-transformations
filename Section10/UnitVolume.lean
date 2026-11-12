module

public import Section10.MeasuredPositiveLift

@[expose] public section

/-! The constant-volume subcategories. The neutral Gamma value is the
paper's additive zero. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section9

noncomputable section

namespace SpecialTransformations.Section10

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {k : ℕ}
local notation "Γ" => Values.Gamma (M := M)

def VolumeScale.unit {G : Type} [CommMonoidWithZero G] (d : VolumeScale M G) : VolumeScale M G :=
  { d with allowed := fun x => d.allowed x ∧ d.value x = 1 }

variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hB : VFGammaGeneratedBase ⟨(C.base : Set M), Ξ⟩)
local notation "RUnit" => VolumeScale.unit (rvVolumeScale (M := M))
local notation "GUnit" => VolumeScale.unit (gammaVolumeScale hc)

def MeasuredRV.forgetUnit {G : Type} [CommMonoidWithZero G] {d : VolumeScale M G}
    (U : MeasuredRV C d.unit k) : MeasuredRV C d k :=
  ⟨U.underlying, U.form, fun a => (U.allowed a).1⟩

def rvUnitIso (U V : MeasuredRV C RUnit k) : Prop :=
  rvMeasuredIso C (U.forgetUnit C) (V.forgetUnit C)

def gammaUnitIso (U V : MeasuredRV C GUnit k) : Prop :=
  gammaMeasuredIso hc C (U.forgetUnit C) (V.forgetUnit C)

variable [CharZero (VFType (M := M))]

private theorem unit_representation {G : Type} [CommMonoidWithZero G] {d : VolumeScale M G}
    (hinj : Function.Injective d.value) (A : MeasuredVF C hc d.unit k) :
    ∃ U : MeasuredRV C d.unit k, Nonempty (A ≅ U.lift hc) := by
  let ν := Map.toSubsingleton A.domain (rawRVSpace (M := M) 0)
  have hconst (a b : A.domain) : A.form a = A.form b :=
    Subtype.ext (hinj ((A.allowed a).2.trans (A.allowed b).2.symm))
  obtain ⟨U, η, g, hrange, hg⟩ :=
    exists_lift_preserving_rv_determined_map hc C A.domain A.finite A.form ν (fun a b _ => hconst a b)
  let V : MeasuredRV C d.unit k := ⟨U, η, by
    intro u
    obtain ⟨a, ha⟩ := hrange u
    rw [ha]
    exact A.allowed a⟩
  refine ⟨V, ⟨MeasuredVF.isoOfRepresentative ⟨g, fun a => ⟨1, (hg a).1, ?_⟩⟩⟩⟩
  rw [map_one, mul_one]
  exact (congrArg (fun x : DefSet.univ d.space (C.base : Set M) => d.value x.val) (hg a).2).symm

include Ξ hB in
private theorem rv_unit_lift_iso (hfinite : FiniteHenselianExtensionReference)
    {U V : MeasuredRV C RUnit k} (h : rvUnitIso C U V) :
    Nonempty (U.lift hc ≅ V.lift hc) := by
  obtain ⟨e⟩ := h
  obtain ⟨g, hg, _⟩ := theorem_10_5_rv_volume hc C Ξ hB hfinite e
  exact ⟨MeasuredVF.isoOfRepresentative ⟨g, hg⟩⟩

include Ξ hB in
private theorem gamma_unit_lift_iso {U V : MeasuredRV C GUnit k} (h : gammaUnitIso hc C U V) :
    Nonempty (U.lift hc ≅ V.lift hc) := by
  obtain ⟨e⟩ := h
  obtain ⟨g, hg, _⟩ := theorem_10_5_gamma_volume hc C Ξ hB e
  exact ⟨MeasuredVF.isoOfRepresentative ⟨g, hg⟩⟩

theorem theorem_10_4_rv_unit (A : MeasuredVF C hc RUnit k) :
    ∃ U : MeasuredRV C RUnit k, Nonempty (A ≅ U.lift hc) := by
  apply unit_representation hc C _ A
  intro x y h
  change x 0 = y 0 at h
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  simpa only [hi] using h

theorem theorem_10_4_gamma_unit (A : MeasuredVF C hc GUnit k) :
    ∃ U : MeasuredRV C GUnit k, Nonempty (A ≅ U.lift hc) := by
  apply unit_representation hc C _ A
  intro x y h
  have transport {s t : LRV.Structure M} (he : s = t) (D : @Space LRV M s) :
      (@Space.Carrier LRV M t (he ▸ D)) = (@Space.Carrier LRV M s D) := by
    cases he
    rfl
  have he : (volumeGammaSpace hc).Carrier = Γ :=
    transport (Section8.normalize_eq_of_isCanonical hc) (@gammaSpace M sM hM)
  change (cast he x).val = (cast he y).val at h
  exact (Equiv.cast he).injective (Subtype.ext h)

theorem corollary_10_6_rv_unit (hfinite : FiniteHenselianExtensionReference) :
    Function.Surjective
      (MeasuredRV.liftHom (k := k) hc (rvUnitIso C) (rv_unit_lift_iso hc C Ξ hB hfinite)) :=
  MeasuredRV.liftHom_surjective _ _ _ (theorem_10_4_rv_unit hc C)

theorem corollary_10_6_gamma_unit :
    Function.Surjective
      (MeasuredRV.liftHom (k := k) hc (gammaUnitIso hc C) (gamma_unit_lift_iso hc C Ξ hB)) :=
  MeasuredRV.liftHom_surjective _ _ _ (theorem_10_4_gamma_unit hc C)

end SpecialTransformations.Section10
