import Section9.PrescribedVolumeLift
import Section9.GaussGraphConstruction
import Section9.RVFiniteEssential
import Section9.UniformRVScaling
import Section4.RVCoordinates

/-! Positive-degree RV volume forms and the forward lift of Theorem 10.5.
The essential isomorphism acts on the nondegenerate parts of finite-volume
objects. Its lift retains the labels and satisfies the measure equation
outside a definable VF-small set. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section4.ResiduePurity
open SpecialTransformations.Section9

noncomputable section

namespace SpecialTransformations.Section10

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}
local notation "VF" => VFType (M := M)
local notation "RV" => CanonicalRV.RVSort M
local notation "n" => (k + 1)

/-- A same-base RV volume form on a definable set. The form takes values
in the nonzero group of the existing RV sort. -/
structure RVVolumeForm {P : Space LRV M} (A : DefSet P S) where
  map : Map A (DefSet.univ (rawRVSpace (M := M) 1) S)
  nonzero : ∀ a, (map a).val 0 ≠ 0

namespace RVVolumeForm

def value {P : Space LRV M} {A : DefSet P S} (ω : RVVolumeForm A) (a : A) : RV :=
  (ω.map a).val 0

def pullback {P Q : Space LRV M} {A : DefSet P S} {B : DefSet Q S}
    (ω : RVVolumeForm B) (f : Map A B) : RVVolumeForm A :=
  ⟨ω.map.comp f, fun a => ω.nonzero (f a)⟩

@[simp] theorem pullback_value {P Q : Space LRV M} {A : DefSet P S} {B : DefSet Q S}
    (ω : RVVolumeForm B) (f : Map A B) (a : A) :
    (ω.pullback f).value a = ω.value (f a) := rfl

end RVVolumeForm

/-- The positive-degree objects of Definition 10.3 in the finite-volume category. -/
structure RVVolumeObject (S : Set M) (k : ℕ) where
  underlying : RVFiniteObject (M := M) S (k + 1)
  form : RVVolumeForm underlying.obj.domain

namespace RVVolumeObject

def essential (U : RVVolumeObject (M := M) S k) : RVVolumeObject (M := M) S k where
  underlying := rvFiniteEssential U.underlying
  form := U.form.pullback (Map.inclusion (rvEssentialLabels_subset U.underlying.obj))

def liftForm (U : RVVolumeObject (M := M) S k) : RVVolumeForm (rvLift U.underlying.obj) :=
  U.form.pullback (liftLabelMap U.underlying.obj)

end RVVolumeObject

/-- Definition 10.3 on the essential parts. The two equations are imposed
on the very same label isomorphism and use the Section 9 Jacobians. -/
structure RVVolumeIso (U V : RVVolumeObject (M := M) S k) where
  labels : RVFiniteEssentialIso U.underlying V.underlying
  gamma_rule : let E := (finiteVolumeProperty S n).ι.mapIso labels
    ∀ u : U.essential.underlying.obj.domain,
      Values.vrv (U.essential.form.value u) =
        Values.vrv (V.essential.form.value (E.hom.map u)) *
          (rvGammaJacobian (U.essential.underlying.obj.value u)
            (V.essential.underlying.obj.value (E.hom.map u))
            (rvEssential_value_nonzero U.underlying.obj u)
            (rvEssential_value_nonzero V.underlying.obj (E.hom.map u))).val
  rv_rule : let E := (finiteVolumeProperty S n).ι.mapIso labels
    ∃ X : DefSet (rawRVSpace (M := M) U.underlying.obj.arity) S, rvDim X < n ∧
      ∀ u : U.essential.underlying.obj.domain, u.val ∉ X.carrier →
        ∃ j : RV, IsRVJacobianAt (volumeCorrespondence E.hom.map).carrier
          (U.essential.underlying.obj.value u) (V.essential.underlying.obj.value (E.hom.map u)) j ∧
          U.essential.form.value u = V.essential.form.value (E.hom.map u) * j

private def rvCoordinateInverseMap (S : Set M) :
    Map (DefSet.univ (rawRVSpace (M := M) 1) S) (DefSet.univ (rawRVSpace (M := M) 1) S) := by
  let Q := rawRVSpace (M := M) 1
  let f (x : Q.Carrier) : Q.Carrier := fun i => (x i)⁻¹
  let F (z : Q.Index → M) : Q.Index → M := fun i => iRVInvFn (z i)
  have hF : S.DefinableMap LRV F := by
    intro i
    exact (Set.DefinableFun.of_empty
      (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.rvInv)).comp
        (show S.DefinableMap LRV (fun z : Q.Index → M => ![z i]) from
          fun j => by fin_cases j; exact Set.DefinableFun.proj LRV)
  have hcode (z : Q.domain) : rvValues (f (Q.decode z)) = F z.val := by
    funext i
    change ((Q.decode z i)⁻¹).val = iRVInvFn (z.val i)
    rw [RVOperations.inv_val]
    exact congrArg iRVInvFn (congrFun (rvValues_decode z) i)
  exact Map.ofCodes _ f F hF (fun z => ⟨f (Q.decode z), hcode z⟩)
    (fun z => rvValues_injective ((rvValues_decode _).trans (hcode z).symm))

private def rvVolumeRatio {P : Space LRV M} {A : DefSet P S}
    (ω η : RVVolumeForm A) : Map A (DefSet.univ (rawRVSpace (M := M) 1) S) :=
  (rvCoordinateProductMap S).comp
    ((ω.map.pair ((rvCoordinateInverseMap S).comp η.map)).toUniv)

private theorem rvVolumeRatio_apply {P : Space LRV M} {A : DefSet P S}
    (ω η : RVVolumeForm A) (a : A) :
    (rvVolumeRatio ω η a).val 0 = ω.value a / η.value a :=
  (div_eq_mul_inv _ _).symm

/-- Theorem 10.5 in positive degree. The underlying map is a definable
bijection on the essential lifts, with the prescribed label map.
Its measure equation holds away from a definable VF-small source cut,
whose image is a VF-small target cut. -/
theorem theorem_10_5_rv_volume_ae [CharZero VF]
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hB : VFGammaGeneratedBase ⟨(C.base : Set M), Ξ⟩)
    (hfinite : FiniteHenselianExtensionReference)
    {U V : RVVolumeObject (M := M) (C.base : Set M) k} (e : RVVolumeIso U V) :
    let A := rvLift U.essential.underlying.obj
    let B := rvLift V.essential.underlying.obj
    let E := (finiteVolumeProperty (C.base : Set M) n).ι.mapIso e.labels
    ∃ G : Map A B, Function.Bijective G ∧
      (∀ p : A, E.hom.map.graph p.val.2 (G p).val.2) ∧
      ∃ Z : DefSet (rawMixedSpace (M := M) n U.underlying.obj.arity) (C.base : Set M),
        ∃ hZ : Z.carrier ⊆ A.carrier,
        vfDim (rawRVSpace (M := M) 1) Z < n ∧
        vfDim (rawRVSpace (M := M) 1) (G.restrict hZ).image < n ∧
        ∀ p : A, p.val ∉ Z.carrier → ∃ J : VF, HasMixedVFJacobianAt G p J ∧
          U.essential.liftForm.value p =
            V.essential.liftForm.value (G p) * CanonicalRV.encodedRv J := by
  let S := (C.base : Set M)
  let E := (finiteVolumeProperty S n).ι.mapIso e.labels
  let ω := U.essential.form
  let η := V.essential.form.pullback E.hom.map
  let d := rvVolumeRatio ω η
  have hU := rvEssential_value_nonzero U.underlying.obj
  have hV := rvEssential_value_nonzero V.underlying.obj
  have hΓ (u : U.essential.underlying.obj.domain) :
      Values.vrv ((d u).val 0) =
        (rvGammaJacobian (U.essential.underlying.obj.value u)
          (V.essential.underlying.obj.value (E.hom.map u)) (hU u) (hV (E.hom.map u))).val := by
    rw [show (d u).val 0 = ω.value u / η.value u from rvVolumeRatio_apply ω η u]
    change RVOperations.vrvHom _ = _
    rw [map_div₀]
    have hne : RVOperations.vrvHom (η.value u) ≠ 0 :=
      (map_ne_zero RVOperations.vrvHom).mpr (η.nonzero u)
    apply (div_eq_iff hne).mpr
    exact (e.gamma_rule u).trans (mul_comm _ _)
  obtain ⟨X, hX, hRV⟩ := e.rv_rule
  have hRV' (u : U.essential.underlying.obj.domain) (hu : u.val ∉ X.carrier) :
      IsRVJacobianAt (volumeCorrespondence E.hom.map).carrier
        (U.essential.underlying.obj.value u) (V.essential.underlying.obj.value (E.hom.map u))
        ((d u).val 0) := by
    obtain ⟨j, hj, he⟩ := hRV u hu
    have hne : η.value u ≠ 0 := η.nonzero u
    have hdiv : ω.value u / η.value u = j :=
      (div_eq_iff hne).mpr (he.trans (mul_comm _ _))
    exact ((rvVolumeRatio_apply ω η u).trans hdiv).symm ▸ hj
  obtain ⟨G, hG, hlabel, Z, hZ, hdim, hJ⟩ :=
    theorem_9_16_finite_volume_of_reference_input hc C Ξ hB e.labels hU hV d hΓ
      ⟨X, hX, hRV'⟩ (acvf_henselizedGaussGraphInput_of_finite_extension_reference hfinite)
  refine ⟨G, hG, hlabel, Z, hZ, hdim, ?_, ?_⟩
  · let f := G.restrict hZ
    have hf : Function.Bijective f.toImage := by
      constructor
      · intro a b hab
        have he : f a = f b := Subtype.ext (congrArg (fun y => y.val) hab)
        exact Subtype.ext (congrArg (fun x => x.val) (hG.injective he))
      · rintro ⟨_, a, rfl⟩
        exact ⟨a, rfl⟩
    exact (vfDim_eq_of_bijective _ f.toImage hf) ▸ hdim
  · intro p hp
    obtain ⟨J, hder, hdet⟩ := hJ p hp
    let u := liftLabelMap U.essential.underlying.obj p
    have htag : E.hom.map u = liftLabelMap V.essential.underlying.obj (G p) :=
      Subtype.ext ((E.hom.map.graph_apply u _).mp (hlabel p))
    refine ⟨J, hder, ?_⟩
    have hd : CanonicalRV.encodedRv J = ω.value u / η.value u :=
      hdet.trans (rvVolumeRatio_apply ω η u)
    change ω.value u = V.essential.form.value (liftLabelMap _ (G p)) * CanonicalRV.encodedRv J
    rw [← htag, hd]
    have hne : η.value u ≠ 0 := η.nonzero u
    exact (mul_div_cancel₀ _ hne).symm

end SpecialTransformations.Section10

end
