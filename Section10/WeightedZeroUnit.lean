import Section10.WeightedZero
import Section10.UnitVolume
import Section4.GammaMultiplicationSyntax
import Section4.RVTagging

/-! Neutral forms at degree zero recover the ordinary isomorphisms.
The ordinary categories themselves retain all their original morphisms. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4

noncomputable section

namespace SpecialTransformations.Section10

variable {M G : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable [CommMonoidWithZero G] {P : Space LRV M} {S : Set M}

private def constantMap {Q : Space LRV M} (A : DefSet P S) (c : Q.Carrier)
    (hc : Q.Definable S {c}) : Map A (DefSet.univ Q S) where
  toFun _ := ⟨c, Set.mem_univ _⟩
  graph_definable := ((A.definable.left_relation P Q).inter P Q
    (hc.right_relation P Q)).congr P Q (by
      intro x y
      constructor
      · rintro ⟨hx, hy⟩
        exact ⟨⟨x, hx⟩, rfl, hy.symm⟩
      · rintro ⟨a, rfl, rfl⟩
        exact ⟨a.property, rfl⟩)

def rvZeroNeutralForm (A : DefSet P S) : ZeroForm (rvVolumeScale (M := M)) A := by
  let F (_ : P.Index → M) (_ : Fin 1) : M := iRVOne
  let f : Map A (DefSet.univ (rawRVSpace (M := M) 1) S) := Map.ofCodes A (fun _ _ => 1) F
    (fun _ => by simpa [F] using rvConstantCode_definable (M := M) S (ι := P.Index) true)
    (fun _ => ⟨fun _ => 1, by funext i; exact RVOperations.one_val⟩)
    (fun z => by
      apply rvValues_injective
      exact (rvValues_decode _).trans (by funext i; exact RVOperations.one_val.symm))
  exact ⟨f, fun _ => one_ne_zero⟩

@[simp] theorem rvZeroNeutralForm_weight (A : DefSet P S) (a : A) :
    (rvZeroNeutralForm A).weight a = 1 := rfl

private theorem normalizedGamma_definable (V : Set (Values.Gamma (M := M)))
    (hV : Values.GammaDefinable S V) :
    @Space.Definable LRV M (CanonicalStructure.normalize (M := M))
      (@gammaSpace M sM hM) S V := by
  have h := (definableAt_iff_normalized_raw S .rv (Values.gammaPullback V)).mp hV |>.1
  change @Set.Definable M S LRV (@CanonicalStructure.normalize M sM) (Fin 1) _
  have he : @Space.preimage LRV M (@CanonicalStructure.normalize M sM) (@gammaSpace M sM hM) V =
      {z : Fin 1 → M | z 0 ∈ Values.gammaPullback V} := by
    change {z : Fin 1 → M | ∃ hz : iRV (z 0) ∧ z 0 ≠ iRVZero,
      Values.gammaOf ⟨z 0, hz.1⟩ hz.2 ∈ V} = _
    ext z
    change (∃ hz : iRV (z 0) ∧ z 0 ≠ iRVZero,
      Values.gammaOf ⟨z 0, hz.1⟩ hz.2 ∈ V) ↔
        ∃ hr : iRV (z 0), ∃ h0 : z 0 ≠ iRVZero, Values.gammaOf ⟨z 0, hr⟩ h0 ∈ V
    exact ⟨fun ⟨h, hV⟩ => ⟨h.1, h.2, hV⟩, fun ⟨hr, h0, hV⟩ => ⟨⟨hr, h0⟩, hV⟩⟩
  rw [he]
  exact h

theorem volumeGammaSpace_definable (hc : CanonicalStructure.IsCanonical (M := M))
    (V : Set (Values.Gamma (M := M))) (hV : Values.GammaDefinable S V) :
    (volumeGammaSpace hc).Definable S {x | cast (gammaCarrier hc) x ∈ V} := by
  have transport {T U : LRV.Structure M} (e : T = U) (Q : @Space LRV M T)
      (V : Set (@Space.Carrier LRV M T Q)) :
      @Space.Definable LRV M T Q S V →
        @Space.Definable LRV M U (e ▸ Q) S
          {x | cast (by cases e; rfl :
            @Space.Carrier LRV M U (e ▸ Q) = @Space.Carrier LRV M T Q) x ∈ V} := by
    cases e
    exact id
  exact transport (Section8.normalize_eq_of_isCanonical hc) (@gammaSpace M sM hM) V
    (normalizedGamma_definable V hV)

def gammaZeroNeutralForm (hc : CanonicalStructure.IsCanonical (M := M))
    (A : DefSet P S) : ZeroForm (gammaVolumeScale hc) A := by
  let c := cast (gammaCarrier hc).symm (1 : Values.Gamma (M := M))
  have hcdef : (volumeGammaSpace hc).Definable S {c} := by
    convert volumeGammaSpace_definable hc {1} (GammaSyntax.one_definable S) using 1
    ext x
    change x = c ↔ cast (gammaCarrier hc) x = 1
    constructor
    · intro h
      rw [h]
      simp only [c, cast_cast, cast_eq]
    · intro h
      apply (Equiv.cast (gammaCarrier hc)).injective
      simpa only [Equiv.cast_apply, c, cast_cast, cast_eq] using h
  exact ⟨constantMap A c hcdef, fun _ => trivial⟩

@[simp] theorem gammaZeroNeutralForm_weight (hc : CanonicalStructure.IsCanonical (M := M))
    (A : DefSet P S) (a : A) : (gammaZeroNeutralForm hc A).weight a = 1 := by
  change (cast (gammaCarrier hc) (cast (gammaCarrier hc).symm (1 : Values.Gamma (M := M)))).val = 1
  rw [cast_cast]
  rfl

namespace WeightedZero

variable {d : VolumeScale M G} {Obj : Type} {Q : Obj → Space LRV M}
variable {D : ∀ X, DefSet (Q X) S}

/-- Every definable bijection between neutral-form objects is measured. -/
def neutralMap {A B : WeightedZero d Q D}
    (hA : ∀ a, A.weight a = 1) (hB : ∀ b, B.weight b = 1)
    (f : Map A.domain B.domain) (hf : Function.Bijective f) : A ⟶ B :=
  ⟨f, hf, fun a => (hA a).trans (hB (f a)).symm⟩

/-- Retain the same form when imposing the neutral-value subcategory. -/
def asUnit (A : WeightedZero d Q D) (hA : ∀ a, A.weight a = 1) :
    WeightedZero d.unit Q D :=
  ⟨A.underlying, ⟨A.form.map, fun a => ⟨A.form.allowed a, hA a⟩⟩⟩

def forgetUnit (A : WeightedZero d.unit Q D) : WeightedZero d Q D :=
  ⟨A.underlying, ⟨A.form.map, fun a => (A.form.allowed a).1⟩⟩

@[simp] theorem asUnit_forgetUnit (A : WeightedZero d Q D) (hA : ∀ a, A.weight a = 1) :
    (A.asUnit hA).forgetUnit = A := rfl

/-- Every neutral-form object is isomorphic to the neutral embedding of
its own underlying ordinary object. -/
def neutralIso (A : WeightedZero d Q D) (ω : ZeroForm d A.domain)
    (hA : ∀ a, A.weight a = 1) (hω : ∀ a, ω.weight a = 1) :
    A ≅ (⟨A.underlying, ω⟩ : WeightedZero d Q D) :=
  isoOfExactMap (neutralMap hA hω (Map.id _) Function.bijective_id)

end WeightedZero

def rvZeroNeutral (U : RVFiniteObject (M := M) S 0) : MeasuredRVZero S rvVolumeScale :=
  ⟨U, rvZeroNeutralForm U.obj.domain⟩

def gammaZeroNeutral (hc : CanonicalStructure.IsCanonical (M := M))
    (U : RVFiniteObject (M := M) S 0) : MeasuredRVZero S (gammaVolumeScale hc) :=
  ⟨U, gammaZeroNeutralForm hc U.obj.domain⟩

def vfRVZeroNeutral (hc : CanonicalStructure.IsCanonical (M := M))
    (A : VFFiniteObject (volumeGammaSpace hc) S 0) : MeasuredVFZero hc S rvVolumeScale :=
  ⟨A, rvZeroNeutralForm A.obj.obj.set⟩

def vfGammaZeroNeutral (hc : CanonicalStructure.IsCanonical (M := M))
    (A : VFFiniteObject (volumeGammaSpace hc) S 0) : MeasuredVFZero hc S (gammaVolumeScale hc) :=
  ⟨A, gammaZeroNeutralForm hc A.obj.obj.set⟩

private def ordinaryRVZeroIso {U V : RVFiniteObject (M := M) S 0}
    (f : Map U.obj.domain V.obj.domain) (hf : Function.Bijective f) : U ≅ V :=
  rvFiniteIsoOfAmbient (rvIsoOfVolumePreservingBijection f hf
    (fun _ => Subsingleton.elim _ _))

theorem rvZeroNeutral_iso_iff (U V : RVFiniteObject (M := M) S 0) :
    Nonempty (rvZeroNeutral U ≅ rvZeroNeutral V) ↔ Nonempty (U ≅ V) := by
  constructor
  · rintro ⟨e⟩
    exact ⟨ordinaryRVZeroIso e.hom.map e.hom.bijective⟩
  · rintro ⟨e⟩
    let E := (rvForget S 0).mapIso ((finiteVolumeProperty S 0).ι.mapIso e)
    exact ⟨WeightedZero.isoOfExactMap (WeightedZero.neutralMap
      (rvZeroNeutralForm_weight _) (rvZeroNeutralForm_weight _)
      E.hom (DefinableSetCat.bijective_of_iso E))⟩

theorem gammaZeroNeutral_iso_iff (hc : CanonicalStructure.IsCanonical (M := M))
    (U V : RVFiniteObject (M := M) S 0) :
    Nonempty (gammaZeroNeutral hc U ≅ gammaZeroNeutral hc V) ↔ Nonempty (U ≅ V) := by
  constructor
  · rintro ⟨e⟩
    exact ⟨ordinaryRVZeroIso e.hom.map e.hom.bijective⟩
  · rintro ⟨e⟩
    let E := (rvForget S 0).mapIso ((finiteVolumeProperty S 0).ι.mapIso e)
    exact ⟨WeightedZero.isoOfExactMap (WeightedZero.neutralMap
      (gammaZeroNeutralForm_weight hc _) (gammaZeroNeutralForm_weight hc _)
      E.hom (DefinableSetCat.bijective_of_iso E))⟩

theorem vfRVZeroNeutral_iso_iff (hc : CanonicalStructure.IsCanonical (M := M))
    (A B : VFFiniteObject (volumeGammaSpace hc) S 0) :
    Nonempty (vfRVZeroNeutral hc A ≅ vfRVZeroNeutral hc B) ↔ Nonempty (A ≅ B) := by
  constructor
  · rintro ⟨e⟩
    exact ⟨vfFiniteBoundedIsoOfAmbient _ (DefinableSetCat.isoOfBijective
      (A := A.obj.obj) (B := B.obj.obj) e.hom.map e.hom.bijective)⟩
  · rintro ⟨e⟩
    let E := (vfDimensionProperty (volumeGammaSpace hc) S 0).ι.mapIso
      ((vfBoundedFiniteProperty (volumeGammaSpace hc) S 0).ι.mapIso e)
    exact ⟨WeightedZero.isoOfExactMap (WeightedZero.neutralMap
      (rvZeroNeutralForm_weight _) (rvZeroNeutralForm_weight _)
      E.hom (DefinableSetCat.bijective_of_iso E))⟩

theorem vfGammaZeroNeutral_iso_iff (hc : CanonicalStructure.IsCanonical (M := M))
    (A B : VFFiniteObject (volumeGammaSpace hc) S 0) :
    Nonempty (vfGammaZeroNeutral hc A ≅ vfGammaZeroNeutral hc B) ↔ Nonempty (A ≅ B) := by
  constructor
  · rintro ⟨e⟩
    exact ⟨vfFiniteBoundedIsoOfAmbient _ (DefinableSetCat.isoOfBijective
      (A := A.obj.obj) (B := B.obj.obj) e.hom.map e.hom.bijective)⟩
  · rintro ⟨e⟩
    let E := (vfDimensionProperty (volumeGammaSpace hc) S 0).ι.mapIso
      ((vfBoundedFiniteProperty (volumeGammaSpace hc) S 0).ι.mapIso e)
    exact ⟨WeightedZero.isoOfExactMap (WeightedZero.neutralMap
      (gammaZeroNeutralForm_weight hc _) (gammaZeroNeutralForm_weight hc _)
      E.hom (DefinableSetCat.bijective_of_iso E))⟩

theorem rvZeroNeutral_complete (U : MeasuredRVZero S rvVolumeScale)
    (hU : ∀ u, U.weight u = 1) : Nonempty (U ≅ rvZeroNeutral U.underlying) :=
  ⟨U.neutralIso _ hU (rvZeroNeutralForm_weight _)⟩

theorem gammaZeroNeutral_complete (hc : CanonicalStructure.IsCanonical (M := M))
    (U : MeasuredRVZero S (gammaVolumeScale hc)) (hU : ∀ u, U.weight u = 1) :
    Nonempty (U ≅ gammaZeroNeutral hc U.underlying) :=
  ⟨U.neutralIso _ hU (gammaZeroNeutralForm_weight hc _)⟩

theorem vfRVZeroNeutral_complete (hc : CanonicalStructure.IsCanonical (M := M))
    (A : MeasuredVFZero hc S rvVolumeScale) (hA : ∀ a, A.weight a = 1) :
    Nonempty (A ≅ vfRVZeroNeutral hc A.underlying) :=
  ⟨A.neutralIso _ hA (rvZeroNeutralForm_weight _)⟩

theorem vfGammaZeroNeutral_complete (hc : CanonicalStructure.IsCanonical (M := M))
    (A : MeasuredVFZero hc S (gammaVolumeScale hc)) (hA : ∀ a, A.weight a = 1) :
    Nonempty (A ≅ vfGammaZeroNeutral hc A.underlying) :=
  ⟨A.neutralIso _ hA (gammaZeroNeutralForm_weight hc _)⟩

end SpecialTransformations.Section10
