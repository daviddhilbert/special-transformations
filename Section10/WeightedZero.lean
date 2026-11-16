module

public import Section10.MeasuredVFCategory
public import Section4.VFFinitePositiveFiltration

@[expose] public section

/-! The corrected measured degree-zero categories. Objects retain an actual
same-base definable form. Arrows are total definable bijections preserving
its value exactly; no locus can be removed in degree zero. The VF carrier
is the ordinary dimension-zero category, with arbitrary mixed arity. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4

noncomputable section

namespace SpecialTransformations.Section10

variable {M G : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CommMonoidWithZero G]

/-- A form on a presentation, retaining its definable map, not just its values. -/
structure ZeroForm (d : VolumeScale M G) {P : Space LRV M} {S : Set M}
    (A : DefSet P S) where
  map : Map A (DefSet.univ d.space S)
  allowed : ∀ a, d.allowed (map a).val

namespace ZeroForm

variable {d : VolumeScale M G} {P Q : Space LRV M} {S : Set M}
variable {A : DefSet P S} {B : DefSet Q S}

def weight (ω : ZeroForm d A) (a : A) : G := d.value (ω.map a).val

def pullback (ω : ZeroForm d B) (f : Map A B) : ZeroForm d A :=
  ⟨ω.map.comp f, fun a => ω.allowed (f a)⟩

@[simp] theorem pullback_weight (ω : ZeroForm d B) (f : Map A B) (a : A) :
    (ω.pullback f).weight a = ω.weight (f a) := rfl

def restrict (ω : ZeroForm d A) (E : DefSet P S) (hE : E.carrier ⊆ A.carrier) :
    ZeroForm d E := ω.pullback (Map.inclusion hE)

@[simp] theorem restrict_weight (ω : ZeroForm d A) (E : DefSet P S)
    (hE : E.carrier ⊆ A.carrier) (a : E) :
    (ω.restrict E hE).weight a = ω.weight ⟨a.val, hE a.property⟩ := rfl

end ZeroForm

/-- Enrich an existing ordinary object family without restricting its objects. -/
structure WeightedZero (d : VolumeScale M G) {Obj : Type}
    (P : Obj → Space LRV M) {S : Set M} (D : ∀ X, DefSet (P X) S) where
  underlying : Obj
  form : ZeroForm d (D underlying)

namespace WeightedZero

variable {d : VolumeScale M G} {Obj : Type} {P : Obj → Space LRV M}
variable {S : Set M} {D : ∀ X, DefSet (P X) S}

abbrev domain (A : WeightedZero d P D) := D A.underlying

def weight (A : WeightedZero d P D) (a : A.domain) : G := A.form.weight a

/-- Exact equality is in the supplied scale: RV equality for RV forms,
and Gamma equality for Gamma forms. -/
structure ExactMap (A B : WeightedZero d P D) where
  map : Map A.domain B.domain
  bijective : Function.Bijective map
  preserves : ∀ a, A.weight a = B.weight (map a)

namespace ExactMap

variable {A B E : WeightedZero d P D}

@[ext] theorem ext {f g : ExactMap A B} (h : f.map = g.map) : f = g := by
  cases f
  cases g
  cases h
  rfl

def id (A : WeightedZero d P D) : ExactMap A A :=
  ⟨Map.id A.domain, Function.bijective_id, fun _ => rfl⟩

def comp (g : ExactMap B E) (f : ExactMap A B) : ExactMap A E :=
  ⟨g.map.comp f.map, g.bijective.comp f.bijective,
    fun a => (f.preserves a).trans (g.preserves (f.map a))⟩

def inverse (f : ExactMap A B) : ExactMap B A where
  map := f.map.inverse f.bijective
  bijective := (Equiv.ofBijective f.map f.bijective).symm.bijective
  preserves b := by
    have h := f.preserves (f.map.inverse f.bijective b)
    rw [Map.apply_inverse] at h
    exact h.symm

end ExactMap

instance : Groupoid (WeightedZero d P D) where
  Hom := ExactMap
  id := ExactMap.id
  comp f g := g.comp f
  id_comp f := by apply ExactMap.ext; apply Map.ext; intro a; rfl
  comp_id f := by apply ExactMap.ext; apply Map.ext; intro a; rfl
  assoc f g h := by apply ExactMap.ext; apply Map.ext; intro a; rfl
  inv := ExactMap.inverse
  inv_comp f := by
    apply ExactMap.ext
    apply Map.ext
    intro b
    exact Map.apply_inverse f.map f.bijective b
  comp_inv f := by
    apply ExactMap.ext
    apply Map.ext
    intro a
    exact Map.inverse_apply f.map f.bijective a

def isoOfExactMap {A B : WeightedZero d P D} (f : ExactMap A B) : A ≅ B := by
  let h : A ⟶ B := f
  exact ⟨h, Groupoid.inv h, Groupoid.comp_inv h, Groupoid.inv_comp h⟩

theorem iso_iff {A B : WeightedZero d P D} :
    Nonempty (A ≅ B) ↔ ∃ f : Map A.domain B.domain,
      Function.Bijective f ∧ ∀ a, A.weight a = B.weight (f a) := by
  constructor
  · rintro ⟨e⟩
    exact ⟨e.hom.map, e.hom.bijective, e.hom.preserves⟩
  · rintro ⟨f, hf, hw⟩
    exact ⟨isoOfExactMap ⟨f, hf, hw⟩⟩

end WeightedZero

abbrev MeasuredRVZero (S : Set M) (d : VolumeScale M G) :=
  WeightedZero d (fun U : RVFiniteObject (M := M) S 0 => rawRVSpace U.obj.arity)
    (fun U => U.obj.domain)

abbrev MeasuredVFZero (hc : CanonicalStructure.IsCanonical (M := M))
    (S : Set M) (d : VolumeScale M G) :=
  WeightedZero d
    (fun A : VFFiniteObject (volumeGammaSpace hc) S 0 => mixedFamily A.obj.obj.index)
    (fun A => A.obj.obj.set)

/-- The label projection in degree zero is a definable bijection. -/
theorem liftLabelMap_zero_bijective {S : Set M} (U : RVFiniteObject (M := M) S 0) :
    Function.Bijective (Section9.liftLabelMap U.obj) := by
  constructor
  · intro p q h
    apply Subtype.ext
    exact Prod.ext (funext (fun i => i.elim0)) (congrArg Subtype.val h)
  · intro u
    exact ⟨⟨((fun i => i.elim0), u.val), u, rfl, funext (fun i => i.elim0)⟩, Subtype.ext rfl⟩

namespace MeasuredRVZero

variable {S : Set M} {d : VolumeScale M G}

def lift (hc : CanonicalStructure.IsCanonical (M := M)) (U : MeasuredRVZero S d) :
    MeasuredVFZero hc S d :=
  ⟨rvLiftFiniteObject (volumeGammaSpace hc) U.underlying,
    U.form.pullback (Section9.liftLabelMap U.underlying.obj)⟩

@[simp] theorem lift_weight (hc : CanonicalStructure.IsCanonical (M := M))
    (U : MeasuredRVZero S d) (p : rvLift U.underlying.obj) :
    (U.lift hc).weight p = U.weight (Section9.liftLabelMap U.underlying.obj p) := rfl

/-- Lift keeps the supplied label map on every point, including its weight. -/
def liftMap (hc : CanonicalStructure.IsCanonical (M := M))
    {U V : MeasuredRVZero S d} (f : U ⟶ V) : U.lift hc ⟶ V.lift hc where
  map := ((Section9.liftLabelMap V.underlying.obj).inverse (liftLabelMap_zero_bijective _)).comp
    (f.map.comp (Section9.liftLabelMap U.underlying.obj))
  bijective := ((Equiv.ofBijective _ (liftLabelMap_zero_bijective V.underlying)).symm.bijective).comp
    (f.bijective.comp (liftLabelMap_zero_bijective U.underlying))
  preserves p := by
    change U.weight (Section9.liftLabelMap U.underlying.obj p) = V.weight
      (Section9.liftLabelMap V.underlying.obj
        ((Section9.liftLabelMap V.underlying.obj).inverse (liftLabelMap_zero_bijective _)
          (f.map (Section9.liftLabelMap U.underlying.obj p))))
    rw [Map.apply_inverse]
    exact f.preserves _

@[simp] theorem liftMap_labels (hc : CanonicalStructure.IsCanonical (M := M))
    {U V : MeasuredRVZero S d} (f : U ⟶ V) (p : rvLift U.underlying.obj) :
    Section9.liftLabelMap V.underlying.obj ((liftMap hc f).map p) =
      f.map (Section9.liftLabelMap U.underlying.obj p) := Map.apply_inverse _ _ _

/-- The actual zero-coordinate chart has determinant one at every point. -/
theorem liftMap_measure (hc : CanonicalStructure.IsCanonical (M := M))
    {U V : MeasuredRVZero S d} (f : U ⟶ V) (p : rvLift U.underlying.obj) :
    Section9.HasMixedVFJacobianAt (liftMap hc f).map p (1 : VFType (M := M)) ∧
      (U.lift hc).weight p = (V.lift hc).weight ((liftMap hc f).map p) * d.determinant 1 := by
  refine ⟨Section9.hasMixedVFJacobianAt_zero_arity _ _, ?_⟩
  rw [map_one, mul_one]
  exact (liftMap hc f).preserves p

theorem theorem_10_5_weighted_zero (hc : CanonicalStructure.IsCanonical (M := M))
    {U V : MeasuredRVZero S d} (e : U ≅ V) : Nonempty (U.lift hc ≅ V.lift hc) :=
  ⟨WeightedZero.isoOfExactMap (liftMap hc e.hom)⟩

end MeasuredRVZero
end SpecialTransformations.Section10
