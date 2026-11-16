module

public import Section10.EssentialVFMeasure
public import Section10.GammaVolumeLift
public import Section10.RVVolumeRepresentative
public import Mathlib.CategoryTheory.Groupoid

@[expose] public section

/-! Remark 10.2 for the two positive-degree finite-volume VF categories.
An arrow is its bijection on independent points together with the
existence of an actual measure-preserving representative. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4

noncomputable section

namespace SpecialTransformations.Section10

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
local notation "VF" => VFType (M := M)

/-- The presentation of a form and the coefficient of a VF determinant. -/
structure VolumeScale (M : Type) [LRV.Structure M] [M ⊨ Axioms.ACVF]
    (G : Type) [CommMonoidWithZero G] where
  space : Space LRV M
  value : space.Carrier → G
  allowed : space.Carrier → Prop
  determinant : VFType (M := M) →*₀ G

def rvVolumeScale : VolumeScale M (CanonicalRV.RVSort M) where
  space := rawRVSpace 1
  value x := x 0
  allowed x := x 0 ≠ 0
  determinant := RVOperations.rvHom

def gammaVolumeScale (hc : CanonicalStructure.IsCanonical (M := M)) :
    VolumeScale M (Values.GammaTop (M := M)) where
  space := volumeGammaSpace hc
  value x := (gammaFormValue (Map.id (DefSet.univ (volumeGammaSpace hc) (∅ : Set M)))
    ⟨x, Set.mem_univ _⟩).val
  allowed _ := True
  determinant := Values.vfValueHom

variable {G : Type} [CommMonoidWithZero G]

/-- The positive-degree finite-volume VF objects of Definition 10.1. -/
structure MeasuredVF (C : BaseContext M) (hc : CanonicalStructure.IsCanonical (M := M))
    (d : VolumeScale M G) (k : ℕ) where
  arity : ℕ
  domain : DefSet (rawMixedSpace (M := M) (k + 1) arity) (C.base : Set M)
  finite : ∀ a, {t | (a, t) ∈ domain.carrier}.Finite
  form : Map domain (DefSet.univ d.space (C.base : Set M))
  allowed : ∀ a, d.allowed (form a).val

namespace MeasuredVF

variable {C : BaseContext M} {hc : CanonicalStructure.IsCanonical (M := M)}
variable {d : VolumeScale M G} {k : ℕ}

def weight (A : MeasuredVF C hc d k) (a : A.domain) : G := d.value (A.form a).val

def Representative (A B : MeasuredVF C hc d k) :=
  {f : EssentialVFMap A.domain B.domain // f.Preserves d.determinant A.weight B.weight}

/-- Using a subtype of the independent-point bijections makes agreement
of morphisms ordinary equality. `quotientEquiv` verifies the quotient. -/
def Germ (A B : MeasuredVF C hc d k) :=
  {e : EssentialVFMap.Generic A.domain ≃ EssentialVFMap.Generic B.domain //
    ∃ f : Representative A B, f.val.genericEquiv hc = e}

def ofRepresentative {A B : MeasuredVF C hc d k} (f : Representative A B) : Germ A B :=
  ⟨f.val.genericEquiv hc, f, rfl⟩

def aeSetoid (A B : MeasuredVF C hc d k) : Setoid (Representative A B) where
  r f g := f.val.genericEquiv hc = g.val.genericEquiv hc
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h j => h.trans j⟩

theorem ae_iff_agreement {A B : MeasuredVF C hc d k} (f g : Representative A B) :
    (aeSetoid A B).r f g ↔
    ∃ E : DefSet (rawMixedSpace (M := M) (k + 1) A.arity) (C.base : Set M),
      vfDim (rawRVSpace 1) (A.domain.sdiff E) < k + 1 ∧
      ∀ x ∈ E.carrier, ∃ (p : f.val.source) (q : g.val.source),
        p.val = x ∧ q.val = x ∧ (f.val.map p).val = (g.val.map q).val :=
  EssentialVFMap.genericEquiv_eq_iff hc C.saturated C.small (Nat.zero_lt_succ k) f.val g.val

/-- Remark 10.2's equivalence classes are exactly the implemented germs. -/
def quotientEquiv (A B : MeasuredVF C hc d k) : Quotient (aeSetoid A B) ≃ Germ A B := by
  let F : Quotient (aeSetoid A B) → Germ A B :=
    Quotient.lift ofRepresentative (fun _ _ h => Subtype.ext h)
  apply Equiv.ofBijective F
  constructor
  · intro x y
    refine Quotient.inductionOn₂ x y ?_
    intro f g he
    exact Quotient.sound (congrArg Subtype.val he)
  · rintro ⟨e, f, rfl⟩
    exact ⟨Quotient.mk _ f, rfl⟩

instance [CharZero VF] : Groupoid (MeasuredVF C hc d k) where
  Hom := Germ
  id A := ⟨Equiv.refl _, by
    obtain ⟨f, hf, he⟩ := EssentialVFMap.exists_preserving_id hc C.uncountable.le
      C.saturated C.small (Nat.zero_lt_succ k) d.determinant A.weight
    exact ⟨⟨f, hf⟩, he⟩⟩
  comp {A B D} f g := ⟨f.val.trans g.val, by
    obtain ⟨p, hp⟩ := f.property
    obtain ⟨q, hq⟩ := g.property
    obtain ⟨e, he, h⟩ := EssentialVFMap.exists_preserving_comp hc C.uncountable.le
      C.saturated C.small (Nat.zero_lt_succ k) d.determinant A.weight B.weight D.weight
      p.val q.val p.property q.property
    exact ⟨⟨e, he⟩, h.trans (congrArg₂ Equiv.trans hp hq)⟩⟩
  id_comp f := by apply Subtype.ext; exact Equiv.refl_trans f.val
  comp_id f := by apply Subtype.ext; exact Equiv.trans_refl f.val
  assoc f g h := by apply Subtype.ext; exact Equiv.trans_assoc f.val g.val h.val
  inv {A B} f := ⟨f.val.symm, by
    obtain ⟨p, hp⟩ := f.property
    obtain ⟨e, he, h⟩ := EssentialVFMap.exists_preserving_symm hc C.uncountable.le
      C.saturated C.small (Nat.zero_lt_succ k) d.determinant A.weight B.weight p.val p.property
    exact ⟨⟨e, he⟩, h.trans (congrArg Equiv.symm hp)⟩⟩
  inv_comp f := by apply Subtype.ext; exact Equiv.symm_trans_self f.val
  comp_inv f := by apply Subtype.ext; exact Equiv.self_trans_symm f.val

/-- Every measured representative yields an isomorphism of germs. -/
def isoOfRepresentative [CharZero VF] {A B : MeasuredVF C hc d k}
    (f : Representative A B) : A ≅ B := by
  let h : A ⟶ B := ofRepresentative f
  exact ⟨h, Groupoid.inv h, Groupoid.comp_inv h, Groupoid.inv_comp h⟩

end MeasuredVF
end SpecialTransformations.Section10
