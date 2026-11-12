module

public import Section4.DefinableCategory
public import Section4.UnionMapLaws
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

@[expose] public section

open Classical FirstOrder FirstOrder.Language CategoryTheory CategoryTheory.Limits

noncomputable section

namespace SpecialTransformations.DefinableGeometry.DefinableSetCat

variable {L : Language} {M : Type} [L.Structure M]
variable {ι : Type} {F : ι → Space L M} {S : Set M}

def objOfSet (i : ι) (A : DefSet (F i) S) : DefinableSetCat F S := ⟨i, A⟩

def unionInl (i : ι) (A B : DefSet (F i) S) :
    objOfSet i A ⟶ objOfSet i (A.union B) := Map.inclusion (fun _ h => Or.inl h)

def unionInr (i : ι) (A B : DefSet (F i) S) :
    objOfSet i B ⟶ objOfSet i (A.union B) := Map.inclusion (fun _ h => Or.inr h)

def unionDesc {i : ι} {A B : DefSet (F i) S} {W : DefinableSetCat F S}
    (f : objOfSet i A ⟶ W) (g : objOfSet i B ⟶ W) : objOfSet i (A.union B) ⟶ W :=
  f.union g

theorem unionInl_desc {i : ι} {A B : DefSet (F i) S} {W : DefinableSetCat F S}
    (f : objOfSet i A ⟶ W) (g : objOfSet i B ⟶ W) : unionInl i A B ≫ unionDesc f g = f := by
  apply Map.ext
  intro a
  exact Map.union_on_left f g a

theorem unionInr_desc {i : ι} {A B : DefSet (F i) S} {W : DefinableSetCat F S}
    (hd : Disjoint A.carrier B.carrier) (f : objOfSet i A ⟶ W) (g : objOfSet i B ⟶ W) :
    unionInr i A B ≫ unionDesc f g = g := by
  apply Map.ext
  intro b
  exact Map.union_on_right f g hd b

theorem union_hom_ext {i : ι} {A B : DefSet (F i) S} {W : DefinableSetCat F S}
    {f g : objOfSet i (A.union B) ⟶ W}
    (hl : unionInl i A B ≫ f = unionInl i A B ≫ g)
    (hr : unionInr i A B ≫ f = unionInr i A B ≫ g) : f = g := by
  apply Map.ext
  intro a
  rcases a.property with ha | hb
  · exact congrArg (fun h : objOfSet i A ⟶ W => homFunction h ⟨a.val, ha⟩) hl
  · exact congrArg (fun h : objOfSet i B ⟶ W => homFunction h ⟨a.val, hb⟩) hr

/-- A disjoint definable union is a categorical coproduct in every
category of finitely presented definable sets with unrestricted definable maps. -/
def unionIsColimit (i : ι) (A B : DefSet (F i) S) (hd : Disjoint A.carrier B.carrier) :
    IsColimit (BinaryCofan.mk (unionInl i A B) (unionInr i A B)) :=
  BinaryCofan.IsColimit.mk _ (fun f g => unionDesc f g) unionInl_desc
    (unionInr_desc hd) (fun f g m hl hr => union_hom_ext
      (hl.trans (unionInl_desc f g).symm) (hr.trans (unionInr_desc hd f g).symm))

end SpecialTransformations.DefinableGeometry.DefinableSetCat

end
