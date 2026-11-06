import Section4.FiniteMaps
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.CategoryTheory.Types.Basic

open Classical FirstOrder FirstOrder.Language CategoryTheory

namespace SpecialTransformations.DefinableGeometry

variable {L : Language} {M : Type} [L.Structure M]

namespace Map

variable {P Q : Space L M} {S : Set M} {A : DefSet P S} {B : DefSet Q S}

/-- A definable bijection has a definable inverse over the same base. -/
noncomputable def inverse (f : Map A B) (hf : Function.Bijective f) : Map B A where
  toFun := (Equiv.ofBijective f hf).symm
  graph_definable := (f.graph_definable.swap P Q).congr Q P (by
    intro y x
    let e : A ≃ B := Equiv.ofBijective f hf
    constructor
    · rintro ⟨a, ha, hf⟩
      refine ⟨e a, hf, ?_⟩
      change (e.symm (e a)).val = x
      simpa only [Equiv.symm_apply_apply] using ha
    · rintro ⟨b, hb, hi⟩
      refine ⟨e.symm b, hi, ?_⟩
      change (e (e.symm b)).val = y
      simpa only [Equiv.apply_symm_apply] using hb)

@[simp] theorem inverse_apply (f : Map A B) (hf : Function.Bijective f) (a : A) :
    f.inverse hf (f a) = a := (Equiv.ofBijective f hf).symm_apply_apply a

@[simp] theorem apply_inverse (f : Map A B) (hf : Function.Bijective f) (b : B) :
    f (f.inverse hf b) = b := (Equiv.ofBijective f hf).apply_symm_apply b

end Map

/-- Objects have finite presentations from the specified family; morphisms
are functions with complete definable graphs, using Mathlib's Category. -/
structure DefinableSetCat {ι : Type} (F : ι → Space L M) (S : Set M) where
  index : ι
  set : DefSet (F index) S

namespace DefinableSetCat

variable {ι : Type} {F : ι → Space L M} {S : Set M}

instance : Category (DefinableSetCat F S) where
  Hom A B := Map A.set B.set
  id A := Map.id A.set
  comp f g := g.comp f
  id_comp _ := by ext a; rfl
  comp_id _ := by ext a; rfl
  assoc _ _ _ := by ext a; rfl

def homFunction {A B : DefinableSetCat F S} (f : A ⟶ B) : A.set → B.set :=
  (show Map A.set B.set from f).toFun

def forget : DefinableSetCat F S ⥤ Type where
  obj A := A.set
  map f := TypeCat.ofHom (homFunction f)

instance : (forget (F := F) (S := S)).Faithful where
  map_injective h := by
    apply Map.ext
    intro a
    exact congrArg (fun u => TypeCat.Hom.hom u a) h

noncomputable def isoOfBijective {A B : DefinableSetCat F S}
    (f : A ⟶ B) (hf : Function.Bijective (homFunction f)) : A ≅ B where
  hom := f
  inv := f.inverse hf
  hom_inv_id := by apply Map.ext; intro a; exact Map.inverse_apply f hf a
  inv_hom_id := by apply Map.ext; intro b; exact Map.apply_inverse f hf b

theorem bijective_of_iso {A B : DefinableSetCat F S} (e : A ≅ B) :
    Function.Bijective (homFunction e.hom) := by
  have hl : Function.LeftInverse (homFunction e.inv) (homFunction e.hom) := by
    intro a
    exact congrArg (fun f : A ⟶ A => homFunction f a) e.hom_inv_id
  have hr : Function.RightInverse (homFunction e.inv) (homFunction e.hom) := by
    intro b
    exact congrArg (fun f : B ⟶ B => homFunction f b) e.inv_hom_id
  exact ⟨hl.injective, hr.surjective⟩

end DefinableSetCat

end SpecialTransformations.DefinableGeometry
