import Section4.RVPadding

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

/-- The same padding functor restricts to RV[k]. -/
def rvFinitePaddingFunctor (S : Set M) (k : ℕ) :
    RVFiniteObject (M := M) S k ⥤ RVFiniteObject (M := M) S (k + 1) where
  obj U := ⟨rvPadObject U.obj, rvPadObject_finite_volume U.obj U.property⟩
  map f := ObjectProperty.homMk (rvPadHom f.hom)
  map_id _ := by apply ObjectProperty.hom_ext; apply RVHom.ext; rfl
  map_comp _ _ := by apply ObjectProperty.hom_ext; apply RVHom.ext; rfl

def rvFinitePaddingFullyFaithful (S : Set M) (k : ℕ) :
    (rvFinitePaddingFunctor (M := M) S k).FullyFaithful where
  preimage f := ObjectProperty.homMk (rvUnpadHom f.hom)
  map_preimage _ := by apply ObjectProperty.hom_ext; apply RVHom.ext; rfl
  preimage_map _ := by apply ObjectProperty.hom_ext; apply RVHom.ext; rfl

theorem rvFinitePadding_injective (S : Set M) (k : ℕ) :
    Function.Injective (rvFinitePaddingFunctor (M := M) S k).obj := by
  intro U V he
  have h := congrArg (fun W : RVFiniteObject (M := M) S (k + 1) => W.obj) he
  apply ObjectProperty.FullSubcategory.ext
  exact rvPadObject_injective S k h

end SpecialTransformations.Section4

end
