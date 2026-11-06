import Section4.RVFinitePositiveComparison
import Section4.RVFinitePadding
import Section4.RVPaddingSplit

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

def rvFinitePaddingInvariant :
    PositiveAdditiveGrothendieck.Invariant (rvFiniteScissorPresentation (M := M) S k)
      (A := RVFiniteKPlus (M := M) S (k + 1)) where
  toFun U := rvFiniteClass ((rvFinitePaddingFunctor S k).obj U)
  iso h := by
    obtain ⟨e⟩ := h
    exact rvFiniteClass_iso ((rvFinitePaddingFunctor S k).mapIso e)
  empty := by
    have he : (rvFinitePaddingFunctor (M := M) S k).obj (rvFiniteEmpty S k) =
        rvFiniteEmpty S (k + 1) := by
      apply ObjectProperty.FullSubcategory.ext
      exact rvPadObject_empty
    change rvFiniteClass ((rvFinitePaddingFunctor S k).obj (rvFiniteEmpty S k)) = 0
    rw [he, rvFiniteClass_empty]
  scissor h := rvFiniteClass_scissor h.pad

def rvFinitePaddingKPlus :
    RVFiniteKPlus (M := M) S k →+ RVFiniteKPlus (M := M) S (k + 1) :=
  PositiveAdditiveGrothendieck.lift (rvFiniteScissorPresentation S k) rvFinitePaddingInvariant

@[simp] theorem rvFinitePaddingKPlus_class (U : RVFiniteObject (M := M) S k) :
    rvFinitePaddingKPlus (rvFiniteClass U) =
      rvFiniteClass ((rvFinitePaddingFunctor S k).obj U) :=
  PositiveAdditiveGrothendieck.lift_of _ _ U

theorem rvFinitePadding_forget :
    (rvFiniteForgetKPlus (M := M) (S := S) (k := k + 1)).comp rvFinitePaddingKPlus =
      rvPaddingKPlus.comp (rvFiniteForgetKPlus (M := M) (S := S) (k := k)) := by
  apply PositiveAdditiveGrothendieck.hom_ext (rvFiniteScissorPresentation S k)
  intro U
  change rvFiniteForgetKPlus (rvFinitePaddingKPlus (rvFiniteClass U)) =
    rvPaddingKPlus (rvFiniteForgetKPlus (rvFiniteClass U))
  rw [rvFinitePaddingKPlus_class, rvFiniteForgetKPlus_class,
    rvFiniteForgetKPlus_class, rvPaddingKPlus_class]
  rfl

/-- The final positive padding injectivity assertion also holds for the
actual finite-volume subcategory. No cancellation assumption is used. -/
theorem rvFinitePaddingKPlus_injective :
    Function.Injective (rvFinitePaddingKPlus (M := M) (S := S) (k := k)) := by
  intro a b h
  apply rvFiniteForgetKPlus_injective
  apply rvPaddingKPlus_injective
  calc
    rvPaddingKPlus (rvFiniteForgetKPlus a) =
        rvFiniteForgetKPlus (rvFinitePaddingKPlus a) :=
      (DFunLike.congr_fun rvFinitePadding_forget a).symm
    _ = rvFiniteForgetKPlus (rvFinitePaddingKPlus b) := congrArg rvFiniteForgetKPlus h
    _ = rvPaddingKPlus (rvFiniteForgetKPlus b) :=
      DFunLike.congr_fun rvFinitePadding_forget b

end SpecialTransformations.Section4

end
