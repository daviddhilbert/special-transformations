module

public import Section6.HenselianImages
public import Section6.ExpandedImages

@[expose] public section

/-! Native image and sort identities for postcomposition into a common
ACVF envelope. These are encoding bridges, with no elimination premise. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.Milestone0.LRV FirstOrder.Language.sum
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Section6.NativeImageTransport
open RVTermSupport ExpandedLogic

variable {E : _root_.FirstOrder.Language.{0, 0}} {M C D : Type}
variable [(Expanded E).Structure M] [LRV.Structure M] [LRV.Structure C] [LRV.Structure D]
variable [(LHom.sumInl : LRV →ᴸ Expanded E).IsExpansionOn M]

theorem sorts_preserved (f : M ↪[LRV] C) (s : SortTag) (m : M) :
    sortEval s (f m) ↔ tagEval (E := E) s m := by
  let r : Rel 1 := match s with | .vf => .memVF | .rv => .memRV
  have h := f.map_rel r ![m]
  have he : f ∘ ![m] = ![f m] := by funext i; fin_cases i; rfl
  rw [he] at h
  have hs := (LHom.sumInl : LRV →ᴸ Expanded E).map_onRelation r ![m]
  cases s <;> exact h.trans (Iff.of_eq hs.symm)

theorem range_comp (f : M ↪[LRV] C) (j : C ↪[LRV] D) :
    ExpandedImages.Image (j.comp f) = (ExpandedImages.Image f).map j.toHom := by
  ext d
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨f m, ⟨m, rfl⟩, hm⟩
  · rintro ⟨c, ⟨m, rfl⟩, hm⟩
    exact ⟨m, hm⟩

theorem henselian_range_comp [C ⊨ Axioms.ACVF] [D ⊨ Axioms.ACVF]
    (f : M ↪[LRV] C) (h : HenselianInputs (ExpandedImages.Image f))
    (hc : CanonicalStructure.IsCanonical (M := C))
    (hd : CanonicalStructure.IsCanonical (M := D)) (j : C ↪ₑ[LRV] D) :
    HenselianInputs (ExpandedImages.Image (j.toEmbedding.comp f)) := by
  rw [range_comp]
  exact h.map hc hd j

end SpecialTransformations.Section6.NativeImageTransport
