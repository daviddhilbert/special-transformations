module

public import CanonicalQF
public import Mathlib.ModelTheory.ElementaryMaps

@[expose] public section

/-! Canonical native models are fixed by the released normalization.
This adapter lets actual elementary maps be used by the earlier envelope
interface, whose source and target structures are explicitly normalized.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Section6.CanonicalEmbedding

theorem normalize_eq {C : Type} [sC : LRV.Structure C]
    (hcan : CanonicalStructure.IsCanonical (M := C)) :
    CanonicalStructure.normalize (M := C) = sC := by
  apply Structure.ext
  · funext k f z
    change (if ∀ i, sortEval (Fn.argSort f i) (z i) then
      Structure.funMap f z else CanonicalStructure.sortZero (Fn.resSort f)) = _
    split_ifs with h
    · rfl
    · exact (hcan.1 f z h).symm
  · funext k r z
    cases r with
    | memVF => rfl
    | memRV => rfl
    | memUnits => rfl
    | rvLe =>
      apply propext
      change ((∀ i, sortEval .rv (z i)) ∧ Structure.RelMap (L := LRV) Rel.rvLe z) ↔
        Structure.RelMap (L := LRV) Rel.rvLe z
      constructor
      · exact And.right
      · intro h
        refine ⟨?_, h⟩
        by_contra hn
        exact hcan.2 z hn h

def normalized {C D : Type} [sC : LRV.Structure C] [sD : LRV.Structure D]
    (hc : CanonicalStructure.IsCanonical (M := C))
    (hd : CanonicalStructure.IsCanonical (M := D)) (j : C ↪ₑ[LRV] D) :
    @ElementaryEmbedding LRV C D (CanonicalStructure.normalize (M := C))
      (CanonicalStructure.normalize (M := D)) := by
  let f : C → D := @ElementaryEmbedding.toFun LRV C D sC sD j
  refine @ElementaryEmbedding.mk LRV C D (CanonicalStructure.normalize (M := C))
    (CanonicalStructure.normalize (M := D)) f ?_
  intro n φ x
  have h := @ElementaryEmbedding.map_formula LRV C D sC sD j (Fin n) φ x
  change @Formula.Realize LRV D (CanonicalStructure.normalize (M := D)) _ φ (f ∘ x) ↔
    @Formula.Realize LRV C (CanonicalStructure.normalize (M := C)) _ φ x
  rw [normalize_eq hc, normalize_eq hd]
  exact h

theorem normalized_apply {C D : Type} [sC : LRV.Structure C] [sD : LRV.Structure D]
    (hc : CanonicalStructure.IsCanonical (M := C))
    (hd : CanonicalStructure.IsCanonical (M := D)) (j : C ↪ₑ[LRV] D) (x : C) :
    normalized hc hd j x = j x := by
  rfl

end SpecialTransformations.Section6.CanonicalEmbedding
