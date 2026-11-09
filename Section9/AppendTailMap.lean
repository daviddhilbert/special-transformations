import Section4.CodeMaps
import Section4.VFRealFibres
import Section7.TupleCoordinates

/-! Append a VF tail to the VF output of a mixed map and retain its RV
label. This operation is definable by a coordinate reindexing. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section4 SpecialTransformations.Section7
open SpecialTransformations.DefinableGeometry

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M] {k m r : ℕ} {S : Set M}
variable {P : Space LRV M} {A : DefSet P S}
variable {B : DefSet (rawMixedSpace (M := M) k r) S}

noncomputable def appendTailMap (H : Map A B)
    (T : Map A (DefSet.univ (rawVFSpace (M := M) m) S)) :
    Map A (DefSet.univ (rawMixedSpace (M := M) (k + m) r) S) := by
  let Q := rawMixedSpace (M := M) k r
  let V := rawVFSpace (M := M) m
  let W := rawMixedSpace (M := M) (k + m) r
  let I := Q.prod V
  let f (p : I.Carrier) : W.Carrier := (productTuple p.1.1 p.2, p.1.2)
  let e : Fin k ⊕ Fin m ≃ Fin (k + m) := finSumFinEquiv
  let σ : W.Index → I.Index := Sum.elim
    (Sum.elim (fun i => .inl (.inl i)) Sum.inr ∘ e.symm) (fun i => .inl (.inr i))
  let F (z : I.Index → M) : W.Index → M := z ∘ σ
  have hcode (z : I.domain) : mixedValues (f (I.decode z)) = F z.val := by
    have hQ := mixedValues_decode ⟨z.val ∘ Sum.inl, z.property.1⟩
    have hV := vfValues_decode ⟨z.val ∘ Sum.inr, z.property.2⟩
    funext i
    rcases i with i | i
    · obtain ⟨j, rfl⟩ := e.surjective i
      cases j with
      | inl j =>
        change (productTuple (I.decode z).1.1 (I.decode z).2 (productLeft k m j)).val = _
        rw [productTuple_left]
        have h := congrFun hQ (Sum.inl j)
        change ((I.decode z).1.1 j).val = z.val (.inl (.inl j)) at h
        simpa only [F, Function.comp_apply, σ, Sum.elim_inl, e.symm_apply_apply] using h
      | inr j =>
        change (productTuple (I.decode z).1.1 (I.decode z).2 (productRight k m j)).val = _
        rw [productTuple_right]
        have h := congrFun hV j
        change ((I.decode z).2 j).val = z.val (.inr j) at h
        simpa only [F, Function.comp_apply, σ, Sum.elim_inl, Sum.elim_inr, e.symm_apply_apply] using h
    · exact congrFun hQ (Sum.inr i)
  have hdom (z : I.domain) : F z.val ∈ W.domain := (hcode z) ▸ mixedValues_mem_domain _
  let L : Map (B.prod (DefSet.univ V S)) (DefSet.univ W S) := Map.ofCodes _ f F
    (fun _ => Set.DefinableFun.proj LRV) hdom (fun z =>
      mixedValues_injective ((mixedValues_decode ⟨F z.val, hdom z⟩).trans (hcode z).symm))
  exact L.comp (H.pair T)

@[simp] theorem appendTailMap_apply (H : Map A B)
    (T : Map A (DefSet.univ (rawVFSpace (M := M) m) S)) (p : A) :
    (appendTailMap H T p).val = (productTuple (H p).val.1 (T p).val, (H p).val.2) := rfl

end SpecialTransformations.Section9
