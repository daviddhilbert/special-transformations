import Section4.CodeMaps
import Section4.RealPresentations
import Section3.DefinableConstants

/-! Diagonal affine coordinate changes on a mixed set keep its RV
label. Named scales and translations suffice for definability. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}
local notation "VF" => VFType (M := M)

noncomputable def affineMixedMap (A : DefSet (rawMixedSpace (M := M) n r) S)
    (a b : Fin n → VF) (ha : ∀ i, (a i).val ∈ S) (hb : ∀ i, (b i).val ∈ S) :
    Map A (DefSet.univ (rawMixedSpace (M := M) n r) S) := by
  let P := rawMixedSpace (M := M) n r
  let F (x : P.Carrier) : P.Carrier := (fun i => a i * x.1 i + b i, x.2)
  let C (z : P.Index → M) : P.Index → M :=
    Sum.elim (fun i => iVFAdd (iVFMul (a i).val (z (.inl i))) (b i).val) (z ∘ Sum.inr)
  have hC : S.DefinableMap LRV C := by
    intro i
    rcases i with i | i
    · have hmul : S.DefinableFun LRV (fun z : P.Index → M => iVFMul (a i).val (z (.inl i))) :=
        (Set.DefinableFun.of_empty (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.vfMul)).comp
          (show S.DefinableMap LRV (fun z : P.Index → M => ![(a i).val, z (.inl i)]) from by
            intro j
            fin_cases j
            · exact LRV.definableFun_const _ (ha i)
            · exact Set.DefinableFun.proj LRV)
      exact (Set.DefinableFun.of_empty (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.vfAdd)).comp
        (show S.DefinableMap LRV (fun z : P.Index → M => ![iVFMul (a i).val (z (.inl i)), (b i).val]) from by
          intro j
          fin_cases j
          · exact hmul
          · exact LRV.definableFun_const _ (hb i))
    · exact Set.DefinableFun.proj LRV
  have hcode (z : P.domain) : mixedValues (F (P.decode z)) = C z.val := by
    funext i
    have he := mixedValues_decode z
    rcases i with i | i
    · have hz : ((P.decode z).1 i).val = z.val (.inl i) := congrFun he (.inl i)
      change iVFAdd (iVFMul (a i).val ((P.decode z).1 i).val) (b i).val = _
      rw [hz]
      rfl
    · exact congrFun he (.inr i)
  have hdom (z : P.domain) : C z.val ∈ P.domain := hcode z ▸ mixedValues_mem_domain _
  exact Map.ofCodes A F C hC hdom (fun z => mixedValues_injective
    ((mixedValues_decode ⟨C z.val, hdom z⟩).trans (hcode z).symm))

@[simp] theorem affineMixedMap_apply (A : DefSet (rawMixedSpace (M := M) n r) S)
    (a b : Fin n → VF) (ha : ∀ i, (a i).val ∈ S) (hb : ∀ i, (b i).val ∈ S) (p : A) :
    (affineMixedMap A a b ha hb p).val = (fun i => a i * p.val.1 i + b i, p.val.2) := rfl

end SpecialTransformations.Section9
