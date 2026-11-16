module

public import Section4.CanonicalLift
public import Section3.FibreDescent
public import Section3.SortedTuples

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.DefinableGeometry

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem rvTupleFibre_raw_definable (S : Set M) {n : ℕ}
    (t : Fin n → CanonicalRV.RVSort M) :
    (S ∪ Set.range (rvValues t)).Definable LRV (tupleRVFibre (rvValues t)) := by
  let B := S ∪ Set.range (rvValues t)
  have h (i : Fin n) : B.Definable LRV
      {z : Fin n → M | iVF (z i) ∧ iRv (z i) = (t i).val} := by
    have hv := (definableAt_sort B .vf).raw_definable.preimage_comp (fun _ : Fin 1 => i)
    have hr : B.DefinableFun LRV (fun z : Fin n → M => iRv (z i)) :=
      (Set.DefinableFun.of_empty
        (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.rvMap)).comp
        (show B.DefinableMap LRV (fun z : Fin n → M => ![z i]) from
          by intro j; fin_cases j; exact Set.DefinableFun.proj LRV)
    have ht : B.DefinableFun LRV (fun _ : Fin n → M => (t i).val) :=
      LRV.definableFun_const (Fin n) (Or.inr (Set.mem_range_self i))
    exact hv.inter (hr.ofPred_eq ht)
  convert Set.definable_iInter_of_finite h using 1
  ext z
  simp only [tupleRVFibre, rvValues, Set.mem_ofPred_eq, Set.mem_iInter]

theorem rvTupleFibre_definable (hcan : CanonicalStructure.IsCanonical (M := M))
    (S : Set M) {n : ℕ} (t : Fin n → CanonicalRV.RVSort M) :
    DefinableOver (S ∪ Set.range (rvValues t)) (fun _ => .vf) (tupleRVFibre (rvValues t)) :=
  raw_definableOver_sorted hcan _ _ _ (rvTupleFibre_raw_definable S t)
    (fun z hz i => (hz i).1)

theorem rvTupleFibre_nonempty {n : ℕ} (t : Fin n → CanonicalRV.RVSort M) :
    (tupleRVFibre (rvValues t)).Nonempty := by
  obtain ⟨a, ha⟩ := tupleRV_surjective t
  refine ⟨vfValues a, ?_⟩
  intro i
  exact ⟨(a i).property, congrArg Subtype.val (congrFun ha i)⟩

end SpecialTransformations.Section4
