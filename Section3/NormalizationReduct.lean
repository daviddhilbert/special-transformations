module

public import Section3.DefinableReduct
public import CanonicalStructure
public import Section3.ParameterBridge
public import Section3.DefinableConstants

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.ModelTheory
namespace SpecialTransformations.Section3
variable {M : Type} [sM : LRV.Structure M]

private theorem sort_definable {k : ℕ} (σ : SortTag) (i : Fin k) :
    (∅ : Set M).Definable LRV {x : Fin k → M | sortEval σ (x i)} := by
  have h : (∅ : Set M).Definable LRV {x : Fin 1 → M | sortEval σ (x 0)} :=
    (definableAt_sort (∅ : Set M) σ).raw_definable
  exact h.preimage_comp (fun _ : Fin 1 => i)

private theorem sortZero_definable {α : Type} (σ : SortTag) :
    (∅ : Set M).DefinableFun LRV (fun _ : α → M => CanonicalStructure.sortZero σ) := by
  cases σ with
  | vf =>
    exact DefinableConstants.constant
      (DefinableConstants.function_symbol (L := LRV) (A := (∅ : Set M))
        Fn.vfZero Fin.elim0 (fun i => i.elim0))
  | rv =>
    exact DefinableConstants.constant
      (DefinableConstants.function_symbol (L := LRV) (A := (∅ : Set M))
        Fn.rvZero Fin.elim0 (fun i => i.elim0))

private theorem relation_definable {k : ℕ} (r : Rel k) :
    (∅ : Set M).Definable LRV {x : Fin k → M | Structure.RelMap (L := LRV) r x} := by
  apply Set.empty_definable_iff.mpr
  exact ⟨.rel r (fun i => .var (.inl i)), rfl⟩

theorem normalization_definableReduct :
    DefinableReduct sM (CanonicalStructure.normalize (M := M)) := by
  classical
  constructor
  · intro k f
    have hguard : (∅ : Set M).Definable LRV
        {x : Fin k → M | ∀ i, sortEval (Fn.argSort f i) (x i)} := by
      convert Set.definable_iInter_of_finite
        (fun i => sort_definable (M := M) (Fn.argSort f i) i) using 1
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    change (∅ : Set M).DefinableFun LRV (fun x : Fin k → M =>
      if ∀ i, sortEval (Fn.argSort f i) (x i) then Structure.funMap (L := LRV) f x
      else CanonicalStructure.sortZero (Fn.resSort f))
    classical
    exact Set.DefinableFun.ite hguard (Set.DefinableFun.fun_symbol f)
      (sortZero_definable (Fn.resSort f))
  · intro k r
    cases r with
    | memVF => exact relation_definable Rel.memVF
    | memRV => exact relation_definable Rel.memRV
    | memUnits => exact relation_definable Rel.memUnits
    | rvLe =>
      have hguard : (∅ : Set M).Definable LRV
          {x : Fin 2 → M | ∀ i, sortEval .rv (x i)} := by
        convert Set.definable_iInter_of_finite
          (fun i => sort_definable (M := M) .rv i) using 1
        ext x
        simp only [Set.mem_ofPred_eq, Set.mem_iInter]
      exact hguard.inter (relation_definable Rel.rvLe)

end SpecialTransformations.Section3
