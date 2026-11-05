import Section3.SortedParameterElimination
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem definableClosureAt_function_symbol (S : Set M) {k : ℕ} (f : Fn k)
    (xs : Fin k → M) (hs : ∀ i, sortEval (Fn.argSort f i) (xs i))
    (hd : ∀ i, DefinableClosureAt S (Fn.argSort f i) (xs i)) :
    DefinableClosureAt S (Fn.resSort f) (Structure.funMap (L := LRV) f xs) := by
  let C := Set.range xs
  let p : Parameters C := ⟨k, xs, Fn.argSort f, hs, fun i => Set.mem_range_self i⟩
  let t : LRV.Term (Fin k ⊕ Fin 1) := .func f (fun i => .var (.inl i))
  let φ : LRV.BoundedFormula (Fin k) 1 := .equal (.var (.inr 0)) t
  have ht : TmSort p.sorts (fun _ : Fin 1 => Fn.resSort f) t = some (Fn.resSort f) := by
    apply tmSort_func
    intro i
    rfl
  have hw : WellSorted p.sorts (fun _ : Fin 1 => Fn.resSort f) φ :=
    .equal _ rfl ht
  have hout := CanonicalStructure.function_sort hM f xs hs
  have he (z : Fin 1 → M) : φ.Realize p.values z ↔
      z 0 = Structure.funMap (L := LRV) f xs := by
    rfl
  have hnamed : DefinableClosureAt C (Fn.resSort f)
      (Structure.funMap (L := LRV) f xs) := by
    constructor
    · refine ⟨p, φ, hw, ?_⟩
      ext z
      change z 0 = Structure.funMap (L := LRV) f xs ↔
        (∀ i, sortEval (Fn.resSort f) (z i)) ∧ φ.Realize p.values z
      constructor
      · intro hz
        refine ⟨?_, (he z).mpr hz⟩
        intro i; fin_cases i
        exact hz ▸ hout
      · intro hz
        exact (he z).mp hz.2
    · rintro y rfl
      exact hout
  apply hnamed.eliminate_sorted_definable_params
  rintro y ⟨i, rfl⟩
  exact ⟨Fn.argSort f i, hd i⟩

end SpecialTransformations.Section3
