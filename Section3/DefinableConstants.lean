module

public import Mathlib

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
namespace SpecialTransformations.DefinableConstants
variable {M : Type*} {L : Language} [L.Structure M] {A : Set M}

theorem constant {a : M} (ha : A.Definable₁ L {a}) {α : Type*} :
    A.DefinableFun L (fun _ : α → M => a) := by
  have ha' : A.Definable L {x : Fin 1 → M | x 0 = a} := ha
  have h := ha'.preimage_comp (fun _ : Fin 1 => (none : Option α))
  change A.Definable L _
  convert h using 1
  ext w
  exact eq_comm

theorem singleton_of_constant {a : M}
    (ha : A.DefinableFun L (fun _ : Fin 0 → M => a)) : A.Definable₁ L {a} := by
  have ha' : A.Definable L (Function.tupleGraph (fun _ : Fin 0 → M => a)) := ha
  have h := ha'.preimage_comp (fun _ : Option (Fin 0) => (0 : Fin 1))
  change A.Definable L _
  convert h using 1
  ext w
  exact eq_comm

theorem function_symbol {k : ℕ} (f : L.Functions k) (a : Fin k → M)
    (ha : ∀ i, A.Definable₁ L {a i}) : A.Definable₁ L {Structure.funMap f a} := by
  have hf : A.DefinableFun L (Structure.funMap f) :=
    Set.DefinableFun.of_empty (Set.DefinableFun.fun_symbol f)
  have hmap : A.DefinableMap L (fun _ : Fin 0 → M => a) := fun i => constant (ha i)
  exact singleton_of_constant (hf.comp hmap)

theorem eliminate_parameters {B : Set M} {n : ℕ} (s : Set (Fin n → M))
    (hB : ∀ b ∈ B, A.Definable₁ L {b}) (hs : B.Definable L s) : A.Definable L s := by
  classical
  obtain ⟨C, hCB, hC⟩ := Set.definable_iff_finitely_definable.mp hs
  obtain ⟨φ, hφ⟩ := Set.definable_iff_exists_formula_sum.mp hC
  have hfree : (∅ : Set M).Definable L
      {w : (↥(C : Set M) ⊕ Fin n) → M | φ.Realize w} :=
    Set.empty_definable_iff.mpr ⟨φ, rfl⟩
  let F (x : Fin n → M) : (↥(C : Set M) ⊕ Fin n) → M := Sum.elim Subtype.val x
  have hF : A.DefinableMap L F := by
    intro i
    cases i with
    | inl c => exact constant (hB c.val (hCB c.property))
    | inr i => exact Set.DefinableFun.proj L
  have hp := (hfree.mono (Set.empty_subset A)).preimage_map hF
  rw [hφ]
  exact hp

end SpecialTransformations.DefinableConstants
