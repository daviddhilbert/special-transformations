/-
# `L_RV`-embeddings transport the `RV` calculus

Direction d5 of swarm `smw2ioy2w`.  An embedding of `L_RV`-structures preserves the function
symbols (`iRVMul`, `iRv`, the constants `iRVOne`, `iRVZero`) hence the `RV`-power `rvPow`, and
preserves *and reflects* the relation symbols (`iLe`, the sort predicates `iRV`, `iVF`).  The
second half is what carries the infinitesimal relation `∀ n, aⁿ ≤ b` of §4 of
`HahnObstruction.lean` across the one-step embedding: an embedding cannot destroy an
infinitesimal, and it cannot create the Archimedean commensurability that the target lacks.
-/
import Enc
import Assembly_frozen

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0

namespace SpecialTransformations.Milestone0.Hahn

/-! ## 1. `L_RV`-embeddings transport the `RV` calculus -/

section Transport

variable {A B : Type} [LRV.Structure A] [LRV.Structure B]

theorem map_rvMul (e : A ↪[LRV] B) (a b : A) :
    e (iRVMul a b) = iRVMul (e a) (e b) := by
  have hvec : (⇑e ∘ ![a, b]) = ![e a, e b] := by funext i; fin_cases i <;> rfl
  have h := e.map_fun Fn.rvMul ![a, b]
  rw [hvec] at h
  simpa [iRVMul] using h

theorem map_rvOne (e : A ↪[LRV] B) : e (iRVOne : A) = (iRVOne : B) := by
  have hvec : (⇑e ∘ (fun i : Fin 0 => i.elim0)) = (fun i : Fin 0 => i.elim0) := by
    funext i; exact i.elim0
  have h := e.map_fun (Fn.rvOne) (fun i : Fin 0 => i.elim0)
  rw [hvec] at h
  simpa [iRVOne] using h

theorem map_rvZero (e : A ↪[LRV] B) : e (iRVZero : A) = (iRVZero : B) := by
  have hvec : (⇑e ∘ (fun i : Fin 0 => i.elim0)) = (fun i : Fin 0 => i.elim0) := by
    funext i; exact i.elim0
  have h := e.map_fun (Fn.rvZero) (fun i : Fin 0 => i.elim0)
  rw [hvec] at h
  simpa [iRVZero] using h

theorem map_rv (e : A ↪[LRV] B) (a : A) : e (iRv a) = iRv (e a) := by
  have hvec : (⇑e ∘ ![a]) = ![e a] := by funext i; fin_cases i; rfl
  have h := e.map_fun Fn.rvMap ![a]
  rw [hvec] at h
  simpa [iRv] using h

/-- `iLe` is preserved and reflected. -/
theorem map_le_iff (e : A ↪[LRV] B) (a b : A) : iLe (e a) (e b) ↔ iLe a b := by
  have hvec : (⇑e ∘ ![a, b]) = ![e a, e b] := by funext i; fin_cases i <;> rfl
  have h := e.map_rel Rel.rvLe ![a, b]
  rw [hvec] at h
  simpa [iLe] using h

/-- `Kˣ` is preserved and reflected. -/
theorem map_units_iff (e : A ↪[LRV] B) (a : A) : iUnits (e a) ↔ iUnits a := by
  have hvec : (⇑e ∘ ![a]) = ![e a] := by funext i; fin_cases i; rfl
  have h := e.map_rel Rel.memUnits ![a]
  rw [hvec] at h
  simpa [iUnits] using h

theorem map_rvMem_iff (e : A ↪[LRV] B) (a : A) : iRV (e a) ↔ iRV a := by
  have hvec : (⇑e ∘ ![a]) = ![e a] := by funext i; fin_cases i; rfl
  have h := e.map_rel Rel.memRV ![a]
  rw [hvec] at h
  simpa [iRV] using h

theorem map_vfMem_iff (e : A ↪[LRV] B) (a : A) : iVF (e a) ↔ iVF a := by
  have hvec : (⇑e ∘ ![a]) = ![e a] := by funext i; fin_cases i; rfl
  have h := e.map_rel Rel.memVF ![a]
  rw [hvec] at h
  simpa [iVF] using h

/-- Embeddings commute with the `RV`-power. -/
theorem map_rvPow (e : A ↪[LRV] B) (a : A) :
    ∀ n : ℕ, e (Assembly.rvPow a n) = Assembly.rvPow (e a) n
  | 0 => by rw [Assembly.rvPow.eq_1, Assembly.rvPow.eq_1, map_rvOne]
  | n + 1 => by
      rw [Assembly.rvPow.eq_2, Assembly.rvPow.eq_2, map_rvMul, map_rvPow e a n]

end Transport

/-! ### Coercion of the `RV` calculus out of a substructure

`Substructure.subtype` is the inclusion; the lemmas below are the four cases §4 of
`HahnObstruction.lean` needs, in the shape in which the coercions actually appear. -/

section Coe

variable {M : Type} [LRV.Structure M]

theorem coe_rvPow (T : LRV.Substructure M) (a : T) (n : ℕ) :
    ((Assembly.rvPow a n : T) : M) = Assembly.rvPow (a : M) n := by
  have h := map_rvPow (Substructure.subtype T) a n
  simpa using h

theorem coe_rv (T : LRV.Substructure M) (a : T) : ((iRv a : T) : M) = iRv (a : M) := by
  have h := map_rv (Substructure.subtype T) a
  simpa using h

theorem coe_rvOne (T : LRV.Substructure M) : ((iRVOne : T) : M) = (iRVOne : M) := by
  have h := map_rvOne (Substructure.subtype T)
  simpa using h

theorem coe_rvZero (T : LRV.Substructure M) : ((iRVZero : T) : M) = (iRVZero : M) := by
  have h := map_rvZero (Substructure.subtype T)
  simpa using h

theorem coe_rvMul (T : LRV.Substructure M) (a b : T) :
    ((iRVMul a b : T) : M) = iRVMul (a : M) (b : M) := by
  have hvec : (fun i => ((![a, b] i : T) : M)) = ![(a : M), (b : M)] := by
    funext i; fin_cases i <;> rfl
  show Structure.funMap (L := LRV) Fn.rvMul (fun i => ((![a, b] i : T) : M))
      = iRVMul (a : M) (b : M)
  rw [hvec]
  rfl

theorem coe_units_iff (T : LRV.Substructure M) (a : T) : iUnits ((a : M)) ↔ iUnits a :=
  map_units_iff (Substructure.subtype T) a

theorem coe_le_iff (T : LRV.Substructure M) (a b : T) :
    iLe ((a : M)) ((b : M)) ↔ iLe a b :=
  map_le_iff (Substructure.subtype T) a b

theorem coe_rvMem_iff (T : LRV.Substructure M) (a : T) : iRV ((a : M)) ↔ iRV a :=
  map_rvMem_iff (Substructure.subtype T) a

theorem coe_vfMem_iff (T : LRV.Substructure M) (a : T) : iVF ((a : M)) ↔ iVF a :=
  map_vfMem_iff (Substructure.subtype T) a

end Coe

end SpecialTransformations.Milestone0.Hahn
