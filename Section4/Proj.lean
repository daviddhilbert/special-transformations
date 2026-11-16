module

/-
**Projection of a definable set along a coordinate** — the same job as `Compose.lean`'s
`DefinableFun`-composition, and the second half of what the project's brief names as the wall.

`Definable S A` says `A ⊆ VF^n × RV^{m+1}` is cut out by a well-sorted `L_RV` formula.  This file
shows that the projection

  `{y : VF^n × RV^m | ∃ c ∈ RV, (y, c) ∈ A}`

is again definable — i.e. `Definable` is closed under the *guarded* existential that `WellSorted`
does admit (`exSortedG`), with the bookkeeping that the projected coordinate is the last `RV`-slot.

The only real work is that bookkeeping: `snocRV` appends an `RV` element to a tuple, and
`fSort_castAdd_one`/`fSort_last`/`fSort_finAppend_rv` say that appending `rv` to the sort signature
is appending the coordinate to the tuple.  `finAppend` is `Fin.addCases` with its two sizes as
*explicit* arguments: `Fin.append` infers its sizes from the ambient type, which in this file is
`Fin (n + (m + 1))` and gets mis-read as `Fin (n + (m + 1)) = Fin (n + (m+1))` with the wrong split.

No `sorry`, no `axiom`, no `native_decide`.
-/
public import Compose

@[expose] public section

set_option linter.unusedVariables false
open FirstOrder FirstOrder.Language

namespace SpecialTransformations.Milestone0
open LRV

namespace Sec4FunComp

open Sec4Dim Sec4Compose

variable {M : Type} [LRV.Structure M]

/-! ## Concatenating tuples with explicit sizes -/

/-- `Fin.addCases` with both sizes explicit.  `Fin.append` is the same function, but Lean infers
its sizes from the ambient `Fin (m + n)`, which is ambiguous for the shapes in this file. -/
def finAppend {N K : ℕ} {β : Type} (a : Fin N → β) (b : Fin K → β) : Fin (N + K) → β :=
  @Fin.addCases N K (fun _ => β) a b

@[simp]
theorem finAppend_castAdd {N K : ℕ} {β : Type} (a : Fin N → β) (b : Fin K → β) (i : Fin N) :
    finAppend a b (Fin.castAdd K i) = a i :=
  Fin.addCases_left _

@[simp]
theorem finAppend_natAdd {N K : ℕ} {β : Type} (a : Fin N → β) (b : Fin K → β) (j : Fin K) :
    finAppend a b (Fin.natAdd N j) = b j :=
  Fin.addCases_right _

theorem finAppend_eq_append {N K : ℕ} {β : Type} (a : Fin N → β) (b : Fin K → β) :
    finAppend a b = Fin.append a b := rfl

/-! ## Sorting: the last slot of `VF^n × RV^{m+1}` -/

theorem fin_last_natAdd_last (n m : ℕ) :
    (Fin.natAdd n (Fin.last m) : Fin (n + (m + 1))) = Fin.natAdd (n + m) (0 : Fin 1) :=
  Fin.ext rfl

theorem fin_castSucc_castAdd (n m : ℕ) (i : Fin n) :
    (Fin.castSucc (Fin.castAdd m i) : Fin (n + (m + 1))) = Fin.castAdd (m + 1) i :=
  Fin.ext rfl

theorem fin_castSucc_natAdd (n m : ℕ) (k : Fin m) :
    (Fin.castSucc (Fin.natAdd n k) : Fin (n + (m + 1))) = Fin.natAdd n (Fin.castSucc k) :=
  Fin.ext rfl

/-- Dropping the last `RV`-slot of `VF^n × RV^{m+1}` gives back the sort of `VF^n × RV^m`. -/
theorem fSort_castSucc (n m : ℕ) (s : Fin (n + m)) :
    fSort n (m + 1) (Fin.castSucc s) = fSort n m s := by
  refine Fin.addCases (fun i₀ => ?_) (fun k => ?_) s
  · rw [fin_castSucc_castAdd]
    simp only [fSort, finSumFinEquiv_symm_apply_castAdd]
    rfl
  · rw [fin_castSucc_natAdd]
    simp only [fSort, finSumFinEquiv_symm_apply_natAdd]
    rfl

/-- Dropping the last `RV`-slot, in the `Fin.castAdd 1` form that `Fin.append` splits at. -/
theorem fSort_castAdd_one (n m : ℕ) (s : Fin (n + m)) :
    fSort n (m + 1) (Fin.castAdd 1 s) = fSort n m s := by
  rw [show (Fin.castAdd 1 s : Fin (n + (m + 1))) = Fin.castSucc s from Fin.ext rfl]
  exact fSort_castSucc n m s

/-- The last `RV`-slot of `VF^n × RV^{m+1}` has sort `rv`. -/
theorem fSort_last (n m : ℕ) :
    fSort n (m + 1) (Fin.natAdd (n + m) (0 : Fin 1)) = SortTag.rv := by
  rw [← fin_last_natAdd_last]
  simp only [fSort, finSumFinEquiv_symm_apply_natAdd]
  rfl

/-- Appending an `rv`-slot to the sort signature is the sort of `VF^n × RV^{m+1}`. -/
theorem fSort_finAppend_rv (n m : ℕ) :
    finAppend (N := n + m) (K := 1) (fSort n m) (fun _ => SortTag.rv) = fSort n (m + 1) := by
  funext t
  refine Fin.addCases (fun s => ?_) (fun i => ?_) t
  · rw [finAppend_castAdd, fSort_castAdd_one]
  · rw [show i = (0 : Fin 1) from Subsingleton.elim i 0, finAppend_natAdd, fSort_last]

/-! ## Appending an `RV` element to a tuple -/

theorem sort_append (y : Tup M n m) (c : M) (hc : iRV c) :
    ∀ t : Fin ((n + m) + 1),
      sortEval (fSort n (m + 1) t)
        (finAppend (N := n + m) (K := 1) (tupAssign y) (fun _ => c) t) := by
  intro t
  refine Fin.addCases (fun s => ?_) (fun i => ?_) t
  · rw [finAppend_castAdd, fSort_castAdd_one]
    exact y.2 (finSumFinEquiv.symm s)
  · rw [show i = (0 : Fin 1) from Subsingleton.elim i 0, finAppend_natAdd, fSort_last]
    exact hc

/-- `y ↦ (y, c)`: append an `RV` element to a tuple of `VF^n × RV^m`. -/
def snocRV {n m : ℕ} (y : Tup M n m) (c : M) (hc : iRV c) : Tup M n (m + 1) :=
  tupOf (k := n) (l := m + 1)
    (finAppend (N := n + m) (K := 1) (tupAssign y) (fun _ => c)) (sort_append y c hc)

theorem tupAssign_snocRV {n m : ℕ} (y : Tup M n m) (c : M) (hc : iRV c) :
    tupAssign (snocRV y c hc) =
      finAppend (N := n + m) (K := 1) (tupAssign y) (fun _ => c) :=
  tupAssign_tupOf _ _

/-- The value of `snocRV` at the last slot, in the `Fin.addCases` form of `finAppend`. -/
theorem snocRV_val {n m : ℕ} (y : Tup M n m) (c : M) (hc : iRV c) (t : Fin ((n + m) + 1)) :
    (snocRV y c hc : Idx n (m + 1) → M) (finSumFinEquiv.symm t) =
      finAppend (N := n + m) (K := 1) (tupAssign y) (fun _ => c) t := by
  simp [snocRV, tupOf]

/-- **The two readings of the appended tuple agree**: `Fin.append` (which `exsG` produces) and the
tuple `snocRV` (which the projection speaks about). -/
theorem append_eq_snocRV {n m : ℕ} (y : Tup M n m) (a : Fin 1 → M) (ha : iRV (a 0)) :
    Fin.append (fun t => (y : Idx n m → M) (finSumFinEquiv.symm t)) a =
      fun t => (snocRV y (a 0) ha : Idx n (m + 1) → M) (finSumFinEquiv.symm t) := by
  funext t
  rw [snocRV_val]
  have ha0 : a = fun _ : Fin 1 => a 0 := by
    funext i
    rw [show i = (0 : Fin 1) from Subsingleton.elim i 0]
  rw [ha0]
  rfl

/-! ## The projection lemma -/

/-- **`Definable` is closed under projection along the last `RV`-coordinate.**  This is the guarded
existential `exSortedG` applied to the defining formula, with the coordinate bookkeeping above. -/
theorem Definable.exists_snocRV (S : SP M) {n m : ℕ} {A : Set (Tup M n (m + 1))}
    (hA : Definable S A) :
    Definable S {y : Tup M n m | ∃ (c : M) (hc : iRV c), snocRV y c hc ∈ A} := by
  obtain ⟨φ, hφ, hA'⟩ := hA
  refine ⟨exsG (n + m) 1 (fun _ => SortTag.rv) φ, ?_, ?_⟩
  · refine wellSorted_exsG S.sortMap 1 (fun _ => SortTag.rv) (fSort n m) ?_
    rw [← finAppend_eq_append, fSort_finAppend_rv]
    exact hφ
  · intro y
    rw [exsG_realize]
    constructor
    · rintro ⟨a, ha, hbody⟩
      have hmem : snocRV y (a 0) (ha 0) ∈ A := by
        refine (hA' (snocRV y (a 0) (ha 0))).1 ?_
        exact append_eq_snocRV y a (ha 0) ▸ hbody
      exact ⟨a 0, ha 0, hmem⟩
    · rintro ⟨c, hc, hmem⟩
      refine ⟨fun _ => c, fun _ => hc, ?_⟩
      exact (append_eq_snocRV y (fun _ => c) hc).symm ▸ (hA' (snocRV y c hc)).2 hmem

/-- Projection along **two** `RV` coordinates, by iterating `exists_snocRV` — the shape a fibre
`fib(A, t̄) ⊆ RV^m` needs when `m ≥ 2`. -/
theorem Definable.exists_snocRV_two (S : SP M) {n m : ℕ} {A : Set (Tup M n (m + 2))}
    (hA : Definable S A) :
    Definable S {y : Tup M n m | ∃ (c₁ : M) (h₁ : iRV c₁) (c₂ : M) (h₂ : iRV c₂),
      snocRV (snocRV y c₁ h₁) c₂ h₂ ∈ A} :=
  Definable.exists_snocRV S (n := n) (m := m)
    (A := {z : Tup M n (m + 1) | ∃ (c : M) (hc : iRV c), snocRV z c hc ∈ A})
    (Definable.exists_snocRV S (n := n) (m := m + 1) (A := A) hA)

end Sec4FunComp

end SpecialTransformations.Milestone0

/-! ## Axiom audit -/

#print axioms SpecialTransformations.Milestone0.Sec4FunComp.fSort_finAppend_rv
#print axioms SpecialTransformations.Milestone0.Sec4FunComp.tupAssign_snocRV
#print axioms SpecialTransformations.Milestone0.Sec4FunComp.Definable.exists_snocRV
#print axioms SpecialTransformations.Milestone0.Sec4FunComp.Definable.exists_snocRV_two
