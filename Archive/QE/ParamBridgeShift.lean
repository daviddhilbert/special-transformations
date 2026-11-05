/-
**Parameter relabelling of the well-sorted fragment** — from swarm `smw1bwjo2` m2, verified here
(compiled; 0 errors, no `sorry`, axioms within {propext, Classical.choice, Quot.sound}).  The earlier
swarm recorded this transport as *not* delivered; with `Occurs := InAntecedent` it is routine,
because the guard transports by its own constructors, which a compiled match could not do.

`wellSorted_relabel`: for `g : α → β ⊕ Fin m` sending every parameter to a *same-sorted* name —
either a parameter of `β` or one of `m` new leading variables — `WellSorted sα sn ψ` gives
`WellSorted sβ (sortAssem sG sn) (ψ.relabel g)`.  This is the parameter ⇄ variable promotion the
`hasQE_of_hasQE_empty` bridge needs, and (independently) what section 3 needs to move `acl` between
parameter pairs.

`guardsLast_of_GuardTrue` is a fact about the frozen predicate worth knowing: `GuardTrue` implies
`GuardsLast`, so `WellSorted.all`'s `hg` field is redundant given `hj`.  The frozen constructor keeps
both (and that is fine); it means the guard information is carried once, not twice.
-/
/-
The forward half of the parameter bridge: the "shift" that turns the first `n` free
variables into parameters, landing at the empty context `Fin 0` with parameter type
`α ⊕ Fin n`.
-/
import Enc

open FirstOrder FirstOrder.Language
open scoped FirstOrder

namespace SpecialTransformations
namespace Milestone0
namespace ParamBridge

open LRV

variable {α : Type} {n : ℕ}

/-! ### The index maps -/

/-- the index map on variables at depth `k`: the first `n` free variables become the
parameters `Sum.inr`, the remaining `k` stay variables -/
noncomputable def gVar (k : ℕ) (i : Fin (n + k)) : (α ⊕ Fin n) ⊕ Fin k :=
  Sum.elim (fun j => Sum.inl (Sum.inr j)) (fun r => Sum.inr r) (finSumFinEquiv.symm i)

/-- the index map on the whole name space at depth `k` -/
noncomputable def gmap (k : ℕ) : α ⊕ Fin (n + k) → (α ⊕ Fin n) ⊕ Fin k :=
  Sum.elim (fun a => Sum.inl (Sum.inl a)) (gVar k)

/-- **The shift**: replace the first `n` free variables by the parameters `Sum.inr`. -/
noncomputable def shiftAux : (k : ℕ) → LRV.BoundedFormula α (n + k) → LRV.BoundedFormula (α ⊕ Fin n) k
  | _, .falsum => .falsum
  | k, .equal t u => .equal (t.relabel (gmap k)) (u.relabel (gmap k))
  | k, .rel R ts => .rel R (fun i => (ts i).relabel (gmap k))
  | k, .imp a b => .imp (shiftAux k a) (shiftAux k b)
  | k, .all χ => .all (shiftAux (k+1) χ)

/-! ### The index maps, by value -/

theorem gVar_of_lt (k : ℕ) (i : Fin (n + k)) (h : (i : ℕ) < n) :
    gVar (α := α) k i = Sum.inl (Sum.inr ⟨(i : ℕ), h⟩) := by
  have h2 : finSumFinEquiv (Sum.inl (⟨(i:ℕ), h⟩ : Fin n)) = i := by
    rw [finSumFinEquiv_apply_left]
    exact Fin.ext rfl
  have h1 : finSumFinEquiv.symm i = Sum.inl (⟨(i:ℕ), h⟩ : Fin n) :=
    (Equiv.symm_apply_eq _).mpr h2.symm
  simp only [gVar, h1, Sum.elim_inl]

theorem gVar_of_ge (k : ℕ) (i : Fin (n + k)) (h : n ≤ (i : ℕ)) :
    gVar (α := α) k i = Sum.inr (⟨(i:ℕ) - n, by omega⟩ : Fin k) := by
  have h2 : finSumFinEquiv (Sum.inr (⟨(i:ℕ) - n, by omega⟩ : Fin k)) = i := by
    rw [finSumFinEquiv_apply_right]
    exact Fin.ext (by simp only [Fin.val_natAdd]; omega)
  have h1 : finSumFinEquiv.symm i = Sum.inr (⟨(i:ℕ) - n, by omega⟩ : Fin k) :=
    (Equiv.symm_apply_eq _).mpr h2.symm
  simp only [gVar, h1, Sum.elim_inr]

/-! ### Semantics -/

section Semantics
variable {M : Type} [LRV.Structure M]

/-- the tuple corresponding to `(v, xk)` at depth `k` -/
noncomputable def tupleAt (k : ℕ) (v : (α ⊕ Fin n) → M) (xk : Fin k → M) :
    Fin (n + k) → M :=
  Fin.append (fun j => v (Sum.inr j)) xk

theorem tupleAt_apply (k : ℕ) (v : (α ⊕ Fin n) → M) (xk : Fin k → M)
    (i : Fin (n + k)) :
    Sum.elim v xk (gVar k i) = tupleAt k v xk i := by
  rcases h : finSumFinEquiv.symm i with l | r
  · have hi : i = Fin.castAdd k l := by
      rw [← Equiv.apply_symm_apply finSumFinEquiv i, h]
      exact finSumFinEquiv_apply_left l
    subst hi
    simp [gVar, tupleAt]
  · have hi : i = Fin.natAdd n r := by
      rw [← Equiv.apply_symm_apply finSumFinEquiv i, h]
      exact finSumFinEquiv_apply_right r
    subst hi
    simp [gVar, tupleAt]

theorem elim_gmap (k : ℕ) (v : (α ⊕ Fin n) → M) (xk : Fin k → M) :
    (Sum.elim v xk) ∘ gmap k =
      Sum.elim (fun a => v (Sum.inl a)) (fun i => Sum.elim v xk (gVar k i)) := by
  funext x
  rcases x with a | i
  · rfl
  · rfl

theorem snoc_apply_val {γ : Type} {N : ℕ} (p : Fin N → γ) (a : γ) (j : ℕ) (hj : j < N + 1) :
    (Fin.snoc p a : Fin (N + 1) → γ) ⟨j, hj⟩ = if h : j < N then p ⟨j, h⟩ else a := by
  by_cases h : j < N
  · rw [dif_pos h]
    have hi : (⟨j, hj⟩ : Fin (N+1)) = Fin.castSucc ⟨j, h⟩ := by ext; simp
    rw [hi, Fin.snoc_castSucc]
  · rw [dif_neg h]
    have hi : (⟨j, hj⟩ : Fin (N+1)) = Fin.last N := by ext; simp; omega
    rw [hi, Fin.snoc_last]

theorem append_apply_val {γ : Type} {m N : ℕ} (u : Fin m → γ) (w : Fin N → γ) (j : ℕ)
    (hj : j < m + N) :
    Fin.append u w ⟨j, hj⟩ = if h : j < m then u ⟨j, h⟩ else w ⟨j - m, by omega⟩ := by
  by_cases h : j < m
  · rw [dif_pos h]
    have hi : (⟨j, hj⟩ : Fin (m+N)) = Fin.castAdd N ⟨j, h⟩ := by ext; simp
    rw [hi, Fin.append_left]
  · rw [dif_neg h]
    have hi : (⟨j, hj⟩ : Fin (m+N)) = Fin.natAdd m ⟨j - m, by omega⟩ := by
      ext; simp; omega
    rw [hi, Fin.append_right]

theorem tupleAt_snoc (k : ℕ) (v : (α ⊕ Fin n) → M) (xk : Fin k → M) (a : M) :
    tupleAt (k+1) v (Fin.snoc xk a) = (Fin.snoc (tupleAt k v xk) a : Fin (n + (k+1)) → M) := by
  funext i
  obtain ⟨j, hj⟩ := i
  have hlt : j < n + (k + 1) := by omega
  have hsub : j - n < k + 1 := by omega
  have hsub' : j - n < k + 1 := by omega
  have hL : ∀ (h : j < n), tupleAt (k+1) v (Fin.snoc xk a) ⟨j, hj⟩ = v (Sum.inr ⟨j, h⟩) := by
    intro h
    simp only [tupleAt]
    rw [append_apply_val (u := fun j => v (Sum.inr j)) (w := (Fin.snoc xk a : Fin (k+1) → M))
      (j := j) (hj := hj), dif_pos h]
  have hL2 : ∀ (h : ¬ j < n), tupleAt (k+1) v (Fin.snoc xk a) ⟨j, hj⟩
      = (Fin.snoc xk a : Fin (k+1) → M) ⟨j - n, hsub⟩ := by
    intro h
    simp only [tupleAt]
    rw [append_apply_val (u := fun j => v (Sum.inr j)) (w := (Fin.snoc xk a : Fin (k+1) → M))
      (j := j) (hj := hj), dif_neg h]
  have hR : ∀ (h : j < n + k),
      (Fin.snoc (tupleAt k v xk) a : Fin (n + (k+1)) → M) ⟨j, hj⟩
        = tupleAt k v xk ⟨j, h⟩ := by
    intro h
    rw [snoc_apply_val (p := tupleAt k v xk) (a := a) (j := j) (hj := by omega), dif_pos h]
  have hR2 : ¬ j < n + k →
      (Fin.snoc (tupleAt k v xk) a : Fin (n + (k+1)) → M) ⟨j, hj⟩ = a := by
    intro h
    rw [snoc_apply_val (p := tupleAt k v xk) (a := a) (j := j) (hj := by omega), dif_neg h]
  have hM : ∀ (h : j < n + k) (h' : j < n),
      tupleAt k v xk ⟨j, h⟩ = v (Sum.inr ⟨j, h'⟩) := by
    intro h h'
    simp only [tupleAt]
    rw [append_apply_val (u := fun j => v (Sum.inr j)) (w := xk) (j := j) (hj := by omega), dif_pos h']
  have hM2 : ∀ (h : j < n + k) (h' : ¬ j < n) (hjj : j - n < k),
      tupleAt k v xk ⟨j, h⟩ = xk ⟨j - n, hjj⟩ := by
    intro h h' hjj
    simp only [tupleAt]
    rw [append_apply_val (u := fun j => v (Sum.inr j)) (w := xk) (j := j) (hj := by omega), dif_neg h']
  have hS : ∀ (h : ¬ j < n) (h2 : j - n < k),
      (Fin.snoc xk a : Fin (k+1) → M) ⟨j - n, hsub⟩ = xk ⟨j - n, h2⟩ := by
    intro h h2
    rw [snoc_apply_val (p := xk) (a := a) (j := j - n) (hj := by omega), dif_pos h2]
  have hS2 : ∀ (h : ¬ j < n) (h2 : ¬ j - n < k),
      (Fin.snoc xk a : Fin (k+1) → M) ⟨j - n, hsub⟩ = a := by
    intro h h2
    rw [snoc_apply_val (p := xk) (a := a) (j := j - n) (hj := by omega), dif_neg h2]
  by_cases h1 : j < n
  · rw [hL h1, hR (by omega), hM (by omega) h1]
  · by_cases h2 : j - n < k
    · rw [hL2 h1, hR (by omega), hS h1 h2, hM2 (by omega) h1 h2]
    · rw [hL2 h1, hR2 (by omega), hS2 h1 h2]

/-- **Realization of the shift**: at the empty context the parameters `Sum.inr` carry the
values of the first `n` variables. -/
theorem realize_shiftAux :
    ∀ (k : ℕ) (χ : LRV.BoundedFormula α (n + k)) (v : (α ⊕ Fin n) → M) (xk : Fin k → M),
      (shiftAux k χ).Realize v xk ↔
        χ.Realize (fun a => v (Sum.inl a)) (fun i => Sum.elim v xk (gVar k i))
  | k, .falsum, v, xk => by simp only [shiftAux]; exact Iff.rfl
  | k, .equal t u, v, xk => by
      simp only [shiftAux]
      show (t.relabel (gmap k)).realize (Sum.elim v xk) = (u.relabel (gmap k)).realize (Sum.elim v xk)
        ↔ t.realize (Sum.elim (fun a => v (Sum.inl a)) (fun i => Sum.elim v xk (gVar k i)))
          = u.realize (Sum.elim (fun a => v (Sum.inl a)) (fun i => Sum.elim v xk (gVar k i)))
      rw [Term.realize_relabel, Term.realize_relabel, elim_gmap]
  | k, .rel R ts, v, xk => by
      simp only [shiftAux]
      show _root_.FirstOrder.Language.Structure.RelMap R
          (fun i => ((ts i).relabel (gmap k)).realize (Sum.elim v xk))
        ↔ _root_.FirstOrder.Language.Structure.RelMap R
          (fun i => (ts i).realize (Sum.elim (fun a => v (Sum.inl a)) (fun i => Sum.elim v xk (gVar k i))))
      simp only [Term.realize_relabel, elim_gmap]
  | k, .imp a b, v, xk => by
      simp only [shiftAux, BoundedFormula.realize_imp]
      rw [realize_shiftAux k a v xk, realize_shiftAux k b v xk]
  | k, .all χ, v, xk => by
      simp only [shiftAux, BoundedFormula.realize_all]
      refine forall_congr' fun a => ?_
      rw [realize_shiftAux (k+1) χ v (Fin.snoc xk a)]
      have h1 : (fun i => Sum.elim v (Fin.snoc xk a) (gVar (k+1) i))
          = tupleAt (k+1) v (Fin.snoc xk a) := by
        funext i; exact tupleAt_apply (k+1) v (Fin.snoc xk a) i
      have h2 : (Fin.snoc (tupleAt k v xk) a : Fin (n + (k+1)) → M)
          = (Fin.snoc ((fun i : Fin (n+k) => Sum.elim v xk (gVar k i))) a
              : Fin (n + (k+1)) → M) := by
        rw [show (fun i : Fin (n+k) => Sum.elim v xk (gVar k i)) = tupleAt k v xk from by
          funext i; exact (tupleAt_apply k v xk i)]
      rw [h1, tupleAt_snoc, h2]

end Semantics

end ParamBridge
end Milestone0
end SpecialTransformations
