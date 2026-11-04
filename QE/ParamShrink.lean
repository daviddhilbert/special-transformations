/-
**The shrink gadget** — from swarm `smw1bwjo2` m2, re-based on the repaired `Enc`, verified here
(compiled, 0 errors, no `sorry`).  `shrinkAux V k : BoundedFormula Empty (m + (n + k)) →
BoundedFormula α (n + k)` turns a formula whose leading variables are named by `V : Fin m → α` back
into a formula over the parameters `α`, and `realize_shrinkAux` is its semantics.  This is the
inverse of the parameter→variable promotion in `ParamBridgeRelabel.lean`; together they are the two
halves of `ParamBridge.hasQE_of_hasQE_empty`.
-/
import Enc

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace W4

variable {α : Type} {m n : ℕ}

/-! ### Turning the first `m` free variables into parameters -/

/-- the index map on variables at depth `k` -/
noncomputable def gVar (V : Fin m → α) (k : ℕ) (i : Fin (m + (n + k))) : α ⊕ Fin (n + k) :=
  Sum.elim (fun j => Sum.inl (V j)) (fun r => Sum.inr r) (finSumFinEquiv.symm i)

/-- the index map on the whole name space at depth `k` -/
noncomputable def gmap (V : Fin m → α) (k : ℕ) :
    Empty ⊕ Fin (m + (n + k)) → α ⊕ Fin (n + k) :=
  Sum.elim Empty.elim (gVar V k)

/-- **The shrink**: replace the first `m` free variables by the parameters `V`. -/
noncomputable def shrinkAux (V : Fin m → α) :
    (k : ℕ) → LRV.BoundedFormula Empty (m + (n + k)) → LRV.BoundedFormula α (n + k)
  | _, .falsum => .falsum
  | k, .equal t u => .equal (t.relabel (gmap V k)) (u.relabel (gmap V k))
  | k, .rel R ts => .rel R (fun i => (ts i).relabel (gmap V k))
  | k, .imp a b => .imp (shrinkAux V k a) (shrinkAux V k b)
  | k, .all χ => .all (shrinkAux V (k+1) χ)

section Semantics
variable {M : Type} [LRV.Structure M]

/-- the tuple corresponding to `(v, xk)` at depth `k` -/
noncomputable def tupleAt (V : Fin m → α) (k : ℕ) (v : α → M) (xk : Fin (n + k) → M) :
    Fin (m + (n + k)) → M :=
  Fin.append (fun j => v (V j)) xk

theorem tupleAt_apply (V : Fin m → α) (k : ℕ) (v : α → M) (xk : Fin (n + k) → M)
    (i : Fin (m + (n + k))) :
    Sum.elim v xk (gVar V k i) = tupleAt V k v xk i := by
  rcases h : finSumFinEquiv.symm i with l | r
  · have hi : i = Fin.castAdd (n + k) l := by
      rw [← Equiv.apply_symm_apply finSumFinEquiv i, h]
      exact finSumFinEquiv_apply_left l
    subst hi
    simp [gVar, tupleAt]
  · have hi : i = Fin.natAdd m r := by
      rw [← Equiv.apply_symm_apply finSumFinEquiv i, h]
      exact finSumFinEquiv_apply_right r
    subst hi
    simp [gVar, tupleAt]

theorem elim_gmap (V : Fin m → α) (k : ℕ) (v : α → M) (xk : Fin (n + k) → M) :
    (Sum.elim v xk) ∘ gmap V k =
      Sum.elim (fun e : Empty => e.elim) (fun i => Sum.elim v xk (gVar V k i)) := by
  funext x
  rcases x with e | i
  · exact e.elim
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

theorem tupleAt_snoc (V : Fin m → α) (k : ℕ) (v : α → M) (xk : Fin (n + k) → M) (a : M) :
    tupleAt V (k+1) v (Fin.snoc xk a) = (Fin.snoc (tupleAt V k v xk) a : Fin (m + (n + (k+1))) → M) := by
  funext i
  obtain ⟨j, hj⟩ := i
  have hlt : j < m + (n + k + 1) := by omega
  have hsub : j - m < n + (k+1) := by omega
  have hsub' : j - m < n + k + 1 := by omega
  have hL : ∀ (h : j < m), tupleAt V (k+1) v (Fin.snoc xk a) ⟨j, hj⟩ = v (V ⟨j, h⟩) := by
    intro h
    simp only [tupleAt]
    rw [append_apply_val (u := fun j => v (V j)) (w := (Fin.snoc xk a : Fin (n+(k+1)) → M))
      (j := j) (hj := hj), dif_pos h]
  have hL2 : ∀ (h : ¬ j < m), tupleAt V (k+1) v (Fin.snoc xk a) ⟨j, hj⟩
      = (Fin.snoc xk a : Fin (n + (k+1)) → M) ⟨j - m, hsub⟩ := by
    intro h
    simp only [tupleAt]
    rw [append_apply_val (u := fun j => v (V j)) (w := (Fin.snoc xk a : Fin (n+(k+1)) → M))
      (j := j) (hj := hj), dif_neg h]
  have hR : ∀ (h : j < m + (n + k)),
      (Fin.snoc (tupleAt V k v xk) a : Fin (m + (n + (k+1))) → M) ⟨j, hj⟩
        = tupleAt V k v xk ⟨j, h⟩ := by
    intro h
    rw [snoc_apply_val (p := tupleAt V k v xk) (a := a) (j := j) (hj := by omega), dif_pos h]
  have hR2 : ¬ j < m + (n + k) →
      (Fin.snoc (tupleAt V k v xk) a : Fin (m + (n + (k+1))) → M) ⟨j, hj⟩ = a := by
    intro h
    rw [snoc_apply_val (p := tupleAt V k v xk) (a := a) (j := j) (hj := by omega), dif_neg h]
  have hM : ∀ (h : j < m + (n + k)) (h' : j < m),
      tupleAt V k v xk ⟨j, h⟩ = v (V ⟨j, h'⟩) := by
    intro h h'
    simp only [tupleAt]
    rw [append_apply_val (u := fun j => v (V j)) (w := xk) (j := j) (hj := by omega), dif_pos h']
  have hM2 : ∀ (h : j < m + (n + k)) (h' : ¬ j < m) (hjj : j - m < n + k),
      tupleAt V k v xk ⟨j, h⟩ = xk ⟨j - m, hjj⟩ := by
    intro h h' hjj
    simp only [tupleAt]
    rw [append_apply_val (u := fun j => v (V j)) (w := xk) (j := j) (hj := by omega), dif_neg h']
  have hS : ∀ (h : ¬ j < m) (h2 : j - m < n + k),
      (Fin.snoc xk a : Fin (n + (k+1)) → M) ⟨j - m, hsub⟩ = xk ⟨j - m, h2⟩ := by
    intro h h2
    rw [snoc_apply_val (p := xk) (a := a) (j := j - m) (hj := by omega), dif_pos h2]
  have hS2 : ∀ (h : ¬ j < m) (h2 : ¬ j - m < n + k),
      (Fin.snoc xk a : Fin (n + (k+1)) → M) ⟨j - m, hsub⟩ = a := by
    intro h h2
    rw [snoc_apply_val (p := xk) (a := a) (j := j - m) (hj := by omega), dif_neg h2]
  by_cases h1 : j < m
  · rw [hL h1, hR (by omega), hM (by omega) h1]
  · by_cases h2 : j - m < n + k
    · rw [hL2 h1, hR (by omega), hS h1 h2, hM2 (by omega) h1 h2]
    · rw [hL2 h1, hR2 (by omega), hS2 h1 h2]

theorem realize_shrinkAux (V : Fin m → α) :
    ∀ (k : ℕ) (χ : LRV.BoundedFormula Empty (m + (n + k))) (v : α → M)
      (xk : Fin (n + k) → M),
      (shrinkAux V k χ).Realize v xk ↔
        χ.Realize (fun e : Empty => e.elim) (fun i => Sum.elim v xk (gVar V k i))
  | k, .falsum, v, xk => by simp only [shrinkAux]; exact Iff.rfl
  | k, .equal t u, v, xk => by
      simp only [shrinkAux]
      show (t.relabel (gmap V k)).realize (Sum.elim v xk) = (u.relabel (gmap V k)).realize (Sum.elim v xk)
        ↔ t.realize (Sum.elim (fun e : Empty => e.elim) (fun i => Sum.elim v xk (gVar V k i)))
          = u.realize (Sum.elim (fun e : Empty => e.elim) (fun i => Sum.elim v xk (gVar V k i)))
      rw [Term.realize_relabel, Term.realize_relabel, elim_gmap]
  | k, .rel R ts, v, xk => by
      simp only [shrinkAux]
      show _root_.FirstOrder.Language.Structure.RelMap R
          (fun i => ((ts i).relabel (gmap V k)).realize (Sum.elim v xk))
        ↔ _root_.FirstOrder.Language.Structure.RelMap R
          (fun i => (ts i).realize (Sum.elim (fun e : Empty => e.elim) (fun i => Sum.elim v xk (gVar V k i))))
      simp only [Term.realize_relabel, elim_gmap]
  | k, .imp a b, v, xk => by
      simp only [shrinkAux, BoundedFormula.realize_imp]
      rw [realize_shrinkAux V k a v xk, realize_shrinkAux V k b v xk]
  | k, .all χ, v, xk => by
      simp only [shrinkAux, BoundedFormula.realize_all]
      refine forall_congr' fun a => ?_
      rw [realize_shrinkAux V (k+1) χ v (Fin.snoc xk a)]
      have h1 : (fun i => Sum.elim v (Fin.snoc xk a) (gVar V (k+1) i))
          = tupleAt V (k+1) v (Fin.snoc xk a) := by
        funext i; exact tupleAt_apply V (k+1) v (Fin.snoc xk a) i
      have h2 : (Fin.snoc (tupleAt V k v xk) a : Fin (m + (n + (k+1))) → M)
          = (Fin.snoc ((fun i : Fin (m + (n+k)) => Sum.elim v xk (gVar V k i))) a
              : Fin (m + (n + (k+1))) → M) := by
        rw [show (fun i : Fin (m + (n+k)) => Sum.elim v xk (gVar V k i)) = tupleAt V k v xk from by
          funext i; exact (tupleAt_apply V k v xk i)]
      rw [h1, tupleAt_snoc, h2]

end Semantics

end W4
