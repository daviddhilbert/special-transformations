/-
**The `VF` sort of a model of the frozen `ACVF` is algebraically closed.**

`QF/VFField.lean` gives the field structure on `Transfer.VFType M`; this file adds
`IsAlgClosed (Transfer.VFType M)`, which is the hypothesis that `rv:root:lift:vf` (Lemma 3.2),
`lift:divisible:hull` (3.5) and `e:transc` (3.7) all carry when they are stated for a valued field.

Ported from `QE/Assembly_val.lean` (namespace `VFAlgClosed`), where it is proved against that file's
own copy of the encoding.  The algebraic content is `Axioms.acfScheme` realised at a root of a monic
irreducible polynomial, via the Horner fold.
-/
import VFValued
import Mathlib.FieldTheory.IsAlgClosed.Basic

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
open SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer

namespace VFAlgClosed

/-- Membership of the algebraic-closedness scheme in `ACVF`. -/
theorem mem_ACVF_vfAlgClosed {s : LRV.Sentence} (h : s ∈ Axioms.vfAlgClosed) :
    s ∈ Axioms.ACVF := by
  simp only [Axioms.ACVF, Axioms.ACVFpaper, Set.mem_union] at *
  tauto

/-! ## 1. The Horner fold and `Polynomial.eval`

`hornerPoly (k := m+1) add mul` is `((x + a_m) * x + a_{m-1}) * x + ⋯ + a_0`, folded over the
list `(List.finRange m).reverse`.  We compute the value of such a fold. -/

/-- `(List.finRange (m+1)).reverse = m :: (m-1) :: ⋯ :: 0`, expressed as the list
`[m-1, …, 0]` pushed forward by `Fin.succ` and with `0` appended. -/
theorem finRange_reverse_succ (m : ℕ) :
    (List.finRange (m + 1)).reverse = (List.finRange m).reverse.map Fin.succ ++ [⟨0, by omega⟩] := by
  rw [List.finRange_succ, List.reverse_cons, List.map_reverse]
  simp

/-- **The value of a Horner fold.**  For an arbitrary initial accumulator `c`,

`((c * r + A_{m-1}) * r + ⋯ + A_0) = c * r^m + ∑_{j<m} A_j r^j`.

The induction has to be stated for a general coefficient family `A : ℕ → R` so that the shift
`A ↦ (fun i => A (i+1))` in the induction step is available. -/
theorem foldl_finRange_reverse {R : Type*} [CommRing R] (A : ℕ → R) (r c : R) (m : ℕ) :
    (List.finRange m).reverse.foldl (fun acc (j : Fin m) => acc * r + A (j : ℕ)) c
      = c * r ^ m + ∑ j : Fin m, A (j : ℕ) * r ^ (j : ℕ) := by
  induction m generalizing c A with
  | zero => simp
  | succ m ih =>
    rw [finRange_reverse_succ, List.foldl_append, List.foldl_map]
    have h1 : List.foldl (fun x y => x * r + A (↑(Fin.succ y))) c (List.finRange m).reverse
        = c * r ^ m + ∑ j : Fin m, A ((j : ℕ) + 1) * r ^ (j : ℕ) :=
      ih (fun i => A (i + 1)) c
    rw [h1, List.foldl_cons, List.foldl_nil]
    have hS : (∑ j : Fin m, A ((j : ℕ) + 1) * r ^ (j : ℕ)) * r
        = ∑ j : Fin m, A ((j : ℕ) + 1) * r ^ ((j : ℕ) + 1) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun j _ => by rw [mul_assoc, ← pow_succ])
    have hshift : (∑ j : Fin m, A ((j : ℕ) + 1) * r ^ ((j : ℕ) + 1)) + A 0
        = ∑ j : Fin m, A (j : ℕ) * r ^ (j : ℕ) + A m * r ^ m := by
      rw [Fin.sum_univ_eq_sum_range (fun i => A (i + 1) * r ^ (i + 1)) m,
        Fin.sum_univ_eq_sum_range (fun i => A i * r ^ i) m,
        show A 0 = A 0 * r ^ 0 from by rw [pow_zero, mul_one],
        ← Finset.sum_range_succ' (fun i => A i * r ^ i) m,
        Finset.sum_range_succ (fun i => A i * r ^ i) m]
    rw [add_mul, mul_assoc, ← pow_succ, hS,
      Fin.sum_univ_castSucc (fun j : Fin (m + 1) => A (j : ℕ) * r ^ (j : ℕ))]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [add_assoc, hshift]

/-- **The Horner value of the monic polynomial with coefficient tuple `A`**:
`x^{m+1} + A_m x^m + ⋯ + A_0`. -/
theorem horner_fold_eq {R : Type*} [CommRing R] (A : ℕ → R) (r : R) (m : ℕ) :
    (List.finRange m).reverse.foldl (fun acc (j : Fin m) => acc * r + A (j : ℕ)) (r + A m)
      = r ^ (m + 1) + ∑ j : Fin (m + 1), A (j : ℕ) * r ^ (j : ℕ) := by
  rw [foldl_finRange_reverse]
  rw [Fin.sum_univ_castSucc (fun j : Fin (m + 1) => A (j : ℕ) * r ^ (j : ℕ))]
  simp only [Fin.val_castSucc, Fin.val_last]
  rw [add_mul, mul_comm r (r ^ m), ← pow_succ]
  ring

/-- **`Polynomial.eval` of a monic polynomial in terms of its coefficients.** -/
theorem eval_monic_eq {R : Type*} [CommRing R] {p : Polynomial R} {m : ℕ} (hp : p.Monic)
    (hd : p.natDegree = m + 1) (r : R) :
    p.eval r = r ^ (m + 1) + ∑ j : Fin (m + 1), p.coeff (j : ℕ) * r ^ (j : ℕ) := by
  have hsum : p.eval r = ∑ i ∈ Finset.range (m + 2), p.coeff i * r ^ i := by
    conv_lhs => rw [Polynomial.as_sum_range_C_mul_X_pow p]
    rw [Polynomial.eval_finsetSum]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    rw [hd]
  rw [hsum, Finset.sum_range_succ,
    Fin.sum_univ_eq_sum_range (fun i => p.coeff i * r ^ i) (m + 1)]
  have hc : p.coeff (m + 1) = 1 := by rw [← hd]; exact hp.coeff_natDegree
  rw [hc, one_mul, add_comm]

end VFAlgClosed

namespace VFAlgClosed

/-! ## 2. The frozen Horner syntax, evaluated

`acfScheme .vf tVFZero tVFAdd tVFMul k` is
`∀ a₀ … a_{k-1} ∈ VF, ∃ x ∈ VF, (hornerPoly tVFAdd tVFMul) = 0`.  We read it semantically. -/

section HornerRealize

variable {M : Type} [LRV.Structure M]

/-- `Fin.snoc` evaluated at a coefficient position. -/
theorem snoc_castSucc_castSucc {k : ℕ} (a : Fin (k + 1) → M) (x : M) (i : Fin k) :
    (Fin.snoc a x : Fin (k + 1 + 1) → M) ⟨i.val, by omega⟩ = a i.castSucc :=
  Fin.snoc_castSucc (α := fun _ : Fin (k + 1 + 1) => M) (x := x) (p := a) (i := i.castSucc)

/-- `Fin.snoc` evaluated at the last coefficient position. -/
theorem snoc_last_coeff {k : ℕ} (a : Fin (k + 1) → M) (x : M) :
    (Fin.snoc a x : Fin (k + 1 + 1) → M) ⟨k, by omega⟩ = a (Fin.last k) :=
  Fin.snoc_castSucc (α := fun _ : Fin (k + 1 + 1) => M) (x := x) (p := a) (i := Fin.last k)

/-- `Fin.snoc` evaluated at the root position. -/
theorem snoc_root {k : ℕ} (a : Fin (k + 1) → M) (x : M) :
    (Fin.snoc a x : Fin (k + 1 + 1) → M) ⟨k + 1, by omega⟩ = x :=
  Fin.snoc_last (α := fun _ : Fin (k + 1 + 1) => M) (x := x) (p := a)

/-- `Fin.snoc` evaluated at its own last position. -/
theorem snoc_last_apply {k : ℕ} (a : Fin k → M) (x : M) :
    (Fin.snoc a x : Fin (k + 1) → M) ⟨k, by omega⟩ = x :=
  Fin.snoc_last (α := fun _ : Fin (k + 1) => M) (x := x) (p := a)

/-- **The value of the frozen Horner term** at a coefficient tuple `a` and a root candidate `x`. -/
theorem hornerPoly_realize {m : ℕ} (a : Fin (m + 1) → M) (x : M) :
    (hornerPoly (k := m + 1) tVFAdd tVFMul).realize
        (Sum.elim (default : Empty → M) (Fin.snoc a x : Fin (m + 1 + 1) → M))
      = (List.finRange m).reverse.foldl
          (fun acc (i : Fin m) => iVFAdd (iVFMul acc x) (a i.castSucc))
          (iVFAdd x (a (Fin.last m))) := by
  rw [hornerPoly]
  have hstep : ∀ (acc : Tm (m + 1 + 1)) (i : Fin m),
      (tVFAdd (tVFMul acc (tv (m + 1) (by omega))) (tv i.val (by omega))).realize
          (Sum.elim (default : Empty → M) (Fin.snoc a x : Fin (m + 1 + 1) → M))
        = iVFAdd (iVFMul ((acc).realize
            (Sum.elim (default : Empty → M) (Fin.snoc a x : Fin (m + 1 + 1) → M))) x)
            (a i.castSucc) := by
    intro acc i
    rw [realize_tVFAdd, realize_tVFMul,
      show (tv (m + 1) (by omega) : Tm (m + 1 + 1)).realize
          (Sum.elim (default : Empty → M) (Fin.snoc a x : Fin (m + 1 + 1) → M))
          = (Fin.snoc a x : Fin (m + 1 + 1) → M) ⟨m + 1, by omega⟩ from rfl,
      show (tv i.val (by omega) : Tm (m + 1 + 1)).realize
          (Sum.elim (default : Empty → M) (Fin.snoc a x : Fin (m + 1 + 1) → M))
          = (Fin.snoc a x : Fin (m + 1 + 1) → M) ⟨i.val, by omega⟩ from rfl,
      snoc_root a x, snoc_castSucc_castSucc a x i]
  have hinit : (tVFAdd (tv (m + 1) (by omega)) (tv m (by omega))).realize
      (Sum.elim (default : Empty → M) (Fin.snoc a x : Fin (m + 1 + 1) → M))
      = iVFAdd x (a (Fin.last m)) := by
    rw [realize_tVFAdd,
      show (tv (m + 1) (by omega) : Tm (m + 1 + 1)).realize
          (Sum.elim (default : Empty → M) (Fin.snoc a x : Fin (m + 1 + 1) → M))
          = (Fin.snoc a x : Fin (m + 1 + 1) → M) ⟨m + 1, by omega⟩ from rfl,
      show (tv m (by omega) : Tm (m + 1 + 1)).realize
          (Sum.elim (default : Empty → M) (Fin.snoc a x : Fin (m + 1 + 1) → M))
          = (Fin.snoc a x : Fin (m + 1 + 1) → M) ⟨m, by omega⟩ from rfl,
      snoc_root a x, snoc_last_coeff a x]
  have h := List.foldl_hom
    (fun t : Tm (m + 1 + 1) => t.realize
      (Sum.elim (default : Empty → M) (Fin.snoc a x : Fin (m + 1 + 1) → M)))
    (g₁ := fun (acc : Tm (m + 1 + 1)) (i : Fin m) =>
      tVFAdd (tVFMul acc (tv (m + 1) (by omega))) (tv i.val (by omega)))
    (g₂ := fun (acc : M) (i : Fin m) => iVFAdd (iVFMul acc x) (a i.castSucc))
    (l := (List.finRange m).reverse)
    (init := tVFAdd (tv (m + 1) (by omega)) (tv m (by omega)))
    (fun acc i => (hstep acc i).symm)
  rw [hinit] at h
  exact h.symm

/-- **The algebraic-closedness scheme of the frozen encoding, semantically.** -/
theorem acfScheme_realize {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {k : ℕ}
    (hk : 1 ≤ k) (a : Fin k → M) (ha : ∀ i, iVF (a i)) :
    ∃ x : M, iVF x ∧ (hornerPoly (k := k) tVFAdd tVFMul).realize
        (Sum.elim (default : Empty → M) (Fin.snoc a x)) = iVFZero := by
  have hmem : allSorted (fun _ : Fin k => SortTag.vf)
      (exSorted SortTag.vf (pEq (hornerPoly tVFAdd tVFMul) tVFZero)) ∈ Axioms.ACVF :=
    mem_ACVF_vfAlgClosed ⟨k, hk, rfl⟩
  have h := allSorted_realize hM hmem a ha
  simp only [exSorted, BoundedFormula.realize_ex, BoundedFormula.realize_inf, sortPred_realize,
    pEq, BoundedFormula.realize_bdEqual, realize_tVFZero, realize_tv] at h
  obtain ⟨x, hx, hxz⟩ := h
  exact ⟨x, snoc_last_apply a x ▸ hx, hxz⟩

end HornerRealize

/-! ## 3. The `VF` sort as a field: the ring operations are the frozen symbols -/

section VFVal

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

@[simp] theorem vf_add_val (u v : VFType (M := M)) : (u + v).1 = iVFAdd u.1 v.1 := rfl

@[simp] theorem vf_mul_val (u v : VFType (M := M)) : (u * v).1 = iVFMul u.1 v.1 := rfl

@[simp] theorem vf_zero_val : (0 : VFType (M := M)).1 = iVFZero := rfl

/-- **The Horner fold computed in `VFType` agrees, on values, with the frozen fold in `M`.** -/
theorem fold_val_eq {m : ℕ} (a : Fin (m + 1) → VFType (M := M)) (x : VFType (M := M)) :
    ((List.finRange m).reverse.foldl
        (fun acc (i : Fin m) => acc * x + a i.castSucc) (x + a (Fin.last m))).1
      = (List.finRange m).reverse.foldl
          (fun acc (i : Fin m) => iVFAdd (iVFMul acc x.1) (a i.castSucc).1)
          (iVFAdd x.1 (a (Fin.last m)).1) := by
  refine Eq.trans ?_ (List.foldl_hom (Subtype.val)
    (g₁ := fun (acc : VFType (M := M)) (i : Fin m) => acc * x + a i.castSucc)
    (g₂ := fun (acc : M) (i : Fin m) => iVFAdd (iVFMul acc x.1) (a i.castSucc).1)
    (l := (List.finRange m).reverse)
    (init := x + a (Fin.last m)) (fun acc i => rfl)).symm
  rfl

end VFVal

/-! ## 4. `IsAlgClosed` of the `VF` sort -/

section Main

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- **The `VF` sort of a model of the frozen `ACVF` is an algebraically closed field.** -/
theorem isAlgClosed_vfType :
    @IsAlgClosed (VFType (M := M)) (vfFieldOfModel (M := M) (hM := hM)) := by
  letI : Field (VFType (M := M)) := vfFieldOfModel (M := M) (hM := hM)
  refine IsAlgClosed.of_exists_root _ ?_
  intro p hpm hpi
  have hdeg : 0 < p.natDegree :=
    Polynomial.natDegree_pos_iff_degree_pos.2 (Polynomial.degree_pos_of_irreducible hpi)
  obtain ⟨m, hm⟩ : ∃ m, p.natDegree = m + 1 := ⟨p.natDegree - 1, by omega⟩
  -- the coefficient tuple, in `M` and in `VFType`
  obtain ⟨x, hx, hxeq⟩ := acfScheme_realize (M := M) hM (k := m + 1) (by omega)
    (fun i => (p.coeff (i : ℕ)).1) (fun i => (p.coeff (i : ℕ)).2)
  set x' : VFType (M := M) := ⟨x, hx⟩ with hx'def
  have hxeq' : (List.finRange m).reverse.foldl
      (fun acc (i : Fin m) => iVFAdd (iVFMul acc x) ((p.coeff (i.castSucc : ℕ)).1))
      (iVFAdd x ((p.coeff (Fin.last m : ℕ)).1)) = iVFZero :=
    (hornerPoly_realize (fun i => (p.coeff (i : ℕ)).1) x).symm.trans hxeq
  refine ⟨x', ?_⟩
  have hK : (List.finRange m).reverse.foldl
      (fun acc (i : Fin m) => acc * x' + p.coeff (i.castSucc : ℕ)) (x' + p.coeff m) = 0 := by
    apply Subtype.ext
    exact (fold_val_eq (a := fun i => p.coeff (i : ℕ)) (x := x')).trans hxeq'
  refine Eq.trans (eval_monic_eq hpm hm x') ?_
  refine Eq.trans (horner_fold_eq (fun i => p.coeff i) x' m).symm ?_
  exact hK

end Main

end VFAlgClosed
