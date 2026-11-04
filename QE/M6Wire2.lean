/-
**The residue chain is a function of residue values.**

`M6Wire.rvChain F b I i₀` is the `iKAdd` chain of the terms `rv (F.coeff i * b ^ i)`.  Since
`iKAdd`, `iRVMul` and `iRv` are all *function* symbols, this chain can be pushed along any
`LRV`-monomorphism (`M6Wire.map_kFold`).  What is still missing for that is to see that the chain
mentions `b` only through `rv b`: `rv (a * b ^ n) = iRVMul (rv a) ((rv b) ^ n)`, where the power on
the right is the iterated `iRVMul` (`iRVPow`).  That is `iRv_mul_pow`, and `rvChain_factors` puts
the chain into that shape.

Why it matters for Lemma 3.4: the paper's `e ∈ VF(M)` has `rv e ∈ RV(S)`, while `e ∉ S`, so `f`
does *not* act on `e` — but it does act on `rv e`, and after `rvChain_factors` that is all the chain
needs.  So the `M`-side residue equation produced by `M6Wire.rvFold_zero_of_isRoot` is a value
`f` can carry to `N`.

`#print axioms` of every theorem is `{propext, Classical.choice, Quot.sound}`.
-/
import M6Wire

set_option linter.unusedSectionVars false

open FirstOrder FirstOrder.Language
open Polynomial
open SpecialTransformations.Milestone0
open SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Milestone0.M6Wire2

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- Iterated `iRVMul`: the `n`-th power on the `RV` sort. -/
def iRVPow (a : M) : ℕ → M
  | 0 => iRVOne
  | n + 1 => iRVMul (iRVPow a n) a

/-- **`rv` of a power is the `RV`-power**: `rv(b ^ n) = (rv b) ^ n`. -/
theorem iRv_pow {b : Transfer.VFType (M := M)} (n : ℕ) :
    iRv ((b ^ n)).1 = iRVPow (iRv b.1) n := by
  induction n with
  | zero =>
      show iRv ((b ^ 0 : Transfer.VFType (M := M))).1 = iRVOne
      rw [pow_zero]
      exact RVCalc.rv_one hM
  | succ n ih =>
      show iRv ((b ^ (n + 1) : Transfer.VFType (M := M))).1
        = iRVMul (iRVPow (iRv b.1) n) (iRv b.1)
      have hp : (b ^ (n + 1) : Transfer.VFType (M := M)) = b ^ n * b := pow_succ b n
      have hmul : iRv ((b ^ (n + 1) : Transfer.VFType (M := M))).1
          = iRv (iVFMul ((b ^ n)).1 b.1) :=
        congrArg (fun t : Transfer.VFType (M := M) => iRv t.1) hp
      exact hmul.trans ((Transfer.rv_mul_hom_of_model hM (b ^ n).2 b.2).trans
        (congrArg (fun t => iRVMul t (iRv b.1)) ih))

/-- **`rv` of `a * b ^ n`**: `iRVMul (rv a) ((rv b) ^ n)`. -/
theorem iRv_mul_pow {a b : Transfer.VFType (M := M)} (n : ℕ) :
    iRv ((a * b ^ n)).1 = iRVMul (iRv a.1) (iRVPow (iRv b.1) n) :=
  (Transfer.rv_mul_hom_of_model hM a.2 (b ^ n).2).trans
    (congrArg (fun t => iRVMul (iRv a.1) t) (iRv_pow n))

/-- **The chain depends only on residues.**  `rvChain F b I i₀` is a fold of `iRVMul` and `iRVPow`
of `rv (F.coeff i)` and `rv b` alone — no other occurrence of `b`, and no `VF`-arithmetic. -/
theorem rvChain_factors (F : (Transfer.VFType (M := M))[X]) (b : Transfer.VFType (M := M))
    (I : Finset ℕ) (i₀ : ℕ) :
    M6Wire.rvChain F b I i₀
      = M6Wire.kFold (iRVMul (iRv (F.coeff i₀).1) (iRVPow (iRv b.1) i₀))
          (((I.erase i₀).sort (· ≤ ·)).map
            (fun i => iRVMul (iRv (F.coeff i).1) (iRVPow (iRv b.1) i))) := by
  show M6Wire.kFold (iRv ((F.coeff i₀ * b ^ i₀)).1)
      (((I.erase i₀).sort (· ≤ ·)).map (fun i => iRv ((F.coeff i * b ^ i)).1)) = _
  rw [iRv_mul_pow]
  exact congrArg (M6Wire.kFold (iRVMul (iRv (F.coeff i₀).1) (iRVPow (iRv b.1) i₀)))
    (List.map_congr_left (fun i _ => iRv_mul_pow i))

/-- Immediate corollary: the chain is unchanged by replacing `b` by an element with the same
residue.  (This is what lets a consumer pick *any* representative of the class `rv b`.) -/
theorem rvChain_eq_of_rv_eq (F : (Transfer.VFType (M := M))[X]) (I : Finset ℕ) (i₀ : ℕ)
    {b b' : Transfer.VFType (M := M)} (h : iRv b.1 = iRv b'.1) :
    M6Wire.rvChain F b I i₀ = M6Wire.rvChain F b' I i₀ := by
  rw [rvChain_factors, rvChain_factors, h]


/-! ## 4. Residue arithmetic commutes with `LRV`-monomorphisms

The chain of `rvChain_factors` is a fold of `iRVPow` and `iRVMul` on the residue values, so a
consumer needs exactly these: on a substructure `S`, the `RV`-operations are `S`'s own operations,
and `f : S ↪[LRV] N` commutes with them because they are function symbols.  Together with
`M6Wire.map_kFold` this says the chain is a term of `RV(S)`, which is what makes it transfer. -/

/-- `iRVOne` lies in every substructure (it is a constant). -/
theorem rvOne_mem {N : Type} [LRV.Structure N] (S : LRV.Substructure N) :
    (iRVOne (M := N)) ∈ S :=
  S.fun_mem Fn.rvOne (fun i => i.elim0) (fun i => i.elim0)

section Commute

variable {N : Type} [LRV.Structure N]

/-- `iRVOne` commutes with an `LRV`-embedding of substructures. -/
theorem map_iRVOne (S : LRV.Substructure M) (f : S ↪[LRV] N) :
    (f (iRVOne : S) : N) = (iRVOne : N) := by
  have h1 := f.map_fun Fn.rvOne (fun i => i.elim0)
  have h2 : (⇑f ∘ (fun i : Fin 0 => i.elim0)) = (fun i : Fin 0 => i.elim0) := by
    funext i; exact i.elim0
  rw [h2] at h1
  exact h1

/-- `iRVMul` commutes with an `LRV`-embedding of substructures. -/
theorem map_iRVMul (S : LRV.Substructure M) (f : S ↪[LRV] N) (a b : S) :
    (f (iRVMul a b) : N) = iRVMul (f a) (f b) := by
  have h1 := f.map_fun Fn.rvMul ![a, b]
  have h2 : (⇑f ∘ ![a, b]) = ![f a, f b] := by funext i; fin_cases i <;> rfl
  rw [h2] at h1
  exact h1

/-- `iKAdd` commutes with an `LRV`-embedding of substructures. -/
theorem map_iKAdd (S : LRV.Substructure M) (f : S ↪[LRV] N) (a b : S) :
    (f (iKAdd a b) : N) = iKAdd (f a) (f b) := by
  have h1 := f.map_fun Fn.kAdd ![a, b]
  have h2 : (⇑f ∘ ![a, b]) = ![f a, f b] := by funext i; fin_cases i <;> rfl
  rw [h2] at h1
  exact h1

/-- `iRv` commutes with an `LRV`-embedding of substructures. -/
theorem map_iRv (S : LRV.Substructure M) (f : S ↪[LRV] N) (a : S) :
    (f (iRv a) : N) = iRv (f a) := by
  have h1 := f.map_fun Fn.rvMap ![a]
  have h2 : (⇑f ∘ ![a]) = ![f a] := by funext i; fin_cases i; rfl
  rw [h2] at h1
  exact h1

/-- `iRVPow` commutes with an `LRV`-embedding of substructures. -/
theorem map_iRVPow (S : LRV.Substructure M) (f : S ↪[LRV] N) (a : S) (n : ℕ) :
    (f (iRVPow a n) : N) = iRVPow (f a) n := by
  induction n with
  | zero =>
      show (f (iRVOne : S) : N) = (iRVOne : N)
      exact map_iRVOne S f
  | succ n ih =>
      show (f (iRVMul (iRVPow a n) a) : N) = iRVMul (iRVPow (f a) n) (f a)
      rw [map_iRVMul, ih]

end Commute

end SpecialTransformations.Milestone0.M6Wire2

#print axioms SpecialTransformations.Milestone0.M6Wire2.iRv_pow
#print axioms SpecialTransformations.Milestone0.M6Wire2.iRv_mul_pow
#print axioms SpecialTransformations.Milestone0.M6Wire2.rvChain_factors
#print axioms SpecialTransformations.Milestone0.M6Wire2.rvChain_eq_of_rv_eq
#print axioms SpecialTransformations.Milestone0.M6Wire2.map_iRVMul
#print axioms SpecialTransformations.Milestone0.M6Wire2.map_iRVPow
#print axioms SpecialTransformations.Milestone0.M6Wire.map_kFold
