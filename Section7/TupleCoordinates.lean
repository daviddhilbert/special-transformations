module

public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Data.Fin.Tuple.Basic

@[expose] public section

/-! Finite coordinate blocks used by the polynomial and definability arguments. -/

namespace SpecialTransformations.Section7

def productTuple {X : Type*} {m n : ℕ} (a : Fin m → X) (b : Fin n → X) :
    Fin (m + n) → X :=
  Sum.elim a b ∘ (finSumFinEquiv : Fin m ⊕ Fin n ≃ Fin (m + n)).symm

def productLeft (m n : ℕ) : Fin m ↪ Fin (m + n) :=
  ⟨fun i => finSumFinEquiv (.inl i), finSumFinEquiv.injective.comp Sum.inl_injective⟩

def productRight (m n : ℕ) : Fin n ↪ Fin (m + n) :=
  ⟨fun i => finSumFinEquiv (.inr i), finSumFinEquiv.injective.comp Sum.inr_injective⟩

@[simp] theorem productTuple_left {X : Type*} {m n : ℕ} (a : Fin m → X) (b : Fin n → X)
    (i : Fin m) : productTuple a b (productLeft m n i) = a i := by
  simp [productTuple, productLeft]

@[simp] theorem productTuple_right {X : Type*} {m n : ℕ} (a : Fin m → X) (b : Fin n → X)
    (i : Fin n) : productTuple a b (productRight m n i) = b i := by
  simp [productTuple, productRight]

theorem productLeft_ne_right {m n : ℕ} (i : Fin m) (j : Fin n) :
    productLeft m n i ≠ productRight m n j := by
  intro h
  have heq : (Sum.inl i : Fin m ⊕ Fin n) = Sum.inr j := finSumFinEquiv.injective h
  cases heq

theorem productTuple_ext {X : Type*} {m n : ℕ} {a b : Fin (m + n) → X}
    (hl : ∀ i, a (productLeft m n i) = b (productLeft m n i))
    (hr : ∀ j, a (productRight m n j) = b (productRight m n j)) : a = b := by
  funext k
  obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective k
  cases s with
  | inl i => exact hl i
  | inr j => exact hr j

theorem extend_productLeft {X : Type*} {m n : ℕ}
    (a a' : Fin m → X) (b : Fin n → X) :
    Function.extend (productLeft m n) a (productTuple a' b) = productTuple a b := by
  apply productTuple_ext
  · intro i
    rw [(productLeft m n).injective.extend_apply, productTuple_left]
  · intro j
    rw [Function.extend_apply' _ _ _ (fun ⟨i, hi⟩ => productLeft_ne_right i j hi)]
    simp

theorem extend_productRight {X : Type*} {m n : ℕ}
    (a : Fin m → X) (b b' : Fin n → X) :
    Function.extend (productRight m n) b (productTuple a b') = productTuple a b := by
  apply productTuple_ext
  · intro i
    rw [Function.extend_apply' _ _ _ (fun ⟨j, hj⟩ => productLeft_ne_right i j hj.symm)]
    simp
  · intro j
    rw [(productRight m n).injective.extend_apply, productTuple_right]

end SpecialTransformations.Section7
