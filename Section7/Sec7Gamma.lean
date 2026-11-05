/-
# Section 7, `def:gamma:poly` (paper.tex 1480): `γ`-polynomials and residue roots

This file formalises the *notion* of Definition 7.1 of Yin, "Special transformations in
algebraically closed valued fields" (arXiv:1006.2467), over a Mathlib valued field, and proves
the one assertion that the definition makes in passing and that every later argument in Section 7
consumes: **"some (hence all)"** — the truth of `vv (F(ā)) > α` does not depend on the choice of
representative `ā` in the `rv`-fibre `rv⁻¹(t̄)`.  Nothing here is assumed and nothing is
`sorry`-ed: the file supplies and validates the notions of Definition 7.1 (the notion itself, its
"some (hence all)", and the well-definedness of *simple* common residue roots on an `rv`-fibre),
proves the `n = 1` case of the paper's Jacobian residue-value computation, and records exactly one
open statement, `JacobianResidueValue`, which is that computation in general.  Lemma 7.2
(`hensel:lemma`) consumes these notions; its proof is not attempted here.

## The bridge from the paper's notation to `Mathlib.Valuation`

The paper writes `\vv` multiplicatively: `\vv(xy) = \vv x · \vv y`,
`\vv(x+y) ≤ max (\vv x) (\vv y)`, `\vv 0 = ∞`, and `𝒪 = {x : \vv x ≤ 1}`.  Mathlib's
`Valuation K Γ₀` (`Γ₀` a `LinearOrderedCommMonoidWithZero`) has exactly the same two laws,
with `v 0 = 0` the *bottom* of `Γ₀` (Mathlib's `map_add_le_max'`) and `v 1 = 1`; its
valuation ring is `{x : v x ≤ 1}`.  So

* the paper's `\vv` is Mathlib's `v` with `∞ ↦ 0`, written with the same order;
* the paper's `γ ∈ Γ` corresponds to `γ : Γ₀` with `γ ≠ 0`;
* the paper's `vv(F(ā)) > α` (a *strict* comparison, "the value of `F` is larger") is
  `v (F ā) < α` in Mathlib's order, `α ≠ 0`.  All statements below are written on the Mathlib
  side, and each carries the paper's sentence, in the paper's notation, in its docstring.

`Γ` is assumed nontrivial (`[Nontrivial Γ₀]`), as throughout the paper (`Γ(S)` nontrivial);
it is what makes `0 < 1` available, and with it `Valuation.zero_iff` (`v x = 0 ↔ x = 0`).

`rv⁻¹(t)` on the `VF`-sort is the fibre of the residue map `rv = vrv`, i.e. the set
`{b : v (b - t) < v t}` (`rvFibre` below; the frozen `L_RV` encoding's `rvBall` is the same set,
and `Milestone0/DECISION.md` records that `Mathlib.Valuation`'s order is the opposite of the
`RV`-order used in the encoding, which is why the comparison reverses sign in the statements).
-/
import Mathlib

namespace Sec7Gamma

open MvPolynomial

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommMonoidWithZero Γ₀] [Nontrivial Γ₀]

/-! ## Part 1 — the paper's `\vv` and `𝒪`, and the `rv`-fibre on the `VF`-sort -/

section Bridge

variable (v : Valuation K Γ₀)

/-- The paper's ultrametric inequality `\vv(x+y) ≤ max (\vv x, \vv y)` (`\vv` multiplicative). -/
theorem gamma_add_le_max (x y : K) : v (x + y) ≤ max (v x) (v y) := v.map_add x y

/-- The paper's multiplicativity `\vv(xy) = \vv x · \vv y`. -/
theorem gamma_mul (x y : K) : v (x * y) = v x * v y := v.map_mul x y

/-- The paper's `\vv 0 = ∞`: the top element of `Γ ∪ {∞}`.  It is Mathlib's bottom `0`. -/
theorem gamma_zero : v (0 : K) = 0 := v.map_zero

/-- The paper's `\vv x = ∞ ↔ x = 0`. -/
theorem gamma_eq_zero_iff (x : K) : v x = 0 ↔ x = 0 := v.zero_iff

/-- The paper's valuation ring `𝒪 = {x : \vv x ≤ 1}`, as a subring of `VF`:
`0, 1 ∈ 𝒪`, and `𝒪` is closed under `+`, `−`, `·` — the two arithmetic closures are exactly
`gamma_add_le_max` and `gamma_mul`. -/
def integralSubring : Subring K where
  carrier := {x : K | v x ≤ 1}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := by
    intro x y hx hy
    exact (v.map_add x y).trans (max_le hx hy)
  neg_mem' := by
    intro x hx
    simpa using hx
  mul_mem' := by
    intro x y hx hy
    show v (x * y) ≤ 1
    rw [Valuation.map_mul]
    exact (mul_le_mul' hx hy).trans_eq (one_mul 1)

/-- The paper's maximal ideal `𝔪 = {x : \vv x < 1}`, as an ideal of `𝒪`: closed under `+` and
under multiplication by any element of `𝒪`. -/
def maxIdeal : Ideal (integralSubring v) where
  carrier := {x : integralSubring v | v (x : K) < 1}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    exact (v.map_add (x : K) (y : K)).trans_lt (max_lt hx hy)
  smul_mem' := by
    intro c x hx
    have hc : v (c : K) ≤ 1 := c.2
    show v ((c : K) * (x : K)) < 1
    rw [Valuation.map_mul]
    calc v (c : K) * v (x : K) ≤ 1 * v (x : K) := mul_le_mul' hc le_rfl
      _ < 1 * 1 := mul_lt_mul_of_pos_left hx zero_lt_one
      _ = 1 := one_mul 1

/-- The `rv`-fibre `rv⁻¹(t)` on the `VF`-sort: the set of `b` with `\vv(b - t) < \vv t`.
This is the paper's `rv⁻¹(t)` (`t ∈ RV^×`), i.e. the "ball" `t·(1+𝔪)`. -/
def rvFibre (t : K) : Set K := {b : K | v (b - t) < v t}

theorem mem_rvFibre {t b : K} : b ∈ rvFibre v t ↔ v (b - t) < v t := Iff.rfl

/-- Every point of the fibre `rv⁻¹(t)` has the same value as `t`: `\vv b = \vv t`. -/
theorem rvFibre_val_eq {t b : K} (hb : b ∈ rvFibre v t) : v b = v t := by
  have h : b = t + (b - t) := by ring
  rw [h, v.map_add_eq_of_lt_left hb]

/-- Two points of the same fibre are closer to each other than the radius:
`\vv(a - b) < \vv t` for `a, b ∈ rv⁻¹(t)`. -/
theorem rvFibre_sub_lt {t a b : K} (ha : a ∈ rvFibre v t) (hb : b ∈ rvFibre v t) :
    v (a - b) < v t := by
  have h : a - b = (a - t) - (b - t) := by ring
  rw [h]
  exact (v.map_sub (a - t) (b - t)).trans_lt (max_lt ha hb)

end Bridge

/-! ## Part 2 — Definition 7.1, first half: `γ̄`-polynomials and residue values

The paper's sentence (paper.tex 1480, label `def:gamma:poly`):

> Let `γ̄ = (γ₁, …, γₙ) ∈ Γ`.  A polynomial `F(X̄) = ∑_{īj} a_{īj} X̄^ī` with coefficients
> `a_{īj} ∈ VF` is a *`γ̄`-polynomial* if there is an `α ∈ Γ` such that
> `α = vv(a_{īj}) + i₁γ₁ + ⋯ + iₙγₙ` for each `īj`.  In this case we say that `α` is a
> *residue value* of `F(X̄)` (with respect to `γ̄`).

(`a_{īj}` is read as the coefficient of `X̄^ī`; multiplicatively the displayed equation says
that *every* coefficient has the same value once weighted by `γ̄^ī`, namely `α`.) -/

section DefGamma

variable {v : Valuation K Γ₀} {σ : Type*} [Fintype σ]

/-- Definition 7.1 (`def:gamma:poly`), first half: `F` is a `γ`-polynomial with residue value
`α` when every coefficient in its support, weighted by the multi-index, has value `α`:

  `α = vv(a_{ī}) + i₁γ₁ + ⋯ + iₙγₙ` for each monomial `ī` of `F`

— written multiplicatively, `v (F.coeff m) * ∏ i, γ i ^ (m i) = α`.  The paper's `α` is
data (it also names it "a residue value"), so the predicate takes `α` as an argument. -/
def IsGammaPoly (v : Valuation K Γ₀) (γ : σ → Γ₀) (F : MvPolynomial σ K) (α : Γ₀) : Prop :=
  ∀ m ∈ F.support, v (F.coeff m) * ∏ i, γ i ^ m i = α

/-- The residue value is determined by `F` (when `F ≠ 0`): the paper's phrase *"a"* residue
value is in fact *"the"* residue value, unless the polynomial is the zero polynomial. -/
theorem residueValue_unique {v : Valuation K Γ₀} {γ : σ → Γ₀} {F : MvPolynomial σ K}
    {α α' : Γ₀} (h : IsGammaPoly v γ F α) (h' : IsGammaPoly v γ F α') (hF : F ≠ 0) :
    α = α' := by
  have hne : F.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h0
    apply hF
    rw [MvPolynomial.as_sum F, h0]
    simp
  obtain ⟨m, hm⟩ := hne
  rw [← h m hm, ← h' m hm]

/-- Two tuples `a`, `a'` of `VF` lie in the same `rv`-fibre over `γ`, written in the paper's
coordinates: `vrv(t̄) = γ̄` for the residue class `t̄` of `a`, and `\vv(aᵢ - a'ᵢ) < γᵢ`
(i.e. `aᵢ` and `a'ᵢ` have the same residue, which is `tᵢ`).  The third component is exactly the
statement that `a'` lies in the fibre `rv⁻¹(t̄)`. -/
def SameRVFibre {σ : Type*} (v : Valuation K Γ₀) (γ : σ → Γ₀) (a a' : σ → K) : Prop :=
  (∀ i, v (a i) = γ i) ∧ (∀ i, v (a' i) = γ i) ∧ ∀ i, v (a i - a' i) < γ i

theorem sameRVFibre_symm {v : Valuation K Γ₀} {γ : σ → Γ₀} {a a' : σ → K}
    (h : SameRVFibre v γ a a') : SameRVFibre v γ a' a :=
  ⟨h.2.1, h.1, fun i => by rw [← neg_sub (a i) (a' i), Valuation.map_neg]; exact h.2.2 i⟩

/-- The value `γ i = v (a i)` occurring in an `rv`-fibre is nonzero, hence positive: a
difference is strictly closer than it (`v (a i - a' i) < γ i`), and `0 ≤ v (a i - a' i)`. -/
theorem sameRVFibre_gamma_pos {v : Valuation K Γ₀} {γ : σ → Γ₀} {a a' : σ → K}
    (h : SameRVFibre v γ a a') (i : σ) : 0 < γ i :=
  lt_of_le_of_lt zero_le (by simpa [h.1 i] using h.2.2 i)

end DefGamma

/-! ## Part 3 — the two valuation estimates behind `some (hence all)` -/

section Estimates

variable {v : Valuation K Γ₀}

/-- Multiplicativity of `\vv` over a finite product: `\vv(∏ f) = ∏ \vv f`. -/
theorem map_prod_val {v : Valuation K Γ₀} {ι : Type*} (s : Finset ι) (f : ι → K) :
    v (∏ i ∈ s, f i) = ∏ i ∈ s, v (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih => rw [Finset.prod_insert hx, Finset.prod_insert hx, Valuation.map_mul, ih]

/-- Powers of two points of the same `rv`-fibre are again close:
`v (x ^ k - y ^ k) < γ ^ k` when `v x = v y = γ` and `v (x - y) < γ`. -/
theorem pow_sub_pow_lt {x y : K} {γ : Γ₀} (hx : v x = γ) (hy : v y = γ)
    (hxy : v (x - y) < γ) (k : ℕ) : v (x ^ k - y ^ k) < γ ^ k := by
  have hγ : 0 < γ := lt_of_le_of_lt zero_le hxy
  induction k with
  | zero => simpa using zero_lt_one
  | succ k ih =>
    have hdec : x ^ (k + 1) - y ^ (k + 1) = (x ^ k - y ^ k) * x + y ^ k * (x - y) := by ring
    rw [hdec, pow_succ]
    refine v.map_add_lt ?_ ?_
    · have h1 : v ((x ^ k - y ^ k) * x) = v (x ^ k - y ^ k) * γ := by
        rw [Valuation.map_mul, hx]
      rw [h1]
      exact mul_lt_mul_of_pos_right ih hγ
    · have h2 : v (y ^ k * (x - y)) = γ ^ k * v (x - y) := by
        rw [Valuation.map_mul, v.map_pow, hy]
      rw [h2]
      exact mul_lt_mul_of_pos_left hxy (pow_pos hγ k)

/-- The product estimate: for tuples of pairwise `rv`-equivalent points,
`v (∏ aᵢ ^ mᵢ - ∏ a'ᵢ ^ mᵢ) < ∏ γᵢ ^ mᵢ`. -/
theorem prod_pow_sub_prod_pow_lt {ι : Type*} {s : Finset ι} {a a' : ι → K} {γ : ι → Γ₀}
    {m : ι → ℕ} (ha : ∀ i ∈ s, v (a i) = γ i) (ha' : ∀ i ∈ s, v (a' i) = γ i)
    (h : ∀ i ∈ s, v (a i - a' i) < γ i) :
    v ((∏ i ∈ s, a i ^ m i) - (∏ i ∈ s, a' i ^ m i)) < ∏ i ∈ s, γ i ^ m i := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero_lt_one
  | insert x s hx ih =>
    have hR : ∏ i ∈ insert x s, γ i ^ m i = γ x ^ m x * ∏ i ∈ s, γ i ^ m i :=
      Finset.prod_insert hx
    rw [Finset.prod_insert hx, Finset.prod_insert hx, hR]
    have hdec : a x ^ m x * ∏ i ∈ s, a i ^ m i - a' x ^ m x * ∏ i ∈ s, a' i ^ m i =
        a x ^ m x * ((∏ i ∈ s, a i ^ m i) - (∏ i ∈ s, a' i ^ m i)) +
          (a x ^ m x - a' x ^ m x) * (∏ i ∈ s, a' i ^ m i) := by ring
    rw [hdec]
    refine v.map_add_lt ?_ ?_
    · rw [Valuation.map_mul, v.map_pow, ha x (Finset.mem_insert_self x s)]
      refine mul_lt_mul_of_pos_left ?_ (pow_pos (lt_of_le_of_lt zero_le (h x (Finset.mem_insert_self x s))) (m x))
      exact ih (fun i hi => ha i (Finset.mem_insert_of_mem hi))
        (fun i hi => ha' i (Finset.mem_insert_of_mem hi))
        (fun i hi => h i (Finset.mem_insert_of_mem hi))
    · rw [Valuation.map_mul]
      have hpos : 0 < ∏ i ∈ s, γ i ^ m i :=
        Finset.prod_pos (fun i hi => pow_pos (lt_of_le_of_lt zero_le (h i (Finset.mem_insert_of_mem hi))) _)
      have hlt : v (a x ^ m x - a' x ^ m x) < γ x ^ m x :=
        pow_sub_pow_lt (ha x (Finset.mem_insert_self x s)) (ha' x (Finset.mem_insert_self x s))
          (h x (Finset.mem_insert_self x s)) (m x)
      have hP : v (∏ i ∈ s, a' i ^ m i) = ∏ i ∈ s, γ i ^ m i := by
        rw [map_prod_val]
        exact Finset.prod_congr rfl (fun i hi => by rw [v.map_pow, ha' i (Finset.mem_insert_of_mem hi)])
      rw [hP]
      exact mul_lt_mul_of_pos_right hlt hpos

end Estimates

/-! ## Part 4 — the theorem behind the paper's "some (hence all)" -/

section Main

variable {v : Valuation K Γ₀} {n : ℕ}

/-- Every monomial of a `γ`-polynomial has value `α`, hence `\vv(F(ā)) ≤ α` in the paper's order;
this is Mathlib's `≤` (`v (F ā) ≤ α`). -/
theorem map_eval_le_residueValue {γ : Fin n → Γ₀} {F : MvPolynomial (Fin n) K} {α : Γ₀}
    (hF : IsGammaPoly v γ F α) {a : Fin n → K} (ha : ∀ i, v (a i) = γ i) :
    v (MvPolynomial.eval a F) ≤ α := by
  rw [MvPolynomial.eval_eq']
  refine v.map_sum_le ?_
  intro m hm
  have hmul : v (∏ i, a i ^ m i) = ∏ i, γ i ^ m i := by
    rw [map_prod_val Finset.univ (fun i => a i ^ m i)]
    exact Finset.prod_congr rfl (fun i _ => by rw [v.map_pow, ha i])
  rw [Valuation.map_mul, hmul, hF m hm]

/-- **The estimate behind "some (hence all)".**  If `F` is a `γ`-polynomial with residue value
`α ≠ 0` and `a`, `a'` are two points of the same `rv`-fibre (over `γ`), then the difference of
their values is strictly smaller than `α`: `\vv(F(ā) - F(ā')) < α`. -/
theorem map_eval_sub_eval_lt {γ : Fin n → Γ₀} {F : MvPolynomial (Fin n) K} {α : Γ₀}
    (hF : IsGammaPoly v γ F α) (hα : α ≠ 0) {a a' : Fin n → K}
    (h : SameRVFibre v γ a a') :
    v (MvPolynomial.eval a F - MvPolynomial.eval a' F) < α := by
  rw [MvPolynomial.eval_eq', MvPolynomial.eval_eq', ← Finset.sum_sub_distrib]
  refine v.map_sum_lt hα ?_
  intro m hm
  have hcoef : 0 < v (MvPolynomial.coeff m F) := by
    rw [zero_lt_iff]
    intro h0
    exact (MvPolynomial.mem_support_iff.mp hm) (v.zero_iff.mp h0)
  have hprod : v (∏ i, a i ^ m i - ∏ i, a' i ^ m i) < ∏ i, γ i ^ m i :=
    prod_pow_sub_prod_pow_lt (s := Finset.univ) (fun i _ => h.1 i) (fun i _ => h.2.1 i)
      (fun i _ => h.2.2 i)
  calc v (MvPolynomial.coeff m F * ∏ i, a i ^ m i - MvPolynomial.coeff m F * ∏ i, a' i ^ m i)
      = v (MvPolynomial.coeff m F) * v (∏ i, a i ^ m i - ∏ i, a' i ^ m i) := by
        rw [← mul_sub, Valuation.map_mul]
    _ < v (MvPolynomial.coeff m F) * ∏ i, γ i ^ m i := mul_lt_mul_of_pos_left hprod hcoef
    _ = α := hF m hm

/-- **Definition 7.1 (`def:gamma:poly`), the paper's "some (hence all)", proved.**

The paper's sentence (paper.tex 1480):

> For a `γ̄`-polynomial `F(X̄)` with residue value `α` and a `t̄ ∈ RV` with `vrv(t̄) = γ̄`, if
> `vv (F(ā)) > α` for some (hence all) `ā ∈ rv⁻¹(t̄)` then `t̄` is a *residue root* of `F(X̄)`.

The parenthetical asserts that the truth of `\vv(F(ā)) > α` is independent of the choice of `ā`
in the fibre `rv⁻¹(t̄)`.  That is this theorem: for two points `a`, `a'` of the same `rv`-fibre
over `γ` (hypothesis `SameRVFibre v γ a a'`, i.e. `\vv(aᵢ - a'ᵢ) < γᵢ`), the comparisons agree.
No hypothesis on `α` is needed: at `α = ∞` (Mathlib `α = 0`) both sides are false. -/
theorem map_eval_lt_iff {γ : Fin n → Γ₀} {F : MvPolynomial (Fin n) K} {α : Γ₀}
    (hF : IsGammaPoly v γ F α) {a a' : Fin n → K} (h : SameRVFibre v γ a a') :
    v (MvPolynomial.eval a F) < α ↔ v (MvPolynomial.eval a' F) < α := by
  rcases eq_or_ne α 0 with h0 | hα
  · subst h0
    exact ⟨fun hh => absurd hh (not_lt.mpr zero_le), fun hh => absurd hh (not_lt.mpr zero_le)⟩
  · constructor
    · intro ha
      have h1 : v (MvPolynomial.eval a' F - MvPolynomial.eval a F) < α :=
        map_eval_sub_eval_lt hF hα (sameRVFibre_symm h)
      have h2 : MvPolynomial.eval a' F =
          (MvPolynomial.eval a' F - MvPolynomial.eval a F) + MvPolynomial.eval a F := by ring
      rw [h2]
      exact (v.map_add _ _).trans_lt (max_lt h1 ha)
    · intro ha'
      have h1 : v (MvPolynomial.eval a F - MvPolynomial.eval a' F) < α :=
        map_eval_sub_eval_lt hF hα h
      have h2 : MvPolynomial.eval a F =
          (MvPolynomial.eval a F - MvPolynomial.eval a' F) + MvPolynomial.eval a' F := by ring
      rw [h2]
      exact (v.map_add _ _).trans_lt (max_lt h1 ha')

end Main

/-! ## Part 5 — residue roots, in the form the paper uses them -/

section ResidueRoot

variable {v : Valuation K Γ₀} {σ : Type*}

/-- Definition 7.1 (`def:gamma:poly`), second half, first clause: `a` is a point of the fibre
`rv⁻¹(t̄)` over `γ` (first component) with `\vv(F(ā)) > α` (second component); ranging over the
fibre, this is the paper's *"`t̄` is a residue root of `F(X̄)`"*. -/
def IsResidueRootAt (v : Valuation K Γ₀) (γ : σ → Γ₀) (F : MvPolynomial σ K) (α : Γ₀)
    (a : σ → K) : Prop :=
  (∀ i, v (a i) = γ i) ∧ v (MvPolynomial.eval a F) < α

/-- `t̄` is a residue root of `F` in the paper's "some" form: some point of the fibre
`rv⁻¹(t̄)` raises the value above `α`. -/
def IsResidueRoot (v : Valuation K Γ₀) (γ : σ → Γ₀) (F : MvPolynomial σ K) (α : Γ₀) : Prop :=
  ∃ a : σ → K, IsResidueRootAt v γ F α a

/-- The paper's "some (hence all)", in the form Definition 7.1 states it: for a `γ`-polynomial
`F` with residue value `α`, if one point `a` of the fibre `rv⁻¹(t̄)` satisfies
`\vv(F(ā)) > α`, then *every* point `a'` of that fibre does. -/
theorem residueRoot_some_hence_all {n : ℕ} {γ : Fin n → Γ₀} {F : MvPolynomial (Fin n) K}
    {α : Γ₀} (hF : IsGammaPoly v γ F α) {a : Fin n → K} (ha : ∀ i, v (a i) = γ i)
    (h : v (MvPolynomial.eval a F) < α) :
    ∀ a' : Fin n → K, (∀ i, v (a' i) = γ i) → (∀ i, v (a i - a' i) < γ i) →
      v (MvPolynomial.eval a' F) < α := by
  intro a' ha' hfib
  exact (map_eval_lt_iff hF ⟨ha, ha', hfib⟩).mp h

/-- On a *fixed* fibre the "some" and "all" forms of the predicate "`t̄` is a residue root of `F`"
agree, which is the content of the paper's parenthetical "some (hence all)".  The hypothesis
`hγ : 0 < γᵢ` is the paper's standing requirement that `t̄ ∈ (RV^×)ⁿ` (Theorem 7.6 works inside
`(RV^×)ⁿ`), and it is needed for `SameRVFibre` to be reflexive.  `rvFibre_sub_lt` moves between
two points of the fibre `rv⁻¹(aᵢ)`. -/
theorem residueRoot_fibre_exists_iff_forall {n : ℕ} {γ : Fin n → Γ₀}
    {F : MvPolynomial (Fin n) K} {α : Γ₀} (hF : IsGammaPoly v γ F α) {a : Fin n → K}
    (ha : ∀ i, v (a i) = γ i) (hγ : ∀ i, 0 < γ i) :
    (∃ a' : Fin n → K, SameRVFibre v γ a a' ∧ v (MvPolynomial.eval a' F) < α) ↔
      (∀ a' : Fin n → K, SameRVFibre v γ a a' → v (MvPolynomial.eval a' F) < α) := by
  constructor
  · rintro ⟨a', ha', hlt⟩ a'' ha''
    have hmem' : ∀ i, a' i ∈ rvFibre v (a i) := fun i => by
      show v (a' i - a i) < v (a i)
      calc v (a' i - a i) = v (a i - a' i) := by rw [← neg_sub, Valuation.map_neg]
        _ < γ i := ha'.2.2 i
        _ = v (a i) := (ha'.1 i).symm
    have hmem'' : ∀ i, a'' i ∈ rvFibre v (a i) := fun i => by
      show v (a'' i - a i) < v (a i)
      calc v (a'' i - a i) = v (a i - a'' i) := by rw [← neg_sub, Valuation.map_neg]
        _ < γ i := ha''.2.2 i
        _ = v (a i) := (ha''.1 i).symm
    have hsame : SameRVFibre v γ a' a'' :=
      ⟨ha'.2.1, ha''.2.1, fun i => by
        have := rvFibre_sub_lt v (hmem' i) (hmem'' i)
        rwa [ha'.1 i] at this⟩
    exact (map_eval_lt_iff hF hsame).mp hlt
  · intro h
    refine ⟨a, ⟨ha, ha, fun i => ?_⟩, h a ⟨ha, ha, fun i => ?_⟩⟩
    · simpa using hγ i
    · simpa using hγ i

end ResidueRoot

/-! ## Part 6 — Definition 7.1, second half: minimal tuples and *simple* common residue roots -/

section SimpleRoot

variable {v : Valuation K Γ₀}

/-- The Jacobian `det ∂(F₁, …, Fₙ)/∂(X₁, …, Xₙ)` of an `n`-tuple of polynomials, as a
polynomial in `X̄`; this is the determinant that Definition 7.1 uses to say that a common residue
root is *simple* ("minimal" is the paper's word for the tuple `F₁, …, Fₙ`). -/
noncomputable def jacobian {n : ℕ} (F : Fin n → MvPolynomial (Fin n) K) :
    MvPolynomial (Fin n) K :=
  (Matrix.of (fun i j => MvPolynomial.pderiv j (F i))).det

/-- The notion "`a` is a residue root of `F` with residue value `α`" is a property of the `rv`-fibre
of `a`, not of `a`: this is the "some (hence all)" of Definition 7.1 in the form used below. -/
theorem isResidueRootAt_iff {n : ℕ} {γ : Fin n → Γ₀} {F : MvPolynomial (Fin n) K} {α : Γ₀}
    (hF : IsGammaPoly v γ F α) {a a' : Fin n → K} (h : SameRVFibre v γ a a') :
    IsResidueRootAt v γ F α a ↔ IsResidueRootAt v γ F α a' := by
  constructor
  · rintro ⟨-, hlt⟩
    exact ⟨h.2.1, (map_eval_lt_iff hF h).mp hlt⟩
  · rintro ⟨-, hlt⟩
    exact ⟨h.1, (map_eval_lt_iff hF h).mpr hlt⟩

/-- Definition 7.1 (`def:gamma:poly`), second half, second clause.  The paper's sentence:

> If `t̄ ∈ RV` is a common residue root of the `γ̄`-polynomials `F₁(X̄), …, Fₙ(X̄)` but is not a
> residue root of the `γ̄`-polynomial `det ∂(F₁, …, Fₙ)/∂X̄`, then we say that
> `F₁(X̄), …, Fₙ(X̄)` are *minimal* for `t̄` and `t̄` is a *simple* common residue root of
> `F₁(X̄), …, Fₙ(X̄)`.

`β` is the residue value of the Jacobian determinant; the paper's computation
`vv (det ∂(F₁*, …, Fₙ*)/∂Ȳ(ā)) = ∑ᵢ αᵢ - ∑ᵢ γᵢ` identifies it as `β = ∏ αᵢ / ∏ γⱼ`
(see `JacobianResidueValue` below, which is *not* proved here). -/
def IsSimpleCommonResidueRoot (v : Valuation K Γ₀) {n : ℕ} (γ α : Fin n → Γ₀)
    (F : Fin n → MvPolynomial (Fin n) K) (β : Γ₀) (a : Fin n → K) : Prop :=
  (∀ i, IsGammaPoly v γ (F i) (α i)) ∧
    (∀ i, IsResidueRootAt v γ (F i) (α i) a) ∧
    IsGammaPoly v γ (jacobian F) β ∧
    ¬ IsResidueRootAt v γ (jacobian F) β a

/-- **The notion of a simple common residue root is well defined on the `rv`-fibre.**  This is the
form in which Definition 7.1's "some (hence all)" is actually used: `t̄` being a simple common
residue root of `F₁, …, Fₙ` is a property of `t̄` (i.e. of the fibre), not of the chosen
representative `ā` in `rv⁻¹(t̄)`. -/
theorem isSimpleCommonResidueRoot_iff {n : ℕ} {γ α : Fin n → Γ₀}
    {F : Fin n → MvPolynomial (Fin n) K} {β : Γ₀} {a a' : Fin n → K}
    (h : SameRVFibre v γ a a') :
    IsSimpleCommonResidueRoot v γ α F β a ↔ IsSimpleCommonResidueRoot v γ α F β a' := by
  constructor
  · rintro ⟨hF, hroot, hJ, hnot⟩
    exact ⟨hF, fun i => (isResidueRootAt_iff (hF i) h).mp (hroot i), hJ,
      fun hbad => hnot ((isResidueRootAt_iff hJ h).mpr hbad)⟩
  · rintro ⟨hF, hroot, hJ, hnot⟩
    exact ⟨hF, fun i => (isResidueRootAt_iff (hF i) h).mpr (hroot i), hJ,
      fun hbad => hnot ((isResidueRootAt_iff hJ h).mp hbad)⟩

/-- **The open statement on which `IsSimpleCommonResidueRoot` rests, recorded exactly.**

The paper computes, in the proof of `hensel:lemma` (paper.tex 1513),
`vv (det ∂(F₁*, …, Fₙ*)/∂Ȳ(ā)) = ∑ᵢ (-αᵢ + γᵢ) + ∑ᵢ αᵢ - ∑ᵢ γᵢ = 0`, i.e. in the notation of
Definition 7.1: **the Jacobian determinant of `γ̄`-polynomials with residue values `α₁, …, αₙ` is
itself a `γ̄`-polynomial, with residue value `∑ᵢ αᵢ - ∑ⱼ γⱼ` (multiplicatively `∏αᵢ/∏γⱼ`).**

This is *not* proved here.  What it needs: residue characteristic `0` (`v (m : K) = 1` for
`m > 0`, so that differentiating a monomial divides its value by `γⱼ` and nothing else), the
Leibniz expansion of the determinant, and the comparison of the `n!` permutation products — which
all have residue value `∏αᵢ/∏γⱼ`.  It is stated as a `Prop` so that it can be carried as an
explicit named hypothesis (never as an axiom). -/
def JacobianResidueValue (v : Valuation K Γ₀) (n : ℕ) (γ α : Fin n → Γ₀) : Prop :=
  ∀ (β : Γ₀) (F : Fin n → MvPolynomial (Fin n) K),
    β * ∏ j, γ j = ∏ i, α i →
      (∀ i, IsGammaPoly v γ (F i) (α i)) →
        IsGammaPoly v γ (jacobian F) β

end SimpleRoot

/-! ## Part 7 — the univariate case of the Jacobian computation

`JacobianResidueValue` is the statement that the Jacobian determinant of `γ`-polynomials with
residue values `α₁, …, αₙ` is a `γ`-polynomial with residue value `∑αᵢ - ∑γⱼ`.  At `n = 1` the
Jacobian is just the derivative, and in that case the computation is provable: the derivative of
`∑ aᵢ Xⁱ` has coefficients `(i+1) a_{i+1}`, so dividing the residue value by `γ` — and here the
paper's residue characteristic `0` is exactly what makes the integral factor `(i+1)` a unit
(`v ((i+1 : ℕ) : K) = 1`), which is carried as the explicit hypothesis `hres`. -/

section Univariate

open Polynomial

/-- Univariate version of Definition 7.1: `f` is a `γ`-polynomial with residue value `α` if every
coefficient in its support, weighted by `γ ^ i`, has value `α`.  (`Polynomial K` is the case
`σ = Fin 1` of `MvPolynomial σ K`, written separately so that the coefficient bookkeeping of the
derivative below stays local.) -/
def IsGammaPoly₁ (v : Valuation K Γ₀) (γ : Γ₀) (f : Polynomial K) (α : Γ₀) : Prop :=
  ∀ n ∈ f.support, v (f.coeff n) * γ ^ n = α

/-- **The `n = 1` case of the paper's Jacobian computation** (paper.tex 1513):
if `f` is a `γ`-polynomial with residue value `α` and `β γ = α`, then the derivative is a
`γ`-polynomial with residue value `β = α / γ` — provided every positive integer has value `1`,
i.e. the residue characteristic is `0`, which is the paper's setting. -/
theorem isGammaPoly₁_derivative {γ α β : Γ₀} (hγ : γ ≠ 0) (hβ : β * γ = α)
    (hres : ∀ m : ℕ, m ≠ 0 → v (m : K) = 1) {f : Polynomial K} (hf : IsGammaPoly₁ v γ f α) :
    IsGammaPoly₁ v γ (Polynomial.derivative f) β := by
  intro n hn
  have hcoeff : (Polynomial.derivative f).coeff n = ((n : K) + 1) * f.coeff (n + 1) := by
    rw [Polynomial.coeff_derivative]; ring
  have hsup : n + 1 ∈ f.support := by
    rw [Polynomial.mem_support_iff]
    intro h0
    exact (Polynomial.mem_support_iff.mp hn) (by rw [hcoeff, h0, mul_zero])
  have hval : v (f.coeff (n + 1)) * γ ^ (n + 1) = α := hf (n + 1) hsup
  have hnat : ((n : K) + 1) = ((n + 1 : ℕ) : K) := by push_cast; ring
  rw [hcoeff, hnat, Valuation.map_mul, hres (n + 1) (Nat.succ_ne_zero n), one_mul, pow_succ] at *
  refine mul_right_cancel₀ hγ ?_
  rw [mul_assoc, hval, hβ]

end Univariate

end Sec7Gamma
