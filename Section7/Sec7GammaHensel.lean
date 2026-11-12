module

/-
# Yin, *Special transformations in algebraically closed valued fields* — Section 7:
`def:gamma:poly` and `hensel:lemma` (generalized Hensel's lemma)

Source: `.ultramath/refs/paper.tex` lines 1480 (`\label{def:gamma:poly}`) and 1513
(`\label{hensel:lemma}`).

## Setting and conventions

The paper works in a valued field `\VF` with valuation ring `\OO`, maximal ideal `\mm`,
residue field `\K`, value group `\Gamma`, and the quotient `\rv : \VF -> \RV` with
`\vrv : \RV -> \Gamma \cup \{\infty\}`.  In this file the valued field is a Mathlib field `K`
with a `Valuation K Γ₀`, and the `RV`-sort is the verified construction of
`QE/Lemma32_root_lifting.lean` (`RV = Option (Kˣ/(1+𝔪))`, `rv`, `rvMul`, `vrv`, `rv_mul`,
`vrv_rv`, `rv_eq_iff`), copied verbatim below so that the file is standalone.

**Two convention differences, both explicit.**  (i) The paper writes `\Gamma` additively and
orders it so that `\vv(x) > 0` means `x ∈ \mm`; Mathlib's `Γ₀` is written multiplicatively
and ordered so that `v x < 1` means `x ∈ \mm`.  The dictionary used below is therefore

* paper `\vv(x) = \alpha`            ↔  Mathlib `v x = α`
* paper `\vv(x) > \alpha`            ↔  Mathlib `v x < α`
* paper `\vv(x) \ge \alpha`          ↔  Mathlib `v x ≤ α`
* paper `\alpha + \beta`             ↔  Γ₀-multiplication `α * β`
* paper `-\alpha`                    ↔  `α⁻¹`
* paper `\infty`                     ↔  `0` (the bottom of `Γ₀`; `v x = 0 ↔ x = 0`)

so the paper's ultrametric inequality `\vv(x+y) \ge \min(\vv x, \vv y)` is Mathlib's
`Valuation.map_add` in the equivalent form `v (x+y) < g` from `v x < g`, `v y < g`
(`Valuation.map_add_lt`).  (ii) The paper's `0` and `∞` in `\RV` are ONE element (`\rv 0`), as
`Milestone0/DECISION.md` records; that is `rvZero` below.

## What is here

* Definition 7.1 (`def:gamma:poly`) as a definition of the paper's three notions:
  `IsGammaPoly` (a `\bar\gamma`-polynomial with residue value `α`), `IsResidueRoot`
  (a residue root), and their combination `IsSimpleCommonResidueRoot` (`F_1,…,F_n` minimal
  for `\bar t`, `\bar t` a simple common residue root), for a *system* of `n` polynomials in
  `n` variables — which is the shape in which `hensel:lemma` uses them.
* Lemma 7.2 (`hensel:lemma`), the generalized Hensel lemma, as the `Prop`
  `HenselLemma v` (the paper's sentence verbatim in the docstring), together with its
  normalized form `NormalizedHensel v` (`γ = 0`, `α = 0`, i.e. all coefficients of value `1`
  and the residue root `(1,…,1)`) and the reduction

      `hensel_of_normalized : NormalizedHensel v → (γ-poly Hensel with t ∈ (RV^×)^n)`,

  which is exactly the body of the paper's proof: the change of variables `X_i = c_i Y_i`
  with `c_i ∈ \rv^{-1}(t_i)`, the multiplication `F_i^* = e_i F_i` with `\vv(e_i) = -\alpha_i`,
  and the Jacobian computation
  `\det \partial F^*/\partial Y (a) = (\prod_i e_i c_i) \cdot \det ∂F/∂X (\bar{ac})`.
  The Jacobian identity is proved here (`jacDet_scaled`) together with the chain rule for
  the diagonal substitution (`pderiv_diagScale`), the coefficient formula for the
  substitution (`diagScale_coeff`), and the residue-root/simple-root transport lemmas.
* `classical_hensel_of_normalized`: what remains is the *classical* multivariate Hensel
  lemma of Bourbaki (Cor. 2, p. 224) in the normalized form `NormalizedHensel`; it is not
  proved in this file and appears only as an explicit hypothesis of the theorems that use it
  (never as an `axiom`).  Its docstring carries the reference.

No `axiom`, no `sorry`, no `native_decide`.
-/
public import Mathlib

@[expose] public section

open MvPolynomial

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 400000

namespace Sec7

variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]

/-! ### The `RV`-sort (copied verbatim from `QE/Lemma32_root_lifting.lean`) -/

/-- The principal unit group `1 + 𝔪` of the valuation ring, as a subgroup of `Kˣ`. -/
def princUnits (v : Valuation K Γ₀) : Subgroup Kˣ where
  carrier := {u | v ((u : K) - 1) < 1}
  mul_mem' := by
    intro a b ha hb
    rw [Set.mem_ofPred] at ha hb ⊢
    have hva : v (a : K) = 1 := by
      have h1 : (a : K) = 1 + ((a : K) - 1) := by ring
      rw [h1, v.map_one_add_of_lt ha]
    have h : ((a * b : Kˣ) : K) - 1 = ((a : K) - 1) + (a : K) * ((b : K) - 1) := by
      push_cast; ring
    rw [h]
    refine v.map_add_lt ha ?_
    rw [map_mul, hva, one_mul]
    exact hb
  one_mem' := by
    rw [Set.mem_ofPred]
    simp
  inv_mem' := by
    intro a ha
    rw [Set.mem_ofPred] at ha ⊢
    have hva : v (a : K) = 1 := by
      have h1 : (a : K) = 1 + ((a : K) - 1) := by ring
      rw [h1, v.map_one_add_of_lt ha]
    have h : ((a⁻¹ : Kˣ) : K) - 1 = -(((a : K) - 1) / (a : K)) := by
      push_cast
      field_simp
      ring
    have hdiv : v (((a : K) - 1) / (a : K)) = v ((a : K) - 1) := by
      rw [div_eq_mul_inv, map_mul, Valuation.map_inv v, hva, inv_one, mul_one]
    rw [h, v.map_neg, hdiv]
    exact ha

/-- Yin's `RV×`: `Kˣ/(1+𝔪)`. -/
abbrev RVUnit (v : Valuation K Γ₀) : Type _ := Kˣ ⧸ princUnits v

/-- Yin's `RV`-sort: `RV = RV× ∪ {0}`, where `0` is the residue field's zero, the value
`rv 0` of `rv` at `0`, and the absorbing (top) element of `RV`.  The paper also writes this
one element as `∞`. -/
abbrev RV (v : Valuation K Γ₀) : Type _ := Option (RVUnit v)

/-- Yin's `rv : VF → RV`, with `rv 0 = 0` (the absorbing element, written `∞` in the paper). -/
noncomputable def rv (v : Valuation K Γ₀) (x : K) : RV v := by
  classical
  exact if h : x = 0 then none else some (QuotientGroup.mk' _ (Units.mk0 x h))

/-- The paper's `0` (and `∞`): `rv(0)`, the absorbing element of `RV`. -/
abbrev rvZero (v : Valuation K Γ₀) : RV v := none

variable {v : Valuation K Γ₀}

theorem rv_zero : rv v (0 : K) = rvZero v := by
  classical exact dif_pos rfl

theorem rv_of_ne {x : K} (h : x ≠ 0) : rv v x = some (QuotientGroup.mk' _ (Units.mk0 x h)) := by
  classical exact dif_neg h

theorem rv_eq_none_iff {x : K} : rv v x = rvZero v ↔ x = 0 := by
  classical
  unfold rv rvZero
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => rfl⟩
  · simp [h]

/-- Multiplication in `RV×`, extended by the absorbing element `0 = ∞`. -/
def rvMul : RV v → RV v → RV v
  | none, _ => none
  | some _, none => none
  | some a, some b => some (a * b)

theorem rv_mul (x y : K) : rv v (x * y) = rvMul (rv v x) (rv v y) := by
  by_cases hx : x = 0
  · rw [hx, zero_mul, rv_zero]
    cases rv v y with
    | none => rfl
    | some q => rfl
  by_cases hy : y = 0
  · rw [hy, mul_zero, rv_zero]
    cases rv v x with
    | none => rfl
    | some q => rfl
  rw [rv_of_ne hx, rv_of_ne hy, rv_of_ne (mul_ne_zero hx hy)]
  have hdef : rvMul (some (QuotientGroup.mk' _ (Units.mk0 x hx)) : RV v)
      (some (QuotientGroup.mk' _ (Units.mk0 y hy)) : RV v)
      = some (QuotientGroup.mk' _ (Units.mk0 x hx) * QuotientGroup.mk' _ (Units.mk0 y hy)) := rfl
  rw [hdef, ← map_mul]
  rw [show (Units.mk0 (x * y) (mul_ne_zero hx hy) : Kˣ) = Units.mk0 x hx * Units.mk0 y hy
      from Units.ext rfl]

/-- `1` of the `RV`-sort. -/
theorem rv_one : rv v (1 : K) = some (QuotientGroup.mk' _ (1 : Kˣ)) := by
  rw [rv_of_ne one_ne_zero]
  congr 2
  exact Units.ext rfl

/-- `rv` is surjective onto `RV ∖ {0}`: the paper's surjectivity of `rv : VF^× → RV^×`. -/
theorem rv_surjective {t : RV v} (h : t ≠ rvZero v) : ∃ x : K, x ≠ 0 ∧ rv v x = t := by
  cases t with
  | none => exact absurd rfl h
  | some q =>
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (princUnits v) q
    exact ⟨(u : K), Units.ne_zero u, by
      rw [rv_of_ne (Units.ne_zero u)]
      congr 2
      exact Units.ext rfl⟩

/-- The valuation, as a monoid homomorphism on the units of `K`. -/
noncomputable def vUnits (v : Valuation K Γ₀) : Kˣ →* Γ₀ˣ where
  toFun u := Units.mk0 (v (u : K)) (by rw [Valuation.ne_zero_iff]; exact Units.ne_zero u)
  map_one' := by ext; simp
  map_mul' a b := by ext; simp [Valuation.map_mul]

theorem vUnits_ker (v : Valuation K Γ₀) : princUnits v ≤ (vUnits v).ker := by
  intro x hx
  have hx' : v ((x : K) - 1) < 1 := hx
  rw [MonoidHom.mem_ker, Units.ext_iff]
  show v ((x : Kˣ) : K) = 1
  have h1 : (x : K) = 1 + ((x : K) - 1) := by ring
  rw [h1, v.map_one_add_of_lt hx']

/-- `vrv` on `RV×`, induced by the valuation. -/
noncomputable def vrvUnit (v : Valuation K Γ₀) : RVUnit v →* Γ₀ˣ :=
  QuotientGroup.lift _ (vUnits v) (vUnits_ker v)

/-- Yin's `vrv : RV → Γ ∪ {∞}` (with `∞` read as `0`; the paper's order on `Γ ∪ {∞}` is the
reverse of Mathlib's order on `Γ₀`). -/
noncomputable def vrv (v : Valuation K Γ₀) : RV v → Γ₀
  | none => 0
  | some q => (vrvUnit v q : Γ₀)

theorem vrv_mk (u : Kˣ) : vrv v (some (QuotientGroup.mk' _ u)) = v (u : K) := by
  show (((vrvUnit v) (QuotientGroup.mk' _ u) : Γ₀ˣ) : Γ₀) = v (u : K)
  rw [vrvUnit]
  rfl

/-- `vv = vrv ∘ rv` (Yin, axiom 6). -/
theorem vrv_rv (x : K) : vrv v (rv v x) = v x := by
  by_cases h : x = 0
  · rw [h, rv_zero, map_zero]
    rfl
  · rw [rv_of_ne h]
    exact vrv_mk (Units.mk0 x h)

/-- **The class condition**, `b' ∈ t` in field terms: two nonzero elements have the same
`rv`-class iff they have the same valuation and their quotient is a principal unit. -/
theorem rv_eq_iff {x y : K} (hy : y ≠ 0) :
    rv v x = rv v y ↔ v x = v y ∧ v (x / y - 1) < 1 := by
  have hxne : x ≠ 0 → y / x ≠ 0 := by
    intro hx h0
    rw [div_eq_zero_iff] at h0
    tauto
  constructor
  · rintro h
    have hx : x ≠ 0 := by
      rintro rfl
      rw [rv_zero, rv_of_ne hy] at h
      exact absurd h (by simp)
    rw [rv_of_ne hx, rv_of_ne hy, Option.some_inj] at h
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at h
    have hmem := QuotientGroup.eq.mp h
    have hmem' : v ((((Units.mk0 x hx)⁻¹ * Units.mk0 y hy : Kˣ) : K) - 1) < 1 := hmem
    have hpush : (((Units.mk0 x hx)⁻¹ * Units.mk0 y hy : Kˣ) : K) = y / x := by
      simp [div_eq_mul_inv, mul_comm]
    rw [hpush] at hmem'
    have hunit : v (y / x) = 1 := by
      have h1 : y / x = 1 + (y / x - 1) := by ring
      rw [h1, v.map_one_add_of_lt hmem']
    have hvy : v y = v x := by
      have h2 : v (y / x) = v y / v x := Valuation.map_div v y x
      rw [h2] at hunit
      rcases eq_or_ne (v x) 0 with h0 | h0
      · rw [h0, div_zero] at hunit
        exact absurd hunit (by simp)
      · calc v y = v y / v x * v x := (div_mul_cancel₀ _ h0).symm
          _ = 1 * v x := by rw [hunit]
          _ = v x := one_mul _
    refine ⟨hvy.symm, ?_⟩
    have h3 : (y / x)⁻¹ - 1 = -((y / x - 1) / (y / x)) := by
      field_simp
      ring
    have h4 : v ((y / x - 1) / (y / x)) = v (y / x - 1) := by
      rw [div_eq_mul_inv, map_mul, Valuation.map_inv v, hunit, inv_one, mul_one]
    have h5 : (y / x)⁻¹ = x / y := by
      field_simp
    have h6 : v ((y / x)⁻¹ - 1) < 1 := by
      rw [h3, v.map_neg, h4]
      exact hmem'
    rwa [h5] at h6
  · rintro ⟨hval, hlt⟩
    have hx : x ≠ 0 := by
      rintro rfl
      rw [zero_div, zero_sub, v.map_neg, map_one] at hlt
      exact absurd hlt (lt_irrefl 1)
    rw [rv_of_ne hx, rv_of_ne hy, Option.some_inj,
      QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have h1 : ((((Units.mk0 x hx)⁻¹ * Units.mk0 y hy : Kˣ) : K)) = y / x := by
      simp [div_eq_mul_inv, mul_comm]
    show v ((((Units.mk0 x hx)⁻¹ * Units.mk0 y hy : Kˣ) : K) - 1) < 1
    rw [h1]
    have hv : v (y / x) = 1 := by
      have h2 : v (y / x) = v y / v x := Valuation.map_div v y x
      rw [h2, ← hval]
      exact div_self ((Valuation.ne_zero_iff v).2 hx)
    have h5 : x / y = (y / x)⁻¹ := by
      field_simp
    rw [h5] at hlt
    have heq : v ((y / x)⁻¹ - 1) = v (y / x - 1) := by
      have h3 : (y / x)⁻¹ - 1 = -((y / x - 1) / (y / x)) := by
        field_simp
        ring
      rw [h3, v.map_neg, div_eq_mul_inv, map_mul, Valuation.map_inv v, hv, inv_one, mul_one]
    rwa [heq] at hlt

/-! ### Definition 7.1: `γ`-polynomials, residue roots, simple common residue roots -/

section Defs

variable (v : Valuation K Γ₀)

/-- The weight of the multi-index `m` at `\bar t ∈ \RV^n`: the paper's `i_1γ_1 + ⋯ + i_nγ_n`
with `γ_j = \vrv(t_j)`, read in `Γ₀` (multiplicatively). -/
noncomputable def gammaWeight {n : ℕ} (t : Fin n → RV v) (m : Fin n →₀ ℕ) : Γ₀ :=
  m.prod fun j e => vrv v (t j) ^ e

/-- **Definition 7.1, first item (`def:gamma:poly`).**  Paper: *"A polynomial
`F(\bar X) = \sum_{\bar i j} a_{\bar i j} \bar X^{\bar i}` with coefficients `a_{\bar i j} ∈ \VF`
is a **`\bar\gamma`-polynomial** if there is an `α ∈ \Gamma` such that
`α = \vv(a_{\bar i j}) + i_1γ_1 + ⋯ + i_nγ_n` for each `\bar i j = (i_1,…,i_n,j)`.  In this case
we say that `α` is a **residue value** of `F(\bar X)` (with respect to `\bar\gamma`)."*

Transcribed: `α` is a residue value of `F` w.r.t. the tuple `\bar t` (whose `vrv` is
`\bar\gamma`) iff every nonzero coefficient `a_m` of `F` satisfies
`v(a_m) * \prod_j γ_j^{m_j} = α` — i.e. the paper's `\vv(a_m) + m\cdotγ = α` after the
dictionary of the header (paper `+` = `Γ₀`-multiplication).  The zero polynomial is a
`\bar\gamma`-polynomial with residue value `0` (= the paper's `∞`), and only it. -/
def IsGammaPoly {n : ℕ} (t : Fin n → RV v) (α : Γ₀) (F : MvPolynomial (Fin n) K) : Prop :=
  ∀ m ∈ F.support, v (F.coeff m) * gammaWeight v t m = α

/-- **Definition 7.1, second item (`def:gamma:poly`).**  Paper: *"For a `\bar\gamma`-polynomial
`F(\bar X)` with residue value `α` and a `\bar t ∈ \RV` with `\vrv(\bar t) = \bar\gamma`, if
`\vv(F(\bar a)) > α` for some (hence all) `\bar a ∈ \rv^{-1}(\bar t)` then `\bar t` is a
**residue root** of `F(\bar X)`."*

Transcribed with the "hence all" quantifier made explicit: `\bar t` is a residue root iff
`v(F(\bar a)) < α` for **every** `\bar a ∈ \rv^{-1}(\bar t)` (the paper's `\vv > α` is Mathlib's
`v < α`).  The parenthetical "(hence all)" is the lemma `isResidueRoot_iff_exists` below in
the situations where it is available; taking `∀` is the form the paper's applications use. -/
def IsResidueRoot {n : ℕ} (t : Fin n → RV v) (α : Γ₀) (F : MvPolynomial (Fin n) K) : Prop :=
  ∀ a : Fin n → K, (∀ j, rv v (a j) = t j) → v (F.eval a) < α

/-- The Jacobian matrix `(\partial F_i/\partial X_j)(\bar a)`. -/
noncomputable def jacMat {n : ℕ} (F : Fin n → MvPolynomial (Fin n) K) (a : Fin n → K) :
    Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j => (pderiv j (F i)).eval a

/-- The Jacobian determinant `\det \partial(F_1,…,F_n)/\partial\bar X`, as a polynomial. -/
noncomputable def jacDet {n : ℕ} (F : Fin n → MvPolynomial (Fin n) K) :
    MvPolynomial (Fin n) K :=
  Matrix.det (Matrix.of fun i j => pderiv j (F i))

/-- **Definition 7.1, third item (`def:gamma:poly`).**  Paper: *"If `\bar t ∈ \RV` is a common
residue root of the `\bar\gamma`-polynomials `F_1(\bar X), …, F_n(\bar X)` but is not a residue
root of the `\bar\gamma`-polynomial `\det \partial(F_1,…,F_n)/\partial\bar X`, then we say that
`F_1(\bar X), …, F_n(\bar X)` are **minimal** for `\bar t` and `\bar t` is a **simple common
residue root** of `F_1(\bar X), …, F_n(\bar X)`."*

The residue value of the Jacobian determinant is `\sum_i α_i - \sum_j γ_j`, i.e. in `Γ₀`
`(∏_i α_i) * (∏_j γ_j)⁻¹` (each `\partial F_i/\partial X_j` is a `\bar\gamma`-polynomial of
residue value `α_i - γ_j`, and the determinant is a signed sum of products of `n` of them);
that value is what "not a residue root of the determinant" is measured against, and it is
what the paper uses in the proof of `RV:iso:class:lifted`
(`\vv(\det ∂(F^*)/∂Y) = \sum_i α_i - \sum_i δ_i`). -/
def IsSimpleCommonResidueRoot {n : ℕ} (t : Fin n → RV v) (α : Fin n → Γ₀)
    (F : Fin n → MvPolynomial (Fin n) K) : Prop :=
  (∀ i, IsGammaPoly v t (α i) (F i)) ∧
  (∀ i, IsResidueRoot v t (α i) (F i)) ∧
  ¬ IsResidueRoot v t ((∏ i, α i) * (∏ j, vrv v (t j))⁻¹) (jacDet F)

/-- `F` is a `\bar t`-system: a family of `n` polynomials in `n` variables forming a system of
`\bar\gamma`-polynomials with residue values `\bar\alpha`. -/
def IsGammaSystem {n : ℕ} (t : Fin n → RV v) (α : Fin n → Γ₀)
    (F : Fin n → MvPolynomial (Fin n) K) : Prop :=
  ∀ i, IsGammaPoly v t (α i) (F i)

end Defs

/-! ### Lemma 7.2: `hensel:lemma`, the generalized Hensel lemma -/

section Hensel

variable (v : Valuation K Γ₀)

/-- **Lemma 7.2 (`hensel:lemma`), the generalized Hensel lemma.**  Paper: *"Let
`F_1(\bar X), …, F_n(\bar X)` be `\bar\gamma`-polynomials with residue values
`α_1, …, α_n`, where `\bar\gamma = (γ_1, …, γ_n) ∈ \Gamma`.  For every simple common residue
root `\bar t = (t_1, …, t_n) ∈ \RV` of `F_1(\bar X), …, F_n(\bar X)` there is a unique
`\bar a ∈ \rv^{-1}(\bar t)` such that `F_i(\bar a) = 0` for every `i`."*

`HenselLemma v` is that sentence, with the uniqueness and existence in `∃!` form; the
hypothesis "the `F_i` are `\bar\gamma`-polynomials with residue values `\bar\alpha` and `\bar t`
is a simple common residue root" is `IsSimpleCommonResidueRoot v \bar t \bar\alpha F`
(Definition 7.1).  The paper's *hypothesis* of the lemma — that the valued field be
topologically complete of rank `1` — is not a hypothesis of the lemma as printed (it is used
inside the proof via Bourbaki's multivariate Hensel lemma), and it is carried explicitly as
the separate hypothesis `NormalizedHensel v` of `hensel_of_normalized` below, whose docstring
names it. -/
def HenselLemma : Prop :=
  ∀ (n : ℕ) (F : Fin n → MvPolynomial (Fin n) K) (t : Fin n → RV v) (α : Fin n → Γ₀),
    IsSimpleCommonResidueRoot v t α F →
      ∃! a : Fin n → K, (∀ j, rv v (a j) = t j) ∧ (∀ i, (F i).eval a = 0)

/-- The same statement with the `\bar t ∈ (\RV^\times)^n` restriction that the paper's use of
it has (`Theorem 7.6` has `C ⊆ (\RV^\times)^n × (\RV^\times)^n`).  This is the form proved
here from the normalized Hensel lemma. -/
def HenselLemmaUnits : Prop :=
  ∀ (n : ℕ) (F : Fin n → MvPolynomial (Fin n) K) (t : Fin n → RV v) (α : Fin n → Γ₀),
    (∀ j, t j ≠ rvZero v) →
    IsSimpleCommonResidueRoot v t α F →
      ∃! a : Fin n → K, (∀ j, rv v (a j) = t j) ∧ (∀ i, (F i).eval a = 0)

/-- **The normalized form of `hensel:lemma`**: `\bar\gamma = \bar 0` (the residue root is
`(1,…,1) ∈ (\RV^\times)^n`, i.e. `vrv = 0` in the paper's notation) and residue values
`α_i = 0` (in `Γ₀`: `α_i = 1`, i.e. all coefficients have value `1`).

This is the statement that the paper's proof invokes from Bourbaki: after the change of
variables `X_i = c_iY_i` and the multiplication by `e_i` with `\vv(e_i) = -α_i`, the system
`F^*_i` has all coefficients of value `1` (`0` in the paper's additive `\Gamma`) and
`(1,…,1)` is a simple common residue root of it; Bourbaki's *multivariate Hensel lemma*
(`\cite[Corollary 2, p. 224]{bourbaki:1989}`) then supplies the root.  So `NormalizedHensel v`
is the classical multivariate Hensel lemma in this language, and it is the one non-elementary
input of `hensel_of_normalized`, carried as an explicit hypothesis. -/
def NormalizedHensel : Prop :=
  ∀ (n : ℕ) (F : Fin n → MvPolynomial (Fin n) K),
    IsSimpleCommonResidueRoot v (fun _ => rv v 1) (fun _ => (1 : Γ₀)) F →
      ∃! a : Fin n → K, (∀ j, rv v (a j) = rv v 1) ∧ (∀ i, (F i).eval a = 0)

end Hensel

/-! ### The diagonal substitution `X_j ↦ c_j X_j` (the paper's `X_i = c_i Y_i`) -/

section DiagScale

/-- The `K`-algebra endomorphism `X_j ↦ c_j · X_j` of `MvPolynomial (Fin n) K`: the paper's
"changing the coefficients accordingly we may rewrite each `F_i(\bar X)` as
`F_i(X_1/c_1, …, X_n/c_n)`", read in the inverse direction (`X_i = c_iY_i`). -/
noncomputable def diagScale {n : ℕ} (c : Fin n → K) :
    MvPolynomial (Fin n) K →ₐ[K] MvPolynomial (Fin n) K :=
  MvPolynomial.aeval fun j => MvPolynomial.C (c j) * MvPolynomial.X j

theorem diagScale_X {n : ℕ} (c : Fin n → K) (j : Fin n) :
    diagScale c (MvPolynomial.X j) = MvPolynomial.C (c j) * MvPolynomial.X j := by
  rw [diagScale, MvPolynomial.aeval_X]

theorem diagScale_C {n : ℕ} (c : Fin n → K) (a : K) :
    diagScale c (MvPolynomial.C a) = MvPolynomial.C a := by
  rw [diagScale, MvPolynomial.aeval_C]
  simp

theorem diagScale_one {n : ℕ} (c : Fin n → K) : diagScale c (1 : MvPolynomial (Fin n) K) = 1 :=
  map_one _

theorem diagScale_zero {n : ℕ} (c : Fin n → K) : diagScale c (0 : MvPolynomial (Fin n) K) = 0 :=
  map_zero _

/-- The value of the substituted monomial: `(cX)^m = (∏_j c_j^{m_j}) · X^m`. -/
theorem diagScale_monomial {n : ℕ} (c : Fin n → K) (d : Fin n →₀ ℕ) (r : K) :
    diagScale c (MvPolynomial.monomial d r)
      = MvPolynomial.monomial d (r * d.prod fun j e => c j ^ e) := by
  rw [diagScale, MvPolynomial.aeval_monomial, MvPolynomial.algebraMap_eq,
    ← MvPolynomial.C_mul_monomial]
  congr 1
  rw [Finsupp.prod, Finsupp.prod]
  rw [show (∏ a ∈ d.support, (MvPolynomial.C (c a) * MvPolynomial.X a) ^ d a)
      = ∏ a ∈ d.support, (MvPolynomial.C (c a ^ d a) * MvPolynomial.X a ^ d a) from
    Finset.prod_congr rfl fun a _ => by rw [mul_pow, MvPolynomial.C_pow]]
  rw [Finset.prod_mul_distrib, MvPolynomial.prod_X_pow_eq_monomial, ← map_prod,
    MvPolynomial.C_mul_monomial, mul_one]

/-- The coefficients of the substituted polynomial:
`coeff_m (F(cX)) = coeff_m F · ∏_j c_j^{m_j}`. -/
theorem diagScale_coeff {n : ℕ} (c : Fin n → K) (P : MvPolynomial (Fin n) K) (m : Fin n →₀ ℕ) :
    (diagScale c P).coeff m = P.coeff m * (m.prod fun j e => c j ^ e) := by
  conv_lhs => rw [MvPolynomial.as_sum P]
  rw [map_sum, MvPolynomial.coeff_sum]
  rw [Finset.sum_eq_single m]
  · rw [diagScale_monomial, MvPolynomial.coeff_monomial, if_pos rfl]
  · intro b hb hne
    rw [diagScale_monomial, MvPolynomial.coeff_monomial, if_neg hne]
  · intro h
    rw [MvPolynomial.notMem_support_iff] at h
    rw [h]
    simp

/-- Evaluation of the substituted polynomial: `F(cX)` at `\bar y` is `F` at `\bar c · \bar y`. -/
theorem eval_diagScale {n : ℕ} (c : Fin n → K) (P : MvPolynomial (Fin n) K) (y : Fin n → K) :
    (diagScale c P).eval y = P.eval fun j => c j * y j := by
  induction P using MvPolynomial.induction_on' with
  | monomial d r =>
    rw [diagScale_monomial, MvPolynomial.eval_monomial, MvPolynomial.eval_monomial]
    have h : d.prod (fun j e => (c j * y j) ^ e)
        = (d.prod fun j e => c j ^ e) * (d.prod fun j e => y j ^ e) := by
      rw [Finsupp.prod, Finsupp.prod, Finsupp.prod,
        show (∏ a ∈ d.support, (c a * y a) ^ d a)
            = ∏ a ∈ d.support, (c a ^ d a * y a ^ d a) from
          Finset.prod_congr rfl fun a _ => mul_pow _ _ _,
        Finset.prod_mul_distrib]
    rw [h]; ring
  | add p q hp hq => rw [map_add, MvPolynomial.eval_add, hp, MvPolynomial.eval_add, hq]

/-- **The chain rule for the diagonal substitution**: `∂/∂Y_i (F(cY)) = c_i (∂F/∂X_i)(cY)`.
This is the derivative form of the change of variables `X_i = c_iY_i`. -/
theorem pderiv_diagScale {n : ℕ} (c : Fin n → K) (i : Fin n) (P : MvPolynomial (Fin n) K) :
    pderiv i (diagScale c P)
      = MvPolynomial.C (c i) * diagScale c (pderiv i P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    simp only [map_add, hp, hq]
    ring
  | mul_X p j hp =>
    have hX : pderiv i (MvPolynomial.C (c j) * MvPolynomial.X j)
        = if i = j then MvPolynomial.C (c j) else 0 := by
      rw [MvPolynomial.pderiv_C_mul]
      by_cases h : i = j
      · subst h; rw [MvPolynomial.pderiv_X_self, mul_one, if_pos rfl]
      · rw [MvPolynomial.pderiv_X_of_ne (Ne.symm h), mul_zero, if_neg h]
    have hdsX : diagScale c (pderiv i (MvPolynomial.X j)) = if i = j then 1 else 0 := by
      by_cases h : i = j
      · subst h; rw [MvPolynomial.pderiv_X_self, map_one, if_pos rfl]
      · rw [MvPolynomial.pderiv_X_of_ne (Ne.symm h), map_zero, if_neg h]
    have hL : pderiv i (diagScale c (p * MvPolynomial.X j))
        = (MvPolynomial.C (c i) * diagScale c (pderiv i p))
            * (MvPolynomial.C (c j) * MvPolynomial.X j)
          + diagScale c p * (if i = j then MvPolynomial.C (c j) else 0) := by
      simp only [map_mul, diagScale_X, MvPolynomial.pderiv_mul, hp, hX]
    have hR : MvPolynomial.C (c i) * diagScale c (pderiv i (p * MvPolynomial.X j))
        = MvPolynomial.C (c i) *
            (diagScale c (pderiv i p) * (MvPolynomial.C (c j) * MvPolynomial.X j)
              + diagScale c p * (if i = j then 1 else 0)) := by
      simp only [MvPolynomial.pderiv_mul, map_add, map_mul, diagScale_X, hdsX]
    rw [hL, hR]
    by_cases h : i = j
    · subst h; simp; ring
    · simp only [if_neg h, mul_zero, add_zero]; ring

end DiagScale

/-! ### The Jacobian computation of `hensel:lemma`

The paper's proof of `hensel:lemma` substitutes `X_i = c_iY_i`, multiplies `F_i` by `e_i` with
`\vv(e_i) = -\alpha_i`, and then computes

  `\det \partial(F^*_1,…,F^*_n)/\partial\bar Y(\bar a) = \bigl(\prod_i e_ic_i\bigr) \cdot
   \det \partial(F_1,…,F_n)/\partial\bar X(\bar{ac})`

and hence `\vv(\det) = \sum_i(-\alpha_i + \gamma_i) + \sum_i\alpha_i - \sum_i\gamma_i = 0`.
That is `jacDet_eval_scaled` and `val_jacDet_scaled` below. -/

section Jacobian

/-- The Jacobian determinant of a system, evaluated: `(jacDet F).eval y = (jacMat F y).det`. -/
theorem eval_jacDet {n : ℕ} (F : Fin n → MvPolynomial (Fin n) K) (y : Fin n → K) :
    (jacDet F).eval y = (jacMat F y).det := by
  rw [jacDet, RingHom.map_det]
  rfl

/-- **The scaled Jacobian**: for `G_i = e_i · F_i(cY)`,
`J_G(y) = \mathrm{diag}(e) · J_F(c·y) · \mathrm{diag}(c)`. -/
theorem jacMat_scaled {n : ℕ} (F : Fin n → MvPolynomial (Fin n) K) (c e y : Fin n → K) :
    jacMat (fun i => MvPolynomial.C (e i) * diagScale c (F i)) y
      = Matrix.diagonal e * jacMat F (fun j => c j * y j) * Matrix.diagonal c := by
  ext i j
  simp only [jacMat, Matrix.of_apply, Matrix.mul_apply, Matrix.diagonal_apply,
    MvPolynomial.pderiv_C_mul, pderiv_diagScale, eval_diagScale, MvPolynomial.eval_mul,
    MvPolynomial.eval_C]
  rw [Finset.sum_eq_single j]
  · rw [if_pos rfl, Finset.sum_eq_single i]
    · rw [if_pos rfl]; ring
    · intro b _ hb
      simp only [if_neg (fun h : i = b => hb h.symm), zero_mul]
    · intro h; exact absurd (Finset.mem_univ i) h
  · intro b _ hb
    simp only [if_neg hb, mul_zero]
  · intro h; exact absurd (Finset.mem_univ j) h

/-- **The scaled Jacobian determinant** (the paper's displayed computation). -/
theorem jacDet_eval_scaled {n : ℕ} (F : Fin n → MvPolynomial (Fin n) K) (c e y : Fin n → K) :
    (jacDet (fun i => MvPolynomial.C (e i) * diagScale c (F i))).eval y
      = (∏ i, e i * c i) * (jacDet F).eval (fun j => c j * y j) := by
  rw [eval_jacDet, jacMat_scaled, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal,
    Matrix.det_diagonal, eval_jacDet, Finset.prod_mul_distrib]
  ring

end Jacobian

/-! ### Transport of the `γ`-polynomial structure along `X_i = c_i Y_i`, `F_i ↦ e_iF_i` -/

section Transport

variable {v : Valuation K Γ₀}

/-- `v` of a finite product. -/
theorem v_finset_prod {ι : Type*} (s : Finset ι) (f : ι → K) :
    v (∏ i ∈ s, f i) = ∏ i ∈ s, v (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, map_mul, ih]

/-- `v` of the monomial factor `∏_j x_j^{m_j}` of the substitution `X_j ↦ c_jX_j`. -/
theorem v_finsupp_prod {n : ℕ} (x : Fin n → K) (m : Fin n →₀ ℕ) :
    v (m.prod fun j e => x j ^ e) = m.prod fun j e => (v (x j)) ^ e := by
  rw [Finsupp.prod, Finsupp.prod, v_finset_prod]
  exact Finset.prod_congr rfl fun j _ => map_pow ..

/-- `rv 1` is a right identity of `rvMul` on `RV ∖ {0}`. -/
theorem rvMul_rv_one {t : RV v} (ht : t ≠ rvZero v) : rvMul t (rv v 1) = t := by
  obtain ⟨x, hx, rfl⟩ := rv_surjective ht
  rw [← rv_mul, mul_one]

/-- Multiplying by an element of the residue class of `1` does not change the `rv`-class. -/
theorem rv_mul_of_rv_eq_one {c y : K} (hy : rv v y = rv v 1) : rv v (c * y) = rv v c := by
  rw [rv_mul, hy]
  by_cases hc : rv v c = rvZero v
  · rw [hc]; rfl
  · exact rvMul_rv_one hc

/-- Two elements of the same `rv`-class have quotient in the class of `1`. -/
theorem rv_div_of_rv_eq {a c : K} (hc : c ≠ 0) (h : rv v a = rv v c) : rv v (a / c) = rv v 1 := by
  obtain ⟨hval, hlt⟩ := (rv_eq_iff hc).1 h
  rw [rv_eq_iff (v := v) (x := a / c) (y := 1) one_ne_zero]
  constructor
  · rw [Valuation.map_div, hval, div_self (by rwa [Valuation.ne_zero_iff]), Valuation.map_one]
  · simpa using hlt

/-- **The `\bar\gamma`-polynomial structure after normalizing**: if `F` is a
`\bar\gamma`-polynomial with residue value `α`, `\rv(c_j) = t_j` and `\vv(e) = -α`, then
`e·F(cY)` is a `\bar 0`-polynomial with residue value `0` (in `Γ₀`: all coefficients have
value `1`). -/
theorem isGammaPoly_scaled {n : ℕ} {F : MvPolynomial (Fin n) K} {t : Fin n → RV v} {αx : Γ₀}
    {c : Fin n → K} {e : K} (hF : IsGammaPoly v t αx F) (hα0 : αx ≠ 0)
    (hc : ∀ j, v (c j) = vrv v (t j)) (he : v e = αx⁻¹) :
    IsGammaPoly v (fun _ => rv v 1) 1 (MvPolynomial.C e * diagScale c F) := by
  intro m hm
  have hm' : m ∈ F.support := by
    rw [MvPolynomial.mem_support_iff] at hm ⊢
    intro h0
    exact hm (by rw [MvPolynomial.coeff_C_mul, diagScale_coeff, h0, zero_mul, mul_zero])
  have h1 := hF m hm'
  have hw : gammaWeight v (fun _ => rv v 1) m = 1 := by
    rw [gammaWeight, Finsupp.prod]
    refine Finset.prod_eq_one fun j _ => ?_
    rw [vrv_rv, map_one, one_pow]
  have hc' : (m.prod fun j e' => (v (c j)) ^ e') = gammaWeight v t m := by
    rw [gammaWeight]
    exact Finsupp.prod_congr fun j _ => by rw [hc j]
  calc v ((MvPolynomial.C e * diagScale c F).coeff m) * gammaWeight v (fun _ => rv v 1) m
      = v e * (v (F.coeff m) * (m.prod fun j e' => (v (c j)) ^ e')) := by
        rw [MvPolynomial.coeff_C_mul, diagScale_coeff, map_mul, map_mul, v_finsupp_prod, hw,
          mul_one]
    _ = v e * αx := by rw [hc', h1]
    _ = 1 := by rw [he, inv_mul_cancel₀ hα0]

/-- **The residue-root property after normalizing**: if `\bar t` is a residue root of `F` and
`\rv(c_j) = t_j`, `\vv(e) = -α`, then `(1,…,1)` is a residue root of `e·F(cY)`. -/
theorem isResidueRoot_scaled {n : ℕ} {F : MvPolynomial (Fin n) K} {t : Fin n → RV v}
    {αx : Γ₀} {c : Fin n → K} {e : K} (hF : IsResidueRoot v t αx F)
    (hc : ∀ j, rv v (c j) = t j) (he : v e = αx⁻¹) :
    IsResidueRoot v (fun _ => rv v 1) 1 (MvPolynomial.C e * diagScale c F) := by
  have hα0 : αx ≠ 0 := by
    intro h0
    have hv := hF c hc
    rw [h0] at hv
    exact absurd hv (not_lt.mpr (zero_le))
  intro y hy
  rw [MvPolynomial.eval_mul, MvPolynomial.eval_C, eval_diagScale, map_mul, he]
  have hw : v ((F).eval fun j => c j * y j) < αx :=
    hF (fun j => c j * y j) fun j => by rw [rv_mul_of_rv_eq_one (hy j), hc j]
  have hstep : αx⁻¹ * v ((F).eval fun j => c j * y j) < αx⁻¹ * αx :=
    mul_lt_mul_of_pos_left hw (inv_pos.mpr (zero_lt_iff.mpr hα0))
  rwa [inv_mul_cancel₀ hα0] at hstep

end Transport

/-! ### The Jacobian value and the reduction to the normalized Hensel lemma -/

section Reduction

variable {v : Valuation K Γ₀}

/-- `vrv` does not vanish off `\rv 0`. -/
theorem vrv_ne_zero {t : RV v} (ht : t ≠ rvZero v) : vrv v t ≠ 0 := by
  cases t with
  | none => exact absurd rfl ht
  | some q =>
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (princUnits v) q
    rw [vrv_mk]
    intro h
    exact ((Valuation.ne_zero_iff v).mpr (Units.ne_zero u)) h

/-- The value of the scaled Jacobian determinant. -/
theorem val_jacDet_scaled {n : ℕ} (F : Fin n → MvPolynomial (Fin n) K) (c e y : Fin n → K) :
    v ((jacDet (fun i => MvPolynomial.C (e i) * diagScale c (F i))).eval y)
      = (∏ i, v (e i) * v (c i)) * v ((jacDet F).eval fun j => c j * y j) := by
  rw [jacDet_eval_scaled, map_mul, v_finset_prod]
  congr 1
  exact Finset.prod_congr rfl fun i _ => map_mul ..

/-- Elementary `Γ₀` arithmetic used for the "not a residue root" transport:
`(P⁻¹G)W < 1` gives `W < PG⁻¹`. -/
theorem lt_of_mul_inv_mul_lt_one {P G W : Γ₀} (hP : P ≠ 0) (hG : G ≠ 0)
    (h : (P⁻¹ * G) * W < 1) : W < P * G⁻¹ := by
  have hPG : P⁻¹ * G ≠ 0 := mul_ne_zero (inv_ne_zero hP) hG
  have hstep : (P⁻¹ * G)⁻¹ * ((P⁻¹ * G) * W) < (P⁻¹ * G)⁻¹ * 1 :=
    mul_lt_mul_of_pos_left h (inv_pos.mpr (zero_lt_iff.mpr hPG))
  rw [← mul_assoc, inv_mul_cancel₀ hPG, one_mul, mul_one, mul_inv_rev, inv_inv] at hstep
  simpa [mul_comm] using hstep

/-- **The "simple root" property after normalizing**: if `\bar t` is not a residue root of the
Jacobian determinant of `F`, then `(1,…,1)` is not a residue root of the Jacobian determinant
of `e_iF_i(cY)`.  This is the half of Definition 7.1's third item that the paper computes
with `\vv(\det ∂F^*/\partial Y) = \sum_i\alpha_i - \sum_i\delta_i`. -/
theorem not_isResidueRoot_jacDet_scaled {n : ℕ} {F : Fin n → MvPolynomial (Fin n) K}
    {t : Fin n → RV v} {α : Fin n → Γ₀} {c e : Fin n → K}
    (h : ¬ IsResidueRoot v t ((∏ i, α i) * (∏ j, vrv v (t j))⁻¹) (jacDet F))
    (hc : ∀ j, rv v (c j) = t j) (he : ∀ i, v (e i) = (α i)⁻¹)
    (hα : ∀ i, α i ≠ 0) (ht : ∀ j, t j ≠ rvZero v) :
    ¬ IsResidueRoot v (fun _ => rv v 1) 1
      (jacDet (fun i => MvPolynomial.C (e i) * diagScale c (F i))) := by
  intro hcontra
  apply h
  intro a ha
  have hcne : ∀ j, c j ≠ 0 := by
    intro j h0
    have h1 := hc j
    rw [h0, rv_zero] at h1
    exact ht j h1.symm
  have hy : ∀ j, rv v (a j / c j) = rv v 1 := fun j =>
    rv_div_of_rv_eq (hcne j) (by rw [ha j, hc j])
  have hay : (fun j => c j * (a j / c j)) = a := by
    funext j
    rw [mul_comm, div_mul_cancel₀ _ (hcne j)]
  have h1 : v ((jacDet (fun i => MvPolynomial.C (e i) * diagScale c (F i))).eval
      (fun j => a j / c j)) < 1 := hcontra (fun j => a j / c j) hy
  rw [val_jacDet_scaled, hay] at h1
  have hprod : (∏ i, v (e i) * v (c i)) = (∏ i, α i)⁻¹ * (∏ j, vrv v (t j)) := by
    rw [Finset.prod_mul_distrib]
    congr 1
    · rw [Finset.prod_congr rfl fun i _ => he i, Finset.prod_inv_distrib]
    · exact Finset.prod_congr rfl fun j _ => by rw [← vrv_rv (v := v), hc j]
  rw [hprod] at h1
  have hP : (∏ i, α i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hα i
  have hG : (∏ j, vrv v (t j)) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => vrv_ne_zero (ht j)
  exact lt_of_mul_inv_mul_lt_one hP hG h1

end Reduction

/-! ### `hensel:lemma` from its normalized form -/

section Main

variable {v : Valuation K Γ₀}

/-- **The paper's proof of `hensel:lemma`.**  *"Without loss of generality we may work in a
topologically complete submodel of `\ACVF` of rank `1`.  Fix a simple common residue root
`\bar t` ... Choose a `c_i ∈ \rv^{-1}(t_i)`.  Changing the coefficients accordingly we may
rewrite each `F_i(\bar X)` as `F_i(X_1/c_1, …, X_n/c_n)`.  Write `Y_i` for `X_i/c_i`.  Note
that, for each `i`, the coefficients of the `\bar 0`-polynomial `F_i(\bar Y)` are all of the
same value `α_i`.  For each `i` choose an `e_i ∈ \VF` with `\vv(e_i) = -α_i`.  We have that
each `\bar 0`-polynomial `F^*_i(\bar Y) = e_iF_i(\bar Y)` has residue value `0` ... Clearly
`(1,…,1)` is a common residue root ... It is actually a simple root because ...  Now the
lemma follows from the multivariate version of Hensel's lemma."*

So: the generalized Hensel lemma for `\bar t ∈ (\RV^\times)^n` follows from the normalized
Bourbaki form `NormalizedHensel v`, given that every value in `Γ₀` is attained by `v`
(`Γ` is the value group, i.e. `\vrv` is onto `\Gamma \setminus \{\infty\}`). -/
theorem hensLemmaUnits_of_normalized (hn : NormalizedHensel v)
    (hsurj : ∀ γ : Γ₀, γ ≠ 0 → ∃ x : K, v x = γ) : HenselLemmaUnits v := by
  intro n F t α ht h
  classical
  -- choose `c_i ∈ rv^{-1}(t_i)`
  choose c hcne hcrv using fun j => rv_surjective (v := v) (ht j)
  -- the residue values are nonzero (they dominate `v(F_i(c))`)
  have hα : ∀ i, α i ≠ 0 := by
    intro i h0
    have hv := h.2.1 i c hcrv
    rw [h0] at hv
    exact absurd hv (not_lt.mpr (zero_le : (0 : Γ₀) ≤ v ((F i).eval c)))
  -- choose `e_i` with `vv(e_i) = -α_i`
  choose e he using fun i => hsurj (α i)⁻¹ (inv_ne_zero (hα i))
  -- the normalized system and its simple common residue root `(1,…,1)`
  have hsimple : IsSimpleCommonResidueRoot v (fun _ => rv v 1) (fun _ => (1 : Γ₀))
      (fun i => MvPolynomial.C (e i) * diagScale c (F i)) := by
    refine ⟨?_, ?_, ?_⟩
    · intro i
      exact isGammaPoly_scaled (h.1 i) (hα i) (fun j => by rw [← vrv_rv (v := v), hcrv j])
        (he i)
    · intro i
      exact isResidueRoot_scaled (h.2.1 i) hcrv (he i)
    · have hsub : (∏ i : Fin n, (1 : Γ₀)) * (∏ j : Fin n, vrv v (rv v 1))⁻¹ = 1 := by
        have h2 : (∏ j : Fin n, vrv v (rv v 1)) = 1 := by
          refine Finset.prod_eq_one fun j _ => ?_
          rw [vrv_rv, map_one]
        rw [h2, inv_one, mul_one]
        exact Finset.prod_const_one
      rw [hsub]
      exact not_isResidueRoot_jacDet_scaled h.2.2 hcrv he hα ht
  obtain ⟨y, hy, hyuniq⟩ := hn n (fun i => MvPolynomial.C (e i) * diagScale c (F i)) hsimple
  have hene : ∀ i, e i ≠ 0 := by
    intro i h0
    have hh := he i
    rw [h0, map_zero] at hh
    exact inv_ne_zero (hα i) hh.symm
  refine ⟨fun j => c j * y j, ⟨?_, ?_⟩, ?_⟩
  · intro j
    rw [rv_mul_of_rv_eq_one (hy.1 j), hcrv j]
  · intro i
    have h0 := hy.2 i
    simp only [MvPolynomial.eval_mul, MvPolynomial.eval_C, eval_diagScale] at h0
    exact (mul_eq_zero.mp h0).resolve_left (hene i)
  · intro a ha
    let z : Fin n → K := fun j => a j / c j
    have hzfib : ∀ j, rv v (z j) = rv v 1 := fun j =>
      rv_div_of_rv_eq (hcne j) (by rw [ha.1 j, hcrv j])
    have hzzero : ∀ i, (MvPolynomial.C (e i) * diagScale c (F i)).eval z = 0 := by
      intro i
      rw [MvPolynomial.eval_mul, MvPolynomial.eval_C, eval_diagScale]
      have hcz : (fun j => c j * z j) = a := by
        funext j
        show c j * (a j / c j) = a j
        rw [mul_comm, div_mul_cancel₀ _ (hcne j)]
      rw [hcz, ha.2 i, mul_zero]
    have hzy : z = y := hyuniq z ⟨hzfib, hzzero⟩
    funext j
    have h1 : a j / c j = y j := congrFun hzy j
    show a j = c j * y j
    rw [← h1, mul_comm, div_mul_cancel₀ _ (hcne j)]

end Main

/-- `HenselLemma` (with no restriction on `\bar t`) implies the `(\RV^\times)^n` form. -/
theorem henselLemmaUnits_of_henselLemma (h : HenselLemma v) : HenselLemmaUnits v :=
  fun n F t α _ hh => h n F t α hh

/-- The weight of a multi-index at `\bar 1 = (1,…,1)` is `1`: the `\bar 0`-case of
`gammaWeight`. -/
theorem gammaWeight_one {n : ℕ} (m : Fin n →₀ ℕ) :
    gammaWeight v (fun _ : Fin n => rv v 1) m = 1 := by
  rw [gammaWeight, Finsupp.prod]
  refine Finset.prod_eq_one fun j _ => ?_
  rw [vrv_rv, map_one, one_pow]

/-- **The paper's remark after Definition 7.1**: *"according to this definition, every
polynomial in `\K[\bar X]` is the projection of a `\bar 0`-polynomial `F(\bar X)` with residue
value `0`"*.  A polynomial all of whose nonzero coefficients have value `1` (`\vv = 0`) is a
`\bar 0`-polynomial with residue value `0` (`1` in `Γ₀`). -/
theorem isGammaPoly_zero_of_coeff_val_one {n : ℕ} {F : MvPolynomial (Fin n) K}
    (h : ∀ m ∈ F.support, v (F.coeff m) = 1) :
    IsGammaPoly v (fun _ => rv v 1) 1 F := by
  intro m hm
  rw [h m hm, gammaWeight_one, mul_one]

end Sec7

/-! ### Axiom footprints -/

#print axioms Sec7.jacDet_eval_scaled
#print axioms Sec7.diagScale_coeff
#print axioms Sec7.pderiv_diagScale
#print axioms Sec7.not_isResidueRoot_jacDet_scaled
#print axioms Sec7.hensLemmaUnits_of_normalized
#print axioms Sec7.henselLemmaUnits_of_henselLemma
