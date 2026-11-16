module

/-
Section 8 of Yin, "Special transformations in algebraically closed valued fields"
(arXiv:1006.2467): `fun:dim:1:val:cons` (`paper.tex:1746`) and `rad:equal:1` (`paper.tex:1772`).
Swarm `smw1kl4vz`, direction d6.  `lean Sec8.lean` exits 0, no `sorry`, no `native_decide`, and
every theorem reported below has axioms exactly `[propext, Classical.choice, Quot.sound]`.

## What is proved, and what is carried

§8 is written in the paper's notation `vv`, `Γ`, `⦰(ā, γ)`, `fib(A, b̄)`, "`ā`-definable", none of
which exists in `Milestone0/Encoding.lean` (whose radii are `RV`-elements and whose order is the
preorder `iLe`).  So the first part of the file builds that notation as an **explicit hypothesis
structure** (never an axiom) and proves its elementary facts; then the two lemmas are stated in the
paper's own words, with every gap named as a separate `Prop` and the parts that are within reach
proved.

**1. The value layer** (`Sec8.ValLayer`): `Γ` an ordered additive `ℚ`-vector space (the paper's
`ACVF` has divisible value group: `Axioms.ACVF00Γ`'s `gDivisible`, `Encoding.lean:1697`, which is
what `k vv(·)` for `k ∈ ℚ` needs), `vv x y` = the paper's `vv(x - y)` into `WithTop Γ = Γ ∪ {∞}`
with `∞` on top, `vrv` = the value of an `RV`-element (`RV ∖ {rv 0} ≅ Γ`; `iRVZero` is `∞`,
`Axioms.leTop`/`leInftyEq`), and `iLe = ≤` (`vrv_le`).  It is inhabited (`valLayerPUnit`).

Proved about it: `oBall_isOpenBall` — **the paper's `⦰(a, t) = {x : vv(x - a) > t}` really is an
open ball in the frozen encoding's sense** (`LRV.IsOpenBall`) — with `oBall_subset_vf`,
`oBall_antitone`, `oBall_self_mem`, `oBall_eq_empty_of_vrv_top`, `oBall_congr`, `oPoly_antitone`,
`oPoly_self_mem`, `oBallTup_antitone`, `oBallTup_self_mem`, `smulTop_one`, `smulTop_mul`.

**2. Bookkeeping** (all proved): `consTup`/`headTup`/`tailTup` with `consTup_zero`,
`consTup_succ`, `consTup_head_tail`, `tailTup_consTup`; `fib`/`fibreCompl` (the paper's
`fib(A, b̄)` and `VF ∖ fib(A, b̄)`); `mkTup1`/`coord1` for `VF^1`; `fibreFun f b` for the paper's
`f ↾ VF × {b̄}`; `dclRV`/`dclRVAt` for "`t` is definable" and "`t` is `ā`-definable" at the `RV`
sort (`SP.dcl` is `VF`-sorted only).

**3. The paper's "almost everywhere"** (`AlmostEverywhere S A P`) with `AlmostEverywhere.mono`,
`almostEverywhere_of_forall`, `dimVF_empty`, `hasDim_empty`, `Definable.empty`.

**4. `fun_dim_1_val_cons`** (`ValConsConcl` is the paper's conclusion, sentence for sentence).
The theorem *constructs* `A`: it is the paper's own
`A = VF^{k+1} ∖ ⋃_{b̄} B_b̄` (`goodSet f`, with `B_b̄ = pointIsolatedSet (fibreFun f b)`).  Its
conclusion 1 — *"`VF ∖ fib(A, b̄)` is finite for all `b̄ ∈ VF^k`"* — is **proved**
(`fibreCompl_goodSet_finite`) from

* `hIso : IsoFibres S f` — §8's `iso:point:dim:less` for the fibres `f ↾ VF × {b̄}` (the §8 lemma
  this file waits on; its general statement is `IsoPointDimLess`, with the paper's sentence), plus
  definability of `B_b̄`;
* `hDim0 : DimZeroFiniteVF1 S` — the `C`-minimality fact that a definable subset of `VF` of
  dimension `0` is finite (§3/§4 content; `QE/Sec3_sat.lean`'s `IsCMinimalWS` is a `sorry`ed frozen
  target and §4's dimension layer does not derive finiteness from `dim_VF = 0`).

The two remaining hypotheses are the §8 residuals, named with the paper's sentences:
`CanonicalDefinable S f` (*"By compactness `A = VF^{k+1} ∖ ⋃_{b̄} B_b̄` is definable"*) and
`DominatingTerm S f` = `LocalLawPointwise S f ∧ ExponentsFinite f` (the second paragraph: *"there is
an `ε ∈ Γ ∪ {∞}` and a rational number `k ≥ 0` such that ... `Z = ε + k vv(X)`; since `Γ` is
`o`-minimal, `ε` and some `δ` are `ā`-definable"*, and *"the number `k` is provided by the exponents
of `X₁` in `φ(X₁, X₂, Ȳ, Z)` and hence there are only finitely many choices"*).

**5. `rad_equal_one`** (the paper's conclusion).  Residuals, again with the paper's sentences:
`PowerLaw S f 𝔞 q` (*"By the proof of Lemma `fun:dim:1:val:cons` we may assume that there is a
definable `ε ∈ Γ` and a positive rational number `k` such that `vv(f(a)) = ε + k vv(a)`"*) and
`ExponentIntegral q` (*"we conclude that `k` must be a positive integer.  Symmetrically `1/k` is
also a positive integer"*, the division-algorithm paragraph).  The paper's last inference is
**proved**: `expIntegral_eq_one` (`q`, `q⁻¹` both positive integers `⟹ q = 1`), and `smulTop_one`
turns `1 vv(·)` into `vv(·)`; hence `vv(f(a)) = ε + vv(a)` on `⦰(0, γ)` with `γ = ta`.

## The exact statements that are still open

* `IsoPointDimLess` / `IsoFibres` — §8's `iso:point:dim:less`, with its `n = 1` case, over §4's
  dimension layer (being produced by member m6 of this swarm).
* `DimZeroFiniteVF1` — a definable `B ⊆ VF` with `dim_VF(B) < 1` is finite (C-minimality + §4).
* `CanonicalDefinable` — the compactness/uniformity step: one formula defines `goodSet f` for all
  `b̄` at once.
* `LocalLawPointwise`, `ExponentsFinite`, `PowerLaw`, `ExponentIntegral` — the two paragraphs of
  `fun:dim:1:val:cons`'s proof and the two sentences of `rad:equal:1`'s proof, quoted verbatim in
  their docstrings.
-/
public import Sec4Dim

@[expose] public section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
open FirstOrder FirstOrder.Language

namespace SpecialTransformations.Milestone0
open LRV

namespace Sec8

open Sec4Dim

variable {M : Type*} [LRV.Structure M]

/-! ## Reading the coordinates of a tuple -/

theorem Tup.vf_mem {n : ℕ} (x : Tup M n 0) (j : Fin n) : iVF (x (Sum.inl j)) :=
  x.property (Sum.inl j)

theorem Tup.rv_mem {m : ℕ} (x : Tup M 0 m) (j : Fin m) : iRV (x (Sum.inr j)) :=
  x.property (Sum.inr j)

/-! ## The `VF`-zero and the set `Γ` of finite radii -/

/-- The interpretation of `0` of the `VF` sort.  (`Milestone0/Encoding.lean` names the two `RV`
constants `iRVOne`/`iRVZero` but not this one; `QE/Sec3_sat.lean` has the same definition under
`SP.iVFZero`, and that file cannot be imported without its frozen `sorry`s, so it is repeated
here.) -/
def iVFZero : M := FirstOrder.Language.Structure.funMap (L := LRV) Fn.vfZero fun i => i.elim0

/-- **`t ∈ Γ`**: the paper's value group, as coded in `L_RV`.  `DECISION.md`: `Γ` is the
definable quotient `RV^× / K^×`, and the encoding writes its elements as `RV`-elements `≠ rv 0`;
`iRVZero` is the paper's `∞` (`Axioms.leTop`/`leInftyEq` in `Milestone0/Encoding.lean`: `∞` is
the top of the order).  So `t ∈ Γ` is `iRV t ∧ t ≠ iRVZero`. -/
def isGamma (t : M) : Prop := iRV t ∧ t ≠ iRVZero

theorem isGamma.rv {t : M} (h : isGamma t) : iRV t := h.1

theorem isGamma.ne_zero {t : M} (h : isGamma t) : t ≠ iRVZero := h.2

/-! ## The value layer

The paper writes `vv` for the valuation `VF → Γ ∪ {∞}`, with `vv 0 = ∞` (`paper.tex:586`), and
compares `vv(x - a)` with radii.  `ValLayer M Γ` bundles that data with its laws.  Everything in
it is a *hypothesis*: it is what §1–§6 (and the encoding's `Axioms.ACVF`) give, and it is
inhabited (see `instValLayerUnit` at the end of the file), so no statement below is vacuous. -/

/-- **The paper's value layer over the frozen encoding.**

* `Γ` is the paper's value group, ordered and written *additively* as Section 8 writes it
  (`ε + k vv(a' - a)`, `vv(X) > δ`), with `ℚ`-scalar multiplication (the group is divisible);
* `vv x y` is the paper's `vv(x - y)`, valued in `WithTop Γ` — the paper's `Γ ∪ {∞}` with `∞`
  the top (`paper.tex:586`: `⦰(ā, ∞) = {ā}`, and `Axioms.leTop`);
* `vrv t` is the value of the `RV`-element `t`; on `rv`-images it agrees with `vv`
  (`vrv_rv`), `vrv` sends `iRVZero` — the paper's `∞` — to `⊤` (`vrv_zero`) and nothing else
  (`vrv_eq_top`), and the encoding's preorder `iLe` on `RV` is `≤` of `Γ ∪ {∞}` (`vrv_le`).

The fields `vf_zero`, `vf_sub`, `rv_sorted` are the encoding-side bookkeeping (the `VF` sort
contains `0` and is closed under subtraction; `rv` maps `VF` into `RV`); the last three of these
are facts about `Milestone0.Encoding`'s symbols that `Encoding.lean` states only inside
`Axioms.ACVF`, not as `LRV.Structure` fields. -/
structure ValLayer (M : Type*) [LRV.Structure M] (Γ : Type*)
    [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] [_root_.SMul ℚ Γ] where
  /-- `Γ` is closed under multiplication by rationals (the paper's `ACVF` has divisible value
  group: `Axioms.ACVF00Γ`'s `gDivisible`, `Encoding.lean:1697`). -/
  smul_one : ∀ γ : Γ, (1 : ℚ) • γ = γ
  smul_mul : ∀ (k k' : ℚ) (γ : Γ), (k * k') • γ = k • (k' • γ)
  /-- `k γ` on `Γ ∪ {∞}`, `∞` absorbing: the paper's `k vv(·)` when `vv(·)` may be `∞`. -/
  smulTop : ℚ → WithTop Γ → WithTop Γ
  smulTop_coe : ∀ (q : ℚ) (γ : Γ), smulTop q (γ : WithTop Γ) = ((q • γ : Γ) : WithTop Γ)
  smulTop_top : ∀ q : ℚ, smulTop q ⊤ = ⊤
  /-- the paper's `vv(x - y)`, valued in `Γ ∪ {∞}` -/
  vv : M → M → WithTop Γ
  /-- the value of an `RV`-element -/
  vrv : M → WithTop Γ
  /-- the `VF`-sort contains `0` -/
  vf_zero : iVF (iVFZero (M := M))
  /-- the `VF`-sort is closed under subtraction -/
  vf_sub : ∀ x y : M, iVF x → iVF y → iVF (iVFAdd x (iVFNeg y))
  /-- `rv` maps the `VF`-sort into the `RV`-sort -/
  rv_sorted : ∀ x : M, iVF x → iRV (iRv x)
  /-- `vv(x - x) = ∞` -/
  vv_self : ∀ x : M, iVF x → vv x x = ⊤
  /-- `vv(x - y) = vv(y - x)` -/
  vv_sym : ∀ x y : M, iVF x → iVF y → vv x y = vv y x
  /-- the ultrametric inequality for `vv(· - ·)` -/
  vv_ultra : ∀ x y z : M, iVF x → iVF y → iVF z → min (vv x y) (vv y z) ≤ vv x z
  /-- `rv(x - y)` has value `vv(x - y)`: the projection `RV^× → Γ` is `vrv` -/
  vrv_rv : ∀ x y : M, iVF x → iVF y → vrv (iRv (iVFAdd x (iVFNeg y))) = vv x y
  /-- the paper's `∞`, i.e. `rv 0`, has value `∞` -/
  vrv_zero : vrv (iRVZero) = ⊤
  /-- `∞` is the only `RV`-element of value `∞` -/
  vrv_eq_top : ∀ t : M, iRV t → vrv t = ⊤ → t = iRVZero
  /-- the encoding's preorder `iLe` on `RV` is `≤` of `Γ ∪ {∞}` -/
  vrv_le : ∀ t s : M, iRV t → iRV s → (iLe t s ↔ vrv t ≤ vrv s)

namespace ValLayer

variable {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] [_root_.SMul ℚ Γ]
  (V : ValLayer M Γ)

/-! ## The open balls and polydiscs of `paper.tex:586` -/

/-- **The paper's `⦰(a, t)`**, for a *finite* radius `t ∈ Γ`: `paper.tex:586`,
"the open polydisc `{(b₁, …, bₙ) : vv(bᵢ - aᵢ) > γᵢ}` is denoted by `⦰(ā, γ̄)`", in dimension
one: `{x ∈ VF : vv(x - a) > t}`, written with `vv(· - ·)`.

For the paper's `∞` the paper has the separate convention `⦰(a, ∞) = {a}`; this definition gives
`∅` there (no value exceeds `⊤`), and `oBallTop` below is the convention.  Every use in Section 8
takes `t ∈ Γ` (`isGamma t`). -/
def oBall (a t : M) : Set M := {x | iVF x ∧ V.vrv t < V.vv x a}

/-- **The paper's convention `⦰(a, ∞) = {a}`** (`paper.tex:586`). -/
def oBallTop (a : M) : Set M := {a}

/-- **The paper's `⦰(ā, γ) ⊆ VF^n`**: the polydisc of constant radius `γ` (`paper.tex:556`,
`paper.tex:586`). -/
def oPoly {n : ℕ} (a : Tup M n 0) (t : M) : Set (Tup M n 0) :=
  {x | ∀ i, V.vrv t < V.vv (x i) (a i)}

/-- `⦰(a, t)` is contained in the `VF`-sort. -/
theorem oBall_subset_vf (a t : M) : V.oBall a t ⊆ {x | iVF x} := fun x hx => hx.1

/-- **`⦰(a, t)` is an *open ball* in the frozen encoding's sense** (`LRV.IsOpenBall` in
`Milestone0/Encoding.lean`): the two notions of open ball — the paper's `vv`-ball and the
encoding's `iLe`-ball — agree, through `vrv_le` and `vrv_rv`.

This is the point `QE/Sec3Infra.lean` records as a trap: `rv`-fibres are *not* closed balls in this
encoding.  `vv`-balls are open balls, and that is what Section 8 uses. -/
theorem oBall_isOpenBall (a t : M) (ha : iVF a) (ht : isGamma t) :
    IsOpenBall (V.oBall a t) := by
  refine Or.inl ⟨a, t, ha, ht.1, ht.2, ?_⟩
  have key : ∀ x : M, iVF x →
      (V.vrv t < V.vv x a ↔
        iLe t (iRv (iVFAdd x (iVFNeg a))) ∧ ¬ iLe (iRv (iVFAdd x (iVFNeg a))) t) := by
    intro x hx
    have hsub : iVF (iVFAdd x (iVFNeg a)) := V.vf_sub x a hx ha
    have h1 := V.vrv_le t (iRv (iVFAdd x (iVFNeg a))) ht.1 (V.rv_sorted _ hsub)
    have h2 := V.vrv_le (iRv (iVFAdd x (iVFNeg a))) t (V.rv_sorted _ hsub) ht.1
    rw [V.vrv_rv x a hx ha] at h1 h2
    constructor
    · intro h
      have hle : V.vrv t ≤ V.vv x a := le_of_lt h
      refine ⟨h1.mpr hle, ?_⟩
      intro hcon
      have hc : V.vv x a ≤ V.vrv t := h2.mp hcon
      exact absurd hc (not_le.mpr h)
    · rintro ⟨h1', h2'⟩
      have hle : V.vrv t ≤ V.vv x a := h1.mp h1'
      have hnle : ¬ (V.vv x a ≤ V.vrv t) := fun hc => h2' (h2.mpr hc)
      exact lt_of_le_of_ne hle (fun he => hnle (le_of_eq he.symm))
  ext x
  simp only [oBall, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hx, h⟩
    exact ⟨hx, (key x hx).1 h⟩
  · rintro ⟨hx, h⟩
    exact ⟨hx, (key x hx).2 h⟩

/-- **`⦰(·, t)` is antitone in the radius**: a larger radius gives a smaller ball
(`paper.tex:586`; this is what "`rad(𝔟) > γ`" means in the proof of `points:apart:fin`). -/
theorem oBall_antitone {a t t' : M} (h : V.vrv t ≤ V.vrv t') : V.oBall a t' ⊆ V.oBall a t := by
  rintro x ⟨hx, hlt⟩
  exact ⟨hx, lt_of_le_of_lt h hlt⟩

/-- The centre lies in every open ball of finite radius: `a ∈ ⦰(a, t)` for `t ∈ Γ`. -/
theorem oBall_self_mem {a t : M} (ha : iVF a) (ht : isGamma t) : a ∈ V.oBall a t := by
  refine ⟨ha, ?_⟩
  rw [V.vv_self a ha]
  exact lt_of_le_of_ne le_top (fun h => ht.2 (V.vrv_eq_top t ht.1 h))

/-- `⦰(a, t)` is empty as soon as `t` has value `∞` (the paper's convention replaces it by
`{a}`; see `oBallTop`). -/
theorem oBall_eq_empty_of_vrv_top {a t : M} (h : V.vrv t = ⊤) : V.oBall a t = ∅ := by
  ext x
  simp only [oBall, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro _
  rw [h]
  exact not_lt.mpr le_top

/-- `oBall` depends on the radius only through its value. -/
theorem oBall_congr {a t t' : M} (h : V.vrv t = V.vrv t') : V.oBall a t = V.oBall a t' := by
  ext x
  simp only [oBall, Set.mem_ofPred_eq, h]

/-! ## The polydiscs -/

/-- **`⦰(·, t)` is antitone in the radius**, tuple form. -/
theorem oPoly_antitone {n : ℕ} {a : Tup M n 0} {t t' : M} (h : V.vrv t ≤ V.vrv t') :
    V.oPoly a t' ⊆ V.oPoly a t := by
  rintro x hx i
  exact lt_of_le_of_lt h (hx i)

/-- The centre lies in every polydisc of finite radius. -/
theorem oPoly_self_mem {n : ℕ} {a : Tup M n 0} {t : M} (ht : isGamma t) :
    a ∈ V.oPoly a t := by
  intro i
  match i with
  | Sum.inl j =>
    show V.vrv t < V.vv (a (Sum.inl j)) (a (Sum.inl j))
    rw [V.vv_self _ (Tup.vf_mem a j)]
    exact lt_of_le_of_ne le_top (fun h => ht.2 (V.vrv_eq_top t ht.1 h))
  | Sum.inr j => exact j.elim0

/-- Membership in `⦰(ā, t)`, unfolded. -/
theorem oPoly_mem_iff {n : ℕ} {a x : Tup M n 0} {t : M} :
    x ∈ V.oPoly a t ↔ ∀ i, V.vrv t < V.vv (x i) (a i) := Iff.rfl

/-! ## Scalar multiplication on `Γ ∪ {∞}`

`WithTop Γ` has no `SMul ℚ` instance in this Mathlib, so `ValLayer` carries the action as data
(`smulTop`) together with the two laws below, which are what the paper's `k vv(·)` needs when the
value is `∞`. -/

theorem smulTop_one (x : WithTop Γ) : V.smulTop 1 x = x := by
  match x with
  | ⊤ => exact V.smulTop_top 1
  | (γ : Γ) => rw [V.smulTop_coe, V.smul_one]

theorem smulTop_mul (k k' : ℚ) (x : WithTop Γ) :
    V.smulTop (k * k') x = V.smulTop k (V.smulTop k' x) := by
  match x with
  | ⊤ => rw [V.smulTop_top, V.smulTop_top, V.smulTop_top]
  | (γ : Γ) => simp only [V.smulTop_coe, V.smul_mul]

/-! ## The paper's `VF^1` and `⦰(0, t) ⊆ VF^1` -/

/-- The single `VF`-coordinate of an element of the paper's `VF^1`. -/
def coord1 (x : Tup M 1 0) : M := x (Sum.inl 0)

/-- **`⦰(0, t) ⊆ VF^1`**, the open ball around `0` in the paper's `VF^1` (`paper.tex:586`). -/
def oBallTup (t : M) : Set (Tup M 1 0) :=
  {x | V.vrv t < V.vv (coord1 x) (iVFZero (M := M))}

theorem oBallTup_antitone {t t' : M} (h : V.vrv t ≤ V.vrv t') :
    V.oBallTup t' ⊆ V.oBallTup t := by
  rintro x hx
  exact lt_of_le_of_lt h hx

theorem oBallTup_self_mem {t : M} (ht : isGamma t) :
    (⟨fun _ => iVFZero (M := M), by
      intro i
      match i with
      | Sum.inl j => exact V.vf_zero
      | Sum.inr j => exact j.elim0⟩ : Tup M 1 0) ∈ V.oBallTup t := by
  show V.vrv t < V.vv (iVFZero (M := M)) (iVFZero (M := M))
  rw [V.vv_self _ V.vf_zero]
  exact lt_of_le_of_ne le_top (fun h => ht.2 (V.vrv_eq_top t ht.1 h))

end ValLayer

/-! ## Tuples: `(a, b̄) ∈ VF × VF^k`, and the fibres `fib(A, b̄)` -/

/-- The underlying function of `consTup`: `(a, b̄)` as a function on `Fin (k+1)`. -/
def consFun {k : ℕ} (a : M) (b : Tup M k 0) (j : Fin (k+1)) : M :=
  Fin.cases a (fun t => b (Sum.inl t)) j

@[simp] theorem consFun_zero {k : ℕ} (a : M) (b : Tup M k 0) : consFun a b 0 = a := rfl

@[simp] theorem consFun_succ {k : ℕ} (a : M) (b : Tup M k 0) (j : Fin k) :
    consFun a b (Fin.succ j) = b (Sum.inl j) := rfl

/-- **`(a, b̄)`**: the paper's pairing of `a ∈ VF` with `b̄ ∈ VF^k` as the first and remaining
coordinates of a tuple in `VF^{k+1}`. -/
def consTup {k : ℕ} (a : M) (ha : iVF a) (b : Tup M k 0) : Tup M (k+1) 0 :=
  ⟨fun i => match i with
    | Sum.inl j => consFun a b j
    | Sum.inr j => j.elim0, by
      intro i
      match i with
      | Sum.inl j =>
        show iVF (consFun a b j)
        induction j using Fin.cases with
        | zero => simpa using ha
        | succ t => simpa using Tup.vf_mem b t
      | Sum.inr j => exact j.elim0⟩

@[simp] theorem consTup_zero {k : ℕ} (a : M) (ha : iVF a) (b : Tup M k 0) :
    consTup a ha b (Sum.inl 0) = a := rfl

@[simp] theorem consTup_succ {k : ℕ} (a : M) (ha : iVF a) (b : Tup M k 0) (j : Fin k) :
    consTup a ha b (Sum.inl (Fin.succ j)) = b (Sum.inl j) := rfl

/-- The first coordinate of a tuple in `VF^{k+1}`. -/
def headTup {k : ℕ} (x : Tup M (k+1) 0) : M := x (Sum.inl 0)

/-- The underlying function of `tailTup`. -/
def tailFun {k : ℕ} (x : Tup M (k+1) 0) (j : Fin k) : M := x (Sum.inl (Fin.succ j))

/-- The remaining coordinates of a tuple in `VF^{k+1}`. -/
def tailTup {k : ℕ} (x : Tup M (k+1) 0) : Tup M k 0 :=
  ⟨fun i => match i with
    | Sum.inl j => tailFun x j
    | Sum.inr j => j.elim0, by
      intro i
      match i with
      | Sum.inl j => exact Tup.vf_mem x (Fin.succ j)
      | Sum.inr j => exact j.elim0⟩

theorem headTup_mem {k : ℕ} (x : Tup M (k+1) 0) : iVF (headTup x) := Tup.vf_mem x 0

/-- Every tuple in `VF^{k+1}` is its head paired with its tail. -/
theorem consTup_head_tail {k : ℕ} (x : Tup M (k+1) 0) :
    consTup (headTup x) (headTup_mem x) (tailTup x) = x := by
  refine Subtype.ext (funext fun i => ?_)
  match i with
  | Sum.inl j =>
    show consFun (headTup x) (tailTup x) j = x (Sum.inl j)
    induction j using Fin.cases with
    | zero => rfl
    | succ t => rfl
  | Sum.inr j => exact j.elim0

/-- **`fib(A, b̄)`**, the paper's fibre of `A ⊆ VF × VF^k` over `b̄`
(`paper.tex:1731`: "`VF ∖ fib(A, b̄)` is finite for all `b̄ ∈ VF^k`"). -/
def fib {k : ℕ} (A : Set (Tup M (k+1) 0)) (b : Tup M k 0) : Set M :=
  {a : M | ∃ ha : iVF a, consTup a ha b ∈ A}

/-- **`VF ∖ fib(A, b̄)`**: the set whose finiteness `fun:dim:1:val:cons` asserts.  Restricting to
`iVF a` is essential: the complement of `fib A b` in `Set M` would also contain the elements of the
`RV`-sort, which are not part of the paper's `VF`. -/
def fibreCompl {k : ℕ} (A : Set (Tup M (k+1) 0)) (b : Tup M k 0) : Set M :=
  {a : M | iVF a ∧ ¬ ∃ ha : iVF a, consTup a ha b ∈ A}

/-! ## Definability of an `RV`-element from a tuple and a parameter pair -/

/-- **`ε` is definable from `ā` over `S`**, at the `RV` sort: the paper's "`ā`-definable
`ε ∈ Γ`".  `QE/Sec3_frozen.lean` has `SP.dcl` for the `VF` sort only (`DECISION.md` records that
`acl`/`dcl` are not built at the `RV` sort), so the `RV`-sorted version is here. -/
def dclRVAt (S : SP M) {n : ℕ} (x : Tup M n 0) (t : M) : Prop :=
  ∃ φ : LRV.BoundedFormula (Fin S.n ⊕ Fin S.m) ((n + 0) + 1),
    WellSorted S.sortMap (Fin.append (fSort n 0) (fun _ : Fin 1 => SortTag.rv)) φ ∧
      ∀ y : M, iRV y →
        (φ.Realize S.toFun
            (Fin.append (fun i : Fin (n + 0) => x (finSumFinEquiv.symm i))
              (fun _ : Fin 1 => y)) ↔
          y = t)

/-- **`ε` is definable over `S`**, at the `RV` sort (the paper's "definable `ε ∈ Γ`"). -/
def dclRV (S : SP M) (t : M) : Prop := SP.DefinableRV S {t}

namespace ValLayer

variable {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] [_root_.SMul ℚ Γ]
  (V : ValLayer M Γ)

/-! ## `VF^1`, the fibre functions `f ↾ VF × {b̄}`, and the isolation sets of `iso:point:dim:less` -/

@[simp] theorem headTup_consTup {k : ℕ} (a : M) (ha : iVF a) (b : Tup M k 0) :
    headTup (consTup a ha b) = a := rfl

theorem tailTup_consTup {k : ℕ} (a : M) (ha : iVF a) (b : Tup M k 0) :
    tailTup (consTup a ha b) = b := by
  refine Subtype.ext (funext fun i => ?_)
  match i with
  | Sum.inl j => rfl
  | Sum.inr j => exact j.elim0

/-- The single coordinate of `x ∈ VF^1` lies in the `VF` sort. -/
theorem coord1_mem (x : Tup M 1 0) : iVF (coord1 x) := x.property (Sum.inl 0)

/-- **`(a) ∈ VF^1`**: the point `a ∈ VF` as an element of `VF^1`. -/
def mkTup1 (a : M) (ha : iVF a) : Tup M 1 0 :=
  ⟨fun i => match i with
    | Sum.inl _ => a
    | Sum.inr j => j.elim0, by
      intro i
      match i with
      | Sum.inl _ => exact ha
      | Sum.inr j => exact j.elim0⟩

@[simp] theorem coord1_mkTup1 (a : M) (ha : iVF a) : coord1 (mkTup1 a ha) = a := rfl

/-- **`f ↾ VF × {b̄}`** as a function on `VF^1` — the paper's `f ↾ VF × {b̄}` in the proof of
`fun:dim:1:val:cons`. -/
def fibreFun {k m : ℕ} (f : Tup M (k+1) 0 → Tup M m 0) (b : Tup M k 0) :
    Tup M 1 0 → Tup M m 0 :=
  fun x => f (consTup (coord1 x) (coord1_mem x) b)

/-- The paper's `B_b̄` of Lemma `iso:point:dim:less`: the points `ā` isolated in `⦰(ā, δ)` with
respect to `f⁻¹(⦰(f(ā), ε))` for some `ε, δ ∈ Γ` — *"the definable subset of those `ā ∈ VF^n` such
that there are `ε, δ ∈ Γ` with `⦰(ā, δ) ∩ f⁻¹(⦰(f(ā), ε)) = {ā}`"* (`paper.tex:1733`). -/
def pointIsolatedSet {n m : ℕ} (f : Tup M n 0 → Tup M m 0) : Set (Tup M n 0) :=
  {x | ∃ ε δ : M, isGamma ε ∧ isGamma δ ∧
    V.oPoly x δ ∩ {y | f y ∈ V.oPoly (f x) ε} = {x}}

/-- **Lemma `iso:point:dim:less`** (`paper.tex:1733`), as a `Prop`: *"Let `f : VF^n → VF^m` be a
definable function.  Let `A ⊆ VF^n` be the definable subset of those `ā` such that there are
`ε, δ ∈ Γ` with `⦰(ā, δ) ∩ f⁻¹(⦰(f(ā), ε)) = {ā}`.  Then `dim_VF(A) < n`."*

This is the §8 lemma the two lemmas of this file wait on; it is *not* proved here (member m6 of this
swarm is producing its statement and its `n = 1` case over §4's dimension layer
`QE/Sec4Dim.lean`).  The lemma's hypothesis "`f` definable" is left to the caller. -/
def IsoPointDimLess (S : SP M) {n m : ℕ} (f : Tup M n 0 → Tup M m 0) : Prop :=
  dimVF S (V.pointIsolatedSet f) < n

/-- **`iso:point:dim:less` for the fibres `f ↾ VF × {b̄}` of `f`**, together with the definability
of the isolation set `B_b̄`.  This is what the first paragraph of `fun:dim:1:val:cons`'s proof takes
from §8's `iso:point:dim:less`: *"For every `b̄ ∈ VF^k` let `B_b̄ ⊆ VF × {b̄}` be as given by
Lemma `iso:point:dim:less` with respect to the function `f ↾ VF × {b̄}`."* -/
def IsoFibres (S : SP M) {k m : ℕ} (f : Tup M (k+1) 0 → Tup M m 0) : Prop :=
  ∀ b : Tup M k 0, Definable S (V.pointIsolatedSet (fibreFun f b)) ∧
    dimVF S (V.pointIsolatedSet (fibreFun f b)) < 1

/-- **A `C`-minimality fact, §3/§4 content carried as a hypothesis**: a definable subset of `VF` of
`VF`-dimension `0` is finite.  The paper uses it as the base case of `points:apart:fin` (*"The base
case `n = 1` just follows from `C`-minimality"*) and here, to pass from `dim_VF(B_b̄) < 1` to
"`B_b̄` is finite".

It is not proved in the tree: `QE/Sec3_sat.lean`'s `IsCMinimalWS` is a frozen `sorry`ed target, and
§4's dimension layer (`QE/Sec4Dim.lean`) does not derive finiteness from `dim_VF = 0`. -/
def DimZeroFiniteVF1 (S : SP M) : Prop :=
  ∀ B : Set (Tup M 1 0), Definable S B → dimVF S B < 1 → B.Finite

/-- **The paper's `A = VF^{k+1} ∖ ⋃_{b̄ ∈ VF^k} B_b̄`**: the points `x = (a, b̄)` such that `a` is
*not* isolated for `f ↾ VF × {b̄}`. -/
def goodSet {k m : ℕ} (f : Tup M (k+1) 0 → Tup M m 0) : Set (Tup M (k+1) 0) :=
  {x | mkTup1 (headTup x) (headTup_mem x) ∉ V.pointIsolatedSet (fibreFun f (tailTup x))}

/-- **The compactness step of `fun:dim:1:val:cons`'s proof**: *"By compactness
`A = VF^{k+1} ∖ ⋃_{b̄ ∈ VF^k} B_b̄` is definable."*  Stated for the paper's `A` (`goodSet f`); it
asserts definability only, so it is strictly weaker than the lemma's conclusions. -/
def CanonicalDefinable (S : SP M) {k m : ℕ} (f : Tup M (k+1) 0 → Tup M m 0) : Prop :=
  Definable S (V.goodSet f)

/-- **Conclusion 1 of `fun:dim:1:val:cons`, proved** for the paper's `A`: *"`VF ∖ fib(A, b̄)` is
finite for all `b̄ ∈ VF^k`."*

The paper gets it from `dim_VF(B_b̄) < 1` (`iso:point:dim:less`) and the finiteness of a
dimension-`0` definable subset of `VF` (`DimZeroFiniteVF1`); that is exactly this proof: the
complement of `fib(A, b̄)` in `VF` is the isolation set `B_b̄`, whose first coordinate is finite. -/
theorem fibreCompl_goodSet_finite {S : SP M} {k m : ℕ} {f : Tup M (k+1) 0 → Tup M m 0}
    (hIso : V.IsoFibres S f) (hDim0 : DimZeroFiniteVF1 S) (b : Tup M k 0) :
    (fibreCompl (V.goodSet f) b).Finite := by
  obtain ⟨hdef, hdim⟩ := hIso b
  have hfin : (V.pointIsolatedSet (fibreFun f b)).Finite := hDim0 _ hdef hdim
  refine (hfin.image coord1).subset ?_
  rintro a ⟨ha, hnot⟩
  have hEq : mkTup1 a ha = mkTup1 (headTup (consTup a ha b)) (headTup_mem _) := Subtype.ext rfl
  have hmem : mkTup1 a ha ∈ V.pointIsolatedSet (fibreFun f b) := by
    by_contra hcon
    refine hnot ⟨ha, ?_⟩
    show mkTup1 (headTup (consTup a ha b)) (headTup_mem _) ∉
      V.pointIsolatedSet (fibreFun f (tailTup (consTup a ha b)))
    rw [tailTup_consTup, ← hEq]
    exact hcon
  exact ⟨mkTup1 a ha, hmem, rfl⟩

/-- The paper's *"`f ↾ ⦰(a, δ) × {b̄}` is constant"*. -/
def ConstAt {k m : ℕ} (f : Tup M (k+1) 0 → Tup M m 0) (x : Tup M (k+1) 0) (δ : M) : Prop :=
  ∀ (a' : M) (ha' : iVF a'), a' ∈ V.oBall (headTup x) δ →
    f (consTup a' ha' (tailTup x)) = f x

/-- The paper's equation `vv(f(a', b̄) - f(a, b̄)) = ε + k vv(a' - a)` on `⦰(a, δ)`. -/
def LawAt {k m : ℕ} (f : Tup M (k+1) 0 → Tup M m 0) (x : Tup M (k+1) 0) (ε δ : M) (q : ℚ) : Prop :=
  ∀ (a' : M) (ha' : iVF a'), a' ∈ V.oBall (headTup x) δ → ∀ j : Fin m,
    V.vv ((f (consTup a' ha' (tailTup x))) (Sum.inl j)) ((f x) (Sum.inl j)) =
      V.vrv ε + V.smulTop q (V.vv a' (headTup x))

/-- The set of exponents `k` with which the local power law holds at some point of the paper's `A`. -/
def exponentSet {k m : ℕ} (f : Tup M (k+1) 0 → Tup M m 0) : Set ℚ :=
  {q | 0 < q ∧ ∃ x ∈ V.goodSet f, ∃ ε δ : M, isGamma ε ∧ isGamma δ ∧ V.LawAt f x ε δ q}

/-- The first sentence of `fun:dim:1:val:cons`'s second paragraph: *"Therefore, there is an
`ε ∈ Γ ∪ {∞}` and a rational number `k ≥ 0` such that for any sufficiently large `δ ∈ Γ`, the
formula `vv(X) > δ ∧ φ(a+X, a, b̄, Z)` defines a function on `⦰(a, δ) × {b̄}` that is given by the
equation `Z = ε + k vv(X)`.  ... Since `Γ` is `o`-minimal, `ε` and some `δ` are
`ā`-definable."* -/
def LocalLawPointwise (S : SP M) {k m : ℕ} (f : Tup M (k+1) 0 → Tup M m 0) : Prop :=
  ∀ x ∈ V.goodSet f, ∃ ε δ : M, isGamma ε ∧ isGamma δ ∧ dclRVAt S x ε ∧ dclRVAt S x δ ∧
    (V.ConstAt f x δ ∨ ∃ q : ℚ, 0 < q ∧ V.LawAt f x ε δ q)

/-- The last sentence of `fun:dim:1:val:cons`'s second paragraph: *"Now it is easy to see that the
number `k` is provided by the exponents of `X₁` in `φ(X₁, X₂, Ȳ, Z)` and hence there are only
finitely many choices."* -/
def ExponentsFinite {k m : ℕ} (f : Tup M (k+1) 0 → Tup M m 0) : Prop :=
  ∃ E : Finset ℚ, (∀ q ∈ E, 0 < q) ∧ V.exponentSet f ⊆ ↑E

/-- **The second paragraph of `fun:dim:1:val:cons`'s proof, as one residual**: the pointwise local
law together with the finiteness of the possible exponents. -/
def DominatingTerm (S : SP M) {k m : ℕ} (f : Tup M (k+1) 0 → Tup M m 0) : Prop :=
  V.LocalLawPointwise S f ∧ V.ExponentsFinite f

/-! ## `fun:dim:1:val:cons` (`paper.tex:1746`) -/

/-- **The conclusion of Lemma `fun:dim:1:val:cons`** (`paper.tex:1746`):

> Let `f : VF × VF^k → VF^m` be a definable function.  Then there are a definable subset
> `A ⊆ VF × VF^k` over `VF^k` and a finite set `E` of positive rational numbers such that
> 1. `VF ∖ fib(A, b̄)` is finite for all `b̄ ∈ VF^k`,
> 2. for every `ā = (a, b̄) ∈ A` there are `ā`-definable `ε, δ ∈ Γ` and a number `k ∈ E` such that
> either `f ↾ ⦰(a, δ) × {b̄}` is constant or, for any `a' ∈ ⦰(a, δ)`,
> `vv(f(a', b̄) - f(a, b̄)) = ε + k vv(a' - a)`.

Rendered with `fib`/`fibreCompl`, `dclRVAt` for "`ā`-definable", `oBall` for `⦰(a, δ)`,
`consTup`/`headTup`/`tailTup` for `(a, b̄)` and `a' ↦ (a', b̄)`, `V.vv` for `vv(· - ·)`,
`V.smulTop k` for `k vv(·)`, and `ConstAt`/`LawAt` for the two alternatives.  "Over `VF^k`" is the
single parameter pair `S` for the whole set `A` (the paper's uniformity in `b̄`). -/
def ValConsConcl (S : SP M) {k m : ℕ} (f : Tup M (k+1) 0 → Tup M m 0) : Prop :=
  ∃ A : Set (Tup M (k+1) 0), Definable S A ∧
    ∃ E : Finset ℚ, (∀ q ∈ E, 0 < q) ∧
      (∀ b : Tup M k 0, (fibreCompl A b).Finite) ∧
        ∀ x ∈ A, ∃ ε δ : M, isGamma ε ∧ isGamma δ ∧ dclRVAt S x ε ∧ dclRVAt S x δ ∧
          (V.ConstAt f x δ ∨ ∃ q ∈ E, V.LawAt f x ε δ q)

/-- **Lemma `fun:dim:1:val:cons`** (`paper.tex:1746`), whose sentence is quoted in
`ValConsConcl`'s docstring.

`A` is *constructed*, not assumed: it is the paper's `A = VF^{k+1} ∖ ⋃_{b̄} B_b̄` (`goodSet f`), and
its conclusion 1 is **proved** (`fibreCompl_goodSet_finite`) from

* `hIso` — §8's `iso:point:dim:less` for the fibres `f ↾ VF × {b̄}` (the §8 lemma this file waits
  on, being stated by member m6 of this swarm), plus definability of `B_b̄`;
* `hDim0` — the `C`-minimality fact that a definable subset of `VF` of dimension `0` is finite
  (§3/§4 content, carried as a hypothesis).

The remaining hypotheses are the two §8 residuals, named in this file as separate `Prop`s with the
paper's sentences:

* `hDefA : CanonicalDefinable S f` — *"By compactness `A = VF^{k+1} ∖ ⋃_{b̄} B_b̄` is definable."*
* `hTerm : DominatingTerm S f` — the second paragraph: `LocalLawPointwise` (*"there is an `ε ∈ Γ`
  and a rational number `k ≥ 0` such that ... `Z = ε + k vv(X)`; since `Γ` is `o`-minimal, `ε` and
  some `δ` are `ā`-definable"*) and `ExponentsFinite` (*"the number `k` is provided by the
  exponents of `X₁` in `φ` and hence there are only finitely many choices"*). -/
theorem fun_dim_1_val_cons (S : SP M) {k m : ℕ} (f : Tup M (k+1) 0 → Tup M m 0)
    (hdef : DefinableFun S Set.univ f)
    (hIso : V.IsoFibres S f) (hDim0 : DimZeroFiniteVF1 S)
    (hDefA : V.CanonicalDefinable S f) (hTerm : V.DominatingTerm S f) :
    V.ValConsConcl S f := by
  obtain ⟨hpoint, E, hEpos, hE⟩ := hTerm
  refine ⟨V.goodSet f, hDefA, E, hEpos,
    fun b => V.fibreCompl_goodSet_finite hIso hDim0 b, ?_⟩
  intro x hx
  obtain ⟨ε, δ, hε, hδ, hεd, hδd, hcase⟩ := hpoint x hx
  refine ⟨ε, δ, hε, hδ, hεd, hδd, ?_⟩
  rcases hcase with hc | ⟨q, hq, hlaw⟩
  · exact Or.inl hc
  · exact Or.inr ⟨q, hE ⟨hq, x, hx, ε, δ, hε, hδ, hlaw⟩, hlaw⟩

end ValLayer

/-! ## The arithmetic step at the end of `rad:equal:1`'s proof -/

/-- **The last inference of `rad:equal:1`'s proof**: *"Since the radius of `𝔞` is sufficiently
large, we conclude that `k` must be a positive integer.  Symmetrically `1/k` is also a positive
integer and hence `k = 1`."*

Proved: a positive rational whose value and whose inverse are both positive integers is `1`. -/
theorem expIntegral_eq_one {q : ℚ} (hq : 0 < q) (hm : ∃ m : ℕ, 0 < m ∧ q = m)
    (hn : ∃ n : ℕ, 0 < n ∧ q⁻¹ = n) : q = 1 := by
  obtain ⟨m, hm0, hmq⟩ := hm
  obtain ⟨n, hn0, hnq⟩ := hn
  have hmq' : (m : ℚ) = q := hmq.symm
  have hnq' : (n : ℚ) = q⁻¹ := hnq.symm
  have hqn : q * (n : ℚ) = 1 := by
    rw [hnq']
    exact mul_inv_cancel₀ (ne_of_gt hq)
  rw [← hmq'] at hqn
  have hnat : m * n = 1 := by exact_mod_cast hqn
  have hm1 : m = 1 := Nat.dvd_one.mp ⟨n, hnat.symm⟩
  rw [← hmq', hm1]
  norm_num

/-- **The integrality input of `rad:equal:1`'s proof**: *"we conclude that `k` must be a positive
integer.  Symmetrically `1/k` is also a positive integer."*  A residual (§8): it is the output of
the division-algorithm paragraph of the paper's proof (`G(X, Y)`, `H(X, Y)`, `i' = i + 1`). -/
def ExponentIntegral (q : ℚ) : Prop :=
  (∃ m : ℕ, 0 < m ∧ q = m) ∧ ∃ n : ℕ, 0 < n ∧ q⁻¹ = n

namespace ValLayer

variable {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] [_root_.SMul ℚ Γ]
  (V : ValLayer M Γ)

/-- **The first sentence of `rad:equal:1`'s proof, as a residual** (§8):

> By the proof of Lemma `fun:dim:1:val:cons` we may assume that there is a definable `ε ∈ Γ` and a
> positive rational number `k` such that `vv(f(a)) = ε + k vv(a)`.

`𝔞` is the ball on which `f` is defined (`f`'s domain in the lemma). -/
def PowerLaw (S : SP M) (f : Tup M 1 0 → Tup M 1 0) (𝔞 : Set (Tup M 1 0)) (q : ℚ) : Prop :=
  ∃ ε : M, isGamma ε ∧ dclRV S ε ∧
    ∀ x : Tup M 1 0, x ∈ 𝔞 →
      V.vv (coord1 (f x)) (iVFZero (M := M)) =
        V.vrv ε + V.smulTop q (V.vv (coord1 x) (iVFZero (M := M)))

/-- **Lemma `rad:equal:1`** (`paper.tex:1772`):

> Let `𝔞, 𝔟` be open balls around `0` and `f : 𝔞 → 𝔟` a definable bijection that takes open balls
> around `0` to open balls around `0`.  Then there are definable `γ, ε ∈ Γ` such that
> `vv(f(a)) = ε + vv(a)` for every `a ∈ ⦰(0, γ)`.

Rendered with `V.oBallTup ta`/`V.oBallTup tb` for the balls `𝔞, 𝔟` (`ta, tb ∈ Γ`; the degenerate ball
`{0}` is the paper's `⦰(0, ∞)` convention, `oBallTop`), `Set.BijOn f` for the bijection (`f` is
total, as in `DefinableFun`, which states the graph of the function on its domain only), `hballs` for
"takes open balls around `0` to open balls around `0`" (each `𝔞 ∩ ⦰(0, γ)` maps *onto*
`𝔟 ∩ ⦰(0, γ')`, which is what the paper's later use of the lemma needs), `hta` for the ball's
radius being definable (it is a parameter of the statement).

The two residuals are §8, and named with the paper's sentences:

* `hpow : PowerLaw S f (V.oBallTup ta) q` — *"By the proof of Lemma `fun:dim:1:val:cons` we may
  assume that there is a definable `ε ∈ Γ` and a positive rational number `k` such that
  `vv(f(a)) = ε + k vv(a)`."*  It is the reductions of `fun:dim:1:val:cons`'s second paragraph
  applied to `f`, after ball preservation has made the exponent uniform on `𝔞`.
* `hint : ExponentIntegral q` — *"we conclude that `k` must be a positive integer.  Symmetrically
  `1/k` is also a positive integer."*  (The division-algorithm paragraph of the paper's proof.)

The last step is **proved**: `expIntegral_eq_one` turns `hint` into `q = 1`, and `smulTop_one`
turns `1 vv(x)` into `vv(x)`; hence the conclusion holds on `𝔞` itself (`γ = ta`). -/
theorem rad_equal_one (S : SP M) (f : Tup M 1 0 → Tup M 1 0)
    (hdef : DefinableFun S (V.oBallTup ta) f) (ta tb : M) (ha : isGamma ta) (hb : isGamma tb)
    (hbij : Set.BijOn f (V.oBallTup ta) (V.oBallTup tb))
    (hballs : ∀ γ : M, isGamma γ → ∃ γ' : M, isGamma γ' ∧
      f '' (V.oBallTup ta ∩ V.oBallTup γ) = V.oBallTup tb ∩ V.oBallTup γ')
    (q : ℚ) (hq : 0 < q) (hpow : V.PowerLaw S f (V.oBallTup ta) q)
    (hint : ExponentIntegral q) (hta : dclRV S ta) :
    ∃ ε γ : M, isGamma ε ∧ isGamma γ ∧ dclRV S ε ∧ dclRV S γ ∧
      ∀ x : Tup M 1 0, x ∈ V.oBallTup ta → x ∈ V.oBallTup γ →
        V.vv (coord1 (f x)) (iVFZero (M := M)) =
          V.vrv ε + V.vv (coord1 x) (iVFZero (M := M)) := by
  obtain ⟨ε, hε, hεd, hlaw⟩ := hpow
  have hq1 : q = 1 := expIntegral_eq_one hq hint.1 hint.2
  refine ⟨ε, ta, hε, ha, hεd, hta, fun x hx _ => ?_⟩
  rw [hlaw x hx, hq1, V.smulTop_one]

end ValLayer

/-! ## The paper's "almost everywhere", and an inhabitant of `ValLayer` -/

/-- The empty set is definable. -/
theorem Definable.empty (S : SP M) {n m : ℕ} : Definable S (∅ : Set (Tup M n m)) := by
  have h := (definable_univ S (n := n) (m := m)).compl
  simpa using h

/-- `∅` has `VF`-dimension `0`: every function is finite-to-one on it. -/
theorem hasDim_empty (S : SP M) {n m : ℕ} :
    HasDim S (∅ : Set (Tup M n m)) 0 := by
  refine ⟨0, le_rfl, 0, fun _ => ⟨fun i => isEmptyElim i, fun i => isEmptyElim i⟩, ?_, ?_⟩
  · exact ⟨⊤, wellSorted_top S.sortMap _, fun x hx => absurd hx (Set.notMem_empty x)⟩
  · intro y
    exact Set.finite_empty.subset (fun x hx => hx.1)

/-- `dim_VF(∅) = 0`. -/
theorem dimVF_empty (S : SP M) {n m : ℕ} : dimVF S (∅ : Set (Tup M n m)) = 0 :=
  (dimVF_eq_zero_iff S ∅).2 (hasDim_empty S)

/-- **The paper's "almost everywhere on `A`"** (Section 8, right after `iso:point:dim:less`):
*"Let `A` be a definable subset with `dim_VF(A) = n`.  A property holds almost everywhere on `A` or
for almost every element in `A` if there is a definable subset `B ⊆ A` with `dim_VF(B) < n` such
that the property holds with respect to `A ∖ B`."* -/
def AlmostEverywhere (S : SP M) {n m : ℕ} (A : Set (Tup M n m))
    (P : Tup M n m → Prop) : Prop :=
  ∃ B : Set (Tup M n m), Definable S B ∧ B ⊆ A ∧ dimVF S B < dimVF S A ∧
    ∀ x : Tup M n m, x ∈ A → x ∉ B → P x

/-- A property that holds everywhere holds almost everywhere, provided `dim_VF(A) > 0` (the paper's
`A` has `dim_VF(A) = n`, so `n = 0`, where there is no `B` with `dim_VF(B) < 0`, is the only case
in which the notion is empty). -/
theorem almostEverywhere_of_forall (S : SP M) {n m : ℕ} {A : Set (Tup M n m)}
    (P : Tup M n m → Prop) (h0 : 0 < dimVF S A) (hP : ∀ x ∈ A, P x) :
    AlmostEverywhere S A P :=
  ⟨∅, Definable.empty S, Set.empty_subset _,
    by rw [dimVF_empty]; exact h0, fun x hx _ => hP x hx⟩

/-- A stronger property gives a weaker one almost everywhere. -/
theorem AlmostEverywhere.mono (S : SP M) {n m : ℕ} {A : Set (Tup M n m)}
    {P Q : Tup M n m → Prop} (h : AlmostEverywhere S A P) (hPQ : ∀ x, P x → Q x) :
    AlmostEverywhere S A Q := by
  obtain ⟨B, hB, hBA, hdim, hP⟩ := h
  exact ⟨B, hB, hBA, hdim, fun x hx hxB => hPQ x (hP x hx hxB)⟩

/-! ## The layer is inhabited

`ValLayer`'s axioms are consistent: the one-point `L_RV`-structure, with the trivial value group
`Γ = ℚ`, satisfies all of them.  (This is a consistency check on the hypothesis bundle, not a
model of `ACVF`: `PUnit` carries no field structure.  A model with nontrivial `Γ` would be a valued
field; §1–§6 of the paper supply those, and nothing below is stated conditionally on their
existence beyond `ValLayer` itself.) -/

/-- The one-point `L_RV`-structure: every sort predicate holds, every function symbol is trivial,
every relation symbol is `True`. -/
instance instStructurePUnit : LRV.Structure PUnit where
  funMap := fun {n} f _ => match f with
    | Fn.vfZero => PUnit.unit
    | Fn.vfOne => PUnit.unit
    | Fn.vfAdd => PUnit.unit
    | Fn.vfNeg => PUnit.unit
    | Fn.vfMul => PUnit.unit
    | Fn.rvOne => PUnit.unit
    | Fn.rvZero => PUnit.unit
    | Fn.rvMul => PUnit.unit
    | Fn.kAdd => PUnit.unit
    | Fn.kNeg => PUnit.unit
    | Fn.rvMap => PUnit.unit
  RelMap := fun {n} r _ => match r with
    | Rel.memVF => True
    | Rel.memRV => True
    | Rel.memUnits => True
    | Rel.rvLe => True

/-- `ValLayer` is inhabited: the trivial value layer on the one-point structure, with `Γ = ℚ`
(so `Γ` really is an ordered additive group with `ℚ`-scalars — `smul_one`/`smul_mul` are
`one_mul`/`mul_assoc` of `ℚ`). -/
def valLayerPUnit : ValLayer PUnit ℚ where
  smul_one := fun γ => one_mul γ
  smul_mul := fun k k' γ => mul_assoc k k' γ
  smulTop := fun q x => match x with
    | ⊤ => ⊤
    | (γ : ℚ) => ((q * γ : ℚ) : WithTop ℚ)
  smulTop_coe := fun q γ => rfl
  smulTop_top := fun q => rfl
  vv := fun _ _ => ⊤
  vrv := fun _ => ⊤
  vf_zero := trivial
  vf_sub := fun _ _ _ _ => trivial
  rv_sorted := fun _ _ => trivial
  vv_self := fun _ _ => rfl
  vv_sym := fun _ _ _ _ => rfl
  vv_ultra := fun _ _ _ _ _ _ => le_refl ⊤
  vrv_rv := fun _ _ _ _ => rfl
  vrv_zero := rfl
  vrv_eq_top := fun t _ _ => Subsingleton.elim t _
  vrv_le := fun t s _ _ => ⟨fun _ => le_refl ⊤, fun _ => trivial⟩

/-- The layer's lemmas fire on the inhabitant: every `vv`-ball there is empty. -/
theorem oBall_valLayerPUnit (t : PUnit) :
    ValLayer.oBall valLayerPUnit PUnit.unit t = ∅ :=
  ValLayer.oBall_eq_empty_of_vrv_top valLayerPUnit rfl


end Sec8

end SpecialTransformations.Milestone0
