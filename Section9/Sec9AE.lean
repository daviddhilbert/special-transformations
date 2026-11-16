module

/-
# Yin, "Special transformations in algebraically closed valued fields" — Sections 9 (`diff:almost:every`,
`special:tran:vol:pre`) and the almost-everywhere terminology of `paper.tex:1744`.

Formalised in `Milestone0/Encoding.lean`'s frozen single-carrier encoding of `L_RV`, on top of
Section 4's dimension layer (`.scratch2/sec3/Sec4Dim.lean`, `import Sec4Dim`).

What is defined here:

* `vv` — the paper's `\vv : VF → Γ`, read as `iRv` (Γ is not a sort of `L_RV`; an element of Γ is
  represented by a `K^×`-element of the `RV` sort, so `ε : Γ` is `iUnits ε` below).
* `AlmostEverywhereOn` — the paper's "a property holds almost everywhere on `A`" (`paper.tex:1744`),
  with the ambient dimension `dim_VF(A)` (and `AlmostEverywhereOnRV`, the `RV`-dimension variant
  the paper says is "also used with respect to `RV`-dimension").
* `HasDerivAtZero` — Definition `defn:diff` (`paper.tex:1966`) in the one-variable form: `d` is the
  derivative of `g` at `0` when for every `ε ∈ Γ` there is `δ ∈ Γ` with
  `vv(g b - g 0 - d·b) - vv(b) > ε` for every `b` with `vv(b) > δ`.  In `RV` this is written
  multiplicatively, `vv(g b - g 0 - d·b) > ε · vv(b)`, because `+` on Γ is `iRVMul` on `RV^×`.
* `HasPartialDeriv`, `ContPartiallyDiffAt` — Definition `defn:diff`'s partial derivatives and the
  "continuously partially differentiable" of Corollary `diff:almost:every`.
* `detVF`, `JacobianEqOne` — the Jacobian of `defn:diff`'s last paragraph (the determinant of the
  matrix of partials) as a term of the encoding.
* `SpecialSteps`, `jacobian_one_of_steps`, `special_tran_vol_pre` — Lemma `special:tran:vol:pre`
  (`paper.tex:2042`).
-/
public import Sec4Dim

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
open FirstOrder FirstOrder.Language

namespace SpecialTransformations.Milestone0
open LRV

namespace Sec9AE

open Sec4Dim

variable {M : Type*} [LRV.Structure M]

/-! ## 1. Readings of the encoding used in Section 9 -/

/-- The paper's `\vv : VF → Γ ∪ {∞}`, as an element of the `RV` sort: `iRv` is the frozen encoding's
`rv` symbol, and `vv` and `rv` are the same function of the paper (Γ is the definable quotient
`RV^× / K^×`, so an element of Γ is represented by an element of `K^×`, i.e. by `iUnits`). -/
abbrev vv (x : M) : M := iRv x

/-- The paper's strict inequality on Γ, `γ < ε`, in the encoding: `iLe` is the paper's `≤`
(`Milestone0/DECISION.md`: the encoding's order is the paper's value-group order, the opposite of
`Mathlib.Valuation`'s). -/
def RVLt (γ ε : M) : Prop := iLe γ ε ∧ ¬ iLe ε γ

/-- `vv x > γ`, i.e. the strict inequality `¬ (vv x ≤ γ)` in the paper's (pre)order. -/
def VvGt (x γ : M) : Prop := ¬ iLe (vv x) γ

/-- `0` of the `VF` sort. -/
def vfZero : M := Structure.funMap (L := LRV) Fn.vfZero fun i => i.elim0

/-- `1` of the `VF` sort. -/
def vfOne : M := Structure.funMap (L := LRV) Fn.vfOne fun i => i.elim0

/-- `x - y` in the `VF` sort. -/
def vfSub (x y : M) : M := iVFAdd x (iVFNeg y)

/-- The `i`-th `VF`-coordinate of a `VF`-tuple. -/
abbrev vfCoord {n : ℕ} (a : Tup M n 0) (i : Fin n) : M := a (Sum.inl i)

/-- The underlying function of `updVF`: replace the `i`-th `VF`-coordinate by `v`. -/
def updVFfun {n : ℕ} (a : Tup M n 0) (i : Fin n) (v : M) : Idx n 0 → M
  | Sum.inl j => if j = i then v else a.1 (Sum.inl j)
  | Sum.inr j => j.elim0

theorem updVFfun_same {n : ℕ} (a : Tup M n 0) (i : Fin n) (v : M) :
    updVFfun a i v (Sum.inl i) = v := by
  simp [updVFfun]

theorem updVFfun_other {n : ℕ} (a : Tup M n 0) {i j : Fin n} (v : M) (h : j ≠ i) :
    updVFfun a i v (Sum.inl j) = a.1 (Sum.inl j) := by
  simp [updVFfun, h]

/-- Replace the `i`-th `VF`-coordinate of a `VF`-tuple by `v`, which must lie in the `VF` sort. -/
def updVF {n : ℕ} (a : Tup M n 0) (i : Fin n) (v : M) (hv : iVF v) : Tup M n 0 :=
  ⟨updVFfun a i v,
   by
    intro t
    match t with
    | Sum.inl j =>
      by_cases h : j = i
      · rw [h, updVFfun_same]; exact hv
      · rw [updVFfun_other a v h]; exact a.2 (Sum.inl j)
    | Sum.inr j => exact j.elim0⟩

@[simp] theorem updVF_same {n : ℕ} (a : Tup M n 0) (i : Fin n) (v : M) (hv : iVF v) :
    updVF a i v hv (Sum.inl i) = v := by
  simp only [updVF, updVFfun_same]

theorem updVF_other {n : ℕ} (a : Tup M n 0) {i j : Fin n} (v : M) (hv : iVF v) (h : j ≠ i) :
    updVF a i v hv (Sum.inl j) = a (Sum.inl j) := by
  simp only [updVF, updVFfun_other a v h]

/-- `iVF` is closed under `+` — Definition 2.2(1) of the paper (`K` is a field): the encoding's
`iVFAdd` is total on the carrier with a junk value off `VF`, and the axiom set `Axioms.ACVF`
relativises `+` to `K`.  Carried explicitly so that the junk convention of `updVF`/`sliceFun` is
harmless; on a model of `ACVF` it is a theorem of `Milestone0/Encoding.lean`'s axiom list. -/
def VFAddClosed : Prop := ∀ x y : M, iVF x → iVF y → iVF (iVFAdd x y)

/-! ## 2. Almost everywhere (`paper.tex:1744`) -/

/-- **"A property holds almost everywhere on `A`"** — `paper.tex:1744`: *"Let `A` be a definable
subset with `dim_VF(A) = n`. A property holds almost everywhere on `A` or for almost every element
in `A` if there is a definable subset `B ⊆ A` with `dim_VF(B) < n` such that the property holds with
respect to `A \ B`. ... This terminology is also used with respect to `RV`-dimension."*

The `n` of the paper is `dimVF S A`: the notion is relative to the set `A` itself, so it is stated
for an arbitrary set `A` and uses `dimVF S A` as the ambient dimension (for `A = univ ⊆ VF^n` this
is `≤ n`, and the paper's `A` has `dim_VF A = n`). -/
def AlmostEverywhereOn (S : SP M) {n m : ℕ} (A : Set (Tup M n m))
    (P : Tup M n m → Prop) : Prop :=
  ∃ B : Set (Tup M n m), Definable S B ∧ B ⊆ A ∧ dimVF S B < dimVF S A ∧
    ∀ x ∈ A, x ∉ B → P x

/-- ... with respect to the `RV`-dimension (`paper.tex:1744`, last sentence: *"This terminology is
also used with respect to `RV`-dimension."*).  For `B ⊆ RV^m` (`m` `RV`-coordinates and no `VF`
ones), the ambient dimension is `dimRV S A`. -/
def AlmostEverywhereOnRV (S : SP M) {m : ℕ} (A : Set (Tup M 0 m))
    (P : Tup M 0 m → Prop) : Prop :=
  ∃ B : Set (Tup M 0 m), Definable S B ∧ B ⊆ A ∧ dimRV S B < dimRV S A ∧
    ∀ x ∈ A, x ∉ B → P x

theorem AlmostEverywhereOn.mono {S : SP M} {n m : ℕ} {A : Set (Tup M n m)} {P Q : Tup M n m → Prop}
    (h : AlmostEverywhereOn S A P) (hPQ : ∀ x, P x → Q x) : AlmostEverywhereOn S A Q := by
  obtain ⟨B, hdB, hBA, hdim, hP⟩ := h
  exact ⟨B, hdB, hBA, hdim, fun x hx hxB => hPQ x (hP x hx hxB)⟩

theorem AlmostEverywhereOnRV.mono {S : SP M} {m : ℕ} {A : Set (Tup M 0 m)}
    {P Q : Tup M 0 m → Prop}
    (h : AlmostEverywhereOnRV S A P) (hPQ : ∀ x, P x → Q x) : AlmostEverywhereOnRV S A Q := by
  obtain ⟨B, hdB, hBA, hdim, hP⟩ := h
  exact ⟨B, hdB, hBA, hdim, fun x hx hxB => hPQ x (hP x hx hxB)⟩

/-- The unique element of the paper's `RV^0` (`VF^0 × RV^0`), i.e. of `Tup M 0 0`. -/
def emptyTup : Tup M 0 0 :=
  ⟨fun t => t.elim (fun i => i.elim0) (fun j => j.elim0),
   fun t => t.elim (fun i => i.elim0) (fun j => j.elim0)⟩

/-- The empty set is definable (`⊥` is well-sorted, `WellSorted.falsum`). -/
theorem definable_empty (S : SP M) {n m : ℕ} : Definable S (∅ : Set (Tup M n m)) := by
  have h : Definable S ((Set.univ : Set (Tup M n m))ᶜ) := (definable_univ S).compl
  simpa using h

/-- The empty set has `VF`-dimension `0`: the empty graph is definable (`∀ x ∈ ∅, …` is vacuous),
so `HasDim S ∅ 0` holds and `dimVF_le_iff` turns the `sInf` definition of `dimVF` into a
minimum. -/
theorem dimVF_empty (S : SP M) {n m : ℕ} : dimVF S (∅ : Set (Tup M n m)) = 0 := by
  have hdef : DefinableFun S (∅ : Set (Tup M n m)) (fun _ => (emptyTup (M := M))) :=
    ⟨⊥, WellSorted.falsum (Fin.append (fSort n m) (fSort 0 0)),
     fun x hx => absurd hx (Set.notMem_empty x)⟩
  have hfin : FibreFinite (∅ : Set (Tup M n m)) (fun _ => (emptyTup (M := M))) :=
    fun y => Set.finite_empty.subset (fun x hx => hx.1)
  have h0 : HasDim S (∅ : Set (Tup M n m)) 0 := ⟨0, le_rfl, 0, _, hdef, hfin⟩
  exact le_antisymm ((dimVF_le_iff S _ 0).2 h0) (Nat.zero_le _)

/-- **A property holding everywhere holds almost everywhere**, as soon as `A` has positive
`VF`-dimension: the bad set is `∅`, which is definable and of dimension `0`. -/
theorem almostEverywhereOn_of_forall {S : SP M} {n m : ℕ} {A : Set (Tup M n m)}
    {P : Tup M n m → Prop} (hP : ∀ x ∈ A, P x) (hpos : 1 ≤ dimVF S A) :
    AlmostEverywhereOn S A P := by
  refine ⟨∅, definable_empty S, Set.empty_subset A, ?_, fun x hx _ => hP x hx⟩
  rw [dimVF_empty S]; omega

/-- The finite-union bound used silently throughout the paper when it passes from finitely many
definable pieces to their union (*"by compactness"*, *"a union of finitely many subsets"*): if two
definable subsets of `A` have `VF`-dimension `< dim_VF(A)`, then so does their union (contained in a
definable subset of `A` of dimension `< dim_VF A`).

Not exported by `Sec4Dim`: its header records exactly the missing ingredient (composing a
`DefinableFun` with the zero-padding `VF^{k'} ↪ VF^k` needs a substitution lemma for
`DefinableFun`), so the bound is carried as an explicit `Prop`-valued hypothesis, and the theorems
below that combine two almost-everywhere statements take it as a hypothesis. -/
def AlmostEverywhereUnionClosed (S : SP M) {n m : ℕ} (A : Set (Tup M n m)) : Prop :=
  ∀ B₁ B₂ : Set (Tup M n m), Definable S B₁ → Definable S B₂ → B₁ ⊆ A → B₂ ⊆ A →
    dimVF S B₁ < dimVF S A → dimVF S B₂ < dimVF S A →
      ∃ B : Set (Tup M n m), Definable S B ∧ B ⊆ A ∧ dimVF S B < dimVF S A ∧ B₁ ∪ B₂ ⊆ B

/-- Two almost-everywhere properties may be conjoined: union the two bad sets.  (The paper does this
without comment whenever it writes "almost everywhere" for a conjunction of properties.) -/
theorem AlmostEverywhereOn.and {S : SP M} {n m : ℕ} {A : Set (Tup M n m)}
    {P Q : Tup M n m → Prop} (hU : AlmostEverywhereUnionClosed S A)
    (hP : AlmostEverywhereOn S A P) (hQ : AlmostEverywhereOn S A Q) :
    AlmostEverywhereOn S A (fun x => P x ∧ Q x) := by
  obtain ⟨B₁, hd₁, hB₁A, hdim₁, hP⟩ := hP
  obtain ⟨B₂, hd₂, hB₂A, hdim₂, hQ⟩ := hQ
  obtain ⟨B, hdB, hBA, hdimB, hBB⟩ := hU B₁ B₂ hd₁ hd₂ hB₁A hB₂A hdim₁ hdim₂
  exact ⟨B, hdB, hBA, hdimB, fun x hx hxB =>
    ⟨hP x hx (fun h => hxB (hBB (Or.inl h))), hQ x hx (fun h => hxB (hBB (Or.inr h)))⟩⟩


open Sec4Dim

variable {M : Type*} [LRV.Structure M]

/-! ## 3. Differentiation in the `VF` sort (Definition `defn:diff`, `paper.tex:1966`)

The paper's definition, verbatim:

> Let `f : VF^n → VF^m` be a definable function. For any `ā ∈ VF^n`, we say that `f` is
> *differentiable at `ā`* if there is a linear map `λ : VF^n → VF^m` (of `VF`-vector spaces) such
> that, for any `ε ∈ Γ`, if `b̄ ∈ VF^n` and `vv(b̄)` is sufficiently large then
> `vv(f(ā + b̄) - f(ā) - λ(b̄)) - vv(b̄) > ε`.

In `RV` the difference `vv(y) - vv(b)` of two value-group elements is the quotient
`vv(y) / vv(b)`, i.e. `iRVMul` of `vv y` by the inverse of `vv b`; the paper's condition
`vv(y) - vv(b) > ε` is therefore `vv(y) > ε · vv(b)`, which is what `HasDerivAtZero` below
states (`VvGt _ (iRVMul ε (vv b))`).  An element `ε ∈ Γ` is represented by a `K^×`-element of
the `RV` sort, i.e. by `ε` with `iUnits ε` — the encoding has no `Γ` sort by design
(`Milestone0/DECISION.md`). -/

/-- **Definition `defn:diff`, one-variable form at `0`.**  `d` is the derivative of `g` at `0` if for
every `ε ∈ Γ` there is `δ ∈ Γ` such that for every `b ∈ VF` with `vv(b) > δ`,

`vv(g b - g 0 - d · b) > ε · vv(b)`,

which is the paper's `vv(g(b) - g(0) - λ(b)) - vv(b) > ε` with `λ = d · (-)`. -/
def HasDerivAtZero (g : M → M) (d : M) : Prop :=
  iVF (g vfZero) ∧ iVF d ∧
    ∀ ε : M, iUnits ε → ∃ δ : M, iUnits δ ∧
      ∀ b : M, iVF b → VvGt b δ →
        VvGt (vfSub (vfSub (g b) (g vfZero)) (iVFMul d b)) (iRVMul ε (vv b))

/-- The `i`-th coordinate slice of `f` through `ā` — the paper's function
`b ↦ f_j(ā_i + b, ā̄_i)` of `defn:diff`'s last paragraph.  It is totalised by `0` at arguments
whose translate `ā_i + b` is not in the `VF` sort; on a model of `ACVF` the `VF` sort is closed
under `+` (`VFAddClosed`), so there the `then` branch is always taken (`sliceFun_of`). -/
noncomputable def sliceFun {n m : ℕ} (f : Tup M n 0 → Tup M m 0) (j : Fin m) (i : Fin n)
    (a : Tup M n 0) (b : M) : M := by
  classical
  exact if h : iVF (iVFAdd (vfCoord a i) b) then
      (f (updVF a i (iVFAdd (vfCoord a i) b) h)).1 (Sum.inl j)
    else vfZero

theorem sliceFun_of {n m : ℕ} (f : Tup M n 0 → Tup M m 0) (j : Fin m) (i : Fin n)
    (a : Tup M n 0) (b : M) (hb : iVF (iVFAdd (vfCoord a i) b)) :
    sliceFun f j i a b = (f (updVF a i (iVFAdd (vfCoord a i) b) hb)).1 (Sum.inl j) := by
  simp only [sliceFun]
  rw [dif_pos hb]

/-- **Definition `defn:diff`, last paragraph**: *"For each `1 ≤ j ≤ m` let `f_j = pr_j ∘ f`. For any
`ā = (a_i, ā̄_i) ∈ VF^n`, if the derivative of the function `f_j ↾ (VF × {ā̄_i})` at `a_i` exists
then we call it the `ij`th partial derivative of `f` at `ā`."*

The derivative at `a_i` of that one-variable function is the derivative at `0` of its translate
`b ↦ f_j(a_i + b, ā̄_i)` (`sliceFun`). -/
def HasPartialDeriv {n m : ℕ} (f : Tup M n 0 → Tup M m 0) (j : Fin m) (i : Fin n)
    (a : Tup M n 0) (d : M) : Prop :=
  HasDerivAtZero (sliceFun f j i a) d

/-- The `ij`-th partial derivative exists at `ā`. -/
def PartialDerivExistsAt {n m : ℕ} (f : Tup M n 0 → Tup M m 0) (j : Fin m) (i : Fin n)
    (a : Tup M n 0) : Prop :=
  ∃ d : M, HasPartialDeriv f j i a d

/-- `f` is partially differentiable at `ā`: all `n · m` partial derivatives exist there. -/
def PartiallyDiffAt {n m : ℕ} (f : Tup M n 0 → Tup M m 0) (a : Tup M n 0) : Prop :=
  ∀ j : Fin m, ∀ i : Fin n, PartialDerivExistsAt f j i a

/-! ## 4. Continuity in the `VF` sort -/

/-- `g : VF^n → VF` is continuous at `ā`: for every `ε ∈ Γ` there is `δ ∈ Γ` such that
`vv(x_i - a_i) > δ` for all `i` implies `vv(g x - g a) > ε` — the ε–δ form of continuity in the
valued-field topology, with the polydisc condition of the paper. -/
def ContinuousAtM {n : ℕ} (g : Tup M n 0 → M) (a : Tup M n 0) : Prop :=
  iVF (g a) ∧ ∀ ε : M, iUnits ε → ∃ δ : M, iUnits δ ∧
    ∀ x : Tup M n 0, (∀ i : Fin n, VvGt (vfSub (vfCoord x i) (vfCoord a i)) δ) →
      VvGt (vfSub (g x) (g a)) ε

/-! ## 5. Corollary `diff:almost:every` (`paper.tex:2027`)

> Let `f : VF^n → VF^m` be a definable function. Then `f` is continuously partially differentiable
> almost everywhere.

The partial derivatives are carried as a *definable system* `D` (`IsPartiallyDifferentiable`), which
is what Lemma `partial:exist` produces ("the linear function is constructed in the usual way, taking
`ζ(ā)` as the slope"): an almost-everywhere statement about a partial *function* needs a function
to speak about. -/

/-- At the point `ā`, the system `D` gives *the* partial derivatives of `f`: `D ā j i` is the
`ij`-th partial derivative. -/
def PartialDerivSystemAt {n m : ℕ} (f : Tup M n 0 → Tup M m 0)
    (D : Tup M n 0 → Fin m → Fin n → M) (a : Tup M n 0) : Prop :=
  ∀ (j : Fin m) (i : Fin n), HasPartialDeriv f j i a (D a j i)

/-- `D` is a system of partial derivatives for `f` everywhere. -/
def IsPartiallyDifferentiable {n m : ℕ} (f : Tup M n 0 → Tup M m 0)
    (D : Tup M n 0 → Fin m → Fin n → M) : Prop :=
  ∀ a : Tup M n 0, PartialDerivSystemAt f D a

/-- `f` is **continuously partially differentiable at `ā`** (the notion of Corollary
`diff:almost:every`), with the partial derivatives given by the system `D`: they are `D ā` at `ā`,
and each partial derivative `x ↦ D x j i`, as a function of the point, is continuous at `ā`. -/
def ContPartiallyDiffAt {n m : ℕ} (f : Tup M n 0 → Tup M m 0)
    (D : Tup M n 0 → Fin m → Fin n → M) (a : Tup M n 0) : Prop :=
  PartialDerivSystemAt f D a ∧ ∀ (j : Fin m) (i : Fin n), ContinuousAtM (fun x => D x j i) a

/-- **Lemma `partial:exist`** (`paper.tex:2017`), the part used here: *"Let `f : VF^n → VF^m` be a
definable function. Then each partial derivative `∂^{ij} f` is defined almost everywhere."* —
derived from the almost-everywhere existence of the whole system `D`. -/
theorem partial_deriv_defined_almost_every (S : SP M) {n m : ℕ} {f : Tup M n 0 → Tup M m 0}
    {D : Tup M n 0 → Fin m → Fin n → M}
    (hPart : AlmostEverywhereOn S (Set.univ : Set (Tup M n 0)) (PartialDerivSystemAt f D))
    (j : Fin m) (i : Fin n) :
    AlmostEverywhereOn S (Set.univ : Set (Tup M n 0)) (fun a => PartialDerivExistsAt f j i a) :=
  hPart.mono fun a ha => ⟨D a j i, ha j i⟩

/-- **Corollary `diff:almost:every`** (`paper.tex:2027`): *"Let `f : VF^n → VF^m` be a definable
function. Then `f` is continuously partially differentiable almost everywhere."*

The paper proves it *"immediate by Lemma `partial:exist` and Lemma `fun:almost:cont`"*; those two are
the hypotheses `hPart` and `hCont` below — `partial:exist` gives the a.e. existence of the partial
derivatives (in the paper through the `ā`-definable functions `g^{ij}_{ā}`, *"the linear function is
constructed in the usual way, taking `ζ(ā)` as the slope"*, which is also what makes the
partial-derivative functions of the system `D` definable), and `fun:almost:cont` applied to those
definable partial-derivative functions `D · j i` gives their a.e. continuity.  The two bad sets are
merged with `AlmostEverywhereUnionClosed`.  Note that `hCont` alone already gives the existence of
the derivatives at almost every point; `hPart` is the paper's separate citation and is the form in
which `partial:exist` is stated. -/
theorem diff_almost_every (S : SP M) {n m : ℕ} {f : Tup M n 0 → Tup M m 0}
    {D : Tup M n 0 → Fin m → Fin n → M}
    (hU : AlmostEverywhereUnionClosed S (Set.univ : Set (Tup M n 0)))
    (hPart : AlmostEverywhereOn S (Set.univ : Set (Tup M n 0)) (PartialDerivSystemAt f D))
    (hCont : AlmostEverywhereOn S (Set.univ : Set (Tup M n 0))
      (fun a => ∀ (j : Fin m) (i : Fin n), ContinuousAtM (fun x => D x j i) a)) :
    AlmostEverywhereOn S (Set.univ : Set (Tup M n 0)) (ContPartiallyDiffAt f D) :=
  AlmostEverywhereOn.and hU hPart hCont

/-! ## 6. The Jacobian and Lemma `special:tran:vol:pre` (`paper.tex:2042`)

The paper's Jacobian in the `VF` sort (Definition after Lemma `partial:exist`): *"If `n = n'` and all
the partial derivatives exist at a point `(ā, t̄)` then the Jacobian of `f` at `(ā, t̄)` is defined in
the usual way, that is, the determinant of the Jacobian matrix, and is denoted by
`jcb_VF f(ā, t̄)`."* -/

/-- The left-associated sum of a list of `VF`-elements, starting at `0`. -/
def sumVF (l : List M) : M := l.foldl (fun x y => iVFAdd x y) vfZero

/-- The left-associated product of a list of `VF`-elements, starting at `1`. -/
def prodVF (l : List M) : M := l.foldl (fun x y => iVFMul x y) vfOne

/-- The determinant of an `n × n` matrix over the `VF` sort, as its Leibniz expansion in the
encoding's `+`, `×` and `−`: `Σ_σ sign(σ) · Π_i D i (σ i)`.  This is the `det` of the paper's
`jcb_VF = det (∂_i f_j)`; it is a term of the encoding, so it is definable in the sense of
`Milestone0/Encoding.lean`.  (No ring laws are proved of `iVFAdd`/`iVFMul` in this layer — the
frozen `Axioms.ACVF` is a first-order axiom set, not a Mathlib `Field` instance — so nothing about
`detVF` beyond its definition is asserted here.) -/
noncomputable def detVF {n : ℕ} (D : Fin n → Fin n → M) : M :=
  sumVF (((Finset.univ : Finset (Equiv.Perm (Fin n))).toList).map (fun σ =>
    (if (Equiv.Perm.sign σ : ℤˣ) = 1 then id else fun x => iVFNeg x)
      (prodVF (List.ofFn (fun i : Fin n => D i (σ i))))))

/-- **The Jacobian of `f : VF^n → VF^n` at `ā` is `1`** — the paper's `jcb_VF f(ā) = 1`: the matrix
of partial derivatives has determinant `1`.  Stated existentially because the matrix of partial
derivatives is only determined where the derivatives exist: `∃ D` collects all `n^2` of them. -/
def JacobianEqOne {n : ℕ} (f : Tup M n 0 → Tup M n 0) (a : Tup M n 0) : Prop :=
  ∃ D : Fin n → Fin n → M,
    (∀ (j : Fin n) (i : Fin n), HasPartialDeriv f j i a (D j i)) ∧ detVF D = vfOne

/-- **Lemma `jcb:chain`** (`paper.tex:2055`), at the level of "determinant `1`" that
`special:tran:vol:pre` uses: *"Let `f : A → B` and `g : B → C` be definable functions. Then for any
`x̄ ∈ A`, `jcb_VF (g ∘ f)(x̄) = jcb_VF g(f(x̄)) · jcb_VF f(x̄)`, if both sides are defined."*
Composing two determinant-`1` Jacobians gives a determinant-`1` Jacobian (`1 · 1 = 1`), which is the
only instance needed here; it is carried as a hypothesis because the product rule for `detVF` needs
the ring laws of the `VF` sort (see `detVF`). -/
def JacobianOneChainRule (n : ℕ) : Prop :=
  ∀ (g f : Tup M n 0 → Tup M n 0) (a : Tup M n 0),
    JacobianEqOne f a → JacobianEqOne g (f a) → JacobianEqOne (fun x => g (f x)) a

/-- The composite of a list of elementary steps, applied left to right. -/
def compSteps {n : ℕ} (l : List (Tup M n 0 → Tup M n 0)) (x : Tup M n 0) : Tup M n 0 :=
  l.foldl (fun x s => s x) x

@[simp] theorem compSteps_nil {n : ℕ} :
    compSteps ([] : List (Tup M n 0 → Tup M n 0)) = id := rfl

@[simp] theorem compSteps_cons {n : ℕ} (s : Tup M n 0 → Tup M n 0)
    (rest : List (Tup M n 0 → Tup M n 0)) :
    compSteps (s :: rest) = compSteps rest ∘ s := rfl

/-- **A composition of steps has Jacobian `1` everywhere if each step has**, by the chain rule —
i.e. the induction behind the paper's *"We may assume that the length of `T` is `1`"* in the proof
of `special:tran:vol:pre`. -/
theorem jacobian_one_of_steps {n : ℕ}
    (hId : ∀ a, JacobianEqOne (id : Tup M n 0 → Tup M n 0) a)
    (hChain : JacobianOneChainRule (M := M) n) :
    ∀ (l : List (Tup M n 0 → Tup M n 0)), (∀ s ∈ l, ∀ a, JacobianEqOne s a) →
      ∀ a, JacobianEqOne (compSteps l) a
  | [], _ => by
    intro a
    rw [compSteps_nil]
    exact hId a
  | s :: rest, hElem => by
    intro a
    have hmem : ∀ t ∈ rest, ∀ a, JacobianEqOne t a :=
      fun t ht => hElem t (List.mem_cons_of_mem s ht)
    have h1 : JacobianEqOne (compSteps rest) (s a) :=
      jacobian_one_of_steps hId hChain rest hmem (s a)
    have h2 : JacobianEqOne (fun x => compSteps rest (s x)) a :=
      hChain (compSteps rest) s a (hElem s (by simp) a) h1
    rw [compSteps_cons]
    exact h2

/-- **A special bijection in the sense of §5, Definition 5.1**, recorded in the syntactic layer of
Section 4: the map `T : A → A^#` (additive translations and canonical bijections composed) together
with its decomposition into elementary steps.  (`QE/Sec5.lean` formalises Definition 5.1 over the
concrete valued-field model `Pt v n m` — `SpecialBijection`, `Step`, `compose`, `eta_wellPosed` —
a different layer from the syntactic `Tup M n 0` used here; that is why the decomposition is carried
as data.) -/
structure SpecialBijection (S : SP M) {n : ℕ} (A : Set (Tup M n 0)) where
  /-- the map `T` -/
  toFun : Tup M n 0 → Tup M n 0
  /-- `T` is definable -/
  definable : DefinableFun S A toFun
  /-- `T : A → A^#` is a bijection onto its image -/
  inj : Set.InjOn toFun A
  /-- the elementary steps of Definition 5.1 that `T` is the composite of -/
  steps : List (Tup M n 0 → Tup M n 0)
  /-- `T` is the composite of its steps -/
  isComp : ∀ x, toFun x = compSteps steps x

/-- **Lemma `special:tran:vol:pre`** (`paper.tex:2042`), the "everywhere" half:

> For any special bijection `T : A → A^#`, the Jacobians of `T` and `T^{-1}` are equal to `1` almost
> everywhere. **If `A` is a nondegenerate `RV`-pullback then they are equal to `1` everywhere.**

The paper's proof: *"We may assume that the length of `T` is `1`. Then this is clear if we apply the
proof of Lemma `partial:exist` to (additive) translation and canonical bijection (or its inverse)."*
So the hypotheses are the length-`1` case for the steps of `T` (`hElem`) and of `T^{-1}`
(`hElemInv`), the Jacobian of the identity (`hId`), and the chain rule (`hChain`, Lemma
`jcb:chain`); the passage to arbitrary length is the induction `jacobian_one_of_steps`.  This is the
`everywhere` conclusion, which implies the `almost everywhere` one of the lemma statement
(`special_tran_vol_pre`), the paper's `nondegenerate RV`-pullback case being the case in which the
derivative is defined everywhere. -/
theorem special_tran_vol_pre_everywhere {n : ℕ} (S : SP M) {A : Set (Tup M n 0)}
    (T Tinv : SpecialBijection (M := M) S A)
    (hId : ∀ a, JacobianEqOne (id : Tup M n 0 → Tup M n 0) a)
    (hChain : JacobianOneChainRule (M := M) n)
    (hElem : ∀ s ∈ T.steps, ∀ a, JacobianEqOne s a)
    (hElemInv : ∀ s ∈ Tinv.steps, ∀ a, JacobianEqOne s a) :
    (∀ a ∈ A, JacobianEqOne T.toFun a) ∧ ∀ a ∈ A, JacobianEqOne Tinv.toFun a := by
  have hT : ∀ a, JacobianEqOne (compSteps T.steps) a :=
    jacobian_one_of_steps hId hChain T.steps hElem
  have hTi : ∀ a, JacobianEqOne (compSteps Tinv.steps) a :=
    jacobian_one_of_steps hId hChain Tinv.steps hElemInv
  have hfun : T.toFun = compSteps T.steps := funext T.isComp
  have hfunInv : Tinv.toFun = compSteps Tinv.steps := funext Tinv.isComp
  constructor
  · intro a _
    rw [hfun]; exact hT a
  · intro a _
    rw [hfunInv]; exact hTi a

/-- **Lemma `special:tran:vol:pre`** (`paper.tex:2042`), first sentence:

> For any special bijection `T : A → A^#`, the Jacobians of `T` and `T^{-1}` are equal to `1` almost
> everywhere.

`hInvOn` is the paper's `T^{-1}`: `Tinv` is the inverse of `T` on `A` (`Tinv ∘ T = id` there); it
plays no role in the determinant computation, which goes through `Tinv`'s own step decomposition.
`hpos` is `dim_VF(A) ≥ 1`, the only case in which "almost everywhere on `A`" is weaker than
"everywhere" (`dim_VF(∅) = 0`); for `dim_VF(A) = 0` the two notions coincide. -/
theorem special_tran_vol_pre {n : ℕ} (S : SP M) {A : Set (Tup M n 0)}
    (T Tinv : SpecialBijection (M := M) S A)
    (hInvOn : ∀ x ∈ A, Tinv.toFun (T.toFun x) = x)
    (hpos : 1 ≤ dimVF S A)
    (hId : ∀ a, JacobianEqOne (id : Tup M n 0 → Tup M n 0) a)
    (hChain : JacobianOneChainRule (M := M) n)
    (hElem : ∀ s ∈ T.steps, ∀ a, JacobianEqOne s a)
    (hElemInv : ∀ s ∈ Tinv.steps, ∀ a, JacobianEqOne s a) :
    AlmostEverywhereOn S A (JacobianEqOne T.toFun) ∧
      AlmostEverywhereOn S A (JacobianEqOne Tinv.toFun) := by
  obtain ⟨hT, hTi⟩ :=
    special_tran_vol_pre_everywhere S T Tinv hId hChain hElem hElemInv
  exact ⟨almostEverywhereOn_of_forall hT hpos, almostEverywhereOn_of_forall hTi hpos⟩


/-! ## 7. Axiom audit (all within `propext`, `Classical.choice`, `Quot.sound`) -/

#print axioms SpecialTransformations.Milestone0.Sec9AE.dimVF_empty
#print axioms SpecialTransformations.Milestone0.Sec9AE.almostEverywhereOn_of_forall
#print axioms SpecialTransformations.Milestone0.Sec9AE.AlmostEverywhereOn.and
#print axioms SpecialTransformations.Milestone0.Sec9AE.partial_deriv_defined_almost_every
#print axioms SpecialTransformations.Milestone0.Sec9AE.diff_almost_every
#print axioms SpecialTransformations.Milestone0.Sec9AE.jacobian_one_of_steps
#print axioms SpecialTransformations.Milestone0.Sec9AE.special_tran_vol_pre_everywhere
#print axioms SpecialTransformations.Milestone0.Sec9AE.special_tran_vol_pre

end Sec9AE

end SpecialTransformations.Milestone0
