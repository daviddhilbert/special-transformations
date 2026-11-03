 /-
**Hypothesis (iii) for `Language.val`, assembled down to two named inputs.**

This is the syntax bridge Johnson's Lemma 2.3.1 needs, plus the assembly of 1-ec from it:

* `termToPoly` and `eval₂_termToPoly`: a `Language.val`-term in one variable with parameters in `K`
  evaluates in `N` as a polynomial over `K` (`evalTerm`), so every atomic formula is
  `P x = 0` or `v (P x) ≤ v (Q x)`;
* `IsKBall`/`Good`: balls of `N` with centre `f c` and radius `w (f b)` (`c b : K`), and finite
  Boolean combinations of them; `good_empty`, `good_univ`, `good_singleton`, `good_compl`,
  `good_union`, `good_iUnion_finset`, `good_of_finite_range`;
* `finite_rootSet`: `{x : N | q.eval₂ f x = 0}` is finite and lies in the image of `K`
  (2.3.1(i), from `IsAlgClosed K`);
* `good_solSet`: every **quantifier-free** `Language.val`-formula in one variable with parameters
  in `K` defines a `Good` set — with the single named input `AtomGood` (= Johnson 2.3.1(ii):
  `{x : v (P x) ≤ v (Q x)}` is a Boolean combination of `K`-balls);
* `oneECIn_of_inputs'`: `OneECIn` for `K ↪[val] L` from `AtomGood` and `GoodMeetsBase`
  (= 2.3.2 ∘ 2.3.8), in the exact shape of Johnson's hypothesis (iii).

**Not proved here: `AtomGood`** — but its first layer is.  The section `Atom` at the end of this
file proves, for `[IsAlgClosed K]`:

* `eval₂_prod_roots_aux`, `eval₂_eq_prod_roots`, `val_eval₂_eq_prod_roots`:
  `w (P.eval₂ f x) = w (f P.leadingCoeff) * ∏_{a ∈ P.roots} w (x - f a)`;
* `val_sub_eq_of_lt`: **far from the other roots a factor is constant** — if
  `w (x - f a) < w (f a - f b)` then `w (x - f b) = w (f a - f b)`;
* `atomGood_P_zero` and `atomGood_Q_zero`: the degenerate cases (`P = 0`: everything; `Q = 0`: the
  finite root set, via `finite_rootSet`).

The *ball condition* — `c_P δ^m ≤ c_Q δ^n` for `δ := w (x - f a)` with constant `c_P`, `c_Q` — is
now complete in all three cases, which is what the region `U_a` of the cluster induction needs:
`good_pow_le_pow_same` (`m = n`: everything, `{f a}` when `m > 0`, `∅` when `m = 0`),
`good_pow_le_pow_lt` (`m < n`: `{f a} ∪ (openBall (f a) (w (f e)))ᶜ` when `m > 0`, the complement
alone when `m = 0`, where `w (f e)^d = c_P / c_Q` and `d = n - m`), and `good_pow_le_pow_gt`
(`m > n`: the closed ball of radius `w (f e)`).  `exists_val_pow_div` supplies `e` from
`IsAlgClosed K`.  Note the two traps: the centre has to be added by hand when `m > 0` (the value
`δ = 0` is below every radius), and the `m = 0` case is *not* the same set as the `m > 0` one.

What remains is the cluster induction.  For a finite root set `A` and `a ∈ A` put
`U_a := ⋂_{b ∈ A, b ≠ a} openBall (f a) (w (f (a - b)))`, a finite intersection of `K`-balls, so
`Good`.  On `U_a` every factor except the `a`-one is the *constant* `w (f a - f b)`
(`val_sub_eq_of_lt`), so with `m_a`, `n_a` the multiplicities of `a` in `P.roots`, `Q.roots` and
`δ := w (x - f a)`, the condition becomes `c_P δ^{m_a} ≤ c_Q δ^{n_a}` with `c_P`, `c_Q` explicit
values of `w ∘ f`: a closed ball when `m_a > n_a`, the complement of an open ball when
`m_a < n_a` (the `(m_a - n_a)`-th root exists because `K` is algebraically closed —
`exists_pow_val_eq`, or `Johnson.exists_pow_val_eq` — applied to the valuation `w.comap f`), and
constant on `U_a` when `m_a = n_a`.  The pieces `U_a` cover only the points that are strictly
closer to one root than to all the others; the rest is handled by induction on the number of
distinct roots, splitting on `δ < γ_a`, `δ = γ_a`, `δ > γ_a` where `γ_a` is the distance from `a`
to the nearest other root — in the middle case the `a`-term is constant and drops out, and in the
third `a` merges with its nearest neighbour so the two coefficients add.  That part is **not**
formalized yet.

Why the naive arg-max argument does not work, for the record: (i) `v(x - a) = v(x - a')` with `x`
not a root is possible, so the strict arg-max cells do not cover `N`; (ii) at `x = a` the
ultrametric "max rule" degenerates (`v(a - a') = M` but `v(x - a') = 0`), so on a non-strict
arg-max set the values `v(x - a')` are *not* all equal.  Two things make it
harder than Johnson's sketch suggests, and they are recorded so that nobody repeats the mistake:
(i) `v(x - a) = v(x - a')` with `x` not a root is possible, so the strict arg-max sets do not
cover `N`; (ii) at `x = a` the ultrametric "max rule" degenerates (`v(a - a') = M` but
`v(x - a') = 0`), so on a non-strict arg-max set the values `v(x - a')` are *not* all equal.
The correct decomposition is by cluster merging: split on `v(x - a) < γ_a`, `= γ_a`, `> γ_a`
where `γ_a` is the distance to the nearest other root; in the first case all other factors are
constants (a ball condition), in the second the `a`-term is constant and can be dropped, and in
the third `a` merges with its nearest neighbour — so the number of distinct roots decreases and
the argument inducts.

Snapshot of swarm `smw0c60wk` member m6 (`OneEC_val.lean`), truncated at its last compiling line
and verified here: compiles, no `sorry`, all `#print axioms` clean.  Not edited.

Only import: Mathlib.
-/

/-
  **The 1-ec step of Johnson §2.3 in the one-sorted language `L_val`: the syntax bridge and the
  assembly.**

  This file isolates the *logical* half of Johnson's Lemma 2.3 (the 1-ec property of a model of
  ACVF inside a valued field).  Its content:

  * the language `Language.val` (copied from `QE/PrimeModels_valued.lean`), its structure on a
    valued field, and the dictionary `IsValEmb ↔ L_val`-embedding;
  * the *term bridge*: an `L_val`-term with parameters in `K` and one free variable denotes a
    polynomial over `K` (`termToPoly`), and `eval₂_termToPoly` identifies the two evaluations;
  * the predicate `Good` "Boolean combination of balls with centre and radius in `K`", closed
    under Boolean operations, containing the zero set of every polynomial (this is the `{P = 0}`
    half of 2.3.1, *proved here* from `IsAlgClosed K` via `finite_rootSet`);
  * the two valuation-theoretic inputs of §2.3, kept as named `Prop`s:
    - `AtomGood`: Johnson 2.3.1(ii) — `{x : v (P x) ≤ v (Q x)}` is such a Boolean combination;
    - `GoodMeetsBase`: Johnson 2.3.2 + 2.3.8 — a nonempty one meets `K`;
  * the conclusion: `oneECIn_of_inputs`, i.e. `OneECIn` for `K ↪[val] L` (Johnson's hypothesis
    (iii) of Lemma 2.1.4 in the `Valuation` framework).

  Nothing is assumed beyond `Mathlib`.  No `sorry`, no `axiom`.
-/
import Mathlib

open FirstOrder FirstOrder.Language
open scoped FirstOrder
open scoped Polynomial

set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

namespace ValOneEC

/-! ## 1. The language `L_val`, its structure on a valued field, and its embeddings

Verbatim from `QE/PrimeModels_valued.lean` (itself the frozen definition of Johnson's `L_val`:
the language of rings together with the binary predicate `v x ≤ v y`). -/

/-- Function symbols of `L_val`: those of the language of rings. -/
inductive ValFunc : ℕ → Type
  | add : ValFunc 2
  | mul : ValFunc 2
  | neg : ValFunc 1
  | zero : ValFunc 0
  | one : ValFunc 0
  deriving DecidableEq

/-- Relation symbols of `L_val`: the single binary predicate `v x ≤ v y`. -/
inductive ValRel : ℕ → Type
  | le : ValRel 2
  deriving DecidableEq

/-- **Johnson's language `L_val`**: the language of rings expanded by a binary predicate for the
relation `v x ≤ v y`. -/
def Language.val : FirstOrder.Language := ⟨ValFunc, ValRel⟩

/-- **The `L_val`-structure of a valued field.** -/
@[instance_reducible]
def valStructure {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation K Γ₀) : Language.val.Structure K where
  funMap := fun {_} f x =>
    match f with
    | ValFunc.add => x 0 + x 1
    | ValFunc.mul => x 0 * x 1
    | ValFunc.neg => - x 0
    | ValFunc.zero => 0
    | ValFunc.one => 1
  RelMap := fun {_} r x =>
    match r with
    | ValRel.le => v (x 0) ≤ v (x 1)

/-- An `L_val`-embedding of valued fields is an injective ring homomorphism preserving the
predicate `v x ≤ v y`.  (Copy of `FracValued.embeddingOfIsValEmb`.) -/
def embeddingOfIsValEmb {K : Type*} [Field K] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    {L : Type*} [Field L] {Γ' : Type*} [LinearOrderedCommGroupWithZero Γ']
    (v : Valuation K Γ) (w : Valuation L Γ') (f : K →+* L)
    (hinj : Function.Injective f) (hord : ∀ x y : K, v x ≤ v y ↔ w (f x) ≤ w (f y)) :
    @FirstOrder.Language.Embedding Language.val K L (valStructure v) (valStructure w) := by
  letI := valStructure v
  letI := valStructure w
  refine { toFun := f, inj' := hinj, map_fun' := ?_, map_rel' := ?_ }
  · intro n g x
    cases g with
    | add => exact map_add f (x 0) (x 1)
    | mul => exact map_mul f (x 0) (x 1)
    | neg => exact map_neg f (x 0)
    | zero => exact map_zero f
    | one => exact map_one f
  · intro n r x
    cases r with
    | le => exact (hord (x 0) (x 1)).symm

/-- The ring homomorphism underlying an `L_val`-embedding.  (Copy of
`FracValued.ringHomOfEmbedding`.) -/
def ringHomOfEmbedding {K : Type*} [Field K] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    {L : Type*} [Field L] {Γ' : Type*} [LinearOrderedCommGroupWithZero Γ']
    (v : Valuation K Γ) (w : Valuation L Γ')
    (F : @FirstOrder.Language.Embedding Language.val K L (valStructure v) (valStructure w)) :
    K →+* L := by
  letI := valStructure v
  letI := valStructure w
  exact { toFun := F
          map_one' := F.map_fun' ValFunc.one (fun i => Fin.elim0 i)
          map_zero' := F.map_fun' ValFunc.zero (fun i => Fin.elim0 i)
          map_mul' := fun x y => F.map_fun' ValFunc.mul ![x, y]
          map_add' := fun x y => F.map_fun' ValFunc.add ![x, y] }

/-! ## 2. Johnson's 1-ec property

Copy of `JohnsonCriterion.OneECIn` (`QE/Johnson_criterion.lean`). -/

/-- **1-ec** (Johnson, Definition 2.1.3): `S` is 1-ec in `N` along the embedding `i` if every
non-empty quantifier-free `S`-definable subset of `N` in one variable meets `S`. -/
def OneECIn {L : FirstOrder.Language.{0, 0}} {S : Type} {N : Type}
    [L.Structure S] [L.Structure N] (i : S ↪[L] N) : Prop :=
  ∀ (φ : L.BoundedFormula S 1), φ.IsQF →
    (∃ a, φ.Realize (fun s => i s) (fun _ => a)) →
      ∃ s : S, φ.Realize (fun s' => i s') (fun _ => i s)

/-! ## 3. Balls with centre and radius in the base field, and Boolean combinations of them

Johnson's §2.3 works with the balls of an algebraically closed valued field `K` *inside* an
extension `N`.  Here `f : K →+* N` is the (injective) map of the base field into `N` and
`IsKBall f w D` says that `D` is one of Johnson's balls with centre and radius in the image of
`K`: `{x : w (x - f c) ≤ w (f b)}`, `{x : w (x - f c) < w (f b)}`, or the whole space.
(`IsValBall` of `QE/Johnson23_valuation.lean`, transported along `f`.) -/

section Balls

variable {N : Type} [Field N] {Γ' : Type*} [LinearOrderedCommGroupWithZero Γ']

/-- The closed ball of radius `γ` about `c`. -/
def closedBall (w : Valuation N Γ') (c : N) (γ : Γ') : Set N := {x | w (x - c) ≤ γ}

/-- The open ball of radius `γ` about `c`. -/
def openBall (w : Valuation N Γ') (c : N) (γ : Γ') : Set N := {x | w (x - c) < γ}

theorem mem_closedBall {w : Valuation N Γ'} {c x : N} {γ : Γ'} :
    x ∈ closedBall w c γ ↔ w (x - c) ≤ γ := Iff.rfl

theorem mem_openBall {w : Valuation N Γ'} {c x : N} {γ : Γ'} :
    x ∈ openBall w c γ ↔ w (x - c) < γ := Iff.rfl

/-- The closed ball of radius zero is a point. -/
theorem closedBall_zero_radius (w : Valuation N Γ') (c : N) : closedBall w c 0 = {c} := by
  ext x
  rw [mem_closedBall, Set.mem_singleton_iff]
  exact ⟨fun h => sub_eq_zero.mp (w.zero_iff.mp (le_antisymm h zero_le)),
    fun h => h ▸ by simp⟩

end Balls

section Good

variable {K : Type} [Field K] {N : Type} [Field N]
variable {Γ' : Type*} [LinearOrderedCommGroupWithZero Γ']

/-- A ball of `N` with centre and radius in the image of the base field `K`. -/
inductive IsKBall (f : K →+* N) (w : Valuation N Γ') : Set N → Prop
  | closed (c b : K) : IsKBall f w (closedBall w (f c) (w (f b)))
  | openball (c b : K) : IsKBall f w (openBall w (f c) (w (f b)))
  | univ : IsKBall f w Set.univ

/-- `D` is a finite Boolean combination of balls with centre and radius in the image of `K`
(Johnson's form of a quantifier-free `K`-definable subset of `N` in one variable, Lemma 2.3.1). -/
def Good (f : K →+* N) (w : Valuation N Γ') (D : Set N) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (b : ι → Set N) (t : Set ι → Bool),
    (∀ i, IsKBall f w (b i)) ∧ ∀ x : N, (x ∈ D ↔ t {i | x ∈ b i} = true)

theorem good_empty (f : K →+* N) (w : Valuation N Γ') : Good f w ∅ := by
  refine ⟨PEmpty, inferInstance, PEmpty.elim, fun _ => false, ?_, ?_⟩
  · intro i; exact i.elim
  · intro x
    simp

theorem good_univ (f : K →+* N) (w : Valuation N Γ') : Good f w Set.univ := by
  refine ⟨PUnit, inferInstance, fun _ => Set.univ, fun _ => true, ?_, ?_⟩
  · intro _; exact IsKBall.univ
  · intro x
    simp

theorem good_singleton (f : K →+* N) (w : Valuation N Γ') (c : K) : Good f w {f c} := by
  classical
  have hball : closedBall w (f c) (w (f 0)) = {f c} := by
    rw [show f 0 = (0 : N) from map_zero f, show w (0 : N) = (0 : Γ') from map_zero w,
      closedBall_zero_radius]
  refine ⟨PUnit, inferInstance, fun _ => closedBall w (f c) (w (f 0)),
    fun S => decide S.Nonempty, ?_, ?_⟩
  · intro _; exact IsKBall.closed c 0
  · intro x
    have hiff : ({i : PUnit | x ∈ closedBall w (f c) (w (f 0))}).Nonempty ↔ x = f c := by
      constructor
      · rintro ⟨i, hi⟩
        rwa [hball] at hi
      · intro hx
        exact ⟨PUnit.unit, by rw [hball]; exact hx⟩
    show (x ∈ ({f c} : Set N)) ↔ (fun S : Set PUnit => decide S.Nonempty)
      {i : PUnit | x ∈ (fun _ => closedBall w (f c) (w (f 0))) i} = true
    rw [Set.mem_singleton_iff]
    have hbeta : (fun S : Set PUnit => decide S.Nonempty)
        {i : PUnit | x ∈ (fun _ => closedBall w (f c) (w (f 0))) i}
        = decide ({i : PUnit | x ∈ closedBall w (f c) (w (f 0))}).Nonempty := rfl
    rw [hbeta, decide_eq_true_eq]
    exact hiff.symm

theorem good_compl {f : K →+* N} {w : Valuation N Γ'} {D : Set N} (h : Good f w D) :
    Good f w Dᶜ := by
  classical
  obtain ⟨ι, _, b, t, hb, ht⟩ := h
  refine ⟨ι, inferInstance, b, fun S => !(t S), hb, ?_⟩
  intro x
  rw [Set.mem_compl_iff, ht x, Bool.not_eq_true]
  simp

theorem good_union {f : K →+* N} {w : Valuation N Γ'} {D₁ D₂ : Set N}
    (h₁ : Good f w D₁) (h₂ : Good f w D₂) : Good f w (D₁ ∪ D₂) := by
  classical
  obtain ⟨ι₁, _, b₁, t₁, hb₁, ht₁⟩ := h₁
  obtain ⟨ι₂, _, b₂, t₂, hb₂, ht₂⟩ := h₂
  refine ⟨ι₁ ⊕ ι₂, inferInstance, Sum.elim b₁ b₂,
    fun S => t₁ (Sum.inl ⁻¹' S) || t₂ (Sum.inr ⁻¹' S), ?_, ?_⟩
  · rintro (i | i)
    · exact hb₁ i
    · exact hb₂ i
  · intro x
    have e₁ : Sum.inl ⁻¹' {i : ι₁ ⊕ ι₂ | x ∈ Sum.elim b₁ b₂ i} = {i : ι₁ | x ∈ b₁ i} := by
      ext i; simp
    have e₂ : Sum.inr ⁻¹' {i : ι₁ ⊕ ι₂ | x ∈ Sum.elim b₁ b₂ i} = {i : ι₂ | x ∈ b₂ i} := by
      ext i; simp
    rw [Set.mem_union, ht₁ x, ht₂ x]
    show (t₁ {i : ι₁ | x ∈ b₁ i} = true ∨ t₂ {i : ι₂ | x ∈ b₂ i} = true) ↔
      (t₁ (Sum.inl ⁻¹' {i : ι₁ ⊕ ι₂ | x ∈ Sum.elim b₁ b₂ i})
        || t₂ (Sum.inr ⁻¹' {i : ι₁ ⊕ ι₂ | x ∈ Sum.elim b₁ b₂ i})) = true
    rw [e₁, e₂, Bool.or_eq_true]

theorem good_iUnion_finset {f : K →+* N} {w : Valuation N Γ'} {ι : Type} (s : Finset ι)
    {b : ι → Set N} (hb : ∀ i ∈ s, Good f w (b i)) : Good f w (⋃ i ∈ s, b i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using good_empty f w
  | insert i s hi ih =>
    have hins : (⋃ j ∈ insert i s, b j) = b i ∪ ⋃ j ∈ s, b j := by
      ext x
      simp only [Set.mem_iUnion, Finset.mem_insert, exists_prop, Set.mem_union]
      constructor
      · rintro ⟨j, hj | hj, hx⟩
        · exact Or.inl (hj ▸ hx)
        · exact Or.inr ⟨j, hj, hx⟩
      · rintro (hx | ⟨j, hj, hx⟩)
        · exact ⟨i, Or.inl rfl, hx⟩
        · exact ⟨j, Or.inr hj, hx⟩
    rw [hins]
    exact good_union (hb i (Finset.mem_insert_self i s))
      (ih fun j hj => hb j (Finset.mem_insert_of_mem hj))

/-- A finite set of points of the image of `K` is good. -/
theorem good_of_finite_range {f : K →+* N} {w : Valuation N Γ'} {D : Set N}
    (hfin : D.Finite) (hsub : D ⊆ Set.range f) : Good f w D := by
  classical
  have hD : D = ⋃ x ∈ hfin.toFinset, ({x} : Set N) := by
    ext y
    constructor
    · intro hy
      exact Set.mem_iUnion.mpr ⟨y, Set.mem_iUnion.mpr ⟨by
        rw [hfin.mem_toFinset]; exact hy, rfl⟩⟩
    · intro hy
      obtain ⟨x, hx⟩ := Set.mem_iUnion.mp hy
      obtain ⟨hxs, hyx⟩ := Set.mem_iUnion.mp hx
      rw [Set.mem_singleton_iff] at hyx
      rw [hyx, ← hfin.mem_toFinset]
      exact hxs
  rw [hD]
  refine good_iUnion_finset (f := f) (w := w) (b := fun x => ({x} : Set N))
    hfin.toFinset (fun x hx => ?_)
  obtain ⟨c, rfl⟩ := hsub (by rwa [hfin.mem_toFinset] at hx)
  exact good_singleton f w c

end Good


/-! ## 4. The term bridge: an `L_val`-term with parameters in `K` is a polynomial over `K`

This is the syntactic half of Johnson's Lemma 2.3.1: the `L_val`-function symbols are `+`, `*`,
`-`, `0`, `1`, so a term in the parameters `K` and one free variable denotes a polynomial with
coefficients in `K`, evaluated in the larger field `N` along the embedding `f`.

The evaluation of terms and of bounded formulas is written through the wrapper definitions
`evalTerm` and `Holds`, which fix the `L_val`-structure on `N` to be `valStructure w`; this keeps
`valStructure` out of the type-class search in the statements. -/

section Poly

variable {K : Type} [Field K] {N : Type} [Field N] {Γ' : Type*} [LinearOrderedCommGroupWithZero Γ']

/-- The polynomial in one variable represented by an `L_val`-term with parameters in `K` and one
free variable. -/
noncomputable def termToPoly : Language.val.Term (K ⊕ Fin 1) → K[X]
  | .var s => Sum.rec (fun k => Polynomial.C k) (fun _ => Polynomial.X) s
  | .func fn args =>
    match fn with
    | ValFunc.add => termToPoly (args 0) + termToPoly (args 1)
    | ValFunc.mul => termToPoly (args 0) * termToPoly (args 1)
    | ValFunc.neg => - termToPoly (args 0)
    | ValFunc.zero => 0
    | ValFunc.one => 1

/-- Evaluation of an `L_val`-term in the valued field `N` (with the structure `valStructure w`). -/
def evalTerm (w : Valuation N Γ') (t : Language.val.Term (K ⊕ Fin 1))
    (v : K ⊕ Fin 1 → N) : N := by
  letI := valStructure w
  exact t.realize v

/-- **The term bridge.**  Evaluation of a term is evaluation of the associated polynomial. -/
theorem eval₂_termToPoly (w : Valuation N Γ') (f : K →+* N)
    (t : Language.val.Term (K ⊕ Fin 1)) (β : N) :
    (termToPoly t).eval₂ f β = evalTerm w t (Sum.elim (fun k => f k) (fun _ => β)) := by
  letI := valStructure w
  change (termToPoly t).eval₂ f β = t.realize (Sum.elim (fun k => f k) (fun _ => β))
  induction t with
  | var s =>
    cases s with
    | inl k => simp [termToPoly]
    | inr i => fin_cases i; simp [termToPoly]
  | func fn args ih =>
    cases fn with
    | add =>
      change Polynomial.eval₂ f β (termToPoly (args 0) + termToPoly (args 1))
        = Term.realize (Sum.elim (fun k => f k) (fun _ => β)) (args 0)
          + Term.realize (Sum.elim (fun k => f k) (fun _ => β)) (args 1)
      rw [Polynomial.eval₂_add, ih 0, ih 1]
    | mul =>
      change Polynomial.eval₂ f β (termToPoly (args 0) * termToPoly (args 1))
        = Term.realize (Sum.elim (fun k => f k) (fun _ => β)) (args 0)
          * Term.realize (Sum.elim (fun k => f k) (fun _ => β)) (args 1)
      rw [Polynomial.eval₂_mul, ih 0, ih 1]
    | neg =>
      change Polynomial.eval₂ f β (- termToPoly (args 0))
        = - Term.realize (Sum.elim (fun k => f k) (fun _ => β)) (args 0)
      rw [Polynomial.eval₂_neg, ih 0]
    | zero =>
      change Polynomial.eval₂ f β (0 : K[X]) = (0 : N)
      rw [Polynomial.eval₂_zero]
    | one =>
      change Polynomial.eval₂ f β (1 : K[X]) = (1 : N)
      rw [Polynomial.eval₂_one]

end Poly

/-! ## 5. The zero set of a polynomial over an algebraically closed field

Johnson 2.3.1(i): over an algebraically closed `K`, the roots in `N` of a polynomial over `K` are
finitely many and lie in the image of `K`.  (Copied from `QE/ACF_validation.lean`, where it is
`finite_rootSet`.) -/

section Roots

variable {K : Type} [Field K] [IsAlgClosed K]
variable {N : Type} [Field N]

theorem finite_rootSet (f : K →+* N) (q : K[X]) (hq : q ≠ 0) :
    {β : N | q.eval₂ f β = 0}.Finite ∧ {β : N | q.eval₂ f β = 0} ⊆ Set.range f := by
  suffices H : ∀ (n : ℕ) (q : K[X]), q.natDegree ≤ n → q ≠ 0 →
      ({β : N | q.eval₂ f β = 0}.Finite ∧
        {β : N | q.eval₂ f β = 0} ⊆ Set.range f) by
    exact H q.natDegree q le_rfl hq
  intro n
  induction n with
  | zero =>
    intro q hn hq
    have hdeg : q.natDegree = 0 := Nat.le_zero.mp hn
    have hqC : q = Polynomial.C (q.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hdeg
    have hc : q.coeff 0 ≠ 0 := by
      intro h; apply hq; rw [hqC, h, Polynomial.C_0]
    have hempty : {β : N | q.eval₂ f β = 0} = ∅ := by
      ext β
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rw [hqC, Polynomial.eval₂_C]
      intro h
      exact hc (f.injective (by simpa using h))
    rw [hempty]
    exact ⟨Set.finite_empty, Set.empty_subset _⟩
  | succ n ih =>
    intro q hn hq
    rcases Nat.eq_zero_or_pos q.natDegree with h0 | hpos
    · have hqC : q = Polynomial.C (q.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero h0
      have hc : q.coeff 0 ≠ 0 := by
        intro h; apply hq; rw [hqC, h, Polynomial.C_0]
      have hempty : {β : N | q.eval₂ f β = 0} = ∅ := by
        ext β
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rw [hqC, Polynomial.eval₂_C]
        intro h
        exact hc (f.injective (by simpa using h))
      rw [hempty]
      exact ⟨Set.finite_empty, Set.empty_subset _⟩
    · have hdeg : q.degree ≠ 0 := by
        rw [Polynomial.degree_eq_natDegree hq]
        simpa using hpos.ne'
      obtain ⟨r, hr⟩ := IsAlgClosed.exists_root q hdeg
      obtain ⟨q₁, hq₁⟩ := (Polynomial.dvd_iff_isRoot (p := q)).2 hr
      have hq₁ne : q₁ ≠ 0 := by
        rintro rfl; rw [mul_zero] at hq₁; exact hq hq₁
      have hdegq : q.natDegree = q₁.natDegree + 1 := by
        rw [hq₁, Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero r) hq₁ne,
          Polynomial.natDegree_X_sub_C, add_comm]
      have hle : q₁.natDegree ≤ n := by omega
      obtain ⟨hfin, hsub⟩ := ih q₁ hle hq₁ne
      have hset : {β : N | q.eval₂ f β = 0}
          = {f r} ∪ {β : N | q₁.eval₂ f β = 0} := by
        ext β
        simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff]
        rw [hq₁]
        simp only [Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_X,
          Polynomial.eval₂_C]
        constructor
        · intro h
          rcases mul_eq_zero.mp h with h' | h'
          · exact Or.inl (sub_eq_zero.mp h')
          · exact Or.inr h'
        · rintro (h' | h')
          · rw [h', sub_self, zero_mul]
          · rw [h', mul_zero]
      rw [hset]
      exact ⟨(Set.finite_singleton _).union hfin,
        Set.union_subset (fun x hx => ⟨r, hx.symm⟩) hsub⟩

end Roots

/-! ## 6. Quantifier-free definable sets are Boolean combinations of balls

The two inputs of Johnson §2.3 that this file does *not* prove are named here as `Prop`s:
`AtomGood` is Lemma 2.3.1(ii) (the valuation inequality `v (P x) ≤ v (Q x)` defines a Boolean
combination of balls), and `GoodMeetsBase` is the conclusion of 2.3.2 together with 2.3.8 (a
nonempty Boolean combination of balls with centre and radius in `K` meets `K`).  Everything
between them is proved here. -/

section Formula

variable {K : Type} [Field K] {N : Type} [Field N] {Γ' : Type*} [LinearOrderedCommGroupWithZero Γ']

/-- Realization of a quantifier-free formula in the valued field `N` along `f : K →+* N`, with the
`L_val`-structure on `N` being `valStructure w`. -/
def Holds (w : Valuation N Γ') (f : K →+* N) (φ : Language.val.BoundedFormula K 1) (a : N) : Prop := by
  letI := valStructure w
  exact φ.Realize (fun k => f k) (fun _ => a)

/-- **Johnson, Lemma 2.3.1(ii)** (input): the value-inequality set `{x : v (P x) ≤ v (Q x)}` is a
Boolean combination of balls with centre and radius in `K`. -/
def AtomGood (f : K →+* N) (w : Valuation N Γ') : Prop :=
  ∀ P Q : K[X], Good f w {x : N | w (P.eval₂ f x) ≤ w (Q.eval₂ f x)}

/-- **Johnson, Lemmas 2.3.2 and 2.3.8** (input, in one piece): a nonempty Boolean combination of
balls with centre and radius in `K` meets the image of `K`. -/
def GoodMeetsBase (f : K →+* N) (w : Valuation N Γ') : Prop :=
  ∀ D : Set N, Good f w D → D.Nonempty → ∃ c : K, f c ∈ D

/-- A **swiss cheese**: a ball `B₀` with centre and radius in `K`, with finitely many balls
`Bᵢ ⊆ B₀` (also with centre and radius in `K`) removed.  (Johnson §2.3.) -/
def SwissCheese (f : K →+* N) (w : Valuation N Γ') (D : Set N) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (B₀ : Set N) (B : ι → Set N),
    IsKBall f w B₀ ∧ (∀ i, IsKBall f w (B i)) ∧ (∀ i, B i ⊆ B₀)
      ∧ D = B₀ \ ⋃ i, B i

/-- **Johnson, Lemma 2.3.2** (input): every Boolean combination of balls with centre and radius in
`K` is a finite union of swiss cheeses. -/
def BoolCombCheese (f : K →+* N) (w : Valuation N Γ') : Prop :=
  ∀ D : Set N, Good f w D →
    ∃ (ι : Type) (_ : Fintype ι) (C : ι → Set N),
      (∀ i, SwissCheese f w (C i)) ∧ D = ⋃ i, C i

/-- **Johnson, Lemma 2.3.8** (input): a nonempty swiss cheese meets the image of `K`. -/
def CheeseMeetsBase (f : K →+* N) (w : Valuation N Γ') : Prop :=
  ∀ D : Set N, SwissCheese f w D → D.Nonempty → ∃ c : K, f c ∈ D

/-- Lemmas 2.3.2 and 2.3.8 together give `GoodMeetsBase`: a nonempty finite union of swiss
cheeses has a nonempty member, which meets the base field. -/
theorem goodMeetsBase_of_swissCheese {f : K →+* N} {w : Valuation N Γ'}
    (h232 : BoolCombCheese f w) (h238 : CheeseMeetsBase f w) : GoodMeetsBase f w := by
  intro D hD hne
  obtain ⟨ι, _, C, hC, hDC⟩ := h232 D hD
  obtain ⟨a, ha⟩ := hne
  rw [hDC] at ha
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp ha
  obtain ⟨c, hc⟩ := h238 (C i) (hC i) ⟨a, hi⟩
  exact ⟨c, by rw [hDC]; exact Set.mem_iUnion.mpr ⟨i, hc⟩⟩

/-- **Johnson, Lemma 2.3.1, assembled**: every quantifier-free `K`-definable subset of `N` in one
variable is a Boolean combination of balls with centre and radius in `K`.  The `{P = 0}` case of
2.3.1(i) is proved (from `IsAlgClosed K`); the case `v (P x) ≤ v (Q x)` is the input
`AtomGood`. -/
theorem good_solSet [IsAlgClosed K] {f : K →+* N} {w : Valuation N Γ'}
    (hAtom : AtomGood f w) (φ : Language.val.BoundedFormula K 1) (hφ : φ.IsQF) :
    Good f w {a : N | Holds w f φ a} := by
  letI := valStructure w
  change Good f w {a : N | φ.Realize (fun k => f k) (fun _ => a)}
  refine BoundedFormula.IsQF.recOn
    (motive := fun ψ _ => Good f w {a : N | ψ.Realize (fun k => f k) (fun _ => a)}) hφ ?_ ?_ ?_
  · -- `⊥`
    have hset : {a : N | (BoundedFormula.falsum : Language.val.BoundedFormula K 1).Realize
        (fun k => f k) (fun _ => a)} = ∅ := by
      ext a
      exact ⟨fun h => h, fun h => h.elim⟩
    rw [hset]
    exact good_empty f w
  · -- atomic
    intro ψ ha
    cases ha with
    | equal t₁ t₂ =>
      have hset : {a : N | (Term.bdEqual t₁ t₂).Realize (fun k => f k) (fun _ => a)}
          = {a : N | (termToPoly t₁ - termToPoly t₂).eval₂ f a = 0} := by
        ext a
        change (evalTerm w t₁ (Sum.elim (fun k => f k) (fun _ => a))
            = evalTerm w t₂ (Sum.elim (fun k => f k) (fun _ => a)))
          ↔ (termToPoly t₁ - termToPoly t₂).eval₂ f a = 0
        rw [← eval₂_termToPoly w f t₁ a, ← eval₂_termToPoly w f t₂ a,
          Polynomial.eval₂_sub, sub_eq_zero]
      rw [hset]
      by_cases hp : termToPoly t₁ - termToPoly t₂ = 0
      · have huniv : {a : N | (termToPoly t₁ - termToPoly t₂).eval₂ f a = 0} = Set.univ := by
          ext a; simp [hp]
        rw [huniv]
        exact good_univ f w
      · exact good_of_finite_range (finite_rootSet f _ hp).1 (finite_rootSet f _ hp).2
    | rel R ts =>
      cases R with
      | le =>
        simp only [Relations.boundedFormula]
        have hset : {a : N | (BoundedFormula.rel ValRel.le ts).Realize (fun k => f k)
              (fun _ => a)}
            = {a : N | w ((termToPoly (ts 0)).eval₂ f a)
                ≤ w ((termToPoly (ts 1)).eval₂ f a)} := by
          ext a
          change (w (evalTerm w (ts 0) (Sum.elim (fun k => f k) (fun _ => a)))
              ≤ w (evalTerm w (ts 1) (Sum.elim (fun k => f k) (fun _ => a))))
            ↔ w ((termToPoly (ts 0)).eval₂ f a) ≤ w ((termToPoly (ts 1)).eval₂ f a)
          rw [← eval₂_termToPoly w f (ts 0) a, ← eval₂_termToPoly w f (ts 1) a]
        rw [hset]
        exact hAtom (termToPoly (ts 0)) (termToPoly (ts 1))
  · -- `⟹`
    intro φ₁ φ₂ _ _ ih1 ih2
    have hset : {a : N | (φ₁.imp φ₂).Realize (fun k => f k) (fun _ => a)}
        = {a : N | φ₁.Realize (fun k => f k) (fun _ => a)}ᶜ
          ∪ {a : N | φ₂.Realize (fun k => f k) (fun _ => a)} := by
      ext a
      simp only [BoundedFormula.realize_imp, Set.mem_ofPred_eq, Set.mem_union,
        Set.mem_compl_iff]
      tauto
    rw [hset]
    exact good_union (good_compl ih1) ih2

/-- **Johnson's 1-ec property for a valued field**: every nonempty quantifier-free `K`-definable
subset of `N` in one variable meets `K`.  This is Claim 2.1.5 in the valued setting: the whole
content of Johnson §2.3 after the two named inputs. -/
theorem exists_solution_in_range [IsAlgClosed K] {f : K →+* N} {w : Valuation N Γ'}
    (hAtom : AtomGood f w) (hMeets : GoodMeetsBase f w)
    (φ : Language.val.BoundedFormula K 1) (hφ : φ.IsQF) (h : ∃ a : N, Holds w f φ a) :
    ∃ c : K, Holds w f φ (f c) := by
  obtain ⟨c, hc⟩ := hMeets _ (good_solSet hAtom φ hφ) ⟨h.choose, h.choose_spec⟩
  exact ⟨c, hc⟩

end Formula


/-! ## 8. Comparability of balls and swiss cheeses (Johnson's Lemma 2.3.2)

This section closes the input `BoolCombCheese` of §6: every Boolean combination of balls with
centre and radius in `K` is a finite union of swiss cheeses.  The proofs are the standard
ultrametric arguments (cf. `QE/Johnson23_valuation.lean`), transported to balls with centre and
radius in the image of the base field. -/

section Comparability

variable {N : Type} [Field N] {Γ' : Type*} [LinearOrderedCommGroupWithZero Γ']

/-- The value of a difference is bounded by the maximum of two others. -/
theorem val_sub_le_max (w : Valuation N Γ') (a b c : N) :
    w (a - c) ≤ max (w (a - b)) (w (b - c)) := by
  have h : a - c = (a - b) + (b - c) := by ring
  rw [h]
  exact map_add_le_max _ _ _

/-- A closed ball grows when the radius grows. -/
theorem closedBall_mono (w : Valuation N Γ') {c₁ c₂ : N} {γ₁ γ₂ : Γ'}
    (h : w (c₁ - c₂) ≤ γ₂) (hγ : γ₁ ≤ γ₂) :
    closedBall w c₁ γ₁ ⊆ closedBall w c₂ γ₂ := by
  intro x hx
  rw [mem_closedBall] at hx ⊢
  exact le_trans (val_sub_le_max w x c₁ c₂) (max_le (le_trans hx hγ) h)

/-- An open ball grows when the radius grows. -/
theorem openBall_mono (w : Valuation N Γ') {c₁ c₂ : N} {γ₁ γ₂ : Γ'}
    (h : w (c₁ - c₂) < γ₂) (hγ : γ₁ ≤ γ₂) :
    openBall w c₁ γ₁ ⊆ openBall w c₂ γ₂ := by
  intro x hx
  rw [mem_openBall] at hx ⊢
  refine lt_of_le_of_lt (val_sub_le_max w x c₁ c₂) (max_lt ?_ h)
  exact lt_of_lt_of_le hx hγ

/-- **Intersecting closed balls are comparable.** -/
theorem closedBall_subset_or_subset (w : Valuation N Γ') {c₁ c₂ : N} {γ₁ γ₂ : Γ'}
    (h : (closedBall w c₁ γ₁ ∩ closedBall w c₂ γ₂).Nonempty) :
    closedBall w c₁ γ₁ ⊆ closedBall w c₂ γ₂ ∨ closedBall w c₂ γ₂ ⊆ closedBall w c₁ γ₁ := by
  obtain ⟨z, hz₁, hz₂⟩ := h
  rw [mem_closedBall] at hz₁ hz₂
  have hz₁' : w (c₁ - z) ≤ γ₁ := by
    rw [show c₁ - z = -(z - c₁) by ring, Valuation.map_neg]; exact hz₁
  have hz₂' : w (c₂ - z) ≤ γ₂ := by
    rw [show c₂ - z = -(z - c₂) by ring, Valuation.map_neg]; exact hz₂
  have h12 : w (c₁ - c₂) ≤ max γ₁ γ₂ :=
    le_trans (val_sub_le_max w c₁ z c₂) (max_le_max hz₁' hz₂)
  have h21 : w (c₂ - c₁) ≤ max γ₂ γ₁ :=
    le_trans (val_sub_le_max w c₂ z c₁) (max_le_max hz₂' hz₁)
  rcases le_total γ₁ γ₂ with hγ | hγ
  · left
    refine closedBall_mono w ?_ hγ
    rwa [max_eq_right hγ] at h12
  · right
    refine closedBall_mono w ?_ hγ
    rwa [max_eq_right hγ] at h21

/-- **Intersecting open balls are comparable.** -/
theorem openBall_subset_or_subset (w : Valuation N Γ') {c₁ c₂ : N} {γ₁ γ₂ : Γ'}
    (h : (openBall w c₁ γ₁ ∩ openBall w c₂ γ₂).Nonempty) :
    openBall w c₁ γ₁ ⊆ openBall w c₂ γ₂ ∨ openBall w c₂ γ₂ ⊆ openBall w c₁ γ₁ := by
  obtain ⟨z, hz₁, hz₂⟩ := h
  rw [mem_openBall] at hz₁ hz₂
  have hz₁' : w (c₁ - z) < γ₁ := by
    rw [show c₁ - z = -(z - c₁) by ring, Valuation.map_neg]; exact hz₁
  have hz₂' : w (c₂ - z) < γ₂ := by
    rw [show c₂ - z = -(z - c₂) by ring, Valuation.map_neg]; exact hz₂
  have h12 : w (c₁ - c₂) < max γ₁ γ₂ :=
    lt_of_le_of_lt (val_sub_le_max w c₁ z c₂) (max_lt_max hz₁' hz₂)
  have h21 : w (c₂ - c₁) < max γ₂ γ₁ :=
    lt_of_le_of_lt (val_sub_le_max w c₂ z c₁) (max_lt_max hz₂' hz₁)
  rcases le_total γ₁ γ₂ with hγ | hγ
  · left
    refine openBall_mono w ?_ hγ
    rwa [max_eq_right hγ] at h12
  · right
    refine openBall_mono w ?_ hγ
    rwa [max_eq_right hγ] at h21

/-- A closed ball of smaller radius inside an open ball. -/
theorem closedBall_subset_openBall (w : Valuation N Γ') {c d : N} {a b : N}
    (hcd : w (c - d) < w b) (ha : w a < w b) :
    closedBall w c (w a) ⊆ openBall w d (w b) := by
  intro x hx
  simp only [mem_closedBall] at hx
  simp only [mem_openBall]
  exact lt_of_le_of_lt (val_sub_le_max w x c d) (max_lt (lt_of_le_of_lt hx ha) hcd)

/-- An open ball inside a closed ball. -/
theorem openBall_subset_closedBall (w : Valuation N Γ') {c d : N} {a b : N}
    (hcd : w (c - d) ≤ w b) (ha : w a ≤ w b) :
    openBall w c (w a) ⊆ closedBall w d (w b) := by
  intro x hx
  simp only [mem_openBall] at hx
  simp only [mem_closedBall]
  exact le_trans (val_sub_le_max w x c d) (max_le (le_of_lt (lt_of_lt_of_le hx ha)) hcd)

/-- The value of `c - d` is at most the larger of two radii, given a common point `z`. -/
theorem val_sub_le_max_of_mem (w : Valuation N Γ') {z c d : N} {a b : N}
    (hz₁ : w (z - c) ≤ w a) (hz₂ : w (z - d) ≤ w b) :
    w (c - d) ≤ max (w a) (w b) := by
  have h1 : w (c - z) ≤ w a := by
    rw [show c - z = -(z - c) by ring, Valuation.map_neg]; exact hz₁
  exact le_trans (val_sub_le_max w c z d) (max_le_max h1 hz₂)

end Comparability

section KBallComparability

variable {K : Type} [Field K] {N : Type} [Field N] {Γ' : Type*} [LinearOrderedCommGroupWithZero Γ']

/-- **Johnson (2.3)** for balls with centre and radius in `K`: two such balls that meet are
comparable. -/
theorem isKBall_subset_or_subset {f : K →+* N} {w : Valuation N Γ'} {B₁ B₂ : Set N}
    (h₁ : IsKBall f w B₁) (h₂ : IsKBall f w B₂) (h : (B₁ ∩ B₂).Nonempty) :
    B₁ ⊆ B₂ ∨ B₂ ⊆ B₁ := by
  obtain ⟨z, hz₁, hz₂⟩ := h
  cases h₁ with
  | univ => exact Or.inr (Set.subset_univ _)
  | closed c a =>
    cases h₂ with
    | univ => exact Or.inl (Set.subset_univ _)
    | closed d b => exact closedBall_subset_or_subset w ⟨z, hz₁, hz₂⟩
    | openball d b =>
      simp only [mem_closedBall] at hz₁
      simp only [mem_openBall] at hz₂
      rcases lt_or_ge (w (f a)) (w (f b)) with hab | hab
      · left
        have h2 : w (z - f d) < w (f b) := hz₂
        refine closedBall_subset_openBall w ?_ hab
        have h3 : w (f c - z) < w (f b) := by
          rw [show f c - z = -(z - f c) by ring, Valuation.map_neg]
          exact lt_of_le_of_lt hz₁ hab
        exact lt_of_le_of_lt (val_sub_le_max w (f c) z (f d)) (max_lt h3 h2)
      · right
        have h2 : w (z - f d) < w (f b) := hz₂
        refine openBall_subset_closedBall (w := w) (c := f d) (d := f c) (a := f b) (b := f a) ?_ hab
        have h1 : w (f d - z) ≤ w (f a) := by
          rw [show f d - z = -(z - f d) by ring, Valuation.map_neg]
          exact le_trans h2.le hab
        have h3 : w (z - f c) ≤ w (f a) := hz₁
        exact le_trans (val_sub_le_max w (f d) z (f c)) (max_le h1 h3)
  | openball c a =>
    simp only [mem_openBall] at hz₁
    cases h₂ with
    | univ => exact Or.inl (Set.subset_univ _)
    | closed d b =>
      simp only [mem_closedBall] at hz₂
      rcases le_or_gt (w (f a)) (w (f b)) with hab | hab
      · left
        refine openBall_subset_closedBall (w := w) ?_ hab
        have h := val_sub_le_max_of_mem w (z := z) hz₁.le hz₂
        rwa [max_eq_right hab] at h
      · right
        refine closedBall_subset_openBall (w := w) (c := f d) (d := f c) (a := f b) (b := f a) ?_ hab
        have h1 : w (f d - z) < w (f a) := by
          rw [show f d - z = -(z - f d) by ring, Valuation.map_neg]
          exact lt_of_le_of_lt hz₂ hab
        have h2 : w (z - f c) < w (f a) := hz₁
        exact lt_of_le_of_lt (val_sub_le_max w (f d) z (f c)) (max_lt h1 h2)
    | openball d b => exact openBall_subset_or_subset w ⟨z, hz₁, hz₂⟩

/-- A nonempty finite intersection of balls of `K`-radius is one of them. -/
theorem exists_mem_of_iInter_finset [DecidableEq ι] {f : K →+* N} {w : Valuation N Γ'}
    {b : ι → Set N} (hb : ∀ i, IsKBall f w (b i)) {S : Finset ι} (hS : S.Nonempty)
    (hne : (⋂ i ∈ S, b i).Nonempty) :
    ∃ j ∈ S, (⋂ i ∈ S, b i) = b j := by
  revert hS hne
  induction S using Finset.induction_on with
  | empty => intro hS; exact absurd hS Finset.not_nonempty_empty
  | insert i S hiS ih =>
    intro hS hne
    by_cases hS' : S.Nonempty
    · have hne' : (⋂ k ∈ S, b k).Nonempty := by
        obtain ⟨x, hx⟩ := hne
        exact ⟨x, by
          simp only [Set.mem_iInter] at hx ⊢
          exact fun k hk => hx k (Finset.mem_insert_of_mem hk)⟩
      obtain ⟨j, hjS, hj⟩ := ih hS' hne'
      have hinter : (⋂ k ∈ insert i S, b k) = b i ∩ b j := by
        rw [show (⋂ k ∈ insert i S, b k) = b i ∩ (⋂ k ∈ S, b k) from by
          ext x; simp [Finset.mem_insert], hj]
      have hne2 : (b i ∩ b j).Nonempty := hinter ▸ hne
      rcases isKBall_subset_or_subset (hb i) (hb j) hne2 with hh | hh
      · exact ⟨i, Finset.mem_insert_self i S, by rw [hinter, Set.inter_eq_left.mpr hh]⟩
      · exact ⟨j, Finset.mem_insert_of_mem hjS, by rw [hinter, Set.inter_eq_right.mpr hh]⟩
    · have hSe : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS'
      subst hSe
      refine ⟨i, Finset.mem_singleton_self i, ?_⟩
      simp

end KBallComparability

/-! ### The cell decomposition and Lemma 2.3.2 -/

section SwissCheese

variable {ι : Type} {K : Type} [Field K] {N : Type} [Field N]
variable {Γ' : Type*} [LinearOrderedCommGroupWithZero Γ']

/-- The cell of a finite set of balls: the points lying in exactly the balls indexed by `S`. -/
def cell [Fintype ι] [DecidableEq ι] (b : ι → Set N) (S : Finset ι) : Set N :=
  (⋂ i ∈ S, b i) \ (⋃ i ∈ Sᶜ, b i)

theorem mem_cell [Fintype ι] [DecidableEq ι] {b : ι → Set N} {S : Finset ι} {x : N} :
    x ∈ cell b S ↔ ∀ i, (x ∈ b i ↔ i ∈ S) := by
  classical
  constructor
  · intro h
    have h1 : ∀ k ∈ S, x ∈ b k := by
      intro k hk
      exact (Set.mem_iInter₂.mp h.1) k hk
    have h2 : ∀ k, k ∉ S → x ∉ b k := by
      intro k hk hx
      exact h.2 (Set.mem_iUnion₂.mpr ⟨k, by simpa using hk, hx⟩)
    exact fun i => ⟨fun hx => by_contra fun hcon => h2 i hcon hx, fun hi => h1 i hi⟩
  · intro h
    refine ⟨Set.mem_iInter₂.mpr fun k hk => (h k).mpr hk, ?_⟩
    intro hx
    obtain ⟨k, hk, hkx⟩ := Set.mem_iUnion₂.mp hx
    have hk' : k ∉ S := by simpa using hk
    exact hk' ((h k).mp hkx)

/-- **The swiss-cheese content of Lemma 2.3.2.**  Every cell of a finite family of balls with
centre and radius in `K` is a swiss cheese over `K`. -/
theorem cell_swissCheese [Fintype ι] [DecidableEq ι] {f : K →+* N} {w : Valuation N Γ'}
    {b : ι → Set N} (hb : ∀ i, IsKBall f w (b i)) (S : Finset ι) :
    ∃ (τ : Type) (_ : Fintype τ) (B₀ : Set N) (B : τ → Set N),
      IsKBall f w B₀ ∧ (∀ j, IsKBall f w (B j)) ∧ (∀ j, B j ⊆ B₀) ∧
        cell b S = B₀ \ ⋃ j, B j := by
  classical
  by_cases hS : S = ∅
  · -- the empty pattern: the whole space minus all the balls
    subst hS
    refine ⟨ι, inferInstance, Set.univ, b, IsKBall.univ, hb, fun _ => Set.subset_univ _, ?_⟩
    ext x
    simp [cell]
  by_cases hne : (⋂ i ∈ S, b i).Nonempty
  · -- the intersection is one of the balls
    obtain ⟨j, hjS, hj⟩ := exists_mem_of_iInter_finset hb (Finset.nonempty_iff_ne_empty.mpr hS) hne
    by_cases hcover : ∃ i ∈ Sᶜ, b j ⊆ b i
    · -- one of the removed balls covers `b j`, so the cell is empty
      obtain ⟨i, hiS, hsub⟩ := hcover
      have hempty : cell b S = ∅ := by
        rw [cell, hj]
        exact Set.diff_eq_empty.mpr (Set.subset_iUnion₂_of_subset i hiS hsub)
      refine ⟨PUnit, inferInstance, Set.univ, fun _ => Set.univ, IsKBall.univ,
        fun _ => IsKBall.univ, fun _ => Set.subset_univ _, ?_⟩
      rw [hempty]
      ext y
      simp
    · -- otherwise the removed balls that matter are the subballs of `b j`
      push_neg at hcover
      refine ⟨{i : ι // i ∉ S ∧ b i ⊆ b j}, inferInstance, b j, fun i => b i.1,
        hb j, fun i => hb i.1, fun i => i.2.2, ?_⟩
      rw [cell, hj, Set.diff_eq]
      ext x
      constructor
      · rintro ⟨hx, hx'⟩
        refine ⟨hx, ?_⟩
        intro hmem
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hmem
        exact hx' (Set.mem_iUnion₂.mpr ⟨i.1, by simpa using i.2.1, hi⟩)
      · rintro ⟨hx, hx'⟩
        refine ⟨hx, ?_⟩
        intro hmem
        obtain ⟨i, hiS, hxi⟩ := Set.mem_iUnion₂.mp hmem
        rcases isKBall_subset_or_subset (hb i) (hb j) ⟨x, hxi, hx⟩ with hsub | hsub
        · exact hx' (Set.mem_iUnion.mpr ⟨⟨i, by simpa using hiS, hsub⟩, hxi⟩)
        · exact absurd hsub (hcover i (by simpa using hiS))
  · -- the intersection is empty, so the cell is empty
    have hempty : (⋂ i ∈ S, b i) = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    refine ⟨PUnit, inferInstance, Set.univ, fun _ => Set.univ, IsKBall.univ,
      fun _ => IsKBall.univ, fun _ => Set.subset_univ _, ?_⟩
    rw [cell, hempty]
    ext y
    simp

/-- **Johnson, Lemma 2.3.2.**  Every Boolean combination of balls with centre and radius in `K`
is a finite union of swiss cheeses over `K`.  (This discharges the input `BoolCombCheese`.) -/
theorem boolCombCheese (f : K →+* N) (w : Valuation N Γ') : BoolCombCheese f w := by
  classical
  intro D hD
  obtain ⟨ι, hι, b, t, hb, ht⟩ := hD
  haveI := hι
  refine ⟨{S : Finset ι // t (S : Set ι) = true}, inferInstance, fun S => cell b S.1,
    fun S => cell_swissCheese hb S.1, ?_⟩
  ext x
  rw [ht x, Set.mem_iUnion]
  constructor
  · intro hx
    have hcoe : ((Finset.univ.filter (fun i => x ∈ b i) : Finset ι) : Set ι) = {i | x ∈ b i} := by
      ext i; simp
    have hS₀t : t ((Finset.univ.filter (fun i => x ∈ b i) : Finset ι) : Set ι) = true := by
      rw [hcoe]; exact hx
    refine ⟨⟨Finset.univ.filter (fun i => x ∈ b i), hS₀t⟩, ?_⟩
    rw [mem_cell]
    intro i
    simp
  · rintro ⟨S, hS⟩
    rw [mem_cell] at hS
    have hpat : ((S.1 : Finset ι) : Set ι) = {i | x ∈ b i} := by
      ext i
      exact (hS i).symm
    rw [← hpat]
    exact S.2

end SwissCheese

/-! ## 7. The 1-ec step in `L_val`

Johnson's hypothesis (iii) of Lemma 2.1.4 for `T` = algebraically closed nontrivially valued
fields, `T₀` = valued fields, stated in the `Valuation` framework (rather than through the
theory `T₀`, which would additionally need the dictionary between `T₀`-models and valued
fields). -/

section OneEC

variable {K : Type} [Field K] {L : Type} [Field L]
variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
variable {Γ' : Type*} [LinearOrderedCommGroupWithZero Γ']

/-- **Johnson, hypothesis (iii) of Lemma 2.1.4, for valued fields.**  An algebraically closed
nontrivially valued field `K` is 1-ec in every valued field extension `L`, modulo the two inputs
`AtomGood` (2.3.1(ii)) and `GoodMeetsBase` (2.3.2 + 2.3.8) of Johnson §2.3. -/
theorem oneECIn_of_inputs (v : Valuation K Γ) (w : Valuation L Γ')
    (F : @FirstOrder.Language.Embedding Language.val K L (valStructure v) (valStructure w))
    [IsAlgClosed K]
    (hAtom : AtomGood (ringHomOfEmbedding v w F) w)
    (h238 : CheeseMeetsBase (ringHomOfEmbedding v w F) w) :
    @OneECIn Language.val K L (valStructure v) (valStructure w) F := by
  intro φ hφ h
  exact exists_solution_in_range hAtom
    (goodMeetsBase_of_swissCheese (boolCombCheese _ w) h238) φ hφ h

/-- The same, with Lemma 2.3.2 also as an explicit hypothesis. -/
theorem oneECIn_of_inputs₃ (v : Valuation K Γ) (w : Valuation L Γ')
    (F : @FirstOrder.Language.Embedding Language.val K L (valStructure v) (valStructure w))
    [IsAlgClosed K]
    (hAtom : AtomGood (ringHomOfEmbedding v w F) w)
    (h232 : BoolCombCheese (ringHomOfEmbedding v w F) w)
    (h238 : CheeseMeetsBase (ringHomOfEmbedding v w F) w) :
    @OneECIn Language.val K L (valStructure v) (valStructure w) F := by
  intro φ hφ h
  exact exists_solution_in_range hAtom (goodMeetsBase_of_swissCheese h232 h238) φ hφ h

/-- The same, from the single packaged input `GoodMeetsBase`. -/
theorem oneECIn_of_inputs' (v : Valuation K Γ) (w : Valuation L Γ')
    (F : @FirstOrder.Language.Embedding Language.val K L (valStructure v) (valStructure w))
    [IsAlgClosed K]
    (hAtom : AtomGood (ringHomOfEmbedding v w F) w)
    (hMeets : GoodMeetsBase (ringHomOfEmbedding v w F) w) :
    @OneECIn Language.val K L (valStructure v) (valStructure w) F := by
  intro φ hφ h
  exact exists_solution_in_range hAtom hMeets φ hφ h

end OneEC

#print axioms ValOneEC.eval₂_termToPoly
#print axioms ValOneEC.good_solSet
#print axioms ValOneEC.exists_solution_in_range
#print axioms ValOneEC.goodMeetsBase_of_swissCheese
#print axioms ValOneEC.boolCombCheese
#print axioms ValOneEC.oneECIn_of_inputs
#print axioms ValOneEC.oneECIn_of_inputs₃
#print axioms ValOneEC.oneECIn_of_inputs'


/-! ## Johnson 2.3.1(ii): the value-inequality set is a Boolean combination of `K`-balls -/

section Atom

open Polynomial

variable {K : Type} [Field K] [IsAlgClosed K] {N : Type} [Field N]
variable {Γ' : Type*} [LinearOrderedCommGroupWithZero Γ']
variable {f : K →+* N} {w : Valuation N Γ'}

/-- Evaluating a polynomial over an algebraically closed field in an extension: the value is the
leading coefficient times the product over the roots in `K` (with multiplicities). -/
theorem eval₂_prod_roots_aux (p : K[X]) (x : N) :
    Polynomial.eval₂ f x ((p.roots.map (fun a => Polynomial.X - Polynomial.C a)).prod)
      = (p.roots.map (fun a => x - f a)).prod := by
  induction p.roots using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Polynomial.eval₂_mul,
      Multiset.map_cons, Multiset.prod_cons, ih]
    simp

theorem eval₂_eq_prod_roots (p : K[X]) (x : N) :
    p.eval₂ f x = f p.leadingCoeff * (p.roots.map (fun a => x - f a)).prod := by
  have hs : p.Splits := IsAlgClosed.splits p
  conv_lhs => rw [hs.eq_prod_roots]
  rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, eval₂_prod_roots_aux]

/-- The same for values. -/
theorem val_eval₂_eq_prod_roots (p : K[X]) (x : N) :
    w (p.eval₂ f x) = w (f p.leadingCoeff) * (p.roots.map (fun a => w (x - f a))).prod := by
  rw [eval₂_eq_prod_roots, map_mul, map_multiset_prod, Multiset.map_map]
  rfl

/-- **Far from the other roots, a factor is constant**: if `x` is closer to `a` than `a` is to
`b`, then `w (x - b) = w (a - b)`. -/
theorem val_sub_eq_of_lt {x : N} {a b : K} (h : w (x - f a) < w (f a - f b)) :
    w (x - f b) = w (f a - f b) := by
  have hsplit : f a - f b = (f a - x) + (x - f b) := by ring
  rcases lt_or_ge (w (x - f b)) (w (f a - f b)) with hlt | hge
  · -- both summands are strictly below `w (a - b)`, so their sum is too
    have h1 : w ((f a - x) + (x - f b)) ≤ max (w (f a - x)) (w (x - f b)) :=
      map_add_le_max w _ _
    have h1' : w (f a - x) = w (x - f a) := by
      rw [show f a - x = -(x - f a) by ring, Valuation.map_neg]
    rw [h1'] at h1
    have hbad : w ((f a - x) + (x - f b)) < w (f a - f b) :=
      lt_of_le_of_lt h1 (max_lt h hlt)
    rw [hsplit] at hbad
    exact absurd hbad (lt_irrefl _)
  · refine le_antisymm ?_ hge
    have h2 : x - f b = (x - f a) + (f a - f b) := by ring
    rw [h2]
    exact le_trans (map_add_le_max w (x - f a) (f a - f b)) (max_le h.le le_rfl)

/-- `P = 0`: the set is everything. -/
theorem atomGood_P_zero (Q : K[X]) :
    Good f w {x : N | w ((0 : K[X]).eval₂ f x) ≤ w (Q.eval₂ f x)} := by
  have h : {x : N | w ((0 : K[X]).eval₂ f x) ≤ w (Q.eval₂ f x)} = Set.univ := by
    ext x
    simp only [Set.mem_setOf_eq, Polynomial.eval₂_zero, map_zero, Set.mem_univ, iff_true]
    exact zero_le
  rw [h]; exact good_univ f w

/-- `Q = 0`: the set is the (finite) root set of `P`. -/
theorem atomGood_Q_zero (P : K[X]) :
    Good f w {x : N | w (P.eval₂ f x) ≤ w ((0 : K[X]).eval₂ f x)} := by
  rcases eq_or_ne P 0 with rfl | hP
  · rw [show {x : N | w ((0 : K[X]).eval₂ f x) ≤ w ((0 : K[X]).eval₂ f x)} = Set.univ from by
      ext x; simp]
    exact good_univ f w
  have h : {x : N | w (P.eval₂ f x) ≤ w ((0 : K[X]).eval₂ f x)} = {x : N | P.eval₂ f x = 0} := by
    ext x
    simp only [Set.mem_setOf_eq, Polynomial.eval₂_zero, map_zero]
    constructor
    · intro hx
      by_contra hne
      exact absurd hx (not_le.mpr (pos_iff_ne_zero.mpr (w.ne_zero_iff.mpr hne)))
    · intro hx; rw [hx, map_zero]
  rw [h]
  exact good_of_finite_range (finite_rootSet f P hP).1 (finite_rootSet f P hP).2

end Atom

/-! ### Closure of `Good` and the regions of the cluster induction -/

section Master

variable {K : Type} [Field K] [IsAlgClosed K] {N : Type} [Field N]
variable {Γ' : Type*} [LinearOrderedCommGroupWithZero Γ']
variable {f : K →+* N} {w : Valuation N Γ'}

/-- A single `K`-ball is a `Good` set. -/
theorem good_of_isKBall {B : Set N} (h : IsKBall f w B) : Good f w B := by
  classical
  refine ⟨PUnit, inferInstance, fun _ => B, fun S => decide S.Nonempty, fun _ => h, ?_⟩
  intro x
  show (x ∈ B) ↔ (decide {i : PUnit | x ∈ B}.Nonempty = true)
  rw [decide_eq_true_iff]
  exact ⟨fun hx => ⟨PUnit.unit, hx⟩, fun ⟨_, hx⟩ => hx⟩

theorem good_inter {D₁ D₂ : Set N} (h₁ : Good f w D₁) (h₂ : Good f w D₂) :
    Good f w (D₁ ∩ D₂) := by
  have h : (D₁ᶜ ∪ D₂ᶜ)ᶜ = D₁ ∩ D₂ := by
    ext x; simp
  rw [← h]
  exact good_compl (good_union (good_compl h₁) (good_compl h₂))

theorem good_diff {D₁ D₂ : Set N} (h₁ : Good f w D₁) (h₂ : Good f w D₂) :
    Good f w (D₁ \ D₂) := by
  rw [Set.diff_eq]
  exact good_inter h₁ (good_compl h₂)

/-- **The near region of a root**: for `a ≠ b`, `{x : w (x - f a) < w (f a - f b)}` is a `K`-ball. -/
theorem good_near {a b : K} : Good f w (openBall w (f a) (w (f a - f b))) := by
  have h : openBall w (f a) (w (f (a - b))) = openBall w (f a) (w (f a - f b)) := by
    rw [map_sub]
  rw [← h]
  exact good_of_isKBall (IsKBall.openball a (a - b))

/-- **The far region**: `{x : w (x - f a) ≥ w (f a - f b)}`. -/
theorem good_far {a b : K} :
    Good f w ((openBall w (f a) (w (f a - f b)))ᶜ) :=
  good_compl good_near

/-- **The sphere**: `{x : w (x - f a) = w (f a - f b)}`, a Boolean combination of `K`-balls. -/
theorem good_sphere {a b : K} :
    Good f w (closedBall w (f a) (w (f a - f b)) \ openBall w (f a) (w (f a - f b))) := by
  have h : closedBall w (f a) (w (f (a - b))) = closedBall w (f a) (w (f a - f b)) := by
    rw [map_sub]
  rw [← h]
  exact good_diff (good_of_isKBall (IsKBall.closed a (a - b))) good_near

/-- A closed `K`-ball of a value radius is `Good`. -/
theorem good_closed {c b : K} : Good f w (closedBall w (f c) (w (f b))) :=
  good_of_isKBall (IsKBall.closed c b)

end Master

/-! ### Multiset product bookkeeping -/

section ProdSplit

variable {K : Type} [Field K] [DecidableEq K] {Γ' : Type*} [LinearOrderedCommGroupWithZero Γ']

/-- The occurrences of one element contribute a power to the product. -/
theorem prod_filter_eq_pow (s : Multiset K) (g : K → Γ') (a : K) :
    ((s.filter (fun b => b = a)).map g).prod = g a ^ (s.count a) := by
  induction s using Multiset.induction with
  | empty => simp
  | cons b s ih =>
    by_cases h : b = a
    · subst h
      rw [Multiset.filter_cons_of_pos (p := fun x => x = b) s rfl,
        Multiset.count_cons_self, Multiset.map_cons, Multiset.prod_cons, ih, pow_succ]
      ac_rfl
    · rw [Multiset.filter_cons_of_neg (p := fun x => x = a) s h,
        Multiset.count_cons_of_ne (Ne.symm h), ih]

/-- **Splitting a product at one element.** -/
theorem prod_split (s : Multiset K) (g : K → Γ') (a : K) :
    (s.map g).prod = g a ^ (s.count a) * ((s.filter (fun b => b ≠ a)).map g).prod := by
  induction s using Multiset.induction with
  | empty => simp
  | cons b s ih =>
    by_cases h : b = a
    · subst h
      rw [Multiset.filter_cons_of_neg (p := fun x => x ≠ b) s (by simp), Multiset.count_cons_self]
      simp only [Multiset.map_cons, Multiset.prod_cons, ih, pow_succ]
      ac_rfl
    · rw [Multiset.filter_cons_of_pos (p := fun x => x ≠ a) s h,
        Multiset.count_cons_of_ne (Ne.symm h)]
      simp only [Multiset.map_cons, Multiset.prod_cons, ih]
      ac_rfl

end ProdSplit

/-! ### The master claim of the cluster induction -/

section GammaAlgebra

variable {Γ' : Type*} [LinearOrderedCommGroupWithZero Γ']

/-- Multiplying by a nonzero power is an order embedding. -/
theorem le_mul_pow_iff {a b δ : Γ'} (hδ : δ ≠ 0) (m : ℕ) :
    a * δ ^ m ≤ b * δ ^ m ↔ a ≤ b := by
  have hcancel : b * δ ^ m * (δ ^ m)⁻¹ = b := by
    rw [mul_assoc, mul_inv_cancel₀ (pow_ne_zero m hδ), mul_one]
  have hcancel' : a * δ ^ m * (δ ^ m)⁻¹ = a := by
    rw [mul_assoc, mul_inv_cancel₀ (pow_ne_zero m hδ), mul_one]
  constructor
  · intro h
    have h' := mul_le_mul_left h ((δ ^ m)⁻¹)
    rwa [hcancel, hcancel'] at h'
  · intro h; exact mul_le_mul_left h _

/-- Multiplying by a nonzero constant: `a / c ≤ b ↔ a ≤ b * c`. -/
theorem le_mul_iff_div {a b c : Γ'} (hc : c ≠ 0) :
    a * c⁻¹ ≤ b ↔ a ≤ b * c := by
  have hcancel : a * c⁻¹ * c = a := by rw [mul_assoc, inv_mul_cancel₀ hc, mul_one]
  have hcancel' : b * c * c⁻¹ = b := by rw [mul_assoc, mul_inv_cancel₀ hc, mul_one]
  constructor
  · intro h
    have h' := mul_le_mul_left h c
    rwa [hcancel] at h'
  · intro h
    have h' := mul_le_mul_left h c⁻¹
    rwa [hcancel'] at h'

end GammaAlgebra

section MasterClaim

variable {K : Type} [Field K] [DecidableEq K] [IsAlgClosed K] {N : Type} [Field N]
variable {Γ' : Type*} [LinearOrderedCommGroupWithZero Γ']
variable {f : K →+* N} {w : Valuation N Γ'}

/-- The set whose `Good`-ness the induction proves. -/
def prodLe (p q : Multiset K) (aP aQ : K) : Set N :=
  {x : N | w (f aP) * (p.map (fun a => w (x - f a))).prod
            ≤ w (f aQ) * (q.map (fun a => w (x - f a))).prod}

/-- If no root occurs, both multisets are empty. -/
theorem eq_zero_of_toFinset_eq_empty {p : Multiset K} (h : p.toFinset = ∅) : p = 0 := by
  rw [Multiset.toFinset_eq_empty] at h
  exact h


/-- **Near region, pointwise**: if `x` is closer to `a` than the nearest other root is to `a`,
then every other root contributes its constant value. -/
theorem val_eq_of_near {p q : Multiset K} {a b : K} (hb : b ∈ p + q)
    (hmin : ∀ c ∈ p + q, c ≠ a → w (f a - f b) ≤ w (f a - f c))
    {x : N} (hx : w (x - f a) < w (f a - f b)) :
    ∀ c ∈ p + q, c ≠ a → w (x - f c) = w (f a - f c) := by
  intro c hc hca
  exact val_sub_eq_of_lt (lt_of_lt_of_le hx (hmin c hc hca))

/-- **Near region, for the product over the roots of one polynomial**: the whole product is a
constant there. -/
theorem prod_map_eq_const_of_near {p q : Multiset K} {a b : K} (hb : b ∈ p + q)
    (hmin : ∀ c ∈ p + q, c ≠ a → w (f a - f b) ≤ w (f a - f c))
    {x : N} (hx : w (x - f a) < w (f a - f b)) :
    ((p.filter (fun c => c ≠ a)).map (fun c => w (x - f c))).prod
      = ((p.filter (fun c => c ≠ a)).map (fun c => w (f a - f c))).prod := by
  have h : (p.filter (fun c => c ≠ a)).map (fun c => w (x - f c))
      = (p.filter (fun c => c ≠ a)).map (fun c => w (f a - f c)) := by
    refine Multiset.map_congr rfl ?_
    intro c hc
    obtain ⟨hcp, hca⟩ := Multiset.mem_filter.mp hc
    exact val_eq_of_near (p := p) (q := q) hb hmin hx c (Multiset.mem_add.mpr (Or.inl hcp)) hca
  rw [h]


/-- The easiest case of the ball condition: equal powers of `δ`.  The set is everything when
`w (f cP) ≤ w (f cQ)`, and the singleton `{f a}` otherwise (at the centre both sides vanish). -/
theorem good_pow_le_pow_same {a cP cQ : K} (m : ℕ) :
    Good f w {x : N | w (f cP) * (w (x - f a)) ^ m ≤ w (f cQ) * (w (x - f a)) ^ m} := by
  by_cases h : w (f cP) ≤ w (f cQ)
  · have hset : {x : N | w (f cP) * (w (x - f a)) ^ m ≤ w (f cQ) * (w (x - f a)) ^ m}
        = Set.univ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact mul_le_mul_left h _
    rw [hset]; exact good_univ f w
  · push_neg at h
    rcases eq_or_ne m 0 with rfl | hm
    · have hset : {x : N | w (f cP) * (w (x - f a)) ^ 0 ≤ w (f cQ) * (w (x - f a)) ^ 0} = ∅ := by
        ext x
        simp only [pow_zero, mul_one, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        exact not_le.mpr h
      rw [hset]; exact good_empty f w
    · have hset : {x : N | w (f cP) * (w (x - f a)) ^ m ≤ w (f cQ) * (w (x - f a)) ^ m}
          = {f a} := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
        constructor
        · intro hx
          by_contra hne
          have hδ : w (x - f a) ≠ 0 := by
            intro h0
            exact hne (sub_eq_zero.mp (w.zero_iff.mp h0))
          have hle : w (f cP) ≤ w (f cQ) :=
            (le_mul_pow_iff (δ := w (x - f a)) hδ m).mp hx
          exact absurd hle (not_le.mpr h)
        · intro hx
          subst hx
          rw [show f a - f a = (0 : N) from sub_self _, map_zero,
            zero_pow hm, mul_zero, mul_zero]
      rw [hset]; exact good_singleton f w a

/-! #### The ball condition with unequal multiplicities -/

/-- `w (f c) = 0` only for `c = 0`. -/
theorem val_eq_zero_iff (c : K) : w (f c) = 0 ↔ c = 0 := by
  rw [w.zero_iff, ← map_zero f, f.injective.eq_iff]

/-- A `d`-th root of a quotient of two values is again a value of `w ∘ f`: `K` is algebraically
closed, so its group of values is divisible. -/
theorem exists_val_pow_div (cP cQ : K) {d : ℕ} (hd : 0 < d) :
    ∃ e : K, w (f e) ^ d = w (f cP) * (w (f cQ))⁻¹ := by
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq (cP * cQ⁻¹) hd
  refine ⟨b, ?_⟩
  rw [← map_pow w (f b), ← map_pow f b d, hb]
  simp only [map_mul, map_inv₀]

/-- `c * a ≤ b ↔ a ≤ b * c⁻¹` for `c ≠ 0`. -/
theorem mul_le_iff_le_mul_inv {a b c : Γ'} (hc : c ≠ 0) : c * a ≤ b ↔ a ≤ b * c⁻¹ := by
  constructor
  · intro h
    have h' := mul_le_mul_left h c⁻¹
    rw [mul_comm c a, mul_assoc, mul_inv_cancel₀ hc, mul_one] at h'
    exact h'
  · intro h
    have h' := mul_le_mul_left h c
    rw [mul_assoc, inv_mul_cancel₀ hc, mul_one] at h'
    rwa [mul_comm c a]

/-- `a ≤ b * c ↔ a * c⁻¹ ≤ b` for `c ≠ 0`. -/
theorem le_mul_iff_mul_inv_le {a b c : Γ'} (hc : c ≠ 0) : a ≤ b * c ↔ a * c⁻¹ ≤ b := by
  constructor
  · intro h
    have h' := mul_le_mul_left h c⁻¹
    rw [mul_assoc, mul_inv_cancel₀ hc, mul_one] at h'
    exact h'
  · intro h
    have h' := mul_le_mul_left h c
    rw [mul_assoc, inv_mul_cancel₀ hc, mul_one] at h'
    exact h'

/-- `a ≤ c * b ↔ a * c⁻¹ ≤ b` for `c ≠ 0`. -/
theorem le_mul_left_iff_mul_inv_le {a b c : Γ'} (hc : c ≠ 0) : a ≤ c * b ↔ a * c⁻¹ ≤ b := by
  rw [mul_comm c b]
  exact le_mul_iff_mul_inv_le hc

/-- **The ball condition when `m < n`.**  With `d = n - m > 0`, off the centre the condition
`c_P δ^m ≤ c_Q δ^{m+d}` reads `w (f e) ≤ δ`, and at the centre it holds exactly when `m > 0`.
Hence the complement of the open ball of radius `w (f e)`, together with the centre if `m > 0`. -/
theorem good_pow_le_pow_lt {a cP cQ e : K} (hcQ : cQ ≠ 0) {m d : ℕ} (hd : 0 < d)
    (he : w (f e) ^ d = w (f cP) * (w (f cQ))⁻¹) :
    Good f w {x : N | w (f cP) * (w (x - f a)) ^ m
      ≤ w (f cQ) * (w (x - f a)) ^ (m + d)} := by
  have hd0 : d ≠ 0 := Nat.pos_iff_ne_zero.mp hd
  have hQ : w (f cQ) ≠ 0 := fun h => hcQ ((val_eq_zero_iff cQ).mp h)
  by_cases hcP : cP = 0
  · have hset : {x : N | w (f cP) * (w (x - f a)) ^ m
        ≤ w (f cQ) * (w (x - f a)) ^ (m + d)} = Set.univ := by
      ext x
      simp only [hcP, map_zero, w.map_zero, zero_mul, Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact zero_le
    rw [hset]; exact good_univ f w
  · have hP : w (f cP) ≠ 0 := fun h => hcP ((val_eq_zero_iff cP).mp h)
    have hfe : w (f e) ≠ 0 := by
      intro h
      have h1 : w (f e) ^ d = 0 := by rw [h]; exact zero_pow hd0
      rw [he] at h1
      exact (mul_ne_zero hP (inv_ne_zero hQ)) h1
    have hoff : ∀ x : N, x ≠ f a →
        (w (f cP) * (w (x - f a)) ^ m ≤ w (f cQ) * (w (x - f a)) ^ (m + d)
          ↔ ¬ w (x - f a) < w (f e)) := by
      intro x hx
      have hδ : w (x - f a) ≠ 0 := fun h => hx (sub_eq_zero.mp (w.zero_iff.mp h))
      have hstep : w (f cQ) * (w (x - f a)) ^ (m + d)
          = (w (f cQ) * (w (x - f a)) ^ d) * (w (x - f a)) ^ m := by
        rw [pow_add, mul_comm ((w (x - f a)) ^ m) ((w (x - f a)) ^ d), mul_assoc]
      rw [hstep, le_mul_pow_iff (δ := w (x - f a)) hδ m, le_mul_left_iff_mul_inv_le hQ, ← he,
        not_lt]
      exact pow_le_pow_iff_left₀ (a := w (f e)) (b := w (x - f a)) zero_le zero_le hd0
    rcases eq_or_ne m 0 with hm | hm
    · subst hm
      have hset : {x : N | w (f cP) * (w (x - f a)) ^ 0
          ≤ w (f cQ) * (w (x - f a)) ^ (0 + d)}
          = (openBall w (f a) (w (f e)))ᶜ := by
        ext x
        simp only [openBall, Set.mem_setOf_eq, Set.mem_compl_iff]
        by_cases hx : x = f a
        · subst hx
          rw [sub_self, w.map_zero, Nat.zero_add, zero_pow hd0, mul_zero, pow_zero, mul_one]
          exact ⟨fun h => False.elim (hP (le_antisymm h zero_le)),
            fun h => False.elim (h (pos_iff_ne_zero.mpr hfe))⟩
        · exact hoff x hx
      rw [hset]
      exact good_compl (good_of_isKBall (IsKBall.openball a e))
    · have hmd : m + d ≠ 0 := by omega
      have hset : {x : N | w (f cP) * (w (x - f a)) ^ m
          ≤ w (f cQ) * (w (x - f a)) ^ (m + d)}
          = {f a} ∪ (openBall w (f a) (w (f e)))ᶜ := by
        ext x
        simp only [openBall, Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff,
          Set.mem_compl_iff]
        by_cases hx : x = f a
        · subst hx
          rw [sub_self, w.map_zero, zero_pow hm, zero_pow hmd, mul_zero, mul_zero]
          exact ⟨fun _ => Or.inl rfl, fun _ => le_refl 0⟩
        · rw [hoff x hx]
          exact ⟨fun h => Or.inr h, fun h => h.elim (fun h' => absurd h' hx) id⟩
      rw [hset]
      exact good_union (good_singleton f w a)
        (good_compl (good_of_isKBall (IsKBall.openball a e)))

/-- **The ball condition when `m > n`.**  With `d = m - n > 0`, the condition
`c_P δ^{n+d} ≤ c_Q δ^n` reads `δ ≤ w (f e)`, and the centre always satisfies it, so the set is
the closed ball of radius `w (f e)`. -/
theorem good_pow_le_pow_gt {a cP cQ e : K} (hcP : cP ≠ 0) {n d : ℕ} (hd : 0 < d)
    (he : w (f e) ^ d = w (f cQ) * (w (f cP))⁻¹) :
    Good f w {x : N | w (f cP) * (w (x - f a)) ^ (n + d)
      ≤ w (f cQ) * (w (x - f a)) ^ n} := by
  have hd0 : d ≠ 0 := Nat.pos_iff_ne_zero.mp hd
  have hP : w (f cP) ≠ 0 := fun h => hcP ((val_eq_zero_iff cP).mp h)
  have hnd : n + d ≠ 0 := by omega
  have hset : {x : N | w (f cP) * (w (x - f a)) ^ (n + d)
      ≤ w (f cQ) * (w (x - f a)) ^ n} = closedBall w (f a) (w (f e)) := by
    ext x
    simp only [closedBall, Set.mem_setOf_eq]
    by_cases hx : x = f a
    · subst hx
      rw [sub_self, w.map_zero, zero_pow hnd, mul_zero]
      rcases eq_or_ne n 0 with hn | hn
      · subst hn
        rw [pow_zero, mul_one]
        exact ⟨fun _ => zero_le, fun _ => zero_le⟩
      · rw [zero_pow hn, mul_zero]
        exact ⟨fun _ => zero_le, fun _ => le_refl 0⟩
    · have hδ : w (x - f a) ≠ 0 := fun h => hx (sub_eq_zero.mp (w.zero_iff.mp h))
      have hstep : w (f cP) * (w (x - f a)) ^ (n + d)
          = (w (f cP) * (w (x - f a)) ^ d) * (w (x - f a)) ^ n := by
        rw [pow_add, mul_comm ((w (x - f a)) ^ n) ((w (x - f a)) ^ d), mul_assoc]
      rw [hstep, le_mul_pow_iff (δ := w (x - f a)) hδ n, mul_le_iff_le_mul_inv hP, ← he]
      exact pow_le_pow_iff_left₀ (a := w (x - f a)) (b := w (f e)) zero_le zero_le hd0
  rw [hset]
  exact good_closed (c := a) (b := e)

/-!
## Johnson 2.3.1(ii) for an algebraically closed base field: the cell decomposition

Write `d_c := w (x - f c)` for `c : K`, `A` for the finite set of roots of `P` and `Q` in `K`
(algebraic closedness makes `P` split, so `w (P x) = w (f P.lc) * ∏_{c ∈ A} d_c ^ (count c)`,
`val_eval₂_eq_prod_roots`), and `γ_{ac} := w (f a - f c)`.

The two ultrametric facts used (both from `w (u + v) ≤ max (w u) (w v)`):

* `closer_eq` : `d_a ≤ d_c ↔ x` lies in the open ball of radius `γ_{ac}` around `f a`, or on the
  sphere of that radius around `f c`, or outside both closed balls;
* `prod_map_split` : if `a` is a nearest root and `S = {c ∈ A | γ_{ac} ≤ d_a}`, then `d_c = d_a`
  for `c ∈ S` (two roots at least as close as `c` forces the max rule) and `d_c = γ_{ac}` for
  `c ∉ S` (`val_sub_eq_of_lt`).

Hence, on the cell `cluster A a S` (a finite intersection of `K`-balls, so `Good`), the product
over `A` collapses to `d_a ^ (∑_{c ∈ S} count c)` times an explicit constant, which is absorbed
into the coefficients by `absorb`; the condition becomes the one-variable inequality
`w (f eP) * δ ^ m ≤ w (f eQ) * δ ^ n` (`good_pow_le_pow`, with `m < n`, `m > n` and `m = n`),
solved by `good_pow_le_pow_lt` / `good_pow_le_pow_gt` / `good_pow_le_pow_same` (the `d`-th root
exists because `K` is algebraically closed, `exists_val_pow_div`).

Since every `x` has a nearest root `a ∈ A` (`Finset.exists_min_image`) and the associated `S` is
determined by `x`, the whole set is the finite union of the `Good` pieces
`cluster A a S ∩ clusterCond …`; `prodLe_good` assembles this and `atomGood_of_isAlgClosed`
transfers it to `AtomGood` via `val_eval₂_eq_prod_roots` and the degenerate cases
`atomGood_P_zero` / `atomGood_Q_zero`.
-/

/-! #### Ultrametric comparisons of distances to the roots -/

/-- `w (f a - f c)` is bounded by the maximum of the two distances of `x` from `f a` and `f c`. -/
theorem val_sub_le_max_of_dist {x : N} (a c : K) :
    w (f a - f c) ≤ max (w (x - f a)) (w (x - f c)) := by
  have h : f a - f c = (f a - x) + (x - f c) := by ring
  rw [h]
  refine le_trans (map_add_le_max w _ _) (le_of_eq ?_)
  rw [show f a - x = -(x - f a) by ring, Valuation.map_neg]

/-- **Closest-root comparison.**  `x` is at least as close to `f a` as to `f c` exactly when one
of three `K`-ball conditions holds: it lies in the open ball of radius `w (f a - f c)` around
`f a`, or on the sphere of that radius around `f c`, or outside both closed balls. -/
theorem closer_eq (a c : K) :
    {x : N | w (x - f a) ≤ w (x - f c)} =
      openBall w (f a) (w (f a - f c))
        ∪ (closedBall w (f c) (w (f a - f c)) \ openBall w (f c) (w (f a - f c)))
        ∪ (closedBall w (f a) (w (f a - f c)) ∪ closedBall w (f c) (w (f a - f c)))ᶜ := by
  have key : ∀ x : N, (w (x - f a) ≤ w (x - f c) ↔
      (w (x - f a) < w (f a - f c) ∨
        (w (x - f c) ≤ w (f a - f c) ∧ w (f a - f c) ≤ w (x - f c)) ∨
        (w (f a - f c) < w (x - f a) ∧ w (f a - f c) < w (x - f c)))) := by
    intro x
    have U1 : w (x - f c) ≤ max (w (x - f a)) (w (f a - f c)) := by
      have h : x - f c = (x - f a) + (f a - f c) := by ring
      rw [h]
      exact map_add_le_max w _ _
    have U2 : w (x - f a) ≤ max (w (x - f c)) (w (f a - f c)) := by
      have h : x - f a = (x - f c) + (f c - f a) := by ring
      rw [h]
      refine le_trans (map_add_le_max w _ _) (le_of_eq ?_)
      rw [show f c - f a = -(f a - f c) by ring, Valuation.map_neg]
    have U3 := val_sub_le_max_of_dist (f := f) (w := w) (x := x) a c
    constructor
    · intro h
      by_cases h1 : w (x - f a) < w (f a - f c)
      · exact Or.inl h1
      · by_cases h2 : w (x - f c) ≤ w (f a - f c)
        · exact Or.inr (Or.inl ⟨h2, le_trans (not_lt.mp h1) h⟩)
        · have h3 : w (x - f c) ≤ w (x - f a) := by
            rw [max_eq_left (not_lt.mp h1)] at U1
            exact U1
          exact Or.inr (Or.inr ⟨lt_of_lt_of_le (not_le.mp h2) h3, not_le.mp h2⟩)
    · rintro (h1 | ⟨h2, h3⟩ | ⟨h2, h3⟩)
      · by_contra hcon
        rw [max_eq_left (not_le.mp hcon).le] at U3
        exact absurd U3 (not_le.mpr h1)
      · rw [max_eq_left h3] at U2
        exact U2
      · rw [max_eq_left h3.le] at U2
        exact U2
  ext x
  have hset : (x ∈ openBall w (f a) (w (f a - f c))
        ∪ (closedBall w (f c) (w (f a - f c)) \ openBall w (f c) (w (f a - f c)))
        ∪ (closedBall w (f a) (w (f a - f c)) ∪ closedBall w (f c) (w (f a - f c)))ᶜ) ↔
      (w (x - f a) < w (f a - f c) ∨
        (w (x - f c) ≤ w (f a - f c) ∧ w (f a - f c) ≤ w (x - f c)) ∨
        (w (f a - f c) < w (x - f a) ∧ w (f a - f c) < w (x - f c))) := by
    simp only [Set.mem_union, Set.mem_diff, Set.mem_compl_iff, mem_openBall, mem_closedBall,
      not_or, not_le, not_lt]
    tauto
  simp only [Set.mem_setOf_eq]
  exact (key x).trans hset.symm

/-- The points at least as close to `f a` as to `f c` form a `Good` set. -/
theorem good_closer (a c : K) : Good f w {x : N | w (x - f a) ≤ w (x - f c)} := by
  rw [closer_eq]
  have hγ : w (f a - f c) = w (f (a - c)) := by rw [← RingHom.map_sub f a c]
  rw [hγ]
  refine good_union (good_union ?_ ?_) ?_
  · exact good_of_isKBall (IsKBall.openball a (a - c))
  · exact good_diff (good_of_isKBall (IsKBall.closed c (a - c)))
      (good_of_isKBall (IsKBall.openball c (a - c)))
  · exact good_compl (good_union (good_of_isKBall (IsKBall.closed a (a - c)))
      (good_of_isKBall (IsKBall.closed c (a - c))))

/-- A finite intersection of `Good` sets is `Good`. -/
theorem good_iInter_finset {ι : Type} (s : Finset ι) {b : ι → Set N}
    (hb : ∀ i ∈ s, Good f w (b i)) : Good f w (⋂ i ∈ s, b i) := by
  classical
  have h : (⋂ i ∈ s, b i) = (⋃ i ∈ s, (b i)ᶜ)ᶜ := by
    ext x
    simp
  rw [h]
  exact good_compl (good_iUnion_finset s fun i hi => good_compl (hb i hi))

/-! #### Multiset products over a superset of the root set -/

/-- A product of distances depends only on the multiplicities of the roots. -/
theorem prod_map_count {p : Multiset K} {A : Finset K} (hA : p.toFinset ⊆ A) (x : N) :
    (p.map (fun c => w (x - f c))).prod = ∏ c ∈ A, (w (x - f c)) ^ (p.count c) := by
  rw [Finset.prod_multiset_map_count]
  refine Finset.prod_subset hA ?_
  intro c _ hc
  have hc' : c ∉ p := by simpa using hc
  rw [Multiset.count_eq_zero_of_notMem hc', pow_zero]

/-- **Splitting a product into the nearest roots and the constant factors.**  If `a` is a nearest
root to `x` and `S` is the set of roots whose distance from `f a` is at most `δ = w (x - f a)`,
then the product over the roots of `p` is `δ ^ (multiplicity in S)` times the product of the
constant values `w (f a - f c)` over the remaining roots. -/
theorem prod_map_split {p : Multiset K} {A : Finset K} (hA : p.toFinset ⊆ A)
    {a : K} {S : Finset K} (hSA : S ⊆ A) {x : N}
    (hcl : ∀ c ∈ A, w (x - f a) ≤ w (x - f c))
    (hS : ∀ c ∈ A, (w (f a - f c) ≤ w (x - f a) ↔ c ∈ S)) :
    (p.map (fun c => w (x - f c))).prod
      = (w (x - f a)) ^ (∑ c ∈ S, p.count c)
        * ∏ c ∈ A \ S, (w (f a - f c)) ^ (p.count c) := by
  have hT : ∀ c ∈ A \ S, (w (x - f c)) ^ (p.count c) = (w (f a - f c)) ^ (p.count c) := by
    intro c hc
    obtain ⟨hcA, hcS⟩ := Finset.mem_sdiff.mp hc
    have hgt : w (x - f a) < w (f a - f c) :=
      not_le.mp fun hle => hcS ((hS c hcA).mp hle)
    rw [val_sub_eq_of_lt hgt]
  have hU : ∀ c ∈ S, (w (x - f c)) ^ (p.count c) = (w (x - f a)) ^ (p.count c) := by
    intro c hc
    have hcA := hSA hc
    have hle : w (f a - f c) ≤ w (x - f a) := (hS c hcA).mpr hc
    have h1 : w (x - f c) ≤ max (w (x - f a)) (w (f a - f c)) := by
      have h : x - f c = (x - f a) + (f a - f c) := by ring
      rw [h]
      exact map_add_le_max w _ _
    rw [max_eq_left hle] at h1
    rw [show w (x - f c) = w (x - f a) from le_antisymm h1 (hcl c hcA)]
  rw [prod_map_count hA x, ← Finset.prod_sdiff hSA,
    Finset.prod_congr rfl hT, Finset.prod_congr rfl hU, Finset.prod_pow_eq_pow_sum]
  exact mul_comm _ _

/-! #### Absorbing the constant factors into a coefficient -/

/-- Multiply a coefficient by the constants `(a - c) ^ (multiplicity of c in p)` for `c ∈ T`. -/
def absorb (aP a : K) (p : Multiset K) (T : Finset K) : K :=
  aP * ∏ c ∈ T, (a - c) ^ (p.count c)

/-- The value of the absorbed coefficient. -/
theorem val_absorb (aP a : K) (p : Multiset K) (T : Finset K) :
    w (f (absorb aP a p T)) = w (f aP) * ∏ c ∈ T, (w (f a - f c)) ^ (p.count c) := by
  have hf : f (absorb aP a p T) = f aP * ∏ c ∈ T, (f a - f c) ^ (p.count c) := by
    unfold absorb
    rw [map_mul, map_prod]
    congr 1
    refine Finset.prod_congr rfl ?_
    intro c _
    rw [map_pow, RingHom.map_sub]
  rw [hf, map_mul, map_prod]
  congr 1
  refine Finset.prod_congr rfl ?_
  intro c _
  rw [map_pow]

/-- The absorbed form of the product, stated so that it can be rewritten in either direction. -/
theorem absorb_mul_pow (aP a : K) (p : Multiset K) (S T : Finset K) (δ : Γ') :
    w (f (absorb aP a p T)) * δ ^ (∑ c ∈ S, p.count c)
      = w (f aP) * (δ ^ (∑ c ∈ S, p.count c)
          * ∏ c ∈ T, (w (f a - f c)) ^ (p.count c)) := by
  rw [val_absorb]
  calc w (f aP) * (∏ c ∈ T, (w (f a - f c)) ^ (p.count c)) * δ ^ (∑ c ∈ S, p.count c)
      = w (f aP) * ((∏ c ∈ T, (w (f a - f c)) ^ (p.count c)) * δ ^ (∑ c ∈ S, p.count c)) :=
        mul_assoc _ _ _
    _ = w (f aP) * (δ ^ (∑ c ∈ S, p.count c)
          * ∏ c ∈ T, (w (f a - f c)) ^ (p.count c)) := by
        rw [mul_comm (∏ c ∈ T, (w (f a - f c)) ^ (p.count c)) (δ ^ (∑ c ∈ S, p.count c))]

/-! #### The one-variable condition -/

/-- A product is nonnegative, so `w (f eP) * δ ^ M ≤ 0` is `{x : δ ^ M = 0}` when `eP ≠ 0`. -/
theorem good_le_zero {a eP : K} (M : ℕ) :
    Good f w {x : N | w (f eP) * (w (x - f a)) ^ M ≤ 0} := by
  rcases eq_or_ne eP 0 with hP | hP
  · have h : {x : N | w (f eP) * (w (x - f a)) ^ M ≤ 0} = Set.univ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true, hP, map_zero, w.map_zero, zero_mul]
      exact zero_le
    rw [h]
    exact good_univ f w
  · have hP' : w (f eP) ≠ 0 := fun h => hP ((val_eq_zero_iff eP).mp h)
    rcases eq_or_ne M 0 with hM | hM
    · have h : {x : N | w (f eP) * (w (x - f a)) ^ M ≤ 0} = ∅ := by
        ext x
        simp only [Set.mem_setOf_eq, hM, pow_zero, mul_one, Set.mem_empty_iff_false, iff_false]
        exact not_le.mpr (pos_iff_ne_zero.mpr hP')
      rw [h]
      exact good_empty f w
    · have h : {x : N | w (f eP) * (w (x - f a)) ^ M ≤ 0} = {f a} := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
        constructor
        · intro hle
          have hzero : w (x - f a) = 0 := by
            by_contra hδ
            exact absurd hle (not_le.mpr (mul_pos (pos_iff_ne_zero.mpr hP')
              (pow_pos (pos_iff_ne_zero.mpr hδ) M)))
          exact sub_eq_zero.mp (w.zero_iff.mp hzero)
        · rintro rfl
          simp [hM]
      rw [h]
      exact good_singleton f w a

/-- **The one-variable condition in full generality**: `w (f eP) * δ ^ m ≤ w (f eQ) * δ ^ n`. -/
theorem good_pow_le_pow (a eP eQ : K) (m n : ℕ) :
    Good f w {x : N | w (f eP) * (w (x - f a)) ^ m ≤ w (f eQ) * (w (x - f a)) ^ n} := by
  rcases lt_trichotomy m n with h | h | h
  · obtain ⟨d, hd⟩ : ∃ d, n = m + d := ⟨n - m, (Nat.add_sub_cancel' h.le).symm⟩
    have hd0 : 0 < d := by omega
    rw [hd]
    rcases eq_or_ne eQ 0 with hQ | hQ
    · simp only [hQ, map_zero, w.map_zero, zero_mul]
      exact good_le_zero m
    · obtain ⟨e, he⟩ := exists_val_pow_div (w := w) eP eQ hd0
      exact good_pow_le_pow_lt hQ hd0 he
  · subst h
    exact good_pow_le_pow_same m
  · obtain ⟨d, hd⟩ : ∃ d, m = n + d := ⟨m - n, (Nat.add_sub_cancel' h.le).symm⟩
    have hd0 : 0 < d := by omega
    rw [hd]
    rcases eq_or_ne eP 0 with hP | hP
    · have hset : {x : N | w (f eP) * (w (x - f a)) ^ (n + d)
          ≤ w (f eQ) * (w (x - f a)) ^ n} = Set.univ := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true, hP, map_zero, w.map_zero, zero_mul]
        exact zero_le
      rw [hset]
      exact good_univ f w
    · obtain ⟨e, he⟩ := exists_val_pow_div (w := w) eQ eP hd0
      exact good_pow_le_pow_gt hP hd0 he

/-! #### The cells of the decomposition -/

/-- The cell indexed by a nearest root `a ∈ A` and the set `S` of roots at distance at most
`δ = w (x - f a)` from `f a`. -/
def cluster (f : K →+* N) (w : Valuation N Γ') (A : Finset K) (a : K)
    (S : Finset K) : Set N :=
  {x : N | (∀ c ∈ A, w (x - f a) ≤ w (x - f c)) ∧
    ∀ c ∈ A, (w (f a - f c) ≤ w (x - f a) ↔ c ∈ S)}

/-- A cell is a finite intersection of `K`-balls. -/
theorem cluster_eq_iInter (A : Finset K) (a : K) (S : Finset K) :
    cluster f w A a S = ⋂ c ∈ A, ({x : N | w (x - f a) ≤ w (x - f c)}
      ∩ (if c ∈ S then (openBall w (f a) (w (f a - f c)))ᶜ
         else openBall w (f a) (w (f a - f c)))) := by
  ext x
  simp only [cluster, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_inter_iff, Set.mem_compl_iff,
    mem_openBall]
  constructor
  · rintro ⟨h1, h2⟩ c hc
    refine ⟨h1 c hc, ?_⟩
    by_cases hcS : c ∈ S
    · rw [if_pos hcS]
      exact not_lt.mpr ((h2 c hc).mpr hcS)
    · rw [if_neg hcS]
      exact not_le.mp fun hle => hcS ((h2 c hc).mp hle)
  · intro h
    refine ⟨fun c hc => (h c hc).1, fun c hc => ?_⟩
    by_cases hcS : c ∈ S
    · have h2 := (h c hc).2
      rw [if_pos hcS] at h2
      exact ⟨fun _ => hcS, fun _ => not_lt.mp h2⟩
    · have h2 := (h c hc).2
      rw [if_neg hcS] at h2
      exact ⟨fun hle => absurd hle (not_le.mpr h2), fun hc' => absurd hc' hcS⟩

theorem cluster_good (A : Finset K) (a : K) (S : Finset K) : Good f w (cluster f w A a S) := by
  rw [cluster_eq_iInter]
  refine good_iInter_finset A fun c _ => ?_
  by_cases hcS : c ∈ S
  · rw [if_pos hcS]
    exact good_inter (good_closer a c) (good_compl (good_near (a := a) (b := c)))
  · rw [if_neg hcS]
    exact good_inter (good_closer a c) (good_near (a := a) (b := c))

/-- The reduced one-variable condition on a cell: only the distance `δ = w (x - f a)` survives,
with the multiplicities of the roots of `S` as exponents. -/
def clusterCond (f : K →+* N) (w : Valuation N Γ') (p q : Multiset K) (aP aQ a : K)
    (A S : Finset K) : Set N :=
  {x : N | w (f (absorb aP a p (A \ S))) * (w (x - f a)) ^ (∑ c ∈ S, p.count c)
      ≤ w (f (absorb aQ a q (A \ S))) * (w (x - f a)) ^ (∑ c ∈ S, q.count c)}

theorem clusterCond_good (p q : Multiset K) (aP aQ a : K) (A S : Finset K) :
    Good f w (clusterCond f w p q aP aQ a A S) :=
  good_pow_le_pow (f := f) (w := w) a (absorb aP a p (A \ S)) (absorb aQ a q (A \ S))
    (∑ c ∈ S, p.count c) (∑ c ∈ S, q.count c)

/-- **On a cell the compound condition reduces to the one-variable condition.** -/
theorem prodLe_iff_clusterCond {p q : Multiset K} {A : Finset K} (hp : p.toFinset ⊆ A)
    (hq : q.toFinset ⊆ A) {aP aQ a : K} {S : Finset K} (hSA : S ⊆ A) {x : N}
    (hx : x ∈ cluster f w A a S) :
    x ∈ prodLe (f := f) (w := w) p q aP aQ ↔ x ∈ clusterCond f w p q aP aQ a A S := by
  obtain ⟨hcl, hS⟩ := hx
  rw [prodLe, Set.mem_setOf_eq, prod_map_split hp hSA hcl hS,
    prod_map_split hq hSA hcl hS, clusterCond, Set.mem_setOf_eq,
    ← absorb_mul_pow aP a p S (A \ S) (w (x - f a)),
    ← absorb_mul_pow aQ a q S (A \ S) (w (x - f a))]

/-- **The compound condition is `Good`**: a finite union of cells, on each of which it reduces to
a one-variable condition. -/
theorem prodLe_good (p q : Multiset K) (aP aQ : K) :
    Good f w (prodLe (f := f) (w := w) p q aP aQ) := by
  classical
  set A : Finset K := p.toFinset ∪ q.toFinset with hA
  have hp : p.toFinset ⊆ A := hA ▸ Finset.subset_union_left
  have hq : q.toFinset ⊆ A := hA ▸ Finset.subset_union_right
  rcases A.eq_empty_or_nonempty with hAe | hAn
  · have hp0 : p = 0 := by
      refine eq_zero_of_toFinset_eq_empty ?_
      rw [hA] at hAe
      exact (Finset.union_eq_empty.mp hAe).1
    have hq0 : q = 0 := by
      refine eq_zero_of_toFinset_eq_empty ?_
      rw [hA] at hAe
      exact (Finset.union_eq_empty.mp hAe).2
    subst hp0
    subst hq0
    simp only [prodLe, Multiset.map_zero, Multiset.prod_zero, mul_one]
    by_cases hle : w (f aP) ≤ w (f aQ)
    · have h : {x : N | w (f aP) ≤ w (f aQ)} = Set.univ := by
        ext x
        simp [hle]
      rw [h]
      exact good_univ f w
    · have h : {x : N | w (f aP) ≤ w (f aQ)} = ∅ := by
        ext x
        simp [hle]
      rw [h]
      exact good_empty f w
  · have hcover : prodLe (f := f) (w := w) p q aP aQ
        = ⋃ a ∈ A, ⋃ S ∈ A.powerset, (cluster f w A a S ∩ clusterCond f w p q aP aQ a A S) := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_inter_iff]
      constructor
      · intro hx
        obtain ⟨a, haA, hmin⟩ := Finset.exists_min_image A (fun c => w (x - f c)) hAn
        refine ⟨a, haA, A.filter (fun c => w (f a - f c) ≤ w (x - f a)),
          Finset.mem_powerset.mpr (Finset.filter_subset _ _), ⟨?_, ?_⟩, ?_⟩
        · exact fun c hc => hmin c hc
        · intro c hc
          rw [Finset.mem_filter]
          exact ⟨fun h => ⟨hc, h⟩, fun h => h.2⟩
        · exact (prodLe_iff_clusterCond hp hq (Finset.filter_subset _ _)
            ⟨fun c hc => hmin c hc, fun c hc => by
              rw [Finset.mem_filter]
              exact ⟨fun h => ⟨hc, h⟩, fun h => h.2⟩⟩).mp hx
      · rintro ⟨a, _, S, hS, hx, hx'⟩
        exact (prodLe_iff_clusterCond hp hq (Finset.mem_powerset.mp hS) hx).mpr hx'
    rw [hcover]
    refine good_iUnion_finset A fun a _ => good_iUnion_finset A.powerset fun S _ => ?_
    exact good_inter (cluster_good A a S) (clusterCond_good p q aP aQ a A S)

/-- **Johnson's Lemma 2.3.1(ii)** for an algebraically closed base field. -/
theorem atomGood_of_isAlgClosed {K : Type} [Field K] [DecidableEq K] [IsAlgClosed K]
    {N : Type} [Field N] {Γ' : Type*} [LinearOrderedCommGroupWithZero Γ']
    {f : K →+* N} {w : Valuation N Γ'} : AtomGood f w := by
  intro P Q
  rcases eq_or_ne P 0 with hP | hP
  · subst hP
    exact atomGood_P_zero Q
  rcases eq_or_ne Q 0 with hQ | hQ
  · subst hQ
    exact atomGood_Q_zero P
  have hset : {x : N | w (P.eval₂ f x) ≤ w (Q.eval₂ f x)}
      = prodLe (f := f) (w := w) P.roots Q.roots P.leadingCoeff Q.leadingCoeff := by
    ext x
    simp only [prodLe, Set.mem_setOf_eq, val_eval₂_eq_prod_roots]
  rw [hset]
  exact prodLe_good (f := f) (w := w) P.roots Q.roots P.leadingCoeff Q.leadingCoeff

end MasterClaim


#print axioms ValOneEC.good_pow_le_pow_same
#print axioms ValOneEC.good_pow_le_pow_lt
#print axioms ValOneEC.good_pow_le_pow_gt
#print axioms ValOneEC.exists_val_pow_div
#print axioms ValOneEC.atomGood_of_isAlgClosed
#print axioms ValOneEC.prodLe_good
