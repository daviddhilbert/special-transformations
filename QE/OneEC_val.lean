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

**Not proved here: `AtomGood`.**  It is the one genuinely analytic step left.  Two things make it
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

