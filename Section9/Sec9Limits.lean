module

/-
# Section 9 of Yin, "Special transformations in algebraically closed valued fields"
(arXiv:1006.2467): the two limit lemmas of the differentiation section.

Yin §9 (`paper.tex:1896`) first sets up a notion of *limit* of a definable function
`f : A → 𝓟(VF^m)` at a point `ā ∈ VF^n` (Definition, `paper.tex:1903`), and then proves

* Lemma `union:lim` (`paper.tex:1917`): the limit of `f₁ ∪ f₂` is `L₁ ∪ L₂`;
* Lemma `fin:lim:bounded` (`paper.tex:1924`): if `f` has finite images of size at most `k`, `A`
  contains a punctured ball around `a`, and `lim f = L` is finite, then `|L| ≤ k`.

These are the two lemmas this file formalises, together with the limit apparatus they use.

## Setting

`Γ` is the value group, written additively (the paper writes `-γ` in `paper.tex:1902`), and `vv` is
the valuation `VF → Γ ∪ {∞}`; `vv (x - y) > γ` reads "`x` and `y` are `γ`-close".  Only this much
of the theory of a valued field is used by §9's limit lemmas, so `NAdvf` bundles exactly it (the
field multiplication is not used anywhere in this layer).  Note that the paper's "radius" is
inverse to inclusion — a *larger* `γ` gives a *smaller* ball (`ballV_anti`) — so the paper's "for a
sufficiently large `δ ∈ Γ`" means "for a sufficiently small ball", and where two conditions at
radii `δ₁`, `δ₂` are combined one takes `max δ₁ δ₂`.

## What is proved, and what is a hypothesis

* `LimitSet`, `MinimalLimit`, `IsClosed`, `IsLimit` — Definition (`paper.tex:1903`), the definition
  of minimality (`paper.tex:1906`), closedness, and the paper's `lim f = L` — *"`L` is a closed
  (hence the unique) minimal limit set of `f` at `ā`"* (`paper.tex:1915`) — as `Prop`s.
* `union_lim` — Lemma `union:lim`, **proved**; the paper's proof steps are factored into
  `isolated_of_minimalLimit`, `exists_isolating_ball` and `not_limitSet_erase_aux`.
* `exists_uniform_disjoint_ballV` — the paper's step *"Let `α ∈ Γ` be such that
  `go(b̄_i,α) ∩ go(b̄_j,α) = ∅` whenever `i ≠ j`"* (`paper.tex:1928`), **proved** from `L` finite
  and the ultrametric inequality; it is *not* a hypothesis of `fin_lim_bounded`.
* `fin_lim_bounded` — Lemma `fin:lim:bounded`, **proved**, from two explicit named hypotheses:
  `hcmin`, the paper's *"By `C`-minimality, some `A_D ∪ {a}` contains an open ball around `a`"*
  (`paper.tex:1932`), and `hdefAD`, the paper's *"Each `A_D` is `seq{L,α}`-definable"*
  (`paper.tex:1932`).  Neither is an `axiom`, and nothing else in the paper's proof is assumed.

## Deviations from the paper's wording, stated explicitly

1. Limit sets are taken inside `VF^m`, i.e. `L : Set (Fin m → K)`.  The paper allows
   `L ⊆ PP(VF)^m`, i.e. the formal point `p_∞` (recorded below as `PP`, `ptV`, `ballP`) may occur in
   a limit set.  The ball system of `PP(VF)^m` is *not* an ultrametric ball system: if `vv a > 0`
   then `a ∈ go(p_∞, 0)`, and every ball around `a` meets `go(p_∞,0)`, so the two properties the
   paper's proofs actually use — "two points of a ball are close to each other"
   (`mem_ballV_of_mem_ballV`) and "distinct points have disjoint small balls"
   (`exists_disjoint_ballV`, which is what the `α` of `paper.tex:1928` is for) — both fail for a
   `p_∞`-coordinate.  They are true in `VF^m`, and both proofs are carried out here in the form in
   which the paper uses them.
2. `fin_lim_bounded` is stated for `ā ∈ VF^n` rather than `a ∈ VF` (`n = 1`); the paper's proof is
   verbatim the same (nothing in it looks at a coordinate of `a`), so this is a strengthening.
3. `Def` is the paper's notion of definability (in the encoding of `Milestone0/Encoding.lean`,
   `Sec4Dim.Definable`).  It is carried as a parameter, so the lemmas hold for *every* `Def`; the
   paper's proofs never unfold "definable".  It is used in `fin_lim_bounded` only where the paper
   uses it, in the C-minimality step, which is a statement about definable sets.
-/
public import Mathlib

@[expose] public section

set_option autoImplicit false
set_option linter.unusedVariables false

namespace YinSec9

open Set

universe u v

/-! ## The `VF`-sort with a point at infinity, and the value group -/

/-- `VF ∪ {p_∞}`, the paper's `PP(VF)` (`paper.tex:1900`):

> In the discussion below it is convenient to think that there is a "point at infinity" in the
> `VF`-sort, denoted by `p_∞`.  The set `VF ∪ {p_∞}` is denoted by `PP(VF)`.

*"We emphasize that `p_∞` will not be treated as a real point.  It is merely a notational device
that allows us to discuss complements of balls around `0` more efficiently."* -/
inductive PP (K : Type u) : Type u where
  | fin (x : K) : PP K
  | infty : PP K

/-- A valued field in the shape needed by §9's limit layer (`paper.tex:1896`): `K` is the `VF`-sort
(an additive group; §9's limits never use multiplication), `Γ` the value group (an ordered abelian
group, written additively — the paper writes `-γ` in `paper.tex:1902`), and `vv` the valuation, with
`vv (x - y) > γ` reading "`x` and `y` are `γ`-close".

Only nondegeneracy, invariance under negation and the ultrametric inequality are assumed; nothing
else about a valued field is used by Lemma `union:lim` or Lemma `fin:lim:bounded`. -/
structure NAdvf (K : Type u) (Γ : Type v) [AddCommGroup K] [AddCommGroup Γ] [LinearOrder Γ]
    [IsOrderedAddMonoid Γ] where
  /-- The valuation `VF → Γ ∪ {∞}`. -/
  vv : K → WithTop Γ
  /-- `vv x = ∞` exactly at `x = 0`. -/
  vv_eq_top : ∀ x : K, vv x = ⊤ ↔ x = 0
  /-- `vv` is invariant under negation. -/
  vv_neg : ∀ x : K, vv (-x) = vv x
  /-- The ultrametric inequality `vv (x + y) ≥ min (vv x) (vv y)`. -/
  vv_add : ∀ x y : K, min (vv x) (vv y) ≤ vv (x + y)

namespace NAdvf

variable {K : Type u} {Γ : Type v} [AddCommGroup K] [AddCommGroup Γ] [LinearOrder Γ]
  [IsOrderedAddMonoid Γ]

/-! ### Elementary properties of the valuation -/

theorem vv_zero (F : NAdvf K Γ) : F.vv 0 = ⊤ := (F.vv_eq_top 0).mpr rfl

theorem vv_sub_comm (F : NAdvf K Γ) (x y : K) : F.vv (x - y) = F.vv (y - x) := by
  rw [show y - x = -(x - y) by abel, F.vv_neg]

theorem min_vv_le_vv_sub (F : NAdvf K Γ) (x y z : K) :
    min (F.vv (x - y)) (F.vv (y - z)) ≤ F.vv (x - z) := by
  have h := F.vv_add (x - y) (y - z)
  rwa [show x - y + (y - z) = x - z by abel] at h

/-! ### Balls -/

/-- The paper's open ball `go(b̄, ε)` around a point `b̄` of the `VF`-sort (`paper.tex:1902`):
`x̄ ∈ go(b̄,ε) ↔ vv (x̄_i - b̄_i) > ε` for every coordinate `i`. -/
def ballV (F : NAdvf K Γ) {m : ℕ} (b : Fin m → K) (ε : Γ) : Set (Fin m → K) :=
  {x | ∀ i, (ε : WithTop Γ) < F.vv (x i - b i)}

/-- Balls are antitone in the radius: a *larger* `ε` gives a *smaller* ball (`paper.tex:1902`;
this is why the paper's "for a sufficiently large `δ ∈ Γ`" means "for a sufficiently small
ball"). -/
theorem ballV_anti (F : NAdvf K Γ) {m : ℕ} {b : Fin m → K} {ε ε' : Γ} (h : ε ≤ ε') :
    ballV F b ε' ⊆ ballV F b ε := by
  intro x hx i
  exact lt_of_le_of_lt (WithTop.coe_le_coe.mpr h) (hx i)

/-- The centre of a ball lies in it. -/
theorem mem_ballV_self (F : NAdvf K Γ) {m : ℕ} (b : Fin m → K) (ε : Γ) :
    b ∈ ballV F b ε := by
  intro i
  simpa [sub_self, F.vv_zero] using WithTop.coe_lt_top (a := ε)

/-- **Two points of a ball are close to each other**: if `x` and `d` both lie in the ball of radius
`ε` around `b`, then `d` lies in the ball of radius `ε` around `x`.  (This is the ultrametric step
by which the paper's proof of Lemma `union:lim` turns "`x ∈ go(b̄,ε)` and `x ∈ go(d̄,ε)`" into
"`d̄ ∈ go(b̄,ε)`".) -/
theorem mem_ballV_of_mem_ballV (F : NAdvf K Γ) {m : ℕ} {b d x : Fin m → K} {ε : Γ}
    (hb : x ∈ ballV F b ε) (hd : x ∈ ballV F d ε) : d ∈ ballV F b ε := by
  intro i
  have h1 : (ε : WithTop Γ) < F.vv (x i - b i) := hb i
  have h2 : (ε : WithTop Γ) < F.vv (x i - d i) := hd i
  have h3 := F.min_vv_le_vv_sub (d i) (x i) (b i)
  rw [F.vv_sub_comm (d i) (x i)] at h3
  exact lt_of_lt_of_le (lt_min h2 h1) h3

/-- The symmetric form: two points `x`, `q` of a ball around `b` are `ε`-close to each other. -/
theorem mem_ballV_of_mem_ballV' (F : NAdvf K Γ) {m : ℕ} {b q x : Fin m → K} {ε : Γ}
    (hx : x ∈ ballV F b ε) (hq : q ∈ ballV F b ε) : x ∈ ballV F q ε := by
  intro i
  have h1 : (ε : WithTop Γ) < F.vv (x i - b i) := hx i
  have h2 : (ε : WithTop Γ) < F.vv (q i - b i) := hq i
  have h3 := F.min_vv_le_vv_sub (x i) (b i) (q i)
  have h2' : (ε : WithTop Γ) < F.vv (b i - q i) := by rwa [F.vv_sub_comm (q i) (b i)] at h2
  exact lt_of_lt_of_le (lt_min h1 h2') h3

/-- **Distinct points have disjoint small balls** (in the `VF`-sort): the paper's step
*"Let `α ∈ Γ` be such that `go(b̄_i,α) ∩ go(b̄_j,α) = ∅` whenever `i ≠ j`"* (`paper.tex:1928`),
for one pair.  Proved from the ultrametric inequality: take `α = vv(b₁ - b₂)`. -/
theorem exists_disjoint_ballV (F : NAdvf K Γ) {m : ℕ} {b₁ b₂ : Fin m → K} (h : b₁ ≠ b₂) :
    ∃ α : Γ, Disjoint (ballV F b₁ α) (ballV F b₂ α) := by
  obtain ⟨i, hi⟩ : ∃ i, b₁ i ≠ b₂ i := by
    by_contra hc
    push Not at hc
    exact h (funext hc)
  have hne : F.vv (b₁ i - b₂ i) ≠ ⊤ := by
    rw [ne_eq, F.vv_eq_top]
    exact sub_ne_zero.mpr hi
  obtain ⟨α, hα⟩ := WithTop.ne_top_iff_exists.mp hne
  refine ⟨α, ?_⟩
  rw [Set.disjoint_left]
  intro x hx1 hx2
  have h1 : (α : WithTop Γ) < F.vv (x i - b₁ i) := hx1 i
  have h2 : (α : WithTop Γ) < F.vv (x i - b₂ i) := hx2 i
  have h3 := F.min_vv_le_vv_sub (b₁ i) (x i) (b₂ i)
  rw [F.vv_sub_comm (b₁ i) (x i), ← hα] at h3
  exact absurd (lt_of_lt_of_le (lt_min h1 h2) h3) (lt_irrefl _)

/-- **The paper's uniform separation radius** (`paper.tex:1928`): for a finite set `L` of points of
the `VF`-sort there is a single `α` such that the balls of radius `α` around distinct points of `L`
are pairwise disjoint.  (The paper's `L` is finite at that point of the proof.) -/
theorem exists_uniform_disjoint_ballV (F : NAdvf K Γ) {m : ℕ} {L : Set (Fin m → K)}
    (hL : L.Finite) :
    ∃ α : Γ, ∀ b₁ ∈ L, ∀ b₂ ∈ L, b₁ ≠ b₂ → Disjoint (ballV F b₁ α) (ballV F b₂ α) := by
  classical
  have hLf : L.Finite := hL
  letI := hL.fintype
  let Pair := {p : L × L // p.1 ≠ p.2}
  have hex : ∀ p : Pair, ∃ α : Γ,
      Disjoint (ballV F ((p.1.1 : L) : Fin m → K) α) (ballV F ((p.1.2 : L) : Fin m → K) α) :=
    fun p => exists_disjoint_ballV F (fun h => p.2 (Subtype.coe_injective h))
  let thr : Pair → Γ := fun p => Classical.choose (hex p)
  have hthr : ∀ p : Pair,
      Disjoint (ballV F ((p.1.1 : L) : Fin m → K) (thr p))
        (ballV F ((p.1.2 : L) : Fin m → K) (thr p)) := fun p => Classical.choose_spec (hex p)
  rcases isEmpty_or_nonempty Pair with hemp | hp
  · refine ⟨0, fun b₁ hb₁ b₂ hb₂ hne' => ?_⟩
    exact (hemp.false ⟨(⟨b₁, hb₁⟩, ⟨b₂, hb₂⟩),
      fun h => hne' (congrArg Subtype.val h)⟩).elim
  · haveI : Nonempty Pair := hp
    refine ⟨Finset.univ.sup' Finset.univ_nonempty thr,
      fun b₁ hb₁ b₂ hb₂ hne' => ?_⟩
    let p : Pair := ⟨(⟨b₁, hb₁⟩, ⟨b₂, hb₂⟩), fun h => hne' (congrArg Subtype.val h)⟩
    have hle : thr p ≤ Finset.univ.sup' Finset.univ_nonempty thr :=
      Finset.le_sup' thr (Finset.mem_univ p)
    exact Disjoint.mono (ballV_anti F hle) (ballV_anti F hle) (hthr p)

/-! ### The paper's `p_∞`-balls, and their relation to `ballV` -/

/-- The inclusion `VF^m ↪ PP(VF)^m`. -/
def ptV {K : Type u} {m : ℕ} (x : Fin m → K) : Fin m → PP K := fun i => .fin (x i)

/-- The paper's balls around points of `PP(VF)^m` (`paper.tex:1900`): for a finite coordinate the
ball is the usual one, and for the coordinate `p_∞`,
`go(p_∞,γ) = VF \ gc(0,-γ) = {x : vv x > -γ}` ("Balls around `p_∞` are defined in a reversed way").
A ball never contains `p_∞` as a point: *"`p_∞` will not be treated as a real point"*. -/
def ballP (F : NAdvf K Γ) {m : ℕ} (b : Fin m → PP K) (ε : Γ) : Set (Fin m → K) :=
  {x | ∀ i, match b i with
    | .fin a => (ε : WithTop Γ) < F.vv (x i - a)
    | .infty => ((-ε : Γ) : WithTop Γ) < F.vv (x i)}

/-- For a tuple of finite points, the `p_∞`-ball is the ordinary ball. -/
theorem ballP_ptV (F : NAdvf K Γ) {m : ℕ} (b : Fin m → K) (ε : Γ) :
    ballP F (ptV b) ε = ballV F b ε := rfl


end NAdvf


/-! ## Limit sets -/

/-- Membership in a union of balls, in the form the paper writes `x̄ ∈ ⋃_{b̄ ∈ L'} go(b̄,ε)`. -/
theorem mem_biUnion_ball {K : Type u} {Γ : Type v} [AddCommGroup K] [AddCommGroup Γ]
    [LinearOrder Γ] [IsOrderedAddMonoid Γ] (F : NAdvf K Γ) {m : ℕ} {S : Set (Fin m → K)}
    {x : Fin m → K} {ε : Γ} :
    (x ∈ ⋃ d ∈ S, NAdvf.ballV F d ε) ↔ ∃ d ∈ S, x ∈ NAdvf.ballV F d ε := by
  simp [Set.mem_iUnion]

/-- The same, for a union indexed by a subset of `L` (as in the paper's `A_D`, `D ⊆ L`). -/
theorem mem_biUnion_ball_subtype {K : Type u} {Γ : Type v} [AddCommGroup K] [AddCommGroup Γ]
    [LinearOrder Γ] [IsOrderedAddMonoid Γ] (F : NAdvf K Γ) {m : ℕ} {L : Set (Fin m → K)}
    {i : Set L} {x : Fin m → K} {ε : Γ} :
    (x ∈ ⋃ d ∈ i, NAdvf.ballV F ((d : L) : Fin m → K) ε) ↔
      ∃ d ∈ i, x ∈ NAdvf.ballV F ((d : L) : Fin m → K) ε := by
  simp [Set.mem_iUnion]

/-- `s = ∅`, unfolded (the paper's "`go(b̄,ε) ∩ (L \ {b̄}) = ∅`"). -/
theorem eq_empty_iff_forall_not_mem {α : Type*} {s : Set α} :
    s = ∅ ↔ ∀ x, x ∉ s := by
  rw [← Set.not_nonempty_iff_eq_empty]
  constructor
  · intro h x hx
    exact h ⟨x, hx⟩
  · rintro h ⟨x, hx⟩
    exact h x hx

/-- **Definition** (`paper.tex:1903`), verbatim:

> Let `A ⊆ VF^n`, `f : A → 𝓟(VF^m)` a definable function, `ā ∈ VF^n`, and `L ⊆ PP(VF)^m`.  We say
> that `L` is a *limit set of `f` at `ā`*, written as `lim_{A → ā} f ⊆ L`, if for every `ε ∈ Γ`
> there is a `δ ∈ Γ` such that if `c̄ ∈ go(ā,δ) ∩ (A \ ā)` then `f(c̄) ⊆ ⋃_{b̄ ∈ L'} go(b̄,ε)` for
> some `L' ⊆ L`.

`L` is taken inside `VF^m` (see item 1 of the deviations at the head of the file); the definability
of `f` is the separate hypothesis of the two lemmas below. -/
def LimitSet {K : Type u} {Γ : Type v} [AddCommGroup K] [AddCommGroup Γ] [LinearOrder Γ]
    [IsOrderedAddMonoid Γ] (F : NAdvf K Γ) {n m : ℕ} (a : Fin n → K) (A : Set (Fin n → K))
    (f : (Fin n → K) → Set (Fin m → K)) (L : Set (Fin m → K)) : Prop :=
  ∀ ε : Γ, ∃ δ : Γ, ∀ c, c ∈ NAdvf.ballV F a δ → c ≠ a → c ∈ A →
    ∃ L' : Set (Fin m → K), L' ⊆ L ∧ f c ⊆ ⋃ d ∈ L', NAdvf.ballV F d ε

/-- The paper's minimality (`paper.tex:1906`): *"A limit set `L` of `f` at `ā` is minimal if no
proper subset of `L` is a limit set of `f` at `ā`."* -/
def MinimalLimit {K : Type u} {Γ : Type v} [AddCommGroup K] [AddCommGroup Γ] [LinearOrder Γ]
    [IsOrderedAddMonoid Γ] (F : NAdvf K Γ) {n m : ℕ} (a : Fin n → K) (A : Set (Fin n → K))
    (f : (Fin n → K) → Set (Fin m → K)) (L : Set (Fin m → K)) : Prop :=
  LimitSet F a A f L ∧ ∀ M, M ⊂ L → ¬ LimitSet F a A f M

/-- Closedness of a set of points of the `VF`-sort, in the topology generated by the balls `go`: a
point is in the closure of `L` iff every ball around it meets `L`.  This is the closedness in
*"`L` is a closed (hence the unique) minimal limit set of `f` at `ā`"* (`paper.tex:1915`). -/
def IsClosed {K : Type u} {Γ : Type v} [AddCommGroup K] [AddCommGroup Γ] [LinearOrder Γ]
    [IsOrderedAddMonoid Γ] (F : NAdvf K Γ) {m : ℕ} (L : Set (Fin m → K)) : Prop :=
  ∀ b, (∀ ε : Γ, (NAdvf.ballV F b ε ∩ L).Nonempty) → b ∈ L

/-- `lim_{A → ā} f = L`: *"This lemma justifies the equality `lim_{A → ā} f = L` when `L` is a
closed (hence the unique) minimal limit set of `f` at `ā`"* (`paper.tex:1915`). -/
def IsLimit {K : Type u} {Γ : Type v} [AddCommGroup K] [AddCommGroup Γ] [LinearOrder Γ]
    [IsOrderedAddMonoid Γ] (F : NAdvf K Γ) {n m : ℕ} (a : Fin n → K) (A : Set (Fin n → K))
    (f : (Fin n → K) → Set (Fin m → K)) (L : Set (Fin m → K)) : Prop :=
  MinimalLimit F a A f L ∧ IsClosed F L

namespace NAdvf

variable {K : Type u} {Γ : Type v} [AddCommGroup K] [AddCommGroup Γ] [LinearOrder Γ]
  [IsOrderedAddMonoid Γ]
variable (F : NAdvf K Γ)
variable {n m : ℕ}

/-! ### Elementary closure properties -/

/-- A superset of a limit set is a limit set (immediate from the definition). -/
theorem limitSet_mono {a : Fin n → K} {A : Set (Fin n → K)} {f : (Fin n → K) → Set (Fin m → K)}
    {L L' : Set (Fin m → K)} (h : LimitSet F a A f L) (hLL' : L ⊆ L') :
    LimitSet F a A f L' := by
  intro ε
  obtain ⟨δ, hδ⟩ := h ε
  refine ⟨δ, fun c hc hne hcA => ?_⟩
  obtain ⟨L'', hL'', hcov⟩ := hδ c hc hne hcA
  exact ⟨L'', hL''.trans hLL', hcov⟩

/-- Limit sets depend only on the function up to pointwise equality, and on the set up to equality. -/
theorem limitSet_congr {a : Fin n → K} {A : Set (Fin n → K)}
    {f f' : (Fin n → K) → Set (Fin m → K)} {L L' : Set (Fin m → K)}
    (hff : ∀ c, f c = f' c) (hL : L = L') (h : LimitSet F a A f L) :
    LimitSet F a A f' L' := by
  intro ε
  obtain ⟨δ, hδ⟩ := h ε
  refine ⟨δ, fun c hc hne hcA => ?_⟩
  obtain ⟨L'', hL'', hcov⟩ := hδ c hc hne hcA
  exact ⟨L'', by rw [← hL]; exact hL'', by rw [← hff c]; exact hcov⟩

/-- The union of two limit sets is a limit set of the union of the two functions:
*"Clearly `L` is a closed limit set of `f` at `ā`"* (`paper.tex:1920`). -/
theorem limitSet_union {a : Fin n → K} {A : Set (Fin n → K)}
    {f₁ f₂ : (Fin n → K) → Set (Fin m → K)} {L₁ L₂ : Set (Fin m → K)}
    (h₁ : LimitSet F a A f₁ L₁) (h₂ : LimitSet F a A f₂ L₂) :
    LimitSet F a A (fun c => f₁ c ∪ f₂ c) (L₁ ∪ L₂) := by
  intro ε
  obtain ⟨δ₁, hδ₁⟩ := h₁ ε
  obtain ⟨δ₂, hδ₂⟩ := h₂ ε
  refine ⟨max δ₁ δ₂, fun c hc hne hcA => ?_⟩
  obtain ⟨L₁', hL₁', hc₁⟩ := hδ₁ c (ballV_anti F (le_max_left _ _) hc) hne hcA
  obtain ⟨L₂', hL₂', hc₂⟩ := hδ₂ c (ballV_anti F (le_max_right _ _) hc) hne hcA
  refine ⟨L₁' ∪ L₂', union_subset (hL₁'.trans subset_union_left)
    (hL₂'.trans subset_union_right), ?_⟩
  intro x hx
  rw [mem_biUnion_ball]
  rcases hx with hx | hx
  · obtain ⟨d, hd, hxd⟩ := by
      have h := hc₁ hx
      rwa [mem_biUnion_ball] at h
    exact ⟨d, Or.inl hd, hxd⟩
  · obtain ⟨d, hd, hxd⟩ := by
      have h := hc₂ hx
      rwa [mem_biUnion_ball] at h
    exact ⟨d, Or.inr hd, hxd⟩

/-- The union of two closed sets is closed (for the topology generated by the balls, whose
neighbourhoods are nested, so the usual argument for finite unions of closed sets applies). -/
theorem isClosed_union {L₁ L₂ : Set (Fin m → K)} (h₁ : IsClosed F L₁) (h₂ : IsClosed F L₂) :
    IsClosed F (L₁ ∪ L₂) := by
  intro b hb
  by_cases h1 : ∀ ε : Γ, (ballV F b ε ∩ L₁).Nonempty
  · exact Or.inl (h₁ b h1)
  · obtain ⟨ε₀, hε₀⟩ := not_forall.mp h1
    right
    refine h₂ b (fun ε => ?_)
    rcases le_total ε ε₀ with hle | hle
    · obtain ⟨x, hx, hxL⟩ := hb ε₀
      refine ⟨x, ballV_anti F hle hx, ?_⟩
      rcases hxL with h | h
      · exact (hε₀ ⟨x, hx, h⟩).elim
      · exact h
    · obtain ⟨x, hx, hxL⟩ := hb ε
      refine ⟨x, hx, ?_⟩
      rcases hxL with h | h
      · exact (hε₀ ⟨x, ballV_anti F hle hx, h⟩).elim
      · exact h

/-- *"Observe that ... in a minimal limit set every element is isolated"* (`paper.tex:1906`): if `b`
lies in a minimal limit set `L`, then some ball around `b` misses `L \ {b}`. -/
theorem isolated_of_minimalLimit {a : Fin n → K} {A : Set (Fin n → K)}
    {f : (Fin n → K) → Set (Fin m → K)} {L : Set (Fin m → K)}
    (h : MinimalLimit F a A f L) {b : Fin m → K} (hb : b ∈ L) :
    ∃ ε : Γ, ballV F b ε ∩ (L \ {b}) = ∅ := by
  by_contra hcon
  push Not at hcon
  have hlim : LimitSet F a A f (L \ {b}) := by
    intro ε
    obtain ⟨δ, hδ⟩ := h.1 ε
    obtain ⟨d, hd⟩ := hcon ε
    refine ⟨δ, fun c hc hne hcA => ?_⟩
    obtain ⟨L', hL', hcov⟩ := hδ c hc hne hcA
    refine ⟨(L' \ {b}) ∪ {d}, ?_, ?_⟩
    · rintro x (hx | hx)
      · exact ⟨hL' hx.1, hx.2⟩
      · rw [Set.mem_singleton_iff] at hx
        exact ⟨by rw [hx]; exact hd.2.1, by simpa [hx] using hd.2.2⟩
    · intro x hx
      rw [mem_biUnion_ball]
      obtain ⟨d', hd', hxd'⟩ := by
        have h := hcov hx
        rwa [mem_biUnion_ball] at h
      rcases eq_or_ne d' b with rfl | hneb
      · exact ⟨d, Or.inr rfl, mem_ballV_of_mem_ballV' F hxd' hd.1⟩
      · exact ⟨d', Or.inl ⟨hd', by simpa using hneb⟩, hxd'⟩
  have hsub : L \ {b} ⊂ L := by
    refine (Set.ssubset_iff_subset_ne).mpr ⟨Set.sdiff_subset, ?_⟩
    intro heq
    have h2 : b ∈ L \ {b} := by rw [heq]; exact hb
    exact h2.2 rfl
  exact h.2 _ hsub hlim

/-- The paper's separation step in the proof of Lemma `union:lim` (`paper.tex:1920`):

> If `b̄ ∈ L₁ ∩ L₂` then, since `b̄` is isolated in both `L₁` and `L₂`, there is an `ε ∈ Γ` such
> that `go(b̄,ε) ∩ (L \ {b̄}) = ∅`.  If `b̄ ∈ L₁ \ L₂` then, since `L₂` is closed, there is again an
> `ε ∈ Γ` such that `go(b̄,ε) ∩ (L \ {b̄}) = ∅`.

Here `L = L₁ ∪ L₂`; the hypothesis `b̄ ∈ L₁ ∪ L₂` covers both cases. -/
theorem exists_isolating_ball {a : Fin n → K} {A : Set (Fin n → K)}
    {f₁ f₂ : (Fin n → K) → Set (Fin m → K)} {L₁ L₂ : Set (Fin m → K)}
    (h₁ : MinimalLimit F a A f₁ L₁) (h₂ : MinimalLimit F a A f₂ L₂)
    (hc₁ : IsClosed F L₁) (hc₂ : IsClosed F L₂) {b : Fin m → K} (hb : b ∈ L₁ ∪ L₂) :
    ∃ ε : Γ, ballV F b ε ∩ ((L₁ ∪ L₂) \ {b}) = ∅ := by
  have key : ∀ (L' : Set (Fin m → K)) (f' : (Fin n → K) → Set (Fin m → K)),
      MinimalLimit F a A f' L' → IsClosed F L' →
      ∃ ε : Γ, ballV F b ε ∩ (L' \ {b}) = ∅ := by
    intro L' f' hmin hcl
    by_cases hb' : b ∈ L'
    · exact isolated_of_minimalLimit F hmin hb'
    · have hex : ∃ ε : Γ, ballV F b ε ∩ L' = ∅ := by
        by_contra hc
        push Not at hc
        exact hb' (hcl b hc)
      obtain ⟨ε, hε⟩ := hex
      refine ⟨ε, ?_⟩
      rw [eq_empty_iff_forall_not_mem] at hε ⊢
      intro x hx
      exact hε x ⟨hx.1, hx.2.1⟩
  obtain ⟨ε₁, hε₁⟩ := key L₁ f₁ h₁ hc₁
  obtain ⟨ε₂, hε₂⟩ := key L₂ f₂ h₂ hc₂
  refine ⟨max ε₁ ε₂, ?_⟩
  rw [eq_empty_iff_forall_not_mem] at hε₁ hε₂ ⊢
  intro x hx
  obtain ⟨hx1, hxLR, hxb⟩ := hx
  rcases hxLR with hxL | hxL
  · exact hε₁ x ⟨ballV_anti F (le_max_left _ _) hx1, hxL, hxb⟩
  · exact hε₂ x ⟨ballV_anti F (le_max_right _ _) hx1, hxL, hxb⟩

/-- The paper's minimality step in the proof of Lemma `union:lim` (`paper.tex:1920`):

> Now, since `L₁` is a limit set of `f₁` at `ā` but `L₁ \ {b̄}` is not, we see that `L \ {b̄}`
> cannot be a limit set of `f` at `ā`.

with `f = f₁ ∪ g`, `L = L₁ ∪ M` and `b̄ ∈ L₁`. -/
theorem not_limitSet_erase_aux {a : Fin n → K} {A : Set (Fin n → K)}
    {f g : (Fin n → K) → Set (Fin m → K)} {L M : Set (Fin m → K)}
    (h : MinimalLimit F a A f L)
    (hsep : ∀ b ∈ L ∪ M, ∃ ε : Γ, ballV F b ε ∩ ((L ∪ M) \ {b}) = ∅)
    {b : Fin m → K} (hb : b ∈ L) :
    ¬ LimitSet F a A (fun c => f c ∪ g c) ((L ∪ M) \ {b}) := by
  intro hM
  refine h.2 (L \ {b}) ?_ ?_
  · refine (Set.ssubset_iff_subset_ne).mpr ⟨Set.sdiff_subset, ?_⟩
    intro heq
    have h2 : b ∈ L \ {b} := by rw [heq]; exact hb
    exact h2.2 rfl
  · intro ε
    obtain ⟨ε', hε'⟩ := hsep b (Or.inl hb)
    rw [eq_empty_iff_forall_not_mem] at hε'
    obtain ⟨δM, hδM⟩ := hM (max ε ε')
    obtain ⟨δ₁, hδ₁⟩ := h.1 (max ε ε')
    refine ⟨max δM δ₁, fun c hc hne hcA => ?_⟩
    obtain ⟨L_M, hL_M, hcov_M⟩ := hδM c (ballV_anti F (le_max_left _ _) hc) hne hcA
    obtain ⟨L₁', hL₁', hcov₁⟩ := hδ₁ c (ballV_anti F (le_max_right _ _) hc) hne hcA
    refine ⟨L \ {b}, fun x hx => hx, ?_⟩
    intro x hx
    rw [mem_biUnion_ball]
    obtain ⟨d₂, hd₂, hxd₂⟩ := by
      have h := hcov_M (Or.inl hx)
      rwa [mem_biUnion_ball] at h
    obtain ⟨d₁, hd₁, hxd₁⟩ := by
      have h := hcov₁ hx
      rwa [mem_biUnion_ball] at h
    have hd₁ne : d₁ ≠ b := by
      rintro rfl
      exact hε' d₂ ⟨ballV_anti F (le_max_right _ _)
        (mem_ballV_of_mem_ballV F hxd₁ hxd₂), hL_M hd₂⟩
    exact ⟨d₁, ⟨hL₁' hd₁, by simpa using hd₁ne⟩, ballV_anti F (le_max_left _ _) hxd₁⟩

/-- **Lemma `union:lim`** (`paper.tex:1917`), verbatim:

> Let `f₁`, `f₂ : A → 𝓟(VF^m)` be definable functions with `lim_{A → ā} f_i = L_i`, then
> `lim_{A → ā} (f₁ ∪ f₂) = L₁ ∪ L₂`.

Proved following the paper: `L = L₁ ∪ L₂` is a closed limit set of `f = f₁ ∪ f₂`, and it is minimal
because removing any `b̄ ∈ L` destroys the limit-set property for one of the `f_i`. -/
theorem union_lim (a : Fin n → K) (A : Set (Fin n → K))
    (f₁ f₂ : (Fin n → K) → Set (Fin m → K)) (L₁ L₂ : Set (Fin m → K))
    (Def : Set (Fin n → K) → ((Fin n → K) → Set (Fin m → K)) → Prop)
    (hdef₁ : Def A f₁) (hdef₂ : Def A f₂)
    (h₁ : IsLimit F a A f₁ L₁) (h₂ : IsLimit F a A f₂ L₂) :
    IsLimit F a A (fun c => f₁ c ∪ f₂ c) (L₁ ∪ L₂) := by
  have hsep : ∀ b ∈ L₁ ∪ L₂, ∃ ε : Γ, ballV F b ε ∩ ((L₁ ∪ L₂) \ {b}) = ∅ :=
    fun b hb => exists_isolating_ball F h₁.1 h₂.1 h₁.2 h₂.2 hb
  refine ⟨⟨limitSet_union F h₁.1.1 h₂.1.1, ?_⟩, isClosed_union F h₁.2 h₂.2⟩
  intro M hM hMlim
  obtain ⟨hMsub, hMne⟩ := Set.ssubset_iff_subset_ne.mp hM
  obtain ⟨b, hbL, hbM⟩ : ∃ b, b ∈ L₁ ∪ L₂ ∧ b ∉ M := by
    by_contra hc
    push Not at hc
    exact hMne (Set.Subset.antisymm hMsub (fun x hx => hc x hx))
  have hMsub' : M ⊆ (L₁ ∪ L₂) \ {b} := fun x hx => ⟨hMsub hx, fun h => hbM (h ▸ hx)⟩
  rcases hbL with hb | hb
  · exact not_limitSet_erase_aux F h₁.1 hsep hb (limitSet_mono F hMlim hMsub')
  · refine not_limitSet_erase_aux (F := F) (h := h₂.1) (M := L₁) (b := b) ?_ hb
      (limitSet_congr F (fun c => Set.union_comm _ _) ?_ (limitSet_mono F hMlim hMsub'))
    · intro b' hb'
      have hb'' : b' ∈ L₁ ∪ L₂ := by rwa [Set.union_comm L₂ L₁] at hb'
      obtain ⟨ε, hε⟩ := hsep b' hb''
      refine ⟨ε, ?_⟩
      show ballV F b' ε ∩ ((L₂ ∪ L₁) \ {b'}) = ∅
      rw [Set.union_comm L₂ L₁]
      exact hε
    · show (L₁ ∪ L₂) \ {b} = (L₂ ∪ L₁) \ {b}
      rw [Set.union_comm L₁ L₂]

/-! ## Lemma `fin:lim:bounded` -/

/-- The paper's family `A_D` in the proof of Lemma `fin:lim:bounded` (`paper.tex:1930`):

> For each `D ⊆ L` with `|D| = k` let `A_D = {c ∈ A : f(c) ⊆ ⋃_{b̄_i ∈ D} go(b̄_i, α)}`.

The paper indexes by the `D` of size exactly `k`; `≤ k` suffices (and is what the covering step
produces), so a `D` of size at most `k` is what is used here.  With `L` finite, the `D` are the
elements of the finite type `Set ↥L`. -/
def coverFamily (F : NAdvf K Γ) {n m : ℕ} (f : (Fin n → K) → Set (Fin m → K)) {L : Set (Fin m → K)}
    (α : Γ) (i : Set L) : Set (Fin n → K) :=
  {c | f c ⊆ ⋃ d ∈ i, ballV F ((d : L) : Fin m → K) α}

/-- The covering step of the proof of Lemma `fin:lim:bounded` (`paper.tex:1928-1930`): if the values
of `f c` are covered by the `α`-balls around a subset `L'` of `L`, if `|f c| ≤ k`, and if the
`α`-balls around distinct points of `L` are pairwise disjoint, then `f c` is in fact covered by the
`α`-balls around a subset of `L` of size at most `k` — because two different points of `L` whose
`α`-balls both meet `f c` must be witnessed by different elements of `f c`. -/
theorem exists_cover_subset (F : NAdvf K Γ) {n m : ℕ} {k : ℕ} {L : Set (Fin m → K)} {α : Γ}
    (hLf : L.Finite)
    (hdisj : ∀ b₁ ∈ L, ∀ b₂ ∈ L, b₁ ≠ b₂ → Disjoint (ballV F b₁ α) (ballV F b₂ α))
    {c : Fin n → K} {f : (Fin n → K) → Set (Fin m → K)} {L' : Set (Fin m → K)}
    (hL' : L' ⊆ L) (hcov : f c ⊆ ⋃ d ∈ L', ballV F d α) (hfc : (f c).Finite)
    (hk : (f c).ncard ≤ k) :
    ∃ i : Set L, i.ncard ≤ k ∧ f c ⊆ ⋃ d ∈ i, ballV F ((d : L) : Fin m → K) α := by
  classical
  letI : Fintype L := hLf.fintype
  set T : Set L := {d | ∃ x ∈ f c, x ∈ ballV F ((d : L) : Fin m → K) α} with hT
  refine ⟨T, ?_, ?_⟩
  · refine le_trans (Set.ncard_le_ncard_of_injOn
      (fun d : L => if h : d ∈ T then Classical.choose h else 0) ?_ ?_ hfc) hk
    · intro d hd
      simp only [dif_pos hd]
      exact (Classical.choose_spec hd).1
    · intro d₁ hd₁ d₂ hd₂ heq
      by_contra hne
      have h1 : Classical.choose hd₁ ∈ ballV F ((d₁ : L) : Fin m → K) α :=
        (Classical.choose_spec hd₁).2
      have h2 : Classical.choose hd₂ ∈ ballV F ((d₂ : L) : Fin m → K) α :=
        (Classical.choose_spec hd₂).2
      have h3 : Classical.choose hd₁ = Classical.choose hd₂ := by
        simpa only [dif_pos hd₁, dif_pos hd₂] using heq
      rw [h3] at h1
      exact Set.disjoint_left.mp
        (hdisj _ d₁.2 _ d₂.2 (fun h => hne (Subtype.coe_injective h))) h1 h2
  · intro x hx
    rw [mem_biUnion_ball_subtype]
    have h := hcov hx
    rw [mem_biUnion_ball] at h
    obtain ⟨d, hd, hxd⟩ := h
    exact ⟨⟨d, hL' hd⟩, ⟨x, hx, hxd⟩, hxd⟩

/-- *"hence `lim_{A → a} f = lim_{A_D → a} (f ↾ A_D) ⊆ D`"* (`paper.tex:1932`): if near `a` the
values of `f` are covered by the `α`-balls around the points of a set `i ⊆ L`, and the `α`-balls
around distinct points of `L` are disjoint, then `i` is a limit set of `f` at `a`. -/
theorem limitSet_of_cover (F : NAdvf K Γ) {n m : ℕ} {a : Fin n → K} {A : Set (Fin n → K)}
    {f : (Fin n → K) → Set (Fin m → K)} {L : Set (Fin m → K)} {i : Set L} {α : Γ}
    (hL : LimitSet F a A f L)
    (hdisj : ∀ b₁ ∈ L, ∀ b₂ ∈ L, b₁ ≠ b₂ → Disjoint (ballV F b₁ α) (ballV F b₂ α))
    (hcov : ∃ δ, ∀ c, c ∈ ballV F a δ → c ≠ a → c ∈ A →
      f c ⊆ ⋃ d ∈ i, ballV F ((d : L) : Fin m → K) α) :
    LimitSet F a A f (Subtype.val '' i) := by
  intro ε
  obtain ⟨δ₀, hδ₀⟩ := hcov
  rcases le_total ε α with hε | hε
  · refine ⟨δ₀, fun c hc hne hcA => ⟨Subtype.val '' i, subset_rfl, ?_⟩⟩
    intro x hx
    rw [mem_biUnion_ball]
    obtain ⟨d, hd, hxd⟩ := by
      have h2 := hδ₀ c hc hne hcA hx
      rwa [mem_biUnion_ball_subtype] at h2
    exact ⟨↑d, ⟨d, hd, rfl⟩, ballV_anti F hε hxd⟩
  · obtain ⟨δ₁, hδ₁⟩ := hL ε
    refine ⟨max δ₀ δ₁, fun c hc hne hcA => ?_⟩
    obtain ⟨L', hL', hcov'⟩ := hδ₁ c (ballV_anti F (le_max_right _ _) hc) hne hcA
    refine ⟨Subtype.val '' i, subset_rfl, ?_⟩
    intro x hx
    rw [mem_biUnion_ball]
    obtain ⟨d₁, hd₁, hxd₁⟩ := by
      have h2 := hδ₀ c (ballV_anti F (le_max_left _ _) hc) hne hcA hx
      rwa [mem_biUnion_ball_subtype] at h2
    obtain ⟨d₂, hd₂, hxd₂⟩ := by
      have h := hcov' hx
      rwa [mem_biUnion_ball] at h
    have hd₂α : d₂ ∈ ballV F ((d₁ : L) : Fin m → K) α :=
      mem_ballV_of_mem_ballV F hxd₁ (ballV_anti F hε hxd₂)
    have hd₁₂ : (d₁ : Fin m → K) = d₂ := by
      by_contra hne'
      exact Set.disjoint_left.mp (hdisj _ d₁.2 _ (hL' hd₂) hne') hd₂α
        (mem_ballV_self F d₂ α)
    exact ⟨↑d₁, ⟨d₁, hd₁, rfl⟩, by rw [hd₁₂]; exact hxd₂⟩

/-- **Lemma `fin:lim:bounded`** (`paper.tex:1924`), verbatim:

> Let `f : A → 𝓟(VF^m)` be a definable function with finite images.  Let `k` be the maximal size of
> `f(c)`.  Let `a ∈ VF` and suppose that there is an open ball `B` containing `a` such that
> `B \ {a} ⊆ A`.  Suppose that `lim_{A → a} f = L`.  If `L` is finite then `|L| ≤ k`.

(Stated for `ā ∈ VF^n`; the paper's case is `n = 1`, see item 2 of the deviations.)

The two hypotheses carrying the paper's C-minimality input are

* `hcmin` — *"By `C`-minimality, some `A_D ∪ {a}` contains an open ball around `a`"*
  (`paper.tex:1932`);
* `hdefAD` — *"Each `A_D` is `seq{L,α}`-definable"* (`paper.tex:1932`).

Everything else in the paper's proof is proved here: `exists_uniform_disjoint_ballV` is the paper's
`α`, `exists_cover_subset` is the construction of the `A_D` together with `|D| ≤ |f(c)| ≤ k`
(*"`i ∈ D`…"*), and `limitSet_of_cover` is *"hence `lim_{A_D → a} (f ↾ A_D) ⊆ D`"*, which
contradicts the minimality of `L` because `|D| ≤ k < |L|`. -/
theorem fin_lim_bounded (F : NAdvf K Γ) {n m : ℕ} (a : Fin n → K) (A : Set (Fin n → K))
    (f : (Fin n → K) → Set (Fin m → K)) (k : ℕ) (L : Set (Fin m → K))
    (Def : Set (Fin n → K) → Prop)
    (DefFun : ((Fin n → K) → Set (Fin m → K)) → Prop)
    (hdefA : Def A) (_hdeff : DefFun f)
    (hffin : ∀ c, (f c).Finite)
    (hk : ∀ c ∈ A, (f c).ncard ≤ k)
    (hball : ∃ B : Γ, ∀ x, x ≠ a → x ∈ ballV F a B → x ∈ A)
    (hlim : IsLimit F a A f L)
    (hLfin : L.Finite)
    (hcmin : ∀ (B : Γ) (ι : Type u) [Fintype ι] (As : ι → Set (Fin n → K)),
      (∀ i, Def (As i)) →
      (∀ x, x ≠ a → x ∈ ballV F a B → ∃ i, x ∈ As i) →
      ∃ i, ∃ B' : Γ, ∀ x, x ≠ a → x ∈ ballV F a B' → x ∈ As i)
    (hdefAD : ∀ (α : Γ) (i : Set L), i.ncard ≤ k → Def (coverFamily F f α i)) :
    L.ncard ≤ k := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨α, hα⟩ := exists_uniform_disjoint_ballV F hLfin
  obtain ⟨B, hB⟩ := hball
  obtain ⟨δ, hδ⟩ := hlim.1.1 α
  letI : Fintype L := hLfin.fintype
  let As : {i : Set L // i.ncard ≤ k} → Set (Fin n → K) := fun i => coverFamily F f α i.1
  have hAsdef : ∀ i, Def (As i) := fun i => hdefAD α i.1 i.2
  have hcover : ∀ x, x ≠ a → x ∈ ballV F a (max B δ) → ∃ i, x ∈ As i := by
    intro x hxne hx
    have hxA : x ∈ A := hB x hxne (ballV_anti F (le_max_left _ _) hx)
    obtain ⟨L', hL', hcov⟩ := hδ x (ballV_anti F (le_max_right _ _) hx) hxne hxA
    obtain ⟨i, hicard, hicov⟩ :=
      exists_cover_subset F hLfin hα hL' hcov (hffin x) (hk x hxA)
    exact ⟨⟨i, hicard⟩, hicov⟩
  obtain ⟨⟨i, hicard⟩, B', hB'⟩ :=
    hcmin (max B δ) {i : Set L // i.ncard ≤ k} As hAsdef hcover
  have hsub : Subtype.val '' i ⊂ L := by
    refine (Set.ssubset_iff_subset_ne).mpr ⟨?_, ?_⟩
    · rintro x ⟨d, -, rfl⟩
      exact d.2
    · intro heq
      have h1 : (Subtype.val '' i).ncard = i.ncard :=
        Set.ncard_image_of_injective i Subtype.val_injective
      rw [heq] at h1
      omega
  have hlim' : LimitSet F a A f (Subtype.val '' i) :=
    limitSet_of_cover F hlim.1.1 hα ⟨B', fun c hc hne hcA => hB' c hne hc⟩
  exact hlim.1.2 _ hsub hlim'

end NAdvf

namespace NAdvf

/-! ## Consistency of the axioms of `NAdvf` -/

/-- The **trivial valuation** on an additive group, as a model of `NAdvf`: `vv 0 = ∞` and
`vv x = 0` for `x ≠ 0`.  This shows that the axioms of `NAdvf` are consistent, hence the two
lemmas above are not vacuous. -/
noncomputable def trivial (K : Type u) [AddCommGroup K] : NAdvf K ℤ :=
  letI : DecidableEq K := Classical.decEq K
  { vv := fun x => if x = 0 then ⊤ else 0
    vv_eq_top := fun x => by by_cases h : x = 0 <;> simp [h]
    vv_neg := fun x => by by_cases h : x = 0 <;> simp [h]
    vv_add := fun x y => by
      by_cases hx : x = 0
      · subst hx; simp
      · by_cases hy : y = 0
        · subst hy; simp [hx]
        · by_cases h : x + y = 0 <;> simp [hx, hy, h] }

/-- The **`p`-adic valuation** on `ℚ`, as a model of `NAdvf`: a genuinely non-archimedean valued
field, so the ball system in which the two lemmas above live is the real one (`go(a,γ)` is the
usual `p`-adic ball), not a degenerate ball system. -/
noncomputable def padic (p : ℕ) [Fact p.Prime] : NAdvf ℚ ℤ where
  vv q := if q = 0 then ⊤ else ((padicValRat p q : ℤ) : WithTop ℤ)
  vv_eq_top q := by by_cases h : q = 0 <;> simp [h]
  vv_neg q := by
    by_cases h : q = 0
    · have h' : -q = 0 := by rw [h, neg_zero]
      simp [h, h']
    · have h' : -q ≠ 0 := by simpa using h
      simp [h, h', padicValRat.neg]
  vv_add q r := by
    by_cases hq : q = 0
    · subst hq; simp
    · by_cases hr : r = 0
      · subst hr; simp [hq]
      · by_cases h : q + r = 0
        · simp [hq, hr, h]
        · have hle := padicValRat.min_le_padicValRat_add (p := p) h
          simp only [hq, hr, h, if_false]
          exact_mod_cast hle

end NAdvf

/-! ## The two lemmas, and what they depend on -/

#print axioms YinSec9.NAdvf.union_lim
#print axioms YinSec9.NAdvf.exists_uniform_disjoint_ballV
#print axioms YinSec9.NAdvf.exists_cover_subset
#print axioms YinSec9.NAdvf.limitSet_of_cover
#print axioms YinSec9.NAdvf.fin_lim_bounded
