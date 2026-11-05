/-
**"At most `k` solutions" as a first-order formula of `L_RV`.**

The paper's first §3 lemma (`paper.tex`, §3, first lemma) is proved by compactness: *"there are a
definable partition `A_1, …, A_m` of `A`, integers `k_1, …, k_m`, formulas
`φ_1(X, Y), …, φ_m(X, Y)`, such that if `a ∈ A_i` then the subset `U_a` defined by the formula
`φ_i(a, Y)` contains `s` and its size is at most `k_i`.  Then `⋂_{a ∈ A} U_a` is a definable finite
subset that contains `s`."*

`SP.acl_of_uniform_cover` (`.ultramath/smw1kv9xm/m1/UniformCover.lean`, ported and verified in this
directory) formalises the last sentence for a **single** formula.  The step that is missing is the
compactness step, and to state its conclusion *inside the encoding* one needs a formula
`atMost k φ(Y)` saying that `{x : iVF x ∧ φ(x, Y)}` has at most `k` elements — finiteness is not
first-order, only *bounded* finiteness is.  This file builds that formula for a two-variable context
`(X, Y)` and proves its realisation lemma:

`atMost2 k ψ` realises at `![x, y]` exactly when there is no injective map `Fin (k+1) → M` into
`{z : iVF z ∧ ψ.Realize v ![z, y]}`, i.e. "no `k+1` distinct solutions" — which is
`Set.Finite ∧ ncard ≤ k` by the pigeonhole lemma of `QE/InfRVDefGam.lean`.

Everything is built with the encoding's own syntax (`exSortedG` for the guarded existential,
`Sec4Compose.BoundedFormula.substVar` for the variable renaming), so `atMost2 k ψ` carries
`WellSorted` (needed by `SP.acl`, whose witness must be a well-sorted formula) and its realisation
lemma is proved, not assumed.

No `sorry`, no `axiom`, no `native_decide`.
-/
import Sec3Infra
import SubstVar
import ExSortedG
import UniformCover

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open FirstOrder FirstOrder.Language
open scoped FirstOrder

namespace SpecialTransformations.Milestone0
open LRV

namespace SP

variable {M : Type} [LRV.Structure M]
variable {α : Type}

/-! ## 1. Finite conjunctions -/

/-- The conjunction of a list of formulas (`⊤` on the empty list). -/
def bigAnd {α : Type} {n : ℕ} (l : List (LRV.BoundedFormula α n)) : LRV.BoundedFormula α n :=
  l.foldr (fun a b => a ⊓ b) ⊤

theorem bigAnd_realize {n : ℕ} (l : List (LRV.BoundedFormula α n)) (v : α → M)
    (xs : Fin n → M) : (bigAnd l).Realize v xs ↔ ∀ φ ∈ l, φ.Realize v xs := by
  induction l with
  | nil => simp [bigAnd]
  | cons a t ih =>
      have hstep : bigAnd (a :: t) = a ⊓ bigAnd t := rfl
      rw [hstep, BoundedFormula.realize_inf, ih]
      constructor
      · rintro ⟨ha, ht⟩ φ hφ
        rcases (List.mem_cons).mp hφ with rfl | hφ'
        · exact ha
        · exact ht φ hφ'
      · intro h
        exact ⟨h a (List.mem_cons_self ..), fun φ hφ => h φ (List.mem_cons_of_mem _ hφ)⟩

theorem bigAnd_wellSorted {n : ℕ} {sα : α → SortTag} {sn : Fin n → SortTag}
    {l : List (LRV.BoundedFormula α n)} (h : ∀ φ ∈ l, WellSorted sα sn φ) :
    WellSorted sα sn (bigAnd l) := by
  induction l with
  | nil =>
      have htop := wellSorted_top (α := α) sα sn
      simpa [bigAnd] using htop
  | cons a t ih =>
      have ha : WellSorted sα sn a := h a (List.mem_cons_self ..)
      have ht : ∀ φ ∈ t, WellSorted sα sn φ := fun φ hφ => h φ (List.mem_cons_of_mem _ hφ)
      have hstep : bigAnd (a :: t) = a ⊓ bigAnd t := rfl
      rw [hstep]
      exact wellSorted_inf (α := α) sα sn ha (ih ht)

theorem bigAnd_append_realize {n : ℕ} (l₁ l₂ : List (LRV.BoundedFormula α n)) (v : α → M)
    (xs : Fin n → M) :
    (bigAnd (l₁ ++ l₂)).Realize v xs ↔
      (bigAnd l₁).Realize v xs ∧ (bigAnd l₂).Realize v xs := by
  rw [bigAnd_realize, bigAnd_realize, bigAnd_realize]
  constructor
  · intro h
    exact ⟨fun φ hφ => h φ (List.mem_append.mpr (Or.inl hφ)),
      fun φ hφ => h φ (List.mem_append.mpr (Or.inr hφ))⟩
  · rintro ⟨h1, h2⟩ φ hφ
    rcases (List.mem_append).mp hφ with h | h
    · exact h1 φ h
    · exact h2 φ h

/-! ## 2. Tuples with values appended at the end

`snocAll xs m ws` is the tuple `xs` followed by `ws 0, …, ws (m-1)`.  It is exactly the tuple that
`m` iterated appends produce, so that the peeling lemma `iterEx_realize` below is definitional in
its induction step. -/

/-- Append one value at the end of a tuple. -/
def snocTup {M : Type} {m : ℕ} (ws : Fin m → M) (a : M) : Fin (m + 1) → M :=
  Fin.lastCases a ws

theorem snocTup_last {m : ℕ} (ws : Fin m → M) (a : M) :
    snocTup ws a (Fin.last m) = a := Fin.lastCases_last

theorem snocTup_castSucc {m : ℕ} (ws : Fin m → M) (a : M) (j : Fin m) :
    snocTup ws a (Fin.castSucc j) = ws j := Fin.lastCases_castSucc j

/-- `snocTup` is the encoding's `Fin.snoc`. -/
theorem fin_snoc_eq_snocTup {m : ℕ} (ws : Fin m → M) (a : M) :
    Fin.snoc ws a = snocTup ws a := by
  funext i
  refine Fin.lastCases ?_ ?_ i
  · rw [Fin.snoc_last, snocTup_last]
  · intro j; rw [Fin.snoc_castSucc, snocTup_castSucc]

/-- `xs` with the `m` values `ws` appended at the end. -/
def snocAll {M : Type} {n : ℕ} (xs : Fin n → M) : (m : ℕ) → (Fin m → M) → Fin (n + m) → M
  | 0, _ => xs
  | (m + 1), ws => snocTup (snocAll xs m (fun k => ws (Fin.castSucc k))) (ws (Fin.last m))

theorem snocAll_succ {n : ℕ} (xs : Fin n → M) (m : ℕ) (ws : Fin (m + 1) → M) :
    snocAll xs (m + 1) ws =
      snocTup (snocAll xs m (fun k => ws (Fin.castSucc k))) (ws (Fin.last m)) := rfl

/-- The value appended last sits at the last position. -/
theorem snocAll_last {n : ℕ} (xs : Fin n → M) (m : ℕ) (ws : Fin (m + 1) → M) :
    snocAll xs (m + 1) ws (Fin.last (n + m)) = ws (Fin.last m) := by
  rw [snocAll_succ, snocTup_last]

/-- All the earlier positions are untouched by the last append. -/
theorem snocAll_castSucc {n : ℕ} (xs : Fin n → M) (m : ℕ) (ws : Fin (m + 1) → M)
    (i : Fin (n + m)) :
    snocAll xs (m + 1) ws (Fin.castSucc i) = snocAll xs m (fun j => ws (Fin.castSucc j)) i := by
  rw [snocAll_succ, snocTup_castSucc]

/-- The appended value `ws j` sits at position `n + j`. -/
theorem snocAll_right {n : ℕ} (xs : Fin n → M) : ∀ (m : ℕ) (ws : Fin m → M) (j : Fin m),
    snocAll xs m ws (Fin.natAdd n j) = ws j := by
  intro m
  induction m with
  | zero => intro ws j; exact j.elim0
  | succ m ih =>
      intro ws j
      refine Fin.lastCases ?_ ?_ j
      · rw [Fin.natAdd_last, snocAll_last]
      · intro j'
        have hidx : (Fin.natAdd n (Fin.castSucc j') : Fin (n + (m + 1))) =
            Fin.castSucc (Fin.natAdd n j' : Fin (n + m)) := rfl
        rw [hidx, snocAll_castSucc, ih]

/-- The initial segment is untouched: `xs i` stays at position `i`. -/
theorem snocAll_left {n : ℕ} (xs : Fin n → M) : ∀ (m : ℕ) (ws : Fin m → M) (i : Fin n),
    snocAll xs m ws (Fin.castAdd m i) = xs i := by
  intro m
  induction m with
  | zero => intro ws i; rfl
  | succ m ih =>
      intro ws i
      have hidx : (Fin.castAdd (m + 1) i : Fin (n + (m + 1))) =
          Fin.castSucc (Fin.castAdd m i : Fin (n + m)) := rfl
      rw [hidx, snocAll_castSucc, ih]

/-- Appending one more value `a` gives the same tuple as appending `a` after the values `ws`. -/
theorem snocAll_snocTup {n : ℕ} (xs : Fin n → M) (m : ℕ) (ws : Fin m → M) (a : M) :
    snocAll xs (m + 1) (snocTup ws a) = snocTup (snocAll xs m ws) a := by
  show snocTup (snocAll xs m (fun k => snocTup ws a (Fin.castSucc k))) (snocTup ws a (Fin.last m))
      = snocTup (snocAll xs m ws) a
  rw [snocTup_last]
  rw [show (fun k => snocTup ws a (Fin.castSucc k)) = ws from by
    funext k; exact snocTup_castSucc ws a k]

/-! ## 3. Iterated guarded existential -/

/-- `m`-fold `VF`-guarded existential over the last `m` variables of a `2 + m` context. -/
def iterEx {α : Type} : (m : ℕ) → LRV.BoundedFormula α (2 + m) → LRV.BoundedFormula α 2
  | 0, χ => χ
  | (m + 1), χ => iterEx m (exSortedG SortTag.vf χ)

/-- **Realisation of the iterated guarded existential.**  The witnesses sit at the end of the
tuple, in the order of their variable indices: `snocAll xs m ws` has `ws j` at position `2 + j`. -/
theorem iterEx_realize {α : Type} (m : ℕ) :
    ∀ (χ : LRV.BoundedFormula α (2 + m)) (v : α → M) (xs : Fin 2 → M),
      (iterEx m χ).Realize v xs ↔
        ∃ ws : Fin m → M, (∀ j, iVF (ws j)) ∧ χ.Realize v (snocAll xs m ws) := by
  induction m with
  | zero =>
      intro χ v xs
      constructor
      · intro h; exact ⟨fun j => j.elim0, fun j => j.elim0, h⟩
      · rintro ⟨ws, -, h⟩; exact h
  | succ m ih =>
      intro χ v xs
      have hstep : iterEx (m + 1) χ = iterEx m (exSortedG SortTag.vf χ) := rfl
      rw [hstep, ih (exSortedG SortTag.vf χ) v xs]
      constructor
      · rintro ⟨ws, hvf, hbody⟩
        obtain ⟨a, haVF, ha⟩ :=
          (exSortedG_realize SortTag.vf χ v (snocAll xs m ws)).mp hbody
        refine ⟨snocTup ws a, ?_, ?_⟩
        · intro j
          refine Fin.lastCases ?_ ?_ j
          · rw [snocTup_last]; exact haVF
          · intro j'; rw [snocTup_castSucc]; exact hvf j'
        · rw [fin_snoc_eq_snocTup, ← snocAll_snocTup] at ha
          exact ha
      · rintro ⟨ws, hvf, hbody⟩
        refine ⟨fun j => ws (Fin.castSucc j), fun j => hvf (Fin.castSucc j), ?_⟩
        refine (exSortedG_realize SortTag.vf χ v (snocAll xs m (fun j => ws (Fin.castSucc j)))).mpr
          ⟨ws (Fin.last m), hvf (Fin.last m), ?_⟩
        rw [fin_snoc_eq_snocTup]
        exact hbody

/-! ## 4. The candidate atoms and the pairwise-distinctness atoms -/

/-- The variable substitution putting the free variable `X` of `ψ` at the candidate variable
`2 + i` of the `2 + (k+1)` context, leaving `Y` at position `1`. -/
def candMap (k : ℕ) (i : Fin (k + 1)) : Fin 2 → LRV.Term (α ⊕ Fin (2 + (k + 1))) :=
  fun t => Fin.cases (Term.var (Sum.inr (Fin.natAdd 2 i))) (fun _ => Term.var (Sum.inr 1)) t

theorem candMap_zero (k : ℕ) (i : Fin (k + 1)) (α : Type) :
    candMap (α := α) k i 0 = Term.var (Sum.inr (Fin.natAdd 2 i)) := rfl

theorem candMap_one (k : ℕ) (i : Fin (k + 1)) (α : Type) :
    candMap (α := α) k i (1 : Fin 2) = Term.var (Sum.inr 1) := rfl

theorem tmSort_candMap {sα : α → SortTag} (k : ℕ) (i : Fin (k + 1)) :
    ∀ t : Fin 2,
      TmSort sα (fun _ : Fin (2 + (k + 1)) => SortTag.vf) (candMap (α := α) k i t) =
        some SortTag.vf := by
  intro t
  fin_cases t
  · simp only [candMap, Fin.cases_zero, tmSort_var_inr]
    rfl
  · simp only [candMap, Fin.cases_succ, tmSort_var_inr]
    rfl

/-- The `k+1` candidate atoms `ψ(X := z_i)`. -/
def candAtoms (k : ℕ) (ψ : LRV.BoundedFormula α 2) :
    List (LRV.BoundedFormula α (2 + (k + 1))) :=
  (List.finRange (k + 1)).map
    fun i => Sec4Compose.BoundedFormula.substVar (candMap (α := α) k i) ψ

/-- The pairs `i < j` in `Fin (k+1)`. -/
def distinctPairs (k : ℕ) : List (Fin (k + 1) × Fin (k + 1)) :=
  ((List.finRange (k + 1)).product (List.finRange (k + 1))).filter
    (fun p => decide (p.1 < p.2))

/-- The atoms `z_i ≠ z_j` for `i < j`. -/
def distinctAtoms (k : ℕ) : List (LRV.BoundedFormula α (2 + (k + 1))) :=
  (distinctPairs k).map fun p =>
    (pEqG (Term.var (Sum.inr (Fin.natAdd 2 p.1)))
      (Term.var (Sum.inr (Fin.natAdd 2 p.2)))).not

theorem mem_candAtoms {k : ℕ} {ψ : LRV.BoundedFormula α 2}
    {φ : LRV.BoundedFormula α (2 + (k + 1))} :
    φ ∈ candAtoms (α := α) k ψ ↔
      ∃ i : Fin (k + 1), φ = Sec4Compose.BoundedFormula.substVar (candMap (α := α) k i) ψ := by
  simp only [candAtoms, List.mem_map]
  constructor
  · rintro ⟨i, -, rfl⟩; exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩; exact ⟨i, List.mem_finRange i, rfl⟩

theorem mem_distinctPairs {k : ℕ} {p : Fin (k + 1) × Fin (k + 1)} :
    p ∈ distinctPairs k ↔ p.1 < p.2 := by
  obtain ⟨i, j⟩ := p
  have hprod : (i, j) ∈ (List.finRange (k + 1)).product (List.finRange (k + 1)) := by simp
  rw [distinctPairs, List.mem_filter]
  simp only [hprod, true_and]
  simp

theorem mem_distinctAtoms {k : ℕ} {φ : LRV.BoundedFormula α (2 + (k + 1))} :
    φ ∈ distinctAtoms (α := α) k ↔
      ∃ i j : Fin (k + 1), i < j ∧
        φ = (pEqG (Term.var (Sum.inr (Fin.natAdd 2 i)))
          (Term.var (Sum.inr (Fin.natAdd 2 j)))).not := by
  simp only [distinctAtoms, List.mem_map]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p.1, p.2, (mem_distinctPairs).mp hp, rfl⟩
  · rintro ⟨i, j, hij, rfl⟩
    exact ⟨(i, j), (mem_distinctPairs).mpr hij, rfl⟩

theorem not_pEqG_var_realize {d : ℕ} (i j : Fin d) (v : α → M) (xs : Fin d → M) :
    ((pEqG (Term.var (Sum.inr i)) (Term.var (Sum.inr j))).not).Realize v xs ↔ xs i ≠ xs j := by
  simp [pEqG]

theorem candMap_tuple (k : ℕ) (i : Fin (k + 1)) (v : α → M)
    (xs : Fin (2 + (k + 1)) → M) :
    (fun t : Fin 2 => Term.realize (Sum.elim v xs) (candMap (α := α) k i t)) =
      ![xs (Fin.natAdd 2 i), xs 1] := by
  funext t
  fin_cases t
  · show Term.realize (Sum.elim v xs) (candMap (α := α) k i 0) = ![xs (Fin.natAdd 2 i), xs 1] 0
    rw [candMap_zero]; simp
  · show Term.realize (Sum.elim v xs) (candMap (α := α) k i 1) = ![xs (Fin.natAdd 2 i), xs 1] 1
    rw [candMap_one]; simp

theorem candAtoms_realize (k : ℕ) (ψ : LRV.BoundedFormula α 2) (v : α → M)
    (xs : Fin (2 + (k + 1)) → M) :
    (bigAnd (candAtoms (α := α) k ψ)).Realize v xs ↔
      ∀ i : Fin (k + 1), ψ.Realize v ![xs (Fin.natAdd 2 i), xs 1] := by
  rw [bigAnd_realize]
  constructor
  · intro h i
    have hi := (Sec4Compose.realize_substVar (φ := ψ) (σ := candMap (α := α) k i) v xs).mp
      (h _ (mem_candAtoms.mpr ⟨i, rfl⟩))
    rw [candMap_tuple] at hi
    exact hi
  · intro h φ hφ
    obtain ⟨i, rfl⟩ := mem_candAtoms.mp hφ
    refine (Sec4Compose.realize_substVar (φ := ψ) (σ := candMap (α := α) k i) v xs).mpr ?_
    rw [candMap_tuple]
    exact h i

theorem distinctAtoms_realize (k : ℕ) (v : α → M) (xs : Fin (2 + (k + 1)) → M) :
    (bigAnd (distinctAtoms (α := α) k)).Realize v xs ↔
      ∀ i j : Fin (k + 1), i < j → xs (Fin.natAdd 2 i) ≠ xs (Fin.natAdd 2 j) := by
  rw [bigAnd_realize]
  constructor
  · intro h i j hij
    have hi := h _ (mem_distinctAtoms.mpr ⟨i, j, hij, rfl⟩)
    rwa [not_pEqG_var_realize] at hi
  · intro h φ hφ
    obtain ⟨i, j, hij, rfl⟩ := mem_distinctAtoms.mp hφ
    rw [not_pEqG_var_realize]
    exact h i j hij

/-- The body of the counting formula: the candidates are solutions and are pairwise distinct.
(`exSortedG`, applied `k+1` times by `iterEx`, supplies `z_i ∈ VF`.) -/
def countBody (k : ℕ) (ψ : LRV.BoundedFormula α 2) : LRV.BoundedFormula α (2 + (k + 1)) :=
  bigAnd (candAtoms (α := α) k ψ ++ distinctAtoms (α := α) k)

theorem countBody_realize (k : ℕ) (ψ : LRV.BoundedFormula α 2) (v : α → M)
    (xs : Fin (2 + (k + 1)) → M) :
    (countBody (α := α) k ψ).Realize v xs ↔
      (∀ i, ψ.Realize v ![xs (Fin.natAdd 2 i), xs 1]) ∧
        Function.Injective (fun i : Fin (k + 1) => xs (Fin.natAdd 2 i)) := by
  rw [countBody, bigAnd_append_realize, candAtoms_realize, distinctAtoms_realize]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun i j hij => ?_⟩
    rcases lt_trichotomy i j with h | h | h
    · exact absurd hij (h2 i j h)
    · exact h
    · exact absurd hij.symm (h2 j i h)
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun i j hij => h2.ne (ne_of_lt hij)⟩

/-- **`atMost2 k ψ`**: "`ψ(X, Y)` has at most `k` solutions `X`", i.e. there are no `k+1` distinct
solutions.  This is the only shape in which the paper's compactness step ("the size of `U_a` is at
most `k_i`") can be written inside the encoding: finiteness itself is not first-order. -/
def atMost2 (k : ℕ) (ψ : LRV.BoundedFormula α 2) : LRV.BoundedFormula α 2 :=
  (iterEx (k + 1) (countBody (α := α) k ψ)).not

/-! ## 5. Well-sortedness of the counting formula -/

/-- `Fin.snoc` of a constant context is constant. -/
theorem fin_snoc_vf_const {n : ℕ} :
    Fin.snoc (fun _ : Fin n => SortTag.vf) SortTag.vf =
      (fun _ : Fin (n + 1) => SortTag.vf) := by
  funext i
  refine Fin.lastCases ?_ ?_ i
  · exact Fin.snoc_last (α := fun _ : Fin (n + 1) => SortTag) SortTag.vf (fun _ => SortTag.vf)
  · intro j
    exact Fin.snoc_castSucc (α := fun _ : Fin (n + 1) => SortTag) SortTag.vf
      (fun _ => SortTag.vf) j

theorem wellSorted_candAtoms {sα : α → SortTag} {k : ℕ} {ψ : LRV.BoundedFormula α 2}
    (hψ : WellSorted sα (fun _ : Fin 2 => SortTag.vf) ψ) :
    ∀ φ ∈ candAtoms (α := α) k ψ,
      WellSorted sα (fun _ : Fin (2 + (k + 1)) => SortTag.vf) φ := by
  intro φ hφ
  obtain ⟨i, rfl⟩ := mem_candAtoms.mp hφ
  exact Sec4Compose.wellSorted_substVar sα hψ (tmSort_candMap k i)

theorem wellSorted_distinctAtoms {sα : α → SortTag} {k : ℕ} :
    ∀ φ ∈ distinctAtoms (α := α) k,
      WellSorted sα (fun _ : Fin (2 + (k + 1)) => SortTag.vf) φ := by
  intro φ hφ
  obtain ⟨i, j, -, rfl⟩ := mem_distinctAtoms.mp hφ
  exact wellSorted_not sα _
    (wellSorted_pEqG (s := SortTag.vf) sα _ (tmSort_var_inr ..) (tmSort_var_inr ..))

theorem wellSorted_countBody {sα : α → SortTag} {k : ℕ} {ψ : LRV.BoundedFormula α 2}
    (hψ : WellSorted sα (fun _ : Fin 2 => SortTag.vf) ψ) :
    WellSorted sα (fun _ : Fin (2 + (k + 1)) => SortTag.vf) (countBody (α := α) k ψ) := by
  refine bigAnd_wellSorted (fun φ hφ => ?_)
  rcases List.mem_append.mp hφ with h | h
  · exact wellSorted_candAtoms hψ φ h
  · exact wellSorted_distinctAtoms φ h

theorem iterEx_wellSorted {sα : α → SortTag} (m : ℕ) :
    ∀ χ : LRV.BoundedFormula α (2 + m),
      WellSorted sα (fun _ : Fin (2 + m) => SortTag.vf) χ →
      WellSorted sα (fun _ : Fin 2 => SortTag.vf) (iterEx m χ) := by
  induction m with
  | zero => intro χ h; exact h
  | succ m ih =>
      intro χ h
      have hstep : iterEx (m + 1) χ = iterEx m (exSortedG SortTag.vf χ) := rfl
      rw [hstep]
      refine ih (exSortedG SortTag.vf χ) ?_
      refine wellSorted_exSortedG sα ?_
      rwa [fin_snoc_vf_const]

/-- **The counting formula is well-sorted**, so it is admissible as the witness in `SP.acl`. -/
theorem wellSorted_atMost2 {sα : α → SortTag} {k : ℕ} {ψ : LRV.BoundedFormula α 2}
    (hψ : WellSorted sα (fun _ : Fin 2 => SortTag.vf) ψ) :
    WellSorted sα (fun _ : Fin 2 => SortTag.vf) (atMost2 (α := α) k ψ) :=
  wellSorted_not sα _ (iterEx_wellSorted (k + 1) (countBody (α := α) k ψ) (wellSorted_countBody hψ))

end SP

end SpecialTransformations.Milestone0
