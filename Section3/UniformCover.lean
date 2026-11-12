module

/-
**§3's first lemma, the step that is not compactness**: from a *uniform* family of algebraic sets to
algebraicity over `S` alone.

The paper (`paper.tex`, §3, first lemma) proves

> *Let `A` be a definable subset and `s` an element such that `s ∈ acl(a)` for every `a ∈ A`, then
> `s ∈ acl(0)`.*

by compactness, in two steps:

1. **(this file)** if a *single* formula `φ(X, Y)` (with `Y` the parameter) contains `s` at every
   `a ∈ A` and has a finite solution set at every `a ∈ A`, then `s` is algebraic over `S` alone —
   the witness being `∀ y (y ∈ A ⟹ φ(X, y))`, whose solution set is contained in the solution set
   at any one `a ∈ A`.  This is the paper's last line, "`⋂_{a ∈ A} U_a` is a definable finite
   subset that contains `s`", done at the level of the encoding.
2. the compactness step (getting a finite subcover of the family of definable sets
   `{a : φ(X,a) has a finite solution set}`) is *not* in this file: it needs saturation.  Over a
   non-saturated model the statement is not a compactness argument at all, and the frozen form
   additionally misses `A ≠ ∅` — see `AclFibres.lean`.

The formula construction is where `QE/SubstVar.lean` and `QE/ParamBridgeRelabel.lean` are used: the
parameter slot of `φ` becomes a bound variable (`BoundedFormula.relabel`), and the free variable `X`
and that new variable are exchanged into the shape `BoundedFormula.all` expects
(`Sec4Compose.BoundedFormula.substVar`).
-/
public import Sec3Infra
public import SubstVar
public import ParamBridgeRelabel

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open FirstOrder FirstOrder.Language
open scoped FirstOrder

namespace SpecialTransformations.Milestone0
open LRV
open ParamBridge

namespace SP

variable {M : Type*} [LRV.Structure M]

/-! ## The sort map of `S` extended by a `VF`-parameter

`SP.extendVFParam` adds the new parameter at the *end of the `VF` block*, so the sort map of the
extended pair does not depend on the value added. -/

/-- The sort map of the parameter type of `S.extendVFParam a ha`: `VF` on the `VF` block, `RV` on
the `RV` block. -/
def extMap (S : SP M) : Fin (S.n + 1) ⊕ Fin S.m → SortTag
  | Sum.inl _ => .vf
  | Sum.inr _ => .rv

theorem extendVFParam_sortMap (S : SP M) (a : M) (ha : iVF a) :
    (S.extendVFParam a ha).sortMap = extMap S := by
  funext i
  rcases i with i | j <;> rfl

/-! ## The relabelling and variable renaming that turn the parameter `a` into a bound variable -/

/-- The parameter label of `a` in the pair `S.extendVFParam a ha` becomes the variable `x₁` of the
two-variable context `(X, y)`; the old parameters keep their sort. -/
def coverRelabel (S : SP M) :
    (Fin (S.n + 1) ⊕ Fin S.m) → (Fin S.n ⊕ Fin S.m) ⊕ Fin 2
  | Sum.inl i => Fin.lastCases (Sum.inr 1) (fun k => Sum.inl (Sum.inl k)) i
  | Sum.inr j => Sum.inl (Sum.inr j)

/-- The variable substitution that puts the free variable `X` of `φ` (which `relabel` has pushed to
position `2`) at position `0`, leaving the new variable `y` at position `1`. -/
def coverSubst (S : SP M) : Fin 3 → LRV.Term ((Fin S.n ⊕ Fin S.m) ⊕ Fin 2)
  | ⟨0, _⟩ => Term.var (Sum.inr 0)
  | ⟨1, _⟩ => Term.var (Sum.inr 1)
  | ⟨2, _⟩ => Term.var (Sum.inr 0)

theorem coverRelabel_rv (S : SP M) (j : Fin S.m) :
    coverRelabel S (Sum.inr j) = Sum.inl (Sum.inr j) := rfl

theorem coverRelabel_last (S : SP M) :
    coverRelabel S (Sum.inl (Fin.last S.n)) = Sum.inr 1 := by
  rw [coverRelabel]
  simp

theorem coverRelabel_castSucc (S : SP M) (i : Fin S.n) :
    coverRelabel S (Sum.inl (Fin.castSucc i)) = Sum.inl (Sum.inl i) := by
  rw [coverRelabel]
  simp

/-! ## The formula `∀ y (y ∈ VF ⟹ (y ∈ A ⟹ φ(X, y)))` -/

/-- `φ` with its parameter slot turned into the variable `x₁` and its free variable `X` kept at
position `0`: the body of the paper's formula `⋂_{a ∈ A} U_a`. -/
def coverBody (S : SP M) (φ : LRV.BoundedFormula (Fin (S.n + 1) ⊕ Fin S.m) 1) :
    LRV.BoundedFormula (Fin S.n ⊕ Fin S.m) 2 :=
  Sec4Compose.BoundedFormula.substVar (coverSubst S) (φ.relabel (coverRelabel S))

/-- `θ` with its free variable moved from position `0` to position `1` (the parameter of the
`∀`-quantifier in `coverForm`). -/
def coverGuard (S : SP M) (θ : LRV.BoundedFormula (Fin S.n ⊕ Fin S.m) 1) :
    LRV.BoundedFormula (Fin S.n ⊕ Fin S.m) 2 :=
  Sec4Compose.BoundedFormula.substVar (fun _ => Term.var (Sum.inr 1)) θ

theorem coverSubst_tmSort (S : SP M) :
    ∀ i, TmSort S.sortMap (fun _ : Fin 2 => SortTag.vf) (coverSubst S i) = some SortTag.vf := by
  intro i
  fin_cases i <;> rfl

theorem coverRelabel_sorts (S : SP M) :
    ∀ b, (∀ b', coverRelabel S b = Sum.inl b' → S.sortMap b' = extMap S b) ∧
      (∀ j, coverRelabel S b = Sum.inr j → (fun _ : Fin 2 => SortTag.vf) j = extMap S b) := by
  intro b
  rcases b with i | j
  · refine Fin.lastCases ?_ ?_ i
    · constructor
      · intro b' hb
        rw [coverRelabel_last] at hb
        exact absurd hb (by simp)
      · intro k hk
        rw [coverRelabel_last] at hk
        simp only [Sum.inr.injEq] at hk
        subst hk
        rfl
    · intro m
      constructor
      · intro b' hb
        rw [coverRelabel_castSucc] at hb
        simp only [Sum.inl.injEq] at hb
        subst hb
        rfl
      · intro k hk
        rw [coverRelabel_castSucc] at hk
        exact absurd hk (by simp)
  · constructor
    · intro b' hb
      rw [coverRelabel_rv] at hb
      simp only [Sum.inl.injEq] at hb
      subst hb
      rfl
    · intro k hk
      rw [coverRelabel_rv] at hk
      exact absurd hk (by simp)

/-- `sortAssem` of two constant `VF` contexts is constant `VF`. -/
theorem sortAssem_vf {m k : ℕ} :
    sortAssem (fun _ : Fin m => SortTag.vf) (fun _ : Fin k => SortTag.vf) =
      (fun _ : Fin (m + k) => SortTag.vf) := by
  funext i
  simp only [sortAssem]
  split_ifs <;> rfl

/-- `Fin.snoc` of a constant context with the same value is constant. -/
theorem fin_snoc_const {n : ℕ} (s : SortTag) :
    Fin.snoc (fun _ : Fin n => s) s = (fun _ : Fin (n + 1) => s) := by
  funext i
  refine Fin.lastCases ?_ ?_ i
  · rw [Fin.snoc_last]
  · intro k
    rw [Fin.snoc_castSucc]

/-- The two-variable `VF`-context is `Fin.snoc` of the one-variable one. -/
theorem fin_snoc_vf_two :
    Fin.snoc (fun _ : Fin 1 => SortTag.vf) SortTag.vf = (fun _ : Fin 2 => SortTag.vf) :=
  fin_snoc_const SortTag.vf

/-- The guard atom `y ∈ VF` at the tuple `(x, a)` is `iVF a`. -/
theorem pVFG_last_realize (S : SP M) (x a : M) :
    (pVFG (Term.var (Sum.inr (Fin.last 1)))).Realize S.toFun ![x, a] ↔ iVF a := by
  simp [iVF, pVFG]

theorem wellSorted_coverBody (S : SP M) {φ : LRV.BoundedFormula (Fin (S.n + 1) ⊕ Fin S.m) 1}
    (hφ : WellSorted (extMap S) (fun _ => SortTag.vf) φ) :
    WellSorted S.sortMap (fun _ : Fin 2 => SortTag.vf) (coverBody S φ) := by
  rw [coverBody]
  have hrel := ParamBridge.wellSorted_relabel (coverRelabel S) (extMap S) S.sortMap
    (fun _ : Fin 2 => SortTag.vf) (coverRelabel_sorts S) hφ
  rw [sortAssem_vf] at hrel
  exact Sec4Compose.wellSorted_substVar S.sortMap hrel (coverSubst_tmSort S)

theorem wellSorted_coverGuard (S : SP M) {θ : LRV.BoundedFormula (Fin S.n ⊕ Fin S.m) 1}
    (hθ : WellSorted S.sortMap (fun _ => SortTag.vf) θ) :
    WellSorted S.sortMap (fun _ : Fin 2 => SortTag.vf) (coverGuard S θ) := by
  rw [coverGuard]
  refine Sec4Compose.wellSorted_substVar S.sortMap hθ ?_
  intro i
  fin_cases i
  rfl

/-- **The realization of the paper's formula.**  At a tuple `(X, a)` the body
`φ(X, a)` of `coverForm` says what the paper's `U_a` says at `X`. -/
theorem coverBody_realize (S : SP M) (φ : LRV.BoundedFormula (Fin (S.n + 1) ⊕ Fin S.m) 1)
    (a x : M) (ha : iVF a) :
    (coverBody S φ).Realize S.toFun ![x, a] ↔
      φ.Realize (S.extendVFParam a ha).toFun ![x] := by
  have hσ : (fun i : Fin 3 => Term.realize (Sum.elim S.toFun ![x, a]) (coverSubst S i))
      = ![x, a, x] := by
    funext i
    fin_cases i <;> simp [coverSubst]
  rw [coverBody, Sec4Compose.realize_substVar, hσ, BoundedFormula.realize_relabel]
  have hmap : (Sum.elim S.toFun (![x, a, x] ∘ Fin.castAdd 1) ∘ coverRelabel S)
      = (S.extendVFParam a ha).toFun := by
    funext p
    rcases p with i | j
    · refine Fin.lastCases ?_ ?_ i
      · rw [Function.comp_apply, coverRelabel_last, Sum.elim_inr]
        simp [SP.extendVFParam, SP.toFun, Fin.snoc_last]
      · intro k
        rw [Function.comp_apply, coverRelabel_castSucc, Sum.elim_inl]
        simp [SP.extendVFParam, SP.toFun, Fin.snoc_castSucc]
    · rw [Function.comp_apply, coverRelabel_rv, Sum.elim_inl]
      simp [SP.extendVFParam, SP.toFun]
  have hvar : (![x, a, x] ∘ Fin.natAdd 2) = ![x] := by
    funext i
    fin_cases i
    simp
  rw [hmap, hvar]

theorem coverGuard_realize (S : SP M) (θ : LRV.BoundedFormula (Fin S.n ⊕ Fin S.m) 1)
    (a x : M) :
    (coverGuard S θ).Realize S.toFun ![x, a] ↔ θ.Realize S.toFun ![a] := by
  rw [coverGuard, Sec4Compose.realize_substVar]
  have h : (fun _ : Fin 1 => Term.realize (Sum.elim S.toFun ![x, a])
      (Term.var (Sum.inr 1) : LRV.Term ((Fin S.n ⊕ Fin S.m) ⊕ Fin 2))) = ![a] := by
    funext i
    fin_cases i
    simp
  rw [h]

/-- The paper's formula `∀ y (y ∈ VF ⟹ (y ∈ A ⟹ φ(X, y)))`.  `BoundedFormula.all` binds the last
variable of a two-variable context, so the quantifier is over `y` (position `1`) and `X` stays free
at position `0`. -/
def coverForm (S : SP M) (θ : LRV.BoundedFormula (Fin S.n ⊕ Fin S.m) 1)
    (φ : LRV.BoundedFormula (Fin (S.n + 1) ⊕ Fin S.m) 1) :
    LRV.BoundedFormula (Fin S.n ⊕ Fin S.m) 1 :=
  BoundedFormula.all (pVFG (Term.var (Sum.inr (Fin.last 1))) ⟹ (coverGuard S θ ⟹ coverBody S φ))

/-- **Well-sortedness of the paper's formula.** -/
theorem wellSorted_coverForm (S : SP M) {θ : LRV.BoundedFormula (Fin S.n ⊕ Fin S.m) 1}
    {φ : LRV.BoundedFormula (Fin (S.n + 1) ⊕ Fin S.m) 1}
    (hθ : WellSorted S.sortMap (fun _ => SortTag.vf) θ)
    (hφ : WellSorted (extMap S) (fun _ => SortTag.vf) φ) :
    WellSorted S.sortMap (fun _ => SortTag.vf) (coverForm S θ φ) := by
  have hη : WellSorted S.sortMap (Fin.snoc (fun _ : Fin 1 => SortTag.vf) SortTag.vf)
      (pVFG (Term.var (Sum.inr (Fin.last 1)))) := by
    refine wellSorted_pVFG S.sortMap _ ?_
    rw [tmSort_var_inr, Fin.snoc_last]
  have hψ : WellSorted S.sortMap (Fin.snoc (fun _ : Fin 1 => SortTag.vf) SortTag.vf)
      (coverGuard S θ ⟹ coverBody S φ) := by
    rw [fin_snoc_vf_two]
    exact WellSorted.imp _ (wellSorted_coverGuard S hθ) (wellSorted_coverBody S hφ)
  exact wellSorted_all_guarded (s := SortTag.vf) S.sortMap hη hψ InAntecedent.atom

/-- **The realization of `coverForm`**: `∀ y ∈ VF, y ∈ A → φ(X, y)`. -/
theorem coverForm_realize (S : SP M) (θ : LRV.BoundedFormula (Fin S.n ⊕ Fin S.m) 1)
    (A : Set M) (hA : ∀ y, y ∈ A ↔ iVF y ∧ θ.Realize S.toFun ![y])
    (φ : LRV.BoundedFormula (Fin (S.n + 1) ⊕ Fin S.m) 1) (x : M) :
    (coverForm S θ φ).Realize S.toFun ![x] ↔
      ∀ (a : M) (ha : iVF a), a ∈ A → φ.Realize (S.extendVFParam a ha).toFun ![x] := by
  rw [coverForm, BoundedFormula.realize_all]
  constructor
  · intro h a ha hA'
    have h1 : (Fin.snoc ![x] a : Fin 2 → M) = ![x, a] := by
      funext i; fin_cases i <;> simp
    have hg := h a
    rw [BoundedFormula.realize_imp, BoundedFormula.realize_imp, h1] at hg
    have hguard2 : (coverGuard S θ).Realize S.toFun ![x, a] := by
      rw [coverGuard_realize]
      exact ((hA a).1 hA').2
    have hconcl := hg ((pVFG_last_realize S x a).2 ha) hguard2
    rwa [coverBody_realize] at hconcl
  · intro h a
    simp only [BoundedFormula.realize_imp]
    intro ha hg
    have h1 : (Fin.snoc ![x] a : Fin 2 → M) = ![x, a] := by
      funext i; fin_cases i <;> simp
    rw [h1] at ha hg ⊢
    rw [coverGuard_realize] at hg
    rw [coverBody_realize]
    exact h a ((pVFG_last_realize S x a).1 ha)
      ((hA a).2 ⟨(pVFG_last_realize S x a).1 ha, hg⟩)

/-- **§3's first lemma, non-compactness part.**  If `A` is `S`-definable, nonempty, `φ` is a
single well-sorted formula that at *every* `a ∈ A` holds at `s` and has a finite solution set, then
`s` is algebraic over `S`: the witness is `∀ y (y ∈ VF ⟹ (y ∈ A ⟹ φ(X, y)))`, which is definable
over `S` alone and whose solution set is contained in the solution set at any one `a ∈ A`. -/
theorem acl_of_uniform_cover
    (S : SP M) (A : Set M) (θ : LRV.BoundedFormula (Fin S.n ⊕ Fin S.m) 1)
    (hθ : WellSorted S.sortMap (fun _ => SortTag.vf) θ)
    (hA : ∀ y, y ∈ A ↔ iVF y ∧ θ.Realize S.toFun ![y])
    (hAne : A.Nonempty)
    (φ : LRV.BoundedFormula (Fin (S.n + 1) ⊕ Fin S.m) 1)
    (hφ : WellSorted (extMap S) (fun _ => SortTag.vf) φ)
    (s : M) (hsVF : iVF s)
    (hs : ∀ a : M, (ha : iVF a) → a ∈ A →
      φ.Realize (S.extendVFParam a ha).toFun ![s])
    (hfin : ∀ a : M, (ha : iVF a) → a ∈ A →
      ({x : M | iVF x ∧ φ.Realize (S.extendVFParam a ha).toFun ![x]} : Set M).Finite) :
    acl S s := by
  classical
  obtain ⟨a₀, ha₀⟩ := hAne
  have ha₀VF : iVF a₀ := ((hA a₀).1 ha₀).1
  have hsub : {x : M | iVF x ∧ (coverForm S θ φ).Realize S.toFun ![x]} ⊆
      {x : M | iVF x ∧ φ.Realize (S.extendVFParam a₀ ha₀VF).toFun ![x]} := by
    intro x hx
    obtain ⟨hxVF, hxΨ⟩ := hx
    refine ⟨hxVF, ?_⟩
    rw [coverForm_realize S θ A hA φ x] at hxΨ
    exact hxΨ a₀ ha₀VF ha₀
  refine ⟨coverForm S θ φ, wellSorted_coverForm S hθ hφ, ?_, hsVF, ?_⟩
  · exact (hfin a₀ ha₀VF ha₀).subset hsub
  · rw [coverForm_realize S θ A hA φ s]
    exact hs

end SP

end SpecialTransformations.Milestone0
