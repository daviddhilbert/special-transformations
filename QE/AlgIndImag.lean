/-
**`alg:ind:imag`** (`paper.tex:702`, §3) — from swarm `smw1jgnht` m5, verified here (compiled:
exit 0, 0 errors, no `sorry`; `#print axioms` on every reported theorem within
{propext, Classical.choice, Quot.sound}).

The paper's Corollary: *if `a ∈ VF` is such that `a ∉ acl(∅)`, then for any `t ∈ RV` we have
`a ∉ acl(t)`* — over a monster model, with the paper's one-line proof ("then `a ∈ acl(b)` for every
`b ∈ rv⁻¹(t)`, so by exchange `b ∈ acl(a)` for all of them, which is impossible").

**The silent step is proved, not assumed.**  `M5.acl_of_rv_eq`: a formula well-sorted over the single
`RV`-parameter `t` becomes a formula over the single `VF`-parameter `b` when each occurrence of `t` is
read as `rv(b)` — via this file's own term/formula substitution (`substTerm`/`substFormula`,
`tmSort_substTerm`, `wellSorted_substFormula` preserving `Occurs`/`InAntecedent`/`GuardsLast`/
`GuardTrue`, `realize_substFormula`).  That is the same operation `QE/SubstVar.lean` builds for §4;
two independent constructions, both green.

Then `fibre_subset_acl` (`rv⁻¹(t) ⊆ acl(a)`), and the cardinality contradiction:
`alg_ind_imag` from `ExchangeVF` (Yin 4.3, a hypothesis), `hfib` (the fibre is not small) and `hacl`
(`acl(a)` is small).  `hacl` is *derived*, not assumed, in `acl_small_of_countable` /
`alg_ind_imag_of_countable` — from `Countable` of the formula set and `ℵ₀ < κ`, which is the right
derivation.

**One case remains, and it is small**: `t = rv 0 = ∞`, where the fibre is `{0}` so `hfib` fails.  The
claim there is `acl(rv 0) ⊆ acl(∅)`-shaped, and it needs the **parameter** substitution that Mathlib
*does* provide — `BoundedFormula.subst (f : α → Term β)` with `f` sending the single `RV` parameter to
the closed term `tRVZero` — plus `realize_subst` and a `WellSorted`-preservation induction for that
substitution.  No variable substitution is involved, so it is a bounded piece of work, not a wall.

Check with `.scratch2/sec3/` (compiled `Enc`, `Sat`, `Sec3Frozen`): copy this file there and
`LEAN_PATH=$PWD:$LEAN_PATH lean` it.
-/
import Sat
import Sec3Frozen

/-!
Compile with (from `<repo>/.ultramath/smw1jgnht/m5/`):

    LEAN_PATH=../../../.scratch2/sec3:$LEAN_PATH lean AlgIndImag.lean
-/

open FirstOrder FirstOrder.Language
open scoped FirstOrder

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

/-
# Section 3, `alg:ind:imag`: nothing algebraic over `∅` is algebraic over an `RV`-element

The paper (`paper.tex`, §3, right after `exchange`):

> **Corollary `alg:ind:imag`.** If `a ∈ VF` is such that `a ∉ acl(0)`, then for any `t ∈ RV` we have
> `a ∉ acl(t)`. Similarly, if `t ∈ RV` is such that `t ∉ acl(0)`, then for any `γ ∈ Γ` we have
> `t ∉ acl(γ)`.
>
> *Proof.* For the first claim, suppose for contradiction that `a ∈ acl(t)`. Then `a ∈ acl(b)` for
> every `b ∈ rv⁻¹(t)`. So by the exchange principle we have `b ∈ acl(a)` for every `b ∈ rv⁻¹(t)`,
> which is impossible. The other claim is proved in the same way.

What is formalized here (the `Γ` half is not expressible: `SP.acl` is `VF`-valued, and `Γ` lives in
the `LRVΓ` expansion — see `QE/Sec3_frozen.lean` and `QE/Sec3_sat.lean`):

* `M5.acl_of_rv_eq` — the paper's silent step "a ∈ acl(b) for every b ∈ rv⁻¹(t)": a formula
  well-sorted over the one `RV`-parameter `t` becomes a formula over the one `VF`-parameter `b` when
  each occurrence of `t` is read as `rv(b)`.  This is a substitution at the level of the encoding's
  syntax (`substFormula`, `substTerm`), with the two facts that make it legitimate:
  `tmSort_substTerm` (the sort of a term is preserved) and `wellSorted_substFormula`
  (`WellSorted` is preserved, including the guards `Occurs`/`InAntecedent`, `GuardTrue`) together
  with `realize_substFormula` (the substituted formula has the same truth value).
* `M5.fibre_subset_acl` — the paper's proof up to the counting: `rv⁻¹(t) ⊆ acl(a)`.
* `M5.alg_ind_imag` — the corollary, with (i) Yin's exchange (paper `exchange`, QE:ACVF:min 4.3) as
  an explicit hypothesis `ExchangeVF`, (ii) the `rv`-fibre is not small (`hfib`; it is a ball, hence
  infinite of the model's cardinality) and (iii) `acl` of one point is small (`hacl`).
* `M5.infinite_of_not_small` — `hfib` implies the paper's "the fibre is infinite".
* `M5.acl_small_of_countable` and `M5.alg_ind_imag_of_countable` — `hacl` is *derived* from the
  countability of the formula set and `κ > ℵ₀`, so the only remaining cardinality input is the size
  of a ball.

No `axiom`, no `sorry`, no `native_decide`; `#print axioms` at the end of the file shows that every
reported theorem depends only on `propext`, `Classical.choice` and `Quot.sound`.
-/

namespace SpecialTransformations
namespace Milestone0
open LRV

namespace M5

/-! ## A. Substituting the `RV` parameter `t` by `rv` of the `VF` parameter `b`

The encoding-level step that the paper's proof of `alg:ind:imag` uses silently ("Then
`a ∈ acl(b)` for every `b ∈ rv⁻¹(t)`"): the formula over the parameter `t` becomes a formula over
the parameter `b` once every occurrence of `t` is read as `rv(b)`. -/

/-- `rv` of the `VF` parameter `b` of the pair `singleVF b`, as a term of the target context. -/
def rvVF {n : ℕ} : LRV.Term ((Fin 1 ⊕ Fin 0) ⊕ Fin n) :=
  Term.func (L := LRV) Fn.rvMap ![Term.var (Sum.inl (Sum.inl 0))]

/-- The map on names underlying `substTerm`: the `RV`-parameter goes to `rv` of the `VF`-parameter,
every variable stays where it is. -/
def substName {n : ℕ} : ((Fin 0 ⊕ Fin 1) ⊕ Fin n) → LRV.Term ((Fin 1 ⊕ Fin 0) ⊕ Fin n)
  | Sum.inl (Sum.inl j) => Fin.elim0 j
  | Sum.inl (Sum.inr _) => rvVF
  | Sum.inr i => Term.var (Sum.inr i)

/-- **Term substitution**: a term of the context of `singleRV t` (parameters `Fin 0 ⊕ Fin 1`,
variables `Fin n`) is read in the context of `singleVF b` (parameters `Fin 1 ⊕ Fin 0`) by sending
the `RV`-parameter to `rv` of the `VF`-parameter.  Variables are untouched. -/
def substTerm {n : ℕ} (t : LRV.Term ((Fin 0 ⊕ Fin 1) ⊕ Fin n)) :
    LRV.Term ((Fin 1 ⊕ Fin 0) ⊕ Fin n) :=
  t.subst (substName (n := n))

/-- **Formula substitution**, on the same contexts. -/
def substFormula : ∀ {n : ℕ},
    LRV.BoundedFormula (Fin 0 ⊕ Fin 1) n → LRV.BoundedFormula (Fin 1 ⊕ Fin 0) n
  | _, .falsum => .falsum
  | _, .equal t u => .equal (substTerm t) (substTerm u)
  | _, .rel R ts => .rel R fun i => substTerm (ts i)
  | _, .imp a b => .imp (substFormula a) (substFormula b)
  | _, .all χ => .all (substFormula χ)

@[simp] theorem substTerm_var_inr {n : ℕ} (i : Fin n) :
    substTerm (n := n) (Term.var (Sum.inr i) : LRV.Term ((Fin 0 ⊕ Fin 1) ⊕ Fin n)) =
      Term.var (Sum.inr i) := rfl

@[simp] theorem substTerm_func {n l : ℕ} (g : Fn l)
    (ts : Fin l → LRV.Term ((Fin 0 ⊕ Fin 1) ⊕ Fin n)) :
    substTerm (Term.func g ts) = Term.func g fun i => substTerm (ts i) := rfl

@[simp] theorem substFormula_falsum {n : ℕ} :
    substFormula (BoundedFormula.falsum (L := LRV) (α := Fin 0 ⊕ Fin 1) (n := n)) = .falsum := rfl

@[simp] theorem substFormula_equal {n : ℕ} (t u : LRV.Term ((Fin 0 ⊕ Fin 1) ⊕ Fin n)) :
    substFormula (BoundedFormula.equal t u) = BoundedFormula.equal (substTerm t) (substTerm u) :=
  rfl

@[simp] theorem substFormula_rel {n l : ℕ} (R : Rel l)
    (ts : Fin l → LRV.Term ((Fin 0 ⊕ Fin 1) ⊕ Fin n)) :
    substFormula (BoundedFormula.rel R ts) = BoundedFormula.rel R (fun i => substTerm (ts i)) :=
  rfl

@[simp] theorem substFormula_imp {n : ℕ} (a b : LRV.BoundedFormula (Fin 0 ⊕ Fin 1) n) :
    substFormula (BoundedFormula.imp a b) =
      BoundedFormula.imp (substFormula a) (substFormula b) := rfl

@[simp] theorem substFormula_all {n : ℕ} (χ : LRV.BoundedFormula (Fin 0 ⊕ Fin 1) (n + 1)) :
    substFormula (BoundedFormula.all χ) = BoundedFormula.all (substFormula χ) := rfl

/-! ## B. Realizability: the substituted formula says the same thing -/

variable {M : Type*}

/-- The valuation of the parameters of the pair `singleVF b`. -/
def valVF (b : M) : Fin 1 ⊕ Fin 0 → M :=
  Sum.elim (fun _ => b) (fun j => Fin.elim0 j)

/-- The valuation of the parameters of the pair `singleRV t`. -/
def valRV (t : M) : Fin 0 ⊕ Fin 1 → M :=
  Sum.elim (fun j => Fin.elim0 j) (fun _ => t)

variable [LRV.Structure M]

theorem realize_substTerm {b t : M} (hbt : iRv b = t) {n : ℕ} (xs : Fin n → M)
    (s : LRV.Term ((Fin 0 ⊕ Fin 1) ⊕ Fin n)) :
    (substTerm s).realize (Sum.elim (valVF b) xs) =
      s.realize (Sum.elim (valRV t) xs) := by
  rw [substTerm, Term.realize_subst]
  refine congrArg (fun v => Term.realize v s) ?_
  funext a
  rcases a with (j | j) | i
  · exact Fin.elim0 j
  · -- the `RV` parameter: its image is `rv` of the `VF` parameter, and `rv b = t`
    have h1 : Term.realize (Sum.elim (valVF b) xs)
        (substName (Sum.inl (Sum.inr j)) : LRV.Term ((Fin 1 ⊕ Fin 0) ⊕ Fin n)) = iRv b := by
      simp only [substName, rvVF, Term.realize, iRv]
      congr 1
      funext i
      rw [Matrix.cons_val_fin_one, Matrix.cons_val_fin_one]
      rfl
    rw [h1, hbt]
    show t = Sum.elim (valRV t) xs (Sum.inl (Sum.inr j))
    simp [valRV]
  · rfl

theorem realize_substFormula {b t : M} (hbt : iRv b = t) :
    ∀ {n : ℕ} (φ : LRV.BoundedFormula (Fin 0 ⊕ Fin 1) n) (xs : Fin n → M),
      (substFormula φ).Realize (valVF b) xs ↔ φ.Realize (valRV t) xs
  | _, .falsum, _ => Iff.rfl
  | _, .equal u v, xs => by
    show (substTerm u).realize (Sum.elim (valVF b) xs) =
        (substTerm v).realize (Sum.elim (valVF b) xs) ↔
      u.realize (Sum.elim (valRV t) xs) = v.realize (Sum.elim (valRV t) xs)
    rw [realize_substTerm hbt xs u, realize_substTerm hbt xs v]
  | _, .rel R ts, xs => by
    show FirstOrder.Language.Structure.RelMap R
        (fun i => (substTerm (ts i)).realize (Sum.elim (valVF b) xs)) ↔
      FirstOrder.Language.Structure.RelMap R
        (fun i => (ts i).realize (Sum.elim (valRV t) xs))
    rw [show (fun i => (substTerm (ts i)).realize (Sum.elim (valVF b) xs)) =
        (fun i => (ts i).realize (Sum.elim (valRV t) xs)) from
      funext fun i => realize_substTerm hbt xs (ts i)]
  | _, .imp a c, xs => by
    show ((substFormula a).Realize (valVF b) xs → (substFormula c).Realize (valVF b) xs) ↔
      (a.Realize (valRV t) xs → c.Realize (valRV t) xs)
    rw [realize_substFormula hbt a xs, realize_substFormula hbt c xs]
  | _, .all χ, xs => by
    show (∀ a : M, (substFormula χ).Realize (valVF b) (Fin.snoc xs a)) ↔
      ∀ a : M, χ.Realize (valRV t) (Fin.snoc xs a)
    exact forall_congr' fun a => realize_substFormula hbt χ (Fin.snoc xs a)


/-! ## C. Well-sortedness is preserved by the substitution -/

/-- The sort of a substituted term: the `RV`-parameter becomes `rv` of a `VF`-parameter, so a term
of sort `s` over `(RV)` stays of sort `s` over `(VF)`. -/
theorem tmSort_substTerm_aux {n : ℕ} {sn : Fin n → SortTag} :
    ∀ (t : LRV.Term ((Fin 0 ⊕ Fin 1) ⊕ Fin n)) (s : SortTag),
      TmSort (fun _ => SortTag.rv) sn t = some s →
        TmSort (fun _ => SortTag.vf) sn (substTerm t) = some s
  | Term.var (Sum.inl (Sum.inl j)), s, _ => Fin.elim0 j
  | Term.var (Sum.inl (Sum.inr _)), s, h => by
    rw [tmSort_var_inl] at h
    have hs : SortTag.rv = s := Option.some.inj h
    subst hs
    have harg : ∀ i : Fin 1, TmSort (fun _ => SortTag.vf) sn
        (![Term.var (Sum.inl (Sum.inl (0 : Fin 1)))] i :
          LRV.Term ((Fin 1 ⊕ Fin 0) ⊕ Fin n)) = some .vf := by
      intro i
      fin_cases i
      exact tmSort_var_inl _ _ _
    exact tmSort_func _ _ Fn.rvMap _ harg
  | Term.var (Sum.inr i), s, h => by
    rw [tmSort_var_inr] at h
    have hs : sn i = s := Option.some.inj h
    subst hs
    exact tmSort_var_inr _ _ i
  | Term.func g ts, s, h => by
    obtain ⟨hargs, hres⟩ := (tmSort_func_iff (sα := fun _ => SortTag.rv) sn g ts).1 h
    subst hres
    exact tmSort_func _ _ g _ (fun i => tmSort_substTerm_aux (ts i) _ (hargs i))

theorem tmSort_substTerm {n : ℕ} {sn : Fin n → SortTag}
    {t : LRV.Term ((Fin 0 ⊕ Fin 1) ⊕ Fin n)} {s : SortTag}
    (h : TmSort (fun _ => SortTag.rv) sn t = some s) :
    TmSort (fun _ => SortTag.vf) sn (substTerm t) = some s :=
  tmSort_substTerm_aux t s h

/-- The guard atoms are untouched by the substitution (they mention variables only). -/
theorem substFormula_sortPredG {n : ℕ} (s : SortTag) (i : Fin n) :
    substFormula (sortPredG (α := Fin 0 ⊕ Fin 1) s (Term.var (Sum.inr i))) =
      sortPredG (α := Fin 1 ⊕ Fin 0) s (Term.var (Sum.inr i)) := by
  cases s with
  | vf =>
    simp only [sortPredG, pVFG, Relations.boundedFormula₁, Relations.boundedFormula,
      substFormula_rel]
    first
      | rfl
      | (congr 1; funext j; fin_cases j; rfl)
  | rv =>
    simp only [sortPredG, pRVG, Relations.boundedFormula₁, Relations.boundedFormula,
      substFormula_rel]
    first
      | rfl
      | (congr 1; funext j; fin_cases j; rfl)

theorem guardAtom_substFormula {n : ℕ} (s : SortTag) (i : Fin n) :
    substFormula (guardAtom (α := Fin 0 ⊕ Fin 1) s i) =
      guardAtom (α := Fin 1 ⊕ Fin 0) s i :=
  substFormula_sortPredG s i

/-- `InAntecedent` is preserved: the guard atoms are unchanged. -/
theorem inAntecedent_substFormula {n : ℕ} {s : SortTag} {i : Fin n}
    {ψ : LRV.BoundedFormula (Fin 0 ⊕ Fin 1) n} (h : InAntecedent s i ψ) :
    InAntecedent s i (substFormula ψ) := by
  induction h with
  | atom =>
    rw [guardAtom_substFormula]
    exact InAntecedent.atom
  | and_left _ ih => exact InAntecedent.and_left ih
  | and_right _ ih => exact InAntecedent.and_right ih

/-- `Occurs` is preserved. -/
theorem occurs_substFormula {n : ℕ} {s : SortTag} {i : Fin n}
    {ψ : LRV.BoundedFormula (Fin 0 ⊕ Fin 1) n} (h : Occurs i s ψ) :
    Occurs i s (substFormula ψ) :=
  inAntecedent_substFormula h

/-- `GuardTrue` implies `GuardsLast` (the `GuardsLast` field of `WellSorted.all` is the weaker of
the two conditions; the frozen constructor keeps both). -/
theorem guardsLast_of_guardTrue {α : Type} {n : ℕ} {s : SortTag} {i : Fin n}
    {ψ : LRV.BoundedFormula α n} (h : GuardTrue s i ψ) : GuardsLast s i ψ := by
  induction h with
  | imp hin => exact Or.inl hin
  | all _ ih => exact ih

/-- `GuardTrue` is preserved. -/
theorem guardTrue_substFormula {n : ℕ} {s : SortTag} {i : Fin n}
    {ψ : LRV.BoundedFormula (Fin 0 ⊕ Fin 1) n} (h : GuardTrue s i ψ) :
    GuardTrue s i (substFormula ψ) := by
  induction h with
  | imp h1 => exact GuardTrue.imp (inAntecedent_substFormula h1)
  | all _ ih => exact GuardTrue.all ih

/-- **Well-sortedness of the substituted formula**: reading the `RV`-parameter as `rv` of the
`VF`-parameter gives a formula of the two-sorted language over the `VF`-parameter, with the same
variables (the substitution only changes one parameter's *sort*). -/
theorem wellSorted_substFormula :
    ∀ {n : ℕ} (sn : Fin n → SortTag) (φ : LRV.BoundedFormula (Fin 0 ⊕ Fin 1) n),
      WellSorted (fun _ => SortTag.rv) sn φ →
        WellSorted (fun _ => SortTag.vf) sn (substFormula φ)
  | _, _, .falsum, _ => WellSorted.falsum _
  | _, sn, .equal t u, h => by
    cases h with
    | equal _ ht hu => exact WellSorted.equal sn (tmSort_substTerm ht) (tmSort_substTerm hu)
  | _, sn, .rel R ts, h => by
    cases h with
    | rel _ _ _ hh =>
      exact WellSorted.rel sn R (fun i => substTerm (ts i)) (fun i => tmSort_substTerm (hh i))
  | _, sn, .imp a b, h => by
    cases h with
    | imp _ ha hb =>
      exact WellSorted.imp sn (wellSorted_substFormula sn a ha)
        (wellSorted_substFormula sn b hb)
  | _, sn, .all χ, h => by
    cases h with
    | all _ hχ hg hj =>
      rename_i sX
      have hgt : GuardTrue sX (Fin.last _) (substFormula χ) :=
        guardTrue_substFormula (ψ := χ) hj
      exact WellSorted.all (s := sX) sn
        (wellSorted_substFormula (Fin.snoc sn sX) χ hχ)
        (guardsLast_of_guardTrue (ψ := substFormula χ) hgt) hgt


end M5

/-! ## D. Transport of `acl` from the `RV` parameter `t` to a `VF` parameter `b` with `rv b = t` -/

namespace SP

variable {M : Type*} [LRV.Structure M]

theorem sortMap_singleVF (b : M) (hb : iVF b) :
    (SP.singleVF b hb).sortMap = fun _ => SortTag.vf := by
  funext x
  rcases x with j | j
  · rfl
  · exact Fin.elim0 j

theorem sortMap_singleRV (t : M) (ht : iRV t) :
    (SP.singleRV t ht).sortMap = fun _ => SortTag.rv := by
  funext x
  rcases x with j | j
  · exact Fin.elim0 j
  · rfl

theorem toFun_singleVF (b : M) (hb : iVF b) : (SP.singleVF b hb).toFun = M5.valVF b := rfl

theorem toFun_singleRV (t : M) (ht : iRV t) : (SP.singleRV t ht).toFun = M5.valRV t := rfl

end SP

namespace M5

variable {M : Type*} [LRV.Structure M]

/-- **The paper's step "then `a ∈ acl(b)` for every `b ∈ rv⁻¹(t)`"**: a formula that is well-sorted
over the one `RV`-parameter `t` reads over the one `VF`-parameter `b` as a formula of the same
variables, with the parameter `t` replaced by `rv(b)`.  The solution set is therefore unchanged when
`rv b = t`, so algebraic closure over `t` implies algebraic closure over `b`. -/
theorem acl_of_rv_eq {t b x : M} (ht : iRV t) (hb : iVF b) (hbt : iRv b = t)
    (h : SP.acl (SP.singleRV t ht) x) : SP.acl (SP.singleVF b hb) x := by
  obtain ⟨φ, hφ, hfin, hx⟩ := h
  -- read the formula in the canonical context `Fin 0 ⊕ Fin 1`
  let φ₀ : LRV.BoundedFormula (Fin 0 ⊕ Fin 1) 1 := φ
  have hφ₀ : WellSorted (fun _ => SortTag.rv) (fun _ => SortTag.vf) φ₀ := by
    rw [SP.sortMap_singleRV] at hφ
    exact hφ
  have hfin₀ : ({y : M | iVF y ∧ φ₀.Realize (valRV t) ![y]} : Set M).Finite := by
    rw [SP.toFun_singleRV] at hfin
    exact hfin
  have hx₀ : iVF x ∧ φ₀.Realize (valRV t) ![x] := by
    rw [SP.toFun_singleRV] at hx
    exact hx
  refine ⟨substFormula φ₀, ?_, ?_, ?_⟩
  · rw [SP.sortMap_singleVF]
    exact wellSorted_substFormula (fun _ => SortTag.vf) φ₀ hφ₀
  · have hset : ({y : M | iVF y ∧ (substFormula φ₀).Realize (valVF b) ![y]} : Set M) =
        {y : M | iVF y ∧ φ₀.Realize (valRV t) ![y]} := by
      refine Set.ext fun y => ?_
      show (iVF y ∧ (substFormula φ₀).Realize (valVF b) ![y]) ↔
        (iVF y ∧ φ₀.Realize (valRV t) ![y])
      rw [realize_substFormula hbt φ₀]
    have hfin' : ({y : M | iVF y ∧ (substFormula φ₀).Realize (valVF b) ![y]} : Set M).Finite :=
      hset ▸ hfin₀
    simpa only [SP.toFun_singleVF] using hfin'
  · refine ⟨hx₀.1, ?_⟩
    have hgoal : (substFormula φ₀).Realize (valVF b) ![x] := by
      rw [realize_substFormula hbt φ₀]
      exact hx₀.2
    simpa only [SP.toFun_singleVF] using hgoal

end M5

/-! ## E. The paper's corollary `alg:ind:imag` -/

namespace M5

/-- **Yin's exchange principle** (paper `exchange`, Lemma 4.3, `VF` half, cited from
`QE:ACVF:min`, Lemma 4.3), as an explicit hypothesis of the theorem below: *"For any `a`, `b ∈ VF`,
if `a ∈ acl(b) ∖ acl(0)` then `b ∈ acl(a)`."*

`acl (S.extendVFParam b hb)` is `acl(S ∪ {b})`, so at `S = 0` (the pair `S.base`) this is exactly
the paper's `a ∈ acl(b) ∖ acl(0) → b ∈ acl(a)`; the paper's statement is at the empty parameter
set, and the general-`S` form is what the paper's Lemma 4.3 is quoted as (`acl(b)`, not `acl(S, b)`),
so nothing beyond the paper's sentence is assumed.  The `RV` half of the paper's exchange
(`t ∈ acl(s) ∖ acl(0) → s ∈ acl(t)` for `t, s ∈ RV`) is not expressible in this encoding, where
`SP.acl` is `VF`-valued (see `QE/Sec3_frozen.lean`); it is not used below. -/
def ExchangeVF (𝕄 : Sat.MonsterACVF) : Prop :=
  ∀ (S : SP 𝕄.M) (a b : 𝕄.M) (ha : iVF a) (hb : iVF b),
    SP.acl (S.extendVFParam b hb) a → ¬ SP.acl S a → SP.acl (S.extendVFParam a ha) b

variable {𝕄 : Sat.MonsterACVF}

/-- **The fibre of `rv` over `t` is contained in `acl(a)`**, given `a ∈ acl(t)` and exchange.
This is the paper's proof of `alg:ind:imag` up to the counting: for every `b` in the fibre,
`a ∈ acl(b)` (the substitution lemma above), so exchange gives `b ∈ acl(a)`. -/
theorem fibre_subset_acl (hex : ExchangeVF 𝕄) (a t : 𝕄.M) (ha : iVF a) (ht : iRV t)
    (h0 : ¬ SP.acl (SP.base (M := 𝕄.M)) a) (h : SP.acl (SP.singleRV t ht) a) :
    {x : 𝕄.M | iVF x ∧ iRv x = t} ⊆ {y : 𝕄.M | SP.acl (SP.singleVF a ha) y} := by
  intro b hb
  obtain ⟨hbVF, hbt⟩ := hb
  exact hex (SP.base (M := 𝕄.M)) a b ha hbVF (M5.acl_of_rv_eq ht hbVF hbt h) h0

/-- A set that is not small in the monster model is infinite: a finite set has cardinality at most
`ℵ₀ ≤ 𝕄.κ`.  (So the hypothesis `hfib` of `alg_ind_imag` is the paper's "for every `t`, the fibre
`rv⁻¹(t)` is infinite", in the sharp form the counting argument needs.) -/
theorem infinite_of_not_small {s : Set 𝕄.M} (h : ¬ 𝕄.Small ↥s) : s.Infinite := by
  intro hfin
  have : Finite ↥s := hfin
  exact h (lt_of_lt_of_le (Cardinal.lt_aleph0_of_finite ↥s) 𝕄.aleph0_le)

/-- **`alg:ind:imag`** (paper §3, corollary of `exchange`; the paper's sentence: *"If `a ∈ VF` is
such that `a ∉ acl(0)`, then for any `t ∈ RV` we have `a ∉ acl(t)`."*).

The proof is the paper's: suppose `a ∈ acl(t)`.  Then `a ∈ acl(b)` for every `b` in the fibre of
`rv` over `t` (the substitution lemma `acl_of_rv_eq`), so by exchange `b ∈ acl(a)` for every such
`b`; the whole fibre is therefore contained in `acl(a)`.  But `acl(a)` is small — it is the union,
over a countable set of formulas with one parameter, of finite solution sets — while the fibre
`rv⁻¹(t)` is a ball, hence has as many elements as the monster model, and so is not small.  The two
numeral facts are taken as explicit hypotheses `hfib`, `hacl`: `hfib` is the cardinality of the
`rv`-fibre, `hacl` the smallness of `acl` of a single point, with `𝕄.Small` from
`Milestone0/Saturation.lean`.

`hfib` is automatic for every `t` whose `rv`-fibre is a ball, and it fails only at `t = rv 0 = ∞`,
where by the axiom `rvEqInfty` the fibre is the singleton `{0}`.  The paper's claim at that `t` is
`a ∉ acl(rv 0)`, which is `a ∉ acl(0)` — the hypothesis `h` itself — because `0` is a term of the
language; reducing `acl(rv 0)` to `acl(0)` is a second instance of the substitution lemma of Part A,
with the *closed* term `rv(0)` in place of `rv(b)`, and is not built here. -/
theorem alg_ind_imag (hex : ExchangeVF 𝕄) (a t : 𝕄.M) (ha : iVF a) (ht : iRV t)
    (hfib : ¬ 𝕄.Small ↥{x : 𝕄.M | iVF x ∧ iRv x = t})
    (hacl : 𝕄.Small ↥{y : 𝕄.M | SP.acl (SP.singleVF a ha) y})
    (h : ¬ SP.acl (SP.base (M := 𝕄.M)) a) :
    ¬ SP.acl (SP.singleRV t ht) a := by
  intro hcon
  exact hfib (lt_of_le_of_lt
    (Cardinal.mk_le_mk_of_subset (fibre_subset_acl hex a t ha ht h hcon)) hacl)

end M5


/-! ## F. The smallness of `acl(a)` from countability

The hypothesis `hacl` of `alg_ind_imag` — `acl` of one point is small — is not an assumption about
the valued field: it holds as soon as the set of formulas is countable and `κ > ℵ₀`, because `acl`
of one point is the union, over the countably many formulas `φ` with one free variable and one
parameter, of the finite solution set `φ(𝕄, a)`.  We prove the implication here, so that the
hypothesis is reduced to the metamathematical countability of the syntax.  (Its companion `hfib`,
that the `rv`-fibre is not small, is the geometric input: `rv⁻¹(t)` is a ball and has as many
elements as the monster model.) -/

namespace M5

/-- **`acl` of a point is small**, given that the formula set is countable and `κ > ℵ₀`: the
algebraic closure of `{a}` is the union of the solution sets of the countably many formulas with
one free `VF`-variable and the parameter `a`, and each of those that is finite contributes a finite
set; the union is therefore countable, hence of cardinality `≤ ℵ₀ < κ`. -/
theorem acl_small_of_countable {𝕄 : Sat.MonsterACVF} (hκ : Cardinal.aleph0 < 𝕄.κ)
    (hcnt : Countable (LRV.BoundedFormula (Fin 1 ⊕ Fin 0) 1)) (a : 𝕄.M) (ha : iVF a) :
    𝕄.Small ↥{y : 𝕄.M | SP.acl (SP.singleVF a ha) y} := by
  classical
  haveI hc : Countable (LRV.BoundedFormula (Fin 1 ⊕ Fin 0) 1) := hcnt
  have hsub : {y : 𝕄.M | SP.acl (SP.singleVF a ha) y} ⊆
      ⋃ (i : {φ : LRV.BoundedFormula (Fin 1 ⊕ Fin 0) 1 //
          ({y : 𝕄.M | iVF y ∧ φ.Realize (valVF a) ![y]} : Set 𝕄.M).Finite}),
        {y : 𝕄.M | iVF y ∧ (i.1).Realize (valVF a) ![y]} := by
    intro y hy
    obtain ⟨φ, hφ, hfin, hy⟩ := hy
    let φ₀ : LRV.BoundedFormula (Fin 1 ⊕ Fin 0) 1 := φ
    have hfin₀ : ({y : 𝕄.M | iVF y ∧ φ₀.Realize (valVF a) ![y]} : Set 𝕄.M).Finite := by
      rw [SP.toFun_singleVF] at hfin
      exact hfin
    have hy₀ : iVF y ∧ φ₀.Realize (valVF a) ![y] := by
      rw [SP.toFun_singleVF] at hy
      exact hy
    exact Set.mem_iUnion.mpr ⟨⟨φ₀, hfin₀⟩, hy₀⟩
  have hU : (⋃ (i : {φ : LRV.BoundedFormula (Fin 1 ⊕ Fin 0) 1 //
        ({y : 𝕄.M | iVF y ∧ φ.Realize (valVF a) ![y]} : Set 𝕄.M).Finite}),
        {y : 𝕄.M | iVF y ∧ (i.1).Realize (valVF a) ![y]}).Countable :=
    Set.countable_iUnion fun i => i.2.countable
  have hA : ({y : 𝕄.M | SP.acl (SP.singleVF a ha) y} : Set 𝕄.M).Countable := hU.mono hsub
  rw [Sat.MonsterModel.Small]
  exact lt_of_le_of_lt (Cardinal.mk_le_aleph0_iff.mpr hA.to_subtype) hκ

/-- **`alg:ind:imag` with the smallness of `acl(a)` derived** rather than assumed: the only
metamathematical inputs left are the countability of the formula set and `κ > ℵ₀`. -/
theorem alg_ind_imag_of_countable {𝕄 : Sat.MonsterACVF} (hex : ExchangeVF 𝕄) (a t : 𝕄.M)
    (ha : iVF a) (ht : iRV t) (hκ : Cardinal.aleph0 < 𝕄.κ)
    (hcnt : Countable (LRV.BoundedFormula (Fin 1 ⊕ Fin 0) 1))
    (hfib : ¬ 𝕄.Small ↥{x : 𝕄.M | iVF x ∧ iRv x = t})
    (h : ¬ SP.acl (SP.base (M := 𝕄.M)) a) :
    ¬ SP.acl (SP.singleRV t ht) a :=
  alg_ind_imag hex a t ha ht hfib (acl_small_of_countable hκ hcnt a ha) h

end M5

end Milestone0
end SpecialTransformations

/-! ## Verification of the axioms used -/

#print axioms SpecialTransformations.Milestone0.M5.realize_substFormula
#print axioms SpecialTransformations.Milestone0.M5.tmSort_substTerm
#print axioms SpecialTransformations.Milestone0.M5.wellSorted_substFormula
#print axioms SpecialTransformations.Milestone0.M5.acl_of_rv_eq
#print axioms SpecialTransformations.Milestone0.M5.fibre_subset_acl
#print axioms SpecialTransformations.Milestone0.M5.alg_ind_imag
#print axioms SpecialTransformations.Milestone0.M5.infinite_of_not_small
#print axioms SpecialTransformations.Milestone0.M5.acl_small_of_countable
#print axioms SpecialTransformations.Milestone0.M5.alg_ind_imag_of_countable
