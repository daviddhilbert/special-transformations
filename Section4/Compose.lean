/-
**Composition of `Sec4Dim.DefinableFun`** — the wall that blocked six items across §4, §7, §8, §9,
§10 of the project.

`Sec4Dim.DefinableFun S A f` says: the graph of `f` on `A` is cut out by a well-sorted `L_RV`
formula over the parameters `S`.  This file proves that it is closed under composition:

  `DefinableFun S A g → DefinableFun S B h → DefinableFun S (A ∩ g ⁻¹' B) (h ∘ g)`,

and, as the same job, that `Sec4Dim.Definable` is closed under projection along a coordinate.

Why it is not immediate: `WellSorted` admits no unguarded quantifier (`Milestone0/Encoding.lean`),
so the intermediate tuple of the composite has to be existentially quantified *guarded*
(`exSortedG`), one coordinate at a time.  The ingredients are

* `QE/SubstVar.lean` — `BoundedFormula.substVar` with `wellSorted_substVar` (a free variable may be
  replaced by a term, which `WellSorted` preserves) and `realize_substVar`;
* `QE/ExSortedG.lean` — `exSortedG_realize`, the semantics of the guarded existential.

The new ingredient here is the **iteration**: `exsG N K s ψ` quantifies the last `K` free variables
of `ψ : BoundedFormula α (N + K)`, each restricted to its sort `s`,

  `exsG_realize : (exsG N K s ψ).Realize v xs ↔
     ∃ a : Fin K → M, (∀ i, sortEval (s i) (a i)) ∧ ψ.Realize v (Fin.append xs a)`,

with `wellSorted_exsG` transporting well-sortedness.  `Fin.append` (not `Fin.snoc`) is the right
bookkeeping: `Fin.append_snoc` is exactly one step of the iteration.

No `sorry`, no `axiom`, no `native_decide`.
-/
import SubstVar
import ExSortedG

set_option linter.unusedVariables false
open FirstOrder FirstOrder.Language

namespace SpecialTransformations.Milestone0
open LRV

namespace Sec4FunComp

open Sec4Dim Sec4Compose

variable {M : Type} [LRV.Structure M]

/-! ## Flat assignments: `Tup M n m` against `Fin (n + m) → M` -/

/-- The assignment `Fin (n + m) → M` attached to a tuple `VF^n × RV^m`.  This is the shape in which
`BoundedFormula.Realize` wants the free variables. -/
def tupAssign {n m : ℕ} (x : Tup M n m) : Fin (n + m) → M :=
  fun t => x (finSumFinEquiv.symm t)

/-- `pairAssign` is the concatenation of the two flat assignments: this is what makes `Fin.append`
the right bookkeeping for the intermediate tuple of a composite. -/
theorem pairAssign_eq_append {n m k l : ℕ} (x : Tup M n m) (y : Tup M k l) :
    pairAssign x y = Fin.append (tupAssign x) (tupAssign y) := rfl

/-- The tuple `VF^k × RV^l` attached to a flat assignment that respects the sorts. -/
def tupOf {k l : ℕ} (a : Fin (k + l) → M) (h : ∀ t, sortEval (fSort k l t) (a t)) :
    Tup M k l :=
  ⟨fun i => a (finSumFinEquiv i), fun i => by
    have h' := h (finSumFinEquiv i)
    simpa [fSort] using h'⟩

@[simp]
theorem tupAssign_tupOf {k l : ℕ} (a : Fin (k + l) → M)
    (h : ∀ t, sortEval (fSort k l t) (a t)) : tupAssign (tupOf a h) = a := by
  funext t
  show a (finSumFinEquiv (finSumFinEquiv.symm t)) = a t
  rw [Equiv.apply_symm_apply]

/-- `Fin.append` with an empty right block is the identity.  (`Fin.append_elim0` states this modulo
a `Fin.cast`; here the types are definitionally equal, so a plain equation is what is needed.) -/
theorem fin_append_zero {N : ℕ} {β : Type*} (xs : Fin N → β) (a : Fin 0 → β) :
    Fin.append xs a = xs := by
  have h0 : a = Fin.elim0 := funext (fun i => i.elim0)
  subst h0
  simp

/-! ## Iterating the guarded existential -/

/-- `exsG N K s ψ` is `ψ` with its last `K` free variables existentially quantified, the `i`-th one
restricted to the sort `s i`.  `ψ` has context `Fin (N + K)`; the result has context `Fin N`. -/
def exsG {α : Type} (N : ℕ) : (K : ℕ) → (Fin K → SortTag) →
    LRV.BoundedFormula α (N + K) → LRV.BoundedFormula α N
  | 0, _, ψ => ψ
  | (K + 1), s, ψ =>
      exsG N K (fun i => s (Fin.castSucc i)) (exSortedG (s (Fin.last K)) ψ)

/-- **The realization of `exsG`**: a guarded existential for each of the last `K` variables, read
with `Fin.append` on the remaining assignment. -/
theorem exsG_realize {α : Type} {N : ℕ} :
    (K : ℕ) → (s : Fin K → SortTag) → (ψ : LRV.BoundedFormula α (N + K)) →
      ∀ (v : α → M) (xs : Fin N → M),
        (exsG N K s ψ).Realize v xs ↔
          ∃ a : Fin K → M, (∀ i, sortEval (s i) (a i)) ∧ ψ.Realize v (Fin.append xs a)
  | 0, s, ψ, v, xs => by
    rw [exsG.eq_1]
    constructor
    · intro h
      exact ⟨Fin.elim0, fun i => i.elim0, by simpa [fin_append_zero] using h⟩
    · rintro ⟨a, -, h⟩
      simpa [fin_append_zero] using h
  | (K + 1), s, ψ, v, xs => by
    have hstep := exsG_realize (N := N) K (fun i => s (Fin.castSucc i))
      (exSortedG (s (Fin.last K)) ψ) v xs
    show (exsG N K (fun i => s (Fin.castSucc i)) (exSortedG (s (Fin.last K)) ψ)).Realize v xs ↔ _
    rw [hstep]
    constructor
    · rintro ⟨a', ha', hb⟩
      rw [exSortedG_realize] at hb
      obtain ⟨b, hb1, hb2⟩ := hb
      refine ⟨Fin.snoc a' b, ?_, ?_⟩
      · intro i
        refine Fin.lastCases ?_ ?_ i
        · rwa [Fin.snoc_last]
        · intro j
          rw [Fin.snoc_castSucc]
          exact ha' j
      · rwa [Fin.append_snoc]
    · rintro ⟨a, ha, hψ⟩
      refine ⟨Fin.init a, ?_, ?_⟩
      · intro j
        simpa [Fin.init] using ha (Fin.castSucc j)
      · rw [exSortedG_realize]
        exact ⟨a (Fin.last K), ha (Fin.last K), by rwa [← Fin.append_snoc, Fin.snoc_init_self]⟩

/-- **Well-sortedness survives the iteration.** -/
theorem wellSorted_exsG {α : Type} (sα : α → SortTag) {N : ℕ} :
    (K : ℕ) → (s : Fin K → SortTag) → (ss : Fin N → SortTag) →
      ∀ {ψ : LRV.BoundedFormula α (N + K)},
        WellSorted sα (Fin.append ss s) ψ → WellSorted sα ss (exsG N K s ψ)
  | 0, s, ss, ψ, h => by
    rw [fin_append_zero] at h
    exact h
  | (K + 1), s, ss, ψ, h => by
    have hs : Fin.append ss s =
        Fin.snoc (Fin.append ss (fun i => s (Fin.castSucc i))) (s (Fin.last K)) := by
      conv_lhs => rw [show s = Fin.snoc (fun i => s (Fin.castSucc i)) (s (Fin.last K)) from
        (Fin.snoc_init_self s).symm]
      rw [Fin.append_snoc]
    have h' : WellSorted sα
        (Fin.snoc (Fin.append ss (fun i => s (Fin.castSucc i))) (s (Fin.last K))) ψ := by
      rw [← hs]; exact h
    exact wellSorted_exsG sα K (fun i => s (Fin.castSucc i)) ss (wellSorted_exSortedG sα h')

/-! ## The substitution that moves the intermediate tuple to the end of the context

For a composite `h ∘ g`, the middle tuple has to be quantified.  The context of the composite
formula is `x` (the input block, `n + m` variables), `y` (the output block, `p + q`), then `z` (the
intermediate tuple, `k + l`); `sigG` and `sigH` relabel the two graph formulas into that context,
leaving the intermediate block last so that `exsG` can quantify it. -/

/-- The relabelling of the free variables of `g`'s graph formula into the context `x, y, z`:
`x` stays at the front, the intermediate block `z` moves to the end. -/
def sigG {α : Type} (n m k l p q : ℕ) :
    Fin ((n + m) + (k + l)) → LRV.Term (α ⊕ Fin (((n + m) + (p + q)) + (k + l))) :=
  Fin.addCases
    (fun i => Term.var (Sum.inr (Fin.castAdd (k + l) (Fin.castAdd (p + q) i))))
    (fun t => Term.var (Sum.inr (Fin.natAdd ((n + m) + (p + q)) t)))

/-- The relabelling of the free variables of `h`'s graph formula into the context `x, y, z`:
the intermediate block `z` goes to the end, the output block `y` stays in the middle. -/
def sigH {α : Type} (n m k l p q : ℕ) :
    Fin ((k + l) + (p + q)) → LRV.Term (α ⊕ Fin (((n + m) + (p + q)) + (k + l))) :=
  Fin.addCases
    (fun t => Term.var (Sum.inr (Fin.natAdd ((n + m) + (p + q)) t)))
    (fun j => Term.var (Sum.inr (Fin.castAdd (k + l) (Fin.natAdd (n + m) j))))

/-- **The composition's graph formula**: `g`'s graph and `h`'s graph, relabelled onto the context
`x, y, z`, with the intermediate tuple `z` quantified guarded. -/
def compForm {α : Type} (n m k l p q : ℕ)
    (φg : LRV.BoundedFormula α ((n + m) + (k + l)))
    (φh : LRV.BoundedFormula α ((k + l) + (p + q))) :
    LRV.BoundedFormula α ((n + m) + (p + q)) :=
  exsG ((n + m) + (p + q)) (k + l) (fSort k l)
    (BoundedFormula.substVar (sigG n m k l p q) φg ⊓
      BoundedFormula.substVar (sigH n m k l p q) φh)

theorem tmSort_sigG {α : Type} (sα : α → SortTag) (n m k l p q : ℕ) :
    ∀ i, TmSort sα (Fin.append (Fin.append (fSort n m) (fSort p q)) (fSort k l))
        (sigG (α := α) n m k l p q i) =
      some ((Fin.append (fSort n m) (fSort k l)) i) := by
  intro i
  refine Fin.addCases (fun i₀ => ?_) (fun t => ?_) i
  · simp only [sigG, Fin.addCases_left, tmSort_var_inr, Fin.append_left]
  · simp only [sigG, Fin.addCases_right, tmSort_var_inr, Fin.append_right]

theorem tmSort_sigH {α : Type} (sα : α → SortTag) (n m k l p q : ℕ) :
    ∀ j, TmSort sα (Fin.append (Fin.append (fSort n m) (fSort p q)) (fSort k l))
        (sigH (α := α) n m k l p q j) =
      some ((Fin.append (fSort k l) (fSort p q)) j) := by
  intro j
  refine Fin.addCases (fun t => ?_) (fun j₀ => ?_) j
  · simp only [sigH, Fin.addCases_left, tmSort_var_inr, Fin.append_right, Fin.append_left]
  · simp only [sigH, Fin.addCases_right, tmSort_var_inr, Fin.append_left, Fin.append_right]

/-- **The composition's graph formula is well-sorted.** -/
theorem wellSorted_compForm (S : SP M) {n m k l p q : ℕ}
    {φg : LRV.BoundedFormula (Fin S.n ⊕ Fin S.m) ((n + m) + (k + l))}
    {φh : LRV.BoundedFormula (Fin S.n ⊕ Fin S.m) ((k + l) + (p + q))}
    (hg : WellSorted S.sortMap (Fin.append (fSort n m) (fSort k l)) φg)
    (hh : WellSorted S.sortMap (Fin.append (fSort k l) (fSort p q)) φh) :
    WellSorted S.sortMap (Fin.append (fSort n m) (fSort p q)) (compForm n m k l p q φg φh) :=
  wellSorted_exsG S.sortMap (k + l) (fSort k l) (Fin.append (fSort n m) (fSort p q))
    (wellSorted_inf S.sortMap _
      (wellSorted_substVar S.sortMap hg (tmSort_sigG S.sortMap n m k l p q))
      (wellSorted_substVar S.sortMap hh (tmSort_sigH S.sortMap n m k l p q)))

/-! ## Reading a flat assignment at the three blocks -/

theorem pair_castAdd {n m k l : ℕ} {x : Tup M n m} {z : Tup M k l} (i₀ : Fin (n + m)) :
    pairAssign x z (Fin.castAdd (k + l) i₀) = tupAssign x i₀ := by
  show Fin.append (tupAssign x) (tupAssign z) (Fin.castAdd (k + l) i₀) = tupAssign x i₀
  rw [Fin.append_left]

theorem pair_natAdd {n m k l : ℕ} {x : Tup M n m} {z : Tup M k l} (t : Fin (k + l)) :
    pairAssign x z (Fin.natAdd (n + m) t) = tupAssign z t := by
  show Fin.append (tupAssign x) (tupAssign z) (Fin.natAdd (n + m) t) = tupAssign z t
  rw [Fin.append_right]

theorem append_pair_castAdd_castAdd {n m k l p q : ℕ} {x : Tup M n m} {y : Tup M p q}
    {a : Fin (k + l) → M} (i₀ : Fin (n + m)) :
    Fin.append (pairAssign x y) a (Fin.castAdd (k + l) (Fin.castAdd (p + q) i₀)) =
      tupAssign x i₀ := by
  rw [Fin.append_left]
  exact pair_castAdd i₀

theorem append_pair_castAdd_natAdd {n m k l p q : ℕ} {x : Tup M n m} {y : Tup M p q}
    {a : Fin (k + l) → M} (j : Fin (p + q)) :
    Fin.append (pairAssign x y) a (Fin.castAdd (k + l) (Fin.natAdd (n + m) j)) =
      tupAssign y j := by
  rw [Fin.append_left]
  exact pair_natAdd j

theorem append_pair_natAdd {n m k l p q : ℕ} {x : Tup M n m} {y : Tup M p q}
    {a : Fin (k + l) → M} (t : Fin (k + l)) :
    Fin.append (pairAssign x y) a (Fin.natAdd ((n + m) + (p + q)) t) = a t := by
  exact Fin.append_right _ _ t

theorem tupOf_tupAssign {k l : ℕ} (z : Tup M k l)
    (h : ∀ t, sortEval (fSort k l t) (tupAssign z t)) : tupOf (tupAssign z) h = z := by
  apply Subtype.ext
  funext i
  show tupAssign z (finSumFinEquiv i) = z i
  rw [tupAssign, Equiv.symm_apply_apply]

/-! ## The realization of the composition's graph formula -/

/-- **The realization of the composition's graph formula**: at a point `x` of the domain whose value
lies in `B`, the composite reads `h (g x) = y`. -/
theorem compForm_realize (S : SP M) {n m k l p q : ℕ}
    {φg : LRV.BoundedFormula (Fin S.n ⊕ Fin S.m) ((n + m) + (k + l))}
    {φh : LRV.BoundedFormula (Fin S.n ⊕ Fin S.m) ((k + l) + (p + q))}
    {A : Set (Tup M n m)} {B : Set (Tup M k l)}
    {g : Tup M n m → Tup M k l} {h : Tup M k l → Tup M p q}
    (hφg : ∀ x, x ∈ A → ∀ y, (φg.Realize S.toFun (pairAssign x y) ↔ g x = y))
    (hφh : ∀ z, z ∈ B → ∀ y, (φh.Realize S.toFun (pairAssign z y) ↔ h z = y))
    {x : Tup M n m} (hx : x ∈ A) (hxB : g x ∈ B) (y : Tup M p q) :
    (compForm n m k l p q φg φh).Realize S.toFun (pairAssign x y) ↔ h (g x) = y := by
  have hsigG : ∀ (a : Fin (k + l) → M) (ha : ∀ i, sortEval (fSort k l i) (a i)),
      (fun i => Term.realize (Sum.elim S.toFun (Fin.append (pairAssign x y) a))
          (sigG n m k l p q i)) = pairAssign x (tupOf a ha) := by
    intro a ha
    funext i
    refine Fin.addCases (fun i₀ => ?_) (fun t => ?_) i
    · simp only [sigG, Fin.addCases_left, Term.realize_var, Sum.elim_inr,
        append_pair_castAdd_castAdd, pair_castAdd]
    · simp only [sigG, Fin.addCases_right, Term.realize_var, Sum.elim_inr,
        append_pair_natAdd, pair_natAdd, tupAssign_tupOf]
  have hsigH : ∀ (a : Fin (k + l) → M) (ha : ∀ i, sortEval (fSort k l i) (a i)),
      (fun j => Term.realize (Sum.elim S.toFun (Fin.append (pairAssign x y) a))
          (sigH n m k l p q j)) = pairAssign (tupOf a ha) y := by
    intro a ha
    funext j
    refine Fin.addCases (fun t => ?_) (fun j₀ => ?_) j
    · simp only [sigH, Fin.addCases_left, Term.realize_var, Sum.elim_inr,
        append_pair_natAdd, pair_castAdd, tupAssign_tupOf]
    · simp only [sigH, Fin.addCases_right, Term.realize_var, Sum.elim_inr,
        append_pair_castAdd_natAdd, pair_natAdd]
  rw [compForm, exsG_realize]
  constructor
  · rintro ⟨a, ha, hbody⟩
    rw [BoundedFormula.realize_inf, Sec4Compose.realize_substVar,
      Sec4Compose.realize_substVar, hsigG a ha, hsigH a ha] at hbody
    obtain ⟨h1, h2⟩ := hbody
    have hgz : g x = tupOf a ha := (hφg x hx (tupOf a ha)).1 h1
    have hzB : tupOf a ha ∈ B := hgz ▸ hxB
    rw [hgz]
    exact (hφh (tupOf a ha) hzB y).1 h2
  · intro hgy
    refine ⟨tupAssign (g x), fun i => (g x).2 (finSumFinEquiv.symm i), ?_⟩
    rw [BoundedFormula.realize_inf, Sec4Compose.realize_substVar,
      Sec4Compose.realize_substVar,
      hsigG (tupAssign (g x)) (fun i => (g x).2 (finSumFinEquiv.symm i)),
      hsigH (tupAssign (g x)) (fun i => (g x).2 (finSumFinEquiv.symm i))]
    have hz : tupOf (tupAssign (g x)) (fun i => (g x).2 (finSumFinEquiv.symm i)) = g x :=
      tupOf_tupAssign (g x) _
    rw [hz]
    exact ⟨(hφg x hx (g x)).2 rfl, (hφh (g x) hxB y).2 hgy⟩

/-- **Non-degeneracy of the composite formula**: at `g = h = id`, the composite formula is
`∃ z, (x = z) ∧ (z = y)`, which must compute the identity graph.  It does — so the guarded
existential does not collapse the formula, and `compForm_realize` is not an empty `↔`. -/
theorem compForm_idForm {S : SP M} {n m : ℕ} (x y : Tup M n m) :
    (compForm n m n m n m (idForm (Fin S.n ⊕ Fin S.m) n m) (idForm (Fin S.n ⊕ Fin S.m) n m)).Realize
        S.toFun (pairAssign x y) ↔ x = y := by
  have hg : ∀ a, a ∈ (Set.univ : Set (Tup M n m)) → ∀ b : Tup M n m,
      ((idForm (Fin S.n ⊕ Fin S.m) n m).Realize S.toFun (pairAssign a b) ↔ (id : Tup M n m → Tup M n m) a = b) :=
    fun a _ b => (realize_idForm M S.toFun a b).trans eq_comm
  exact compForm_realize (S := S) (A := Set.univ) (B := Set.univ) (g := id) (h := id) hg hg
    (Set.mem_univ x) (Set.mem_univ x) y

/-- **`DefinableFun` is closed under composition.**  If `g` is definable on `A` and `h` is definable
on `B`, then `h ∘ g` is definable on `A ∩ g ⁻¹' B`.

This is the wall: the graph of the composite needs the intermediate tuple existentially
quantified, and `WellSorted` admits only guarded quantifiers, so the elimination is the iteration
`exsG` of `exSortedG`. -/
theorem DefinableFun.comp {S : SP M} {n m k l p q : ℕ}
    {A : Set (Tup M n m)} {B : Set (Tup M k l)}
    {g : Tup M n m → Tup M k l} {h : Tup M k l → Tup M p q}
    (hg : DefinableFun S A g) (hh : DefinableFun S B h) :
    DefinableFun S (A ∩ (fun x => g x) ⁻¹' B) (fun x => h (g x)) := by
  obtain ⟨φg, hφgs, hφg⟩ := hg
  obtain ⟨φh, hφhs, hφh⟩ := hh
  exact ⟨compForm n m k l p q φg φh, wellSorted_compForm S hφgs hφhs,
    fun x hx y => compForm_realize S hφg hφh hx.1 hx.2 y⟩

/-- **Composition, with the domain kept as `B`**: if `g` is definable on `B`, `h` on `A`, and `g`
maps `B` into `A`, then `h ∘ g` is definable on `B`.  This is the form in which the tree's
`hcomp` hypotheses (`QE/Sec4Polydisc.lean`) are stated. -/
theorem DefinableFun.comp_of_mapsTo {S : SP M} {n m k l p q : ℕ}
    {A : Set (Tup M k l)} {B : Set (Tup M n m)}
    {g : Tup M n m → Tup M k l} {h : Tup M k l → Tup M p q}
    (hg : DefinableFun S B g) (hh : DefinableFun S A h) (hmaps : ∀ b ∈ B, g b ∈ A) :
    DefinableFun S B (fun b => h (g b)) := by
  have h := DefinableFun.comp hg hh
  have hdom : B ∩ (fun b => g b) ⁻¹' A = B :=
    Set.inter_eq_left.2 (fun b hb => hmaps b hb)
  rwa [hdom] at h

end Sec4FunComp

end SpecialTransformations.Milestone0

/-! ## Axiom audit -/

#print axioms SpecialTransformations.Milestone0.Sec4FunComp.exsG_realize
#print axioms SpecialTransformations.Milestone0.Sec4FunComp.wellSorted_exsG
#print axioms SpecialTransformations.Milestone0.Sec4FunComp.wellSorted_compForm
#print axioms SpecialTransformations.Milestone0.Sec4FunComp.compForm_realize
#print axioms SpecialTransformations.Milestone0.Sec4FunComp.compForm_idForm
#print axioms SpecialTransformations.Milestone0.Sec4FunComp.DefinableFun.comp
#print axioms SpecialTransformations.Milestone0.Sec4FunComp.DefinableFun.comp_of_mapsTo
