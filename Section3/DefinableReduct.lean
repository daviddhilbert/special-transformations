module

public import Mathlib

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open FirstOrder FirstOrder.Language
namespace SpecialTransformations.ModelTheory
variable {M : Type} {L : Language}

/-- Uniform parameter-free definability of the symbols of another structure
on the same carrier. This is a first-order definable reduct condition. -/
structure DefinableReduct (sM tM : L.Structure M) : Prop where
  functions : ∀ {k : ℕ} (f : L.Functions k),
    @Set.DefinableFun M L sM (Fin k) (∅ : Set M) (@Structure.funMap L M tM k f)
  relations : ∀ {k : ℕ} (r : L.Relations k),
    @Set.Definable M (∅ : Set M) L sM (Fin k) {x | @Structure.RelMap L M tM k r x}

variable {sM tM : L.Structure M}

theorem DefinableReduct.term (h : DefinableReduct sM tM) (S : Set M) {α β : Type}
    (w : (β → M) → α → M) (hw : ∀ i, @Set.DefinableFun M L sM β S (fun z => w z i))
    (t : L.Term α) : @Set.DefinableFun M L sM β S (fun z => @Term.realize L M tM α (w z) t) := by
  letI := sM
  induction t with
  | var i => exact hw i
  | func f ts ih => exact (h.functions f).of_empty.comp ih

theorem DefinableReduct.formula (h : DefinableReduct sM tM) (S : Set M) {α β : Type}
    [Finite β] {n : ℕ} (φ : L.BoundedFormula α n)
    (u : (β → M) → α → M) (x : (β → M) → Fin n → M)
    (hu : ∀ i, @Set.DefinableFun M L sM β S (fun z => u z i))
    (hx : ∀ i, @Set.DefinableFun M L sM β S (fun z => x z i)) :
    @Set.Definable M S L sM β {z | @BoundedFormula.Realize L M tM α n φ (u z) (x z)} := by
  letI := sM
  induction φ generalizing β with
  | falsum => exact Set.definable_empty
  | @equal n a b =>
    have hm (i : α ⊕ Fin n) : S.DefinableFun L
        (fun z => Sum.elim (u z) (x z) i) := by
      cases i with
      | inl i => exact hu i
      | inr i => exact hx i
    exact (h.term S _ hm a).ofPred_eq (h.term S _ hm b)
  | @rel n k r ts =>
    have hm (i : α ⊕ Fin n) : S.DefinableFun L
        (fun z => Sum.elim (u z) (x z) i) := by
      cases i with
      | inl i => exact hu i
      | inr i => exact hx i
    exact ((h.relations r).mono (Set.empty_subset S)).preimage_map
      (fun i => h.term S _ hm (ts i))
  | imp φ ψ ihφ ihψ => exact (ihφ u x hu hx).himp (ihψ u x hu hx)
  | @all n φ ih =>
    let U (z : β ⊕ Fin 1 → M) : α → M := u (z ∘ Sum.inl)
    let X (z : β ⊕ Fin 1 → M) : Fin (n + 1) → M := Fin.snoc (x (z ∘ Sum.inl)) (z (.inr 0))
    have hproj : S.DefinableMap L (fun z : β ⊕ Fin 1 → M => z ∘ Sum.inl) :=
      fun _ => Set.DefinableFun.proj L
    have hU (i : α) : S.DefinableFun L (fun z => U z i) := (hu i).comp hproj
    have hX (i : Fin (n + 1)) : S.DefinableFun L (fun z => X z i) := by
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [X, Fin.snoc_last] using
          (Set.DefinableFun.proj (L := L) (A := S) (i := Sum.inr (0 : Fin 1)))
      · simpa only [X, Fin.snoc_castSucc] using (hx j).comp hproj
    have hb := ih U X hU hX
    have hall := hb.forall_of_finite
    change S.Definable L {z : β → M | ∀ a : M,
      @BoundedFormula.Realize L M tM α (n + 1) φ (u z) (Fin.snoc (x z) a)}
    convert hall using 1
    ext z
    change (∀ a : M, @BoundedFormula.Realize L M tM α (n + 1) φ (u z)
      (Fin.snoc (x z) a)) ↔ ∀ a : Fin 1 → M,
      @BoundedFormula.Realize L M tM α (n + 1) φ (u z) (Fin.snoc (x z) (a 0))
    exact ⟨fun hz a => hz (a 0), fun hz a => hz ![a]⟩

theorem DefinableReduct.definable (h : DefinableReduct sM tM) (S : Set M) {n : ℕ}
    (s : Set (Fin n → M)) (hs : @Set.Definable M S L tM (Fin n) s) : @Set.Definable M S L sM (Fin n) s := by
  letI := sM
  obtain ⟨φ, hφ⟩ : ∃ φ : L.Formula (S ⊕ Fin n),
      s = {x | @Formula.Realize L M tM (S ⊕ Fin n) φ (Sum.elim Subtype.val x)} := by
    letI := tM
    exact Set.definable_iff_exists_formula_sum.mp hs
  have hu (i : S ⊕ Fin n) : S.DefinableFun L
      (fun z : Fin n → M => Sum.elim Subtype.val z i) := by
    cases i with
    | inl i => exact L.definableFun_const (Fin n) i.property
    | inr i => exact Set.DefinableFun.proj L
  have hf := h.formula S φ (fun z => Sum.elim Subtype.val z)
    (fun _ => Fin.elim0) hu (fun i => i.elim0)
  rw [hφ]
  exact hf

end SpecialTransformations.ModelTheory
