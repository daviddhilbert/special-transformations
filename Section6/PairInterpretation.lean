module

public import Mathlib.ModelTheory.Definability

@[expose] public section

/-! A finite-product interpretation compiler in the pinned first-order
syntax. A source element is represented by two auxiliary coordinates.
Only atomic equality, function graphs and relation graphs are supplied;
the compiler proves closure under terms and all first-order quantifiers.
This is not an elimination hypothesis. The intended Denef–Pas instance
uses residue/value codes, with the value coordinate ignored at zero.
-/

noncomputable section
open Classical FirstOrder FirstOrder.Language

namespace SpecialTransformations.Section6.PairInterpretation

variable {L A : Language} {Q D I : Type} [L.Structure Q] [A.Structure D]

abbrev Coord := Fin 2

def decode (code : (Coord → D) → Q) (v : (I × Coord) → D) : I → Q :=
  fun i => code (fun b => v (i, b))

def termGraph (code : (Coord → D) → Q) (t : L.Term I) : Set (((I × Coord) ⊕ Coord) → D) :=
  {v | code (v ∘ Sum.inr) = t.realize (decode code (v ∘ Sum.inl))}

structure Data (L A : Language) (Q D : Type) [L.Structure Q] [A.Structure D] where
  code : (Coord → D) → Q
  onto : Function.Surjective code
  equality : (∅ : Set D).Definable A
    {v : (Coord ⊕ Coord) → D | code (v ∘ Sum.inl) = code (v ∘ Sum.inr)}
  functionGraph : ∀ {k} (f : L.Functions k), (∅ : Set D).Definable A
    {v : ((Fin k × Coord) ⊕ Coord) → D |
      code (v ∘ Sum.inr) = Structure.funMap f (decode code (v ∘ Sum.inl))}
  relationGraph : ∀ {k} (r : L.Relations k), (∅ : Set D).Definable A
    {v : (Fin k × Coord) → D | Structure.RelMap r (decode code v)}

variable (p : Data L A Q D)

private theorem finite_conjunction {J V : Type} [Finite J]
    (P : J → (V → D) → Prop)
    (h : ∀ j, (∅ : Set D).Definable A {v | P j v}) :
    (∅ : Set D).Definable A {v | ∀ j, P j v} := by
  simpa only [Set.ofPred_forall] using Set.definable_iInter_of_finite h

theorem term_graph_definable (t : L.Term I) :
    (∅ : Set D).Definable A (termGraph p.code t) := by
  induction t with
  | var i =>
    exact p.equality.preimage_comp (Sum.elim Sum.inr (fun b => Sum.inl (i, b)))
  | @func k f ts ih =>
    let V := ((I × Coord) ⊕ Coord) ⊕ (Fin k × Coord)
    let child (i : Fin k) : ((I × Coord) ⊕ Coord) → V :=
      Sum.elim (Sum.inl ∘ Sum.inl) (fun b => .inr (i, b))
    let output : ((Fin k × Coord) ⊕ Coord) → V :=
      Sum.elim Sum.inr (Sum.inl ∘ Sum.inr)
    have hc := finite_conjunction (A := A)
      (fun i v => v ∘ child i ∈ termGraph p.code (ts i))
      (fun i => (ih i).preimage_comp (child i))
    have hf := p.functionGraph f |>.preimage_comp output
    have h := (hc.inter hf).exists_of_finite
    convert h using 1
    ext v
    change p.code (v ∘ Sum.inr) = (Term.func f ts).realize (decode p.code (v ∘ Sum.inl)) ↔
      ∃ u : (Fin k × Coord) → D,
        (∀ i, Sum.elim v u ∘ child i ∈ termGraph p.code (ts i)) ∧
          Sum.elim v u ∘ output ∈
            {w | p.code (w ∘ Sum.inr) = Structure.funMap f (decode p.code (w ∘ Sum.inl))}
    have hchild (u : (Fin k × Coord) → D) (i : Fin k) :
        Sum.elim v u ∘ child i ∈ termGraph p.code (ts i) ↔
          p.code (fun b => u (i, b)) = (ts i).realize (decode p.code (v ∘ Sum.inl)) := Iff.rfl
    have houtput (u : (Fin k × Coord) → D) :
        Sum.elim v u ∘ output ∈
          {w | p.code (w ∘ Sum.inr) = Structure.funMap f (decode p.code (w ∘ Sum.inl))} ↔
          p.code (v ∘ Sum.inr) = Structure.funMap f (decode p.code u) := Iff.rfl
    simp only [hchild, houtput, Term.realize]
    constructor
    · intro hv
      choose u hu using fun i => p.onto ((ts i).realize (decode p.code (v ∘ Sum.inl)))
      refine ⟨fun b => u b.1 b.2, hu, ?_⟩
      have he : decode p.code (fun b => u b.1 b.2) =
          (fun i => (ts i).realize (decode p.code (v ∘ Sum.inl))) := funext hu
      simpa only [he] using hv
    · rintro ⟨u, hu, hv⟩
      have he : decode p.code u =
          (fun i => (ts i).realize (decode p.code (v ∘ Sum.inl))) := funext hu
      simpa only [he] using hv

/-- Substitution of source terms into any interpreted finite relation. -/
theorem relation_of_terms {k : ℕ} (P : (Fin k → Q) → Prop)
    (hP : (∅ : Set D).Definable A {v : (Fin k × Coord) → D | P (decode p.code v)})
    (ts : Fin k → L.Term I) :
    (∅ : Set D).Definable A
      {v : (I × Coord) → D | P (fun i => (ts i).realize (decode p.code v))} := by
  let child (i : Fin k) : ((I × Coord) ⊕ Coord) → (I × Coord) ⊕ (Fin k × Coord) :=
    Sum.elim Sum.inl (fun b => .inr (i, b))
  have hc := finite_conjunction (A := A)
    (fun i v => v ∘ child i ∈ termGraph p.code (ts i))
    (fun i => (term_graph_definable p (ts i)).preimage_comp (child i))
  have hp := hP.preimage_comp (Sum.inr : (Fin k × Coord) → (I × Coord) ⊕ (Fin k × Coord))
  have h := (hc.inter hp).exists_of_finite
  convert h using 1
  ext v
  change P (fun i => (ts i).realize (decode p.code v)) ↔
    ∃ u : (Fin k × Coord) → D,
      (∀ i, Sum.elim v u ∘ child i ∈ termGraph p.code (ts i)) ∧ P (decode p.code u)
  change _ ↔ ∃ u : (Fin k × Coord) → D,
    (∀ i, p.code (fun b => u (i, b)) = (ts i).realize (decode p.code v)) ∧ P (decode p.code u)
  constructor
  · intro hv
    choose u hu using fun i => p.onto ((ts i).realize (decode p.code v))
    have he : decode p.code (fun b => u b.1 b.2) =
        (fun i => (ts i).realize (decode p.code v)) := funext hu
    exact ⟨fun b => u b.1 b.2, hu, by simpa only [he] using hv⟩
  · rintro ⟨u, hu, hv⟩
    have he : decode p.code u = (fun i => (ts i).realize (decode p.code v)) := funext hu
    simpa only [he] using hv

def formulaSet {α : Type} {n : ℕ} (φ : L.BoundedFormula α n) :
    Set (((α ⊕ Fin n) × Coord) → D) :=
  {v | φ.Realize (decode p.code v ∘ Sum.inl) (decode p.code v ∘ Sum.inr)}

def splitLast {α : Type} {n : ℕ} :
    ((α ⊕ Fin (n + 1)) × Coord) → (((α ⊕ Fin n) × Coord) ⊕ Coord)
  | (.inl a, b) => .inl (.inl a, b)
  | (.inr i, b) => Fin.lastCases (.inr b) (fun j => .inl (.inr j, b)) i

theorem formula_set_definable {α : Type} {n : ℕ} (φ : L.BoundedFormula α n) :
    (∅ : Set D).Definable A (formulaSet p φ) := by
  induction φ with
  | falsum => exact Set.definable_empty
  | equal t u =>
    have he : (∅ : Set D).Definable A
        {v : (Fin 2 × Coord) → D | decode p.code v 0 = decode p.code v 1} :=
      p.equality.preimage_comp (Sum.elim (fun b => (0, b)) (fun b => (1, b)))
    simpa only [formulaSet, BoundedFormula.Realize, Sum.elim_comp_inl_inr,
      Matrix.cons_val_zero, Matrix.cons_val_one] using
      relation_of_terms p (fun z => z 0 = z 1) he ![t, u]
  | rel r ts =>
    simpa only [formulaSet, BoundedFormula.Realize, Sum.elim_comp_inl_inr] using
      relation_of_terms p (Structure.RelMap r) (p.relationGraph r) ts
  | imp φ ψ ihφ ihψ =>
    convert ihφ.himp ihψ using 1
    ext v
    simp only [formulaSet, Set.mem_setOf_eq, BoundedFormula.realize_imp,
      Set.mem_himp_iff]
  | @all n φ ih =>
    have h := (ih.preimage_comp (splitLast (α := α) (n := n))).forall_of_finite
    convert h using 1
    ext v
    change (∀ q : Q, φ.Realize (decode p.code v ∘ Sum.inl)
        (Fin.snoc (decode p.code v ∘ Sum.inr) q)) ↔
      ∀ u : Coord → D, φ.Realize
        (decode p.code (Sum.elim v u ∘ splitLast) ∘ Sum.inl)
        (decode p.code (Sum.elim v u ∘ splitLast) ∘ Sum.inr)
    have hx (u : Coord → D) :
        decode p.code (Sum.elim v u ∘ splitLast) ∘ Sum.inr =
          Fin.snoc (decode p.code v ∘ Sum.inr) (p.code u) := by
      funext i
      cases i using Fin.lastCases <;> simp [decode, splitLast, Function.comp_def]
    simp only [hx]
    constructor
    · exact fun h u => h (p.code u)
    · intro h q
      obtain ⟨u, rfl⟩ := p.onto q
      exact h u

/-- Every actual source formula has an actual auxiliary formula on its
pair codes. There are no field witnesses in this translation. -/
theorem exists_formula {α : Type} (φ : L.Formula α) :
    ∃ ψ : A.Formula (α × Coord),
      ∀ v : (α × Coord) → D, ψ.Realize v ↔ φ.Realize (decode p.code v) := by
  let project : ((α ⊕ Fin 0) × Coord) → (α × Coord)
    | (.inl a, b) => (a, b)
    | (.inr i, _) => i.elim0
  have h := (formula_set_definable p φ).preimage_comp project
  obtain ⟨θ, hθ⟩ := Set.definable_iff_exists_formula_sum.mp h
  let removeEmpty : (∅ : Set D) ⊕ (α × Coord) → α × Coord :=
    Sum.elim (fun a => False.elim a.property) id
  refine ⟨θ.relabel removeEmpty, ?_⟩
  intro v
  have he : v ∘ removeEmpty = Sum.elim (Subtype.val : (∅ : Set D) → D) v := by
    funext j
    cases j with
    | inl a => exact False.elim a.property
    | inr a => rfl
  rw [Formula.realize_relabel, he]
  have hv := Set.ext_iff.mp hθ v
  have h0 : decode p.code (v ∘ project) ∘ Sum.inr = (default : Fin 0 → Q) := by
    funext i
    exact i.elim0
  have hfree : decode p.code (v ∘ project) ∘ Sum.inl = decode p.code v := rfl
  change BoundedFormula.Realize φ (decode p.code (v ∘ project) ∘ Sum.inl)
    (decode p.code (v ∘ project) ∘ Sum.inr) ↔ θ.Realize (Sum.elim Subtype.val v) at hv
  rw [h0, hfree] at hv
  exact hv.symm

end SpecialTransformations.Section6.PairInterpretation
