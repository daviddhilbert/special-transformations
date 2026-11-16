module

public import Section6.PairInterpretation
public import Section6.RVFormula

@[expose] public section

/-! Uniform two-coordinate interpretation syntax. Atomic formulas are
chosen before the structures. This strengthens the per-model definability
interface in PairInterpretation without assuming any formula translation.
-/

noncomputable section
open Classical FirstOrder FirstOrder.Language

namespace SpecialTransformations.Section6.PairSyntax

abbrev Coord := Fin 2

structure Syntax (L A : Language) where
  equality : A.Formula (Coord ⊕ Coord)
  functionGraph : ∀ {k}, L.Functions k → A.Formula ((Fin k × Coord) ⊕ Coord)
  relationGraph : ∀ {k}, L.Relations k → A.Formula (Fin k × Coord)

variable {L A : Language} {Q D I : Type} [L.Structure Q] [A.Structure D]

structure Realizes (p : Syntax L A) (Q D : Type) [L.Structure Q] [A.Structure D] where
  code : (Coord → D) → Q
  onto : Function.Surjective code
  equality : ∀ v, p.equality.Realize v ↔ code (v ∘ Sum.inl) = code (v ∘ Sum.inr)
  functionGraph : ∀ {k} (f : L.Functions k) v,
    (p.functionGraph f).Realize v ↔ code (v ∘ Sum.inr) =
      Structure.funMap f (PairInterpretation.decode code (v ∘ Sum.inl))
  relationGraph : ∀ {k} (r : L.Relations k) v,
    (p.relationGraph r).Realize v ↔
      Structure.RelMap r (PairInterpretation.decode code v)

def child {k : ℕ} (i : Fin k) : ((I × Coord) ⊕ Coord) →
    (((I × Coord) ⊕ Coord) ⊕ (Fin k × Coord)) :=
  Sum.elim (Sum.inl ∘ Sum.inl) (fun b => .inr (i, b))

def output {k : ℕ} : ((Fin k × Coord) ⊕ Coord) →
    (((I × Coord) ⊕ Coord) ⊕ (Fin k × Coord)) :=
  Sum.elim Sum.inr (Sum.inl ∘ Sum.inr)

def term (p : Syntax L A) : L.Term I → A.Formula ((I × Coord) ⊕ Coord)
  | .var i => p.equality.relabel (Sum.elim Sum.inr (fun b => .inl (i, b)))
  | @Term.func _ _ k f ts => Formula.iExs (Fin k × Coord)
      ((Formula.iInf fun i => (term p (ts i)).relabel (child i)) ⊓
        (p.functionGraph f).relabel output)

theorem term_realize (p : Syntax L A) (h : Realizes p Q D) (t : L.Term I)
    (v : ((I × Coord) ⊕ Coord) → D) :
    (term p t).Realize v ↔ h.code (v ∘ Sum.inr) =
      t.realize (PairInterpretation.decode h.code (v ∘ Sum.inl)) := by
  induction t generalizing v with
  | var i =>
    rw [term, Formula.realize_relabel, h.equality]
    rfl
  | @func k f ts ih =>
    simp only [term, Formula.realize_iExs, Formula.realize_inf,
      Formula.realize_iInf, Formula.realize_relabel, ih, h.functionGraph]
    have hc (u : (Fin k × Coord) → D) (i : Fin k) :
        h.code ((Sum.elim v u ∘ child i) ∘ Sum.inr) =
          (ts i).realize (PairInterpretation.decode h.code
            ((Sum.elim v u ∘ child i) ∘ Sum.inl)) ↔
        h.code (fun b => u (i, b)) =
          (ts i).realize (PairInterpretation.decode h.code (v ∘ Sum.inl)) := Iff.rfl
    have ho (u : (Fin k × Coord) → D) :
        h.code ((Sum.elim v u ∘ output) ∘ Sum.inr) =
          Structure.funMap f (PairInterpretation.decode h.code
            ((Sum.elim v u ∘ output) ∘ Sum.inl)) ↔
        h.code (v ∘ Sum.inr) = Structure.funMap f (PairInterpretation.decode h.code u) := Iff.rfl
    simp only [hc, ho, Term.realize]
    constructor
    · rintro ⟨u, hu, hf⟩
      have he : PairInterpretation.decode h.code u =
          (fun i => (ts i).realize (PairInterpretation.decode h.code (v ∘ Sum.inl))) :=
        funext hu
      simpa only [he] using hf
    · intro hv
      choose u hu using fun i => h.onto
        ((ts i).realize (PairInterpretation.decode h.code (v ∘ Sum.inl)))
      refine ⟨fun b => u b.1 b.2, hu, ?_⟩
      have he : PairInterpretation.decode h.code (fun b => u b.1 b.2) =
          (fun i => (ts i).realize (PairInterpretation.decode h.code (v ∘ Sum.inl))) :=
        funext hu
      simpa only [he] using hv

def argument {k : ℕ} (i : Fin k) : ((I × Coord) ⊕ Coord) →
    ((I × Coord) ⊕ (Fin k × Coord)) :=
  Sum.elim Sum.inl (fun b => .inr (i, b))

def applyRelation (p : Syntax L A) {k : ℕ} (ρ : A.Formula (Fin k × Coord))
    (ts : Fin k → L.Term I) : A.Formula (I × Coord) :=
  Formula.iExs (Fin k × Coord)
    ((Formula.iInf fun i => (term p (ts i)).relabel (argument i)) ⊓ ρ.relabel Sum.inr)

theorem applyRelation_realize (p : Syntax L A) (h : Realizes p Q D) {k : ℕ}
    (ρ : A.Formula (Fin k × Coord)) (P : (Fin k → Q) → Prop)
    (hρ : ∀ v, ρ.Realize v ↔ P (PairInterpretation.decode h.code v))
    (ts : Fin k → L.Term I) (v : (I × Coord) → D) :
    (applyRelation p ρ ts).Realize v ↔
      P (fun i => (ts i).realize (PairInterpretation.decode h.code v)) := by
  simp only [applyRelation, Formula.realize_iExs, Formula.realize_inf,
    Formula.realize_iInf, Formula.realize_relabel, term_realize p h, hρ]
  change (∃ u : (Fin k × Coord) → D,
    (∀ i, h.code (fun b => u (i, b)) =
      (ts i).realize (PairInterpretation.decode h.code v)) ∧
        P (PairInterpretation.decode h.code u)) ↔ _
  constructor
  · rintro ⟨u, hu, hv⟩
    have he : PairInterpretation.decode h.code u =
        (fun i => (ts i).realize (PairInterpretation.decode h.code v)) := funext hu
    simpa only [he] using hv
  · intro hv
    choose u hu using fun i => h.onto ((ts i).realize (PairInterpretation.decode h.code v))
    have he : PairInterpretation.decode h.code (fun b => u b.1 b.2) =
        (fun i => (ts i).realize (PairInterpretation.decode h.code v)) := funext hu
    exact ⟨fun b => u b.1 b.2, hu, by simpa only [he] using hv⟩

def equalityRelation (p : Syntax L A) : A.Formula (Fin 2 × Coord) :=
  p.equality.relabel (Sum.elim (fun b => (0, b)) (fun b => (1, b)))

def bounded (p : Syntax L A) {α : Type} :
    {n : ℕ} → L.BoundedFormula α n → A.Formula ((α ⊕ Fin n) × Coord)
  | _, .falsum => ⊥
  | _, .equal t u => applyRelation p (equalityRelation p) ![t, u]
  | _, .rel r ts => applyRelation p (p.relationGraph r) ts
  | _, .imp φ ψ => (bounded p φ).imp (bounded p ψ)
  | _, .all φ => Formula.iAlls Coord ((bounded p φ).relabel PairInterpretation.splitLast)

theorem bounded_realize (p : Syntax L A) (h : Realizes p Q D) {α : Type} {n : ℕ}
    (φ : L.BoundedFormula α n) (v : ((α ⊕ Fin n) × Coord) → D) :
    (bounded p φ).Realize v ↔
      φ.Realize (PairInterpretation.decode h.code v ∘ Sum.inl)
        (PairInterpretation.decode h.code v ∘ Sum.inr) := by
  induction φ with
  | falsum => rfl
  | equal t u =>
    have he (w : (Fin 2 × Coord) → D) :
        (equalityRelation p).Realize w ↔
          PairInterpretation.decode h.code w 0 = PairInterpretation.decode h.code w 1 := by
      rw [equalityRelation, Formula.realize_relabel, h.equality]
      rfl
    simpa only [bounded, BoundedFormula.Realize, Sum.elim_comp_inl_inr,
      Matrix.cons_val_zero, Matrix.cons_val_one] using
      applyRelation_realize p h (equalityRelation p) (fun z => z 0 = z 1) he ![t, u] v
  | rel r ts =>
    simpa only [bounded, BoundedFormula.Realize, Sum.elim_comp_inl_inr] using
      applyRelation_realize p h (p.relationGraph r) (Structure.RelMap r) (h.relationGraph r) ts v
  | imp φ ψ ihφ ihψ =>
    simp only [bounded, Formula.realize_imp, BoundedFormula.realize_imp, ihφ, ihψ]
  | @all n φ ih =>
    simp only [bounded, Formula.realize_iAlls, Formula.realize_relabel, ih,
      BoundedFormula.realize_all]
    have hx (u : Coord → D) :
        PairInterpretation.decode h.code (Sum.elim v u ∘ PairInterpretation.splitLast) ∘ Sum.inr =
          Fin.snoc (PairInterpretation.decode h.code v ∘ Sum.inr) (h.code u) := by
      funext i
      cases i using Fin.lastCases <;>
        simp [PairInterpretation.decode, PairInterpretation.splitLast, Function.comp_def]
    have hv (u : Coord → D) :
        PairInterpretation.decode h.code (Sum.elim v u ∘ PairInterpretation.splitLast) ∘ Sum.inl =
          PairInterpretation.decode h.code v ∘ Sum.inl := rfl
    simp only [hx, hv]
    constructor
    · intro hall q
      obtain ⟨u, rfl⟩ := h.onto q
      exact hall u
    · exact fun hall u => hall (h.code u)

def formula (p : Syntax L A) {α : Type} (φ : L.Formula α) : A.Formula (α × Coord) :=
  (bounded p φ).relabel (fun j => (j.1.elim id Fin.elim0, j.2))

/-- A single actual formula, determined entirely by the atomic dictionary,
works in every pair of structures realizing that dictionary. -/
theorem formula_realize (p : Syntax L A) (h : Realizes p Q D) {α : Type}
    (φ : L.Formula α) (v : (α × Coord) → D) :
    (formula p φ).Realize v ↔ φ.Realize (PairInterpretation.decode h.code v) := by
  rw [formula, Formula.realize_relabel, bounded_realize p h]
  change BoundedFormula.Realize φ (PairInterpretation.decode h.code v) _ ↔
    BoundedFormula.Realize φ (PairInterpretation.decode h.code v) default
  have h0 : PairInterpretation.decode h.code
      (v ∘ (fun j : (α ⊕ Fin 0) × Coord => (j.1.elim id Fin.elim0, j.2))) ∘ Sum.inr =
        (default : Fin 0 → Q) := Subsingleton.elim _ _
  rw [h0]

end SpecialTransformations.Section6.PairSyntax
