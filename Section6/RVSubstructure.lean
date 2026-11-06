import Section6.RVAbstraction
import Section6.SyntacticDescent

/-! Interpret the auxiliary language on the actual RV part of a
substructure. Extra RV structure is lifted only to that substructure,
not to the ACVF ambient model. This supplies the concrete compatibility
conditions used by formula_realize, without assuming elementary
preservation of RV quantifiers. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer

namespace SpecialTransformations.Section6.RVSubstructure
open RVAbstraction RVTermSupport

variable {C : Type} [LRV.Structure C] [hC : C ⊨ Axioms.ACVF]
variable {E : Language} (X : LRV.Substructure C)

def inclusion (q : SubRV (X : Set C)) : X := ⟨q.val.val, q.property⟩

theorem inclusion_injective : Function.Injective (inclusion X) := by
  intro a b he
  exact Subtype.ext (Subtype.ext (congrArg (fun t : X => t.val) he))

def zero : SubRV (X : Set C) :=
  ⟨⟨iRVZero, rv_zero_mem hC⟩,
    X.fun_mem Fn.rvZero Fin.elim0 (fun i => i.elim0)⟩

variable [E.Structure (SubRV (X : Set C))]

@[instance_reducible] def auxiliaryStructure : (Auxiliary E).Structure (SubRV (X : Set C)) where
  funMap {k} f z := match f with
    | .inr f => Structure.funMap (L := E) f z
    | .inl f =>
      ⟨⟨Structure.funMap (L := LRV) f.val (fun i => (z i).val.val), by
        have h := CanonicalStructure.function_sort hC f.val (fun i => (z i).val.val) (by
          intro i
          rw [f.property.2 i]
          exact (z i).val.property)
        simpa only [f.property.1, sortEval, iRV] using h⟩,
        X.fun_mem f.val _ (fun i => (z i).property)⟩
  RelMap {k} r z := match r with
    | .inr r => Structure.RelMap (L := E) r z
    | .inl r => Structure.RelMap (L := LRV) r.val (fun i => (z i).val.val)

@[instance_reducible] def extraStructure : E.Structure X where
  funMap {k} f z :=
    if h : ∀ i, iRV (z i).val then
      inclusion X (Structure.funMap (L := E) f (fun i => ⟨⟨(z i).val, h i⟩, (z i).property⟩))
    else inclusion X (zero X)
  RelMap {k} r z :=
    if h : ∀ i, iRV (z i).val then
      Structure.RelMap (L := E) r
        (fun i => (⟨⟨(z i).val, h i⟩, (z i).property⟩ : SubRV (X : Set C)))
    else False

local instance : (Auxiliary E).Structure (SubRV (X : Set C)) := auxiliaryStructure X
local instance : E.Structure X := extraStructure X

theorem functions_compatible : Compatible (E := E) (inclusion X) := by
  constructor
  · intro k f z
    apply Subtype.ext
    rfl
  · intro k f z
    have hz : ∀ i, iRV ((inclusion X ∘ z) i).val := fun i => (z i).val.property
    change inclusion X (Structure.funMap (L := E) f z) =
      (if h : ∀ i, iRV ((inclusion X ∘ z) i).val then
        inclusion X (Structure.funMap (L := E) f
          (fun i => ⟨⟨((inclusion X ∘ z) i).val, h i⟩, ((inclusion X ∘ z) i).property⟩))
        else inclusion X (zero X))
    rw [dif_pos hz]
    rfl

theorem relations_compatible : RelationsCompatible (E := E) (inclusion X) := by
  intro k r z
  cases r with
  | inl r => rfl
  | inr r =>
    have hz : ∀ i, iRV ((inclusion X ∘ z) i).val := fun i => (z i).val.property
    change Structure.RelMap (L := E) r z ↔
      (if h : ∀ i, iRV ((inclusion X ∘ z) i).val then
        Structure.RelMap (L := E) r
          (fun i => (⟨⟨((inclusion X ∘ z) i).val, h i⟩,
            ((inclusion X ∘ z) i).property⟩ : SubRV (X : Set C)))
        else False)
    rw [dif_pos hz]
    rfl

theorem guard_compatible : GuardCompatible (E := E) (inclusion X) := by
  intro a
  change Structure.RelMap (L := LRV) Rel.memRV (fun i : Fin 1 => (![a] i).val) ↔ _
  have he : (fun i : Fin 1 => (![a] i).val) = ![a.val] := by
    funext i
    fin_cases i
    rfl
  rw [he]
  change iRV a.val ↔ ∃ q : SubRV (X : Set C), inclusion X q = a
  constructor
  · intro ha
    exact ⟨⟨⟨a.val, ha⟩, a.property⟩, rfl⟩
  · rintro ⟨q, rfl⟩
    exact q.val.property

theorem vf_term_sort {V : Type} (v : V → X) (hv : ∀ i, iVF (v i).val)
    (p : (Expanded E).Term V) (hp : termSort (fun _ => .vf) p = some .vf) :
    iVF (p.realize v).val := by
  induction p with
  | var i => exact hv i
  | func f ts ih =>
    obtain ⟨harg, hres⟩ := (termSort_func (fun _ => .vf) f ts).mp hp
    cases f with
    | inr f => cases hres
    | inl f =>
      have hs : ∀ i, Fn.argSort f i = .vf := by
        cases f <;> try cases hres
        all_goals intro i; first | exact i.elim0 | rfl
      change iVF (Structure.funMap (L := LRV) f (fun i => ((ts i).realize v).val))
      have he : Fn.resSort f = .vf := hres
      have hh := CanonicalStructure.function_sort hC f (fun i => ((ts i).realize v).val) (by
        intro i
        rw [hs i]
        exact ih i (by simpa only [argumentSort, hs i] using harg i))
      simpa only [he, sortEval, iVF] using hh

/-- A syntax-only total extension to unused/ill-sorted token names.
Every genuine polynomial token is left unchanged. -/
def polynomialOrZero {V : Type} (p : (Expanded E).Term V) : (Expanded E).Term V :=
  if termSort (fun _ => .vf) p = some .vf then p else .func (.inl .vfZero) Fin.elim0

theorem polynomialOrZero_sort {V : Type} (p : (Expanded E).Term V) :
    termSort (fun _ => .vf) (polynomialOrZero p) = some .vf := by
  unfold polynomialOrZero
  split_ifs with h
  · exact h
  · simp [termSort, resultSort, argumentSort, Fn.resSort]

def coefficient {V : Type} (v : V → X) (hv : ∀ i, iVF (v i).val)
    (p : (Expanded E).Term V) : SubRV (X : Set C) :=
  let a := (polynomialOrZero p).realize v
  ⟨⟨iRv a.val, rv_mem hC (vf_term_sort X v hv _ (polynomialOrZero_sort p))⟩,
    X.fun_mem Fn.rvMap ![a.val] (by intro i; fin_cases i; exact a.property)⟩

theorem coefficient_spec {V : Type} (v : V → X) (hv : ∀ i, iVF (v i).val)
    (p : (Expanded E).Term V) (hp : termSort (fun _ => .vf) p = some .vf) :
    inclusion X (coefficient X v hv p) = (rvTerm p).realize v := by
  apply Subtype.ext
  simp only [coefficient, polynomialOrZero, if_pos hp, inclusion]
  change iRv (p.realize v).val =
    Structure.funMap (L := LRV) Fn.rvMap (fun i => ((![p] : Fin 1 → (Expanded E).Term V) i).realize v |>.val)
  have he : (fun i => ((![p] : Fin 1 → (Expanded E).Term V) i).realize v |>.val) =
      ![(p.realize v).val] := by
    funext i
    fin_cases i
    rfl
  rw [he]
  rfl

/-- Concrete guarded-RV abstraction in the substructure itself. All
compatibility and polynomial-coefficient premises are discharged here. -/
theorem formula_realize_substructure {V R : Type} {n : ℕ}
    (v : V → X) (hv : ∀ i, iVF (v i).val)
    (r : R → SubRV (X : Set C)) (x : Fin n → SubRV (X : Set C))
    (φ : (Expanded E).BoundedFormula (V ⊕ R) n) (hφ : Fragment φ) :
    (formula φ).Realize (Sum.elim (coefficient X v hv) r) x ↔
      φ.Realize (Sum.elim v (inclusion X ∘ r)) (inclusion X ∘ x) :=
  formula_realize (inclusion X) (inclusion_injective X) (functions_compatible X)
    (relations_compatible X) (guard_compatible X) v r (coefficient X v hv)
    (coefficient_spec X v hv) φ hφ x

end SpecialTransformations.Section6.RVSubstructure
