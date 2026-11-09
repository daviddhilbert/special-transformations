import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.ModelTheory.Semantics
import Mathlib.Tactic.FinCases
import Section6.AngularOrderCodes
import Section6.RVGraphLanguage
import Section6.RVTermSupport

/-! Coherent Section 6 module. The source bodies below are retained
from the individually developed fragments; only imports and file scope
are consolidated. The exported names and mathematical statements remain. -/

/-! Source: Section6.DenefPasAux -/
section

/-! The two auxiliary sorts of the Denef-Pas dictionary. The value
sort is written multiplicatively: its zero is the paper's infinity, so
its order predicate reverses Mathlib's valuation order. These are DP
auxiliary symbols, not a replacement for the shared native RV language.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language

namespace SpecialTransformations.Section6.DenefPasAux

inductive Functions : ℕ → Type
  | rZero : Functions 0
  | rOne : Functions 0
  | rAdd : Functions 2
  | rNeg : Functions 1
  | rMul : Functions 2
  | gInfinity : Functions 0
  | gOne : Functions 0
  | gMul : Functions 2

inductive Relations : ℕ → Type
  | residue : Relations 1
  | value : Relations 1
  | valueLe : Relations 2

def auxLanguage : FirstOrder.Language := ⟨Functions, Relations⟩
set_option allowUnsafeReducibility true in
attribute [local reducible] auxLanguage

variable {R G : Type} [Field R] [LinearOrderedCommGroupWithZero G]

def residue : R ⊕ G → R
  | .inl r => r
  | .inr _ => 0

def value : R ⊕ G → G
  | .inl _ => 1
  | .inr g => g

@[instance_reducible] def auxStructure : auxLanguage.Structure (R ⊕ G) where
  funMap f z := match f with
    | .rZero => .inl 0
    | .rOne => .inl 1
    | .rAdd => match z 0, z 1 with
      | .inl r, .inl s => .inl (r + s)
      | _, _ => .inl 0
    | .rNeg => match z 0 with
      | .inl r => .inl (-r)
      | .inr _ => .inl 0
    | .rMul => match z 0, z 1 with
      | .inl r, .inl s => .inl (r * s)
      | _, _ => .inl 0
    | .gInfinity => .inr 0
    | .gOne => .inr 1
    | .gMul => match z 0, z 1 with
      | .inr g, .inr h => .inr (g * h)
      | _, _ => .inr 1
  RelMap r z := match r with
    | .residue => ∃ a : R, z 0 = .inl a
    | .value => ∃ g : G, z 0 = .inr g
    | .valueLe => ∃ g h : G, z 0 = .inr g ∧ z 1 = .inr h ∧ h ≤ g

local instance instAuxStructure : auxLanguage.Structure (R ⊕ G) := auxStructure

private theorem realize_func2 {I : Type} (f : Functions 2) (t u : auxLanguage.Term I)
    (v : I → R ⊕ G) :
    (Term.func f ![t, u]).realize v = Structure.funMap (L := auxLanguage) f ![t.realize v, u.realize v] := by
  apply congrArg (Structure.funMap (L := auxLanguage) f)
  funext i
  fin_cases i <;> rfl

private theorem realize_rZero {I : Type} (v : I → R ⊕ G) :
    (Term.func Functions.rZero Fin.elim0 : auxLanguage.Term I).realize v = Sum.inl (0 : R) := rfl

private theorem realize_gOne {I : Type} (v : I → R ⊕ G) :
    (Term.func Functions.gOne Fin.elim0 : auxLanguage.Term I).realize v = Sum.inr (1 : G) := rfl

private theorem rAdd_eval (x y : R ⊕ G) :
    Structure.funMap (L := auxLanguage) Functions.rAdd ![x, y] =
      (match x, y with | .inl r, .inl s => Sum.inl (r + s) | _, _ => Sum.inl (0 : R)) := rfl

private theorem gMul_eval (x y : R ⊕ G) :
    Structure.funMap (L := auxLanguage) Functions.gMul ![x, y] =
      (match x, y with | .inr g, .inr h => Sum.inr (g * h) | _, _ => Sum.inr (1 : G)) := rfl

def residueProjection {I : Type} (t : auxLanguage.Term I) : auxLanguage.Term I :=
  .func Functions.rAdd ![t, .func Functions.rZero Fin.elim0]

def valueProjection {I : Type} (t : auxLanguage.Term I) : auxLanguage.Term I :=
  .func Functions.gMul ![t, .func Functions.gOne Fin.elim0]

theorem residueProjection_realize {I : Type} (t : auxLanguage.Term I) (v : I → R ⊕ G) :
    (residueProjection t).realize v = .inl (residue (t.realize v)) := by
  rw [residueProjection, realize_func2, realize_rZero, rAdd_eval]
  cases h : t.realize v <;> simp [residue, h]

theorem valueProjection_realize {I : Type} (t : auxLanguage.Term I) (v : I → R ⊕ G) :
    (valueProjection t).realize v = .inr (value (t.realize v)) := by
  rw [valueProjection, realize_func2, realize_gOne, gMul_eval]
  cases h : t.realize v <;> simp [value, h]

end SpecialTransformations.Section6.DenefPasAux

end
end

/-! Source: Section6.DenefPasCodes -/
section

/-! Total pair codes into the actual leading-term quotient. The value
coordinate includes infinity (zero in multiplicative notation). A zero
residue or infinite value codes the single RV zero. Ordinary RV elements
have representatives with both coordinates nonzero. -/

noncomputable section
open Classical

namespace SpecialTransformations.Section6.DenefPasCodes
open AngularComponent

variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]

abbrev Coord := Fin 2
abbrev Gamma (v : Valuation K Γ) := WithZero (ValueGroup v)
abbrev Aux (v : Valuation K Γ) := Residue v ⊕ Gamma v

@[simp] theorem zero_eq_none (v : Valuation K Γ) : (0 : Gamma v) = none := rfl

def residueCoord (v : Valuation K Γ) (p : Coord → Aux v) : Residue v :=
  match p 0 with | .inl r => r | .inr _ => 0

def valueCoord (v : Valuation K Γ) (p : Coord → Aux v) : Gamma v :=
  match p 1 with | .inl _ => 1 | .inr g => g

def decode (v : Valuation K Γ) (a : Data v) (p : Coord → Aux v) : RVCalc.RV v :=
  match valueCoord v p with
  | none => none
  | some g => encode v a (residueCoord v p) g

def ZeroCode (v : Valuation K Γ) (p : Coord → Aux v) : Prop :=
  residueCoord v p = 0 ∨ valueCoord v p = none

theorem decode_surjective (v : Valuation K Γ) (a : Data v) : Function.Surjective (decode v a) := by
  intro q
  obtain ⟨⟨r, g⟩, h⟩ := encode_surjective v a q
  refine ⟨![Sum.inl r, Sum.inr (some g)], ?_⟩
  exact h

theorem decode_zero_iff (v : Valuation K Γ) (a : Data v) (p : Coord → Aux v) :
    decode v a p = none ↔ ZeroCode v p := by
  cases hg : valueCoord v p with
  | none =>
    have hz : ZeroCode v p := Or.inr hg
    have hd : decode v a p = none := by unfold decode; rw [hg]
    exact iff_of_true hd hz
  | some g =>
    by_cases hr : residueCoord v p = 0
    · simp [decode, ZeroCode, hg, hr, encode_zero]
    · simp [decode, ZeroCode, hg, hr, encode_ne_zero v a _ hr]

def residueValue (v : Valuation K Γ) (a : Data v) : RVCalc.RV v → Residue v
  | none => 0
  | some q => ((splitting v a q).1 : Residue v)

def gammaValue (v : Valuation K Γ) (a : Data v) : RVCalc.RV v → Gamma v
  | none => none
  | some q => some (splitting v a q).2

theorem residue_decode (v : Valuation K Γ) (a : Data v) (p : Coord → Aux v) :
    residueValue v a (decode v a p) = if ZeroCode v p then 0 else residueCoord v p := by
  cases hg : valueCoord v p with
  | none =>
    rw [if_pos (show ZeroCode v p from Or.inr hg)]
    unfold decode
    rw [hg] <;> rfl
  | some g =>
    by_cases hr : residueCoord v p = 0
    · simp [decode, residueValue, ZeroCode, hg, hr, encode_zero]
    · simp [decode, residueValue, ZeroCode, hg, hr, encode_ne_zero v a _ hr]

theorem gamma_decode (v : Valuation K Γ) (a : Data v) (p : Coord → Aux v) :
    gammaValue v a (decode v a p) = if ZeroCode v p then none else valueCoord v p := by
  cases hg : valueCoord v p with
  | none =>
    rw [if_pos (show ZeroCode v p from Or.inr hg)]
    unfold decode
    rw [hg] <;> rfl
  | some g =>
    by_cases hr : residueCoord v p = 0
    · rw [if_pos (show ZeroCode v p from Or.inl hr)]
      unfold decode
      rw [hg, hr]
      change gammaValue v a (encode v a 0 g) = none
      rw [encode_zero]
      rfl
    · simp [decode, gammaValue, ZeroCode, hg, hr, encode_ne_zero v a _ hr] <;> rfl

end SpecialTransformations.Section6.DenefPasCodes
end
end

/-! Source: Section6.DenefPasAngularMap -/
section

/-! The cross-sort angular-component map factors through the actual RV
quotient. No field representative is chosen by the resulting RV function. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical

namespace SpecialTransformations.Section6.DenefPasCodes
open AngularComponent
variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]

theorem residueValue_rv (v : Valuation K Γ) (a : Data v) (x : K) :
    residueValue v a (RVCalc.rv v x) = a.ac x := by
  by_cases hx : x = 0
  · subst x
    rw [RVCalc.rv_zero, map_zero]
    rfl
  · rw [RVCalc.rv_of_ne hx]
    rfl

theorem residueValue_encode (v : Valuation K Γ) (a : Data v)
    (r : Residue v) (g : ValueGroup v) : residueValue v a (encode v a r g) = r := by
  by_cases hr : r = 0
  · subst r
    rw [encode_zero]
    rfl
  · rw [encode_ne_zero v a r hr]
    change ((splitting v a ((splitting v a).symm (Units.mk0 r hr, g))).1 : Residue v) = r
    rw [MulEquiv.apply_symm_apply]
    rfl

def angular (v : Valuation K Γ) (a : Data v) (q : RVCalc.RV v) : RVCalc.RV v :=
  encode v a (residueValue v a q) 1

theorem angular_encode (v : Valuation K Γ) (a : Data v)
    (r : Residue v) (g : ValueGroup v) : angular v a (encode v a r g) = encode v a r 1 := by
  rw [angular, residueValue_encode]

theorem angular_rv (v : Valuation K Γ) (a : Data v) (x : K) :
    angular v a (RVCalc.rv v x) = encode v a (a.ac x) 1 := by
  rw [angular, residueValue_rv]

theorem angular_idempotent (v : Valuation K Γ) (a : Data v) (q : RVCalc.RV v) :
    angular v a (angular v a q) = angular v a q := by
  exact angular_encode v a (residueValue v a q) 1

theorem angular_zero (v : Valuation K Γ) (a : Data v) : angular v a none = none := by
  exact encode_zero v a 1

end SpecialTransformations.Section6.DenefPasCodes
end
end

/-! Source: Section6.DenefPasLanguage -/
section

/-! A concrete three-sort Denef-Pas signature. The field functions are
the VF-only symbols of the released language. The auxiliary signature may
be expanded arbitrarily; it has no field arguments. Parameter constants
are handled by the ordinary withConstants construction. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Section6.DenefPasLanguage
open DenefPasCodes AngularComponent

def FieldFunction (k : ℕ) := {f : Fn k // Fn.resSort f = .vf ∧ ∀ i, Fn.argSort f i = .vf}

inductive Cross : ℕ → Type
  | angular : Cross 1
  | value : Cross 1

inductive SortRelation : ℕ → Type
  | field : SortRelation 1
  | residue : SortRelation 1
  | value : SortRelation 1

def language (E : Language) : Language :=
  ⟨fun k => FieldFunction k ⊕ ((DenefPasAux.auxLanguage.sum E).Functions k ⊕ Cross k),
    fun k => SortRelation k ⊕ (DenefPasAux.auxLanguage.sum E).Relations k⟩

set_option allowUnsafeReducibility true in
attribute [local reducible] language

abbrev Carrier {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) := K ⊕ Aux v

variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]

def fieldValue {D : Type} : K ⊕ D → K
  | .inl x => x
  | .inr _ => 0

def auxValue {v : Valuation K Γ} : Carrier v → Aux v
  | .inl _ => .inl 0
  | .inr d => d

def IsField {D : Type} (x : K ⊕ D) : Prop := ∃ a : K, x = .inl a
def IsAux {v : Valuation K Γ} (x : Carrier v) : Prop := ∃ a : Aux v, x = .inr a

def fieldFunction {D : Type} {k : ℕ} (f : FieldFunction k) (z : Fin k → K ⊕ D) : K :=
  if ∀ i, IsField (z i) then
    match f.val with
    | .vfZero => 0
    | .vfOne => 1
    | .vfAdd => fieldValue (z 0) + fieldValue (z 1)
    | .vfNeg => -fieldValue (z 0)
    | .vfMul => fieldValue (z 0) * fieldValue (z 1)
    | _ => 0
  else 0

@[instance_reducible] def dpStructure (E : Language) (v : Valuation K Γ) (a : Data v)
    [E.Structure (Aux v)] : (language E).Structure (Carrier v) := by
  letI : DenefPasAux.auxLanguage.Structure (Aux v) := DenefPasAux.auxStructure
  letI : (DenefPasAux.auxLanguage.sum E).Structure (Aux v) := inferInstance
  exact {
    funMap := fun f z => match f with
      | .inl f => .inl (fieldFunction f z)
      | .inr (.inl f) =>
        if ∀ i, IsAux (z i) then .inr (Structure.funMap f (fun i => auxValue (z i)))
        else .inr (.inl 0)
      | .inr (.inr .angular) => .inr (.inl (a.ac (fieldValue (z 0))))
      | .inr (.inr .value) => .inr (.inr (gammaValue v a (RVCalc.rv v (fieldValue (z 0)))))
    RelMap := fun r z => match r with
      | .inl .field => IsField (z 0)
      | .inl .residue => ∃ b : Residue v, z 0 = .inr (.inl b)
      | .inl .value => ∃ g : Gamma v, z 0 = .inr (.inr g)
      | .inr r => (∀ i, IsAux (z i)) ∧ Structure.RelMap r (fun i => auxValue (z i)) }

def guard {E : Language} {I : Type} {n : ℕ} (r : SortRelation 1) :
    (language E).BoundedFormula I (n + 1) :=
  .rel (.inl r) ![.var (.inr (Fin.last n))]

def allResidue {E : Language} {I : Type} {n : ℕ}
    (φ : (language E).BoundedFormula I (n + 1)) : (language E).BoundedFormula I n :=
  ((guard .residue) ⟹ φ).all

def allValue {E : Language} {I : Type} {n : ℕ}
    (φ : (language E).BoundedFormula I (n + 1)) : (language E).BoundedFormula I n :=
  ((guard .value) ⟹ φ).all

def allAux {E : Language} {I : Type} {n : ℕ}
    (φ : (language E).BoundedFormula I (n + 1)) : (language E).BoundedFormula I n :=
  (((guard .residue) ⊔ (guard .value)) ⟹ φ).all

/-- The strict output quantifier class: every binder is in RF or Gamma. -/
inductive IsFieldQF {E : Language} {I : Type} :
    {n : ℕ} → (language E).BoundedFormula I n → Prop
  | falsum {n} : IsFieldQF (⊥ : (language E).BoundedFormula I n)
  | atomic {n} {φ : (language E).BoundedFormula I n} (hφ : φ.IsAtomic) : IsFieldQF φ
  | imp {n} {φ ψ : (language E).BoundedFormula I n}
      (hφ : IsFieldQF φ) (hψ : IsFieldQF ψ) : IsFieldQF (φ.imp ψ)
  | residue {n} {φ : (language E).BoundedFormula I (n + 1)}
      (hφ : IsFieldQF φ) : IsFieldQF (allResidue φ)
  | value {n} {φ : (language E).BoundedFormula I (n + 1)}
      (hφ : IsFieldQF φ) : IsFieldQF (allValue φ)

end SpecialTransformations.Section6.DenefPasLanguage


end
end

/-! Source: Section6.DenefPasAuxLift -/
section

/-! Embed actual auxiliary formulas in the three-sort language. Every
auxiliary binder splits into an RF binder and a value-group binder, so the
output has the strict field-quantifier-free syntax. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.Section6.DenefPasAux.auxLanguage
  SpecialTransformations.Section6.DenefPasLanguage.language FirstOrder.Language.sum
open Classical FirstOrder FirstOrder.Language

namespace SpecialTransformations.Section6.DenefPasAuxLift
open DenefPasLanguage DenefPasCodes AngularComponent

abbrev Auxiliary (E : Language) := DenefPasAux.auxLanguage.sum E

def inclusion (E : Language) : Auxiliary E →ᴸ language E where
  onFunction := fun {_} f => .inr (.inl f)
  onRelation := fun {_} r => .inr r

def lift {E : Language} {I : Type} : {n : ℕ} → (Auxiliary E).BoundedFormula I n →
    (language E).BoundedFormula I n
  | _, .falsum => ⊥
  | _, .equal t u => .equal ((inclusion E).onTerm t) ((inclusion E).onTerm u)
  | _, .rel r ts => .rel (.inr r) (fun i => (inclusion E).onTerm (ts i))
  | _, .imp φ ψ => (lift φ).imp (lift ψ)
  | _, .all φ => allResidue (lift φ) ⊓ allValue (lift φ)

theorem fieldQF_inf {E : Language} {I : Type} {n : ℕ}
    {φ ψ : (language E).BoundedFormula I n} (hφ : IsFieldQF φ) (hψ : IsFieldQF ψ) :
    IsFieldQF (φ ⊓ ψ) :=
  .imp (.imp hφ (.imp hψ .falsum)) .falsum

theorem isFieldQF {E : Language} {I : Type} {n : ℕ} (φ : (Auxiliary E).BoundedFormula I n) :
    IsFieldQF (lift φ) := by
  induction φ with
  | falsum => exact .falsum
  | equal t u => exact .atomic (.equal _ _)
  | rel r ts => exact .atomic (.rel _ _)
  | imp φ ψ ihφ ihψ => exact .imp ihφ ihψ
  | all φ ih => exact fieldQF_inf (.residue ih) (.value ih)

def Model {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (E : Language) (val : Valuation K Γ) (a : Data val) : Type := Carrier val

def embed {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (E : Language) (val : Valuation K Γ) (a : Data val) : Aux val → Model E val a := Sum.inr

section Semantics
variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]
variable (E : Language) (val : Valuation K Γ) (a : Data val) [E.Structure (Aux val)]
local instance : DenefPasAux.auxLanguage.Structure (Aux val) := DenefPasAux.auxStructure
local instance : (Auxiliary E).Structure (Aux val) :=
  FirstOrder.Language.sumStructure DenefPasAux.auxLanguage E (Aux val)
local instance : (language E).Structure (Model E val a) := dpStructure E val a

theorem term_realize {I : Type} (t : (Auxiliary E).Term I) (z : I → Aux val) :
    ((inclusion E).onTerm t).realize (embed E val a ∘ z) = embed E val a (t.realize z) := by
  induction t with
  | var i => rfl
  | func f ts ih =>
    change Structure.funMap (L := language E) (M := Model E val a) (.inr (.inl f)) _ = Sum.inr _
    have he : (fun i => ((inclusion E).onTerm (ts i)).realize (embed E val a ∘ z)) =
        (fun i => embed E val a ((ts i).realize z)) := funext ih
    rw [he]
    change (if ∀ i, IsAux (Sum.inr ((ts i).realize z) : Carrier val) then _ else _) = _
    rw [if_pos (fun i => ⟨(ts i).realize z, rfl⟩)]
    rfl

theorem guard_realize {I : Type} {n : ℕ} (r : SortRelation 1)
    (z : I → Model E val a) (x : Fin (n + 1) → Model E val a) :
    (guard r : (language E).BoundedFormula I (n + 1)).Realize z x ↔
      Structure.RelMap (L := language E) (.inl r) ![x (Fin.last n)] := by
  change Structure.RelMap (L := language E) (.inl r) _ ↔ _
  have he : (fun i : Fin 1 =>
      ((![Term.var (.inr (Fin.last n))] : Fin 1 → (language E).Term (I ⊕ Fin (n + 1))) i).realize
        (Sum.elim z x)) = ![x (Fin.last n)] := by
    funext i
    fin_cases i
    rfl
  rw [he]

theorem allResidue_realize {I : Type} {n : ℕ} (φ : (language E).BoundedFormula I (n + 1))
    (z : I → Model E val a) (x : Fin n → Model E val a) :
    (allResidue φ).Realize z x ↔
      ∀ r : Residue val, φ.Realize z (Fin.snoc x (Sum.inr (Sum.inl r))) := by
  rw [allResidue, BoundedFormula.realize_all]
  simp only [BoundedFormula.realize_imp, guard_realize, Fin.snoc_last]
  change (∀ b : Model E val a, (∃ r : Residue val, b = .inr (.inl r)) →
    φ.Realize z (Fin.snoc x b)) ↔ _
  exact ⟨fun h r => h _ ⟨r, rfl⟩, fun h b ⟨r, hr⟩ => hr.symm ▸ h r⟩

theorem allValue_realize {I : Type} {n : ℕ} (φ : (language E).BoundedFormula I (n + 1))
    (z : I → Model E val a) (x : Fin n → Model E val a) :
    (allValue φ).Realize z x ↔
      ∀ g : Gamma val, φ.Realize z (Fin.snoc x (Sum.inr (Sum.inr g))) := by
  rw [allValue, BoundedFormula.realize_all]
  simp only [BoundedFormula.realize_imp, guard_realize, Fin.snoc_last]
  change (∀ b : Model E val a, (∃ g : Gamma val, b = .inr (.inr g)) →
    φ.Realize z (Fin.snoc x b)) ↔ _
  exact ⟨fun h g => h _ ⟨g, rfl⟩, fun h b ⟨g, hg⟩ => hg.symm ▸ h g⟩

private theorem aux_comp_elim {I : Type} {n : ℕ} (z : I → Aux val) (x : Fin n → Aux val) :
    Sum.elim (embed E val a ∘ z) (embed E val a ∘ x) =
      embed E val a ∘ Sum.elim z x := by
  funext i
  cases i <;> rfl

theorem realize {I : Type} {n : ℕ} (φ : (Auxiliary E).BoundedFormula I n)
    (z : I → Aux val) (x : Fin n → Aux val) :
    (lift φ).Realize (embed E val a ∘ z) (embed E val a ∘ x) ↔ φ.Realize z x := by
  induction φ with
  | falsum => rfl
  | equal t u =>
    change ((inclusion E).onTerm t).realize _ = ((inclusion E).onTerm u).realize _ ↔ _
    rw [aux_comp_elim, term_realize, term_realize]
    simp only [embed, BoundedFormula.Realize, Sum.inr.injEq]
    constructor
    · exact fun h => Sum.inr.inj h
    · exact fun h => congrArg (Sum.inr : Aux val → Model E val a) h
  | rel r ts =>
    change Structure.RelMap (L := language E) (.inr r) _ ↔ _
    have he : (fun i => ((inclusion E).onTerm (ts i)).realize
        (Sum.elim (embed E val a ∘ z) (embed E val a ∘ x))) =
        (fun i => embed E val a ((ts i).realize (Sum.elim z x))) := by
      funext i
      rw [aux_comp_elim, term_realize]
    rw [he]
    change ((∀ i, IsAux (Sum.inr ((ts i).realize (Sum.elim z x)) : Carrier val)) ∧
      Structure.RelMap (L := Auxiliary E) r _) ↔ _
    exact and_iff_right (fun i => ⟨_, rfl⟩)
  | imp φ ψ ihφ ihψ => exact imp_congr (ihφ x) (ihψ x)
  | @all n φ ih =>
    rw [lift, BoundedFormula.realize_inf, allResidue_realize, allValue_realize,
      BoundedFormula.realize_all]
    have hr (r : Residue val) := ih (Fin.snoc x (Sum.inl r))
    have hg (g : Gamma val) := ih (Fin.snoc x (Sum.inr g))
    simp only [Fin.comp_snoc] at hr hg
    constructor
    · rintro ⟨hRF, hG⟩ d
      cases d with
      | inl r => exact (hr r).mp (hRF r)
      | inr g => exact (hg g).mp (hG g)
    · intro h
      exact ⟨fun r => (hr r).mpr (h (.inl r)), fun g => (hg g).mpr (h (.inr g))⟩

end Semantics
end SpecialTransformations.Section6.DenefPasAuxLift
end
end

/-! Source: Section6.DenefPasEquality -/
section

/-! The equality entry of the fixed Denef-Pas atomic dictionary. All
syntax is chosen independently of the valued field and angular component. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language

namespace SpecialTransformations.Section6.DenefPasCodes
open AngularComponent DenefPasAux
variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]

theorem coordinates_injective (v : Valuation K Γ) (a : Data v) :
    Function.Injective (fun q => (residueValue v a q, gammaValue v a q)) := by
  intro q q' h
  have hr := congrArg Prod.fst h
  have hg := congrArg Prod.snd h
  cases q with
  | none =>
    cases q' with
    | none => rfl
    | some q' => exact (Option.some_ne_none _ (show some _ = (none : Option (ValueGroup v)) from hg.symm)).elim
  | some q =>
    cases q' with
    | none => exact (Option.some_ne_none _ (show some _ = (none : Option (ValueGroup v)) from hg)).elim
    | some q' =>
      congr 1
      apply (splitting v a).injective
      exact Prod.ext (Units.ext hr) (Option.some.inj hg)

theorem decode_eq_iff (v : Valuation K Γ) (a : Data v) (p q : Coord → Aux v) :
    decode v a p = decode v a q ↔
      (ZeroCode v p ∧ ZeroCode v q) ∨
      (¬ ZeroCode v p ∧ ¬ ZeroCode v q ∧
        residueCoord v p = residueCoord v q ∧ valueCoord v p = valueCoord v q) := by
  constructor
  · intro h
    by_cases hp : ZeroCode v p
    · exact Or.inl ⟨hp, (decode_zero_iff v a q).mp
        (h.symm.trans ((decode_zero_iff v a p).mpr hp))⟩
    · have hq : ¬ ZeroCode v q := fun hq => hp ((decode_zero_iff v a p).mp
        (h.trans ((decode_zero_iff v a q).mpr hq)))
      refine Or.inr ⟨hp, hq, ?_, ?_⟩
      · have he := congrArg (residueValue v a) h
        simpa only [residue_decode, if_neg hp, if_neg hq] using he
      · have he := congrArg (gammaValue v a) h
        simpa only [gamma_decode, hp, hq, if_false] using he
  · rintro (⟨hp, hq⟩ | ⟨hp, hq, hr, hg⟩)
    · exact ((decode_zero_iff v a p).mpr hp).trans ((decode_zero_iff v a q).mpr hq).symm
    · apply coordinates_injective v a
      exact Prod.ext
        (by simpa only [residue_decode, if_neg hp, if_neg hq] using hr)
        (by simpa only [gamma_decode, hp, hq, if_false] using hg)

end SpecialTransformations.Section6.DenefPasCodes

namespace SpecialTransformations.Section6.DenefPasEquality
open DenefPasAux DenefPasCodes AngularComponent

def r {I : Type} (p : Coord → auxLanguage.Term I) : auxLanguage.Term I :=
  residueProjection (p 0)

def g {I : Type} (p : Coord → auxLanguage.Term I) : auxLanguage.Term I :=
  valueProjection (p 1)

def zero {I : Type} (p : Coord → auxLanguage.Term I) : auxLanguage.Formula I :=
  (r p).equal (.func Functions.rZero Fin.elim0) ⊔
    (g p).equal (.func Functions.gInfinity Fin.elim0)

def equal {I : Type} (p q : Coord → auxLanguage.Term I) : auxLanguage.Formula I :=
  (zero p ⊓ zero q) ⊔
    ((zero p).not ⊓ (zero q).not ⊓ (r p).equal (r q) ⊓ (g p).equal (g q))

variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]
local instance (v : Valuation K Γ) : auxLanguage.Structure (Aux v) := auxStructure

theorem r_realize (v : Valuation K Γ) {I : Type} (p : Coord → auxLanguage.Term I)
    (z : I → Aux v) : (r p).realize z = Sum.inl (residueCoord v (fun i => (p i).realize z)) := by
  rw [r, residueProjection_realize]
  unfold residueCoord DenefPasAux.residue
  cases h : (p 0).realize z <;> simp only [h]

theorem g_realize (v : Valuation K Γ) {I : Type} (p : Coord → auxLanguage.Term I)
    (z : I → Aux v) : (g p).realize z = Sum.inr (valueCoord v (fun i => (p i).realize z)) := by
  rw [g, valueProjection_realize]
  unfold valueCoord DenefPasAux.value
  cases h : (p 1).realize z <;> simp only [h]

theorem zero_realize (v : Valuation K Γ) {I : Type} (p : Coord → auxLanguage.Term I)
    (z : I → Aux v) : (zero p).Realize z ↔ ZeroCode v (fun i => (p i).realize z) := by
  simp only [zero, Formula.realize_sup, Formula.realize_equal, r_realize, g_realize]
  change (Sum.inl (residueCoord v _) = Sum.inl (0 : Residue v) ∨
    Sum.inr (valueCoord v _) = Sum.inr (0 : Gamma v)) ↔ _
  rw [Sum.inl.injEq, Sum.inr.injEq]
  rfl

theorem equal_realize (v : Valuation K Γ) (a : Data v) {I : Type}
    (p q : Coord → auxLanguage.Term I) (z : I → Aux v) :
    (equal p q).Realize z ↔
      decode v a (fun i => (p i).realize z) = decode v a (fun i => (q i).realize z) := by
  rw [decode_eq_iff]
  simp only [equal, Formula.realize_sup, Formula.realize_inf, Formula.realize_not,
    Formula.realize_equal, zero_realize, r_realize, g_realize, Sum.inl.injEq, Sum.inr.injEq]
  tauto

end SpecialTransformations.Section6.DenefPasEquality
end
end

/-! Source: Section6.DenefPasMultiplication -/
section

/-! RV multiplication in the fixed auxiliary dictionary. Raw pair
coordinates may be zero or infinity; both encode the same single RV zero. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language

namespace SpecialTransformations.Section6.DenefPasCodes
open AngularComponent
variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]

def mulPair (v : Valuation K Γ) (p q : Coord → Aux v) : Coord → Aux v :=
  ![Sum.inl (residueCoord v p * residueCoord v q), Sum.inr (valueCoord v p * valueCoord v q)]

theorem decode_mulPair (v : Valuation K Γ) (a : Data v) (p q : Coord → Aux v) :
    decode v a (mulPair v p q) = RVCalc.rvMul v (decode v a p) (decode v a q) := by
  cases hp : valueCoord v p with
  | none =>
    have hz : valueCoord v (mulPair v p q) = none := by
      change valueCoord v p * valueCoord v q = _
      rw [hp]
      exact zero_mul _
    unfold decode
    rw [hz, hp]
    exact (RVCalc.rvMul_none_left _).symm
  | some g =>
    cases hq : valueCoord v q with
    | none =>
      have hz : valueCoord v (mulPair v p q) = none := by
        change valueCoord v p * valueCoord v q = _
        rw [hq]
        exact mul_zero _
      unfold decode
      rw [hz, hq]
      exact (RVCalc.rvMul_none_right _).symm
    | some h =>
      unfold decode
      rw [show valueCoord v (mulPair v p q) = some (g * h) by
        change valueCoord v p * valueCoord v q = _
        rw [hp, hq]
        rfl, hp, hq]
      exact (encode_mul v a _ _ g h).symm

end SpecialTransformations.Section6.DenefPasCodes

namespace SpecialTransformations.Section6.DenefPasMultiplication
open DenefPasAux DenefPasCodes AngularComponent

def pair {I : Type} (p q : Coord → auxLanguage.Term I) : Coord → auxLanguage.Term I :=
  ![.func Functions.rMul ![DenefPasEquality.r p, DenefPasEquality.r q],
    .func Functions.gMul ![DenefPasEquality.g p, DenefPasEquality.g q] ]

def graph {I : Type} (p q z : Coord → auxLanguage.Term I) : auxLanguage.Formula I :=
  DenefPasEquality.equal z (pair p q)

variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]
local instance (v : Valuation K Γ) : auxLanguage.Structure (Aux v) := auxStructure

private theorem func2_realize (v : Valuation K Γ) {I : Type}
    (f : Functions 2) (t u : auxLanguage.Term I) (z : I → Aux v) :
    (Term.func f ![t, u]).realize z =
      Structure.funMap (L := auxLanguage) f ![t.realize z, u.realize z] := by
  apply congrArg (Structure.funMap (L := auxLanguage) f)
  funext i
  fin_cases i <;> rfl

theorem pair_realize (v : Valuation K Γ) {I : Type}
    (p q : Coord → auxLanguage.Term I) (z : I → Aux v) :
    (fun i => (pair p q i).realize z) =
      mulPair v (fun i => (p i).realize z) (fun i => (q i).realize z) := by
  funext i
  fin_cases i
  · change (Term.func Functions.rMul ![DenefPasEquality.r p, DenefPasEquality.r q] :
        auxLanguage.Term I).realize z =
      Sum.inl (residueCoord v (fun i => (p i).realize z) * residueCoord v (fun i => (q i).realize z))
    rw [func2_realize, DenefPasEquality.r_realize, DenefPasEquality.r_realize]
    rfl
  · change (Term.func Functions.gMul ![DenefPasEquality.g p, DenefPasEquality.g q] :
        auxLanguage.Term I).realize z =
      Sum.inr (valueCoord v (fun i => (p i).realize z) * valueCoord v (fun i => (q i).realize z))
    rw [func2_realize, DenefPasEquality.g_realize, DenefPasEquality.g_realize]
    rfl

theorem graph_realize (v : Valuation K Γ) (a : Data v) {I : Type}
    (p q z : Coord → auxLanguage.Term I) (w : I → Aux v) :
    (graph p q z).Realize w ↔ decode v a (fun i => (z i).realize w) =
      RVCalc.rvMul v (decode v a (fun i => (p i).realize w))
        (decode v a (fun i => (q i).realize w)) := by
  rw [graph, DenefPasEquality.equal_realize, pair_realize, decode_mulPair]

end SpecialTransformations.Section6.DenefPasMultiplication
end
end

/-! Source: Section6.DenefPasInverse -/
section

/-! RV inversion has an auxiliary graph using multiplication and the
single zero case. No inverse symbol is required in either DP ring language. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language

namespace SpecialTransformations.Section6.DenefPasInverse
open DenefPasAux DenefPasCodes AngularComponent

def one {I : Type} : Coord → auxLanguage.Term I :=
  ![.func Functions.rOne Fin.elim0, .func Functions.gOne Fin.elim0]

def graph {I : Type} (p q : Coord → auxLanguage.Term I) : auxLanguage.Formula I :=
  (DenefPasEquality.zero p ⊓ DenefPasEquality.zero q) ⊔
    DenefPasMultiplication.graph p q one

variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]
local instance (v : Valuation K Γ) : auxLanguage.Structure (Aux v) := auxStructure

theorem inverse_iff (v : Valuation K Γ) (p q : RVCalc.RV v) :
    q = p.map Inv.inv ↔ (p = none ∧ q = none) ∨ RVCalc.rvMul v p q = some 1 := by
  cases p with
  | none => cases q <;> simp [RVCalc.rvMul]
  | some p =>
    cases q with
    | none => simp [RVCalc.rvMul]
    | some q =>
      simp only [Option.map_some, Option.some.injEq, Option.some_ne_none,
        false_and, false_or, RVCalc.rvMul_some]
      constructor
      · rintro rfl
        exact mul_inv_cancel p
      · intro h
        exact mul_left_cancel (h.trans (mul_inv_cancel p).symm)

theorem one_realize (v : Valuation K Γ) (a : Data v) {I : Type} (z : I → Aux v) :
    decode v a (fun i => (one i : auxLanguage.Term I).realize z) = some 1 := by
  change encode v a 1 1 = some 1
  exact encode_one v a

theorem graph_realize (v : Valuation K Γ) (a : Data v) {I : Type}
    (p q : Coord → auxLanguage.Term I) (z : I → Aux v) :
    (graph p q).Realize z ↔ decode v a (fun i => (q i).realize z) =
      (decode v a (fun i => (p i).realize z)).map Inv.inv := by
  rw [graph, Formula.realize_sup, Formula.realize_inf,
    DenefPasEquality.zero_realize, DenefPasEquality.zero_realize,
    DenefPasMultiplication.graph_realize, one_realize, inverse_iff,
    decode_zero_iff, decode_zero_iff]
  exact or_congr Iff.rfl eq_comm

end SpecialTransformations.Section6.DenefPasInverse
end
end

/-! Source: Section6.DenefPasNativeCodes -/
section

/-! A total two-coordinate forward code from the native carrier onto
the three-sort DP carrier. Its first coordinate distinguishes RF and
Gamma payloads; field payloads retain the actual field element. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical

namespace SpecialTransformations.Section6.DenefPasNativeCodes
open AngularComponent DenefPasCodes DenefPasLanguage
variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]

abbrev NativeCarrier (v : Valuation K Γ) := K ⊕ RVCalc.RV v

def valueRepresentative (v : Valuation K Γ) (a : Data v) : Gamma v → RVCalc.RV v
  | none => none
  | some g => encode v a 1 g

theorem valueRepresentative_value (v : Valuation K Γ) (a : Data v) (g : Gamma v) :
    gammaValue v a (valueRepresentative v a g) = g := by
  cases g with
  | none => rfl
  | some g =>
    rw [valueRepresentative, encode_ne_zero v a 1 one_ne_zero]
    change some (splitting v a ((splitting v a).symm (Units.mk0 1 one_ne_zero, g))).2 = some g
    rw [MulEquiv.apply_symm_apply]

def code (v : Valuation K Γ) (a : Data v) (p : Coord → NativeCarrier v) : Carrier v :=
  match p 1 with
  | .inl x => .inl x
  | .inr q =>
    if p 0 = .inl 0 then .inr (.inl (residueValue v a q)) else .inr (.inr (gammaValue v a q))

def pack (v : Valuation K Γ) (a : Data v) : Carrier v → Coord → NativeCarrier v
  | .inl x => ![.inl 0, .inl x]
  | .inr (.inl r) => ![.inl 0, .inr (encode v a r 1)]
  | .inr (.inr g) => ![.inr none, .inr (valueRepresentative v a g)]

theorem code_pack (v : Valuation K Γ) (a : Data v) (q : Carrier v) :
    code v a (pack v a q) = q := by
  cases q with
  | inl x => rfl
  | inr d =>
    cases d with
    | inl r =>
      change (if (Sum.inl 0 : NativeCarrier v) = Sum.inl 0 then _ else _) = _
      rw [if_pos rfl, residueValue_encode]
    | inr g =>
      change (if (Sum.inr none : NativeCarrier v) = Sum.inl 0
        then Sum.inr (Sum.inl (residueValue v a (valueRepresentative v a g)))
        else Sum.inr (Sum.inr (gammaValue v a (valueRepresentative v a g)))) =
          (Sum.inr (Sum.inr g) : Carrier v)
      rw [if_neg (by intro h; cases h), valueRepresentative_value]

theorem code_surjective (v : Valuation K Γ) (a : Data v) : Function.Surjective (code v a) :=
  fun q => ⟨pack v a q, code_pack v a q⟩

end SpecialTransformations.Section6.DenefPasNativeCodes
end
end

/-! Source: Section6.DenefPasNormalization -/
section

/-! Normalize raw pair codes to the actual angular/value coordinates.
This prevents an auxiliary relation from seeing the ignored residue or
value coordinate of a code for RV zero. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language

namespace SpecialTransformations.Section6.DenefPasNormalization
open DenefPasAux DenefPasCodes AngularComponent
variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]

def coordinates (v : Valuation K Γ) (a : Data v) (q : RVCalc.RV v) : Coord → Aux v :=
  ![Sum.inl (residueValue v a q), Sum.inr (gammaValue v a q)]

theorem decode_coordinates (v : Valuation K Γ) (a : Data v) (q : RVCalc.RV v) :
    decode v a (coordinates v a q) = q := by
  cases q with
  | none => rfl
  | some q =>
    change encode v a ((splitting v a q).1 : Residue v) (splitting v a q).2 = some q
    rw [encode_ne_zero v a _ (Units.ne_zero (splitting v a q).1)]
    congr 1
    apply (splitting v a).injective
    rw [MulEquiv.apply_symm_apply]
    exact Prod.ext (Units.ext rfl) rfl

theorem pair_eq_iff {D : Type} (p : Coord → D) (r g : D) :
    p = ![r, g] ↔ p 0 = r ∧ p 1 = g := by
  constructor
  · intro h
    exact ⟨congrFun h 0, congrFun h 1⟩
  · rintro ⟨h0, h1⟩
    funext i
    fin_cases i
    · exact h0
    · exact h1

def graph {I : Type} (p q : Coord → auxLanguage.Term I) : auxLanguage.Formula I :=
  (DenefPasEquality.zero p ⊓
    ((q 0).equal (Constants.term (L := auxLanguage) Functions.rZero) ⊓
      (q 1).equal (Constants.term (L := auxLanguage) Functions.gInfinity))) ⊔
    ((DenefPasEquality.zero p).not ⊓
      ((q 0).equal (DenefPasEquality.r p) ⊓ (q 1).equal (DenefPasEquality.g p)))

local instance (v : Valuation K Γ) : auxLanguage.Structure (Aux v) := auxStructure

private theorem rZero_realize (v : Valuation K Γ) {I : Type} (z : I → Aux v) :
    (Constants.term (L := auxLanguage) Functions.rZero).realize z = Sum.inl (0 : Residue v) := rfl

private theorem gInfinity_realize (v : Valuation K Γ) {I : Type} (z : I → Aux v) :
    (Constants.term (L := auxLanguage) Functions.gInfinity).realize z = Sum.inr (none : Gamma v) := rfl

theorem graph_realize (v : Valuation K Γ) (a : Data v) {I : Type}
    (p q : Coord → auxLanguage.Term I) (z : I → Aux v) :
    (graph p q).Realize z ↔ (fun i => (q i).realize z) =
      coordinates v a (decode v a (fun i => (p i).realize z)) := by
  simp only [graph, Formula.realize_sup, Formula.realize_inf, Formula.realize_not,
    DenefPasEquality.zero_realize v p z, Formula.realize_equal,
    DenefPasEquality.r_realize, DenefPasEquality.g_realize, rZero_realize, gInfinity_realize]
  by_cases hp : ZeroCode v (fun i => (p i).realize z)
  · simp only [hp, true_and, not_true_eq_false, false_and, or_false]
    rw [(decode_zero_iff v a _).mpr hp]
    simpa only [coordinates, residueValue, gammaValue] using
      (pair_eq_iff (fun i => (q i).realize z) (Sum.inl (0 : Residue v) : Aux v)
        (Sum.inr (none : Gamma v) : Aux v)).symm
  · simp only [hp, false_and, not_false_eq_true, true_and, false_or]
    simp only [coordinates, residue_decode, gamma_decode, hp, if_false, pair_eq_iff]

end SpecialTransformations.Section6.DenefPasNormalization
end
end

/-! Source: Section6.DenefPasRV -/
section

/-! The auxiliary native symbols on the actual RV quotient, expressed
through the proved angular-component splitting. Residue operations are
totalized at RV zero outside the residue domain, as in the common language. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Section6.DenefPasRV
open DenefPasCodes AngularComponent RVGraphLanguage
variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]

def residueDomain (v : Valuation K Γ) (a : Data v) (q : RVCalc.RV v) : Prop :=
  q = none ∨ gammaValue v a q = 1

def add (v : Valuation K Γ) (a : Data v) (p q : RVCalc.RV v) : RVCalc.RV v :=
  if residueDomain v a p ∧ residueDomain v a q then
    if p = none then q else if q = none then p
      else encode v a (residueValue v a p + residueValue v a q) 1
  else none

def neg (v : Valuation K Γ) (a : Data v) (p : RVCalc.RV v) : RVCalc.RV v :=
  if residueDomain v a p then encode v a (-residueValue v a p) 1 else none

@[instance_reducible] def rvStructure (v : Valuation K Γ) (a : Data v) :
    RVBase.Structure (RVCalc.RV v) where
  funMap f z := match f.val with
    | .rvZero => none
    | .rvOne => some 1
    | .rvMul => RVCalc.rvMul v (z 0) (z 1)
    | .rvInv => (z 0).map Inv.inv
    | .kAdd => add v a (z 0) (z 1)
    | .kNeg => neg v a (z 0)
    | _ => none
  RelMap r z := match r.val with
    | .memRV => True
    | .memVF => False
    | .memUnits => z 0 ≠ none ∧ gammaValue v a (z 0) = 1
    | .rvLe => gammaValue v a (z 1) ≤ gammaValue v a (z 0)

theorem domain_decode (v : Valuation K Γ) (a : Data v) (p : Coord → Aux v) :
    residueDomain v a (decode v a p) ↔ ZeroCode v p ∨ valueCoord v p = 1 := by
  rw [residueDomain, decode_zero_iff, gamma_decode]
  by_cases hp : ZeroCode v p
  · simp only [hp, true_or]
  · simp only [hp, if_false, false_or]

theorem units_decode (v : Valuation K Γ) (a : Data v) (p : Coord → Aux v) :
    (decode v a p ≠ none ∧ gammaValue v a (decode v a p) = 1) ↔
      ¬ ZeroCode v p ∧ valueCoord v p = 1 := by
  have hn : decode v a p ≠ none ↔ ¬ ZeroCode v p := not_congr (decode_zero_iff v a p)
  rw [hn, gamma_decode]
  by_cases hp : ZeroCode v p
  · simp only [hp, not_true_eq_false, false_and]
  · simp only [hp, not_false_eq_true, true_and, if_false]

end SpecialTransformations.Section6.DenefPasRV

end
end

/-! Source: Section6.DenefPasResidue -/
section

/-! Residue-domain and residue-negation entries of the auxiliary atomic
dictionary, with the common off-domain totalization. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language

namespace SpecialTransformations.Section6.DenefPasResidue
open DenefPasAux DenefPasCodes AngularComponent

def domain {I : Type} (p : Coord → auxLanguage.Term I) : auxLanguage.Formula I :=
  DenefPasEquality.zero p ⊔
    (DenefPasEquality.g p).equal (Constants.term (L := auxLanguage) Functions.gOne)

def negPair {I : Type} (p : Coord → auxLanguage.Term I) : Coord → auxLanguage.Term I :=
  ![Functions.apply₁ (L := auxLanguage) Functions.rNeg (DenefPasEquality.r p),
    Constants.term (L := auxLanguage) Functions.gOne]

def negGraph {I : Type} (p q : Coord → auxLanguage.Term I) : auxLanguage.Formula I :=
  (domain p ⊓ ((DenefPasEquality.zero p ⊓ DenefPasEquality.zero q) ⊔
    ((DenefPasEquality.zero p).not ⊓ DenefPasEquality.equal q (negPair p)))) ⊔
    ((domain p).not ⊓ DenefPasEquality.zero q)

variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]
local instance (v : Valuation K Γ) : auxLanguage.Structure (Aux v) := auxStructure

theorem domain_realize (v : Valuation K Γ) (a : Data v) {I : Type}
    (p : Coord → auxLanguage.Term I) (z : I → Aux v) :
    (domain p).Realize z ↔ DenefPasRV.residueDomain v a (decode v a (fun i => (p i).realize z)) := by
  rw [domain, Formula.realize_sup, DenefPasEquality.zero_realize, Formula.realize_equal,
    DenefPasEquality.g_realize, DenefPasRV.domain_decode]
  change (_ ∨ Sum.inr (valueCoord v _) = Sum.inr (1 : Gamma v)) ↔ _
  rw [Sum.inr.injEq]

theorem negPair_decode (v : Valuation K Γ) (a : Data v) {I : Type}
    (p : Coord → auxLanguage.Term I) (z : I → Aux v) :
    decode v a (fun i => (negPair p i).realize z) =
      encode v a (-residueCoord v (fun i => (p i).realize z)) 1 := by
  have hn : (Functions.apply₁ (L := auxLanguage) Functions.rNeg (DenefPasEquality.r p)).realize z =
      Sum.inl (-residueCoord v (fun i => (p i).realize z)) := by
    rw [Term.realize_functions_apply₁, DenefPasEquality.r_realize]
    rfl
  have he : (fun i => (negPair p i).realize z) =
      ![Sum.inl (-residueCoord v (fun i => (p i).realize z)), Sum.inr (1 : Gamma v)] := by
    funext i
    fin_cases i
    · exact hn
    · rfl
  rw [he]
  rfl

theorem negGraph_realize (v : Valuation K Γ) (a : Data v) {I : Type}
    (p q : Coord → auxLanguage.Term I) (z : I → Aux v) :
    (negGraph p q).Realize z ↔ decode v a (fun i => (q i).realize z) =
      DenefPasRV.neg v a (decode v a (fun i => (p i).realize z)) := by
  simp only [negGraph, Formula.realize_sup, Formula.realize_inf, Formula.realize_not,
    domain_realize v a p z, DenefPasEquality.zero_realize v p z,
    DenefPasEquality.zero_realize v q z,
    DenefPasEquality.equal_realize v a q (negPair p) z,
    negPair_decode, DenefPasRV.neg]
  by_cases hd : DenefPasRV.residueDomain v a (decode v a (fun i => (p i).realize z))
  · rw [if_pos hd]
    simp only [hd, true_and, not_true_eq_false, false_and, or_false]
    by_cases hp : ZeroCode v (fun i => (p i).realize z)
    · rw [(decode_zero_iff v a _).mpr hp]
      simp only [hd, hp, true_and, not_true_eq_false, false_and, or_false,
        false_or, residueValue, neg_zero, encode_zero, decode_zero_iff]
    · rw [residue_decode, if_neg hp]
      simp only [hd, hp, true_and, not_false_eq_true, false_and, or_false, false_or]
  · rw [if_neg hd, decode_zero_iff]
    simp only [hd, false_and, not_false_eq_true, true_and, false_or]

def addPair {I : Type} (p q : Coord → auxLanguage.Term I) : Coord → auxLanguage.Term I :=
  ![Functions.apply₂ (L := auxLanguage) Functions.rAdd (DenefPasEquality.r p) (DenefPasEquality.r q),
    Constants.term (L := auxLanguage) Functions.gOne]

def addGraph {I : Type} (p q z : Coord → auxLanguage.Term I) : auxLanguage.Formula I :=
  ((domain p ⊓ domain q) ⊓
    ((DenefPasEquality.zero p ⊓ DenefPasEquality.equal z q) ⊔
      (DenefPasEquality.zero q ⊓ DenefPasEquality.equal z p) ⊔
      ((DenefPasEquality.zero p).not ⊓ (DenefPasEquality.zero q).not ⊓
        DenefPasEquality.equal z (addPair p q)))) ⊔
    ((domain p ⊓ domain q).not ⊓ DenefPasEquality.zero z)

theorem addPair_decode (v : Valuation K Γ) (a : Data v) {I : Type}
    (p q : Coord → auxLanguage.Term I) (z : I → Aux v) :
    decode v a (fun i => (addPair p q i).realize z) =
      encode v a (residueCoord v (fun i => (p i).realize z) +
        residueCoord v (fun i => (q i).realize z)) 1 := by
  have hn : (Functions.apply₂ (L := auxLanguage) Functions.rAdd
      (DenefPasEquality.r p) (DenefPasEquality.r q)).realize z =
      Sum.inl (residueCoord v (fun i => (p i).realize z) +
        residueCoord v (fun i => (q i).realize z)) := by
    rw [Term.realize_functions_apply₂, DenefPasEquality.r_realize, DenefPasEquality.r_realize]
    rfl
  have he : (fun i => (addPair p q i).realize z) =
      ![Sum.inl (residueCoord v (fun i => (p i).realize z) +
        residueCoord v (fun i => (q i).realize z)), Sum.inr (1 : Gamma v)] := by
    funext i
    fin_cases i
    · exact hn
    · rfl
  rw [he]
  rfl

theorem addGraph_realize (v : Valuation K Γ) (a : Data v) {I : Type}
    (p q z : Coord → auxLanguage.Term I) (w : I → Aux v) :
    (addGraph p q z).Realize w ↔ decode v a (fun i => (z i).realize w) =
      DenefPasRV.add v a (decode v a (fun i => (p i).realize w))
        (decode v a (fun i => (q i).realize w)) := by
  simp only [addGraph, Formula.realize_sup, Formula.realize_inf, Formula.realize_not,
    domain_realize v a p w, domain_realize v a q w,
    DenefPasEquality.zero_realize v p w, DenefPasEquality.zero_realize v q w,
    DenefPasEquality.zero_realize v z w,
    DenefPasEquality.equal_realize v a z q w, DenefPasEquality.equal_realize v a z p w,
    DenefPasEquality.equal_realize v a z (addPair p q) w, addPair_decode,
    DenefPasRV.add]
  by_cases hd : DenefPasRV.residueDomain v a (decode v a (fun i => (p i).realize w)) ∧
      DenefPasRV.residueDomain v a (decode v a (fun i => (q i).realize w))
  · rw [if_pos hd]
    simp only [hd, true_and, not_true_eq_false, false_and, or_false]
    by_cases hp : ZeroCode v (fun i => (p i).realize w)
    · have hdp := (decode_zero_iff v a _).mpr hp
      rw [if_pos hdp]
      by_cases hq : ZeroCode v (fun i => (q i).realize w)
      · rw [hdp, (decode_zero_iff v a _).mpr hq]
        simp only [decode_zero_iff]
        simp only [hp, hq, true_and, not_true_eq_false, false_and, or_false, or_self]
      · have hnq := (not_congr (decode_zero_iff v a _)).mpr hq
        tauto
    · have hdp := (not_congr (decode_zero_iff v a _)).mpr hp
      rw [if_neg hdp]
      by_cases hq : ZeroCode v (fun i => (q i).realize w)
      · rw [if_pos ((decode_zero_iff v a _).mpr hq)]
        tauto
      · have hdq := (not_congr (decode_zero_iff v a _)).mpr hq
        rw [if_neg hdq, residue_decode, if_neg hp, residue_decode, if_neg hq]
        tauto
  · rw [if_neg hd, decode_zero_iff]
    simp only [hd, false_and, not_false_eq_true, true_and, false_or]

end SpecialTransformations.Section6.DenefPasResidue
end
end

/-! Source: Section6.DenefPasOrder -/
section

/-! The native RV comparison in auxiliary syntax. The order is reversed
relative to Mathlib's multiplicative valuation order, and RV zero is its
top element in the paper convention. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language

namespace SpecialTransformations.Section6.DenefPasOrder
open DenefPasAux DenefPasCodes AngularComponent

def compare {I : Type} (p q : Coord → auxLanguage.Term I) : auxLanguage.Formula I :=
  FirstOrder.Language.Relations.formula₂ (L := auxLanguage) Relations.valueLe
    (DenefPasEquality.g p) (DenefPasEquality.g q)

def graph {I : Type} (p q : Coord → auxLanguage.Term I) : auxLanguage.Formula I :=
  DenefPasEquality.zero q ⊔
    ((DenefPasEquality.zero p).not ⊓ ((DenefPasEquality.zero q).not ⊓ compare p q))

variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]
local instance (v : Valuation K Γ) : auxLanguage.Structure (Aux v) := auxStructure

theorem compare_realize (v : Valuation K Γ) {I : Type} (p q : Coord → auxLanguage.Term I)
    (z : I → Aux v) :
    (compare p q).Realize z ↔ valueCoord v (fun i => (q i).realize z) ≤
      valueCoord v (fun i => (p i).realize z) := by
  rw [compare, Formula.realize_rel₂, DenefPasEquality.g_realize, DenefPasEquality.g_realize]
  change (∃ g h : Gamma v,
    Sum.inr (valueCoord v (fun i => (p i).realize z)) = Sum.inr g ∧
    Sum.inr (valueCoord v (fun i => (q i).realize z)) = Sum.inr h ∧ h ≤ g) ↔ _
  simp only [Sum.inr.injEq]
  constructor
  · rintro ⟨g, h, hg, hh, hle⟩
    rw [← hg, ← hh] at hle
    exact hle
  · intro h
    exact ⟨_, _, rfl, rfl, h⟩

theorem graph_realize (v : Valuation K Γ) (a : Data v) {I : Type}
    (p q : Coord → auxLanguage.Term I) (z : I → Aux v) :
    (graph p q).Realize z ↔
      gammaValue v a (decode v a (fun i => (q i).realize z)) ≤
        gammaValue v a (decode v a (fun i => (p i).realize z)) := by
  simp only [graph, Formula.realize_sup, Formula.realize_inf, Formula.realize_not,
    DenefPasEquality.zero_realize v p z, DenefPasEquality.zero_realize v q z,
    compare_realize, gamma_decode]
  by_cases hp : ZeroCode v (fun i => (p i).realize z)
  · by_cases hq : ZeroCode v (fun i => (q i).realize z)
    · simp only [hp, hq, true_or, if_true]
      exact iff_of_true trivial le_rfl
    · simp only [hp, hq, false_or, not_true_eq_false, false_and, if_true, if_false]
      change False ↔ valueCoord v (fun i => (q i).realize z) ≤ (⊥ : Gamma v)
      refine ⟨False.elim, fun h => hq (Or.inr ?_)⟩
      exact le_antisymm h bot_le
  · by_cases hq : ZeroCode v (fun i => (q i).realize z)
    · simp only [hp, hq, true_or, if_true, if_false]
      change True ↔ (⊥ : Gamma v) ≤ valueCoord v (fun i => (p i).realize z)
      exact iff_of_true trivial bot_le
    · simp only [hp, hq, false_or, not_false_eq_true, true_and, if_false]

end SpecialTransformations.Section6.DenefPasOrder
end
end

