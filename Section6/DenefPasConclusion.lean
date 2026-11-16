module

public import Section6.DenefPasTrivialBranch

@[expose] public section

/-! Coherent Section 6 module. The source bodies below are retained
from the individually developed fragments; only imports and file scope
are consolidated. The exported names and mathematical statements remain. -/

/-! Source: Section6.DenefPasElimination -/
section

/-! Corollary6.5 in the concrete tagged DP presentation. One output formula
works for trivial and nontrivial valuations, over exactly the original free
context. Earlier-section and authorized standard inputs remain explicit. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language

namespace SpecialTransformations.Section6.DenefPasElimination
open AngularComponent DenefPasCodes DenefPasLanguage DenefPasParameters

def combine {E : _root_.FirstOrder.Language.{0, 0}} {I : Type}
    (ψT ψN : (language E).Formula I) : (language E).Formula I :=
  (DenefPasTrivialTest.test ⊓ ψT) ⊔ (DenefPasTrivialTest.test.not ⊓ ψN)

theorem combine_isFieldQF {E : _root_.FirstOrder.Language.{0, 0}} {I : Type}
    {ψT ψN : (language E).Formula I} (hT : IsFieldQF ψT) (hN : IsFieldQF ψN) :
    IsFieldQF (combine ψT ψN) :=
  DenefPasTrivialTest.fieldQF_sup
    (DenefPasAuxLift.fieldQF_inf DenefPasTrivialTest.isFieldQF hT)
    (DenefPasAuxLift.fieldQF_inf (.imp DenefPasTrivialTest.isFieldQF .falsum) hN)

theorem encoded_corollary_6_5 (hRecognition : DenefPasHenselianModels.OrdinaryRecognition)
    (E : _root_.FirstOrder.Language.{0, 0})
    (hEarlier : EnvelopeUniformity.EarlierPreparation)
    (hEnv : UniformNormalizedElimination.NativeEnvelopes (DenefPasMorley.signature E))
    (hNormal : HenselianElimination.RVLiteralNormalForm (DenefPasMorley.signature E))
    {I : Type} [Finite I] (s : I → SortKind) (φ : (language E).Formula I) :
    ∃ ψ : (language E).Formula I, IsFieldQF ψ ∧
      ∀ (K Γ : Type) [Field K] [LinearOrderedCommGroupWithZero Γ]
        (v : Valuation K Γ) (a : Data v) [CharZero K] [CharZero (Residue v)]
        [HenselianLocalRing v.valuationSubring] [E.Structure (Aux v)],
        letI : (language E).Structure (DenefPasAuxLift.Model E v a) := dpStructure E v a
        ∀ z : I → DenefPasAuxLift.Model E v a, Sorted E v a s z →
          (φ.Realize z ↔ ψ.Realize z) := by
  obtain ⟨ψN, hN, heN⟩ := DenefPasHenselianModels.eliminate_nontrivial hRecognition E
    hEarlier hEnv hNormal s φ
  let ψT := DenefPasTrivialElimination.formula s φ
  refine ⟨combine ψT ψN, combine_isFieldQF (DenefPasTrivialElimination.isFieldQF s φ) hN, ?_⟩
  intro K Γ _ _ v a _ _ _ _
  letI : (language E).Structure (DenefPasAuxLift.Model E v a) := dpStructure E v a
  intro z hz
  by_cases ht : Trivial v
  · have htest := (DenefPasTrivialTest.realize E v a z).mpr ht
    have he := DenefPasTrivialElimination.realize E v a ht s φ z hz
    simpa only [combine, Formula.realize_sup, Formula.realize_inf, Formula.realize_not,
      htest, not_true_eq_false, true_and, false_and, or_false] using he.symm
  · have htest : ¬ (DenefPasTrivialTest.test (E := E) (I := I)).Realize z :=
      fun hh => ht ((DenefPasTrivialTest.realize E v a z).mp hh)
    simpa only [combine, Formula.realize_sup, Formula.realize_inf, Formula.realize_not,
      htest, not_false_eq_true, false_and, true_and, false_or] using heN K Γ v a ht z hz

end SpecialTransformations.Section6.DenefPasElimination
end
end

/-! Source: Section6.DenefPasFreeParameters -/
section

/-! Extend the finite-context result to arbitrary original parameter
names using the formula's actual finite free-variable support. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language

namespace SpecialTransformations.Section6.DenefPasFreeParameters
open AngularComponent DenefPasCodes DenefPasLanguage DenefPasParameters

def restrict {E : _root_.FirstOrder.Language.{0, 0}} {I : Type} (φ : (language E).Formula I) :
    (language E).Formula φ.freeVarFinset := φ.restrictFreeVar id

theorem restrict_realize {E : _root_.FirstOrder.Language.{0, 0}} {I M : Type}
    [(language E).Structure M] (φ : (language E).Formula I) (z : I → M) :
    (restrict φ).Realize (z ∘ Subtype.val) ↔ φ.Realize z := by
  apply BoundedFormula.realize_restrictFreeVar z
  intro i
  rfl

theorem encoded_corollary_6_5 (hRecognition : DenefPasHenselianModels.OrdinaryRecognition)
    (E : _root_.FirstOrder.Language.{0, 0})
    (hEarlier : EnvelopeUniformity.EarlierPreparation)
    (hEnv : UniformNormalizedElimination.NativeEnvelopes (DenefPasMorley.signature E))
    (hNormal : HenselianElimination.RVLiteralNormalForm (DenefPasMorley.signature E))
    {I : Type} (s : I → SortKind) (φ : (language E).Formula I) :
    ∃ ψ : (language E).Formula I, IsFieldQF ψ ∧
      ∀ (K Γ : Type) [Field K] [LinearOrderedCommGroupWithZero Γ]
        (v : Valuation K Γ) (a : Data v) [CharZero K] [CharZero (Residue v)]
        [HenselianLocalRing v.valuationSubring] [E.Structure (Aux v)],
        letI : (language E).Structure (DenefPasAuxLift.Model E v a) := dpStructure E v a
        ∀ z : I → DenefPasAuxLift.Model E v a, Sorted E v a s z →
          (φ.Realize z ↔ ψ.Realize z) := by
  let A := φ.freeVarFinset
  let sA : A → SortKind := fun i => s i.val
  obtain ⟨ψA, hA, heA⟩ := DenefPasElimination.encoded_corollary_6_5 hRecognition E hEarlier
    hEnv hNormal sA (restrict φ)
  let f : A → (language E).Term I := fun i => .var i.val
  refine ⟨ψA.subst f, DenefPasSubstitution.isFieldQF_subst f hA, ?_⟩
  intro K Γ _ _ v a _ _ _ _
  letI : (language E).Structure (DenefPasAuxLift.Model E v a) := dpStructure E v a
  intro z hz
  have hs : Sorted E v a sA (z ∘ Subtype.val) := fun i => hz i.val
  have hr := restrict_realize φ z
  have he := heA K Γ v a (z ∘ Subtype.val) hs
  have hsubst : Formula.Realize (ψA.subst f) z ↔ ψA.Realize (z ∘ Subtype.val) := by
    rw [Formula.Realize, BoundedFormula.realize_subst]
    rfl
  exact hr.symm.trans (he.trans hsubst.symm)

end SpecialTransformations.Section6.DenefPasFreeParameters
end
end

/-! Source: Section6.DenefPasSorts -/
section

/-! Sort metadata on the existing DP signature, with canonical tagged
semantics. This adds no language or formula datatype. The model laws are
only symbol typing and off-sort totalization, never elimination properties. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.Section6.DenefPasLanguage.language
  SpecialTransformations.Section6.DenefPasAux.auxLanguage FirstOrder.Language.sum
open Classical FirstOrder FirstOrder.Language

namespace SpecialTransformations.Section6.DenefPasSorts
open AngularComponent DenefPasCodes DenefPasLanguage DenefPasParameters

structure AuxiliarySorts (E : _root_.FirstOrder.Language.{0, 0}) where
  functionResult : ∀ {k}, E.Functions k → Bool
  functionArgument : ∀ {k}, E.Functions k → Fin k → Bool
  relationArgument : ∀ {k}, E.Relations k → Fin k → Bool

def auxiliaryKind (b : Bool) : SortKind := if b then .value else .residue

def nativeAuxResult {k : ℕ} : DenefPasAux.Functions k → SortKind
  | .rZero | .rOne | .rAdd | .rNeg | .rMul => .residue
  | .gInfinity | .gOne | .gMul => .value

def functionResult {E : _root_.FirstOrder.Language.{0, 0}} (p : AuxiliarySorts E) {k : ℕ} :
    (language E).Functions k → SortKind
  | .inl _ => .field
  | .inr (.inl (.inl f)) => nativeAuxResult f
  | .inr (.inl (.inr f)) => auxiliaryKind (p.functionResult f)
  | .inr (.inr .angular) => .residue
  | .inr (.inr .value) => .value

def functionArgument {E : _root_.FirstOrder.Language.{0, 0}} (p : AuxiliarySorts E) {k : ℕ} :
    (language E).Functions k → Fin k → SortKind
  | .inl _ => fun _ => .field
  | .inr (.inl (.inl f)) => fun _ => nativeAuxResult f
  | .inr (.inl (.inr f)) => fun i => auxiliaryKind (p.functionArgument f i)
  | .inr (.inr _) => fun _ => .field

def relationArgument {E : _root_.FirstOrder.Language.{0, 0}} (p : AuxiliarySorts E) {k : ℕ} :
    (language E).Relations k → Fin k → SortKind
  | .inl .field => fun _ => .field
  | .inl .residue => fun _ => .residue
  | .inl .value => fun _ => .value
  | .inr (.inl .residue) => fun _ => .residue
  | .inr (.inl .value) => fun _ => .value
  | .inr (.inl .valueLe) => fun _ => .value
  | .inr (.inr r) => fun i => auxiliaryKind (p.relationArgument r i)

inductive Literal
  | fieldZero | residueZero | valueOne | valueInfinity

def literalKind : Literal → SortKind
  | .fieldZero => .field
  | .residueZero => .residue
  | .valueOne | .valueInfinity => .value

def literalTerm {E : _root_.FirstOrder.Language.{0, 0}} {I : Type} : Literal → (language E).Term I
  | .fieldZero => fieldZero
  | .residueZero => auxiliaryConstant .rZero
  | .valueOne => auxiliaryConstant .gOne
  | .valueInfinity => auxiliaryConstant .gInfinity

def junk {E : _root_.FirstOrder.Language.{0, 0}} (p : AuxiliarySorts E) {k : ℕ}
    (f : (language E).Functions k) (s : Fin k → SortKind) : Literal :=
  match f with
  | .inl _ => .fieldZero
  | .inr (.inr .angular) => .residueZero
  | .inr (.inr .value) => .valueInfinity
  | .inr (.inl f) =>
    if ∃ i, s i = .field then .residueZero else
      if functionResult p (.inr (.inl f)) = .residue then .residueZero else .valueOne

def termSort {E : _root_.FirstOrder.Language.{0, 0}} (p : AuxiliarySorts E) {I : Type}
    (s : I → SortKind) : (language E).Term I → Option SortKind
  | .var i => some (s i)
  | .func f ts => if ∀ i, termSort p s (ts i) = some (functionArgument p f i)
      then some (functionResult p f) else none

theorem termSort_func {E : _root_.FirstOrder.Language.{0, 0}} (p : AuxiliarySorts E) {I : Type}
    (s : I → SortKind) {k : ℕ} (f : (language E).Functions k) (ts : Fin k → (language E).Term I)
    (t : SortKind) : termSort p s (.func f ts) = some t ↔
      (∀ i, termSort p s (ts i) = some (functionArgument p f i)) ∧ functionResult p f = t := by
  simp only [termSort]
  split_ifs with h <;> simp [h]

theorem literalTerm_sort {E : _root_.FirstOrder.Language.{0, 0}} (p : AuxiliarySorts E)
    {I : Type} (s : I → SortKind) (l : Literal) :
    termSort p s (literalTerm l) = some (literalKind l) := by
  cases l <;> simp [literalTerm, literalKind, fieldZero, auxiliaryConstant, termSort,
    functionResult, functionArgument, nativeAuxResult]

variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]

def Holds (E : _root_.FirstOrder.Language.{0, 0}) (v : Valuation K Γ) (a : Data v)
    (s : SortKind) (x : DenefPasAuxLift.Model E v a) : Prop :=
  match s with
  | .field => DenefPasLanguage.IsField x
  | .residue => ∃ r : Residue v, x = .inr (.inl r)
  | .value => ∃ g : Gamma v, x = .inr (.inr g)

def literalValue (E : _root_.FirstOrder.Language.{0, 0}) (v : Valuation K Γ) (a : Data v) :
    Literal → DenefPasAuxLift.Model E v a
  | .fieldZero => .inl 0
  | .residueZero => .inr (.inl 0)
  | .valueOne => .inr (.inr 1)
  | .valueInfinity => .inr (.inr 0)

theorem holds_unique (E : _root_.FirstOrder.Language.{0, 0}) (v : Valuation K Γ) (a : Data v)
    {s t : SortKind} {x : DenefPasAuxLift.Model E v a} (hs : Holds E v a s x) (ht : Holds E v a t x) : s = t := by
  cases s <;> cases t
  all_goals first | rfl | skip
  all_goals
    rcases hs with ⟨u, rfl⟩
    rcases ht with ⟨w, hw⟩
    cases hw

theorem literalValue_holds (E : _root_.FirstOrder.Language.{0, 0}) (v : Valuation K Γ) (a : Data v) (l : Literal) :
    Holds E v a (literalKind l) (literalValue E v a l) := by
  cases l <;> exact ⟨_, rfl⟩

section Semantics
variable (E : _root_.FirstOrder.Language.{0, 0}) (v : Valuation K Γ) (a : Data v) [E.Structure (Aux v)]
local instance : (language E).Structure (DenefPasAuxLift.Model E v a) := dpStructure E v a

theorem literalTerm_realize {I : Type} (l : Literal) (z : I → DenefPasAuxLift.Model E v a) :
    (literalTerm (E := E) l : (language E).Term I).realize z = literalValue E v a l := by
  cases l
  · exact fieldZero_realize E v a z
  all_goals simpa only [literalTerm, literalValue, constantValue] using auxiliaryConstant_realize E v a _ z

structure Canonical (p : AuxiliarySorts E) : Prop where
  functions : ∀ {k} (f : (language E).Functions k) (z : Fin k → DenefPasAuxLift.Model E v a),
    (∀ i, Holds E v a (functionArgument p f i) (z i)) →
      Holds E v a (functionResult p f) (Structure.funMap f z)
  junk : ∀ {k} (f : (language E).Functions k) (s : Fin k → SortKind)
    (z : Fin k → DenefPasAuxLift.Model E v a), (∀ i, Holds E v a (s i) (z i)) →
    ¬ (∀ i, s i = functionArgument p f i) → Structure.funMap f z = literalValue E v a (junk p f s)
  relations : ∀ {k} (r : (language E).Relations k) (z : Fin k → DenefPasAuxLift.Model E v a),
    Structure.RelMap r z → ∀ i, Holds E v a (relationArgument p r i) (z i)

end Semantics
end SpecialTransformations.Section6.DenefPasSorts
end
end

/-! Source: Section6.DenefPasSortedTerms -/
section

/-! Normalize raw tagged terms in the existing DP signature. The output is
properly sorted and keeps the value of the original totalized term. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language

namespace SpecialTransformations.Section6.DenefPasSorts
open AngularComponent DenefPasCodes DenefPasLanguage DenefPasParameters

def normalized {E : _root_.FirstOrder.Language.{0, 0}} (p : AuxiliarySorts E)
    {I : Type} (s : I → SortKind) : (language E).Term I → SortKind × (language E).Term I
  | .var i => (s i, .var i)
  | .func f ts =>
    let ns := fun i => normalized p s (ts i)
    if ∀ i, (ns i).1 = functionArgument p f i then
      (functionResult p f, .func f (fun i => (ns i).2))
    else (literalKind (junk p f (fun i => (ns i).1)),
      literalTerm (junk p f (fun i => (ns i).1)))

theorem normalized_sort {E : _root_.FirstOrder.Language.{0, 0}} (p : AuxiliarySorts E)
    {I : Type} (s : I → SortKind) (t : (language E).Term I) :
    termSort p s (normalized p s t).2 = some (normalized p s t).1 := by
  induction t with
  | var i => rfl
  | func f ts ih =>
    dsimp only [normalized]
    split_ifs with hp
    · apply (termSort_func p s f _ _).mpr
      exact ⟨fun i => (ih i).trans (congrArg some (hp i)), rfl⟩
    · exact literalTerm_sort p s _

section Semantics
variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]
variable (E : _root_.FirstOrder.Language.{0, 0}) (v : Valuation K Γ) (a : Data v)
variable [E.Structure (Aux v)]
local instance : (language E).Structure (DenefPasAuxLift.Model E v a) := dpStructure E v a

theorem normalized_spec (p : AuxiliarySorts E) (hc : Canonical E v a p)
    {I : Type} (s : I → SortKind) (t : (language E).Term I)
    (z : I → DenefPasAuxLift.Model E v a) (hz : ∀ i, Holds E v a (s i) (z i)) :
    Holds E v a (normalized p s t).1 ((normalized p s t).2.realize z) ∧
      (normalized p s t).2.realize z = t.realize z := by
  induction t with
  | var i => exact ⟨hz i, rfl⟩
  | func f ts ih =>
    have he : (fun i => (normalized p s (ts i)).2.realize z) =
        (fun i => (ts i).realize z) := funext (fun i => (ih i).2)
    dsimp only [normalized]
    split_ifs with hp
    · change Holds E v a (functionResult p f) (Structure.funMap f _) ∧ _
      constructor
      · apply hc.functions
        intro i
        rw [← hp i]
        exact (ih i).1
      · exact congrArg (Structure.funMap f) he
    · rw [literalTerm_realize]
      refine ⟨literalValue_holds E v a _, ?_⟩
      exact (hc.junk f _ _ (fun i => (ih i).1) hp).symm.trans
        (congrArg (Structure.funMap f) he)

end Semantics
end SpecialTransformations.Section6.DenefPasSorts
end
end

/-! Source: Section6.DenefPasSortedAtoms -/
section

/-! Proper many-sorted formulas inside the existing tagged DP language. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language

namespace SpecialTransformations.Section6.DenefPasSorts
open AngularComponent DenefPasCodes DenefPasLanguage DenefPasParameters

inductive WellSorted {E : _root_.FirstOrder.Language.{0, 0}} (p : AuxiliarySorts E)
    {I : Type} (s : I → SortKind) :
    {n : ℕ} → (Fin n → SortKind) → (language E).BoundedFormula I n → Prop
  | falsum {n} {sn : Fin n → SortKind} : WellSorted p s sn ⊥
  | equal {n} {sn : Fin n → SortKind} {t u : (language E).Term (I ⊕ Fin n)} {q : SortKind}
      (ht : termSort p (Sum.elim s sn) t = some q)
      (hu : termSort p (Sum.elim s sn) u = some q) : WellSorted p s sn (.equal t u)
  | rel {n} {sn : Fin n → SortKind} {k} (r : (language E).Relations k)
      (ts : Fin k → (language E).Term (I ⊕ Fin n))
      (ht : ∀ i, termSort p (Sum.elim s sn) (ts i) = some (relationArgument p r i)) :
      WellSorted p s sn (.rel r ts)
  | imp {n} {sn : Fin n → SortKind} {φ ψ : (language E).BoundedFormula I n}
      (hφ : WellSorted p s sn φ) (hψ : WellSorted p s sn ψ) : WellSorted p s sn (φ.imp ψ)
  | residue {n} {sn : Fin n → SortKind} {φ : (language E).BoundedFormula I (n + 1)}
      (hφ : WellSorted p s (Fin.snoc sn .residue) φ) : WellSorted p s sn (allResidue φ)
  | value {n} {sn : Fin n → SortKind} {φ : (language E).BoundedFormula I (n + 1)}
      (hφ : WellSorted p s (Fin.snoc sn .value) φ) : WellSorted p s sn (allValue φ)

theorem WellSorted.isFieldQF {E : _root_.FirstOrder.Language.{0, 0}} {p : AuxiliarySorts E}
    {I : Type} {s : I → SortKind} {n} {sn : Fin n → SortKind}
    {φ : (language E).BoundedFormula I n} (h : WellSorted p s sn φ) : IsFieldQF φ := by
  induction h with
  | falsum => exact .falsum
  | equal _ _ => exact .atomic (.equal _ _)
  | rel _ _ _ => exact .atomic (.rel _ _)
  | imp _ _ ihφ ihψ => exact .imp ihφ ihψ
  | residue _ ih => exact .residue ih
  | value _ ih => exact .value ih

def normalizedEqual {E : _root_.FirstOrder.Language.{0, 0}} (p : AuxiliarySorts E)
    {I : Type} {n} (s : I → SortKind) (sn : Fin n → SortKind)
    (t u : (language E).Term (I ⊕ Fin n)) : (language E).BoundedFormula I n :=
  let nt := normalized p (Sum.elim s sn) t
  let nu := normalized p (Sum.elim s sn) u
  if nt.1 = nu.1 then .equal nt.2 nu.2 else ⊥

theorem normalizedEqual_sorted {E : _root_.FirstOrder.Language.{0, 0}} (p : AuxiliarySorts E)
    {I : Type} {n} (s : I → SortKind) (sn : Fin n → SortKind)
    (t u : (language E).Term (I ⊕ Fin n)) : WellSorted p s sn (normalizedEqual p s sn t u) := by
  dsimp only [normalizedEqual]
  split_ifs with hp
  · exact .equal (normalized_sort p _ t) ((normalized_sort p _ u).trans (congrArg some hp.symm))
  · exact .falsum

def normalizedRel {E : _root_.FirstOrder.Language.{0, 0}} (p : AuxiliarySorts E)
    {I : Type} {n} (s : I → SortKind) (sn : Fin n → SortKind) {k}
    (r : (language E).Relations k) (ts : Fin k → (language E).Term (I ⊕ Fin n)) :
    (language E).BoundedFormula I n :=
  let ns := fun i => normalized p (Sum.elim s sn) (ts i)
  if ∀ i, (ns i).1 = relationArgument p r i then .rel r (fun i => (ns i).2) else ⊥

theorem normalizedRel_sorted {E : _root_.FirstOrder.Language.{0, 0}} (p : AuxiliarySorts E)
    {I : Type} {n} (s : I → SortKind) (sn : Fin n → SortKind) {k}
    (r : (language E).Relations k) (ts : Fin k → (language E).Term (I ⊕ Fin n)) :
    WellSorted p s sn (normalizedRel p s sn r ts) := by
  dsimp only [normalizedRel]
  split_ifs with hp
  · exact .rel r _ (fun i => (normalized_sort p _ (ts i)).trans (congrArg some (hp i)))
  · exact .falsum

section Semantics
variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]
variable (E : _root_.FirstOrder.Language.{0, 0}) (v : Valuation K Γ) (a : Data v)
variable [E.Structure (Aux v)]
local instance : (language E).Structure (DenefPasAuxLift.Model E v a) := dpStructure E v a

theorem holds_sumElim {I : Type} {n} (s : I → SortKind) (sn : Fin n → SortKind)
    (z : I → DenefPasAuxLift.Model E v a) (x : Fin n → DenefPasAuxLift.Model E v a)
    (hz : ∀ i, Holds E v a (s i) (z i)) (hx : ∀ i, Holds E v a (sn i) (x i)) :
    ∀ i, Holds E v a (Sum.elim s sn i) (Sum.elim z x i) := by
  intro i
  cases i with
  | inl i => exact hz i
  | inr i => exact hx i

theorem normalizedEqual_realize (p : AuxiliarySorts E) (hc : Canonical E v a p)
    {I : Type} {n} (s : I → SortKind) (sn : Fin n → SortKind)
    (t u : (language E).Term (I ⊕ Fin n))
    (z : I → DenefPasAuxLift.Model E v a) (x : Fin n → DenefPasAuxLift.Model E v a)
    (hz : ∀ i, Holds E v a (s i) (z i)) (hx : ∀ i, Holds E v a (sn i) (x i)) :
    (normalizedEqual p s sn t u).Realize z x ↔ (.equal t u : (language E).BoundedFormula I n).Realize z x := by
  have ht := normalized_spec E v a p hc (Sum.elim s sn) t (Sum.elim z x) (holds_sumElim E v a s sn z x hz hx)
  have hu := normalized_spec E v a p hc (Sum.elim s sn) u (Sum.elim z x) (holds_sumElim E v a s sn z x hz hx)
  dsimp only [normalizedEqual]
  split_ifs with hp
  · change _ = _ ↔ _ = _
    rw [ht.2, hu.2]
  · change False ↔ t.realize (Sum.elim z x) = u.realize (Sum.elim z x)
    apply iff_of_false (fun h => h)
    intro he
    apply hp
    exact holds_unique E v a (ht.2 ▸ ht.1) (he.symm ▸ (hu.2 ▸ hu.1))

theorem normalizedRel_realize (p : AuxiliarySorts E) (hc : Canonical E v a p)
    {I : Type} {n} (s : I → SortKind) (sn : Fin n → SortKind) {k}
    (r : (language E).Relations k) (ts : Fin k → (language E).Term (I ⊕ Fin n))
    (z : I → DenefPasAuxLift.Model E v a) (x : Fin n → DenefPasAuxLift.Model E v a)
    (hz : ∀ i, Holds E v a (s i) (z i)) (hx : ∀ i, Holds E v a (sn i) (x i)) :
    (normalizedRel p s sn r ts).Realize z x ↔ (.rel r ts : (language E).BoundedFormula I n).Realize z x := by
  have ht i := normalized_spec E v a p hc (Sum.elim s sn) (ts i) (Sum.elim z x)
    (holds_sumElim E v a s sn z x hz hx)
  have he : (fun i => (normalized p (Sum.elim s sn) (ts i)).2.realize (Sum.elim z x)) =
      (fun i => (ts i).realize (Sum.elim z x)) := funext (fun i => (ht i).2)
  dsimp only [normalizedRel]
  split_ifs with hp
  · change Structure.RelMap r _ ↔ Structure.RelMap r _
    rw [he]
  · change False ↔ Structure.RelMap r (fun i => (ts i).realize (Sum.elim z x))
    apply iff_of_false (fun h => h)
    intro hr
    apply hp
    intro i
    exact holds_unique E v a ((ht i).2 ▸ (ht i).1) (hc.relations r _ hr i)

end Semantics
end SpecialTransformations.Section6.DenefPasSorts
end
end

/-! Source: Section6.DenefPasSortedFormula -/
section

/-! Uniform proper-sort normalization preserves the absence of field
quantifiers. Quantifiers already in RF or Gamma remain in that sort. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language

namespace SpecialTransformations.Section6.DenefPasSorts
open AngularComponent DenefPasCodes DenefPasLanguage DenefPasParameters

def Equivalent {E : _root_.FirstOrder.Language.{0, 0}} (p : AuxiliarySorts E)
    {I : Type} {n} (s : I → SortKind) (sn : Fin n → SortKind)
    (φ ψ : (language E).BoundedFormula I n) : Prop :=
  ∀ (K Γ : Type) [Field K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) (a : Data v) [E.Structure (Aux v)],
    Canonical E v a p →
    letI : (language E).Structure (DenefPasAuxLift.Model E v a) := dpStructure E v a
    ∀ (z : I → DenefPasAuxLift.Model E v a) (x : Fin n → DenefPasAuxLift.Model E v a),
      (∀ i, Holds E v a (s i) (z i)) → (∀ i, Holds E v a (sn i) (x i)) →
        (φ.Realize z x ↔ ψ.Realize z x)

theorem holds_snoc {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (E : _root_.FirstOrder.Language.{0, 0}) (v : Valuation K Γ) (a : Data v)
    {n} (sn : Fin n → SortKind) (x : Fin n → DenefPasAuxLift.Model E v a)
    (hx : ∀ i, Holds E v a (sn i) (x i)) (q : SortKind) (b : DenefPasAuxLift.Model E v a)
    (hb : Holds E v a q b) :
    ∀ i, Holds E v a (Fin.snoc (α := fun _ => SortKind) sn q i)
      (Fin.snoc (α := fun _ => DenefPasAuxLift.Model E v a) x b i) := by
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa only [Fin.snoc_last] using hb
  · simpa only [Fin.snoc_castSucc] using hx j

theorem normalize {E : _root_.FirstOrder.Language.{0, 0}} (p : AuxiliarySorts E)
    {I : Type} (s : I → SortKind) {n} {φ : (language E).BoundedFormula I n}
    (hφ : IsFieldQF φ) (sn : Fin n → SortKind) :
    ∃ ψ : (language E).BoundedFormula I n, WellSorted p s sn ψ ∧ Equivalent p s sn φ ψ := by
  induction hφ with
  | falsum =>
    refine ⟨⊥, .falsum, ?_⟩
    intro K Γ _ _ v a _ hc z x hz hx
    rfl
  | atomic h =>
    cases h with
    | equal t u =>
      refine ⟨normalizedEqual p s sn t u, normalizedEqual_sorted p s sn t u, ?_⟩
      intro K Γ _ _ v a _ hc z x hz hx
      exact (normalizedEqual_realize E v a p hc s sn t u z x hz hx).symm
    | rel r ts =>
      refine ⟨normalizedRel p s sn r ts, normalizedRel_sorted p s sn r ts, ?_⟩
      intro K Γ _ _ v a _ hc z x hz hx
      exact (normalizedRel_realize E v a p hc s sn r ts z x hz hx).symm
  | imp hφ hψ ihφ ihψ =>
    obtain ⟨φ', hφ', eφ⟩ := ihφ sn
    obtain ⟨ψ', hψ', eψ⟩ := ihψ sn
    refine ⟨φ'.imp ψ', .imp hφ' hψ', ?_⟩
    intro K Γ _ _ v a _ hc z x hz hx
    exact imp_congr (eφ K Γ v a hc z x hz hx) (eψ K Γ v a hc z x hz hx)
  | residue hφ ih =>
    obtain ⟨ψ, hψ, he⟩ := ih (Fin.snoc sn .residue)
    refine ⟨allResidue ψ, .residue hψ, ?_⟩
    intro K Γ _ _ v a _ hc z x hz hx
    letI : (language E).Structure (DenefPasAuxLift.Model E v a) := dpStructure E v a
    rw [DenefPasAuxLift.allResidue_realize, DenefPasAuxLift.allResidue_realize]
    apply forall_congr'
    intro r
    exact he K Γ v a hc z (Fin.snoc x (Sum.inr (Sum.inl r))) hz
      (holds_snoc E v a sn x hx .residue _ ⟨r, rfl⟩)
  | value hφ ih =>
    obtain ⟨ψ, hψ, he⟩ := ih (Fin.snoc sn .value)
    refine ⟨allValue ψ, .value hψ, ?_⟩
    intro K Γ _ _ v a _ hc z x hz hx
    letI : (language E).Structure (DenefPasAuxLift.Model E v a) := dpStructure E v a
    rw [DenefPasAuxLift.allValue_realize, DenefPasAuxLift.allValue_realize]
    apply forall_congr'
    intro g
    exact he K Γ v a hc z (Fin.snoc x (Sum.inr (Sum.inr g))) hz
      (holds_snoc E v a sn x hx .value _ ⟨g, rfl⟩)

end SpecialTransformations.Section6.DenefPasSorts
end
end

/-! Source: Section6.DenefPasCorollary -/
section

/-! Corollary 6.5 for proper sorted presentations of the Denef-Pas language.
`Canonical` records only primitive symbol typing and the chosen values of
ill-sorted applications in the tagged encoding. It contains no elimination
or definability premise. The output uses the original parameter names. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language

namespace SpecialTransformations.Section6.DenefPasCorollary
open AngularComponent DenefPasCodes DenefPasLanguage DenefPasParameters DenefPasSorts

theorem corollary_6_5 (hRecognition : DenefPasHenselianModels.OrdinaryRecognition)
    (E : _root_.FirstOrder.Language.{0, 0}) (p : AuxiliarySorts E)
    (hEarlier : EnvelopeUniformity.EarlierPreparation)
    (hEnv : UniformNormalizedElimination.NativeEnvelopes (DenefPasMorley.signature E))
    (hNormal : HenselianElimination.RVLiteralNormalForm (DenefPasMorley.signature E))
    {I : Type} (s : I → SortKind) (φ : (language E).Formula I) :
    ∃ ψ : (language E).Formula I, WellSorted p s Fin.elim0 ψ ∧ IsFieldQF ψ ∧
      ∀ (K Γ : Type) [Field K] [LinearOrderedCommGroupWithZero Γ]
        (v : Valuation K Γ) (a : Data v) [CharZero K] [CharZero (Residue v)]
        [HenselianLocalRing v.valuationSubring] [E.Structure (Aux v)],
        Canonical E v a p →
        letI : (language E).Structure (DenefPasAuxLift.Model E v a) := dpStructure E v a
        ∀ z : I → DenefPasAuxLift.Model E v a, Sorted E v a s z →
          (φ.Realize z ↔ ψ.Realize z) := by
  obtain ⟨χ, hχ, heχ⟩ := DenefPasFreeParameters.encoded_corollary_6_5 hRecognition E
    hEarlier hEnv hNormal s φ
  obtain ⟨ψ, hsψ, heψ⟩ := normalize p s hχ Fin.elim0
  refine ⟨ψ, hsψ, hsψ.isFieldQF, ?_⟩
  intro K Γ _ _ v a _ _ _ _ hc
  letI : (language E).Structure (DenefPasAuxLift.Model E v a) := dpStructure E v a
  intro z hz
  exact (heχ K Γ v a z hz).trans (heψ K Γ v a hc z default hz (fun i => i.elim0))

end SpecialTransformations.Section6.DenefPasCorollary
end
end

/-! Source: Section6.DenefPasCanonical -/
section

/-! The primitive sort laws of the ordinary DP symbols are proved here.
Only the interpretations of the optional auxiliary expansion are supplied
by the user of an expanded language. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.Section6.DenefPasLanguage.language
  SpecialTransformations.Section6.DenefPasAux.auxLanguage FirstOrder.Language.sum
open Classical FirstOrder FirstOrder.Language

namespace SpecialTransformations.Section6.DenefPasSorts
open AngularComponent DenefPasCodes DenefPasLanguage DenefPasParameters

def AuxHolds {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]
    {v : Valuation K Γ} (b : Bool) (d : Aux v) : Prop :=
  if b then ∃ g : Gamma v, d = .inr g else ∃ r : Residue v, d = .inl r

def auxDefault {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) (b : Bool) : Aux v := if b then .inr 1 else .inl 0

section Semantics
variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]
variable (E : _root_.FirstOrder.Language.{0, 0}) (v : Valuation K Γ) (a : Data v)
variable [E.Structure (Aux v)]
local instance : (language E).Structure (DenefPasAuxLift.Model E v a) := dpStructure E v a
local instance : DenefPasAux.auxLanguage.Structure (Aux v) := DenefPasAux.auxStructure
local instance : (DenefPasAux.auxLanguage.sum E).Structure (Aux v) :=
  FirstOrder.Language.sumStructure DenefPasAux.auxLanguage E (Aux v)

structure AuxiliaryCanonical (p : AuxiliarySorts E) : Prop where
  functions : ∀ {k} (f : E.Functions k) (z : Fin k → Aux v),
    AuxHolds (p.functionResult f) (Structure.funMap f z)
  junk : ∀ {k} (f : E.Functions k) (z : Fin k → Aux v),
    ¬ (∀ i, AuxHolds (p.functionArgument f i) (z i)) →
      Structure.funMap f z = auxDefault v (p.functionResult f)
  relations : ∀ {k} (r : E.Relations k) (z : Fin k → Aux v),
    Structure.RelMap r z → ∀ i, AuxHolds (p.relationArgument r i) (z i)

theorem auxHolds_iff (b : Bool) (d : Aux v) :
    AuxHolds b d ↔ Holds E v a (auxiliaryKind b) (Sum.inr d) := by
  cases b <;> dsimp [AuxHolds, Holds, auxiliaryKind]
  all_goals
    apply exists_congr
    intro r
    exact ⟨fun h => congrArg Sum.inr h, fun h => Sum.inr.inj h⟩

theorem nativeAux_holds {k} (f : DenefPasAux.Functions k) (z : Fin k → Aux v) :
    Holds E v a (nativeAuxResult f) (Sum.inr (Structure.funMap (L := DenefPasAux.auxLanguage) f z)) := by
  cases f
  all_goals
    simp only [Structure.funMap, DenefPasAux.auxStructure, nativeAuxResult, Holds]
  all_goals first | exact ⟨_, rfl⟩ | skip
  all_goals cases hz0 : z 0
  all_goals try cases hz1 : z 1
  all_goals simp only [hz0, hz1]
  all_goals exact ⟨_, rfl⟩

theorem holds_isAux {q : SortKind} {x : DenefPasAuxLift.Model E v a}
    (hq : q ≠ .field) (hx : Holds E v a q x) : DenefPasLanguage.IsAux x := by
  cases q with
  | field => exact (hq rfl).elim
  | residue => obtain ⟨r, rfl⟩ := hx; exact ⟨.inl r, rfl⟩
  | value => obtain ⟨g, rfl⟩ := hx; exact ⟨.inr g, rfl⟩

theorem auxiliaryArgument_ne_field (p : AuxiliarySorts E) {k}
    (f : (DenefPasAux.auxLanguage.sum E).Functions k) (i : Fin k) :
    functionArgument p (.inr (.inl f)) i ≠ .field := by
  cases f with
  | inl f => cases f <;> simp [functionArgument, nativeAuxResult]
  | inr f => cases hb : p.functionArgument f i <;> simp [functionArgument, auxiliaryKind, hb]

theorem canonical_functions (p : AuxiliarySorts E) (he : AuxiliaryCanonical E v p)
    {k} (f : (language E).Functions k) (z : Fin k → DenefPasAuxLift.Model E v a)
    (hz : ∀ i, Holds E v a (functionArgument p f i) (z i)) :
    Holds E v a (functionResult p f) (Structure.funMap f z) := by
  cases f with
  | inl f => exact ⟨_, rfl⟩
  | inr f =>
    cases f with
    | inl f =>
      have haux : ∀ i, DenefPasLanguage.IsAux (z i) :=
        fun i => holds_isAux E v a (auxiliaryArgument_ne_field E p f i) (hz i)
      change Holds E v a _ (if ∀ i, DenefPasLanguage.IsAux (z i) then _ else _)
      rw [if_pos haux]
      cases f with
      | inl f => exact nativeAux_holds E v a f (fun i => auxValue (z i))
      | inr f => exact (auxHolds_iff E v a _ _).mp (he.functions f (fun i => auxValue (z i)))
    | inr f => cases f <;> exact ⟨_, rfl⟩

theorem nativeAux_offsort {k} (f : DenefPasAux.Functions k) (z : Fin k → Aux v)
    (hs : ¬ ∀ i, Holds E v a (nativeAuxResult f) (Sum.inr (z i))) :
    Structure.funMap (L := DenefPasAux.auxLanguage) f z =
      (if nativeAuxResult f = .residue then Sum.inl 0 else Sum.inr 1) := by
  cases f
  all_goals first | exact (hs (fun i => i.elim0)).elim | skip
  all_goals cases hz0 : z 0
  all_goals try cases hz1 : z 1
  all_goals simp [Structure.funMap, DenefPasAux.auxStructure, nativeAuxResult, hz0, hz1]
  all_goals
    exfalso
    apply hs
    intro i
    fin_cases i <;> first | exact ⟨_, congrArg Sum.inr hz0⟩ | exact ⟨_, congrArg Sum.inr hz1⟩

theorem holds_tag_not_field {q : SortKind} {d : Aux v}
    (h : Holds E v a q (Sum.inr d)) : q ≠ .field := by
  intro he
  rw [he] at h
  obtain ⟨x, hx⟩ := h
  cases hx

theorem nativeAux_junk (p : AuxiliarySorts E) {k} (f : DenefPasAux.Functions k)
    (s : Fin k → SortKind) (z : Fin k → DenefPasAuxLift.Model E v a)
    (hz : ∀ i, Holds E v a (s i) (z i)) (haux : ∀ i, DenefPasLanguage.IsAux (z i))
    (hs : ¬ ∀ i, s i = functionArgument p (.inr (.inl (.inl f))) i) :
    Structure.funMap (L := language E) (.inr (.inl (.inl f))) z =
      literalValue E v a (junk p (.inr (.inl (.inl f))) s) := by
  have htag i : z i = Sum.inr (auxValue (z i)) := by
    obtain ⟨d, hd⟩ := haux i
    simpa only [hd, auxValue] using hd
  have hnf : ¬ ∃ i, s i = .field := by
    rintro ⟨i, hi⟩
    exact holds_tag_not_field E v a (htag i ▸ hz i) hi
  have hwrong : ¬ ∀ i, Holds E v a (nativeAuxResult f) (Sum.inr (auxValue (z i))) := by
    intro ht
    apply hs
    intro i
    exact holds_unique E v a (htag i ▸ hz i) (ht i)
  have he := nativeAux_offsort E v a f (fun i => auxValue (z i)) hwrong
  change (if ∀ i, DenefPasLanguage.IsAux (z i) then _ else _) = _
  rw [if_pos haux]
  change Sum.inr (Structure.funMap (L := DenefPasAux.auxLanguage) f (fun i => auxValue (z i))) = _
  rw [he]
  simp only [junk, hnf, ↓reduceIte, functionResult]
  split_ifs <;> rfl

theorem expansion_junk (p : AuxiliarySorts E) (he : AuxiliaryCanonical E v p) {k} (f : E.Functions k)
    (s : Fin k → SortKind) (z : Fin k → DenefPasAuxLift.Model E v a)
    (hz : ∀ i, Holds E v a (s i) (z i)) (haux : ∀ i, DenefPasLanguage.IsAux (z i))
    (hs : ¬ ∀ i, s i = functionArgument p (.inr (.inl (.inr f))) i) :
    Structure.funMap (L := language E) (.inr (.inl (.inr f))) z =
      literalValue E v a (junk p (.inr (.inl (.inr f))) s) := by
  have htag i : z i = Sum.inr (auxValue (z i)) := by
    obtain ⟨d, hd⟩ := haux i
    simpa only [hd, auxValue] using hd
  have hnf : ¬ ∃ i, s i = .field := by
    rintro ⟨i, hi⟩
    exact holds_tag_not_field E v a (htag i ▸ hz i) hi
  have hwrong : ¬ ∀ i, AuxHolds (p.functionArgument f i) (auxValue (z i)) := by
    intro ht
    apply hs
    intro i
    exact holds_unique E v a (htag i ▸ hz i) ((auxHolds_iff E v a _ _).mp (ht i))
  change (if ∀ i, DenefPasLanguage.IsAux (z i) then _ else _) = _
  rw [if_pos haux]
  change Sum.inr (Structure.funMap (L := E) f (fun i => auxValue (z i))) = _
  rw [he.junk f _ hwrong]
  cases hb : p.functionResult f <;>
    simp [auxDefault, junk, hnf, functionResult, auxiliaryKind, hb, literalValue]

theorem auxiliary_field_junk (p : AuxiliarySorts E) {k}
    (f : (DenefPasAux.auxLanguage.sum E).Functions k) (s : Fin k → SortKind)
    (z : Fin k → DenefPasAuxLift.Model E v a) (hz : ∀ i, Holds E v a (s i) (z i))
    (hn : ¬ ∀ i, DenefPasLanguage.IsAux (z i)) :
    Structure.funMap (L := language E) (.inr (.inl f)) z =
      literalValue E v a (junk p (.inr (.inl f)) s) := by
  have hs : ∃ i, s i = .field := by
    by_contra h
    apply hn
    intro i
    apply holds_isAux E v a _ (hz i)
    exact fun hi => h ⟨i, hi⟩
  change (if ∀ i, DenefPasLanguage.IsAux (z i) then _ else _) = _
  simp only [if_neg hn, junk, if_pos hs, literalValue]

theorem canonical_junk (p : AuxiliarySorts E) (he : AuxiliaryCanonical E v p)
    {k} (f : (language E).Functions k) (s : Fin k → SortKind)
    (z : Fin k → DenefPasAuxLift.Model E v a) (hz : ∀ i, Holds E v a (s i) (z i))
    (hs : ¬ ∀ i, s i = functionArgument p f i) :
    Structure.funMap f z = literalValue E v a (junk p f s) := by
  cases f with
  | inl f =>
    have hn : ¬ ∀ i, DenefPasLanguage.IsField (z i) := by
      intro ht
      apply hs
      intro i
      exact holds_unique E v a (hz i) (ht i)
    simp [Structure.funMap, dpStructure, fieldFunction, hn, junk, literalValue]
  | inr f =>
    cases f with
    | inl f =>
      by_cases haux : ∀ i, DenefPasLanguage.IsAux (z i)
      · cases f with
        | inl f => exact nativeAux_junk E v a p f s z hz haux hs
        | inr f => exact expansion_junk E v a p he f s z hz haux hs
      · exact auxiliary_field_junk E v a p f s z hz haux
    | inr f =>
      cases f
      all_goals
        have hn : ¬ DenefPasLanguage.IsField (z 0) := by
          intro h
          apply hs
          intro i
          fin_cases i
          exact holds_unique E v a (hz 0) h
        cases h0 : z 0 with
        | inl x => exact (hn ⟨x, h0⟩).elim
        | inr d =>
          simp [Structure.funMap, dpStructure, h0, fieldValue, junk, literalValue,
            map_zero, RVCalc.rv_zero, gammaValue]

theorem nativeRel_holds (p : AuxiliarySorts E) {k} (r : DenefPasAux.Relations k)
    (z : Fin k → Aux v) (hr : Structure.RelMap (L := DenefPasAux.auxLanguage) r z) :
    ∀ i, Holds E v a (relationArgument p (.inr (.inl r)) i) (Sum.inr (z i)) := by
  cases r with
  | residue =>
    obtain ⟨r, hr⟩ := hr
    intro i
    fin_cases i
    exact ⟨r, congrArg Sum.inr hr⟩
  | value =>
    obtain ⟨g, hg⟩ := hr
    intro i
    fin_cases i
    exact ⟨g, congrArg Sum.inr hg⟩
  | valueLe =>
    obtain ⟨g, h, hg, hh, hle⟩ := hr
    intro i
    fin_cases i
    · exact ⟨g, congrArg Sum.inr hg⟩
    · exact ⟨h, congrArg Sum.inr hh⟩

theorem canonical_relations (p : AuxiliarySorts E) (he : AuxiliaryCanonical E v p)
    {k} (r : (language E).Relations k) (z : Fin k → DenefPasAuxLift.Model E v a)
    (hr : Structure.RelMap r z) : ∀ i, Holds E v a (relationArgument p r i) (z i) := by
  cases r with
  | inl r => cases r <;> intro i <;> fin_cases i <;> exact hr
  | inr r =>
    change (∀ i, DenefPasLanguage.IsAux (z i)) ∧
      Structure.RelMap (L := DenefPasAux.auxLanguage.sum E) r (fun i => auxValue (z i)) at hr
    have htag i : z i = Sum.inr (auxValue (z i)) := by
      obtain ⟨d, hd⟩ := hr.1 i
      simpa only [hd, auxValue] using hd
    cases r with
    | inl r =>
      intro i
      exact (htag i).symm ▸ nativeRel_holds E v a p r _ hr.2 i
    | inr r =>
      intro i
      exact (htag i).symm ▸ (auxHolds_iff E v a _ _).mp (he.relations r _ hr.2 i)

theorem canonical (p : AuxiliarySorts E) (he : AuxiliaryCanonical E v p) : Canonical E v a p :=
  ⟨canonical_functions E v a p he, canonical_junk E v a p he, canonical_relations E v a p he⟩

end Semantics
end SpecialTransformations.Section6.DenefPasSorts
end
end

/-! Source: Section6.DenefPasAuxiliaryStructure -/
section

/-! Arbitrary genuinely sorted auxiliary expansions. Their symbols are
interpreted by maps between the declared RF/Gamma sorts. The canonical
tagged interpretation and all of its sort laws are constructed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language

namespace SpecialTransformations.Section6.DenefPasSorts
open AngularComponent DenefPasCodes DenefPasLanguage DenefPasParameters

variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]

def AuxCarrier (v : Valuation K Γ) (b : Bool) : Type := if b then Gamma v else Residue v

def toAux (v : Valuation K Γ) : (b : Bool) → AuxCarrier v b → Aux v
  | false, r => .inl r
  | true, g => .inr g

def fromAux (v : Valuation K Γ) : (b : Bool) → Aux v → AuxCarrier v b
  | false, d => DenefPasAux.residue (R := Residue v) (G := Gamma v) d
  | true, d => DenefPasAux.value (R := Residue v) (G := Gamma v) d

theorem toAux_holds (v : Valuation K Γ) (b : Bool) (x : AuxCarrier v b) : AuxHolds b (toAux v b x) := by
  cases b <;> exact ⟨_, rfl⟩

theorem auxDefault_holds (v : Valuation K Γ) (b : Bool) : AuxHolds b (auxDefault v b) := by
  cases b <;> exact ⟨_, rfl⟩

structure AuxiliaryStructure {E : _root_.FirstOrder.Language.{0, 0}}
    (p : AuxiliarySorts E) (v : Valuation K Γ) where
  functions : ∀ {k} (f : E.Functions k),
    ((i : Fin k) → AuxCarrier v (p.functionArgument f i)) → AuxCarrier v (p.functionResult f)
  relations : ∀ {k} (r : E.Relations k),
    ((i : Fin k) → AuxCarrier v (p.relationArgument r i)) → Prop

def auxiliaryStructure {E : _root_.FirstOrder.Language.{0, 0}} (p : AuxiliarySorts E)
    (v : Valuation K Γ) (d : AuxiliaryStructure p v) : E.Structure (Aux v) where
  funMap f z := if ∀ i, AuxHolds (p.functionArgument f i) (z i) then
    toAux v (p.functionResult f) (d.functions f (fun i => fromAux v (p.functionArgument f i) (z i)))
    else auxDefault v (p.functionResult f)
  RelMap r z := (∀ i, AuxHolds (p.relationArgument r i) (z i)) ∧
    d.relations r (fun i => fromAux v (p.relationArgument r i) (z i))

theorem auxiliaryStructure_canonical {E : _root_.FirstOrder.Language.{0, 0}} (p : AuxiliarySorts E)
    (v : Valuation K Γ) (d : AuxiliaryStructure p v) :
    letI : E.Structure (Aux v) := auxiliaryStructure p v d
    AuxiliaryCanonical E v p := by
  letI : E.Structure (Aux v) := auxiliaryStructure p v d
  constructor
  · intro k f z
    change AuxHolds _ (if _ then _ else _)
    split_ifs
    · exact toAux_holds v _ _
    · exact auxDefault_holds v _
  · intro k f z hn
    change (if _ then _ else _) = _
    exact if_neg hn
  · intro k r z hr
    exact hr.1

theorem dpStructure_canonical {E : _root_.FirstOrder.Language.{0, 0}} (p : AuxiliarySorts E)
    (v : Valuation K Γ) (a : Data v) (d : AuxiliaryStructure p v) :
    letI : E.Structure (Aux v) := auxiliaryStructure p v d
    Canonical E v a p := by
  letI : E.Structure (Aux v) := auxiliaryStructure p v d
  exact canonical E v a p (auxiliaryStructure_canonical p v d)

end SpecialTransformations.Section6.DenefPasSorts
end
end

/-! Source: Section6.DenefPasTheorem -/
section

/-! Corollary 6.5 with genuinely sorted arbitrary auxiliary expansions.
All DP interpretation and sorting laws are constructed from the actual
field, valuation, angular component, and sorted auxiliary symbol maps. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language

namespace SpecialTransformations.Section6.DenefPasTheorem
open AngularComponent DenefPasCodes DenefPasLanguage DenefPasParameters DenefPasSorts

theorem corollary_6_5 (hRecognition : DenefPasHenselianModels.OrdinaryRecognition)
    (E : _root_.FirstOrder.Language.{0, 0}) (p : AuxiliarySorts E)
    (hEarlier : EnvelopeUniformity.EarlierPreparation)
    (hEnv : UniformNormalizedElimination.NativeEnvelopes (DenefPasMorley.signature E))
    (hNormal : HenselianElimination.RVLiteralNormalForm (DenefPasMorley.signature E))
    {I : Type} (s : I → SortKind) (φ : (language E).Formula I) :
    ∃ ψ : (language E).Formula I, WellSorted p s Fin.elim0 ψ ∧ IsFieldQF ψ ∧
      ∀ (K Γ : Type) [Field K] [LinearOrderedCommGroupWithZero Γ]
        (v : Valuation K Γ) (a : Data v) [CharZero K] [CharZero (Residue v)]
        [HenselianLocalRing v.valuationSubring] (d : AuxiliaryStructure p v),
        letI : E.Structure (Aux v) := auxiliaryStructure p v d
        letI : (language E).Structure (DenefPasAuxLift.Model E v a) := dpStructure E v a
        ∀ z : I → DenefPasAuxLift.Model E v a, Sorted E v a s z →
          (φ.Realize z ↔ ψ.Realize z) := by
  obtain ⟨ψ, hsψ, hψ, heψ⟩ := DenefPasCorollary.corollary_6_5 hRecognition E p
    hEarlier hEnv hNormal s φ
  refine ⟨ψ, hsψ, hψ, ?_⟩
  intro K Γ _ _ v a _ _ _ d
  letI : E.Structure (Aux v) := auxiliaryStructure p v d
  letI : (language E).Structure (DenefPasAuxLift.Model E v a) := dpStructure E v a
  exact heψ K Γ v a (dpStructure_canonical p v a d)

end SpecialTransformations.Section6.DenefPasTheorem
end
end

