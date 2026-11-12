module

public import Section6.AlignedComparison
public import Section6.AngularCodes
public import Section6.AngularComponent
public import Section6.AngularOrderCodes
public import Section6.AuxiliaryDenaming
public import Section6.CanonicalEmbedding
public import Section6.CommonEnvelopeComparison
public import Section6.ContractionGraph
public import Section6.DefinableMaps
public import Section6.DenefPasAlgebra
public import Section6.ElementaryTestFamily
public import Section6.ElementaryTransfer
public import Section6.EnvelopeUniformity
public import Section6.ExpandedImages
public import Section6.ExpandedLiterals
public import Section6.ExpandedLogic
public import Section6.ExpandedOpenBounds
public import Section6.ExpandedParameterRelabel
public import Section6.ExpandedRenaming
public import Section6.ExpandedRestriction
public import Section6.ExtraSortSemantics
public import Section6.FVBinding
public import Section6.FiniteAbstraction
public import Section6.FiniteCover
public import Section6.FiniteNamedSyntax
public import Section6.FiniteNormalizedElimination
public import Section6.FiniteParameterSyntax
public import Section6.FiniteSortContext
public import Section6.FragmentCompactness
public import Section6.FunctionalClosure
public import Section6.GeneratedDenaming
public import Section6.GeneratedParameters
public import Section6.HenselianClosure
public import Section6.HenselianElimination
public import Section6.HenselianImages
public import Section6.HenselianInputs
public import Section6.HenselianModel
public import Section6.HenselianTheory
public import Section6.MapFormulaDescent
public import Section6.NamedLanguage
public import Section6.NativeAmalgamation
public import Section6.NativeExpandedSyntax
public import Section6.NativeFormulaElimination
public import Section6.NativeImageComparison
public import Section6.NativeImageTransport
public import Section6.NativeOccurrence
public import Section6.NativeTermMap
public import Section6.NativeTerms
public import Section6.NormalizedQuery
public import Section6.OneStepPresentation
public import Section6.PairInterpretation
public import Section6.PairSyntax
public import Section6.ParameterNaming
public import Section6.PolynomialDescent
public import Section6.PolynomialFormulaDescent
public import Section6.PreparedDescent
public import Section6.RVAbstraction
public import Section6.RVExpansionTransport
public import Section6.RVFormula
public import Section6.RVFragmentRenaming
public import Section6.RVGraphExpansion
public import Section6.RVGraphLanguage
public import Section6.RVQuotients
public import Section6.RVSourceFormula
public import Section6.RVSubstructure
public import Section6.RVTermSupport
public import Section6.RelativeSyntax
public import Section6.SentenceDenaming
public import Section6.SortedFragment
public import Section6.SyntacticDescent
public import Section6.SyntacticLemma63
public import Section6.TypedNativeTerms
public import Section6.UniformNormalizedElimination
public import TypedModelMap

@[expose] public section

/-! Coherent Section 6 module. The source bodies below are retained
from the individually developed fragments; only imports and file scope
are consolidated. The exported names and mathematical statements remain. -/

/-! Source: Section6.TrivialAngularComponent -/
section

/-! In the trivial-valuation case the angular component is an actual
field isomorphism to the residue field. This supplies the separate algebraic
bridge needed before applying a field-quantifier elimination statement that
includes trivially valued models. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical

namespace SpecialTransformations.Section6.AngularComponent
variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]

def Trivial (v : Valuation K Γ) : Prop := ∀ x : K, x ≠ 0 → v x = 1

def trivialInclusion (v : Valuation K Γ) (h : Trivial v) : K →+* v.valuationSubring where
  toFun x := ⟨x, by
    change v x ≤ 1
    by_cases hx : x = 0
    · subst x
      simp only [map_zero, zero_le_one]
    · rw [h x hx]⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

def trivialResidueMap (v : Valuation K Γ) (h : Trivial v) : K →+* Residue v :=
  (IsLocalRing.residue v.valuationSubring).comp (trivialInclusion v h)

theorem trivialResidueMap_surjective (v : Valuation K Γ) (h : Trivial v) :
    Function.Surjective (trivialResidueMap v h) := by
  intro r
  obtain ⟨x, hx⟩ := IsLocalRing.residue_surjective r
  refine ⟨(x : K), ?_⟩
  change IsLocalRing.residue v.valuationSubring (trivialInclusion v h (x : K)) = r
  have he : trivialInclusion v h (x : K) = x := Subtype.ext rfl
  rw [he]
  exact hx

theorem trivialResidueMap_eq_ac (v : Valuation K Γ) (a : Data v) (h : Trivial v) (x : K) :
    trivialResidueMap v h x = a.ac x := by
  by_cases hx : x = 0
  · subst x
    rw [map_zero, map_zero]
  · exact (a.agrees (trivialInclusion v h x) (h x hx)).symm

def trivialAcEquiv (v : Valuation K Γ) (a : Data v) (h : Trivial v) : K ≃+* Residue v :=
  RingEquiv.ofBijective (trivialResidueMap v h)
    ⟨(trivialResidueMap v h).injective, trivialResidueMap_surjective v h⟩

theorem trivialAcEquiv_apply (v : Valuation K Γ) (a : Data v) (h : Trivial v) (x : K) :
    trivialAcEquiv v a h x = a.ac x := trivialResidueMap_eq_ac v a h x

end SpecialTransformations.Section6.AngularComponent
end
end

/-! Source: Section6.DenefPasNativeDictionary -/
section

/-! The fixed native RV atomic dictionary in DP auxiliary syntax. This
uses the published RV-only function/relation symbols and the actual quotient
interpretation defined in DenefPasRV. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Section6.DenefPasNativeDictionary
open DenefPasAux DenefPasCodes AngularComponent RVAbstraction RVGraphLanguage

abbrev FunctionContext (k : ℕ) := (Fin k × Coord) ⊕ Coord

def arg {k : ℕ} (i : Fin k) (b : Coord) : auxLanguage.Term (FunctionContext k) := .var (.inl (i, b))
def output {k : ℕ} (b : Coord) : auxLanguage.Term (FunctionContext k) := .var (.inr b)
def relArg {k : ℕ} (i : Fin k) (b : Coord) : auxLanguage.Term (Fin k × Coord) := .var (i, b)

def units {I : Type} (p : Coord → auxLanguage.Term I) : auxLanguage.Formula I :=
  (DenefPasEquality.zero p).not ⊓
    (DenefPasEquality.g p).equal (Constants.term (L := auxLanguage) Functions.gOne)

def functionGraph {k : ℕ} (f : RVFunction k) : auxLanguage.Formula (FunctionContext k) :=
  match f.val with
  | .rvZero => DenefPasEquality.zero output
  | .rvOne => DenefPasEquality.equal output DenefPasInverse.one
  | .rvMul => DenefPasMultiplication.graph (arg 0) (arg 1) output
  | .rvInv => DenefPasInverse.graph (arg 0) output
  | .kAdd => DenefPasResidue.addGraph (arg 0) (arg 1) output
  | .kNeg => DenefPasResidue.negGraph (arg 0) output
  | _ => ⊥

def relationGraph {k : ℕ} (r : RVRelation k) : auxLanguage.Formula (Fin k × Coord) :=
  match r.val with
  | .memRV => ⊤
  | .memVF => ⊥
  | .memUnits => units (relArg 0)
  | .rvLe => DenefPasOrder.graph (relArg 0) (relArg 1)

def dictionary : PairSyntax.Syntax RVBase auxLanguage where
  equality := DenefPasEquality.equal (fun b => .var (.inl b)) (fun b => .var (.inr b))
  functionGraph := functionGraph
  relationGraph := relationGraph

variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]
local instance (v : Valuation K Γ) : auxLanguage.Structure (Aux v) := auxStructure

theorem units_realize (v : Valuation K Γ) (a : Data v) {I : Type}
    (p : Coord → auxLanguage.Term I) (z : I → Aux v) :
    (units p).Realize z ↔ (decode v a (fun i => (p i).realize z) ≠ none ∧
      gammaValue v a (decode v a (fun i => (p i).realize z)) = 1) := by
  rw [units, Formula.realize_inf, Formula.realize_not, DenefPasEquality.zero_realize,
    Formula.realize_equal, DenefPasEquality.g_realize, DenefPasRV.units_decode]
  change (¬ ZeroCode v (fun i => (p i).realize z) ∧
    Sum.inr (valueCoord v (fun i => (p i).realize z)) = Sum.inr (1 : Gamma v)) ↔ _
  rw [Sum.inr.injEq]

theorem functionGraph_realize (v : Valuation K Γ) (a : Data v) {k : ℕ}
    (f : RVFunction k) (w : FunctionContext k → Aux v) :
    letI : RVBase.Structure (RVCalc.RV v) := DenefPasRV.rvStructure v a
    (functionGraph f).Realize w ↔ decode v a (w ∘ Sum.inr) =
      Structure.funMap (L := RVBase) f (PairInterpretation.decode (decode v a) (w ∘ Sum.inl)) := by
  letI : RVBase.Structure (RVCalc.RV v) := DenefPasRV.rvStructure v a
  change (functionGraph f).Realize w ↔ decode v a (w ∘ Sum.inr) =
    @Structure.funMap RVBase (RVCalc.RV v) (DenefPasRV.rvStructure v a) k f
      (PairInterpretation.decode (decode v a) (w ∘ Sum.inl))
  rcases f with ⟨f, hf⟩
  cases f with
  | vfZero => cases hf.1
  | vfOne => cases hf.1
  | vfAdd => cases hf.1
  | vfNeg => cases hf.1
  | vfMul => cases hf.1
  | rvMap => have h := hf.2 0; cases h
  | rvZero =>
    have h := (DenefPasEquality.zero_realize v (output (k := 0)) w).trans (decode_zero_iff v a _).symm
    simpa only [functionGraph, output, Term.realize_var, Function.comp_def,
      Structure.funMap, Structure.RelMap, DenefPasRV.rvStructure] using h
  | rvOne =>
    have h := DenefPasEquality.equal_realize v a (output (k := 0)) DenefPasInverse.one w
    rw [DenefPasInverse.one_realize] at h
    simpa only [functionGraph, output, Term.realize_var, Function.comp_def,
      Structure.funMap, Structure.RelMap, DenefPasRV.rvStructure] using h
  | rvMul =>
    simpa only [functionGraph, arg, output, Term.realize_var, Function.comp_def,
      PairInterpretation.decode, Structure.funMap, Structure.RelMap, DenefPasRV.rvStructure] using
      DenefPasMultiplication.graph_realize v a (arg 0) (arg 1) output w
  | rvInv =>
    simpa only [functionGraph, arg, output, Term.realize_var, Function.comp_def,
      PairInterpretation.decode, Structure.funMap, Structure.RelMap, DenefPasRV.rvStructure] using
      DenefPasInverse.graph_realize v a (arg 0) output w
  | kAdd =>
    simpa only [functionGraph, arg, output, Term.realize_var, Function.comp_def,
      PairInterpretation.decode, Structure.funMap, Structure.RelMap, DenefPasRV.rvStructure] using
      DenefPasResidue.addGraph_realize v a (arg 0) (arg 1) output w
  | kNeg =>
    simpa only [functionGraph, arg, output, Term.realize_var, Function.comp_def,
      PairInterpretation.decode, Structure.funMap, Structure.RelMap, DenefPasRV.rvStructure] using
      DenefPasResidue.negGraph_realize v a (arg 0) output w

theorem relationGraph_realize (v : Valuation K Γ) (a : Data v) {k : ℕ}
    (r : RVRelation k) (w : Fin k × Coord → Aux v) :
    letI : RVBase.Structure (RVCalc.RV v) := DenefPasRV.rvStructure v a
    (relationGraph r).Realize w ↔ Structure.RelMap (L := RVBase) r
      (PairInterpretation.decode (decode v a) w) := by
  letI : RVBase.Structure (RVCalc.RV v) := DenefPasRV.rvStructure v a
  change (relationGraph r).Realize w ↔
    @Structure.RelMap RVBase (RVCalc.RV v) (DenefPasRV.rvStructure v a) k r
      (PairInterpretation.decode (decode v a) w)
  rcases r with ⟨r, hr⟩
  cases r with
  | memVF => have h := hr 0; cases h
  | memRV => simp only [relationGraph, Formula.realize_top, Structure.funMap, Structure.RelMap, DenefPasRV.rvStructure]
  | memUnits =>
    simpa only [relationGraph, relArg, Term.realize_var, Function.comp_def,
      PairInterpretation.decode, Structure.funMap, Structure.RelMap, DenefPasRV.rvStructure] using units_realize v a (relArg 0) w
  | rvLe =>
    simpa only [relationGraph, relArg, Term.realize_var, Function.comp_def,
      PairInterpretation.decode, Structure.funMap, Structure.RelMap, DenefPasRV.rvStructure] using
      DenefPasOrder.graph_realize v a (relArg 0) (relArg 1) w

def realizes (v : Valuation K Γ) (a : Data v) :
    letI : RVBase.Structure (RVCalc.RV v) := DenefPasRV.rvStructure v a
    PairSyntax.Realizes dictionary (RVCalc.RV v) (Aux v) := by
  letI : RVBase.Structure (RVCalc.RV v) := DenefPasRV.rvStructure v a
  exact {
    code := decode v a
    onto := decode_surjective v a
    equality := fun w => by
      simpa only [dictionary, Term.realize_var, Function.comp_def] using
        DenefPasEquality.equal_realize v a (fun b => .var (.inl b)) (fun b => .var (.inr b)) w
    functionGraph := fun f w => functionGraph_realize v a f w
    relationGraph := fun r w => relationGraph_realize v a r w }

end SpecialTransformations.Section6.DenefPasNativeDictionary
end
end

/-! Source: Section6.DenefPasMorley -/
section

/-! Relational Morleyization of the auxiliary DP language on RV. Each
symbol is indexed by an actual auxiliary formula, chosen before models.
Its auxiliary graph normalizes all raw pair codes before using that formula. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language

namespace SpecialTransformations.Section6.DenefPasMorley
open DenefPasAux DenefPasCodes AngularComponent

abbrev Auxiliary (E : _root_.FirstOrder.Language.{0, 0}) := auxLanguage.sum E

def signature (E : _root_.FirstOrder.Language.{0, 0}) : _root_.FirstOrder.Language.{0, 0} :=
  ⟨fun _ => Empty, fun n => (Auxiliary E).Formula (Fin n × Coord)⟩

instance (E : _root_.FirstOrder.Language.{0, 0}) : (signature E).IsRelational := fun _ => inferInstanceAs (IsEmpty Empty)

def norm : auxLanguage.Formula (Coord ⊕ Coord) :=
  DenefPasNormalization.graph (fun i => .var (.inl i)) (fun i => .var (.inr i))

def normExpanded (E : _root_.FirstOrder.Language.{0, 0}) : (Auxiliary E).Formula (Coord ⊕ Coord) :=
  (LHom.sumInl : auxLanguage →ᴸ Auxiliary E).onBoundedFormula norm

def slot {n : ℕ} (i : Fin n) : Coord ⊕ Coord → (Fin n × Coord) ⊕ (Fin n × Coord) :=
  Sum.elim (fun b => .inl (i, b)) (fun b => .inr (i, b))

def relationGraph {E : _root_.FirstOrder.Language.{0, 0}} {n : ℕ} (θ : (Auxiliary E).Formula (Fin n × Coord)) :
    (Auxiliary E).Formula (Fin n × Coord) :=
  Formula.iExs (Fin n × Coord)
    ((Formula.iInf fun i : Fin n => (normExpanded E).relabel (slot i)) ⊓ θ.relabel Sum.inr)

variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]

@[instance_reducible] def rvStructure (E : _root_.FirstOrder.Language.{0, 0}) (v : Valuation K Γ) (a : Data v)
    [(Auxiliary E).Structure (Aux v)] : (signature E).Structure (RVCalc.RV v) where
  funMap f := isEmptyElim f
  RelMap θ q := θ.Realize (fun i => DenefPasNormalization.coordinates v a (q i.1) i.2)

section Semantics
variable (E : _root_.FirstOrder.Language.{0, 0}) (v : Valuation K Γ) (a : Data v) [E.Structure (Aux v)]
local instance : auxLanguage.Structure (Aux v) := auxStructure
local instance : (Auxiliary E).Structure (Aux v) :=
  FirstOrder.Language.sumStructure auxLanguage E (Aux v)

theorem normExpanded_realize (z : Coord ⊕ Coord → Aux v) :
    (normExpanded E).Realize z ↔ (z ∘ Sum.inr) =
      DenefPasNormalization.coordinates v a (decode v a (z ∘ Sum.inl)) := by
  have h := DenefPasNormalization.graph_realize v a
    (fun i => Term.var (.inl i)) (fun i => Term.var (.inr i)) z
  simpa only [normExpanded, norm, Formula.Realize, LHom.realize_onBoundedFormula,
    Term.realize_var, Function.comp_def] using h

theorem relationGraph_realize {n : ℕ} (θ : (Auxiliary E).Formula (Fin n × Coord))
    (w : Fin n × Coord → Aux v) :
    (relationGraph θ).Realize w ↔ θ.Realize
      (fun j => DenefPasNormalization.coordinates v a (decode v a (fun b => w (j.1, b))) j.2) := by
  simp only [relationGraph, Formula.realize_iExs, Formula.realize_inf,
    Formula.realize_iInf, Formula.realize_relabel, normExpanded_realize E v a]
  change (∃ u : Fin n × Coord → Aux v,
    (∀ i, (fun b => u (i, b)) = DenefPasNormalization.coordinates v a
      (decode v a (fun b => w (i, b)))) ∧ θ.Realize u) ↔ _
  constructor
  · rintro ⟨u, hu, hθ⟩
    have he : u = (fun j => DenefPasNormalization.coordinates v a
        (decode v a (fun b => w (j.1, b))) j.2) := by
      funext j
      exact congrFun (hu j.1) j.2
    simpa only [he] using hθ
  · intro hθ
    exact ⟨_, fun _ => rfl, hθ⟩

end Semantics
end SpecialTransformations.Section6.DenefPasMorley

end
end

/-! Source: Section6.DenefPasDictionary -/
section

/-! The uniform auxiliary interpretation, including every relational
symbol indexed by an auxiliary formula. No formula is chosen from a model. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language

namespace SpecialTransformations.Section6.DenefPasDictionary
open DenefPasAux DenefPasCodes AngularComponent RVGraphLanguage

abbrev Source (E : _root_.FirstOrder.Language.{0, 0}) := RVBase.sum (DenefPasMorley.signature E)
abbrev Target (E : _root_.FirstOrder.Language.{0, 0}) := DenefPasMorley.Auxiliary E

def lift (E : _root_.FirstOrder.Language.{0, 0}) {I : Type}
    (φ : auxLanguage.Formula I) : (Target E).Formula I :=
  (LHom.sumInl : auxLanguage →ᴸ Target E).onBoundedFormula φ

def dictionary (E : _root_.FirstOrder.Language.{0, 0}) : PairSyntax.Syntax (Source E) (Target E) where
  equality := lift E DenefPasNativeDictionary.dictionary.equality
  functionGraph := fun f => match f with
    | .inl f => lift E (DenefPasNativeDictionary.functionGraph f)
    | .inr f => isEmptyElim f
  relationGraph := fun r => match r with
    | .inl r => lift E (DenefPasNativeDictionary.relationGraph r)
    | .inr θ => DenefPasMorley.relationGraph θ

variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]
variable (E : _root_.FirstOrder.Language.{0, 0}) (v : Valuation K Γ) (a : Data v)
variable [E.Structure (Aux v)]
local instance : auxLanguage.Structure (Aux v) := auxStructure
local instance : (Target E).Structure (Aux v) :=
  FirstOrder.Language.sumStructure auxLanguage E (Aux v)
def Model (v : Valuation K Γ) (_a : Data v) : Type := RVCalc.RV v
local instance : RVBase.Structure (Model v a) := DenefPasRV.rvStructure v a
local instance : (DenefPasMorley.signature E).Structure (Model v a) :=
  DenefPasMorley.rvStructure E v a
local instance : (Source E).Structure (Model v a) :=
  FirstOrder.Language.sumStructure RVBase (DenefPasMorley.signature E) (Model v a)

theorem lift_realize {I : Type} (φ : auxLanguage.Formula I) (z : I → Aux v) :
    (lift E φ).Realize z ↔ φ.Realize z := by
  exact LHom.realize_onBoundedFormula (LHom.sumInl : auxLanguage →ᴸ Target E) φ

def code : (PairSyntax.Coord → Aux v) → Model v a := decode v a

def realizes : PairSyntax.Realizes (dictionary E) (Model v a) (Aux v) where
  code := code v a
  onto := decode_surjective v a
  equality := fun w => by
    rw [dictionary, lift_realize]
    simpa only [code, DenefPasNativeDictionary.dictionary, Term.realize_var, Function.comp_def] using
      DenefPasEquality.equal_realize v a (fun b => .var (.inl b)) (fun b => .var (.inr b)) w
  functionGraph := fun f w => by
    cases f with
    | inl f =>
      rw [dictionary, lift_realize]
      exact DenefPasNativeDictionary.functionGraph_realize v a f w
    | inr f => exact isEmptyElim f
  relationGraph := fun r w => by
    cases r with
    | inl r =>
      rw [dictionary, lift_realize]
      exact DenefPasNativeDictionary.relationGraph_realize v a r w
    | inr θ =>
      change (DenefPasMorley.relationGraph θ).Realize w ↔ θ.Realize
        (fun j => DenefPasNormalization.coordinates v a
          (decode v a (fun b => w (j.1, b))) j.2)
      exact DenefPasMorley.relationGraph_realize E v a θ w

/-- This is a fixed syntactic translation of the complete RV auxiliary
fragment, including arbitrary auxiliary relations. -/
theorem formula_realize {I : Type} (φ : (Source E).Formula I) (z : (I × PairSyntax.Coord) → Aux v) :
    (PairSyntax.formula (dictionary E) φ).Realize z ↔
      φ.Realize (PairInterpretation.decode (code v a) z) :=
  PairSyntax.formula_realize (dictionary E) (realizes E v a) φ z

end SpecialTransformations.Section6.DenefPasDictionary
end
end

/-! Source: Section6.DenefPasNativeModel -/
section

/-! The actual native tagged carrier used by the forward DP interpretation.
The field signature is taken directly from the released language. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Section6.DenefPasNativeModel
open DenefPasCodes AngularComponent RVAbstraction RVGraphLanguage DenefPasLanguage
open DenefPasNativeCodes
variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]

def rvValue {v : Valuation K Γ} : NativeCarrier v → RVCalc.RV v :=
  Sum.elim (fun _ => none) id

def IsRV {v : Valuation K Γ} (x : NativeCarrier v) : Prop := ∃ q : RVCalc.RV v, x = .inr q

def liftRV (v : Valuation K Γ) (a : Data v) {k : ℕ} (f : RVFunction k)
    (z : Fin k → NativeCarrier v) : NativeCarrier v :=
  if ∀ i, IsRV (z i) then .inr
    (@Structure.funMap RVBase (RVCalc.RV v) (DenefPasRV.rvStructure v a) k f (rvValue ∘ z))
  else .inr none

def nativeFunction (v : Valuation K Γ) (a : Data v) {k : ℕ} (f : Fn k)
    (z : Fin k → NativeCarrier v) : NativeCarrier v :=
  match f with
  | .vfZero => .inl (fieldFunction ⟨.vfZero, rfl, fun i => i.elim0⟩ z)
  | .vfOne => .inl (fieldFunction ⟨.vfOne, rfl, fun i => i.elim0⟩ z)
  | .vfAdd => .inl (fieldFunction ⟨.vfAdd, rfl, fun _ => rfl⟩ z)
  | .vfNeg => .inl (fieldFunction ⟨.vfNeg, rfl, fun _ => rfl⟩ z)
  | .vfMul => .inl (fieldFunction ⟨.vfMul, rfl, fun _ => rfl⟩ z)
  | .rvMap => .inr (RVCalc.rv v (fieldValue (z 0)))
  | .rvZero => liftRV v a ⟨.rvZero, rfl, fun i => i.elim0⟩ z
  | .rvOne => liftRV v a ⟨.rvOne, rfl, fun i => i.elim0⟩ z
  | .rvMul => liftRV v a ⟨.rvMul, rfl, fun _ => rfl⟩ z
  | .rvInv => liftRV v a ⟨.rvInv, rfl, fun _ => rfl⟩ z
  | .kAdd => liftRV v a ⟨.kAdd, rfl, fun _ => rfl⟩ z
  | .kNeg => liftRV v a ⟨.kNeg, rfl, fun _ => rfl⟩ z

def nativeRelation (v : Valuation K Γ) (a : Data v) {k : ℕ} (r : Rel k)
    (z : Fin k → NativeCarrier v) : Prop :=
  match r with
  | .memVF => IsField (z 0)
  | .memRV => IsRV (z 0)
  | .memUnits => IsRV (z 0) ∧ rvValue (z 0) ≠ none ∧ gammaValue v a (rvValue (z 0)) = 1
  | .rvLe => (∀ i, IsRV (z i)) ∧ gammaValue v a (rvValue (z 1)) ≤ gammaValue v a (rvValue (z 0))

def Model (E : _root_.FirstOrder.Language.{0, 0}) (v : Valuation K Γ) (_a : Data v) : Type := NativeCarrier v

@[instance_reducible] def structureOn (E : _root_.FirstOrder.Language.{0, 0})
    (v : Valuation K Γ) (a : Data v) [E.Structure (Aux v)] :
    (RVTermSupport.Expanded (DenefPasMorley.signature E)).Structure (Model E v a) := by
  letI : DenefPasAux.auxLanguage.Structure (Aux v) := DenefPasAux.auxStructure
  letI : (DenefPasMorley.Auxiliary E).Structure (Aux v) :=
    FirstOrder.Language.sumStructure DenefPasAux.auxLanguage E (Aux v)
  exact {
    funMap := fun f z => match f with
      | .inl f => nativeFunction v a f z
      | .inr f => isEmptyElim f
    RelMap := fun r z => match r with
      | .inl r => nativeRelation v a r z
      | .inr θ => (∀ i, IsRV (z i)) ∧ θ.Realize
          (fun j => DenefPasNormalization.coordinates v a (rvValue (z j.1)) j.2) }

theorem liftRV_inr (v : Valuation K Γ) (a : Data v) {k : ℕ} (f : RVFunction k)
    (z : Fin k → RVCalc.RV v) :
    liftRV v a f (Sum.inr ∘ z) = .inr
      (@Structure.funMap RVBase (RVCalc.RV v) (DenefPasRV.rvStructure v a) k f z) := by
  rw [liftRV, if_pos (fun i => ⟨z i, rfl⟩)]
  rfl

theorem nativeFunction_field (v : Valuation K Γ) (a : Data v) {k : ℕ}
    (f : FieldFunction k) (z : Fin k → NativeCarrier v) :
    nativeFunction v a f.val z = .inl (fieldFunction f z) := by
  rcases f with ⟨f, hf, ha⟩
  cases f <;> first | rfl | cases hf

theorem nativeFunction_rv (v : Valuation K Γ) (a : Data v) {k : ℕ}
    (f : RVFunction k) (z : Fin k → RVCalc.RV v) :
    nativeFunction v a f.val (Sum.inr ∘ z) = .inr
      (@Structure.funMap RVBase (RVCalc.RV v) (DenefPasRV.rvStructure v a) k f z) := by
  rcases f with ⟨f, hf, ha⟩
  cases f <;> try cases hf
  all_goals first
    | exact liftRV_inr v a _ z
    | have h := ha 0; cases h

end SpecialTransformations.Section6.DenefPasNativeModel

end
end

/-! Source: Section6.DenefPasForwardCodes -/
section

/-! Exact sort and field-operation behavior of the forward pair code. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical

namespace SpecialTransformations.Section6.DenefPasForwardCodes
open AngularComponent DenefPasCodes DenefPasLanguage DenefPasNativeCodes DenefPasNativeModel
variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]

theorem fieldValue_code (v : Valuation K Γ) (a : Data v) (p : Coord → NativeCarrier v) :
    fieldValue (code v a p) = fieldValue (p 1) := by
  cases h : p 1 with
  | inl x => simp [code, h, fieldValue]
  | inr q => by_cases ht : p 0 = .inl 0 <;> simp [code, h, ht, fieldValue]

theorem isField_code (v : Valuation K Γ) (a : Data v) (p : Coord → NativeCarrier v) :
    IsField (code v a p) ↔ IsField (p 1) := by
  cases h : p 1 with
  | inl x => simp [code, h, DenefPasLanguage.IsField]
  | inr q => by_cases ht : p 0 = .inl 0 <;> simp [code, h, ht, DenefPasLanguage.IsField]

theorem isResidue_code (v : Valuation K Γ) (a : Data v) (p : Coord → NativeCarrier v) :
    (∃ r : Residue v, code v a p = .inr (.inl r)) ↔ IsRV (p 1) ∧ p 0 = .inl 0 := by
  unfold code
  cases h : p 1 with
  | inl x => simp [IsRV]
  | inr q =>
    by_cases ht : p 0 = .inl 0 <;> simp [ht, IsRV]

theorem isValue_code (v : Valuation K Γ) (a : Data v) (p : Coord → NativeCarrier v) :
    (∃ g : Gamma v, code v a p = .inr (.inr g)) ↔ IsRV (p 1) ∧ p 0 ≠ .inl 0 := by
  unfold code
  cases h : p 1 with
  | inl x => simp [IsRV]
  | inr q =>
    by_cases ht : p 0 = .inl 0 <;> simp [ht, IsRV]

theorem isAux_code (v : Valuation K Γ) (a : Data v) (p : Coord → NativeCarrier v) :
    IsAux (code v a p) ↔ IsRV (p 1) := by
  cases h : p 1 with
  | inl x => simp [code, h, IsAux, IsRV]
  | inr q => by_cases ht : p 0 = .inl 0 <;> simp [code, h, ht, IsAux, IsRV]

theorem fieldFunction_code (v : Valuation K Γ) (a : Data v) {k : ℕ}
    (f : FieldFunction k) (p : Fin k → Coord → NativeCarrier v) :
    fieldFunction f (fun i => code v a (p i)) = fieldFunction f (fun i => p i 1) := by
  rcases f with ⟨f, hf, ha⟩
  cases f <;> simp only [fieldFunction, isField_code, fieldValue_code]

theorem fieldFunction_graph (v : Valuation K Γ) (a : Data v) {k : ℕ}
    (f : FieldFunction k) (p : Fin k → Coord → NativeCarrier v) (q : Coord → NativeCarrier v) :
    code v a q = .inl (fieldFunction f (fun i => code v a (p i))) ↔
      IsField (q 1) ∧ q 1 = nativeFunction v a f.val (fun i => p i 1) := by
  rw [fieldFunction_code, nativeFunction_field]
  cases h : q 1 with
  | inl x => simp [code, h, DenefPasLanguage.IsField]
  | inr r => by_cases ht : q 0 = .inl 0 <;> simp [code, h, ht, DenefPasLanguage.IsField]

end SpecialTransformations.Section6.DenefPasForwardCodes
end
end

/-! Source: Section6.DenefPasForwardPatterns -/
section

/-! Finite RF/Gamma patterns for the forward interpretation. The patterns
are syntax, while their semantic meaning is proved on the actual pair code. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Section6.DenefPasForwardPatterns
open AngularComponent DenefPasCodes DenefPasLanguage DenefPasNativeCodes DenefPasNativeModel
variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]

def Category {v : Valuation K Γ} (b : Bool) (p : Coord → NativeCarrier v) : Prop :=
  IsRV (p 1) ∧ if b then p 0 ≠ .inl 0 else p 0 = .inl 0

def selected (v : Valuation K Γ) (a : Data v) (b : Bool) (q : RVCalc.RV v) : Aux v :=
  if b then .inr (gammaValue v a q) else .inl (residueValue v a q)

theorem category_code (v : Valuation K Γ) (a : Data v) (b : Bool)
    (p : Coord → NativeCarrier v) (h : Category b p) :
    code v a p = .inr (selected v a b (rvValue (p 1))) := by
  obtain ⟨q, hq⟩ := h.1
  cases b <;> simp only [Category, Bool.false_eq_true, Bool.true_eq, if_false, if_true] at h
  · simp [code, hq, h.2, selected, rvValue]
  · simp [code, hq, h.2, selected, rvValue]

theorem category_cover {v : Valuation K Γ} (p : Coord → NativeCarrier v) (h : IsRV (p 1)) :
    ∃ b, Category b p := by
  by_cases ht : p 0 = .inl 0
  · exact ⟨false, h, ht⟩
  · exact ⟨true, h, ht⟩

theorem category_auxValue (v : Valuation K Γ) (a : Data v) (b : Bool)
    (p : Coord → NativeCarrier v) (h : Category b p) :
    auxValue (code v a p) = selected v a b (rvValue (p 1)) := by
  rw [category_code v a b p h]
  rfl

theorem function_patterns (v : Valuation K Γ) (a : Data v) {k : ℕ}
    (F : (Fin k → Aux v) → Aux v) (p : Fin k → Coord → NativeCarrier v)
    (q : Coord → NativeCarrier v) (hp : ∀ i, IsRV (p i 1)) :
    code v a q = .inr (F (fun i => auxValue (code v a (p i)))) ↔
      ∃ (σ : Fin k → Bool) (β : Bool), (∀ i, Category (σ i) (p i)) ∧ Category β q ∧
        selected v a β (rvValue (q 1)) = F (fun i => selected v a (σ i) (rvValue (p i 1))) := by
  constructor
  · intro he
    choose σ hσ using fun i => category_cover (p i) (hp i)
    have hq : IsRV (q 1) := (DenefPasForwardCodes.isAux_code v a q).mp ⟨_, he⟩
    obtain ⟨β, hβ⟩ := category_cover q hq
    refine ⟨σ, β, hσ, hβ, ?_⟩
    have ha : (fun i => auxValue (code v a (p i))) =
        (fun i => selected v a (σ i) (rvValue (p i 1))) :=
      funext (fun i => category_auxValue v a (σ i) (p i) (hσ i))
    rw [category_code v a β q hβ, ha] at he
    exact Sum.inr.inj he
  · rintro ⟨σ, β, hσ, hβ, he⟩
    rw [category_code v a β q hβ, he]
    congr 2
    funext i
    exact (category_auxValue v a (σ i) (p i) (hσ i)).symm

theorem relation_patterns (v : Valuation K Γ) (a : Data v) {k : ℕ}
    (P : (Fin k → Aux v) → Prop) (p : Fin k → Coord → NativeCarrier v) :
    ((∀ i, IsAux (code v a (p i))) ∧ P (fun i => auxValue (code v a (p i)))) ↔
      ∃ σ : Fin k → Bool, (∀ i, Category (σ i) (p i)) ∧
        P (fun i => selected v a (σ i) (rvValue (p i 1))) := by
  constructor
  · rintro ⟨hp, hP⟩
    choose σ hσ using fun i => category_cover (p i)
      ((DenefPasForwardCodes.isAux_code v a (p i)).mp (hp i))
    refine ⟨σ, hσ, ?_⟩
    have ha : (fun i => auxValue (code v a (p i))) =
        (fun i => selected v a (σ i) (rvValue (p i 1))) :=
      funext (fun i => category_auxValue v a (σ i) (p i) (hσ i))
    rwa [ha] at hP
  · rintro ⟨σ, hσ, hP⟩
    refine ⟨fun i => (DenefPasForwardCodes.isAux_code v a (p i)).mpr (hσ i).1, ?_⟩
    have ha : (fun i => auxValue (code v a (p i))) =
        (fun i => selected v a (σ i) (rvValue (p i 1))) :=
      funext (fun i => category_auxValue v a (σ i) (p i) (hσ i))
    rwa [ha]

abbrev Native (E : _root_.FirstOrder.Language.{0, 0}) := RVTermSupport.Expanded (DenefPasMorley.signature E)

def zero {E : _root_.FirstOrder.Language.{0, 0}} {I : Type} : (Native E).Term I :=
  .func (.inl .vfZero) Fin.elim0

def field {E : _root_.FirstOrder.Language.{0, 0}} {I : Type} (t : (Native E).Term I) :
    (Native E).Formula I := Relations.formula (L := Native E) (.inl .memVF) ![t]

def auxiliary {E : _root_.FirstOrder.Language.{0, 0}} {I : Type} (t : (Native E).Term I) :
    (Native E).Formula I := Relations.formula (L := Native E) (.inl .memRV) ![t]

def category {E : _root_.FirstOrder.Language.{0, 0}} {I : Type}
    (b : Bool) (p : Coord → (Native E).Term I) : (Native E).Formula I :=
  auxiliary (p 1) ⊓ if b then ((p 0).equal zero).not else (p 0).equal zero

def fieldGraph {E : _root_.FirstOrder.Language.{0, 0}} {I : Type} {k : ℕ}
    (f : FieldFunction k) (p : Fin k → Coord → (Native E).Term I)
    (q : Coord → (Native E).Term I) : (Native E).Formula I :=
  field (q 1) ⊓ (q 1).equal (.func (.inl f.val) (fun i => p i 1))

section Semantics
variable (E : _root_.FirstOrder.Language.{0, 0}) (v : Valuation K Γ) (a : Data v)
variable [E.Structure (Aux v)]
local instance : (Native E).Structure (Model E v a) := structureOn E v a
local instance : DenefPasAux.auxLanguage.Structure (Aux v) := DenefPasAux.auxStructure
local instance : (DenefPasMorley.Auxiliary E).Structure (Aux v) :=
  FirstOrder.Language.sumStructure DenefPasAux.auxLanguage E (Aux v)

theorem zero_realize {I : Type} (z : I → Model E v a) :
    (zero : (Native E).Term I).realize (M := Model E v a) z = (Sum.inl 0 : Model E v a) := by
  simp [zero, Term.realize, Structure.funMap, structureOn, nativeFunction, fieldFunction]

theorem field_realize {I : Type} (t : (Native E).Term I) (z : I → Model E v a) :
    (field t).Realize z ↔ DenefPasLanguage.IsField (t.realize (M := Model E v a) z) := by
  simp only [field, auxiliary, Relations.formula, Relations.boundedFormula, Formula.Realize,
    BoundedFormula.Realize, Term.realize_relabel, Sum.elim_comp_inl]
  rfl

theorem auxiliary_realize {I : Type} (t : (Native E).Term I) (z : I → Model E v a) :
    (auxiliary t).Realize z ↔ IsRV (t.realize (M := Model E v a) z) := by
  simp only [field, auxiliary, Relations.formula, Relations.boundedFormula, Formula.Realize,
    BoundedFormula.Realize, Term.realize_relabel, Sum.elim_comp_inl]
  rfl

theorem category_realize {I : Type} (b : Bool) (p : Coord → (Native E).Term I)
    (z : I → Model E v a) :
    (category b p).Realize z ↔ Category b (fun i => (p i).realize (M := Model E v a) z) := by
  cases b <;> simp only [category, Formula.realize_inf, auxiliary_realize,
    Bool.false_eq_true, Bool.true_eq, if_false, if_true, Formula.realize_not,
    Formula.realize_equal, zero_realize, Category]

theorem fieldGraph_realize {I : Type} {k : ℕ} (f : FieldFunction k)
    (p : Fin k → Coord → (Native E).Term I) (q : Coord → (Native E).Term I)
    (z : I → Model E v a) :
    (fieldGraph f p q).Realize z ↔ code v a (fun b => (q b).realize (M := Model E v a) z) =
      .inl (fieldFunction f (fun i => code v a (fun b => (p i b).realize (M := Model E v a) z))) := by
  rw [fieldGraph, Formula.realize_inf, field_realize, Formula.realize_equal]
  exact (DenefPasForwardCodes.fieldFunction_graph v a f
    (fun i b => (p i b).realize (M := Model E v a) z) (fun b => (q b).realize (M := Model E v a) z)).symm

theorem extra_realize {I : Type} {k : ℕ}
    (θ : (DenefPasMorley.Auxiliary E).Formula (Fin k × Coord))
    (ts : Fin k → (Native E).Term I) (z : I → Model E v a) :
    (Formula.Realize (Relations.formula (L := Native E) (.inr θ) ts) z ↔
      (∀ i, IsRV ((ts i).realize (M := Model E v a) z)) ∧ θ.Realize
        (fun j => DenefPasNormalization.coordinates v a (rvValue ((ts j.1).realize (M := Model E v a) z)) j.2)) := by
  simp only [field, auxiliary, Relations.formula, Relations.boundedFormula, Formula.Realize,
    BoundedFormula.Realize, Term.realize_relabel, Sum.elim_comp_inl]
  rfl

end Semantics
end SpecialTransformations.Section6.DenefPasForwardPatterns
end
end

/-! Source: Section6.DenefPasForwardAuxiliary -/
section

/-! Fixed atomic auxiliary graphs in the relational RV expansion. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 50000
open Classical FirstOrder FirstOrder.Language

namespace SpecialTransformations.Section6.DenefPasForwardAuxiliary
open AngularComponent DenefPasCodes DenefPasLanguage DenefPasNativeCodes DenefPasNativeModel
open DenefPasForwardPatterns

def coordinate (b : Bool) : Coord := if b then 1 else 0

def relationFormula {E : _root_.FirstOrder.Language.{0, 0}} {k : ℕ}
    (r : (DenefPasMorley.Auxiliary E).Relations k) (σ : Fin k → Bool) :
    (DenefPasMorley.Auxiliary E).Formula (Fin k × Coord) :=
  Relations.formula (L := DenefPasMorley.Auxiliary E) r (fun i => .var (i, coordinate (σ i)))

def functionFormula {E : _root_.FirstOrder.Language.{0, 0}} {k : ℕ}
    (f : (DenefPasMorley.Auxiliary E).Functions k) (σ : Fin k → Bool) (β : Bool) :
    (DenefPasMorley.Auxiliary E).Formula (Fin (k + 1) × Coord) :=
  (Term.var (L := DenefPasMorley.Auxiliary E) (Fin.last k, coordinate β)).equal
    (.func f (fun i => .var (i.castSucc, coordinate (σ i))))

def relationGraph {E : _root_.FirstOrder.Language.{0, 0}} {I : Type} {k : ℕ}
    (r : (DenefPasMorley.Auxiliary E).Relations k)
    (p : Fin k → Coord → (Native E).Term I) : (Native E).Formula I :=
  Formula.iSup (L := Native E) fun σ : Fin k → Bool =>
    (Formula.iInf (L := Native E) fun i => category (σ i) (p i)) ⊓
      Relations.formula (L := Native E) (.inr (relationFormula r σ)) (fun i => p i 1)

def functionGraphGood {E : _root_.FirstOrder.Language.{0, 0}} {I : Type} {k : ℕ}
    (f : (DenefPasMorley.Auxiliary E).Functions k)
    (p : Fin k → Coord → (Native E).Term I) (q : Coord → (Native E).Term I) : (Native E).Formula I :=
  Formula.iSup (L := Native E) fun σ : Fin k → Bool => Formula.iSup (L := Native E) fun β : Bool =>
    (Formula.iInf (L := Native E) fun i => category (σ i) (p i)) ⊓ (category β q ⊓
      Relations.formula (L := Native E) (.inr (functionFormula f σ β)) (Fin.snoc (α := fun _ => (Native E).Term I) (fun i => p i 1) (q 1)))

def zeroFormula (E : _root_.FirstOrder.Language.{0, 0}) :
    (DenefPasMorley.Auxiliary E).Formula (Fin 1 × Coord) :=
  (Term.var (0, 0)).equal
    (Constants.term (L := DenefPasMorley.Auxiliary E) (.inl DenefPasAux.Functions.rZero))

def zeroGraph {E : _root_.FirstOrder.Language.{0, 0}} {I : Type}
    (q : Coord → (Native E).Term I) : (Native E).Formula I :=
  category false q ⊓ Relations.formula (L := Native E) (.inr (zeroFormula E)) ![q 1]

def functionGraph {E : _root_.FirstOrder.Language.{0, 0}} {I : Type} {k : ℕ}
    (f : (DenefPasMorley.Auxiliary E).Functions k)
    (p : Fin k → Coord → (Native E).Term I) (q : Coord → (Native E).Term I) : (Native E).Formula I :=
  functionGraphGood f p q ⊔ ((Formula.iInf fun i => auxiliary (p i 1)).not ⊓ zeroGraph q)

variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]
variable (E : _root_.FirstOrder.Language.{0, 0}) (v : Valuation K Γ) (a : Data v)
variable [E.Structure (Aux v)]
local instance : (Native E).Structure (Model E v a) := structureOn E v a
local instance : DenefPasAux.auxLanguage.Structure (Aux v) := DenefPasAux.auxStructure
local instance : (DenefPasMorley.Auxiliary E).Structure (Aux v) :=
  FirstOrder.Language.sumStructure DenefPasAux.auxLanguage E (Aux v)

theorem coordinate_realize (b : Bool) (q : RVCalc.RV v) :
    DenefPasNormalization.coordinates v a q (coordinate b) = selected v a b q := by
  cases b <;> rfl

theorem relationFormula_realize {k : ℕ} (r : (DenefPasMorley.Auxiliary E).Relations k)
    (σ : Fin k → Bool) (u : Fin k → RVCalc.RV v) :
    (relationFormula r σ).Realize (fun j => DenefPasNormalization.coordinates v a (u j.1) j.2) ↔
      Structure.RelMap r (fun i => selected v a (σ i) (u i)) := by
  simp only [relationFormula, Relations.formula, Relations.boundedFormula, Formula.Realize,
    BoundedFormula.Realize, Term.realize_relabel, Sum.elim_comp_inl, Term.realize_var,
    coordinate_realize]

theorem functionFormula_realize {k : ℕ} (f : (DenefPasMorley.Auxiliary E).Functions k)
    (σ : Fin k → Bool) (β : Bool) (u : Fin (k + 1) → RVCalc.RV v) :
    (functionFormula f σ β).Realize (fun j => DenefPasNormalization.coordinates v a (u j.1) j.2) ↔
      selected v a β (u (Fin.last k)) =
        Structure.funMap f (fun i => selected v a (σ i) (u i.castSucc)) := by
  simp only [functionFormula, Formula.realize_equal, Term.realize_var, Term.realize_func,
    coordinate_realize]

theorem relationGraph_realize {I : Type} {k : ℕ} (r : (DenefPasMorley.Auxiliary E).Relations k)
    (p : Fin k → Coord → (Native E).Term I) (z : I → Model E v a) :
    (relationGraph r p).Realize z ↔
      (∀ i, IsAux (code v a (fun b => (p i b).realize (M := Model E v a) z))) ∧
        Structure.RelMap r (fun i => auxValue (code v a (fun b => (p i b).realize (M := Model E v a) z))) := by
  simp only [relationGraph, Formula.realize_iSup, Formula.realize_inf, Formula.realize_iInf,
    category_realize E v a, extra_realize E v a]
  rw [relation_patterns]
  constructor
  · rintro ⟨σ, hσ, _, hr⟩
    exact ⟨σ, hσ, (relationFormula_realize E v a r σ _).mp hr⟩
  · rintro ⟨σ, hσ, hr⟩
    exact ⟨σ, hσ, (fun i => (hσ i).1), (relationFormula_realize E v a r σ _).mpr hr⟩

theorem functionGraphGood_patterns {I : Type} {k : ℕ} (f : (DenefPasMorley.Auxiliary E).Functions k)
    (p : Fin k → Coord → (Native E).Term I) (q : Coord → (Native E).Term I)
    (z : I → Model E v a) :
    (functionGraphGood f p q).Realize z ↔ ∃ (σ : Fin k → Bool) (β : Bool),
      (∀ i, Category (σ i) (fun b => (p i b).realize (M := Model E v a) z)) ∧
      Category β (fun b => (q b).realize (M := Model E v a) z) ∧
      selected v a β (rvValue ((q 1).realize (M := Model E v a) z)) =
        Structure.funMap f (fun i => selected v a (σ i) (rvValue ((p i 1).realize (M := Model E v a) z))) := by
  simp only [functionGraphGood, Formula.realize_iSup, Formula.realize_inf,
    Formula.realize_iInf, category_realize E v a, extra_realize E v a]
  let u : Fin (k + 1) → RVCalc.RV v := Fin.snoc
    (fun i => rvValue ((p i 1).realize (M := Model E v a) z))
    (rvValue ((q 1).realize (M := Model E v a) z))
  have he (j : Fin (k + 1)) :
      rvValue ((Fin.snoc (α := fun _ => (Native E).Term I) (fun i => p i 1) (q 1) j).realize (M := Model E v a) z) = u j := by
    cases j using Fin.lastCases <;> simp only [u, Fin.snoc_last, Fin.snoc_castSucc]
  have hθ (σ : Fin k → Bool) (β : Bool) := functionFormula_realize E v a f σ β u
  simp only [he, hθ, u, Fin.snoc_last, Fin.snoc_castSucc]
  constructor
  · rintro ⟨σ, β, hσ, hβ, _, ht⟩
    exact ⟨σ, β, hσ, hβ, ht⟩
  · rintro ⟨σ, β, hσ, hβ, ht⟩
    refine ⟨σ, β, hσ, hβ, ?_, ht⟩
    intro j
    cases j using Fin.lastCases
    · simpa only [Fin.snoc_last] using hβ.1
    · rename_i i
      simpa only [Fin.snoc_castSucc] using (hσ i).1

theorem functionGraphGood_realize {I : Type} {k : ℕ} (f : (DenefPasMorley.Auxiliary E).Functions k)
    (p : Fin k → Coord → (Native E).Term I) (q : Coord → (Native E).Term I)
    (z : I → Model E v a) (hp : ∀ i, IsRV ((p i 1).realize (M := Model E v a) z)) :
    (functionGraphGood f p q).Realize z ↔ code v a (fun b => (q b).realize (M := Model E v a) z) =
      .inr (Structure.funMap f (fun i => auxValue (code v a (fun b => (p i b).realize (M := Model E v a) z)))) := by
  rw [functionGraphGood_patterns]
  exact (function_patterns v a (Structure.funMap f)
    (fun i b => (p i b).realize (M := Model E v a) z)
    (fun b => (q b).realize (M := Model E v a) z) hp).symm

theorem zeroFormula_realize (u : Fin 1 → RVCalc.RV v) :
    (zeroFormula E).Realize (fun j => DenefPasNormalization.coordinates v a (u j.1) j.2) ↔
      selected v a false (u 0) = Sum.inl 0 := by
  simp only [zeroFormula, Formula.realize_equal, Term.realize_var, Term.realize_constants]
  rfl

theorem zeroGraph_realize {I : Type} (q : Coord → (Native E).Term I) (z : I → Model E v a) :
    (zeroGraph q).Realize z ↔ code v a (fun b => (q b).realize (M := Model E v a) z) = .inr (.inl 0) := by
  simp only [zeroGraph, Formula.realize_inf, category_realize E v a, extra_realize E v a]
  constructor
  · rintro ⟨hcat, _, hθ⟩
    have hz := (zeroFormula_realize E v a
      (fun i => rvValue ((![(q 1)] i).realize (M := Model E v a) z))).mp hθ
    rw [category_code v a false _ hcat]
    exact congrArg (Sum.inr : Aux v → Carrier v) hz
  · intro he
    have hcat : Category false (fun b => (q b).realize (M := Model E v a) z) :=
      (DenefPasForwardCodes.isResidue_code v a _).mp ⟨0, he⟩
    refine ⟨hcat, ?_, ?_⟩
    · intro i
      fin_cases i
      exact hcat.1
    · apply (zeroFormula_realize E v a
        (fun i => rvValue ((![(q 1)] i).realize (M := Model E v a) z))).mpr
      exact Sum.inr.inj ((category_code v a false _ hcat).symm.trans he)

theorem functionGraph_realize {I : Type} {k : ℕ} (f : (DenefPasMorley.Auxiliary E).Functions k)
    (p : Fin k → Coord → (Native E).Term I) (q : Coord → (Native E).Term I)
    (z : I → Model E v a) :
    (functionGraph f p q).Realize z ↔ code v a (fun b => (q b).realize (M := Model E v a) z) =
      (if ∀ i, IsAux (code v a (fun b => (p i b).realize (M := Model E v a) z)) then
        .inr (Structure.funMap f (fun i => auxValue (code v a (fun b => (p i b).realize (M := Model E v a) z))))
      else .inr (.inl 0)) := by
  simp only [DenefPasForwardCodes.isAux_code]
  by_cases hp : ∀ i, IsRV ((p i 1).realize (M := Model E v a) z)
  · simp only [functionGraph, Formula.realize_sup, Formula.realize_inf, Formula.realize_not,
      Formula.realize_iInf, auxiliary_realize, hp, not_true_eq_false, false_and, or_false,
      if_true, functionGraphGood_realize E v a f p q z hp]
    simp
  · have hbad : ¬ (functionGraphGood f p q).Realize z := by
      intro h
      obtain ⟨σ, β, hσ, _, _⟩ := (functionGraphGood_patterns E v a f p q z).mp h
      exact hp (fun i => (hσ i).1)
    simp only [functionGraph, Formula.realize_sup, Formula.realize_inf, Formula.realize_not,
      Formula.realize_iInf, auxiliary_realize, hp, not_false_eq_true, true_and,
      zeroGraph_realize, hbad, false_or, if_false]

end SpecialTransformations.Section6.DenefPasForwardAuxiliary
end
end

/-! Source: Section6.DenefPasForwardEquality -/
section

/-! Equality and the two mixed-sort maps in the forward interpretation. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Section6.DenefPasForwardEquality
open AngularComponent DenefPasCodes DenefPasLanguage DenefPasNativeCodes DenefPasNativeModel
open DenefPasForwardPatterns

def coordinate (b : Bool) : Coord := if b then 1 else 0

def equalityFormula (E : _root_.FirstOrder.Language.{0, 0}) (b : Bool) :
    (DenefPasMorley.Auxiliary E).Formula (Fin 2 × Coord) :=
  (Term.var (0, coordinate b)).equal (.var (1, coordinate b))

def auxiliaryEquality {E : _root_.FirstOrder.Language.{0, 0}} {I : Type}
    (b : Bool) (p q : Coord → (Native E).Term I) : (Native E).Formula I :=
  category b p ⊓ (category b q ⊓
    Relations.formula (L := Native E) (.inr (equalityFormula E b)) ![p 1, q 1])

def equalityGraph {E : _root_.FirstOrder.Language.{0, 0}} {I : Type}
    (p q : Coord → (Native E).Term I) : (Native E).Formula I :=
  (field (p 1) ⊓ (p 1).equal (q 1)) ⊔ Formula.iSup (fun b => auxiliaryEquality b p q)

variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]

theorem equality_patterns (v : Valuation K Γ) (a : Data v) (p q : Coord → NativeCarrier v) :
    code v a p = code v a q ↔
      (DenefPasLanguage.IsField (p 1) ∧ p 1 = q 1) ∨
        ∃ b : Bool, Category b p ∧ Category b q ∧
          selected v a b (rvValue (p 1)) = selected v a b (rvValue (q 1)) := by
  cases hp : p 1 <;> cases hq : q 1 <;>
    by_cases ht : p 0 = .inl 0 <;> by_cases hu : q 0 = .inl 0 <;>
    simp [code, hp, hq, ht, hu, Category, selected, rvValue,
      DenefPasLanguage.IsField, IsRV, Bool.exists_bool]

section Semantics
variable (E : _root_.FirstOrder.Language.{0, 0}) (v : Valuation K Γ) (a : Data v)
variable [E.Structure (Aux v)]
local instance : (Native E).Structure (Model E v a) := structureOn E v a
local instance : DenefPasAux.auxLanguage.Structure (Aux v) := DenefPasAux.auxStructure
local instance : (DenefPasMorley.Auxiliary E).Structure (Aux v) :=
  FirstOrder.Language.sumStructure DenefPasAux.auxLanguage E (Aux v)

theorem equalityFormula_realize (b : Bool) (u : Fin 2 → RVCalc.RV v) :
    (equalityFormula E b).Realize (fun j => DenefPasNormalization.coordinates v a (u j.1) j.2) ↔
      selected v a b (u 0) = selected v a b (u 1) := by
  cases b <;> rfl

theorem auxiliaryEquality_realize {I : Type} (b : Bool)
    (p q : Coord → (Native E).Term I) (z : I → Model E v a) :
    (auxiliaryEquality b p q).Realize z ↔
      Category b (fun c => (p c).realize (M := Model E v a) z) ∧
      Category b (fun c => (q c).realize (M := Model E v a) z) ∧
        selected v a b (rvValue ((p 1).realize (M := Model E v a) z)) =
          selected v a b (rvValue ((q 1).realize (M := Model E v a) z)) := by
  simp only [auxiliaryEquality, Formula.realize_inf, category_realize, extra_realize]
  have he := equalityFormula_realize E v a b
    (fun i => rvValue ((![(p 1), (q 1)] i).realize (M := Model E v a) z))
  constructor
  · rintro ⟨hp, hq, _, hθ⟩
    exact ⟨hp, hq, he.mp hθ⟩
  · rintro ⟨hp, hq, hθ⟩
    refine ⟨hp, hq, ?_, he.mpr hθ⟩
    intro i
    fin_cases i
    · exact hp.1
    · exact hq.1

theorem equalityGraph_realize {I : Type} (p q : Coord → (Native E).Term I) (z : I → Model E v a) :
    (equalityGraph p q).Realize z ↔
      code v a (fun c => (p c).realize (M := Model E v a) z) =
        code v a (fun c => (q c).realize (M := Model E v a) z) := by
  simp only [equalityGraph, Formula.realize_sup, Formula.realize_inf, field_realize,
    Formula.realize_equal, Formula.realize_iSup, auxiliaryEquality_realize]
  exact (equality_patterns v a (fun c => (p c).realize (M := Model E v a) z)
    (fun c => (q c).realize (M := Model E v a) z)).symm

end Semantics
end SpecialTransformations.Section6.DenefPasForwardEquality
end
end

/-! Source: Section6.DenefPasForwardCross -/
section

/-! The angular-component and valuation graphs in the native interpretation. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Section6.DenefPasForwardCross
open AngularComponent DenefPasCodes DenefPasLanguage DenefPasNativeCodes DenefPasNativeModel
open DenefPasForwardPatterns DenefPasForwardEquality

def rvTerm {E : _root_.FirstOrder.Language.{0, 0}} {I : Type} (t : (Native E).Term I) :
    (Native E).Term I := .func (.inl .rvMap) ![t]

def graph {E : _root_.FirstOrder.Language.{0, 0}} {I : Type}
    (b : Bool) (p q : Coord → (Native E).Term I) : (Native E).Formula I :=
  category b q ⊓ Relations.formula (L := Native E)
    (.inr (equalityFormula E b)) ![q 1, rvTerm (p 1)]

variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]
variable (E : _root_.FirstOrder.Language.{0, 0}) (v : Valuation K Γ) (a : Data v)
variable [E.Structure (Aux v)]
local instance : (Native E).Structure (Model E v a) := structureOn E v a
local instance : DenefPasAux.auxLanguage.Structure (Aux v) := DenefPasAux.auxStructure
local instance : (DenefPasMorley.Auxiliary E).Structure (Aux v) :=
  FirstOrder.Language.sumStructure DenefPasAux.auxLanguage E (Aux v)

theorem rvTerm_realize {I : Type} (t : (Native E).Term I) (z : I → Model E v a) :
    (rvTerm t).realize (M := Model E v a) z =
      (Sum.inr (RVCalc.rv v (fieldValue (t.realize (M := Model E v a) z))) : Model E v a) := rfl

theorem category_of_selected (b : Bool) (p : Coord → NativeCarrier v) (u : RVCalc.RV v)
    (h : code v a p = .inr (selected v a b u)) : Category b p := by
  cases b
  · exact (DenefPasForwardCodes.isResidue_code v a p).mp ⟨_, h⟩
  · exact (DenefPasForwardCodes.isValue_code v a p).mp ⟨_, h⟩

theorem graph_realize {I : Type} (b : Bool) (p q : Coord → (Native E).Term I) (z : I → Model E v a) :
    (graph b p q).Realize z ↔ code v a (fun c => (q c).realize (M := Model E v a) z) =
      .inr (selected v a b (RVCalc.rv v
        (fieldValue (code v a (fun c => (p c).realize (M := Model E v a) z))))) := by
  simp only [graph, Formula.realize_inf, category_realize E v a, extra_realize E v a]
  rw [DenefPasForwardCodes.fieldValue_code]
  have he := equalityFormula_realize E v a b
    (fun i => rvValue ((![(q 1), rvTerm (p 1)] i).realize (M := Model E v a) z))
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, rvTerm_realize, rvValue, Sum.elim_inr] at he
  constructor
  · rintro ⟨hcat, _, hθ⟩
    rw [category_code v a b _ hcat]
    exact congrArg (Sum.inr : Aux v → Carrier v) (he.mp hθ)
  · intro h
    have hcat := category_of_selected v a b (fun c => (q c).realize (M := Model E v a) z) _ h
    refine ⟨hcat, ?_, he.mpr ?_⟩
    · intro i
      fin_cases i
      · exact hcat.1
      · exact ⟨_, rvTerm_realize E v a (p 1) z⟩
    · exact Sum.inr.inj ((category_code v a b _ hcat).symm.trans h)

theorem angular_realize {I : Type} (p q : Coord → (Native E).Term I) (z : I → Model E v a) :
    (graph false p q).Realize z ↔ code v a (fun c => (q c).realize (M := Model E v a) z) =
      .inr (.inl (a.ac (fieldValue (code v a (fun c => (p c).realize (M := Model E v a) z))))) := by
  rw [graph_realize]
  simp only [selected, Bool.false_eq_true, if_false, DenefPasCodes.residueValue_rv]

theorem value_realize {I : Type} (p q : Coord → (Native E).Term I) (z : I → Model E v a) :
    (graph true p q).Realize z ↔ code v a (fun c => (q c).realize (M := Model E v a) z) =
      .inr (.inr (gammaValue v a (RVCalc.rv v
        (fieldValue (code v a (fun c => (p c).realize (M := Model E v a) z)))))) := by
  rw [graph_realize]
  rfl

end SpecialTransformations.Section6.DenefPasForwardCross
end
end

/-! Source: Section6.DenefPasForwardDictionary -/
section

/-! The complete fixed forward dictionary. The source is the actual
three-sort DP signature; the target is a relational RV expansion of the
published native language. This is an interpretation, not a QE hypothesis. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.Section6.DenefPasLanguage.language
open Classical FirstOrder FirstOrder.Language

namespace SpecialTransformations.Section6.DenefPasForwardDictionary
open AngularComponent DenefPasCodes DenefPasLanguage DenefPasNativeModel
open DenefPasForwardPatterns

def arg {E : _root_.FirstOrder.Language.{0, 0}} {k : ℕ} (i : Fin k) (b : Coord) :
    (Native E).Term ((Fin k × Coord) ⊕ Coord) := .var (.inl (i, b))
def output {E : _root_.FirstOrder.Language.{0, 0}} {k : ℕ} (b : Coord) :
    (Native E).Term ((Fin k × Coord) ⊕ Coord) := .var (.inr b)
def relArg {E : _root_.FirstOrder.Language.{0, 0}} {k : ℕ} (i : Fin k) (b : Coord) :
    (Native E).Term (Fin k × Coord) := .var (i, b)

def dictionary (E : _root_.FirstOrder.Language.{0, 0}) : PairSyntax.Syntax (language E) (Native E) where
  equality := DenefPasForwardEquality.equalityGraph (fun b => .var (.inl b)) (fun b => .var (.inr b))
  functionGraph := fun f => match f with
    | .inl f => DenefPasForwardPatterns.fieldGraph f arg output
    | .inr (.inl f) => DenefPasForwardAuxiliary.functionGraph f arg output
    | .inr (.inr .angular) => DenefPasForwardCross.graph false (arg 0) output
    | .inr (.inr .value) => DenefPasForwardCross.graph true (arg 0) output
  relationGraph := fun r => match r with
    | .inl .field => field (relArg 0 1)
    | .inl .residue => category false (relArg 0)
    | .inl .value => category true (relArg 0)
    | .inr r => DenefPasForwardAuxiliary.relationGraph r relArg

variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]
variable (E : _root_.FirstOrder.Language.{0, 0}) (v : Valuation K Γ) (a : Data v)
variable [E.Structure (Aux v)]
local instance : (Native E).Structure (Model E v a) := structureOn E v a
local instance : (language E).Structure (DenefPasAuxLift.Model E v a) := dpStructure E v a
local instance : DenefPasAux.auxLanguage.Structure (Aux v) := DenefPasAux.auxStructure
local instance : (DenefPasMorley.Auxiliary E).Structure (Aux v) :=
  FirstOrder.Language.sumStructure DenefPasAux.auxLanguage E (Aux v)

def code : (Coord → Model E v a) → DenefPasAuxLift.Model E v a := DenefPasNativeCodes.code v a

def realizes : PairSyntax.Realizes (dictionary E) (DenefPasAuxLift.Model E v a) (Model E v a) where
  code := code E v a
  onto := DenefPasNativeCodes.code_surjective v a
  equality := fun w => by
    simpa only [dictionary, code, Term.realize_var, Function.comp_def] using
      DenefPasForwardEquality.equalityGraph_realize E v a
        (fun b => .var (.inl b)) (fun b => .var (.inr b)) w
  functionGraph := fun f w => by
    cases f with
    | inl f =>
      change (DenefPasForwardPatterns.fieldGraph f arg output).Realize w ↔
        DenefPasNativeCodes.code v a (w ∘ Sum.inr) = .inl
          (fieldFunction f (fun i => DenefPasNativeCodes.code v a (fun b => w (.inl (i, b)))))
      simpa only [arg, output, Term.realize_var, Function.comp_def] using
        DenefPasForwardPatterns.fieldGraph_realize E v a f arg output w
    | inr f =>
      cases f with
      | inl f =>
        simpa only [dictionary, code, arg, output, Term.realize_var, Function.comp_def,
          PairInterpretation.decode, Structure.funMap, dpStructure] using
          DenefPasForwardAuxiliary.functionGraph_realize E v a f arg output w
      | inr f =>
        cases f with
        | angular =>
          simpa only [dictionary, code, arg, output, Term.realize_var, Function.comp_def,
            PairInterpretation.decode, Structure.funMap, dpStructure] using
            DenefPasForwardCross.angular_realize E v a (arg 0) output w
        | value =>
          simpa only [dictionary, code, arg, output, Term.realize_var, Function.comp_def,
            PairInterpretation.decode, Structure.funMap, dpStructure] using
            DenefPasForwardCross.value_realize E v a (arg 0) output w
  relationGraph := fun r w => by
    cases r with
    | inl r =>
      cases r with
      | field =>
        have h := DenefPasForwardPatterns.field_realize E v a (relArg 0 1) w
        simpa only [dictionary, code, relArg, Term.realize_var, Function.comp_def,
          PairInterpretation.decode, Structure.RelMap, dpStructure,
          DenefPasForwardCodes.isField_code] using h
      | residue =>
        have h := DenefPasForwardPatterns.category_realize E v a false (relArg 0) w
        simpa only [dictionary, code, relArg, Term.realize_var, Function.comp_def,
          PairInterpretation.decode, Structure.RelMap, dpStructure, Category,
          Bool.false_eq_true, if_false, DenefPasForwardCodes.isResidue_code] using h
      | value =>
        have h := DenefPasForwardPatterns.category_realize E v a true (relArg 0) w
        simpa only [dictionary, code, relArg, Term.realize_var, Function.comp_def,
          PairInterpretation.decode, Structure.RelMap, dpStructure, Category,
          Bool.true_eq, if_true, DenefPasForwardCodes.isValue_code] using h
    | inr r =>
      simpa only [dictionary, code, relArg, Term.realize_var, Function.comp_def,
        PairInterpretation.decode, Structure.RelMap, dpStructure] using
        DenefPasForwardAuxiliary.relationGraph_realize E v a r relArg w

theorem formula_realize {I : Type} (φ : (language E).Formula I) (z : (I × Coord) → Model E v a) :
    (PairSyntax.formula (dictionary E) φ).Realize z ↔
      φ.Realize (PairInterpretation.decode (code E v a) z) :=
  PairSyntax.formula_realize (dictionary E) (realizes E v a) φ z

end SpecialTransformations.Section6.DenefPasForwardDictionary
end
end

/-! Source: Section6.DenefPasFieldTerms -/
section

/-! A native VF polynomial is still an ordinary DP ring term. Only the
published field symbols are mapped; there is no VF inverse. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Section6.DenefPasFieldTerms
open AngularComponent DenefPasCodes DenefPasLanguage DenefPasNativeModel
open DenefPasForwardPatterns RVTermSupport

def term {E : _root_.FirstOrder.Language.{0, 0}} {V : Type} : (Native E).Term V → (language E).Term V
  | .var i => .var i
  | .func f ts => match f with
    | .inl .vfZero => .func (.inl ⟨.vfZero, rfl, fun i => i.elim0⟩) Fin.elim0
    | .inl .vfOne => .func (.inl ⟨.vfOne, rfl, fun i => i.elim0⟩) Fin.elim0
    | .inl .vfAdd => .func (.inl ⟨.vfAdd, rfl, fun _ => rfl⟩) (fun i => term (ts i))
    | .inl .vfNeg => .func (.inl ⟨.vfNeg, rfl, fun _ => rfl⟩) (fun i => term (ts i))
    | .inl .vfMul => .func (.inl ⟨.vfMul, rfl, fun _ => rfl⟩) (fun i => term (ts i))
    | _ => .func (.inl ⟨.vfZero, rfl, fun i => i.elim0⟩) Fin.elim0

def evaluate {E : _root_.FirstOrder.Language.{0, 0}} {V K : Type} [Field K]
    (x : V → K) : (Native E).Term V → K
  | .var i => x i
  | .func f ts => match f with
    | .inl .vfZero => 0
    | .inl .vfOne => 1
    | .inl .vfAdd => evaluate x (ts 0) + evaluate x (ts 1)
    | .inl .vfNeg => -evaluate x (ts 0)
    | .inl .vfMul => evaluate x (ts 0) * evaluate x (ts 1)
    | _ => 0

variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]
variable (E : _root_.FirstOrder.Language.{0, 0}) (v : Valuation K Γ) (a : Data v)
variable [E.Structure (Aux v)]
local instance : (Native E).Structure (Model E v a) := structureOn E v a
local instance : (language E).Structure (DenefPasAuxLift.Model E v a) := dpStructure E v a

theorem realize {V : Type} (p : (Native E).Term V)
    (hp : termSort (fun _ => .vf) p = some .vf) (x : V → K) :
    p.realize (M := Model E v a) (Sum.inl ∘ x) = Sum.inl (evaluate x p) ∧
      (term p).realize (M := DenefPasAuxLift.Model E v a) (Sum.inl ∘ x) = Sum.inl (evaluate x p) := by
  induction p with
  | var i => exact ⟨rfl, rfl⟩
  | @func k f ts ih =>
    obtain ⟨harg, hres⟩ := (termSort_func (fun _ => .vf) f ts).mp hp
    have hs : ∀ i, argumentSort f i = .vf := by
      cases f with
      | inr f => cases hres
      | inl f =>
        cases f <;> try cases hres
        all_goals intro i; first | exact i.elim0 | rfl
    have hn : (fun i => (ts i).realize (M := Model E v a) (Sum.inl ∘ x)) =
        (fun i => (Sum.inl (evaluate x (ts i)) : Model E v a)) := by
      funext i
      exact (ih i ((harg i).trans (congrArg some (hs i)))).1
    have hd : (fun i => (term (ts i)).realize (M := DenefPasAuxLift.Model E v a) (Sum.inl ∘ x)) =
        (fun i => (Sum.inl (evaluate x (ts i)) : DenefPasAuxLift.Model E v a)) := by
      funext i
      exact (ih i ((harg i).trans (congrArg some (hs i)))).2
    have hn' (i : Fin k) := congrFun hn i
    have hd' (i : Fin k) := congrFun hd i
    cases f with
    | inr f => cases hres
    | inl f =>
      cases f <;> try cases hres
      all_goals
        simp only [term, evaluate, Term.realize_func, Structure.funMap, structureOn,
          nativeFunction, dpStructure]
        simp [hn', hd', fieldFunction, DenefPasLanguage.IsField, fieldValue]

end SpecialTransformations.Section6.DenefPasFieldTerms
end
end

/-! Source: Section6.DenefPasPolynomialCodes -/
section

/-! The two source terms coding each polynomial leaf: ac(P), val(P). -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language

namespace SpecialTransformations.Section6.DenefPasPolynomialCodes
open AngularComponent DenefPasCodes DenefPasLanguage DenefPasNativeModel DenefPasForwardPatterns

def coordinateTerm {E : _root_.FirstOrder.Language.{0, 0}} {V : Type}
    (p : (Native E).Term V) : Coord → (language E).Term V :=
  ![.func (.inr (.inr .angular)) ![DenefPasFieldTerms.term p],
    .func (.inr (.inr .value)) ![DenefPasFieldTerms.term p] ]

variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]
variable (E : _root_.FirstOrder.Language.{0, 0}) (v : Valuation K Γ) (a : Data v)
variable [E.Structure (Aux v)]
local instance : (language E).Structure (DenefPasAuxLift.Model E v a) := dpStructure E v a

theorem isAux_realize {V : Type} (p : (Native E).Term V)
    (z : V → DenefPasAuxLift.Model E v a) (b : Coord) :
    IsAux ((coordinateTerm p b).realize (M := DenefPasAuxLift.Model E v a) z) := by
  fin_cases b <;> exact ⟨_, rfl⟩

theorem realize {V : Type} (p : (Native E).Term V)
    (hp : RVTermSupport.termSort (fun _ => .vf) p = some .vf) (x : V → K) (b : Coord) :
    (coordinateTerm p b).realize (M := DenefPasAuxLift.Model E v a) (Sum.inl ∘ x) =
      Sum.inr (DenefPasNormalization.coordinates v a (RVCalc.rv v (DenefPasFieldTerms.evaluate x p)) b) := by
  fin_cases b
  · change Sum.inr (Sum.inl (a.ac (fieldValue
      ((DenefPasFieldTerms.term p).realize (M := DenefPasAuxLift.Model E v a) (Sum.inl ∘ x))))) =
        Sum.inr (Sum.inl (residueValue v a (RVCalc.rv v (DenefPasFieldTerms.evaluate x p))))
    rw [(DenefPasFieldTerms.realize E v a p hp x).2, residueValue_rv]
    rfl
  · change Sum.inr (Sum.inr (gammaValue v a (RVCalc.rv v (fieldValue
      ((DenefPasFieldTerms.term p).realize (M := DenefPasAuxLift.Model E v a) (Sum.inl ∘ x)))))) =
        Sum.inr (Sum.inr (gammaValue v a (RVCalc.rv v (DenefPasFieldTerms.evaluate x p))))
    rw [(DenefPasFieldTerms.realize E v a p hp x).2]
    rfl

theorem decode_realize {V : Type} (p : (Native E).Term V)
    (hp : RVTermSupport.termSort (fun _ => .vf) p = some .vf) (x : V → K) :
    decode v a (fun b => auxValue ((coordinateTerm p b).realize
      (M := DenefPasAuxLift.Model E v a) (Sum.inl ∘ x))) =
        RVCalc.rv v (DenefPasFieldTerms.evaluate x p) := by
  have he : (fun b => auxValue ((coordinateTerm p b).realize
      (M := DenefPasAuxLift.Model E v a) (Sum.inl ∘ x))) =
        DenefPasNormalization.coordinates v a (RVCalc.rv v (DenefPasFieldTerms.evaluate x p)) := by
    funext b
    rw [realize E v a p hp x b]
    rfl
  rw [he, DenefPasNormalization.decode_coordinates]

end SpecialTransformations.Section6.DenefPasPolynomialCodes
end
end

/-! Source: Section6.DenefPasRVReduct -/
section

/-! Compatibility of the actual RV reduct with polynomial abstraction.
The abstraction theorem itself is reused from RVAbstraction. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Section6.DenefPasRVReduct
open AngularComponent DenefPasCodes RVAbstraction RVGraphLanguage DenefPasNativeModel
open DenefPasForwardPatterns
variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]
variable (E : _root_.FirstOrder.Language.{0, 0}) (v : Valuation K Γ) (a : Data v)
variable [E.Structure (Aux v)]

abbrev Q := DenefPasDictionary.Model v a
local instance : DenefPasAux.auxLanguage.Structure (Aux v) := DenefPasAux.auxStructure
local instance : (DenefPasMorley.Auxiliary E).Structure (Aux v) :=
  FirstOrder.Language.sumStructure DenefPasAux.auxLanguage E (Aux v)
local instance : RVBase.Structure (Q v a) := DenefPasRV.rvStructure v a
local instance : (DenefPasMorley.signature E).Structure (Q v a) := DenefPasMorley.rvStructure E v a
local instance : (Auxiliary (DenefPasMorley.signature E)).Structure (Q v a) :=
  FirstOrder.Language.sumStructure RVBase (DenefPasMorley.signature E) (Q v a)
local instance : (Native E).Structure (Model E v a) := structureOn E v a

def inclusion : Q v a → Model E v a := Sum.inr

theorem inclusion_injective : Function.Injective (inclusion E v a) := fun _ _ h => Sum.inr.inj h

theorem functions : Compatible (E := DenefPasMorley.signature E) (inclusion E v a) := by
  constructor
  · intro k f z
    change Sum.inr (@Structure.funMap RVBase (RVCalc.RV v) (DenefPasRV.rvStructure v a) k f z) =
      nativeFunction v a f.val (Sum.inr ∘ z)
    exact (nativeFunction_rv v a f z).symm
  · intro k f
    exact isEmptyElim f

theorem relations : RelationsCompatible (E := DenefPasMorley.signature E) (inclusion E v a) := by
  intro k r z
  cases r with
  | inl r =>
    rcases r with ⟨r, hr⟩
    cases r with
    | memVF => have h := hr 0; cases h
    | memRV =>
      change True ↔ IsRV (Sum.inr (z 0) : DenefPasNativeCodes.NativeCarrier v)
      simp [IsRV]
    | memUnits =>
      change (z 0 ≠ none ∧ gammaValue v a (z 0) = 1) ↔
        IsRV (Sum.inr (z 0) : DenefPasNativeCodes.NativeCarrier v) ∧
          rvValue (Sum.inr (z 0)) ≠ none ∧ gammaValue v a (rvValue (Sum.inr (z 0))) = 1
      simp [IsRV, rvValue]
    | rvLe =>
      change (gammaValue v a (z 1) ≤ gammaValue v a (z 0)) ↔
        (∀ i, IsRV (Sum.inr (z i) : DenefPasNativeCodes.NativeCarrier v)) ∧
          gammaValue v a (rvValue (Sum.inr (z 1))) ≤ gammaValue v a (rvValue (Sum.inr (z 0)))
      simp [IsRV, rvValue]
  | inr θ =>
    change θ.Realize (fun j => DenefPasNormalization.coordinates v a (z j.1) j.2) ↔
      (∀ i, IsRV (Sum.inr (z i) : DenefPasNativeCodes.NativeCarrier v)) ∧
        θ.Realize (fun j => DenefPasNormalization.coordinates v a (rvValue (Sum.inr (z j.1))) j.2)
    simp [IsRV, rvValue]

theorem guard : GuardCompatible (E := DenefPasMorley.signature E) (inclusion E v a) := by
  intro x
  change IsRV x ↔ ∃ q : Q v a, Sum.inr q = x
  exact ⟨fun ⟨q, h⟩ => ⟨q, h.symm⟩, fun ⟨q, h⟩ => ⟨q, h.symm⟩⟩

def coefficient {V : Type} (u : V → Model E v a) (p : (Native E).Term V) : Q v a :=
  RVCalc.rv v (DenefPasLanguage.fieldValue (p.realize (M := Model E v a) u))

theorem coefficient_realize {V : Type} (u : V → Model E v a) (p : (Native E).Term V) :
    inclusion E v a (coefficient E v a u p) = (RVTermSupport.rvTerm p).realize (M := Model E v a) u := rfl

theorem formula_realize {V R : Type} (φ : (Native E).Formula (V ⊕ R)) (hφ : Fragment φ)
    (u : V → Model E v a) (r : R → Q v a) :
    Formula.Realize (RVAbstraction.formula φ) (Sum.elim (coefficient E v a u) r) ↔
      φ.Realize (Sum.elim u (inclusion E v a ∘ r)) := by
  have h := RVAbstraction.formula_realize (inclusion E v a) (inclusion_injective E v a)
    (functions E v a) (relations E v a) (guard E v a) u r (coefficient E v a u)
    (fun p _ => coefficient_realize E v a u p) φ hφ (default : Fin 0 → Q v a)
  have h0 : inclusion E v a ∘ (default : Fin 0 → Q v a) = (default : Fin 0 → Model E v a) :=
    Subsingleton.elim _ _
  simpa only [Formula.Realize, h0] using h

end SpecialTransformations.Section6.DenefPasRVReduct
end
end

/-! Source: Section6.DenefPasParameters -/
section

/-! Original free parameters and the sorts of their canonical native codes.
This introduces no new parameter names in the DP output. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Section6.DenefPasParameters
open AngularComponent DenefPasCodes DenefPasLanguage DenefPasNativeModel DenefPasForwardPatterns
open FiniteSortContext

abbrev SortKind := SortRelation 1

def nativeSort {I : Type} (s : I → SortKind) (j : I × Coord) : SortTag :=
  match s j.1 with
  | .field => .vf
  | .residue => if j.2 = 0 then .vf else .rv
  | .value => .rv

def fieldZero {E : _root_.FirstOrder.Language.{0, 0}} {I : Type} : (language E).Term I :=
  .func (.inl ⟨.vfZero, rfl, fun i => i.elim0⟩) Fin.elim0

def auxiliaryConstant {E : _root_.FirstOrder.Language.{0, 0}} {I : Type}
    (f : DenefPasAux.Functions 0) : (language E).Term I :=
  .func (.inr (.inl (.inl f))) Fin.elim0

def fieldParameter {E : _root_.FirstOrder.Language.{0, 0}} {I : Type} (s : I → SortKind)
    (j : VFPart (nativeSort s)) : (language E).Term I :=
  if j.val.2 = 0 then fieldZero else .var j.val.1

def rvParameter {E : _root_.FirstOrder.Language.{0, 0}} {I : Type} (s : I → SortKind)
    (j : RVPart (nativeSort s)) : Coord → (language E).Term I :=
  match s j.val.1 with
  | .field => ![auxiliaryConstant .rZero, auxiliaryConstant .gInfinity]
  | .residue => ![.var j.val.1, auxiliaryConstant .gOne]
  | .value => if j.val.2 = 0 then ![auxiliaryConstant .rZero, auxiliaryConstant .gInfinity]
      else ![auxiliaryConstant .rOne, .var j.val.1]

variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]
variable (E : _root_.FirstOrder.Language.{0, 0}) (v : Valuation K Γ) (a : Data v)
variable [E.Structure (Aux v)]
local instance : (Native E).Structure (Model E v a) := structureOn E v a
local instance : (language E).Structure (DenefPasAuxLift.Model E v a) := dpStructure E v a

def Sorted {I : Type} (s : I → SortKind) (z : I → DenefPasAuxLift.Model E v a) : Prop :=
  ∀ i, match s i with
  | .field => DenefPasLanguage.IsField (z i)
  | .residue => ∃ r : Residue v, z i = .inr (.inl r)
  | .value => ∃ g : Gamma v, z i = .inr (.inr g)

def packed {I : Type} (z : I → DenefPasAuxLift.Model E v a) : (I × Coord) → Model E v a :=
  fun j => DenefPasNativeCodes.pack v a (z j.1) j.2

theorem fieldZero_realize {I : Type} (z : I → DenefPasAuxLift.Model E v a) :
    (fieldZero : (language E).Term I).realize z = (Sum.inl 0 : DenefPasAuxLift.Model E v a) := by
  simp [fieldZero, Term.realize, Structure.funMap, dpStructure, fieldFunction, DenefPasLanguage.IsField]

def constantValue (f : DenefPasAux.Functions 0) : Aux v :=
  match f with
  | .rZero => .inl 0
  | .rOne => .inl 1
  | .gInfinity => .inr 0
  | .gOne => .inr 1

theorem auxiliaryConstant_realize {I : Type} (f : DenefPasAux.Functions 0)
    (z : I → DenefPasAuxLift.Model E v a) :
    (auxiliaryConstant f : (language E).Term I).realize z =
      (Sum.inr (constantValue v f) : DenefPasAuxLift.Model E v a) := by
  cases f <;> simp [auxiliaryConstant, Term.realize, Structure.funMap, dpStructure,
    FirstOrder.Language.sumStructure, DenefPasAux.auxStructure, constantValue]

theorem packed_sorts {I : Type} (s : I → SortKind) (z : I → DenefPasAuxLift.Model E v a)
    (hz : Sorted E v a s z) (j : I × Coord) :
    ExpandedLogic.tagEval (E := DenefPasMorley.signature E) (M := Model E v a)
      (nativeSort s j) (packed E v a z j) := by
  rcases j with ⟨i, b⟩
  have hi := hz i
  cases hs : s i with
  | field =>
    rw [hs] at hi
    obtain ⟨x, hx⟩ := hi
    fin_cases b <;>
      simp [nativeSort, hs, packed, hx, DenefPasNativeCodes.pack, ExpandedLogic.tagEval, ExpandedLogic.sortRelation,
        Structure.RelMap, structureOn, nativeRelation, DenefPasLanguage.IsField, IsRV]

  | residue =>
    rw [hs] at hi
    obtain ⟨r, hr⟩ := hi
    fin_cases b <;>
      simp [nativeSort, hs, packed, hr, DenefPasNativeCodes.pack, ExpandedLogic.tagEval, ExpandedLogic.sortRelation,
        Structure.RelMap, structureOn, nativeRelation, DenefPasLanguage.IsField, IsRV]
  | value =>
    rw [hs] at hi
    obtain ⟨g, hg⟩ := hi
    fin_cases b <;>
      simp [nativeSort, hs, packed, hg, DenefPasNativeCodes.pack, ExpandedLogic.tagEval, ExpandedLogic.sortRelation,
        Structure.RelMap, structureOn, nativeRelation, DenefPasLanguage.IsField, IsRV]

theorem packed_vf {I : Type} (s : I → SortKind) (z : I → DenefPasAuxLift.Model E v a)
    (hz : Sorted E v a s z) (j : VFPart (nativeSort s)) :
    packed E v a z j.val = Sum.inl (fieldValue (packed E v a z j.val)) := by
  have h := packed_sorts E v a s z hz j.val
  rw [j.property] at h
  change DenefPasLanguage.IsField (packed E v a z j.val) at h
  obtain ⟨x, hx⟩ := h
  rw [hx]
  rfl

theorem packed_rv {I : Type} (s : I → SortKind) (z : I → DenefPasAuxLift.Model E v a)
    (hz : Sorted E v a s z) (j : RVPart (nativeSort s)) :
    packed E v a z j.val = DenefPasRVReduct.inclusion E v a (rvValue (packed E v a z j.val)) := by
  have h := packed_sorts E v a s z hz j.val
  rw [j.property] at h
  change IsRV (packed E v a z j.val) at h
  obtain ⟨q, hq⟩ := h
  rw [hq]
  rfl

theorem fieldParameter_realize {I : Type} (s : I → SortKind) (z : I → DenefPasAuxLift.Model E v a)
    (hz : Sorted E v a s z) (j : VFPart (nativeSort s)) :
    (fieldParameter (E := E) s j).realize (M := DenefPasAuxLift.Model E v a) z =
      Sum.inl (fieldValue (packed E v a z j.val)) := by
  rcases j with ⟨⟨i, b⟩, hj⟩
  have hi := hz i
  cases hs : s i with
  | field =>
    rw [hs] at hi
    obtain ⟨x, hx⟩ := hi
    fin_cases b <;>
      simp [fieldParameter, fieldZero_realize E v a, Term.realize_var, packed,
        DenefPasNativeCodes.pack, hx, fieldValue]
  | residue =>
    rw [hs] at hi
    obtain ⟨r, hr⟩ := hi
    fin_cases b
    · simp [fieldParameter, fieldZero_realize E v a, packed, DenefPasNativeCodes.pack, hr, fieldValue]
    · simp [nativeSort, hs] at hj
  | value => simp [nativeSort, hs] at hj

theorem rvParameter_decode {I : Type} (s : I → SortKind) (z : I → DenefPasAuxLift.Model E v a)
    (hz : Sorted E v a s z) (j : RVPart (nativeSort s)) :
    decode v a (fun c => auxValue ((rvParameter (E := E) s j c).realize (M := DenefPasAuxLift.Model E v a) z)) =
      rvValue (packed E v a z j.val) := by
  rcases j with ⟨⟨i, b⟩, hj⟩
  have hi := hz i
  cases hs : s i with
  | field => simp [nativeSort, hs] at hj
  | residue =>
    rw [hs] at hi
    obtain ⟨r, hr⟩ := hi
    fin_cases b
    · simp [nativeSort, hs] at hj
    · simp [rvParameter, hs, auxiliaryConstant_realize E v a, constantValue, Term.realize_var,
        packed, DenefPasNativeCodes.pack, hr, rvValue, auxValue, decode, residueCoord, valueCoord]
      rfl
  | value =>
    rw [hs] at hi
    obtain ⟨g, hg⟩ := hi
    fin_cases b
    · simp [rvParameter, hs, auxiliaryConstant_realize E v a, constantValue,
        packed, DenefPasNativeCodes.pack, hg, rvValue, auxValue, decode, residueCoord, valueCoord]
    · cases g <;>
        simp [rvParameter, hs, auxiliaryConstant_realize E v a, constantValue, Term.realize_var,
          packed, DenefPasNativeCodes.pack, hg, DenefPasNativeCodes.valueRepresentative,
          rvValue, auxValue, decode, residueCoord, valueCoord]

theorem rvParameter_isAux {I : Type} (s : I → SortKind) (z : I → DenefPasAuxLift.Model E v a)
    (hz : Sorted E v a s z) (j : RVPart (nativeSort s)) (c : Coord) :
    IsAux ((rvParameter (E := E) s j c).realize (M := DenefPasAuxLift.Model E v a) z) := by
  rcases j with ⟨⟨i, b⟩, hj⟩
  have hi := hz i
  cases hs : s i with
  | field => simp [nativeSort, hs] at hj
  | residue =>
    rw [hs] at hi
    obtain ⟨r, hr⟩ := hi
    fin_cases c <;> simp [rvParameter, hs, auxiliaryConstant_realize E v a, Term.realize_var, hr, IsAux]
  | value =>
    rw [hs] at hi
    obtain ⟨g, hg⟩ := hi
    by_cases hb : b = 0 <;> fin_cases c <;>
      simp [rvParameter, hs, hb, auxiliaryConstant_realize E v a, Term.realize_var, hg, IsAux]

end SpecialTransformations.Section6.DenefPasParameters
end
end

/-! Source: Section6.DenefPasSubstitution -/
section

/-! Substitution keeps the strict RF/Gamma quantifier class. This follows
the parameter-free guard argument in retained Shared/SubstParam, applied
to the DP signature and Mathlib's existing substitution operation. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language

namespace SpecialTransformations.Section6.DenefPasSubstitution
open DenefPasLanguage DenefPasCodes AngularComponent

theorem guard_subst {E : Language} {I J : Type} {n : ℕ}
    (r : SortRelation 1) (f : I → (language E).Term J) :
    (guard r : (language E).BoundedFormula I (n + 1)).subst f =
      (guard r : (language E).BoundedFormula J (n + 1)) := by
  simp only [DenefPasLanguage.guard, BoundedFormula.subst, BoundedFormula.mapTermRel]
  congr 1
  funext i
  fin_cases i
  rfl

theorem allResidue_subst {E : Language} {I J : Type} {n : ℕ}
    (φ : (language E).BoundedFormula I (n + 1)) (f : I → (language E).Term J) :
    (allResidue φ).subst f = allResidue (φ.subst f) := by
  change (((guard .residue).subst f) ⟹ φ.subst f).all = _
  rw [guard_subst]
  rfl

theorem allValue_subst {E : Language} {I J : Type} {n : ℕ}
    (φ : (language E).BoundedFormula I (n + 1)) (f : I → (language E).Term J) :
    (allValue φ).subst f = allValue (φ.subst f) := by
  change (((guard .value).subst f) ⟹ φ.subst f).all = _
  rw [guard_subst]
  rfl

theorem isFieldQF_subst {E : Language} {I J : Type} {n : ℕ}
    (f : I → (language E).Term J) {φ : (language E).BoundedFormula I n}
    (hφ : IsFieldQF φ) : IsFieldQF (φ.subst f) := by
  induction hφ with
  | falsum => exact .falsum
  | atomic hφ => cases hφ with
    | equal t u => exact .atomic (.equal _ _)
    | rel r ts => exact .atomic (.rel _ _)
  | imp hφ hψ ihφ ihψ => exact .imp ihφ ihψ
  | residue hφ ih => rw [allResidue_subst]; exact .residue ih
  | value hφ ih => rw [allValue_subst]; exact .value ih

variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]
variable (E : Language) (v : Valuation K Γ) (a : Data v) [E.Structure (Aux v)]
local instance : DenefPasAux.auxLanguage.Structure (Aux v) := DenefPasAux.auxStructure
local instance : (DenefPasAuxLift.Auxiliary E).Structure (Aux v) :=
  FirstOrder.Language.sumStructure DenefPasAux.auxLanguage E (Aux v)
local instance : (language E).Structure (DenefPasAuxLift.Model E v a) := dpStructure E v a

theorem subst_realize {I J : Type} (φ : (DenefPasAuxLift.Auxiliary E).Formula I)
    (f : I → (language E).Term J) (z : J → DenefPasAuxLift.Model E v a)
    (hf : ∀ i, IsAux ((f i).realize (M := DenefPasAuxLift.Model E v a) z)) :
    Formula.Realize ((DenefPasAuxLift.lift φ).subst f) z ↔
      φ.Realize (fun i => auxValue ((f i).realize (M := DenefPasAuxLift.Model E v a) z)) := by
  let u : I → Aux v := fun i => auxValue ((f i).realize (M := DenefPasAuxLift.Model E v a) z)
  have he : (fun i => (f i).realize (M := DenefPasAuxLift.Model E v a) z) = DenefPasAuxLift.embed E v a ∘ u := by
    funext i
    obtain ⟨q, hq⟩ := hf i
    simp only [Function.comp_apply, u, DenefPasAuxLift.embed, hq, auxValue]
  rw [Formula.Realize, BoundedFormula.realize_subst, he]
  convert (DenefPasAuxLift.realize E v a φ u (Fin.elim0 : Fin 0 → Aux v)) using 1
  · apply iff_of_eq
    congr 1
    exact Subsingleton.elim (α := Fin 0 → DenefPasAuxLift.Model E v a) _ _
  · simp only [Formula.Realize, u]
    apply iff_of_eq
    congr 1

end SpecialTransformations.Section6.DenefPasSubstitution
end
end

/-! Source: Section6.DenefPasReturnParameters -/
section

/-! Substitute every backwards auxiliary coordinate by a term over the
original free context. Polynomial leaves use ac(P), val(P); old RV code
parameters use their original RF/Gamma parameter and the fixed tag terms. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language

namespace SpecialTransformations.Section6.DenefPasReturnParameters
open AngularComponent DenefPasCodes DenefPasLanguage DenefPasNativeModel DenefPasForwardPatterns
open DenefPasParameters FiniteSortContext

abbrev Leaves (E : _root_.FirstOrder.Language.{0, 0}) {I : Type} (s : I → SortKind) :=
  (Native E).Term (VFPart (nativeSort s)) ⊕ RVPart (nativeSort s)

def replacement {E : _root_.FirstOrder.Language.{0, 0}} {I : Type} (s : I → SortKind)
    (j : Leaves E s × Coord) : (language E).Term I :=
  match j.1 with
  | .inl p => (DenefPasPolynomialCodes.coordinateTerm p j.2).subst (fieldParameter (E := E) s)
  | .inr r => rvParameter (E := E) s r j.2

variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]
variable (E : _root_.FirstOrder.Language.{0, 0}) (v : Valuation K Γ) (a : Data v)
variable [E.Structure (Aux v)]
local instance : (Native E).Structure (Model E v a) := structureOn E v a
local instance : (language E).Structure (DenefPasAuxLift.Model E v a) := dpStructure E v a

def fieldValues {I : Type} (s : I → SortKind) (z : I → DenefPasAuxLift.Model E v a)
    (j : VFPart (nativeSort s)) : K := fieldValue (packed E v a z j.val)

theorem replacement_isAux {I : Type} (s : I → SortKind) (z : I → DenefPasAuxLift.Model E v a)
    (hz : Sorted E v a s z) (j : Leaves E s × Coord) :
    IsAux ((replacement s j).realize (M := DenefPasAuxLift.Model E v a) z) := by
  rcases j with ⟨p | r, b⟩
  · simp only [replacement, Term.realize_subst]
    exact DenefPasPolynomialCodes.isAux_realize E v a p _ b
  · exact rvParameter_isAux E v a s z hz r b

def coefficient {I : Type} (s : I → SortKind) (z : I → DenefPasAuxLift.Model E v a)
    (p : (Native E).Term (VFPart (nativeSort s))) : DenefPasDictionary.Model v a :=
  decode v a (fun b => auxValue ((replacement s (.inl p, b)).realize (M := DenefPasAuxLift.Model E v a) z))

theorem coefficient_eq {I : Type} (s : I → SortKind) (z : I → DenefPasAuxLift.Model E v a)
    (hz : Sorted E v a s z) (p : (Native E).Term (VFPart (nativeSort s)))
    (hp : RVTermSupport.termSort (fun _ => .vf) p = some .vf) :
    coefficient E v a s z p = RVCalc.rv v (DenefPasFieldTerms.evaluate (fieldValues E v a s z) p) := by
  unfold coefficient
  simp only [replacement, Term.realize_subst]
  have he : (fun j => (fieldParameter (E := E) s j).realize (M := DenefPasAuxLift.Model E v a) z) =
      Sum.inl ∘ fieldValues E v a s z := by
    funext j
    exact fieldParameter_realize E v a s z hz j
  rw [he]
  exact DenefPasPolynomialCodes.decode_realize E v a p hp (fieldValues E v a s z)

theorem coefficient_realize {I : Type} (s : I → SortKind) (z : I → DenefPasAuxLift.Model E v a)
    (hz : Sorted E v a s z) (p : (Native E).Term (VFPart (nativeSort s)))
    (hp : RVTermSupport.termSort (fun _ => .vf) p = some .vf) :
    DenefPasRVReduct.inclusion E v a (coefficient E v a s z p) =
      (RVTermSupport.rvTerm p).realize (M := Model E v a) (fun j => packed E v a z j.val) := by
  rw [coefficient_eq E v a s z hz p hp]
  have he : (fun j : VFPart (nativeSort s) => packed E v a z j.val) =
      Sum.inl ∘ fieldValues E v a s z := by
    funext j
    exact packed_vf E v a s z hz j
  rw [he]
  change Sum.inr (RVCalc.rv v (DenefPasFieldTerms.evaluate (fieldValues E v a s z) p)) =
    Sum.inr (RVCalc.rv v (fieldValue (p.realize (M := Model E v a) (Sum.inl ∘ fieldValues E v a s z))))
  rw [(DenefPasFieldTerms.realize E v a p hp (fieldValues E v a s z)).1]
  rfl

end SpecialTransformations.Section6.DenefPasReturnParameters
end
end

/-! Source: Section6.DenefPasReturnFormula -/
section

/-! Return the entire RV fragment to a DP formula over its original free
parameters. Every output binder is guarded in RF or Gamma. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language

namespace SpecialTransformations.Section6.DenefPasReturnFormula
open AngularComponent DenefPasCodes DenefPasLanguage DenefPasNativeModel DenefPasForwardPatterns
open DenefPasParameters DenefPasReturnParameters FiniteSortContext RVAbstraction RVGraphLanguage

def formula {E : _root_.FirstOrder.Language.{0, 0}} {I : Type} (s : I → SortKind)
    (χ : (Native E).Formula (VFPart (nativeSort s) ⊕ RVPart (nativeSort s))) :
    (language E).Formula I :=
  (DenefPasAuxLift.lift (PairSyntax.formula (DenefPasDictionary.dictionary E)
    (RVAbstraction.formula χ))).subst (replacement s)

theorem isFieldQF {E : _root_.FirstOrder.Language.{0, 0}} {I : Type} (s : I → SortKind)
    (χ : (Native E).Formula (VFPart (nativeSort s) ⊕ RVPart (nativeSort s))) :
    IsFieldQF (formula s χ) :=
  DenefPasSubstitution.isFieldQF_subst _ (DenefPasAuxLift.isFieldQF _)

variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]
variable (E : _root_.FirstOrder.Language.{0, 0}) (v : Valuation K Γ) (a : Data v)
variable [E.Structure (Aux v)]
local instance : (Native E).Structure (Model E v a) := structureOn E v a
local instance : (language E).Structure (DenefPasAuxLift.Model E v a) := dpStructure E v a
local instance : DenefPasAux.auxLanguage.Structure (Aux v) := DenefPasAux.auxStructure
local instance : (DenefPasMorley.Auxiliary E).Structure (Aux v) :=
  FirstOrder.Language.sumStructure DenefPasAux.auxLanguage E (Aux v)
local instance : RVBase.Structure (DenefPasDictionary.Model v a) := DenefPasRV.rvStructure v a
local instance : (DenefPasMorley.signature E).Structure (DenefPasDictionary.Model v a) :=
  DenefPasMorley.rvStructure E v a
local instance : (Auxiliary (DenefPasMorley.signature E)).Structure (DenefPasDictionary.Model v a) :=
  FirstOrder.Language.sumStructure RVBase (DenefPasMorley.signature E) (DenefPasDictionary.Model v a)

theorem realize {I : Type} (s : I → SortKind)
    (χ : (Native E).Formula (VFPart (nativeSort s) ⊕ RVPart (nativeSort s))) (hχ : Fragment χ)
    (z : I → DenefPasAuxLift.Model E v a) (hz : Sorted E v a s z) :
    (formula s χ).Realize z ↔ χ.Realize (packed E v a z ∘ (partition (nativeSort s)).symm) := by
  let u : Leaves E s × Coord → Aux v :=
    fun j => auxValue ((replacement s j).realize (M := DenefPasAuxLift.Model E v a) z)
  let uV : VFPart (nativeSort s) → Model E v a := fun j => packed E v a z j.val
  let uR : RVPart (nativeSort s) → DenefPasDictionary.Model v a := fun j => rvValue (packed E v a z j.val)
  have hsubst := DenefPasSubstitution.subst_realize E v a
    (PairSyntax.formula (DenefPasDictionary.dictionary E) (RVAbstraction.formula χ))
    (replacement s) z (replacement_isAux E v a s z hz)
  have hcode : PairInterpretation.decode (DenefPasDictionary.code v a) u =
      Sum.elim (DenefPasReturnParameters.coefficient E v a s z) uR := by
    funext j
    cases j with
    | inl p => rfl
    | inr r => exact rvParameter_decode E v a s z hz r
  have hdict := DenefPasDictionary.formula_realize E v a (RVAbstraction.formula χ) u
  rw [hcode] at hdict
  have habs := RVAbstraction.formula_realize (DenefPasRVReduct.inclusion E v a)
    (DenefPasRVReduct.inclusion_injective E v a) (DenefPasRVReduct.functions E v a)
    (DenefPasRVReduct.relations E v a) (DenefPasRVReduct.guard E v a) uV uR
    (DenefPasReturnParameters.coefficient E v a s z)
    (coefficient_realize E v a s z hz) χ hχ (default : Fin 0 → DenefPasDictionary.Model v a)
  have h0 : DenefPasRVReduct.inclusion E v a ∘ (default : Fin 0 → DenefPasDictionary.Model v a) =
      (default : Fin 0 → Model E v a) := Subsingleton.elim _ _
  have habs' : Formula.Realize (RVAbstraction.formula χ)
      (Sum.elim (DenefPasReturnParameters.coefficient E v a s z) uR) ↔
        χ.Realize (Sum.elim uV (DenefPasRVReduct.inclusion E v a ∘ uR)) := by
    simpa only [Formula.Realize, h0] using habs
  have hfree : Sum.elim uV (DenefPasRVReduct.inclusion E v a ∘ uR) =
      packed E v a z ∘ (partition (nativeSort s)).symm := by
    funext j
    cases j with
    | inl j => rfl
    | inr j => exact (packed_rv E v a s z hz j).symm
  rw [hfree] at habs'
  exact hsubst.trans (hdict.trans habs')

end SpecialTransformations.Section6.DenefPasReturnFormula
end
end

/-! Source: Section6.ExpandedRawLogic -/
section

/-! Convert raw formulas to the guarded sorted syntax, once their atoms
have been sorted. This is a generic logical adapter. Its atomic premise
must be proved from the canonical interpretation; it is not a henselian
elimination premise. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 50000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Section6.ExpandedRawLogic
open RVTermSupport ExpandedLogic


def Equivalent {E : _root_.FirstOrder.Language.{0, 0}} (T : (Expanded E).Theory) {I : Type}
    (s : I → SortTag) {n : ℕ} (sn : Fin n → SortTag)
    (φ ψ : (Expanded E).BoundedFormula I n) : Prop :=
  ∀ (M : Type) [(Expanded E).Structure M], M ⊨ T →
    ∀ (v : I → M) (x : Fin n → M),
      (∀ i, tagEval (E := E) (s i) (v i)) →
      (∀ i, tagEval (E := E) (sn i) (x i)) → (φ.Realize v x ↔ ψ.Realize v x)


def SortCover {E : _root_.FirstOrder.Language.{0, 0}} (T : (Expanded E).Theory) : Prop :=
  ∀ (M : Type) [(Expanded E).Structure M], M ⊨ T →
    ∀ a : M, tagEval (E := E) .vf a ∨ tagEval (E := E) .rv a


def AtomicSorting {E : _root_.FirstOrder.Language.{0, 0}} (T : (Expanded E).Theory) : Prop :=
  ∀ (I : Type) (s : I → SortTag) (n : ℕ) (sn : Fin n → SortTag)
    (φ : (Expanded E).BoundedFormula I n), φ.IsAtomic →
    ∃ ψ : (Expanded E).BoundedFormula I n, ψ.IsQF ∧ ExpandedLogic.WellSorted s sn ψ ∧ Equivalent T s sn φ ψ


theorem wellSorted_inf {E : _root_.FirstOrder.Language.{0, 0}} {I : Type} {s : I → SortTag}
    {n : ℕ} {sn : Fin n → SortTag} {φ ψ : (Expanded E).BoundedFormula I n}
    (hφ : ExpandedLogic.WellSorted s sn φ) (hψ : ExpandedLogic.WellSorted s sn ψ) : ExpandedLogic.WellSorted s sn (φ ⊓ ψ) :=
  ExpandedLogic.WellSorted.not
    (ExpandedLogic.WellSorted.imp hφ (ExpandedLogic.WellSorted.not hψ))


theorem normalize {E : _root_.FirstOrder.Language.{0, 0}} (T : (Expanded E).Theory)
    (hcover : SortCover T) (hatom : AtomicSorting T)
    {I : Type} (s : I → SortTag) {n : ℕ} (φ : (Expanded E).BoundedFormula I n)
    (sn : Fin n → SortTag) :
    ∃ ψ : (Expanded E).BoundedFormula I n, ExpandedLogic.WellSorted s sn ψ ∧ Equivalent T s sn φ ψ := by
  induction φ with
  | falsum => exact ⟨⊥, .falsum sn, fun _ _ _ _ _ _ _ => Iff.rfl⟩
  | equal t u =>
    obtain ⟨ψ, _, hsψ, heψ⟩ := hatom I s _ sn (.equal t u) (.equal t u)
    exact ⟨ψ, hsψ, heψ⟩
  | rel r ts =>
    obtain ⟨ψ, _, hsψ, heψ⟩ := hatom I s _ sn (.rel r ts) (.rel r ts)
    exact ⟨ψ, hsψ, heψ⟩
  | imp φ θ ihφ ihθ =>
    obtain ⟨ψ, hsψ, heψ⟩ := ihφ sn
    obtain ⟨χ, hsχ, heχ⟩ := ihθ sn
    refine ⟨ψ.imp χ, .imp hsψ hsχ, ?_⟩
    intro M _ hM v x hv hx
    exact imp_congr (heψ M hM v x hv hx) (heχ M hM v x hv hx)
  | @all n φ ih =>
    obtain ⟨ψ, hsψ, heψ⟩ := ih (Fin.snoc sn .vf)
    obtain ⟨χ, hsχ, heχ⟩ := ih (Fin.snoc sn .rv)
    refine ⟨allSorted .vf ψ ⊓ allSorted .rv χ,
      wellSorted_inf (.all hsψ) (.all hsχ), ?_⟩
    intro M _ hM v x hv hx
    rw [BoundedFormula.realize_all, BoundedFormula.realize_inf,
      allSorted_realize, allSorted_realize]
    constructor
    · intro hall
      exact ⟨fun a ha => (heψ M hM v (Fin.snoc x a) hv (ExpandedLogic.sorted_snoc hx ha)).mp (hall a),
        fun a ha => (heχ M hM v (Fin.snoc x a) hv (ExpandedLogic.sorted_snoc hx ha)).mp (hall a)⟩
    · rintro ⟨hVF, hRV⟩ a
      rcases hcover M hM a with ha | ha
      · exact (heψ M hM v (Fin.snoc x a) hv (ExpandedLogic.sorted_snoc hx ha)).mpr (hVF a ha)
      · exact (heχ M hM v (Fin.snoc x a) hv (ExpandedLogic.sorted_snoc hx ha)).mpr (hRV a ha)


theorem eliminate {E : _root_.FirstOrder.Language.{0, 0}} (T : (Expanded E).Theory)
    (hcover : SortCover T) (hatom : AtomicSorting T) (hQE : ExpandedLogic.HasVFQE T)
    {I : Type} (s : I → SortTag) {n : ℕ} (φ : (Expanded E).BoundedFormula I n)
    (sn : Fin n → SortTag) :
    ∃ ψ : (Expanded E).BoundedFormula I n, ExpandedLogic.IsVFQF ψ ∧ ExpandedLogic.WellSorted s sn ψ ∧ Equivalent T s sn φ ψ := by
  obtain ⟨χ, hsχ, heχ⟩ := normalize T hcover hatom s φ sn
  obtain ⟨ψ, hψ, hsψ, heψ⟩ := hQE I s n sn χ hsχ
  refine ⟨ψ, hψ, hsψ, ?_⟩
  intro M _ hM v x hv hx
  exact (heχ M hM v x hv hx).trans (heψ M hM v x hv hx)

end SpecialTransformations.Section6.ExpandedRawLogic





end
end

/-! Source: Section6.HenselianNativeSyntax -/
section

/-! Reuse the released canonical native syntax in henselian submodels.
The native embedding transfers only terms and QF formulas. No elementarity
of the henselian field in its algebraic closure is asserted or needed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Section6.HenselianNativeSyntax
open RVTermSupport

theorem tagEval_native (E : Language) (M : Type) [(Expanded E).Structure M]
    [LRV.Structure M] [(LHom.sumInl : LRV →ᴸ Expanded E).IsExpansionOn M]
    (s : SortTag) (a : M) : ExpandedLogic.tagEval (E := E) s a ↔ sortEval s a := by
  cases s with
  | vf => exact Iff.of_eq ((LHom.sumInl : LRV →ᴸ Expanded E).map_onRelation Rel.memVF ![a])
  | rv => exact Iff.of_eq ((LHom.sumInl : LRV →ᴸ Expanded E).map_onRelation Rel.memRV ![a])

theorem sortCover (E : Language) (hEnv : UniformNormalizedElimination.NativeEnvelopes E) :
    ExpandedRawLogic.SortCover (HenselianTheory.expanded E) := by
  intro M sM hM a
  letI := (LHom.sumInl : LRV →ᴸ Expanded E).reduct M
  cases hEnv M hM with
  | @in_model U sU hU h00 hc f hH =>
    rcases TypedModelMap.sort_cover (f a) with ha | ha
    · exact Or.inl ((NativeImageTransport.sorts_preserved (E := E) f .vf a).mp ha)
    · exact Or.inr ((NativeImageTransport.sorts_preserved (E := E) f .rv a).mp ha)

theorem on_isQF {E : Language} {I : Type} {n : ℕ}
    (φ : LRV.BoundedFormula I n) (hφ : φ.IsQF) :
    ((LHom.sumInl : LRV →ᴸ Expanded E).onBoundedFormula φ).IsQF := by
  induction hφ with
  | falsum => exact .falsum
  | of_isAtomic h =>
    cases h with
    | equal t u => exact .of_isAtomic (.equal _ _)
    | rel r ts => exact .of_isAtomic (.rel _ _)
  | imp hφ hψ ihφ ihψ => exact .imp ihφ ihψ

theorem native_qf (E : Language) (hEnv : UniformNormalizedElimination.NativeEnvelopes E)
    {I : Type} (s : I → SortTag) {n : ℕ} (sn : Fin n → SortTag)
    (φ : LRV.BoundedFormula I n) (hφ : φ.IsQF) :
    ∃ ψ : (Expanded E).BoundedFormula I n, ψ.IsQF ∧ ExpandedLogic.WellSorted s sn ψ ∧
      ExpandedRawLogic.Equivalent (HenselianTheory.expanded E) s sn
        ((LHom.sumInl : LRV →ᴸ Expanded E).onBoundedFormula φ) ψ := by
  let θ := CanonicalStructure.sortedQF s sn φ
  have hθ := CanonicalStructure.sortedQF_isQF s sn φ
  have hsθ := CanonicalStructure.sortedQF_wellSorted s sn φ
  refine ⟨(LHom.sumInl : LRV →ᴸ Expanded E).onBoundedFormula θ,
    on_isQF θ hθ, NativeExpandedSyntax.qf_wellSorted s sn θ hθ hsθ, ?_⟩
  intro M sM hM v x hv hx
  letI := (LHom.sumInl : LRV →ᴸ Expanded E).reduct M
  cases hEnv M hM with
  | @in_model U sU hU h00 hc f hH =>
    have hvU := fun i => (NativeImageTransport.sorts_preserved (E := E) f (s i) (v i)).mpr (hv i)
    have hxU := fun i => (NativeImageTransport.sorts_preserved (E := E) f (sn i) (x i)).mpr (hx i)
    have he := CanonicalStructure.sortedQF_realize hU hc s sn (f ∘ v) (f ∘ x) hvU hxU φ hφ
    have hnative := (hφ.realize_embedding f (v := v) (xs := x)).symm.trans
      (he.symm.trans (hθ.realize_embedding f (v := v) (xs := x)))
    simpa only [LHom.realize_onBoundedFormula] using hnative

theorem native_term (E : Language) (hEnv : UniformNormalizedElimination.NativeEnvelopes E)
    {I : Type} (s : I → SortTag) (t : LRV.Term I)
    (M : Type) [sM : (Expanded E).Structure M] (hM : M ⊨ HenselianTheory.expanded E)
    (v : I → M) (hv : ∀ i, ExpandedLogic.tagEval (E := E) (s i) (v i)) :
    letI := (LHom.sumInl : LRV →ᴸ Expanded E).reduct M
    (TypedNativeTerms.term s t).realize v = t.realize v ∧
      sortEval (TypedNativeTerms.tag s t) (t.realize v) := by
  letI := (LHom.sumInl : LRV →ᴸ Expanded E).reduct M
  cases hEnv M hM with
  | @in_model U sU hU h00 hc f hH =>
    have hvU := fun i => (NativeImageTransport.sorts_preserved (E := E) f (s i) (v i)).mpr (hv i)
    have he := TypedNativeTerms.term_realize hc s (f ∘ v) hvU t
    have hs := TypedNativeTerms.realized_sort s (f ∘ v) hvU t
    have hm : (TypedNativeTerms.term s t).realize v = t.realize v := by
      apply f.injective
      rw [← HomClass.realize_term f, ← HomClass.realize_term f]
      exact he
    refine ⟨hm, ?_⟩
    have hs' : sortEval (TypedNativeTerms.tag s t) (f (t.realize v)) := by
      rw [← HomClass.realize_term f, ← he]
      exact hs
    have hr := (NativeImageTransport.sorts_preserved (E := E) f (TypedNativeTerms.tag s t) (t.realize v)).mp hs'
    exact (tagEval_native E M _ _).mp hr

theorem bounded_native_term (E : Language) (hEnv : UniformNormalizedElimination.NativeEnvelopes E)
    {I : Type} (s : I → SortTag) {n : ℕ} (sn : Fin n → SortTag)
    (t : LRV.Term (I ⊕ Fin n))
    (M : Type) [sM : (Expanded E).Structure M] (hM : M ⊨ HenselianTheory.expanded E)
    (v : I → M) (x : Fin n → M)
    (hv : ∀ i, ExpandedLogic.tagEval (E := E) (s i) (v i))
    (hx : ∀ i, ExpandedLogic.tagEval (E := E) (sn i) (x i)) :
    letI := (LHom.sumInl : LRV →ᴸ Expanded E).reduct M
    (CanonicalStructure.sortedTerm s sn t).realize (Sum.elim v x) = t.realize (Sum.elim v x) ∧
      sortEval (CanonicalStructure.resultSort s sn t) (t.realize (Sum.elim v x)) := by
  letI := (LHom.sumInl : LRV →ᴸ Expanded E).reduct M
  cases hEnv M hM with
  | @in_model U sU hU h00 hc f hH =>
    have hvU := fun i => (NativeImageTransport.sorts_preserved (E := E) f (s i) (v i)).mpr (hv i)
    have hxU := fun i => (NativeImageTransport.sorts_preserved (E := E) f (sn i) (x i)).mpr (hx i)
    have he := CanonicalStructure.sortedTerm_realize hU hc s sn (f ∘ v) (f ∘ x) hvU hxU t
    have hz : f ∘ Sum.elim v x = Sum.elim (f ∘ v) (f ∘ x) := by
      funext i
      cases i <;> rfl
    have hm : (CanonicalStructure.sortedTerm s sn t).realize (Sum.elim v x) =
        t.realize (Sum.elim v x) := by
      apply f.injective
      rw [← HomClass.realize_term f, ← HomClass.realize_term f, hz]
      exact he
    refine ⟨hm, ?_⟩
    have hs := CanonicalStructure.term_sort hU s sn (f ∘ v) (f ∘ x) hvU hxU
      (CanonicalStructure.sortedTerm s sn t) (CanonicalStructure.sortedTerm_sort s sn t)
    rw [he, ← hz, HomClass.realize_term f] at hs
    exact (tagEval_native E M _ _).mp
      ((NativeImageTransport.sorts_preserved (E := E) f (CanonicalStructure.resultSort s sn t)
        (t.realize (Sum.elim v x))).mp hs)

end SpecialTransformations.Section6.HenselianNativeSyntax

end
end

/-! Source: Section6.RelationalTerms -/
section

/-! A relational RV expansion adds no new terms. Strip and reinsert only
the language-sum injections, keeping the published native language intact. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.Milestone0.LRV FirstOrder.Language.sum
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Section6.RelationalTerms
open RVTermSupport
variable {E : Language} [E.IsRelational] {I : Type}

def strip : (Expanded E).Term I → LRV.Term I
  | .var i => .var i
  | .func (.inl f) ts => .func f (fun i => strip (ts i))
  | .func (.inr f) _ => isEmptyElim f

theorem lift_strip (t : (Expanded E).Term I) :
    (LHom.sumInl : LRV →ᴸ Expanded E).onTerm (strip t) = t := by
  induction t with
  | var i => rfl
  | func f ts ih =>
    cases f with
    | inl f =>
      change Term.func (L := Expanded E) (.inl f) _ = Term.func (L := Expanded E) (.inl f) _
      congr 1
      exact funext ih
    | inr f => exact isEmptyElim f

theorem equality {n : ℕ} (t u : (Expanded E).Term (I ⊕ Fin n)) :
    (LHom.sumInl : LRV →ᴸ Expanded E).onBoundedFormula
      (BoundedFormula.equal (strip t) (strip u)) = BoundedFormula.equal t u := by
  change BoundedFormula.equal _ _ = _
  rw [lift_strip, lift_strip]

theorem relation {n k : ℕ} (r : Rel k) (ts : Fin k → (Expanded E).Term (I ⊕ Fin n)) :
    (LHom.sumInl : LRV →ᴸ Expanded E).onBoundedFormula
      (BoundedFormula.rel r (fun i => strip (ts i))) = BoundedFormula.rel (L := Expanded E) (.inl r) ts := by
  change BoundedFormula.rel (L := Expanded E) (.inl r) _ = _
  congr 1
  funext i
  exact lift_strip (ts i)

theorem strip_realize {M : Type} [(Expanded E).Structure M] [LRV.Structure M]
    [(LHom.sumInl : LRV →ᴸ Expanded E).IsExpansionOn M]
    (t : (Expanded E).Term I) (v : I → M) : (strip t).realize v = t.realize v := by
  calc
    (strip t).realize v = ((LHom.sumInl : LRV →ᴸ Expanded E).onTerm (strip t)).realize v :=
      (LHom.realize_onTerm (LHom.sumInl : LRV →ᴸ Expanded E) (strip t) v).symm
    _ = t.realize v := congrArg (fun u : (Expanded E).Term I => u.realize v) (lift_strip t)

end SpecialTransformations.Section6.RelationalTerms
end
end

/-! Source: Section6.HenselianRelationalSorting -/
section

/-! Atomic sorting for a relational RV expansion. Native atoms use the
released canonical QF normalizer; new relation atoms use the actual sort
axioms, and all their terms are native by RelationalTerms. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Section6.HenselianRelationalSorting
open RVTermSupport
variable {E : Language} [E.IsRelational] {I : Type} {n : ℕ}

def tag (s : I → SortTag) (sn : Fin n → SortTag) (t : (Expanded E).Term (I ⊕ Fin n)) : SortTag :=
  CanonicalStructure.resultSort s sn (RelationalTerms.strip t)

def term (s : I → SortTag) (sn : Fin n → SortTag) (t : (Expanded E).Term (I ⊕ Fin n)) :
    (Expanded E).Term (I ⊕ Fin n) :=
  (LHom.sumInl : LRV →ᴸ Expanded E).onTerm
    (CanonicalStructure.sortedTerm s sn (RelationalTerms.strip t))

theorem term_sorted (s : I → SortTag) (sn : Fin n → SortTag)
    (t : (Expanded E).Term (I ⊕ Fin n)) : termSort (Sum.elim s sn) (term s sn t) = some (tag s sn t) := by
  rw [term, NativeExpandedSyntax.term_sort]
  exact CanonicalStructure.sortedTerm_sort s sn _

theorem term_realize (hEnv : UniformNormalizedElimination.NativeEnvelopes E)
    (s : I → SortTag) (sn : Fin n → SortTag) (t : (Expanded E).Term (I ⊕ Fin n))
    (M : Type) [(Expanded E).Structure M] (hM : M ⊨ HenselianTheory.expanded E)
    (v : I → M) (x : Fin n → M)
    (hv : ∀ i, ExpandedLogic.tagEval (E := E) (s i) (v i))
    (hx : ∀ i, ExpandedLogic.tagEval (E := E) (sn i) (x i)) :
    (term s sn t).realize (Sum.elim v x) = t.realize (Sum.elim v x) ∧
      ExpandedLogic.tagEval (E := E) (tag s sn t) (t.realize (Sum.elim v x)) := by
  letI := (LHom.sumInl : LRV →ᴸ Expanded E).reduct M
  have h := HenselianNativeSyntax.bounded_native_term E hEnv s sn
    (RelationalTerms.strip t) M hM v x hv hx
  constructor
  · simpa only [term, LHom.realize_onTerm, RelationalTerms.strip_realize] using h.1
  · apply (HenselianNativeSyntax.tagEval_native E M _ _).mpr
    simpa only [RelationalTerms.strip_realize, tag] using h.2

theorem sort_unique (hEnv : UniformNormalizedElimination.NativeEnvelopes E)
    (M : Type) [(Expanded E).Structure M] (hM : M ⊨ HenselianTheory.expanded E)
    {s t : SortTag} {a : M} (hs : ExpandedLogic.tagEval (E := E) s a)
    (ht : ExpandedLogic.tagEval (E := E) t a) : s = t := by
  letI := (LHom.sumInl : LRV →ᴸ Expanded E).reduct M
  cases hEnv M hM with
  | @in_model U sU hU h00 hc f hH =>
    exact CanonicalStructure.sort_unique hU
      ((NativeImageTransport.sorts_preserved (E := E) f s a).mpr hs)
      ((NativeImageTransport.sorts_preserved (E := E) f t a).mpr ht)

def relation (s : I → SortTag) (sn : Fin n → SortTag) {k : ℕ} (r : E.Relations k)
    (ts : Fin k → (Expanded E).Term (I ⊕ Fin n)) : (Expanded E).BoundedFormula I n :=
  if ∀ i, tag s sn (ts i) = .rv then .rel (.inr r) (fun i => term s sn (ts i)) else ⊥

theorem relation_isQF (s : I → SortTag) (sn : Fin n → SortTag) {k : ℕ} (r : E.Relations k)
    (ts : Fin k → (Expanded E).Term (I ⊕ Fin n)) : (relation s sn r ts).IsQF := by
  unfold relation
  split
  · exact .of_isAtomic (.rel _ _)
  · exact .falsum

theorem relation_wellSorted (s : I → SortTag) (sn : Fin n → SortTag) {k : ℕ} (r : E.Relations k)
    (ts : Fin k → (Expanded E).Term (I ⊕ Fin n)) : ExpandedLogic.WellSorted s sn (relation s sn r ts) := by
  unfold relation
  split
  · rename_i ht
    exact .rel _ _ (fun i => by rw [term_sorted, ht i]; rfl)
  · exact .falsum sn

theorem relation_equivalent (hEnv : UniformNormalizedElimination.NativeEnvelopes E)
    (s : I → SortTag) (sn : Fin n → SortTag) {k : ℕ} (r : E.Relations k)
    (ts : Fin k → (Expanded E).Term (I ⊕ Fin n)) :
    ExpandedRawLogic.Equivalent (HenselianTheory.expanded E) s sn
      (.rel (.inr r) ts) (relation s sn r ts) := by
  intro M _ hM v x hv hx
  unfold relation
  split
  · change Structure.RelMap (L := Expanded E) (.inr r) _ ↔ Structure.RelMap (L := Expanded E) (.inr r) _
    have he : (fun i => (term s sn (ts i)).realize (Sum.elim v x)) =
        (fun i => (ts i).realize (Sum.elim v x)) := by
      funext i
      exact (term_realize hEnv s sn (ts i) M hM v x hv hx).1
    rw [he]
  · rename_i hbad
    change Structure.RelMap (L := Expanded E) (.inr r) _ ↔ False
    refine ⟨fun hr => ?_, False.elim⟩
    apply hbad
    have hs := (ExtraSortSemantics.laws_of_henselian_model hM).relations r _ hr
    intro i
    exact sort_unique hEnv M hM (term_realize hEnv s sn (ts i) M hM v x hv hx).2 (hs i)

theorem atomicSorting (hEnv : UniformNormalizedElimination.NativeEnvelopes E) :
    ExpandedRawLogic.AtomicSorting (HenselianTheory.expanded E) := by
  intro I s n sn φ hφ
  cases hφ with
  | equal t u =>
    obtain ⟨ψ, hψ, hsψ, heψ⟩ := HenselianNativeSyntax.native_qf E hEnv s sn
      (.equal (RelationalTerms.strip t) (RelationalTerms.strip u)) (.of_isAtomic (.equal _ _))
    rw [RelationalTerms.equality] at heψ
    exact ⟨ψ, hψ, hsψ, heψ⟩
  | rel r ts =>
    cases r with
    | inl r =>
      obtain ⟨ψ, hψ, hsψ, heψ⟩ := HenselianNativeSyntax.native_qf E hEnv s sn
        (.rel r (fun i => RelationalTerms.strip (ts i))) (.of_isAtomic (.rel _ _))
      rw [RelationalTerms.relation] at heψ
      exact ⟨ψ, hψ, hsψ, heψ⟩
    | inr r => exact ⟨relation s sn r ts, relation_isQF s sn r ts,
        relation_wellSorted s sn r ts, relation_equivalent hEnv s sn r ts⟩

/-- Raw syntax can be used for an interpretation into a relational RV
expansion. Atomic sorting and the sort cover are discharged above. -/
theorem eliminate
    (hEarlier : EnvelopeUniformity.EarlierPreparation)
    (hEnv : UniformNormalizedElimination.NativeEnvelopes E)
    (hNormal : HenselianElimination.RVLiteralNormalForm E)
    (s : I → SortTag) (sn : Fin n → SortTag) (φ : (Expanded E).BoundedFormula I n) :
    ∃ ψ : (Expanded E).BoundedFormula I n, ExpandedLogic.IsVFQF ψ ∧
      ExpandedLogic.WellSorted s sn ψ ∧
      ExpandedRawLogic.Equivalent (HenselianTheory.expanded E) s sn φ ψ :=
  ExpandedRawLogic.eliminate (HenselianTheory.expanded E)
    (HenselianNativeSyntax.sortCover E hEnv) (atomicSorting hEnv)
    (HenselianElimination.hasVFQE E hEarlier hEnv hNormal) s φ sn

end SpecialTransformations.Section6.HenselianRelationalSorting

end
end

/-! Source: Section6.DenefPasNativeElimination -/
section

/-! Uniform DP elimination on the actual native models. Ordinary
henselian-field recognition and the trivial valuation branch are separate
from this theorem; neither is hidden in the elimination hypotheses. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Section6.DenefPasNativeElimination
open AngularComponent DenefPasCodes DenefPasLanguage DenefPasNativeModel DenefPasForwardPatterns
open DenefPasParameters FiniteSortContext

theorem eliminate_native_models (E : _root_.FirstOrder.Language.{0, 0})
    (hEarlier : EnvelopeUniformity.EarlierPreparation)
    (hEnv : UniformNormalizedElimination.NativeEnvelopes (DenefPasMorley.signature E))
    (hNormal : HenselianElimination.RVLiteralNormalForm (DenefPasMorley.signature E))
    {I : Type} [Finite I] (s : I → SortKind) (φ : (language E).Formula I) :
    ∃ ψ : (language E).Formula I, IsFieldQF ψ ∧
      ∀ (K Γ : Type) [Field K] [LinearOrderedCommGroupWithZero Γ]
        (v : Valuation K Γ) (a : Data v) [E.Structure (Aux v)],
        letI : (Native E).Structure (Model E v a) := structureOn E v a
        letI : (language E).Structure (DenefPasAuxLift.Model E v a) := dpStructure E v a
        Model E v a ⊨ HenselianTheory.expanded (DenefPasMorley.signature E) →
        ∀ z : I → DenefPasAuxLift.Model E v a, Sorted E v a s z →
          (φ.Realize z ↔ ψ.Realize z) := by
  let ns := nativeSort s
  let V := VFPart ns
  let R := RVPart ns
  let e := partition ns
  let θ := PairSyntax.formula (DenefPasForwardDictionary.dictionary E) φ
  obtain ⟨η, hη, hsη, heη⟩ := HenselianRelationalSorting.eliminate hEarlier hEnv hNormal
    ns (fun _ : Fin 0 => .rv) θ
  let θ' : (Native E).Formula (V ⊕ R) := (BoundedFormula.relabelEquiv e) η
  have he : ∀ j, Sum.elim (fun _ : V => SortTag.vf) (fun _ : R => .rv) (e j) = ns j := by
    intro j
    obtain ⟨j', rfl⟩ := e.symm.surjective j
    rw [Equiv.apply_symm_apply]
    cases j' with
    | inl j => exact j.property.symm
    | inr j => exact j.property.symm
  letI : Fintype V := Fintype.ofFinite V
  letI : Fintype R := Fintype.ofFinite R
  obtain ⟨χ, hχ, heχ⟩ := hNormal V R θ'
    (ExpandedRenaming.wellSorted e ns _ he (fun _ : Fin 0 => .rv) η hsη)
    (ExpandedRenaming.isVFQF e η hη)
  refine ⟨DenefPasReturnFormula.formula s χ, DenefPasReturnFormula.isFieldQF s χ, ?_⟩
  intro K Γ _ _ v a _
  letI : (Native E).Structure (Model E v a) := structureOn E v a
  letI : (language E).Structure (DenefPasAuxLift.Model E v a) := dpStructure E v a
  intro hM z hz
  letI := hM
  letI : Nonempty (Model E v a) := ⟨Sum.inl 0⟩
  let model := Theory.ModelType.of (HenselianTheory.expanded (DenefPasMorley.signature E)) (Model E v a)
  let zN := packed E v a z
  have hpack : PairInterpretation.decode (DenefPasForwardDictionary.code E v a) zN = z := by
    funext i
    exact DenefPasNativeCodes.code_pack v a (z i)
  have hfwd := DenefPasForwardDictionary.formula_realize E v a φ zN
  rw [hpack] at hfwd
  have hnative : θ.Realize zN ↔ Formula.Realize η zN :=
    heη (Model E v a) hM zN default (packed_sorts E v a s z hz) (fun j => j.elim0)
  have hcomp : (zN ∘ e.symm) ∘ e = zN := by
    rw [Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id]
  have hrename : θ'.Realize (zN ∘ e.symm) ↔ Formula.Realize η zN := by
    change Formula.Realize ((BoundedFormula.relabelEquiv e) η) (zN ∘ e.symm) ↔ Formula.Realize η zN
    rw [Formula.Realize, BoundedFormula.realize_relabelEquiv, hcomp]
    rfl
  let uV : V → Model E v a := fun j => zN j.val
  let uR : R → Model E v a := fun j => zN j.val
  have hv : ∀ j, ExpandedLogic.tagEval (E := DenefPasMorley.signature E) .vf (uV j) := by
    intro j
    have h := packed_sorts E v a s z hz j.val
    change ExpandedLogic.tagEval (E := DenefPasMorley.signature E) (ns j.val) (zN j.val) at h
    rw [j.property] at h
    exact h
  have hr : ∀ j, ExpandedLogic.tagEval (E := DenefPasMorley.signature E) .rv (uR j) := by
    intro j
    have h := packed_sorts E v a s z hz j.val
    change ExpandedLogic.tagEval (E := DenefPasMorley.signature E) (ns j.val) (zN j.val) at h
    rw [j.property] at h
    exact h
  have hsplit : Sum.elim uV uR = zN ∘ e.symm := by
    funext j
    cases j <;> rfl
  have hnormal : θ'.Realize (zN ∘ e.symm) ↔ χ.Realize (zN ∘ e.symm) := by
    simpa only [hsplit] using heχ model uV uR hv hr
  have hreturn := DenefPasReturnFormula.realize E v a s χ hχ z hz
  exact hfwd.symm.trans (hnative.trans (hrename.symm.trans (hnormal.trans hreturn.symm)))

end SpecialTransformations.Section6.DenefPasNativeElimination
end
end

/-! Source: Section6.DenefPasHenselianModels -/
section

/-! The ordinary valued-field representation boundary. The author's
standing authorization permits standard Engler--Prestel inputs as explicit
hypotheses. Recognition below asserts only the native henselian axioms for
an actual field, valuation and residue field; it asserts no elimination or
definability theorem. The relational expansion is constructed here. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Section6.DenefPasHenselianModels
open AngularComponent DenefPasCodes DenefPasLanguage DenefPasNativeModel DenefPasForwardPatterns
open DenefPasParameters

@[instance_reducible] def nativeStructure {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) (a : Data v) : LRV.Structure (DenefPasNativeCodes.NativeCarrier v) where
  funMap := nativeFunction v a
  RelMap := nativeRelation v a

/-- Explicit standard representation input. The first-order axioms are the
ordinary pure-characteristic-zero henselian axioms with the stated tagged
presentation. No Section6 conclusion occurs in this input. -/
def OrdinaryRecognition : Prop :=
  ∀ (K Γ : Type) [Field K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) (a : Data v) [CharZero K] [CharZero (Residue v)]
    [HenselianLocalRing v.valuationSubring], ¬ Trivial v →
    letI : LRV.Structure (DenefPasNativeCodes.NativeCarrier v) := nativeStructure v a
    DenefPasNativeCodes.NativeCarrier v ⊨ HenselianTheory.canonicalHen00

section Expansion
variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]
variable (E : _root_.FirstOrder.Language.{0, 0}) (v : Valuation K Γ) (a : Data v)
variable [E.Structure (Aux v)]
local instance : LRV.Structure (Model E v a) := nativeStructure v a
local instance : (Native E).Structure (Model E v a) := structureOn E v a
local instance : (LHom.sumInl : LRV →ᴸ Native E).IsExpansionOn (Model E v a) := by
  constructor <;> intro n f z <;> rfl

theorem extra_model : Model E v a ⊨ HenselianTheory.extraSortAxioms (DenefPasMorley.signature E) := by
  constructor
  intro σ hσ
  rcases hσ with (⟨n, f, rfl⟩ | ⟨n, f, rfl⟩) | ⟨n, θ, rfl⟩
  · exact isEmptyElim f
  · exact isEmptyElim f
  · apply (ExtraSortSemantics.relationSort_realize θ).mpr
    intro z hz
    change (∀ i, IsRV (z i)) ∧ _ at hz
    exact hz.1

theorem expanded_model (h : Model E v a ⊨ HenselianTheory.canonicalHen00) :
    Model E v a ⊨ HenselianTheory.expanded (DenefPasMorley.signature E) := by
  have hi : Model E v a ⊨ (LHom.sumInl : LRV →ᴸ Native E).onTheory HenselianTheory.canonicalHen00 :=
    (LHom.onTheory_model _ _).mpr h
  have he := extra_model E v a
  constructor
  intro σ hσ
  rcases hσ with hσ | hσ
  · exact hi.realize_of_mem σ hσ
  · exact he.realize_of_mem σ hσ

end Expansion

theorem eliminate_nontrivial (hRecognition : OrdinaryRecognition)
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
        ¬ Trivial v → ∀ z : I → DenefPasAuxLift.Model E v a, Sorted E v a s z →
          (φ.Realize z ↔ ψ.Realize z) := by
  obtain ⟨ψ, hψ, he⟩ := DenefPasNativeElimination.eliminate_native_models E hEarlier hEnv hNormal s φ
  refine ⟨ψ, hψ, ?_⟩
  intro K Γ _ _ v a _ _ _ _ hnt z hz
  letI : LRV.Structure (Model E v a) := nativeStructure v a
  letI : (Native E).Structure (Model E v a) := structureOn E v a
  have hn : Model E v a ⊨ HenselianTheory.canonicalHen00 := hRecognition K Γ v a hnt
  exact he K Γ v a (expanded_model E v a hn) z hz

end SpecialTransformations.Section6.DenefPasHenselianModels
end
end

/-! Source: Section6.Library -/
section

/-! Section 6's new shared-language library. Legacy snapshots are excluded.
The remaining syntax/expansion obligations are listed in STATUS.md. -/

set_option pp.explicit true
set_option pp.fullNames true

#check @SpecialTransformations.Section6.singleton_tuple_coordinates
#print axioms SpecialTransformations.Section6.singleton_tuple_coordinates
#check @SpecialTransformations.Section6.singleton_of_unique_relation
#print axioms SpecialTransformations.Section6.singleton_of_unique_relation
#check @SpecialTransformations.Section6.functionallyClosed_of_dclClosed
#print axioms SpecialTransformations.Section6.functionallyClosed_of_dclClosed
#check @SpecialTransformations.Section6.dclClosed_of_functionallyClosed
#print axioms SpecialTransformations.Section6.dclClosed_of_functionallyClosed
#check @SpecialTransformations.Section6.functionallyClosed_iff_dclClosed
#print axioms SpecialTransformations.Section6.functionallyClosed_iff_dclClosed
#check @SpecialTransformations.Section6.definable_singleton_fixed
#print axioms SpecialTransformations.Section6.definable_singleton_fixed
#check @SpecialTransformations.Section6.DclClosed.image
#print axioms SpecialTransformations.Section6.DclClosed.image
#check @SpecialTransformations.Section6.FunctionallyClosed.image
#print axioms SpecialTransformations.Section6.FunctionallyClosed.image
#check @SpecialTransformations.Section6.valuedAutomorphism
#print axioms SpecialTransformations.Section6.valuedAutomorphism
#check @SpecialTransformations.Section6.valuedAutomorphism_vf
#print axioms SpecialTransformations.Section6.valuedAutomorphism_vf
#check @SpecialTransformations.Section6.valuedAutomorphism_rv
#print axioms SpecialTransformations.Section6.valuedAutomorphism_rv
#check @SpecialTransformations.Section6.valuedAutomorphism_fixes_base
#print axioms SpecialTransformations.Section6.valuedAutomorphism_fixes_base
#check @SpecialTransformations.Section6.henselian_vf_dcl
#print axioms SpecialTransformations.Section6.henselian_vf_dcl
#check @SpecialTransformations.Section6.lemma_6_2_in_algebraic_envelope
#print axioms SpecialTransformations.Section6.lemma_6_2_in_algebraic_envelope
#check @SpecialTransformations.Section6.lemma_6_2
#print axioms SpecialTransformations.Section6.lemma_6_2
#check @SpecialTransformations.Section6.FunctionallyClosed.over
#print axioms SpecialTransformations.Section6.FunctionallyClosed.over
#check @SpecialTransformations.Section6.map_preserves_represented
#print axioms SpecialTransformations.Section6.map_preserves_represented
#check @SpecialTransformations.Section6.pointIn_iff_represented
#print axioms SpecialTransformations.Section6.pointIn_iff_represented
#check @SpecialTransformations.Section6.keyIn_iff_represented
#print axioms SpecialTransformations.Section6.keyIn_iff_represented
#check @SpecialTransformations.Section6.map_preserves_pointIn
#print axioms SpecialTransformations.Section6.map_preserves_pointIn
#check @SpecialTransformations.Section6.map_preserves_keyIn
#print axioms SpecialTransformations.Section6.map_preserves_keyIn
#check @SpecialTransformations.Section6.restrictSpecialBijection
#print axioms SpecialTransformations.Section6.restrictSpecialBijection
#check @SpecialTransformations.Section6.keyIn_of_pointIn
#print axioms SpecialTransformations.Section6.keyIn_of_pointIn
#check @SpecialTransformations.Section6.pullback_key_realized
#print axioms SpecialTransformations.Section6.pullback_key_realized
#check @SpecialTransformations.Section6.prepared_exists_descends
#print axioms SpecialTransformations.Section6.prepared_exists_descends
#check @SpecialTransformations.Section6.exists_preparation_with_descent
#print axioms SpecialTransformations.Section6.exists_preparation_with_descent
#check @SpecialTransformations.Section6.sortPredG_var_realize
#print axioms SpecialTransformations.Section6.sortPredG_var_realize
#check @SpecialTransformations.Section6.inAntecedent_false
#print axioms SpecialTransformations.Section6.inAntecedent_false
#check @SpecialTransformations.Section6.guardTrue_true
#print axioms SpecialTransformations.Section6.guardTrue_true
#check @SpecialTransformations.Section6.IsVFQF.ex_rv
#print axioms SpecialTransformations.Section6.IsVFQF.ex_rv
#check @SpecialTransformations.Section6.hasVFQE_of_step
#print axioms SpecialTransformations.Section6.hasVFQE_of_step

#print SpecialTransformations.Section6.FunctionallyClosed
#print SpecialTransformations.Section6.DclClosed
#print SpecialTransformations.Section6.FunctionallyClosedOver
#print SpecialTransformations.Section6.HenselianAutomorphismInvariance
#print SpecialTransformations.Section6.DefinableRVLifting
#print SpecialTransformations.Section6.PointIn
#print SpecialTransformations.Section6.KeyIn
#print SpecialTransformations.Section6.VFQE_step
#print SpecialTransformations.Section6.HasVFQE
#print SpecialTransformations.Section6.IsVFQF

#check @SpecialTransformations.Section6.RVFormula.abstractLeft_realize
#print axioms SpecialTransformations.Section6.RVFormula.abstractLeft_realize
#check @SpecialTransformations.Section6.RVFormula.existsLeft_realize
#print axioms SpecialTransformations.Section6.RVFormula.existsLeft_realize
#check @SpecialTransformations.Section6.RVFormula.assemble_realize
#print axioms SpecialTransformations.Section6.RVFormula.assemble_realize
#check @SpecialTransformations.Section6.RVTermSupport.termSort_func
#print axioms SpecialTransformations.Section6.RVTermSupport.termSort_func
#check @SpecialTransformations.Section6.RVTermSupport.leaves_quotient
#print axioms SpecialTransformations.Section6.RVTermSupport.leaves_quotient
#check @SpecialTransformations.Section6.RVTermSupport.leaves_inverse
#print axioms SpecialTransformations.Section6.RVTermSupport.leaves_inverse
#check @SpecialTransformations.Section6.RVTermSupport.realize_eq_of_leaves
#print axioms SpecialTransformations.Section6.RVTermSupport.realize_eq_of_leaves
#check @SpecialTransformations.Section6.keyTuple_mem
#print axioms SpecialTransformations.Section6.keyTuple_mem
#check @SpecialTransformations.Section6.keyIn_of_tuple
#print axioms SpecialTransformations.Section6.keyIn_of_tuple
#check @SpecialTransformations.Section6.prepared_formula_elimination
#print axioms SpecialTransformations.Section6.prepared_formula_elimination
#check @SpecialTransformations.Section6.AngularComponent.residue_eq_one_iff
#print axioms SpecialTransformations.Section6.AngularComponent.residue_eq_one_iff
#check @SpecialTransformations.Section6.AngularComponent.value_one_of_principal
#print axioms SpecialTransformations.Section6.AngularComponent.value_one_of_principal
#check @SpecialTransformations.Section6.AngularComponent.coordinates_kernel
#print axioms SpecialTransformations.Section6.AngularComponent.coordinates_kernel
#check @SpecialTransformations.Section6.AngularComponent.residue_lift_value_one
#print axioms SpecialTransformations.Section6.AngularComponent.residue_lift_value_one
#check @SpecialTransformations.Section6.AngularComponent.coordinates_surjective
#print axioms SpecialTransformations.Section6.AngularComponent.coordinates_surjective
#check @SpecialTransformations.Section6.AngularComponent.splitting
#print axioms SpecialTransformations.Section6.AngularComponent.splitting
#check @SpecialTransformations.Section6.AngularComponent.splitting_mk
#print axioms SpecialTransformations.Section6.AngularComponent.splitting_mk
#check @SpecialTransformations.Section6.AngularComponent.splittingWithZero
#print axioms SpecialTransformations.Section6.AngularComponent.splittingWithZero
#check @SpecialTransformations.Section6.AngularComponent.splittingWithZero_zero
#print axioms SpecialTransformations.Section6.AngularComponent.splittingWithZero_zero
#check @SpecialTransformations.Section6.AngularComponent.splittingWithZero_rv
#print axioms SpecialTransformations.Section6.AngularComponent.splittingWithZero_rv
#check @SpecialTransformations.Section6.RVAbstraction.polynomial_sort
#print axioms SpecialTransformations.Section6.RVAbstraction.polynomial_sort
#check @SpecialTransformations.Section6.RVAbstraction.polynomial_realize
#print axioms SpecialTransformations.Section6.RVAbstraction.polynomial_realize
#check @SpecialTransformations.Section6.RVAbstraction.term_realize
#print axioms SpecialTransformations.Section6.RVAbstraction.term_realize
#check @SpecialTransformations.Section6.RVAbstraction.formula_realize
#print axioms SpecialTransformations.Section6.RVAbstraction.formula_realize
#check @SpecialTransformations.Section6.contractionGraphCodes_definable
#print axioms SpecialTransformations.Section6.contractionGraphCodes_definable
#check @SpecialTransformations.Section6.contractionGraphCodes_sorted
#print axioms SpecialTransformations.Section6.contractionGraphCodes_sorted
#check @SpecialTransformations.Section6.exists_qf_contraction_graph
#print axioms SpecialTransformations.Section6.exists_qf_contraction_graph
#check @SpecialTransformations.Section6.finite_sentence_cover
#print axioms SpecialTransformations.Section6.finite_sentence_cover
#check @SpecialTransformations.Section6.finite_formula_cover
#print axioms SpecialTransformations.Section6.finite_formula_cover
#check @SpecialTransformations.Section6.uniform_of_local_certificates
#print axioms SpecialTransformations.Section6.uniform_of_local_certificates

#print SpecialTransformations.Section6.ContractionGraphFormula
#print SpecialTransformations.Section6.RVAbstraction.Auxiliary
#print SpecialTransformations.Section6.RVAbstraction.Fragment
#print SpecialTransformations.Section6.RVAbstraction.Compatible
#print SpecialTransformations.Section6.RVAbstraction.RelationsCompatible
#print SpecialTransformations.Section6.RVAbstraction.GuardCompatible
#print SpecialTransformations.Section6.AngularComponent.Data

#check @SpecialTransformations.Section6.RVSubstructure.functions_compatible
#print axioms SpecialTransformations.Section6.RVSubstructure.functions_compatible
#check @SpecialTransformations.Section6.RVSubstructure.relations_compatible
#print axioms SpecialTransformations.Section6.RVSubstructure.relations_compatible
#check @SpecialTransformations.Section6.RVSubstructure.guard_compatible
#print axioms SpecialTransformations.Section6.RVSubstructure.guard_compatible
#check @SpecialTransformations.Section6.RVSubstructure.coefficient_spec
#print axioms SpecialTransformations.Section6.RVSubstructure.coefficient_spec
#check @SpecialTransformations.Section6.RVSubstructure.formula_realize_substructure
#print axioms SpecialTransformations.Section6.RVSubstructure.formula_realize_substructure
#check @SpecialTransformations.Section6.ExpandedLogic.hasVFQE_of_oneStep
#print axioms SpecialTransformations.Section6.ExpandedLogic.hasVFQE_of_oneStep
#check @SpecialTransformations.Section6.GuardedLift.formula_isVFQF
#print axioms SpecialTransformations.Section6.GuardedLift.formula_isVFQF
#check @SpecialTransformations.Section6.GuardedLift.formula_wellSorted
#print axioms SpecialTransformations.Section6.GuardedLift.formula_wellSorted
#check @SpecialTransformations.Section6.GuardedLift.formula_realize
#print axioms SpecialTransformations.Section6.GuardedLift.formula_realize
#check @SpecialTransformations.Section6.polynomial_descent_certificate
#print axioms SpecialTransformations.Section6.polynomial_descent_certificate
#check @SpecialTransformations.Section6.polynomial_formula_descent
#print axioms SpecialTransformations.Section6.polynomial_formula_descent
#check @SpecialTransformations.Section6.polynomial_source_formula_descent
#print axioms SpecialTransformations.Section6.polynomial_source_formula_descent
#check @SpecialTransformations.Section6.map_formula_descent
#print axioms SpecialTransformations.Section6.map_formula_descent
#check @SpecialTransformations.Section6.native_formula_elimination_points
#print axioms SpecialTransformations.Section6.native_formula_elimination_points
#check @SpecialTransformations.Section6.native_formula_elimination
#print axioms SpecialTransformations.Section6.native_formula_elimination
#check @SpecialTransformations.Section6.syntactic_lemma_6_3
#print axioms SpecialTransformations.Section6.syntactic_lemma_6_3
#check @SpecialTransformations.Section6.equivalent_of_elementary_cover
#print axioms SpecialTransformations.Section6.equivalent_of_elementary_cover
#check @SpecialTransformations.Section6.FragmentCompactness.realize_type
#print axioms SpecialTransformations.Section6.FragmentCompactness.realize_type
#check @SpecialTransformations.Section6.FragmentCompactness.countermodels
#print axioms SpecialTransformations.Section6.FragmentCompactness.countermodels
#check @SpecialTransformations.Section6.FragmentCompactness.definable_of_type_invariant
#print axioms SpecialTransformations.Section6.FragmentCompactness.definable_of_type_invariant
#check @SpecialTransformations.Section6.RVGraphLanguage.qf_definition_on_substructures
#print axioms SpecialTransformations.Section6.RVGraphLanguage.qf_definition_on_substructures
#check @SpecialTransformations.Section6.RVGraphLanguage.qf_contraction_definition
#print axioms SpecialTransformations.Section6.RVGraphLanguage.qf_contraction_definition
#check @SpecialTransformations.Section6.RVGraphLanguage.contractionGraphCodes_append
#print axioms SpecialTransformations.Section6.RVGraphLanguage.contractionGraphCodes_append
#check @SpecialTransformations.Section6.RVGraphLanguage.prepared_graph_formula
#print axioms SpecialTransformations.Section6.RVGraphLanguage.prepared_graph_formula
#check @SpecialTransformations.Section6.RVGraphExpansion.graph_expansion
#print axioms SpecialTransformations.Section6.RVGraphExpansion.graph_expansion
#check @SpecialTransformations.Section6.RVGraphExpansion.prepared_graph_formula
#print axioms SpecialTransformations.Section6.RVGraphExpansion.prepared_graph_formula
#check @SpecialTransformations.Section6.RVSourceFormula.lift_isVFQF
#print axioms SpecialTransformations.Section6.RVSourceFormula.lift_isVFQF
#check @SpecialTransformations.Section6.RVSourceFormula.lift_wellSorted
#print axioms SpecialTransformations.Section6.RVSourceFormula.lift_wellSorted
#check @SpecialTransformations.Section6.RVSourceFormula.lift_realize_substructure
#print axioms SpecialTransformations.Section6.RVSourceFormula.lift_realize_substructure
#check @SpecialTransformations.Section6.FiniteAbstraction.body_realize_substructure
#print axioms SpecialTransformations.Section6.FiniteAbstraction.body_realize_substructure
#check @SpecialTransformations.Section6.NativeTerms.exists_native_vf
#print axioms SpecialTransformations.Section6.NativeTerms.exists_native_vf
#check @SpecialTransformations.Section6.NativeTerms.realize_native
#print axioms SpecialTransformations.Section6.NativeTerms.realize_native
#check @SpecialTransformations.Section6.HenselianInputs.dclClosed
#print axioms SpecialTransformations.Section6.HenselianInputs.dclClosed
#check @SpecialTransformations.Section6.HenselianInputs.rv_surjective
#print axioms SpecialTransformations.Section6.HenselianInputs.rv_surjective
#check @SpecialTransformations.Section6.SortedFragment.fragment_boolean
#print axioms SpecialTransformations.Section6.SortedFragment.fragment_boolean
#check @SpecialTransformations.Section6.SortedFragment.definable_of_sorted_type_invariant
#print axioms SpecialTransformations.Section6.SortedFragment.definable_of_sorted_type_invariant
#check @SpecialTransformations.Section6.NativeTermMap.code_definable
#print axioms SpecialTransformations.Section6.NativeTermMap.code_definable
#check @SpecialTransformations.Section6.NativeTermMap.tupleMap_values
#print axioms SpecialTransformations.Section6.NativeTermMap.tupleMap_values
#check @SpecialTransformations.Section6.NamedLanguage.names_expansion
#print axioms SpecialTransformations.Section6.NamedLanguage.names_expansion
#check @SpecialTransformations.Section6.NamedLanguage.fromAuxiliary_rvQuantified
#print axioms SpecialTransformations.Section6.NamedLanguage.fromAuxiliary_rvQuantified
#check @SpecialTransformations.Section6.NamedLanguage.RVQuantified.guarded
#print axioms SpecialTransformations.Section6.NamedLanguage.RVQuantified.guarded
#check @SpecialTransformations.Section6.NamedLanguage.fromAuxiliary_realize
#print axioms SpecialTransformations.Section6.NamedLanguage.fromAuxiliary_realize
#check @SpecialTransformations.Section6.ParameterNaming.nameFinite_realize
#print axioms SpecialTransformations.Section6.ParameterNaming.nameFinite_realize
#check @SpecialTransformations.Section6.NativeOccurrence.native_shape
#print axioms SpecialTransformations.Section6.NativeOccurrence.native_shape
#check @SpecialTransformations.Section6.NativeOccurrence.native_sorted
#print axioms SpecialTransformations.Section6.NativeOccurrence.native_sorted
#check @SpecialTransformations.Section6.NativeOccurrence.coefficient_native
#print axioms SpecialTransformations.Section6.NativeOccurrence.coefficient_native
#check @SpecialTransformations.Section6.FiniteNamedSyntax.nameInput_realize
#print axioms SpecialTransformations.Section6.FiniteNamedSyntax.nameInput_realize
#check @SpecialTransformations.Section6.FVBinding.guards_realize
#print axioms SpecialTransformations.Section6.FVBinding.guards_realize
#check @SpecialTransformations.Section6.FVBinding.existsVF_realize_points
#print axioms SpecialTransformations.Section6.FVBinding.existsVF_realize_points
#check @SpecialTransformations.Section6.FiniteParameterSyntax.fragment_restrict
#print axioms SpecialTransformations.Section6.FiniteParameterSyntax.fragment_restrict
#check @SpecialTransformations.Section6.FiniteParameterSyntax.formula_fragment
#print axioms SpecialTransformations.Section6.FiniteParameterSyntax.formula_fragment
#check @SpecialTransformations.Section6.FiniteParameterSyntax.formula_realize
#print axioms SpecialTransformations.Section6.FiniteParameterSyntax.formula_realize
#check @SpecialTransformations.Section6.OriginalParameterSyntax.nameInput_realize
#print axioms SpecialTransformations.Section6.OriginalParameterSyntax.nameInput_realize
#check @SpecialTransformations.Section6.AuxiliaryDenaming.unname_realize
#print axioms SpecialTransformations.Section6.AuxiliaryDenaming.unname_realize
#check @SpecialTransformations.Section6.AuxiliaryDenaming.formula_isVFQF
#print axioms SpecialTransformations.Section6.AuxiliaryDenaming.formula_isVFQF
#check @SpecialTransformations.Section6.AuxiliaryDenaming.formula_wellSorted
#print axioms SpecialTransformations.Section6.AuxiliaryDenaming.formula_wellSorted
#check @SpecialTransformations.Section6.AuxiliaryDenaming.formula_realize
#print axioms SpecialTransformations.Section6.AuxiliaryDenaming.formula_realize
#check @SpecialTransformations.Section6.AngularComponent.encode_surjective
#print axioms SpecialTransformations.Section6.AngularComponent.encode_surjective
#check @SpecialTransformations.Section6.AngularComponent.residueCoordinate_encode
#print axioms SpecialTransformations.Section6.AngularComponent.residueCoordinate_encode
#check @SpecialTransformations.Section6.AngularComponent.encode_eq_encode
#print axioms SpecialTransformations.Section6.AngularComponent.encode_eq_encode
#check @SpecialTransformations.Section6.AngularComponent.encode_mul
#print axioms SpecialTransformations.Section6.AngularComponent.encode_mul
#check @SpecialTransformations.Section6.AngularComponent.exists_encode
#print axioms SpecialTransformations.Section6.AngularComponent.exists_encode
#check @SpecialTransformations.Section6.AngularComponent.forall_encode
#print axioms SpecialTransformations.Section6.AngularComponent.forall_encode
#check @SpecialTransformations.Section6.PairInterpretation.term_graph_definable
#print axioms SpecialTransformations.Section6.PairInterpretation.term_graph_definable
#check @SpecialTransformations.Section6.PairInterpretation.relation_of_terms
#print axioms SpecialTransformations.Section6.PairInterpretation.relation_of_terms
#check @SpecialTransformations.Section6.PairInterpretation.formula_set_definable
#print axioms SpecialTransformations.Section6.PairInterpretation.formula_set_definable
#check @SpecialTransformations.Section6.PairInterpretation.exists_formula
#print axioms SpecialTransformations.Section6.PairInterpretation.exists_formula
#check @SpecialTransformations.Section6.TypedNativeTerms.term_sorted
#print axioms SpecialTransformations.Section6.TypedNativeTerms.term_sorted
#check @SpecialTransformations.Section6.TypedNativeTerms.term_realize
#print axioms SpecialTransformations.Section6.TypedNativeTerms.term_realize
#check @SpecialTransformations.Section6.GeneratedParameters.rv_parameter_term
#print axioms SpecialTransformations.Section6.GeneratedParameters.rv_parameter_term
#check @SpecialTransformations.Section6.GeneratedParameters.expanded_rv_parameter_term
#print axioms SpecialTransformations.Section6.GeneratedParameters.expanded_rv_parameter_term
#check @SpecialTransformations.Section6.GeneratedDenaming.dename_rv_formula
#print axioms SpecialTransformations.Section6.GeneratedDenaming.dename_rv_formula
#print SpecialTransformations.Section6.HenselianInputs
#print SpecialTransformations.Section6.HenselianInputs.of_envelope
#print SpecialTransformations.Section6.RVGraphLanguage.RVQFDefinitions
#print SpecialTransformations.Section6.NamedLanguage.RVQuantified
#print SpecialTransformations.Section6.ExpandedLogic.OneStep
#print SpecialTransformations.Section6.ExpandedLogic.HasVFQE
#print SpecialTransformations.Section6.ElementaryCover
#print SpecialTransformations.Section6.FragmentCompactness.BooleanClosed
#print SpecialTransformations.Section6.FragmentCompactness.Equivalent
#print SpecialTransformations.Section6.PairInterpretation.Data
#print SpecialTransformations.Section6.HenselianTheory.hen00
#print SpecialTransformations.Section6.HenselianTheory.canonicalHen00
#print SpecialTransformations.Section6.HenselianTheory.expanded
#print SpecialTransformations.Section6.HenselianTheory.named
#check @SpecialTransformations.Section6.CommonEnvelopeComparison.existential_type_invariant
#print axioms SpecialTransformations.Section6.CommonEnvelopeComparison.existential_type_invariant
#check @SpecialTransformations.Section6.NativeAmalgamation.common_envelope
#print axioms SpecialTransformations.Section6.NativeAmalgamation.common_envelope
#check @SpecialTransformations.Section6.CanonicalEmbedding.normalize_eq
#print axioms SpecialTransformations.Section6.CanonicalEmbedding.normalize_eq
#check @SpecialTransformations.Section6.CanonicalEmbedding.normalized_apply
#print axioms SpecialTransformations.Section6.CanonicalEmbedding.normalized_apply
#check @SpecialTransformations.Section6.HenselianInputs.map
#print axioms SpecialTransformations.Section6.HenselianInputs.map
#check @SpecialTransformations.Section6.NativeExpandedSyntax.qf_isVFQF
#print axioms SpecialTransformations.Section6.NativeExpandedSyntax.qf_isVFQF
#check @SpecialTransformations.Section6.NativeExpandedSyntax.qf_wellSorted
#print axioms SpecialTransformations.Section6.NativeExpandedSyntax.qf_wellSorted
#check @SpecialTransformations.Section6.NativeExpandedSyntax.envelope_qf_type
#print axioms SpecialTransformations.Section6.NativeExpandedSyntax.envelope_qf_type
#check @SpecialTransformations.Section6.RVExpansionTransport.rv_preserved
#print axioms SpecialTransformations.Section6.RVExpansionTransport.rv_preserved
#check @SpecialTransformations.Section6.RVExpansionTransport.auxiliaryEquiv
#print axioms SpecialTransformations.Section6.RVExpansionTransport.auxiliaryEquiv
#check @SpecialTransformations.Section6.RVExpansionTransport.expandedEquiv
#print axioms SpecialTransformations.Section6.RVExpansionTransport.expandedEquiv
#check @SpecialTransformations.Section6.AngularComponent.encode_one
#print axioms SpecialTransformations.Section6.AngularComponent.encode_one
#check @SpecialTransformations.Section6.AngularComponent.encode_inverse
#print axioms SpecialTransformations.Section6.AngularComponent.encode_inverse
#print SpecialTransformations.Section6.NativeAmalgamation.SaturatedElementaryExtensionAt
#check @SpecialTransformations.Section6.ExtraSortSemantics.laws_of_henselian_model
#print axioms SpecialTransformations.Section6.ExtraSortSemantics.laws_of_henselian_model
#check @SpecialTransformations.Section6.ExpandedImages.rvImage_bijective
#print axioms SpecialTransformations.Section6.ExpandedImages.rvImage_bijective
#check @SpecialTransformations.Section6.ExpandedImages.expandedEquiv
#print axioms SpecialTransformations.Section6.ExpandedImages.expandedEquiv
#check @SpecialTransformations.Section6.NormalizedQuery.realize
#print axioms SpecialTransformations.Section6.NormalizedQuery.realize
#check @SpecialTransformations.Section6.NormalizedQuery.named_realize
#print axioms SpecialTransformations.Section6.NormalizedQuery.named_realize
#check @SpecialTransformations.Section6.ExpandedRenaming.isVFQF
#print axioms SpecialTransformations.Section6.ExpandedRenaming.isVFQF
#check @SpecialTransformations.Section6.ExpandedRenaming.wellSorted
#print axioms SpecialTransformations.Section6.ExpandedRenaming.wellSorted
#check @SpecialTransformations.Section6.SentenceDenaming.dename
#print axioms SpecialTransformations.Section6.SentenceDenaming.dename
#check @SpecialTransformations.Section6.AlignedComparison.existential_type_invariant
#print axioms SpecialTransformations.Section6.AlignedComparison.existential_type_invariant
#print SpecialTransformations.Section6.ExtraSortSemantics.Laws
#check @SpecialTransformations.Section6.PairSyntax.term_realize
#print axioms SpecialTransformations.Section6.PairSyntax.term_realize
#check @SpecialTransformations.Section6.PairSyntax.applyRelation_realize
#print axioms SpecialTransformations.Section6.PairSyntax.applyRelation_realize
#check @SpecialTransformations.Section6.PairSyntax.bounded_realize
#print axioms SpecialTransformations.Section6.PairSyntax.bounded_realize
#check @SpecialTransformations.Section6.PairSyntax.formula_realize
#print axioms SpecialTransformations.Section6.PairSyntax.formula_realize
#check @SpecialTransformations.Section6.NativeImageComparison.existential_type_invariant
#print axioms SpecialTransformations.Section6.NativeImageComparison.existential_type_invariant
#check @SpecialTransformations.Section6.NativeImageTransport.sorts_preserved
#print axioms SpecialTransformations.Section6.NativeImageTransport.sorts_preserved
#check @SpecialTransformations.Section6.NativeImageTransport.range_comp
#print axioms SpecialTransformations.Section6.NativeImageTransport.range_comp
#check @SpecialTransformations.Section6.NativeImageTransport.henselian_range_comp
#print axioms SpecialTransformations.Section6.NativeImageTransport.henselian_range_comp
#check @SpecialTransformations.Section6.EnvelopeUniformity.existential_type_invariant
#print axioms SpecialTransformations.Section6.EnvelopeUniformity.existential_type_invariant
#check @SpecialTransformations.Section6.UniformNormalizedElimination.eliminate
#print axioms SpecialTransformations.Section6.UniformNormalizedElimination.eliminate
#print SpecialTransformations.Section6.PairSyntax.Syntax
#print SpecialTransformations.Section6.PairSyntax.Realizes
#print SpecialTransformations.Section6.EnvelopeUniformity.PreparationInputs
#print SpecialTransformations.Section6.EnvelopeUniformity.EarlierPreparation
#print SpecialTransformations.Section6.UniformNormalizedElimination.NativeEnvelope
#print SpecialTransformations.Section6.UniformNormalizedElimination.NativeEnvelopes
#check @SpecialTransformations.Section6.FiniteSortContext.reindex_sort
#print axioms SpecialTransformations.Section6.FiniteSortContext.reindex_sort
#check @SpecialTransformations.Section6.ExpandedLiterals.rvEquality_fragment
#print axioms SpecialTransformations.Section6.ExpandedLiterals.rvEquality_fragment
#check @SpecialTransformations.Section6.ExpandedLiterals.vf_realize_sorted
#print axioms SpecialTransformations.Section6.ExpandedLiterals.vf_realize_sorted
#check @SpecialTransformations.Section6.ExpandedLiterals.rvEquality_realize
#print axioms SpecialTransformations.Section6.ExpandedLiterals.rvEquality_realize
#check @SpecialTransformations.Section6.ExpandedRestriction.isVFQF
#print axioms SpecialTransformations.Section6.ExpandedRestriction.isVFQF
#check @SpecialTransformations.Section6.ExpandedRestriction.wellSorted
#print axioms SpecialTransformations.Section6.ExpandedRestriction.wellSorted
#check @SpecialTransformations.Section6.ExpandedFreeRenaming.isVFQF
#print axioms SpecialTransformations.Section6.ExpandedFreeRenaming.isVFQF
#check @SpecialTransformations.Section6.ExpandedFreeRenaming.wellSorted
#print axioms SpecialTransformations.Section6.ExpandedFreeRenaming.wellSorted
#check @SpecialTransformations.Section6.ExpandedFreeRenaming.realize
#print axioms SpecialTransformations.Section6.ExpandedFreeRenaming.realize
#check @SpecialTransformations.Section6.FiniteContextLogic.oneStep_of_finite
#print axioms SpecialTransformations.Section6.FiniteContextLogic.oneStep_of_finite
#check @SpecialTransformations.Section6.FiniteContextLogic.hasVFQE_of_finite
#print axioms SpecialTransformations.Section6.FiniteContextLogic.hasVFQE_of_finite
#check @SpecialTransformations.Section6.AngularComponent.value_splitting
#print axioms SpecialTransformations.Section6.AngularComponent.value_splitting
#check @SpecialTransformations.Section6.AngularComponent.value_encode
#print axioms SpecialTransformations.Section6.AngularComponent.value_encode
#check @SpecialTransformations.Section6.AngularComponent.encode_nonzero
#print axioms SpecialTransformations.Section6.AngularComponent.encode_nonzero
#check @SpecialTransformations.Section6.AngularComponent.group_value_one
#print axioms SpecialTransformations.Section6.AngularComponent.group_value_one
#check @SpecialTransformations.Section6.AngularComponent.residue_unit_encode
#print axioms SpecialTransformations.Section6.AngularComponent.residue_unit_encode
#check @SpecialTransformations.Section6.AngularComponent.residue_domain_encode
#print axioms SpecialTransformations.Section6.AngularComponent.residue_domain_encode
#check @SpecialTransformations.Section6.AngularComponent.value_order_encode
#print axioms SpecialTransformations.Section6.AngularComponent.value_order_encode
#check @SpecialTransformations.Section6.RVQuotients.rv_inverse
#print axioms SpecialTransformations.Section6.RVQuotients.rv_inverse
#check @SpecialTransformations.Section6.RVQuotients.rv_division
#print axioms SpecialTransformations.Section6.RVQuotients.rv_division
#check @SpecialTransformations.Section6.RVFragmentRenaming.fragment
#print axioms SpecialTransformations.Section6.RVFragmentRenaming.fragment
#check @SpecialTransformations.Section6.FiniteNormalizedElimination.eliminate
#print axioms SpecialTransformations.Section6.FiniteNormalizedElimination.eliminate
#print SpecialTransformations.Section6.FiniteContextLogic.FiniteOneStep
#check @SpecialTransformations.Section6.ExpandedParameterRelabel.term_sort
#print axioms SpecialTransformations.Section6.ExpandedParameterRelabel.term_sort
#check @SpecialTransformations.Section6.ExpandedParameterRelabel.guard
#print axioms SpecialTransformations.Section6.ExpandedParameterRelabel.guard
#check @SpecialTransformations.Section6.ExpandedParameterRelabel.allSorted
#print axioms SpecialTransformations.Section6.ExpandedParameterRelabel.allSorted
#check @SpecialTransformations.Section6.ExpandedParameterRelabel.isVFQF
#print axioms SpecialTransformations.Section6.ExpandedParameterRelabel.isVFQF
#check @SpecialTransformations.Section6.ExpandedParameterRelabel.wellSorted
#print axioms SpecialTransformations.Section6.ExpandedParameterRelabel.wellSorted
#check @SpecialTransformations.Section6.ExpandedOpenBounds.splitLast_free
#print axioms SpecialTransformations.Section6.ExpandedOpenBounds.splitLast_free
#check @SpecialTransformations.Section6.ExpandedOpenBounds.splitLast_cast
#print axioms SpecialTransformations.Section6.ExpandedOpenBounds.splitLast_cast
#check @SpecialTransformations.Section6.ExpandedOpenBounds.splitLast_last
#print axioms SpecialTransformations.Section6.ExpandedOpenBounds.splitLast_last
#check @SpecialTransformations.Section6.ExpandedOpenBounds.guard
#print axioms SpecialTransformations.Section6.ExpandedOpenBounds.guard
#check @SpecialTransformations.Section6.ExpandedOpenBounds.isVFQF
#print axioms SpecialTransformations.Section6.ExpandedOpenBounds.isVFQF
#check @SpecialTransformations.Section6.ExpandedOpenBounds.term_sort
#print axioms SpecialTransformations.Section6.ExpandedOpenBounds.term_sort
#check @SpecialTransformations.Section6.ExpandedOpenBounds.sortAssem_empty
#print axioms SpecialTransformations.Section6.ExpandedOpenBounds.sortAssem_empty
#check @SpecialTransformations.Section6.ExpandedOpenBounds.wellSorted
#print axioms SpecialTransformations.Section6.ExpandedOpenBounds.wellSorted
#check @SpecialTransformations.Section6.OneStepPresentation.inverse_vf
#print axioms SpecialTransformations.Section6.OneStepPresentation.inverse_vf
#check @SpecialTransformations.Section6.OneStepPresentation.inverse_rv
#print axioms SpecialTransformations.Section6.OneStepPresentation.inverse_rv
#check @SpecialTransformations.Section6.OneStepPresentation.inverse_new
#print axioms SpecialTransformations.Section6.OneStepPresentation.inverse_new
#check @SpecialTransformations.Section6.OneStepPresentation.old_sort
#print axioms SpecialTransformations.Section6.OneStepPresentation.old_sort
#check @SpecialTransformations.Section6.OneStepPresentation.inverse_sort
#print axioms SpecialTransformations.Section6.OneStepPresentation.inverse_sort
#check @SpecialTransformations.Section6.OneStepPresentation.body_isVFQF
#print axioms SpecialTransformations.Section6.OneStepPresentation.body_isVFQF
#check @SpecialTransformations.Section6.OneStepPresentation.body_wellSorted
#print axioms SpecialTransformations.Section6.OneStepPresentation.body_wellSorted
#check @SpecialTransformations.Section6.OneStepPresentation.old_value
#print axioms SpecialTransformations.Section6.OneStepPresentation.old_value
#check @SpecialTransformations.Section6.OneStepPresentation.body_realize
#print axioms SpecialTransformations.Section6.OneStepPresentation.body_realize
#check @SpecialTransformations.Section6.HenselianElimination.finite_oneStep
#print axioms SpecialTransformations.Section6.HenselianElimination.finite_oneStep
#check @SpecialTransformations.Section6.HenselianElimination.hasVFQE
#print axioms SpecialTransformations.Section6.HenselianElimination.hasVFQE
#print SpecialTransformations.Section6.HenselianElimination.RVLiteralNormalForm
end

