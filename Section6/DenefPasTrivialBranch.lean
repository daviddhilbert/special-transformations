import Section6.DenefPasInterpretation

/-! Coherent Section 6 module. The source bodies below are retained
from the individually developed fragments; only imports and file scope
are consolidated. The exported names and mathematical statements remain. -/

/-! Source: Section6.DenefPasTrivialCodes -/
section

/-! Actual auxiliary pair codes for the native carrier under trivial
valuation. VF uses the proved ac ring equivalence. RV keeps its existing
two-coordinate code, selected by a Gamma-valued second coordinate. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical

namespace SpecialTransformations.Section6.DenefPasTrivialCodes
open AngularComponent DenefPasCodes DenefPasLanguage DenefPasNativeCodes DenefPasNativeModel
variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]

private theorem rv_onto (v : Valuation K Γ) : Function.Surjective (RVCalc.rv v) := by
  intro q
  cases q with
  | none => exact ⟨0, RVCalc.rv_zero⟩
  | some q =>
    obtain ⟨x, _, hx⟩ := RVCalc.rv_surjective v q
    exact ⟨x, hx⟩

def rvResidueEquiv (v : Valuation K Γ) (a : Data v) (h : Trivial v) : RVCalc.RV v ≃ Residue v where
  toFun := residueValue v a
  invFun := fun r => RVCalc.rv v ((trivialAcEquiv v a h).symm r)
  left_inv := fun q => by
    obtain ⟨x, rfl⟩ := rv_onto v q
    change RVCalc.rv v ((trivialAcEquiv v a h).symm (residueValue v a (RVCalc.rv v x))) = RVCalc.rv v x
    rw [residueValue_rv, ← trivialAcEquiv_apply v a h x, RingEquiv.symm_apply_apply]
  right_inv := fun r => by
    rw [residueValue_rv, ← trivialAcEquiv_apply v a h, RingEquiv.apply_symm_apply]

theorem rv_encode (v : Valuation K Γ) (a : Data v) (h : Trivial v) (x : K) :
    RVCalc.rv v x = encode v a (a.ac x) 1 := by
  apply (rvResidueEquiv v a h).injective
  change residueValue v a (RVCalc.rv v x) = residueValue v a (encode v a (a.ac x) 1)
  rw [residueValue_rv, residueValue_encode]

def code (v : Valuation K Γ) (a : Data v) (h : Trivial v) (p : Coord → Aux v) : NativeCarrier v :=
  match p 1 with
  | .inl r => .inl ((trivialAcEquiv v a h).symm r)
  | .inr _ => .inr (decode v a p)

def pack (v : Valuation K Γ) (a : Data v) : NativeCarrier v → Coord → Aux v
  | .inl x => ![.inl 0, .inl (a.ac x)]
  | .inr q => DenefPasNormalization.coordinates v a q

theorem code_pack (v : Valuation K Γ) (a : Data v) (h : Trivial v) (q : NativeCarrier v) :
    code v a h (pack v a q) = q := by
  cases q with
  | inl x =>
    change Sum.inl ((trivialAcEquiv v a h).symm (a.ac x)) = Sum.inl x
    rw [← trivialAcEquiv_apply v a h x, RingEquiv.symm_apply_apply]
  | inr q =>
    change Sum.inr (decode v a (DenefPasNormalization.coordinates v a q)) = Sum.inr q
    rw [DenefPasNormalization.decode_coordinates]

theorem code_surjective (v : Valuation K Γ) (a : Data v) (h : Trivial v) :
    Function.Surjective (code v a h) := fun q => ⟨pack v a q, code_pack v a h q⟩

theorem field_code (v : Valuation K Γ) (a : Data v) (h : Trivial v) (p : Coord → Aux v) :
    DenefPasLanguage.IsField (code v a h p) ↔ ∃ r : Residue v, p 1 = .inl r := by
  cases hp : p 1 <;> simp [code, hp, DenefPasLanguage.IsField]

theorem rv_code (v : Valuation K Γ) (a : Data v) (h : Trivial v) (p : Coord → Aux v) :
    IsRV (code v a h p) ↔ ∃ g : Gamma v, p 1 = .inr g := by
  cases hp : p 1 <;> simp [code, hp, IsRV]

theorem fieldValue_code (v : Valuation K Γ) (a : Data v) (h : Trivial v) (p : Coord → Aux v) :
    fieldValue (code v a h p) = (trivialAcEquiv v a h).symm (DenefPasAux.residue (p 1)) := by
  cases hp : p 1 <;> simp [code, hp, fieldValue, DenefPasAux.residue]

theorem ac_fieldValue_code (v : Valuation K Γ) (a : Data v) (h : Trivial v) (p : Coord → Aux v) :
    a.ac (fieldValue (code v a h p)) = DenefPasAux.residue (p 1) := by
  rw [fieldValue_code, ← trivialAcEquiv_apply v a h, RingEquiv.apply_symm_apply]

theorem rvValue_code (v : Valuation K Γ) (a : Data v) (h : Trivial v) (p : Coord → Aux v)
    (hp : ∃ g : Gamma v, p 1 = .inr g) : rvValue (code v a h p) = decode v a p := by
  obtain ⟨g, hg⟩ := hp
  simp [code, hg, rvValue]

theorem code_eq_field (v : Valuation K Γ) (a : Data v) (h : Trivial v)
    (p : Coord → Aux v) (x : K) : code v a h p = .inl x ↔ p 1 = .inl (a.ac x) := by
  cases hp : p 1 with
  | inl r =>
    simp only [code, hp, Sum.inl.injEq]
    rw [← trivialAcEquiv_apply v a h x]
    constructor
    · intro hr
      have he := congrArg (trivialAcEquiv v a h) hr
      simpa using he
    · intro hr
      rw [hr, RingEquiv.symm_apply_apply]
  | inr g => simp [code, hp]

theorem code_eq_rv (v : Valuation K Γ) (a : Data v) (h : Trivial v)
    (p : Coord → Aux v) (q : RVCalc.RV v) :
    code v a h p = .inr q ↔ (∃ g : Gamma v, p 1 = .inr g) ∧ decode v a p = q := by
  cases hp : p 1 <;> simp [code, hp]

theorem equality_iff (v : Valuation K Γ) (a : Data v) (h : Trivial v) (p q : Coord → Aux v) :
    code v a h p = code v a h q ↔
      ((∃ r : Residue v, p 1 = .inl r) ∧ p 1 = q 1) ∨
      ((∃ g : Gamma v, p 1 = .inr g) ∧ (∃ g : Gamma v, q 1 = .inr g) ∧ decode v a p = decode v a q) := by
  cases hp : p 1 <;> cases hq : q 1 <;>
    simp [code, hp, hq, (trivialAcEquiv v a h).symm.injective.eq_iff]

end SpecialTransformations.Section6.DenefPasTrivialCodes
end
end

/-! Source: Section6.DenefPasTrivialFieldGraphs -/
section

/-! The native field atoms in auxiliary syntax under trivial valuation.
The ac ring equivalence proves the operation graphs, including junk inputs. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Section6.DenefPasTrivialFieldGraphs
open AngularComponent DenefPasCodes DenefPasLanguage DenefPasNativeModel

abbrev Target (E : _root_.FirstOrder.Language.{0, 0}) := DenefPasMorley.Auxiliary E

def fieldSymbol {k : ℕ} (f : FieldFunction k) : DenefPasAux.Functions k := by
  rcases f with ⟨f, hf, ha⟩
  cases f <;> try cases hf
  · exact .rZero
  · exact .rOne
  · exact .rAdd
  · exact .rNeg
  · exact .rMul

def field {E : _root_.FirstOrder.Language.{0, 0}} {I : Type} (t : (Target E).Term I) :
    (Target E).Formula I := Relations.formula (.inl DenefPasAux.Relations.residue) ![t]

def rv {E : _root_.FirstOrder.Language.{0, 0}} {I : Type} (t : (Target E).Term I) :
    (Target E).Formula I := Relations.formula (.inl DenefPasAux.Relations.value) ![t]

def fieldGraph {E : _root_.FirstOrder.Language.{0, 0}} {I : Type} {k : ℕ}
    (f : FieldFunction k) (p : Fin k → Coord → (Target E).Term I)
    (q : Coord → (Target E).Term I) : (Target E).Formula I :=
  (q 1).equal (.func (.inl (fieldSymbol f)) (fun i => p i 1))

variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]

theorem fieldSymbol_eval (v : Valuation K Γ) (a : Data v) (h : Trivial v) {k : ℕ}
    (f : FieldFunction k) (p : Fin k → Coord → Aux v) :
    @Structure.funMap DenefPasAux.auxLanguage (Aux v) DenefPasAux.auxStructure k
        (fieldSymbol f) (fun i => p i 1) =
      Sum.inl (a.ac (fieldFunction f (fun i => DenefPasTrivialCodes.code v a h (p i)))) := by
  rw [← trivialAcEquiv_apply v a h]
  rcases f with ⟨f, hf, ha⟩
  cases f <;> try cases hf
  · simp [fieldSymbol, Structure.funMap, DenefPasAux.auxStructure, fieldFunction]
  · simp [fieldSymbol, Structure.funMap, DenefPasAux.auxStructure, fieldFunction]
  · cases h0 : p 0 1 <;> cases h1 : p 1 1 <;>
      simp [fieldSymbol, Structure.funMap, DenefPasAux.auxStructure, fieldFunction,
        DenefPasTrivialCodes.code, h0, h1, DenefPasLanguage.IsField, fieldValue]
  · cases h0 : p 0 1 <;>
      simp [fieldSymbol, Structure.funMap, DenefPasAux.auxStructure, fieldFunction,
        DenefPasTrivialCodes.code, h0, DenefPasLanguage.IsField, fieldValue]
  · cases h0 : p 0 1 <;> cases h1 : p 1 1 <;>
      simp [fieldSymbol, Structure.funMap, DenefPasAux.auxStructure, fieldFunction,
        DenefPasTrivialCodes.code, h0, h1, DenefPasLanguage.IsField, fieldValue]

section Semantics
variable (E : _root_.FirstOrder.Language.{0, 0}) (v : Valuation K Γ) (a : Data v)
variable [E.Structure (Aux v)]
local instance : DenefPasAux.auxLanguage.Structure (Aux v) := DenefPasAux.auxStructure
local instance : (Target E).Structure (Aux v) :=
  FirstOrder.Language.sumStructure DenefPasAux.auxLanguage E (Aux v)

theorem field_realize {I : Type} (t : (Target E).Term I) (z : I → Aux v) :
    (field t).Realize z ↔ ∃ r : Residue v, t.realize z = .inl r := by
  simp only [field, Relations.formula, Relations.boundedFormula, Formula.Realize,
    BoundedFormula.Realize, Term.realize_relabel, Sum.elim_comp_inl]
  rfl

theorem rv_realize {I : Type} (t : (Target E).Term I) (z : I → Aux v) :
    (rv t).Realize z ↔ ∃ g : Gamma v, t.realize z = .inr g := by
  simp only [rv, Relations.formula, Relations.boundedFormula, Formula.Realize,
    BoundedFormula.Realize, Term.realize_relabel, Sum.elim_comp_inl]
  rfl

theorem fieldGraph_realize (h : Trivial v) {I : Type} {k : ℕ} (f : FieldFunction k)
    (p : Fin k → Coord → (Target E).Term I) (q : Coord → (Target E).Term I) (z : I → Aux v) :
    (fieldGraph f p q).Realize z ↔ DenefPasTrivialCodes.code v a h (fun b => (q b).realize z) =
      nativeFunction v a f.val (fun i => DenefPasTrivialCodes.code v a h (fun b => (p i b).realize z)) := by
  rw [fieldGraph, Formula.realize_equal, Term.realize_func]
  change (q 1).realize z = @Structure.funMap DenefPasAux.auxLanguage (Aux v) DenefPasAux.auxStructure k
      (fieldSymbol f) (fun i => (p i 1).realize z) ↔ _
  rw [fieldSymbol_eval v a h f (fun i b => (p i b).realize z), nativeFunction_field]
  exact (DenefPasTrivialCodes.code_eq_field v a h (fun b => (q b).realize z)
    (fieldFunction f (fun i => DenefPasTrivialCodes.code v a h (fun b => (p i b).realize z)))).symm

end Semantics
end SpecialTransformations.Section6.DenefPasTrivialFieldGraphs
end
end

/-! Source: Section6.DenefPasTrivialRVGraphs -/
section

/-! Native RV atoms reuse the already constructed RV dictionary. Only
the native VF/RV tag and canonical wrong-sort branch are added. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Section6.DenefPasTrivialRVGraphs
open AngularComponent DenefPasCodes DenefPasNativeModel RVAbstraction RVGraphLanguage
open DenefPasTrivialFieldGraphs

abbrev Context (k : ℕ) := DenefPasNativeDictionary.FunctionContext k

def inputsRV (E : _root_.FirstOrder.Language.{0, 0}) (k : ℕ) : (Target E).Formula (Context k) :=
  Formula.iInf (fun i : Fin k => rv (.var (.inl (i, 1))))

def functionGraph (E : _root_.FirstOrder.Language.{0, 0}) {k : ℕ} (f : RVFunction k) :
    (Target E).Formula (Context k) :=
  rv (.var (.inr 1)) ⊓
    ((inputsRV E k ⊓ DenefPasDictionary.lift E (DenefPasNativeDictionary.functionGraph f)) ⊔
      ((inputsRV E k).not ⊓ DenefPasDictionary.lift E
        (DenefPasEquality.zero DenefPasNativeDictionary.output)))

theorem native_function {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) (a : Data v) {k : ℕ} (f : RVFunction k)
    (z : Fin k → DenefPasNativeCodes.NativeCarrier v) :
    nativeFunction v a f.val z = liftRV v a f z := by
  rcases f with ⟨f, hf, ha⟩
  cases f <;> try cases hf
  all_goals first | rfl | have h := ha 0; cases h

variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]
variable (E : _root_.FirstOrder.Language.{0, 0}) (v : Valuation K Γ) (a : Data v)
variable [E.Structure (Aux v)]
local instance : DenefPasAux.auxLanguage.Structure (Aux v) := DenefPasAux.auxStructure
local instance : (Target E).Structure (Aux v) :=
  FirstOrder.Language.sumStructure DenefPasAux.auxLanguage E (Aux v)

theorem inputsRV_realize {k : ℕ} (w : Context k → Aux v) :
    (inputsRV E k).Realize w ↔ ∀ i, ∃ g : Gamma v, w (.inl (i, 1)) = .inr g := by
  simp only [inputsRV, Formula.realize_iInf, rv_realize E v, Term.realize_var]

theorem functionGraph_realize (h : Trivial v) {k : ℕ} (f : RVFunction k) (w : Context k → Aux v) :
    (functionGraph E f).Realize w ↔ DenefPasTrivialCodes.code v a h (w ∘ Sum.inr) =
      nativeFunction v a f.val (PairInterpretation.decode (DenefPasTrivialCodes.code v a h) (w ∘ Sum.inl)) := by
  let z := PairInterpretation.decode (DenefPasTrivialCodes.code v a h) (w ∘ Sum.inl)
  let u := PairInterpretation.decode (decode v a) (w ∘ Sum.inl)
  let P : Prop := ∀ i : Fin k, ∃ g : Gamma v, w (.inl (i, 1)) = .inr g
  have htag : (∀ i, IsRV (z i)) ↔ P := by
    exact forall_congr' (fun i => DenefPasTrivialCodes.rv_code v a h (fun b => w (.inl (i, b))))
  have hvalues (hp : P) : rvValue ∘ z = u := by
    funext i
    exact DenefPasTrivialCodes.rvValue_code v a h (fun b => w (.inl (i, b))) (hp i)
  have hn : nativeFunction v a f.val z = if P then
      Sum.inr (@Structure.funMap RVBase (RVCalc.RV v) (DenefPasRV.rvStructure v a) k f u)
      else Sum.inr none := by
    rw [native_function, liftRV]
    by_cases hp : P
    · rw [if_pos (htag.mpr hp), hvalues hp, if_pos hp]
    · rw [if_neg (fun hz => hp (htag.mp hz)), if_neg hp]
  have hf := DenefPasNativeDictionary.functionGraph_realize v a f w
  have hz : (DenefPasEquality.zero (DenefPasNativeDictionary.output (k := k))).Realize w ↔
      decode v a (w ∘ Sum.inr) = none := by
    have hh := (DenefPasEquality.zero_realize v (DenefPasNativeDictionary.output (k := k)) w).trans
      (decode_zero_iff v a _).symm
    simpa only [DenefPasNativeDictionary.output, Term.realize_var, Function.comp_def] using hh
  change (functionGraph E f).Realize w ↔ DenefPasTrivialCodes.code v a h (w ∘ Sum.inr) = nativeFunction v a f.val z
  rw [hn]
  simp only [functionGraph, Formula.realize_inf, Formula.realize_sup, Formula.realize_not,
    inputsRV_realize E v, rv_realize E v, Term.realize_var, DenefPasDictionary.lift_realize E v, hf, hz]
  by_cases hp : P <;> dsimp only [P] at hp <;>
    simp only [P, u, Function.comp_def, hp, if_true, if_false, not_true_eq_false, not_false_eq_true, true_and, false_and,
      true_or, false_or, or_false, DenefPasTrivialCodes.code_eq_rv] <;>
    simp [DenefPasTrivialCodes.code_eq_rv]

end SpecialTransformations.Section6.DenefPasTrivialRVGraphs
end
end

/-! Source: Section6.DenefPasTrivialMixedGraphs -/
section

/-! Equality and rv on the native carrier in the trivial branch. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Section6.DenefPasTrivialMixedGraphs
open AngularComponent DenefPasCodes DenefPasNativeModel
open DenefPasTrivialFieldGraphs

def equalityGraph (E : _root_.FirstOrder.Language.{0, 0}) : (Target E).Formula (Coord ⊕ Coord) :=
  (field (.var (.inl 1)) ⊓ (Term.var (.inl 1)).equal (.var (.inr 1))) ⊔
    (rv (.var (.inl 1)) ⊓ (rv (.var (.inr 1)) ⊓
      DenefPasDictionary.lift E DenefPasNativeDictionary.dictionary.equality))

def fieldCode {I : Type} (t : DenefPasAux.auxLanguage.Term I) : Coord → DenefPasAux.auxLanguage.Term I :=
  ![DenefPasAux.residueProjection t, .func DenefPasAux.Functions.gOne Fin.elim0]

def rvMapGraph (E : _root_.FirstOrder.Language.{0, 0}) :
    (Target E).Formula (DenefPasNativeDictionary.FunctionContext 1) :=
  rv (.var (.inr 1)) ⊓ DenefPasDictionary.lift E
    (DenefPasEquality.equal DenefPasNativeDictionary.output
      (fieldCode (DenefPasNativeDictionary.arg 0 1)))

variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]
variable (E : _root_.FirstOrder.Language.{0, 0}) (v : Valuation K Γ) (a : Data v)
variable [E.Structure (Aux v)]
local instance : DenefPasAux.auxLanguage.Structure (Aux v) := DenefPasAux.auxStructure
local instance : (Target E).Structure (Aux v) :=
  FirstOrder.Language.sumStructure DenefPasAux.auxLanguage E (Aux v)

theorem equalityGraph_realize (h : Trivial v) (w : Coord ⊕ Coord → Aux v) :
    (equalityGraph E).Realize w ↔
      DenefPasTrivialCodes.code v a h (w ∘ Sum.inl) = DenefPasTrivialCodes.code v a h (w ∘ Sum.inr) := by
  have he := DenefPasEquality.equal_realize v a
    (fun b => Term.var (.inl b)) (fun b => Term.var (.inr b)) w
  simp only [Term.realize_var, Function.comp_def] at he
  simp only [equalityGraph, Formula.realize_sup, Formula.realize_inf, field_realize E v,
    rv_realize E v, Formula.realize_equal, Term.realize_var, DenefPasDictionary.lift_realize E v,
    DenefPasNativeDictionary.dictionary, he]
  exact (DenefPasTrivialCodes.equality_iff v a h (w ∘ Sum.inl) (w ∘ Sum.inr)).symm

theorem fieldCode_decode {I : Type} (t : DenefPasAux.auxLanguage.Term I) (w : I → Aux v) :
    decode v a (fun b => (fieldCode t b).realize w) = encode v a (DenefPasAux.residue (t.realize w)) 1 := by
  have he : (fun b => (fieldCode t b).realize w) =
      ![Sum.inl (DenefPasAux.residue (t.realize w)), Sum.inr (1 : Gamma v)] := by
    funext b
    fin_cases b
    · exact DenefPasAux.residueProjection_realize t w
    · rfl
  rw [he]
  rfl

theorem rvMapGraph_realize (h : Trivial v) (w : DenefPasNativeDictionary.FunctionContext 1 → Aux v) :
    (rvMapGraph E).Realize w ↔ DenefPasTrivialCodes.code v a h (w ∘ Sum.inr) =
      nativeFunction v a Fn.rvMap
        (PairInterpretation.decode (DenefPasTrivialCodes.code v a h) (w ∘ Sum.inl)) := by
  have he : (DenefPasEquality.equal DenefPasNativeDictionary.output
      (fieldCode (DenefPasNativeDictionary.arg 0 1))).Realize w ↔
      decode v a (w ∘ Sum.inr) = encode v a (DenefPasAux.residue (w (.inl (0, 1)))) 1 := by
    have hh := DenefPasEquality.equal_realize v a DenefPasNativeDictionary.output
      (fieldCode (DenefPasNativeDictionary.arg 0 1)) w
    rw [fieldCode_decode] at hh
    simpa only [DenefPasNativeDictionary.arg, DenefPasNativeDictionary.output, Term.realize_var,
      Function.comp_def] using hh
  simp only [rvMapGraph, Formula.realize_inf, rv_realize E v, Term.realize_var,
    DenefPasDictionary.lift_realize E v, he]
  change ((∃ g : Gamma v, w (.inr 1) = .inr g) ∧ decode v a (w ∘ Sum.inr) =
    encode v a (DenefPasAux.residue (w (.inl (0, 1)))) 1) ↔
      DenefPasTrivialCodes.code v a h (w ∘ Sum.inr) = .inr (RVCalc.rv v
        (DenefPasLanguage.fieldValue (DenefPasTrivialCodes.code v a h (fun b => w (.inl (0, b))))))
  rw [DenefPasTrivialCodes.code_eq_rv, DenefPasTrivialCodes.rv_encode v a h,
    DenefPasTrivialCodes.ac_fieldValue_code]
  rfl

end SpecialTransformations.Section6.DenefPasTrivialMixedGraphs
end
end

/-! Source: Section6.DenefPasTrivialRelationalGraphs -/
section

/-! Guarded native RV relations and auxiliary Morley predicates. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Section6.DenefPasTrivialRelationalGraphs
open AngularComponent DenefPasCodes DenefPasNativeModel RVAbstraction RVGraphLanguage
open DenefPasTrivialFieldGraphs

def arguments (E : _root_.FirstOrder.Language.{0, 0}) (k : ℕ) : (Target E).Formula (Fin k × Coord) :=
  Formula.iInf (fun i : Fin k => rv (.var (i, 1)))

def relationGraph (E : _root_.FirstOrder.Language.{0, 0}) {k : ℕ} (r : RVRelation k) :
    (Target E).Formula (Fin k × Coord) :=
  arguments E k ⊓ DenefPasDictionary.lift E (DenefPasNativeDictionary.relationGraph r)

def extraGraph {E : _root_.FirstOrder.Language.{0, 0}} {k : ℕ}
    (θ : (Target E).Formula (Fin k × Coord)) : (Target E).Formula (Fin k × Coord) :=
  arguments E k ⊓ DenefPasMorley.relationGraph θ

theorem native_relation {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) (a : Data v) {k : ℕ} (r : RVRelation k)
    (z : Fin k → DenefPasNativeCodes.NativeCarrier v) :
    nativeRelation v a r.val z ↔ (∀ i, IsRV (z i)) ∧
      @Structure.RelMap RVBase (RVCalc.RV v) (DenefPasRV.rvStructure v a) k r (rvValue ∘ z) := by
  rcases r with ⟨r, hr⟩
  cases r with
  | memVF => have h := hr 0; cases h
  | memRV =>
    change IsRV (z 0) ↔ (∀ i : Fin 1, IsRV (z i)) ∧ True
    constructor
    · intro h
      exact ⟨fun i => by fin_cases i; exact h, trivial⟩
    · exact fun h => h.1 0
  | memUnits =>
    change (IsRV (z 0) ∧ rvValue (z 0) ≠ none ∧ gammaValue v a (rvValue (z 0)) = 1) ↔
      (∀ i : Fin 1, IsRV (z i)) ∧ rvValue (z 0) ≠ none ∧ gammaValue v a (rvValue (z 0)) = 1
    constructor
    · intro h
      exact ⟨fun i => by fin_cases i; exact h.1, h.2⟩
    · exact fun h => ⟨h.1 0, h.2⟩
  | rvLe => rfl

variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]
variable (E : _root_.FirstOrder.Language.{0, 0}) (v : Valuation K Γ) (a : Data v)
variable [E.Structure (Aux v)]
local instance : DenefPasAux.auxLanguage.Structure (Aux v) := DenefPasAux.auxStructure
local instance : (Target E).Structure (Aux v) :=
  FirstOrder.Language.sumStructure DenefPasAux.auxLanguage E (Aux v)

theorem arguments_realize {k : ℕ} (w : Fin k × Coord → Aux v) :
    (arguments E k).Realize w ↔ ∀ i, ∃ g : Gamma v, w (i, 1) = .inr g := by
  simp only [arguments, Formula.realize_iInf, rv_realize E v, Term.realize_var]

theorem relationGraph_realize (h : Trivial v) {k : ℕ} (r : RVRelation k) (w : Fin k × Coord → Aux v) :
    (relationGraph E r).Realize w ↔
      nativeRelation v a r.val (PairInterpretation.decode (DenefPasTrivialCodes.code v a h) w) := by
  let z := PairInterpretation.decode (DenefPasTrivialCodes.code v a h) w
  let u := PairInterpretation.decode (decode v a) w
  let P : Prop := ∀ i : Fin k, ∃ g : Gamma v, w (i, 1) = .inr g
  have htag : (∀ i, IsRV (z i)) ↔ P :=
    forall_congr' (fun i => DenefPasTrivialCodes.rv_code v a h (fun b => w (i, b)))
  have hvalues (hp : P) : rvValue ∘ z = u := by
    funext i
    exact DenefPasTrivialCodes.rvValue_code v a h (fun b => w (i, b)) (hp i)
  have hb := DenefPasNativeDictionary.relationGraph_realize v a r w
  change (relationGraph E r).Realize w ↔ nativeRelation v a r.val z
  rw [native_relation]
  simp only [relationGraph, Formula.realize_inf, arguments_realize E v,
    DenefPasDictionary.lift_realize E v, hb]
  by_cases hp : P
  · rw [hvalues hp]
    have hz := htag.mpr hp
    dsimp only [P] at hp
    simp only [hp, hz, u, true_and]
  · have hz : ¬ ∀ i, IsRV (z i) := fun hh => hp (htag.mp hh)
    dsimp only [P] at hp
    simp only [hp, hz, false_and]

theorem extraGraph_realize (h : Trivial v) {k : ℕ}
    (θ : (Target E).Formula (Fin k × Coord)) (w : Fin k × Coord → Aux v) :
    (extraGraph θ).Realize w ↔
      (∀ i, IsRV (DenefPasTrivialCodes.code v a h (fun b => w (i, b)))) ∧ θ.Realize
        (fun j => DenefPasNormalization.coordinates v a
          (rvValue (DenefPasTrivialCodes.code v a h (fun b => w (j.1, b)))) j.2) := by
  simp only [extraGraph, Formula.realize_inf, arguments_realize E v, DenefPasMorley.relationGraph_realize E v a]
  have htag : (∀ i, IsRV (DenefPasTrivialCodes.code v a h (fun b => w (i, b)))) ↔
      (∀ i, ∃ g : Gamma v, w (i, 1) = .inr g) :=
    forall_congr' (fun i => DenefPasTrivialCodes.rv_code v a h (fun b => w (i, b)))
  by_cases hp : ∀ i, ∃ g : Gamma v, w (i, 1) = .inr g
  · have hz := htag.mpr hp
    have he : (fun j : Fin k × Coord => DenefPasNormalization.coordinates v a
        (rvValue (DenefPasTrivialCodes.code v a h (fun b => w (j.1, b)))) j.2) =
        (fun j => DenefPasNormalization.coordinates v a (decode v a (fun b => w (j.1, b))) j.2) := by
      funext j
      rw [DenefPasTrivialCodes.rvValue_code v a h _ (hp j.1)]
    rw [he]
    simp only [hp, hz, true_and]
  · have hz : ¬ ∀ i, IsRV (DenefPasTrivialCodes.code v a h (fun b => w (i, b))) :=
      fun hh => hp (htag.mp hh)
    simp only [hp, hz, false_and]

end SpecialTransformations.Section6.DenefPasTrivialRelationalGraphs
end
end

/-! Source: Section6.DenefPasTrivialDictionary -/
section

/-! A fixed interpretation of the complete native relational expansion
in the auxiliary language when the valuation is trivial. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Section6.DenefPasTrivialDictionary
open AngularComponent DenefPasCodes DenefPasNativeModel DenefPasForwardPatterns
open DenefPasTrivialFieldGraphs

def arg {E : _root_.FirstOrder.Language.{0, 0}} {k : ℕ} (i : Fin k) (b : Coord) :
    (Target E).Term (DenefPasNativeDictionary.FunctionContext k) := .var (.inl (i, b))
def output {E : _root_.FirstOrder.Language.{0, 0}} {k : ℕ} (b : Coord) :
    (Target E).Term (DenefPasNativeDictionary.FunctionContext k) := .var (.inr b)
def relArg {E : _root_.FirstOrder.Language.{0, 0}} {k : ℕ} (i : Fin k) (b : Coord) :
    (Target E).Term (Fin k × Coord) := .var (i, b)

def dictionary (E : _root_.FirstOrder.Language.{0, 0}) : PairSyntax.Syntax (Native E) (Target E) where
  equality := DenefPasTrivialMixedGraphs.equalityGraph E
  functionGraph := fun f => match f with
    | .inr f => isEmptyElim f
    | .inl .vfZero => fieldGraph ⟨.vfZero, rfl, fun i => i.elim0⟩ arg output
    | .inl .vfOne => fieldGraph ⟨.vfOne, rfl, fun i => i.elim0⟩ arg output
    | .inl .vfAdd => fieldGraph ⟨.vfAdd, rfl, fun _ => rfl⟩ arg output
    | .inl .vfNeg => fieldGraph ⟨.vfNeg, rfl, fun _ => rfl⟩ arg output
    | .inl .vfMul => fieldGraph ⟨.vfMul, rfl, fun _ => rfl⟩ arg output
    | .inl .rvMap => DenefPasTrivialMixedGraphs.rvMapGraph E
    | .inl .rvZero => DenefPasTrivialRVGraphs.functionGraph E ⟨.rvZero, rfl, fun i => i.elim0⟩
    | .inl .rvOne => DenefPasTrivialRVGraphs.functionGraph E ⟨.rvOne, rfl, fun i => i.elim0⟩
    | .inl .rvMul => DenefPasTrivialRVGraphs.functionGraph E ⟨.rvMul, rfl, fun _ => rfl⟩
    | .inl .rvInv => DenefPasTrivialRVGraphs.functionGraph E ⟨.rvInv, rfl, fun _ => rfl⟩
    | .inl .kAdd => DenefPasTrivialRVGraphs.functionGraph E ⟨.kAdd, rfl, fun _ => rfl⟩
    | .inl .kNeg => DenefPasTrivialRVGraphs.functionGraph E ⟨.kNeg, rfl, fun _ => rfl⟩
  relationGraph := fun r => match r with
    | .inl .memVF => field (relArg 0 1)
    | .inl .memRV => rv (relArg 0 1)
    | .inl .memUnits => DenefPasTrivialRelationalGraphs.relationGraph E ⟨.memUnits, fun _ => rfl⟩
    | .inl .rvLe => DenefPasTrivialRelationalGraphs.relationGraph E ⟨.rvLe, fun _ => rfl⟩
    | .inr θ => DenefPasTrivialRelationalGraphs.extraGraph θ

variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]
variable (E : _root_.FirstOrder.Language.{0, 0}) (v : Valuation K Γ) (a : Data v)
variable [E.Structure (Aux v)]
local instance : (Native E).Structure (Model E v a) := structureOn E v a
local instance : DenefPasAux.auxLanguage.Structure (Aux v) := DenefPasAux.auxStructure
local instance : (Target E).Structure (Aux v) :=
  FirstOrder.Language.sumStructure DenefPasAux.auxLanguage E (Aux v)

def interpretedCode (h : Trivial v) : (Coord → Aux v) → Model E v a := DenefPasTrivialCodes.code v a h

def realizes (h : Trivial v) : PairSyntax.Realizes (dictionary E) (Model E v a) (Aux v) where
  code := interpretedCode E v a h
  onto := DenefPasTrivialCodes.code_surjective v a h
  equality := fun w => DenefPasTrivialMixedGraphs.equalityGraph_realize E v a h w
  functionGraph := fun f w => by
    cases f with
    | inr f => exact isEmptyElim f
    | inl f =>
      change ((dictionary E).functionGraph (.inl f)).Realize w ↔
        DenefPasTrivialCodes.code v a h (w ∘ Sum.inr) =
          nativeFunction v a f (fun i => DenefPasTrivialCodes.code v a h (fun b => w (.inl (i, b))))
      cases f with
      | vfZero =>
        simpa only [dictionary, interpretedCode, arg, output, Term.realize_var, Function.comp_def,
          PairInterpretation.decode, Structure.funMap, structureOn] using
          fieldGraph_realize E v a h ⟨.vfZero, rfl, fun i => i.elim0⟩ arg output w
      | vfOne =>
        simpa only [dictionary, interpretedCode, arg, output, Term.realize_var, Function.comp_def,
          PairInterpretation.decode, Structure.funMap, structureOn] using
          fieldGraph_realize E v a h ⟨.vfOne, rfl, fun i => i.elim0⟩ arg output w
      | vfAdd =>
        simpa only [dictionary, interpretedCode, arg, output, Term.realize_var, Function.comp_def,
          PairInterpretation.decode, Structure.funMap, structureOn] using
          fieldGraph_realize E v a h ⟨.vfAdd, rfl, fun _ => rfl⟩ arg output w
      | vfNeg =>
        simpa only [dictionary, interpretedCode, arg, output, Term.realize_var, Function.comp_def,
          PairInterpretation.decode, Structure.funMap, structureOn] using
          fieldGraph_realize E v a h ⟨.vfNeg, rfl, fun _ => rfl⟩ arg output w
      | vfMul =>
        simpa only [dictionary, interpretedCode, arg, output, Term.realize_var, Function.comp_def,
          PairInterpretation.decode, Structure.funMap, structureOn] using
          fieldGraph_realize E v a h ⟨.vfMul, rfl, fun _ => rfl⟩ arg output w
      | rvMap =>
        exact DenefPasTrivialMixedGraphs.rvMapGraph_realize E v a h w
      | rvZero =>
        exact DenefPasTrivialRVGraphs.functionGraph_realize E v a h ⟨.rvZero, rfl, fun i => i.elim0⟩ w
      | rvOne =>
        exact DenefPasTrivialRVGraphs.functionGraph_realize E v a h ⟨.rvOne, rfl, fun i => i.elim0⟩ w
      | rvMul =>
        exact DenefPasTrivialRVGraphs.functionGraph_realize E v a h ⟨.rvMul, rfl, fun _ => rfl⟩ w
      | rvInv =>
        exact DenefPasTrivialRVGraphs.functionGraph_realize E v a h ⟨.rvInv, rfl, fun _ => rfl⟩ w
      | kAdd =>
        exact DenefPasTrivialRVGraphs.functionGraph_realize E v a h ⟨.kAdd, rfl, fun _ => rfl⟩ w
      | kNeg =>
        exact DenefPasTrivialRVGraphs.functionGraph_realize E v a h ⟨.kNeg, rfl, fun _ => rfl⟩ w
  relationGraph := fun r w => by
    cases r with
    | inl r =>
      cases r with
      | memVF =>
        simpa only [dictionary, interpretedCode, relArg, Term.realize_var, Structure.RelMap,
          structureOn, nativeRelation, PairInterpretation.decode, DenefPasTrivialCodes.field_code] using
          field_realize E v (relArg 0 1) w
      | memRV =>
        simpa only [dictionary, interpretedCode, relArg, Term.realize_var, Structure.RelMap,
          structureOn, nativeRelation, PairInterpretation.decode, DenefPasTrivialCodes.rv_code] using
          rv_realize E v (relArg 0 1) w
      | memUnits =>
        simpa only [dictionary, interpretedCode, Structure.RelMap, structureOn] using
          DenefPasTrivialRelationalGraphs.relationGraph_realize E v a h ⟨.memUnits, fun _ => rfl⟩ w
      | rvLe =>
        simpa only [dictionary, interpretedCode, Structure.RelMap, structureOn] using
          DenefPasTrivialRelationalGraphs.relationGraph_realize E v a h ⟨.rvLe, fun _ => rfl⟩ w
    | inr θ =>
      simpa only [dictionary, interpretedCode, Structure.RelMap, structureOn, PairInterpretation.decode] using
        DenefPasTrivialRelationalGraphs.extraGraph_realize E v a h θ w

theorem formula_realize (h : Trivial v) {I : Type} (φ : (Native E).Formula I) (z : (I × Coord) → Aux v) :
    (PairSyntax.formula (dictionary E) φ).Realize z ↔
      φ.Realize (PairInterpretation.decode (interpretedCode E v a h) z) :=
  PairSyntax.formula_realize (dictionary E) (realizes E v a h) φ z

end SpecialTransformations.Section6.DenefPasTrivialDictionary
end
end

/-! Source: Section6.DenefPasTrivialParameters -/
section

/-! Auxiliary code terms for the original free parameters in the trivial
branch. The original native packed assignment is recovered exactly. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language

namespace SpecialTransformations.Section6.DenefPasTrivialParameters
open AngularComponent DenefPasCodes DenefPasLanguage DenefPasNativeModel DenefPasForwardPatterns
open DenefPasParameters FiniteSortContext

def replacement {E : _root_.FirstOrder.Language.{0, 0}} {I : Type} (s : I → SortKind)
    (j : (I × Coord) × Coord) : (language E).Term I :=
  match partition (nativeSort s) j.1 with
  | .inl p => if j.2 = 0 then auxiliaryConstant .rZero
      else .func (.inr (.inr .angular)) ![fieldParameter s p]
  | .inr r => rvParameter s r j.2

variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]
variable (E : _root_.FirstOrder.Language.{0, 0}) (v : Valuation K Γ) (a : Data v)
variable [E.Structure (Aux v)]
local instance : (Native E).Structure (Model E v a) := structureOn E v a
local instance : (language E).Structure (DenefPasAuxLift.Model E v a) := dpStructure E v a

theorem rvParameter_value {I : Type} (s : I → SortKind) (z : I → DenefPasAuxLift.Model E v a)
    (hz : Sorted E v a s z) (r : RVPart (nativeSort s)) :
    ∃ g : Gamma v, (rvParameter (E := E) s r 1).realize (M := DenefPasAuxLift.Model E v a) z = .inr (.inr g) := by
  rcases r with ⟨⟨i, b⟩, hr⟩
  have hi := hz i
  cases hs : s i with
  | field => simp [nativeSort, hs] at hr
  | residue => simp [rvParameter, hs, auxiliaryConstant_realize E v a, constantValue] <;> exact ⟨_, rfl⟩
  | value =>
    rw [hs] at hi
    obtain ⟨g, hg⟩ := hi
    by_cases hb : b = 0 <;>
      simp [rvParameter, hs, hb, auxiliaryConstant_realize E v a, constantValue, Term.realize_var, hg] <;> exact ⟨_, rfl⟩

theorem replacement_isAux {I : Type} (s : I → SortKind) (z : I → DenefPasAuxLift.Model E v a)
    (hz : Sorted E v a s z) (j : (I × Coord) × Coord) :
    IsAux ((replacement (E := E) s j).realize (M := DenefPasAuxLift.Model E v a) z) := by
  rcases j with ⟨j, c⟩
  cases he : partition (nativeSort s) j with
  | inl p =>
    simp only [replacement, he]
    fin_cases c
    · simp [replacement, he, auxiliaryConstant_realize E v a, IsAux]
    · change IsAux ((if (1 : Coord) = 0 then auxiliaryConstant .rZero else
        Term.func (L := language E) (.inr (.inr .angular)) ![fieldParameter s p]).realize
          (M := DenefPasAuxLift.Model E v a) z)
      rw [if_neg (by decide)]
      exact ⟨_, rfl⟩
  | inr r => simpa only [replacement, he] using rvParameter_isAux E v a s z hz r c

theorem decode_replacement (h : Trivial v) {I : Type} (s : I → SortKind)
    (z : I → DenefPasAuxLift.Model E v a) (hz : Sorted E v a s z) (j : I × Coord) :
    DenefPasTrivialDictionary.interpretedCode E v a h
      (fun c => auxValue ((replacement (E := E) s (j, c)).realize (M := DenefPasAuxLift.Model E v a) z)) =
        packed E v a z j := by
  cases he : partition (nativeSort s) j with
  | inl p =>
    have hj : p.val = j := by
      have hh := (partition (nativeSort s)).symm_apply_apply j
      rw [he] at hh
      exact hh
    have hsecond : auxValue ((replacement (E := E) s (j, 1)).realize
        (M := DenefPasAuxLift.Model E v a) z) = .inl (a.ac (fieldValue (packed E v a z p.val))) := by
      simp only [replacement, he, if_neg (show (1 : Coord) ≠ 0 by decide)]
      change auxValue (Sum.inr (Sum.inl (a.ac (fieldValue ((fieldParameter (E := E) s p).realize
        (M := DenefPasAuxLift.Model E v a) z))))) = _
      rw [fieldParameter_realize E v a s z hz p]
      rfl
    have hc := (DenefPasTrivialCodes.code_eq_field v a h
      (fun c => auxValue ((replacement (E := E) s (j, c)).realize (M := DenefPasAuxLift.Model E v a) z))
      (fieldValue (packed E v a z p.val))).mpr hsecond
    exact hc.trans ((packed_vf E v a s z hz p).symm.trans (congrArg (packed E v a z) hj))
  | inr r =>
    have hj : r.val = j := by
      have hh := (partition (nativeSort s)).symm_apply_apply j
      rw [he] at hh
      exact hh
    obtain ⟨g, hg⟩ := rvParameter_value E v a s z hz r
    have hgamma : ∃ g : Gamma v, auxValue ((rvParameter (E := E) s r 1).realize
        (M := DenefPasAuxLift.Model E v a) z) = .inr g := by
      refine ⟨g, ?_⟩
      rw [hg]
      rfl
    have hc := (DenefPasTrivialCodes.code_eq_rv v a h
      (fun c => auxValue ((rvParameter (E := E) s r c).realize (M := DenefPasAuxLift.Model E v a) z))
      (rvValue (packed E v a z r.val))).mpr ⟨hgamma, rvParameter_decode E v a s z hz r⟩
    have hout := hc.trans ((packed_rv E v a s z hz r).symm.trans (congrArg (packed E v a z) hj))
    simpa only [DenefPasTrivialDictionary.interpretedCode, replacement, he] using hout

end SpecialTransformations.Section6.DenefPasTrivialParameters
end
end

/-! Source: Section6.DenefPasTrivialElimination -/
section

/-! Uniform field-quantifier elimination for trivial valuations. No
henselian model-recognition or elimination theorem is needed in this branch. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language

namespace SpecialTransformations.Section6.DenefPasTrivialElimination
open AngularComponent DenefPasCodes DenefPasLanguage DenefPasNativeModel DenefPasForwardPatterns
open DenefPasParameters

def formula {E : _root_.FirstOrder.Language.{0, 0}} {I : Type} (s : I → SortKind)
    (φ : (language E).Formula I) : (language E).Formula I :=
  (DenefPasAuxLift.lift (PairSyntax.formula (DenefPasTrivialDictionary.dictionary E)
    (PairSyntax.formula (DenefPasForwardDictionary.dictionary E) φ))).subst
      (DenefPasTrivialParameters.replacement (E := E) s)

theorem isFieldQF {E : _root_.FirstOrder.Language.{0, 0}} {I : Type} (s : I → SortKind)
    (φ : (language E).Formula I) : IsFieldQF (formula s φ) :=
  DenefPasSubstitution.isFieldQF_subst _ (DenefPasAuxLift.isFieldQF _)

variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]
variable (E : _root_.FirstOrder.Language.{0, 0}) (v : Valuation K Γ) (a : Data v)
variable [E.Structure (Aux v)]
local instance : (Native E).Structure (Model E v a) := structureOn E v a
local instance : (language E).Structure (DenefPasAuxLift.Model E v a) := dpStructure E v a
local instance : DenefPasAux.auxLanguage.Structure (Aux v) := DenefPasAux.auxStructure
local instance : (DenefPasMorley.Auxiliary E).Structure (Aux v) :=
  FirstOrder.Language.sumStructure DenefPasAux.auxLanguage E (Aux v)

theorem realize (h : Trivial v) {I : Type} (s : I → SortKind) (φ : (language E).Formula I)
    (z : I → DenefPasAuxLift.Model E v a) (hz : Sorted E v a s z) :
    (formula s φ).Realize z ↔ φ.Realize z := by
  let θ := PairSyntax.formula (DenefPasForwardDictionary.dictionary E) φ
  let χ := PairSyntax.formula (DenefPasTrivialDictionary.dictionary E) θ
  let u : (I × Coord) × Coord → Aux v := fun j => auxValue
    ((DenefPasTrivialParameters.replacement (E := E) s j).realize (M := DenefPasAuxLift.Model E v a) z)
  have hsubst := DenefPasSubstitution.subst_realize E v a χ
    (DenefPasTrivialParameters.replacement (E := E) s) z (DenefPasTrivialParameters.replacement_isAux E v a s z hz)
  have hcode : PairInterpretation.decode (DenefPasTrivialDictionary.interpretedCode E v a h) u =
      packed E v a z := by
    funext j
    exact DenefPasTrivialParameters.decode_replacement E v a h s z hz j
  have htriv := DenefPasTrivialDictionary.formula_realize E v a h θ u
  rw [hcode] at htriv
  have hpack : PairInterpretation.decode (DenefPasForwardDictionary.code E v a) (packed E v a z) = z := by
    funext i
    exact DenefPasNativeCodes.code_pack v a (z i)
  have hforward := DenefPasForwardDictionary.formula_realize E v a φ (packed E v a z)
  rw [hpack] at hforward
  exact hsubst.trans (htriv.trans hforward)

end SpecialTransformations.Section6.DenefPasTrivialElimination
end
end

/-! Source: Section6.DenefPasTrivialTest -/
section

/-! The auxiliary sentence detecting trivial valuation. Gamma is the
actual valuation image with infinity, so this test needs no VF quantifier. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language

namespace SpecialTransformations.Section6.DenefPasTrivialTest
open AngularComponent DenefPasCodes DenefPasLanguage DenefPasParameters

theorem fieldQF_sup {E : Language} {I : Type} {n : ℕ} {φ ψ : (language E).BoundedFormula I n}
    (hφ : IsFieldQF φ) (hψ : IsFieldQF ψ) : IsFieldQF (φ ⊔ ψ) :=
  .imp (.imp hφ .falsum) hψ

def body {E : _root_.FirstOrder.Language.{0, 0}} {I : Type} : (language E).BoundedFormula I 1 :=
  (.equal (.var (.inr 0)) (auxiliaryConstant .gInfinity)) ⊔
    (.equal (.var (.inr 0)) (auxiliaryConstant .gOne))

def test {E : _root_.FirstOrder.Language.{0, 0}} {I : Type} : (language E).Formula I := allValue body

theorem isFieldQF {E : _root_.FirstOrder.Language.{0, 0}} {I : Type} :
    IsFieldQF (test (E := E) (I := I)) :=
  .value (fieldQF_sup (.atomic (.equal _ _)) (.atomic (.equal _ _)))

variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]

theorem group_eq_one (v : Valuation K Γ) (h : Trivial v) (g : ValueGroup v) : g = 1 := by
  obtain ⟨u, hu⟩ := g.property
  apply Subtype.ext
  rw [← hu]
  exact Units.ext (h (u : K) (Units.ne_zero u))

theorem values_iff (v : Valuation K Γ) : (∀ g : Gamma v, g = 0 ∨ g = 1) ↔ Trivial v := by
  constructor
  · intro hg x hx
    let u := Units.mk0 x hx
    let g : ValueGroup v := (unitValue v).rangeRestrict u
    have he := hg (some g)
    change some g = none ∨ some g = some 1 at he
    rcases he with he | he
    · cases he
    · have hg1 : g = 1 := Option.some.inj he
      exact congrArg (fun t : ValueGroup v => (t.val : Γ)) hg1
  · intro h g
    cases g with
    | none => exact Or.inl rfl
    | some g => exact Or.inr (congrArg some (group_eq_one v h g))

variable (E : _root_.FirstOrder.Language.{0, 0}) (v : Valuation K Γ) (a : Data v)
variable [E.Structure (Aux v)]
local instance : (language E).Structure (DenefPasAuxLift.Model E v a) := dpStructure E v a

theorem realize {I : Type} (z : I → DenefPasAuxLift.Model E v a) :
    (test (E := E) (I := I)).Realize z ↔ Trivial v := by
  rw [test, Formula.Realize, DenefPasAuxLift.allValue_realize]
  apply Iff.trans ?_ (values_iff v)
  apply forall_congr'
  intro g
  simp only [body, BoundedFormula.realize_sup, BoundedFormula.Realize,
    Term.realize_var, auxiliaryConstant_realize E v a, constantValue]
  change ((Sum.inr (Sum.inr g) : Carrier v) = Sum.inr (Sum.inr 0) ∨
    (Sum.inr (Sum.inr g) : Carrier v) = Sum.inr (Sum.inr 1)) ↔ g = 0 ∨ g = 1
  simp only [Sum.inr.injEq]

end SpecialTransformations.Section6.DenefPasTrivialTest
end
end

