module

public import Section3.GuardedRVArithmetic
public import Section3.GuardedRVLiterals
public import Section3.GuardedRVTerms
public import Section3.QuantifierFree
public import Section3.RVNormalForm

@[expose] public section

/-!
# GuardedRationalNormalForm

The author-approved rational, explicitly guarded Definition 2.4. Completed QE
feeds a model-uniform DNF in the original language and original parameter slots.
The same-base definable-set wrapper introduces no additional parameters.

See NORMAL-FORM-NOTE.md for the agreed statement and language conventions.
-/

/- Component: NormalFormSourceSemantics -/
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open CanonicalRV ValuedModelMap ResidueTranscendentalTransport
namespace SpecialTransformations.Section3.GuardedRVNormalForm

namespace SourceAssignment
variable {α : Type} {n : ℕ} (sα : α → SortTag) (sn : Fin n → SortTag)
    {M : Type} [LRV.Structure M] (v : α → M) (x : Fin n → M)
    (hv : ∀ i, sortEval (sα i) (v i)) (hx : ∀ i, sortEval (sn i) (x i))

def vfValues (i : VFSlot sα sn) : VFType (M := M) := by
  refine ⟨Sum.elim v x i.val,?_⟩
  have hi : sortEval (Sum.elim sα sn i.val) (Sum.elim v x i.val) := by
    rcases i with ⟨i,hi⟩
    cases i with
    | inl j => exact hv j
    | inr j => exact hx j
  rw [i.property] at hi
  exact hi

def rvParameters (i : RVParameterSlot sα) : RVSort M :=
  ⟨v i.val,by simpa only [i.property,sortEval,iRV] using hv i.val⟩

def rvVariables (i : RVVariableSlot sn) : RVSort M :=
  ⟨x i.val,by simpa only [i.property,sortEval,iRV] using hx i.val⟩

variable [hM : M ⊨ Axioms.ACVF]
theorem expression_realize
    (P : RVExpr (VFSlot sα sn) (RVParameterSlot sα) (RVVariableSlot sn)) :
    (P.toTerm (vfSlotMap sα sn) (rvParameterMap (n := n) sα) (rvVariableMap (α := α) sn)).realize (Sum.elim v x) =
      (P.eval (vfValues sα sn v x hv hx) (rvParameters sα v hv) (rvVariables sn x hx)).val :=
  P.toTerm_realize _ _ _ (Sum.elim v x) _ _ _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)

theorem represented_realize (t : LRV.Term (α ⊕ Fin n))
    (P : RVExpr (VFSlot sα sn) (RVParameterSlot sα) (RVVariableSlot sn))
    (hP : P.toTerm (vfSlotMap sα sn) (rvParameterMap (n := n) sα) (rvVariableMap (α := α) sn)=t) :
    t.realize (Sum.elim v x) =
      (P.eval (vfValues sα sn v x hv hx) (rvParameters sα v hv) (rvVariables sn x hx)).val := by
  rw [← hP]
  exact expression_realize sα sn v x hv hx P
end SourceAssignment

end SpecialTransformations.Section3.GuardedRVNormalForm

namespace SpecialTransformations.Section3.PolarityDNF.Expr
variable {A : Type}
def negation (P : PolarityDNF.Expr A) : PolarityDNF.Expr A := .imp P .falsum
def conjunction (P Q : PolarityDNF.Expr A) : PolarityDNF.Expr A := negation (.imp P (negation Q))
theorem eval_negation (p : A → Prop) (P : PolarityDNF.Expr A) :
    (negation P).eval p ↔ ¬P.eval p := Iff.rfl
theorem eval_conjunction (p : A → Prop) (P Q : PolarityDNF.Expr A) :
    (conjunction P Q).eval p ↔ P.eval p ∧ Q.eval p := by
  simp only [conjunction,eval_negation,PolarityDNF.Expr.eval]
  tauto
end SpecialTransformations.Section3.PolarityDNF.Expr

namespace SpecialTransformations.Section3.GuardedRVNormalForm
theorem units_iff_nonzero_orders {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] (z : RVSort M) :
    iUnits z.val ↔ z ≠ 0 ∧ iLe z.val (1 : RVSort M).val ∧ iLe (1 : RVSort M).val z.val := by
  constructor
  · intro hz
    have h0 : z ≠ 0 := by
      intro he
      exact ValuedModelMap.units_ne_zero hz (by rw [he,RVOperations.zero_val])
    have ha := (RVOperations.units_iff_absolute_one z h0).mp hz
    refine ⟨h0,?_⟩
    rw [rvLe_iff_absolute,rvLe_iff_absolute,map_one,ha]
    exact ⟨le_rfl,le_rfl⟩
  · rintro ⟨hz,hl,hr⟩
    apply (RVOperations.units_iff_absolute_one z hz).mpr
    rw [rvLe_iff_absolute,map_one] at hl hr
    exact le_antisymm hr hl

namespace RVExpr
variable {I R V : Type}
def unitsExpression (P : RVExpr I R V) : PolarityDNF.Expr (RVAtom I R V) :=
  PolarityDNF.Expr.conjunction (PolarityDNF.Expr.negation (.atom (.equality P .zero)))
    (PolarityDNF.Expr.conjunction (.atom (.order P .one)) (.atom (.order .one P)))

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
theorem unitsExpression_correct (a : I → VFType (M := M)) (r : R → RVSort M) (y : V → RVSort M)
    (P : RVExpr I R V) :
    P.unitsExpression.eval (RVAtom.eval a r y) ↔ iUnits (P.eval a r y).val := by
  simp only [unitsExpression,PolarityDNF.Expr.eval_conjunction,PolarityDNF.Expr.eval_negation,
    PolarityDNF.Expr.eval,RVAtom.eval,eval]
  exact (units_iff_nonzero_orders _).symm
end RVExpr

namespace SourceAssignment
variable {α : Type} {n : ℕ} (sα : α → SortTag) (sn : Fin n → SortTag)
    {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] (v : α → M) (x : Fin n → M)
    (hv : ∀ i, sortEval (sα i) (v i)) (hx : ∀ i, sortEval (sn i) (x i))

theorem equality_realize (t u : LRV.Term (α ⊕ Fin n))
    (P Q : RVExpr (VFSlot sα sn) (RVParameterSlot sα) (RVVariableSlot sn))
    (hP : P.toTerm (vfSlotMap sα sn) (rvParameterMap (n := n) sα) (rvVariableMap (α := α) sn)=t)
    (hQ : Q.toTerm (vfSlotMap sα sn) (rvParameterMap (n := n) sα) (rvVariableMap (α := α) sn)=u) :
    (t.bdEqual u).Realize v x ↔ RVAtom.eval (vfValues sα sn v x hv hx) (rvParameters sα v hv)
      (rvVariables sn x hx) (.equality P Q) := by
  change t.realize (Sum.elim v x)=u.realize (Sum.elim v x) ↔ _
  rw [represented_realize sα sn v x hv hx t P hP,represented_realize sα sn v x hv hx u Q hQ]
  exact Subtype.val_inj

theorem rel1_realize (R : Rel 1) (t : LRV.Term (α ⊕ Fin n)) :
    (BoundedFormula.rel R ![t]).Realize v x ↔ Structure.RelMap (L := LRV) R ![t.realize (Sum.elim v x)] := by
  change Structure.RelMap (L := LRV) R (fun i => (![t] i).realize (Sum.elim v x)) ↔ _
  have he : (fun i => (![t] i).realize (Sum.elim v x)) = ![t.realize (Sum.elim v x)] := by
    funext i
    fin_cases i
    rfl
  rw [he]

theorem rel2_realize (R : Rel 2) (t u : LRV.Term (α ⊕ Fin n)) :
    (BoundedFormula.rel R ![t,u]).Realize v x ↔
      Structure.RelMap (L := LRV) R ![t.realize (Sum.elim v x),u.realize (Sum.elim v x)] := by
  change Structure.RelMap (L := LRV) R (fun i => (![t,u] i).realize (Sum.elim v x)) ↔ _
  have he : (fun i => (![t,u] i).realize (Sum.elim v x)) =
      ![t.realize (Sum.elim v x),u.realize (Sum.elim v x)] := by
    funext i
    fin_cases i <;> rfl
  rw [he]

theorem order_realize (t u : LRV.Term (α ⊕ Fin n))
    (P Q : RVExpr (VFSlot sα sn) (RVParameterSlot sα) (RVVariableSlot sn))
    (hP : P.toTerm (vfSlotMap sα sn) (rvParameterMap (n := n) sα) (rvVariableMap (α := α) sn)=t)
    (hQ : Q.toTerm (vfSlotMap sα sn) (rvParameterMap (n := n) sα) (rvVariableMap (α := α) sn)=u) :
    (BoundedFormula.rel Rel.rvLe ![t,u]).Realize v x ↔ RVAtom.eval (vfValues sα sn v x hv hx)
      (rvParameters sα v hv) (rvVariables sn x hx) (.order P Q) := by
  rw [rel2_realize]
  change iLe (t.realize (Sum.elim v x)) (u.realize (Sum.elim v x)) ↔ _
  rw [represented_realize sα sn v x hv hx t P hP,represented_realize sα sn v x hv hx u Q hQ]
  rfl

theorem units_realize (t : LRV.Term (α ⊕ Fin n))
    (P : RVExpr (VFSlot sα sn) (RVParameterSlot sα) (RVVariableSlot sn))
    (hP : P.toTerm (vfSlotMap sα sn) (rvParameterMap (n := n) sα) (rvVariableMap (α := α) sn)=t) :
    (BoundedFormula.rel Rel.memUnits ![t]).Realize v x ↔
      P.unitsExpression.eval (RVAtom.eval (vfValues sα sn v x hv hx) (rvParameters sα v hv) (rvVariables sn x hx)) := by
  rw [rel1_realize]
  change iUnits (t.realize (Sum.elim v x)) ↔ _
  rw [represented_realize sα sn v x hv hx t P hP]
  exact (RVExpr.unitsExpression_correct _ _ _ P).symm
end SourceAssignment

end SpecialTransformations.Section3.GuardedRVNormalForm

/- Component: NormalFormSourceParser -/
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open CanonicalRV ValuedModelMap ResidueTranscendentalTransport
namespace SpecialTransformations.Section3.GuardedRVNormalForm

variable {α : Type} {n : ℕ} (sα : α → SortTag) (sn : Fin n → SortTag)
abbrev SourceBoolean := PolarityDNF.Expr (RVAtom (VFSlot sα sn) (RVParameterSlot sα) (RVVariableSlot sn))

def SourceEquivalent (φ : LRV.BoundedFormula α n) (E : SourceBoolean sα sn) : Prop :=
  ∀ (M : Type) [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] (v : α → M) (x : Fin n → M)
    (hv : ∀ i, sortEval (sα i) (v i)) (hx : ∀ i, sortEval (sn i) (x i)),
    φ.Realize v x ↔ E.eval (RVAtom.eval (SourceAssignment.vfValues sα sn v x hv hx)
      (SourceAssignment.rvParameters sα v hv) (SourceAssignment.rvVariables sn x hx))

/-- The parser chooses its finite syntax before quantifying over models. -/
theorem qf_source_boolean (φ : LRV.BoundedFormula α n) (hqf : φ.IsQF) (hws : WellSorted sα sn φ) :
    ∃ E : SourceBoolean sα sn, SourceEquivalent sα sn φ E := by
  induction hqf with
  | falsum =>
    refine ⟨.falsum,?_⟩
    intro M sM hM v x hv hx
    rfl
  | of_isAtomic ha =>
    cases ha with
    | equal t u =>
      cases hws with
      | @equal _ _ _ _ σ ht hu =>
        cases σ with
        | rv =>
          obtain ⟨P,hP⟩ := (source_term_representations sα sn t).2 ht
          obtain ⟨Q,hQ⟩ := (source_term_representations sα sn u).2 hu
          refine ⟨.atom (.equality P Q),?_⟩
          intro M sM hM v x hv hx
          exact SourceAssignment.equality_realize sα sn v x hv hx t u P Q hP hQ
        | vf =>
          let t' : LRV.Term (α ⊕ Fin n) := .func Fn.rvMap ![.func Fn.vfAdd ![t,.func Fn.vfNeg ![u] ] ]
          let u' : LRV.Term (α ⊕ Fin n) := .func Fn.rvZero Fin.elim0
          have ht' : TmSort sα sn t'=some .rv := by
            apply tmSort_func sα sn Fn.rvMap
            intro i
            fin_cases i
            apply tmSort_func sα sn Fn.vfAdd
            intro j
            fin_cases j
            · exact ht
            · apply tmSort_func sα sn Fn.vfNeg
              intro k
              fin_cases k
              exact hu
          have hu' : TmSort sα sn u'=some .rv := by
            apply tmSort_func sα sn Fn.rvZero
            intro i
            exact i.elim0
          obtain ⟨P,hP⟩ := (source_term_representations sα sn t').2 ht'
          obtain ⟨Q,hQ⟩ := (source_term_representations sα sn u').2 hu'
          refine ⟨.atom (.equality P Q),?_⟩
          intro M sM hM v x hv hx
          exact (realize_rvEquality sα sn v x hv hx t u ht hu).trans
            (SourceAssignment.equality_realize sα sn v x hv hx t' u' P Q hP hQ)
    | rel R ts =>
      cases hws with
      | rel _ _ _ hts =>
        cases R with
        | memVF =>
          refine ⟨.imp .falsum .falsum,?_⟩
          intro M sM hM v x hv hx
          have ht := CanonicalStructure.term_sort hM sα sn v x hv hx (ts 0) (hts 0)
          have he : ts=![ts 0] := by funext i; fin_cases i; rfl
          rw [he]
          exact (SourceAssignment.rel1_realize (v := v) (x := x) Rel.memVF (ts 0)).trans
            ⟨fun _ h => h,fun _ => ht⟩
        | memRV =>
          refine ⟨.imp .falsum .falsum,?_⟩
          intro M sM hM v x hv hx
          have ht := CanonicalStructure.term_sort hM sα sn v x hv hx (ts 0) (hts 0)
          have he : ts=![ts 0] := by funext i; fin_cases i; rfl
          rw [he]
          exact (SourceAssignment.rel1_realize (v := v) (x := x) Rel.memRV (ts 0)).trans
            ⟨fun _ h => h,fun _ => ht⟩
        | memUnits =>
          obtain ⟨P,hP⟩ := (source_term_representations sα sn (ts 0)).2 (hts 0)
          refine ⟨P.unitsExpression,?_⟩
          intro M sM hM v x hv hx
          have he : ts=![ts 0] := by funext i; fin_cases i; rfl
          rw [he]
          exact SourceAssignment.units_realize sα sn v x hv hx (ts 0) P hP
        | rvLe =>
          obtain ⟨P,hP⟩ := (source_term_representations sα sn (ts 0)).2 (hts 0)
          obtain ⟨Q,hQ⟩ := (source_term_representations sα sn (ts 1)).2 (hts 1)
          refine ⟨.atom (.order P Q),?_⟩
          intro M sM hM v x hv hx
          have he : ts=![ts 0,ts 1] := by funext i; fin_cases i <;> rfl
          rw [he]
          exact SourceAssignment.order_realize sα sn v x hv hx (ts 0) (ts 1) P Q hP hQ
  | @imp φ ψ hφ hψ ihφ ihψ =>
    cases hws with
    | imp _ hwφ hwψ =>
      obtain ⟨E,hE⟩ := ihφ hwφ
      obtain ⟨F,hF⟩ := ihψ hwψ
      refine ⟨.imp E F,?_⟩
      intro M sM hM v x hv hx
      exact imp_congr (hE M v x hv hx) (hF M v x hv hx)

/-- Uniform finite normal-form syntax over exactly the original slots.
The final original-language and explicit-domain compiler is a separate bridge. -/
theorem model_uniform_normal_form (φ : LRV.BoundedFormula α n) (hws : WellSorted sα sn φ) :
    ∃ D : LiteralDNF (VFSlot sα sn) (RVParameterSlot sα) (RVVariableSlot sn),
      ∀ (M : Type) [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] (v : α → M) (x : Fin n → M)
        (hv : ∀ i, sortEval (sα i) (v i)) (hx : ∀ i, sortEval (sn i) (x i)),
      φ.Realize v x ↔ PolarityDNF.holds (RVLiteral.holds (SourceAssignment.vfValues sα sn v x hv hx)
        (SourceAssignment.rvParameters sα v hv) (SourceAssignment.rvVariables sn x hx)) D := by
  obtain ⟨ψ,hqf,hwsψ,heq⟩ := theorem_2_3_quantifier_elimination α sα n sn φ hws
  obtain ⟨E,hE⟩ := qf_source_boolean sα sn ψ hqf hwsψ
  refine ⟨booleanNormalForm E,?_⟩
  intro M sM hM v x hv hx
  exact (heq M hM v x hv hx).trans ((hE M v x hv hx).trans
    (booleanNormalForm_correct (SourceAssignment.vfValues sα sn v x hv hx)
      (SourceAssignment.rvParameters sα v hv) (SourceAssignment.rvVariables sn x hx) E).symm)

end SpecialTransformations.Section3.GuardedRVNormalForm

/- Component: NormalFormTermSorting -/
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3.GuardedRVNormalForm

namespace VFPolynomial
variable {I α : Type} {n : ℕ}
theorem relabeled_sorted (sα : α → SortTag) (sn : Fin n → SortTag)
    (fv : I → α ⊕ Fin n) (hfv : ∀ i, Sum.elim sα sn (fv i)=.vf) (P : VFPolynomial I) :
    TmSort sα sn ((RingSyntax.ofRingTerm P).relabel fv)=some .vf := by
  induction P with
  | var i =>
    change TmSort sα sn (.var (fv i))=some .vf
    have hi := congrArg some (hfv i)
    cases he : fv i with
    | inl j => simpa only [he,TmSort,Sum.elim_inl,Sum.elim_inr] using hi
    | inr j => simpa only [he,TmSort,Sum.elim_inl,Sum.elim_inr] using hi
  | func f ts ih =>
    change TmSort sα sn (.func (RingSyntax.vfFn f) (fun i => (RingSyntax.ofRingTerm (ts i)).relabel fv))=some .vf
    cases f <;> apply tmSort_func <;> intro i <;> first | exact ih i | exact i.elim0
end VFPolynomial

namespace RVExpr
variable {I R V α : Type} {n : ℕ}
theorem toTerm_sorted (sα : α → SortTag) (sn : Fin n → SortTag)
    (fv : I → α ⊕ Fin n) (fr : R → α ⊕ Fin n) (fy : V → α ⊕ Fin n)
    (hfv : ∀ i, Sum.elim sα sn (fv i)=.vf) (hfr : ∀ i, Sum.elim sα sn (fr i)=.rv)
    (hfy : ∀ i, Sum.elim sα sn (fy i)=.rv) (P : RVExpr I R V) :
    TmSort sα sn (P.toTerm fv fr fy)=some .rv := by
  induction P with
  | zero =>
    apply tmSort_func
    intro i
    exact i.elim0
  | one =>
    apply tmSort_func
    intro i
    exact i.elim0
  | vf P =>
    apply tmSort_func
    intro i
    fin_cases i
    exact VFPolynomial.relabeled_sorted sα sn fv hfv P
  | parameter i =>
    change TmSort sα sn (.var (fr i))=some .rv
    have hi := congrArg some (hfr i)
    cases he : fr i with
    | inl j => simpa only [he,TmSort,Sum.elim_inl,Sum.elim_inr] using hi
    | inr j => simpa only [he,TmSort,Sum.elim_inl,Sum.elim_inr] using hi
  | ofVariable i =>
    change TmSort sα sn (.var (fy i))=some .rv
    have hi := congrArg some (hfy i)
    cases he : fy i with
    | inl j => simpa only [he,TmSort,Sum.elim_inl,Sum.elim_inr] using hi
    | inr j => simpa only [he,TmSort,Sum.elim_inl,Sum.elim_inr] using hi
  | mul P Q ihP ihQ =>
    apply tmSort_func
    intro i
    fin_cases i
    · exact ihP
    · exact ihQ
  | inv P ihP =>
    apply tmSort_func
    intro i
    fin_cases i
    exact ihP
  | addK P Q ihP ihQ =>
    apply tmSort_func
    intro i
    fin_cases i
    · exact ihP
    · exact ihQ
  | negK P ihP =>
    apply tmSort_func
    intro i
    fin_cases i
    exact ihP
end RVExpr
end SpecialTransformations.Section3.GuardedRVNormalForm

/- Component: NormalFormFormulaCompilation -/
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open CanonicalRV ValuedModelMap ResidueTranscendentalTransport
namespace SpecialTransformations.Section3.GuardedRVNormalForm

namespace RVLiteral
variable {I R V α : Type} {n : ℕ}
noncomputable def rawFormula (fv : I → α ⊕ Fin n) (fr : R → α ⊕ Fin n) (fy : V → α ⊕ Fin n) :
    RVLiteral I R V → LRV.BoundedFormula α n
  | .equality E pos =>
    let t := (RVExpr.mul E.left.expression E.leftK.expression).toTerm fv fr fy
    let u := (RVExpr.mul E.right.expression E.rightK.expression).toTerm fv fr fy
    let A := t.bdEqual u
    if pos then A else .imp A .falsum
  | .order E pos =>
    let A := BoundedFormula.rel Rel.rvLe ![E.left.expression.toTerm fv fr fy,E.right.expression.toTerm fv fr fy]
    if pos then A else .imp A .falsum

theorem rawFormula_qf (fv : I → α ⊕ Fin n) (fr : R → α ⊕ Fin n) (fy : V → α ⊕ Fin n)
    (L : RVLiteral I R V) : (rawFormula fv fr fy L).IsQF := by
  cases L with
  | equality E pos =>
    cases pos
    · exact (BoundedFormula.IsQF.of_isAtomic (.equal _ _)).imp .falsum
    · exact .of_isAtomic (.equal _ _)
  | order E pos =>
    cases pos
    · exact (BoundedFormula.IsQF.of_isAtomic (.rel _ _)).imp .falsum
    · exact .of_isAtomic (.rel _ _)

theorem rawFormula_sorted (sα : α → SortTag) (sn : Fin n → SortTag)
    (fv : I → α ⊕ Fin n) (fr : R → α ⊕ Fin n) (fy : V → α ⊕ Fin n)
    (hfv : ∀ i, Sum.elim sα sn (fv i)=.vf) (hfr : ∀ i, Sum.elim sα sn (fr i)=.rv)
    (hfy : ∀ i, Sum.elim sα sn (fy i)=.rv) (L : RVLiteral I R V) :
    WellSorted sα sn (rawFormula fv fr fy L) := by
  have hsort := RVExpr.toTerm_sorted sα sn fv fr fy hfv hfr hfy
  cases L with
  | equality E pos =>
    have ha := WellSorted.equal sn (hsort (.mul E.left.expression E.leftK.expression))
      (hsort (.mul E.right.expression E.rightK.expression))
    cases pos
    · exact .imp sn ha (.falsum sn)
    · exact ha
  | order E pos =>
    have ha : WellSorted sα sn (BoundedFormula.rel Rel.rvLe
        ![E.left.expression.toTerm fv fr fy,E.right.expression.toTerm fv fr fy]) := by
      apply WellSorted.rel
      intro i
      fin_cases i
      · exact hsort E.left.expression
      · exact hsort E.right.expression
    cases pos
    · exact .imp sn ha (.falsum sn)
    · exact ha
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
theorem rawFormula_realize (fv : I → α ⊕ Fin n) (fr : R → α ⊕ Fin n) (fy : V → α ⊕ Fin n)
    (v : α → M) (x : Fin n → M) (a : I → VFType (M := M)) (r : R → RVSort M) (y : V → RVSort M)
    (ha : ∀ i, Sum.elim v x (fv i)=(a i).val) (hr : ∀ i, Sum.elim v x (fr i)=(r i).val)
    (hy : ∀ i, Sum.elim v x (fy i)=(y i).val) (L : RVLiteral I R V) :
    (rawFormula fv fr fy L).Realize v x ↔ comparison a r y L := by
  have ht (P : RVExpr I R V) := RVExpr.toTerm_realize fv fr fy (Sum.elim v x) a r y ha hr hy P
  cases L with
  | equality E pos =>
    have he : (((RVExpr.mul E.left.expression E.leftK.expression).toTerm fv fr fy).bdEqual
        ((RVExpr.mul E.right.expression E.rightK.expression).toTerm fv fr fy)).Realize v x ↔
        E.left.rawEval a r y*E.leftK.rawEval a r y=E.right.rawEval a r y*E.rightK.rawEval a r y := by
      change _ = _ ↔ _
      rw [ht,ht]
      simp only [RVExpr.eval,Monomial.expression_eval,KPolynomial.expression_eval]
      exact Subtype.val_inj
    cases pos
    · exact not_congr he
    · exact he
  | order E pos =>
    have he : (BoundedFormula.rel Rel.rvLe
        ![E.left.expression.toTerm fv fr fy,E.right.expression.toTerm fv fr fy]).Realize v x ↔
        iLe (E.left.rawEval a r y).val (E.right.rawEval a r y).val := by
      rw [SourceAssignment.rel2_realize]
      change iLe _ _ ↔ _
      rw [ht,ht,Monomial.expression_eval,Monomial.expression_eval]
    cases pos
    · exact not_congr he
    · exact he

end RVLiteral

namespace LiteralDNF
variable {I R V α : Type} {n : ℕ}
noncomputable def clauseFormula (fv : I → α ⊕ Fin n) (fr : R → α ⊕ Fin n) (fy : V → α ⊕ Fin n) :
    List (RVLiteral I R V) → LRV.BoundedFormula α n
  | [] => ⊤
  | L::Ls => RVLiteral.rawFormula fv fr fy L ⊓ clauseFormula fv fr fy Ls
noncomputable def rawFormula (fv : I → α ⊕ Fin n) (fr : R → α ⊕ Fin n) (fy : V → α ⊕ Fin n) :
    LiteralDNF I R V → LRV.BoundedFormula α n
  | [] => ⊥
  | C::Cs => clauseFormula fv fr fy C ⊔ rawFormula fv fr fy Cs

theorem clauseFormula_qf (fv : I → α ⊕ Fin n) (fr : R → α ⊕ Fin n) (fy : V → α ⊕ Fin n)
    (C : List (RVLiteral I R V)) : (clauseFormula fv fr fy C).IsQF := by
  induction C with
  | nil => exact .top
  | cons L Ls ih =>
    exact (.imp (.imp (RVLiteral.rawFormula_qf fv fr fy L) (.imp ih .falsum)) .falsum)

theorem rawFormula_qf (fv : I → α ⊕ Fin n) (fr : R → α ⊕ Fin n) (fy : V → α ⊕ Fin n)
    (D : LiteralDNF I R V) : (rawFormula fv fr fy D).IsQF := by
  induction D with
  | nil => exact .falsum
  | cons C Cs ih => exact (.imp (.imp (clauseFormula_qf fv fr fy C) .falsum) ih)
theorem clauseFormula_sorted (sα : α → SortTag) (sn : Fin n → SortTag)
    (fv : I → α ⊕ Fin n) (fr : R → α ⊕ Fin n) (fy : V → α ⊕ Fin n)
    (hfv : ∀ i, Sum.elim sα sn (fv i)=.vf) (hfr : ∀ i, Sum.elim sα sn (fr i)=.rv)
    (hfy : ∀ i, Sum.elim sα sn (fy i)=.rv) (C : List (RVLiteral I R V)) :
    WellSorted sα sn (clauseFormula fv fr fy C) := by
  induction C with
  | nil => exact wellSorted_top sα sn
  | cons L Ls ih => exact wellSorted_inf sα sn (RVLiteral.rawFormula_sorted sα sn fv fr fy hfv hfr hfy L) ih

theorem rawFormula_sorted (sα : α → SortTag) (sn : Fin n → SortTag)
    (fv : I → α ⊕ Fin n) (fr : R → α ⊕ Fin n) (fy : V → α ⊕ Fin n)
    (hfv : ∀ i, Sum.elim sα sn (fv i)=.vf) (hfr : ∀ i, Sum.elim sα sn (fr i)=.rv)
    (hfy : ∀ i, Sum.elim sα sn (fy i)=.rv) (D : LiteralDNF I R V) :
    WellSorted sα sn (rawFormula fv fr fy D) := by
  induction D with
  | nil => exact .falsum sn
  | cons C Cs ih =>
    exact .imp sn (.imp sn (clauseFormula_sorted sα sn fv fr fy hfv hfr hfy C) (.falsum sn)) ih

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
theorem clauseFormula_realize (fv : I → α ⊕ Fin n) (fr : R → α ⊕ Fin n) (fy : V → α ⊕ Fin n)
    (v : α → M) (x : Fin n → M) (a : I → VFType (M := M)) (r : R → RVSort M) (y : V → RVSort M)
    (ha : ∀ i, Sum.elim v x (fv i)=(a i).val) (hr : ∀ i, Sum.elim v x (fr i)=(r i).val)
    (hy : ∀ i, Sum.elim v x (fy i)=(y i).val) (C : List (RVLiteral I R V)) :
    (clauseFormula fv fr fy C).Realize v x ↔ ∀ L ∈ C, RVLiteral.comparison a r y L := by
  induction C with
  | nil => simp [clauseFormula]
  | cons L Ls ih =>
    simp only [clauseFormula,BoundedFormula.realize_inf,
      RVLiteral.rawFormula_realize fv fr fy v x a r y ha hr hy,ih]
    simp

theorem rawFormula_realize (fv : I → α ⊕ Fin n) (fr : R → α ⊕ Fin n) (fy : V → α ⊕ Fin n)
    (v : α → M) (x : Fin n → M) (a : I → VFType (M := M)) (r : R → RVSort M) (y : V → RVSort M)
    (ha : ∀ i, Sum.elim v x (fv i)=(a i).val) (hr : ∀ i, Sum.elim v x (fr i)=(r i).val)
    (hy : ∀ i, Sum.elim v x (fy i)=(y i).val) (D : LiteralDNF I R V) :
    (rawFormula fv fr fy D).Realize v x ↔ PolarityDNF.holds (RVLiteral.comparison a r y) D := by
  induction D with
  | nil => simp [rawFormula,PolarityDNF.holds]
  | cons C Cs ih =>
    simp only [rawFormula,BoundedFormula.realize_sup,clauseFormula_realize fv fr fy v x a r y ha hr hy,ih,
      PolarityDNF.holds,List.mem_cons]
    aesop

end LiteralDNF
end SpecialTransformations.Section3.GuardedRVNormalForm

/- Component: NormalFormPolynomialBridge -/
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.GuardedRVNormalForm.VFPolynomial
variable {I : Type}

/-- The ring-term syntax used for VF factors is an actual multivariate
polynomial, with exactly the original VF slots as its variables. -/
noncomputable def polynomial : VFPolynomial I → MvPolynomial I ℤ
  | .var i => MvPolynomial.X i
  | .func .zero _ => 0
  | .func .one _ => 1
  | .func .add ts => polynomial (ts 0)+polynomial (ts 1)
  | .func .mul ts => polynomial (ts 0)*polynomial (ts 1)
  | .func .neg ts => -polynomial (ts 0)

attribute [local instance] FirstOrder.Ring.compatibleRingOfRing
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
theorem polynomial_realize (P : VFPolynomial I) (a : I → VFType (M := M)) :
    MvPolynomial.eval₂ (Int.castRingHom (VFType (M := M))) a P.polynomial=P.realize a := by
  induction P with
  | var i => simp only [polynomial,MvPolynomial.eval₂_X]; rfl
  | func f ts ih =>
    cases f with
    | zero => simp only [polynomial,MvPolynomial.eval₂_zero]; rfl
    | one => simp only [polynomial,MvPolynomial.eval₂_one]; rfl
    | add => simp only [polynomial,MvPolynomial.eval₂_add,ih]; rfl
    | mul => simp only [polynomial,MvPolynomial.eval₂_mul,ih]; rfl
    | neg => simp only [polynomial,MvPolynomial.eval₂_neg,ih]; rfl

end SpecialTransformations.Section3.GuardedRVNormalForm.VFPolynomial

/- Component: GuardedRationalNormalForm -/
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open CanonicalRV ValuedModelMap ResidueTranscendentalTransport
namespace SpecialTransformations.Section3.GuardedRVNormalForm

variable {α : Type} {n : ℕ} (sα : α → SortTag) (sn : Fin n → SortTag)
abbrev SourceDNF := LiteralDNF (VFSlot sα sn) (RVParameterSlot sα) (RVVariableSlot sn)

noncomputable def sourceFormula (D : SourceDNF sα sn) : LRV.BoundedFormula α n :=
  LiteralDNF.rawFormula (vfSlotMap sα sn) (rvParameterMap (n := n) sα) (rvVariableMap (α := α) sn) D

theorem sourceFormula_qf (D : SourceDNF sα sn) : (sourceFormula sα sn D).IsQF :=
  LiteralDNF.rawFormula_qf _ _ _ D

theorem sourceFormula_sorted (D : SourceDNF sα sn) : WellSorted sα sn (sourceFormula sα sn D) :=
  LiteralDNF.rawFormula_sorted sα sn _ _ _ (fun i => i.property) (fun i => i.property) (fun i => i.property) D

theorem sourceFormula_realize {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
    (v : α → M) (x : Fin n → M) (hv : ∀ i, sortEval (sα i) (v i)) (hx : ∀ i, sortEval (sn i) (x i))
    (D : SourceDNF sα sn) :
    (sourceFormula sα sn D).Realize v x ↔
      PolarityDNF.holds (RVLiteral.comparison (SourceAssignment.vfValues sα sn v x hv hx)
        (SourceAssignment.rvParameters sα v hv) (SourceAssignment.rvVariables sn x hx)) D :=
  LiteralDNF.rawFormula_realize _ _ _ v x _ _ _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) D

/-- Uniformity is outside the model quantifier. Every true raw clause has
explicit guard literals establishing every rational pole and residue-sum
domain. No new VF or RV parameter slot is introduced. -/
theorem model_uniform_raw_normal_form (φ : LRV.BoundedFormula α n) (hws : WellSorted sα sn φ) :
    ∃ D : SourceDNF sα sn,
      ∀ (M : Type) [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] (v : α → M) (x : Fin n → M)
        (hv : ∀ i, sortEval (sα i) (v i)) (hx : ∀ i, sortEval (sn i) (x i)),
      (φ.Realize v x ↔ PolarityDNF.holds (RVLiteral.comparison (SourceAssignment.vfValues sα sn v x hv hx)
        (SourceAssignment.rvParameters sα v hv) (SourceAssignment.rvVariables sn x hx)) D) ∧
      LiteralDNF.Certified (SourceAssignment.vfValues sα sn v x hv hx)
        (SourceAssignment.rvParameters sα v hv) (SourceAssignment.rvVariables sn x hx) D := by
  obtain ⟨ψ,hqf,hwsψ,heq⟩ := theorem_2_3_quantifier_elimination α sα n sn φ hws
  obtain ⟨E,hE⟩ := qf_source_boolean sα sn ψ hqf hwsψ
  refine ⟨booleanNormalForm E,?_⟩
  intro M sM hM v x hv hx
  exact ⟨(heq M hM v x hv hx).trans ((hE M v x hv hx).trans
      (booleanNormalForm_raw_correct (SourceAssignment.vfValues sα sn v x hv hx)
        (SourceAssignment.rvParameters sα v hv) (SourceAssignment.rvVariables sn x hx) E).symm),
    booleanNormalForm_certified (SourceAssignment.vfValues sα sn v x hv hx)
      (SourceAssignment.rvParameters sα v hv) (SourceAssignment.rvVariables sn x hx) E⟩

/-- The author-approved rational, explicitly guarded version of Definition2.4.
`sourceFormula` is literally a finite disjunction of finite conjunctions of
raw RV comparisons. Equality payloads have two flat K factors of arity>=2;
order payloads have no K factors. Their left coefficient is one. -/
theorem definition_2_4_guarded_rational_normal_form (φ : LRV.BoundedFormula α n) (hws : WellSorted sα sn φ) :
    ∃ D : SourceDNF sα sn,
      (sourceFormula sα sn D).IsQF ∧ WellSorted sα sn (sourceFormula sα sn D) ∧
      ∀ (M : Type) [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] (v : α → M) (x : Fin n → M)
        (hv : ∀ i, sortEval (sα i) (v i)) (hx : ∀ i, sortEval (sn i) (x i)),
      (φ.Realize v x ↔ (sourceFormula sα sn D).Realize v x) ∧
      LiteralDNF.Certified (SourceAssignment.vfValues sα sn v x hv hx)
        (SourceAssignment.rvParameters sα v hv) (SourceAssignment.rvVariables sn x hx) D := by
  obtain ⟨D,hD⟩ := model_uniform_raw_normal_form sα sn φ hws
  refine ⟨D,sourceFormula_qf sα sn D,sourceFormula_sorted sα sn D,?_⟩
  intro M sM hM v x hv hx
  have hd := hD M v x hv hx
  exact ⟨hd.1.trans (sourceFormula_realize sα sn v x hv hx D).symm,hd.2⟩

end SpecialTransformations.Section3.GuardedRVNormalForm

namespace SpecialTransformations.Section3
open GuardedRVNormalForm
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem DefinableOver.guarded_rational_normal_form {A : Set M} {n : ℕ}
    {sn : Fin n → SortTag} {s : Set (Fin n → M)} (hs : DefinableOver A sn s) :
    ∃ p : Parameters A, ∃ D : SourceDNF p.sorts sn,
      (sourceFormula p.sorts sn D).IsQF ∧ WellSorted p.sorts sn (sourceFormula p.sorts sn D) ∧
      s={x | (∀ i, sortEval (sn i) (x i)) ∧ (sourceFormula p.sorts sn D).Realize p.values x} := by
  obtain ⟨p,φ,hφ,rfl⟩ := hs
  obtain ⟨D,hqf,hws,hD⟩ := definition_2_4_guarded_rational_normal_form p.sorts sn φ hφ
  refine ⟨p,D,hqf,hws,?_⟩
  ext x
  constructor
  · rintro ⟨hx,hφx⟩
    exact ⟨hx,((hD M p.values x p.sorted hx).1).mp hφx⟩
  · rintro ⟨hx,hψx⟩
    exact ⟨hx,((hD M p.values x p.sorted hx).1).mpr hψx⟩

end SpecialTransformations.Section3
