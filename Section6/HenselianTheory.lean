import Section6.RVTermSupport

/-! The henselian theory in the published native language. The base keeps
the field, RV group, residue-field and valuation-link axioms, but includes
neither algebraic closedness nor the ACVF divisibility scheme. The new
scheme is the ordinary simple-root form of Hensel's lemma on the valuation
ring. The comparison predicates below use the paper's order; the actual
Mathlib valuation inequalities are reversed.

This file specifies the theory. Identification of its models with ordinary
henselian valued fields is a separate standard valued-field input, not an
elimination theorem and not certified merely by these definitions.
-/

noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Section6.HenselianTheory

def polynomialTerm {n m : ℕ} (c : Fin (n + 1) → Tm m) (x : Tm m) : Tm m :=
  ((List.finRange (n + 1)).map (fun i => tVFMul (c i) (tVFPow x i.val))).foldr tVFAdd tVFZero

def derivativeTerm {n m : ℕ} (c : Fin (n + 1) → Tm m) (x : Tm m) : Tm m :=
  ((List.finRange (n + 1)).map (fun i =>
    tVFMul (tVFMul (tVFNumeral i.val) (c i)) (tVFPow x (i.val - 1)))).foldr tVFAdd tVFZero

/-- v(x) ≤ 1 in Mathlib's multiplicative convention. -/
def integral {m : ℕ} (x : Tm m) : Bf m := pLe tRVOne (tRv x)

/-- v(x) < 1, including x=0, in Mathlib's multiplicative convention. -/
def inMaximalIdeal {m : ℕ} (x : Tm m) : Bf m := pGtOne (tRv x)

def valuationOne {m : ℕ} (x : Tm m) : Bf m :=
  pLe tRVOne (tRv x) ⊓ pLe (tRv x) tRVOne

def henselScheme (n : ℕ) : LRV.Sentence :=
  let c : Fin (n + 1) → Tm (n + 2) := fun i => .var (.inr i.castSucc)
  let a : Tm (n + 2) := .var (.inr (Fin.last (n + 1)))
  let ci : Bf (n + 2) :=
    ((List.finRange (n + 1)).map (fun i => integral (c i))).foldr (· ⊓ ·) ⊤
  let c' : Fin (n + 1) → Tm (n + 3) := fun i => .var (.inr i.castSucc.castSucc)
  let a' : Tm (n + 3) := .var (.inr (Fin.last (n + 1)).castSucc)
  let y : Tm (n + 3) := .var (.inr (Fin.last (n + 2)))
  allSorted (fun _ : Fin (n + 2) => .vf)
    ((ci ⊓ integral a ⊓ inMaximalIdeal (polynomialTerm c a) ⊓
      valuationOne (derivativeTerm c a)) ⟹
      exSorted .vf (integral y ⊓ pEq (polynomialTerm c' y) tVFZero ⊓
        inMaximalIdeal (tVFAdd y (tVFNeg a'))))

def rvGroupBase : LRV.Theory :=
  Axioms.ofList [Axioms.rvOneMem, Axioms.rvMulMem, Axioms.rvMulAssoc, Axioms.rvMulComm,
    Axioms.rvMulOne, Axioms.rvMulInv, Axioms.rvMulZeroK, Axioms.rvMulInfty]

def valuedField : LRV.Theory :=
  Axioms.sortAxioms ∪ Axioms.vfField ∪ rvGroupBase ∪ Axioms.kField ∪
    Axioms.preorderRV ∪ Axioms.rvAxioms ∪ Axioms.repairRV

def hen : LRV.Theory := valuedField ∪ Set.range henselScheme

def hen00 : LRV.Theory :=
  hen ∪ {σ | ∃ k, σ = Axioms.charZeroVF k} ∪
    {σ | ∃ p, p.Prime ∧ σ = Axioms.residueCharZero p}

def sortZero {n : ℕ} : SortTag → Tm n
  | .vf => tVFZero
  | .rv => tRVZero

/-- Fix only off-sort native evaluations, as in the shared canonical
normalization. This is a choice of tagged presentation, not an additional
valued-field axiom or a new language symbol. -/
def nativeFunctionJunk {n : ℕ} (f : Fn n) : LRV.Sentence :=
  ((sortedHyps (Fn.argSort f)).not ⟹ BoundedFormula.equal
    (.func f (fun i => .var (.inr i))) (sortZero (Fn.resSort f))).alls

def nativeRelationSort {n : ℕ} (r : Rel n) : LRV.Sentence :=
  (BoundedFormula.rel r (fun i => .var (.inr i)) ⟹ sortedHyps (Rel.argSort r)).alls

def canonicalNative : LRV.Theory :=
  {σ | ∃ n, ∃ f : Fn n, σ = nativeFunctionJunk f} ∪
    {σ | ∃ n, ∃ r : Rel n, σ = nativeRelationSort r}

def canonicalHen00 : LRV.Theory := hen00 ∪ canonicalNative

def rvArguments (E : Language) (n : ℕ) : (RVTermSupport.Expanded E).BoundedFormula Empty n :=
  ((List.finRange n).map (fun i => BoundedFormula.rel (L := RVTermSupport.Expanded E) (.inl Rel.memRV)
    ![Term.var (.inr i)])).foldr (· ⊓ ·) ⊤

/-- New functions are genuinely RV-sorted, including nullary symbols. -/
def extraFunctionSort (E : Language) {n : ℕ} (f : E.Functions n) :
    (RVTermSupport.Expanded E).Sentence :=
  (rvArguments E n ⟹ BoundedFormula.rel (L := RVTermSupport.Expanded E) (.inl Rel.memRV)
    ![Term.func (.inr f) (fun i => .var (.inr i))]).alls

/-- Canonical off-sort totalization of an RV function in the tagged
encoding. It has no effect on formulas of the sorted language. -/
def extraFunctionJunk (E : Language) {n : ℕ} (f : E.Functions n) :
    (RVTermSupport.Expanded E).Sentence :=
  ((rvArguments E n).not ⟹ BoundedFormula.equal
    (.func (.inr f) (fun i => .var (.inr i))) (.func (.inl Fn.rvZero) Fin.elim0)).alls

def extraRelationSort (E : Language) {n : ℕ} (r : E.Relations n) :
    (RVTermSupport.Expanded E).Sentence :=
  (BoundedFormula.rel (L := RVTermSupport.Expanded E) (.inr r)
    (fun i => .var (.inr i)) ⟹ rvArguments E n).alls

def extraSortAxioms (E : Language) : (RVTermSupport.Expanded E).Theory :=
  {σ | ∃ n, ∃ f : E.Functions n, σ = extraFunctionSort E f} ∪
    {σ | ∃ n, ∃ f : E.Functions n, σ = extraFunctionJunk E f} ∪
    {σ | ∃ n, ∃ r : E.Relations n, σ = extraRelationSort E r}

def expanded (E : Language) : (RVTermSupport.Expanded E).Theory :=
  (LHom.sumInl : LRV →ᴸ RVTermSupport.Expanded E).onTheory canonicalHen00 ∪ extraSortAxioms E

def namedNativeInclusion {C : Type} [LRV.Structure C]
    (E : Language) (S : LRV.Substructure C) :
    LRV[[(S : Set C)]] →ᴸ (RVTermSupport.Expanded E)[[(S : Set C)]] :=
  (LHom.sumInl : LRV →ᴸ RVTermSupport.Expanded E).sumMap (LHom.id _)

def named {C : Type} [LRV.Structure C] (E : Language) (S : LRV.Substructure C) :
    (RVTermSupport.Expanded E)[[(S : Set C)]].Theory :=
  ((RVTermSupport.Expanded E).lhomWithConstants (S : Set C)).onTheory (expanded E) ∪
    (namedNativeInclusion E S).onTheory (SubstructureTheory.atomicDiagram S)

end SpecialTransformations.Section6.HenselianTheory
