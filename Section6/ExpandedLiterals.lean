import Section6.RVSubstructure
import Section6.CommonEnvelopeComparison

/-! The earlier equality-at-the-difference identity in an actual RV-only
expansion of a native substructure. RV quantifiers and RV parameters
stay in that substructure. No field algebra or polynomial normal form
is reconstructed here. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 100000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.Milestone0.LRV FirstOrder.Language.sum
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer

namespace SpecialTransformations.Section6.ExpandedLiterals
open RVTermSupport RVAbstraction

variable {E : _root_.FirstOrder.Language.{0, 0}} {V R : Type} {n : ℕ}

private theorem realize_func0 {I M : Type} [(Expanded E).Structure M]
    (f : (Expanded E).Functions 0) (v : I → M) :
    (Term.func f Fin.elim0 : (Expanded E).Term I).realize v =
      Structure.funMap f (Fin.elim0 : Fin 0 → M) := by
  change Structure.funMap f _ = _
  congr 1
  exact Subsingleton.elim _ _

private theorem realize_func1 {I M : Type} [(Expanded E).Structure M]
    (f : (Expanded E).Functions 1) (t : (Expanded E).Term I) (v : I → M) :
    (Term.func f ![t]).realize v = Structure.funMap f ![t.realize v] := by
  change Structure.funMap f _ = _
  congr 1
  funext i
  fin_cases i
  rfl

private theorem realize_func2 {I M : Type} [(Expanded E).Structure M]
    (f : (Expanded E).Functions 2) (t u : (Expanded E).Term I) (v : I → M) :
    (Term.func f ![t, u]).realize v = Structure.funMap f ![t.realize v, u.realize v] := by
  change Structure.funMap f _ = _
  congr 1
  funext i
  fin_cases i <;> rfl

def rvEquality (t u : (Expanded E).Term ((V ⊕ R) ⊕ Fin n)) :
    (Expanded E).BoundedFormula (V ⊕ R) n :=
  .equal (rvTerm (.func (.inl Fn.vfAdd) ![t, .func (.inl Fn.vfNeg) ![u] ]))
    (.func (.inl Fn.rvZero) Fin.elim0)

theorem rvEquality_fragment (t u : (Expanded E).Term ((V ⊕ R) ⊕ Fin n))
    (ht : termSort sourceSort t = some .vf) (hu : termSort sourceSort u = some .vf) :
    Fragment (rvEquality t u) := by
  apply Fragment.equal
  · apply (termSort_func sourceSort (.inl Fn.rvMap) _).mpr
    refine ⟨?_, rfl⟩
    intro i
    fin_cases i
    apply (termSort_func sourceSort (.inl Fn.vfAdd) _).mpr
    refine ⟨?_, rfl⟩
    intro j
    fin_cases j
    · exact ht
    · apply (termSort_func sourceSort (.inl Fn.vfNeg) _).mpr
      refine ⟨?_, rfl⟩
      intro k
      fin_cases k
      exact hu
  · exact (termSort_func sourceSort (.inl Fn.rvZero) _).mpr ⟨fun i => i.elim0, rfl⟩

variable {C : Type} [LRV.Structure C] [hC : C ⊨ Axioms.ACVF]

private theorem coe_fun0 (X : LRV.Substructure C) (f : Fn 0) :
    (Structure.funMap (L := LRV) f (Fin.elim0 : Fin 0 → X)).val =
      Structure.funMap (L := LRV) f (Fin.elim0 : Fin 0 → C) := by
  change Structure.funMap (L := LRV) f _ = _
  congr 1
  exact Subsingleton.elim _ _

private theorem coe_fun1 (X : LRV.Substructure C) (f : Fn 1) (a : X) :
    (Structure.funMap (L := LRV) f ![a]).val = Structure.funMap (L := LRV) f ![a.val] := by
  change Structure.funMap (L := LRV) f _ = _
  congr 1
  funext i
  fin_cases i
  rfl

private theorem coe_fun2 (X : LRV.Substructure C) (f : Fn 2) (a b : X) :
    (Structure.funMap (L := LRV) f ![a, b]).val = Structure.funMap (L := LRV) f ![a.val, b.val] := by
  change Structure.funMap (L := LRV) f _ = _
  congr 1
  funext i
  fin_cases i <;> rfl

theorem vf_realize_sorted (X : LRV.Substructure C) [E.Structure (SubRV (X : Set C))]
    (t : (Expanded E).Term ((V ⊕ R) ⊕ Fin n))
    (ht : termSort sourceSort t = some .vf)
    (v : V → X) (hv : ∀ i, iVF (v i).val) (r : R → X) (x : Fin n → X) :
    letI := RVSubstructure.extraStructure (E := E) X
    letI := CommonEnvelopeComparison.expandedStructure (E := E) X
    iVF ((t.realize (Sum.elim (Sum.elim v r) x)).val) := by
  letI := RVSubstructure.extraStructure (E := E) X
  letI := CommonEnvelopeComparison.expandedStructure (E := E) X
  rw [← polynomial_realize t ht v r x]
  exact RVSubstructure.vf_term_sort X v hv (polynomial t) (polynomial_sort t ht)

theorem rvEquality_realize (X : LRV.Substructure C) [E.Structure (SubRV (X : Set C))]
    (t u : (Expanded E).Term ((V ⊕ R) ⊕ Fin n))
    (ht : termSort sourceSort t = some .vf) (hu : termSort sourceSort u = some .vf)
    (v : V → X) (hv : ∀ i, iVF (v i).val) (r : R → X) (x : Fin n → X) :
    letI := RVSubstructure.extraStructure (E := E) X
    letI := CommonEnvelopeComparison.expandedStructure (E := E) X
    ((BoundedFormula.equal t u).Realize (Sum.elim v r) x ↔
      (rvEquality t u).Realize (Sum.elim v r) x) := by
  letI := RVSubstructure.extraStructure (E := E) X
  letI := CommonEnvelopeComparison.expandedStructure (E := E) X
  let a := t.realize (Sum.elim (Sum.elim v r) x)
  let b := u.realize (Sum.elim (Sum.elim v r) x)
  let aC : VFType (M := C) := ⟨a.val, vf_realize_sorted X t ht v hv r x⟩
  let bC : VFType (M := C) := ⟨b.val, vf_realize_sorted X u hu v hv r x⟩
  simp only [rvEquality, rvTerm, BoundedFormula.Realize, realize_func0, realize_func1,
    realize_func2, Subtype.ext_iff]
  change a.val = b.val ↔
    (Structure.funMap (L := LRV) Fn.rvMap
      ![Structure.funMap (L := LRV) Fn.vfAdd
        ![a, Structure.funMap (L := LRV) Fn.vfNeg ![b] ] ]).val =
      (Structure.funMap (L := LRV) Fn.rvZero (Fin.elim0 : Fin 0 → X)).val
  simp only [coe_fun0, coe_fun1, coe_fun2]
  change a.val = b.val ↔ iRv (iVFAdd a.val (iVFNeg b.val)) = iRVZero
  have h : aC = bC ↔ iRv (aC - bC).val = iRVZero :=
    ((CanonicalRV.encodedRv_zero_iff (aC - bC)).trans sub_eq_zero).symm
  constructor
  · intro he
    exact h.mp (Subtype.ext he)
  · intro he
    exact congrArg (fun q : VFType (M := C) => q.val) (h.mpr he)

end SpecialTransformations.Section6.ExpandedLiterals
