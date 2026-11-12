module

public import Section6.FiniteAbstraction
public import Section6.NativeTermMap

@[expose] public section

/-! The finite abstraction coefficients are the values of the actual
native term map. The chosen native terms depend only on syntax. Unused
ill-sorted token names are sent to the existing zero term; genuine FV
occurrences are unchanged by polynomialOrZero.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5

namespace SpecialTransformations.Section6.NativeOccurrence
open RVTermSupport RVAbstraction

variable {E : Language} {V R : Type}

def native (φ : (Expanded E).Formula (V ⊕ R)) (i : Fin (FiniteAbstraction.count φ)) :
    LRV.Term V := Classical.choose (NativeTerms.exists_native_vf
      (RVSubstructure.polynomialOrZero (FiniteAbstraction.occurrence φ i))
      (RVSubstructure.polynomialOrZero_sort _))

theorem native_shape (φ : (Expanded E).Formula (V ⊕ R)) (i : Fin (FiniteAbstraction.count φ)) :
    (LHom.sumInl : LRV →ᴸ Expanded E).onTerm (native φ i) =
      RVSubstructure.polynomialOrZero (FiniteAbstraction.occurrence φ i) :=
  (Classical.choose_spec (NativeTerms.exists_native_vf
    (RVSubstructure.polynomialOrZero (FiniteAbstraction.occurrence φ i))
    (RVSubstructure.polynomialOrZero_sort _))).1

theorem native_sorted (φ : (Expanded E).Formula (V ⊕ R)) (i : Fin (FiniteAbstraction.count φ)) :
    NativeTermMap.VFSorted (native φ i) :=
  (Classical.choose_spec (NativeTerms.exists_native_vf
    (RVSubstructure.polynomialOrZero (FiniteAbstraction.occurrence φ i))
    (RVSubstructure.polynomialOrZero_sort _))).2

variable {C : Type} [LRV.Structure C] [C ⊨ Axioms.ACVF] {r n : ℕ}

def fvTuple (X : LRV.Substructure C) (c : Fin r → VF (M := C))
    (hc : ∀ i, (c i).val ∈ X) (x : Fin n → VF (M := C))
    (hx : ∀ i, (x i).val ∈ X) : Fin r ⊕ Fin n → X :=
  Sum.elim (fun i => ⟨(c i).val, hc i⟩) (fun i => ⟨(x i).val, hx i⟩)

theorem fvTuple_sorted (X : LRV.Substructure C) (c : Fin r → VF (M := C))
    (hc : ∀ i, (c i).val ∈ X) (x : Fin n → VF (M := C))
    (hx : ∀ i, (x i).val ∈ X) : ∀ i, iVF (fvTuple X c hc x hx i).val :=
  Sum.rec (fun i => (c i).property) (fun i => (x i).property)

theorem coefficient_native (X : LRV.Substructure C)
    [E.Structure (SubRV (X : Set C))] (c : Fin r → VF (M := C))
    (hc : ∀ i, (c i).val ∈ X) (x : Fin n → VF (M := C)) (hx : ∀ i, (x i).val ∈ X)
    (φ : (Expanded E).Formula ((Fin r ⊕ Fin n) ⊕ R))
    (i : Fin (FiniteAbstraction.count φ)) :
    letI := RVSubstructure.extraStructure (E := E) X
    (RVSubstructure.coefficient X (fvTuple X c hc x hx) (fvTuple_sorted X c hc x hx)
      (FiniteAbstraction.occurrence φ i)).val =
      rv (NativeTermMap.vfValue c (native φ i) (native_sorted φ i) x) := by
  letI := RVSubstructure.extraStructure (E := E) X
  apply Subtype.ext
  change iRv ((RVSubstructure.polynomialOrZero (FiniteAbstraction.occurrence φ i)).realize
      (fvTuple X c hc x hx)).val = _
  rw [← native_shape φ i, NativeTerms.realize_native]
  apply congrArg iRv
  have hargs : (Substructure.subtype X) ∘ fvTuple X c hc x hx =
      Sum.elim (fun i => (c i).val) (fun i => (x i).val) := by
    funext j
    cases j <;> rfl
  have hh := HomClass.realize_term (Substructure.subtype X)
    (t := native φ i) (v := fvTuple X c hc x hx)
  rw [hargs] at hh
  simpa only [NativeTermMap.vfValue, Substructure.coe_subtype] using hh.symm

end SpecialTransformations.Section6.NativeOccurrence

namespace SpecialTransformations.Section6

def vfAssignment {C : Type} [LRV.Structure C] [C ⊨ Axioms.ACVF] {S : Set C} {n : ℕ}
    (X : LRV.Substructure C) (a : PresentedSet.univ (pointSpace (M := C) n 0) S)
    (ha : PointIn (X : Set C) a.val) : Fin n → X :=
  fun i => ⟨(a.val.1 i).val, ha (.inl i)⟩

end SpecialTransformations.Section6
