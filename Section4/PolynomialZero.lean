import Section4.RealPresentations
import Section3.RingSyntax
import Section3.SortedTuples
import Section3.VFDefinableClosure

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3
open scoped BigOperators

noncomputable section

namespace SpecialTransformations.Section4.PolynomialZero

section Expression

variable {R : Type} [CommRing R] {n : ℕ} (p : MvPolynomial (Fin n) R)

def enumeration : Fin p.support.card ≃ p.support := (Finset.equivFin p.support).symm

def expression : FreeCommRing (Fin p.support.card ⊕ Fin n) :=
  ∑ j : Fin p.support.card, FreeCommRing.of (Sum.inl j) *
    ∏ i : Fin n, FreeCommRing.of (Sum.inr i) ^ ((enumeration p j).val i)

theorem expression_eval {T : Type} [CommRing T] (h : R →+* T) (x : Fin n → T) :
    FreeCommRing.lift
      (Sum.elim (fun j => h (p.coeff ((enumeration p j).val))) x) (expression p) =
      p.eval₂ h x := by
  simp only [expression, map_sum, map_mul, map_prod, map_pow, FreeCommRing.lift_of,
    Sum.elim_inl, Sum.elim_inr]
  rw [MvPolynomial.eval₂_eq']
  calc
    _ = ∑ d : p.support, h (p.coeff d.val) * ∏ i : Fin n, x i ^ (d.val i) :=
      Fintype.sum_equiv (enumeration p) _ _ (fun _ => rfl)
    _ = _ := Finset.sum_coe_sort p.support
      (fun d : Fin n →₀ ℕ => h (p.coeff d) * ∏ i : Fin n, x i ^ (d i))

end Expression

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n : ℕ}
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

def zeroSet (E : Subfield (VFType (M := M))) (p : MvPolynomial (Fin n) E) :
    Set (Fin n → M) :=
  {z | ∃ hz : ∀ i, iVF (z i), p.eval₂ E.subtype (fun i => ⟨z i, hz i⟩) = 0}

theorem zeroSet_named_definable (S : Set M) (E : Subfield (VFType (M := M)))
    (hE : ∀ c : E, c.val.val ∈ S) (p : MvPolynomial (Fin n) E) :
    DefinableOver S (fun _ => .vf) (zeroSet E p) := by
  let m := p.support.card
  let e := enumeration p
  let coeff (j : Fin m) : VFType (M := M) := (p.coeff (e j).val).val
  let r : Parameters S := ⟨m, fun j => (coeff j).val, fun _ => .vf,
    fun j => (coeff j).property, fun j => hE (p.coeff (e j).val)⟩
  let q : FreeCommRing (Fin m ⊕ Fin n) := expression p
  let t : LRV.Term (Fin m ⊕ Fin n) := RingSyntax.ofRingTerm (FirstOrder.Ring.termOfFreeCommRing q)
  let z : LRV.Term (Fin m ⊕ Fin n) := .func Fn.vfZero Fin.elim0
  let φ : LRV.BoundedFormula (Fin m) n := .equal t z
  have hw : WellSorted r.sorts (fun _ => .vf) φ := by
    apply WellSorted.equal (s := .vf)
    · exact RingSyntax.sorted _
    · apply tmSort_func
      intro i
      exact i.elim0
  have ht (x : Fin n → VFType (M := M)) :
      t.realize (Sum.elim r.values (vfValues x)) = (p.eval₂ E.subtype x).val := by
    have hv : (fun a => ((Sum.elim coeff x) a).val) = Sum.elim r.values (vfValues x) := by
      funext a
      cases a <;> rfl
    rw [← hv, RingSyntax.realizes, FirstOrder.Ring.realize_termOfFreeCommRing]
    exact congrArg (fun y : VFType (M := M) => y.val) (expression_eval p E.subtype x)
  have hz (x : Fin n → VFType (M := M)) :
      z.realize (Sum.elim r.values (vfValues x)) = (0 : VFType (M := M)).val := by
    change Structure.funMap (L := LRV) Fn.vfZero (fun _ => _) =
      Structure.funMap (L := LRV) Fn.vfZero Fin.elim0
    congr 1
    funext i
    exact i.elim0
  have hφ (x : Fin n → VFType (M := M)) :
      φ.Realize r.values (vfValues x) ↔ p.eval₂ E.subtype x = 0 := by
    change t.realize _ = z.realize _ ↔ _
    rw [ht, hz]
    exact Subtype.val_inj
  refine ⟨r, φ, hw, ?_⟩
  ext a
  constructor
  · rintro ⟨ha, hp⟩
    exact ⟨ha, (hφ (fun i => ⟨a i, ha i⟩)).mpr hp⟩
  · rintro ⟨ha, hp⟩
    exact ⟨ha, (hφ (fun i => ⟨a i, ha i⟩)).mp hp⟩

/-- Coefficients in the actual VF parameter field are already definable
over S. Eliminate their temporary names using the accepted Section 3 API. -/
theorem zeroSet_parameterField_definable (S : Set M)
    (p : MvPolynomial (Fin n) (vfParameterField (M := M) S)) :
    DefinableOver S (fun _ => .vf) (zeroSet (vfParameterField S) p) := by
  let E := vfParameterField (M := M) S
  let B : Set M := {x | ∃ c : E, c.val.val = x}
  have h := zeroSet_named_definable B E (fun c => ⟨c, rfl⟩) p
  apply h.eliminate_sorted_definable_params
  rintro x ⟨c, rfl⟩
  exact ⟨.vf, vfParameterField_le_definableClosureField S c.property⟩

end SpecialTransformations.Section4.PolynomialZero

end
