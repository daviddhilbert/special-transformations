import JohnsonMain
import ValuedFieldExtension

/-!
The checked Johnson theorem applies to the actual valued-field reduct used by
the RV proof. The two ordinary valued-field languages differ only in their
symbol names. This module proves the symbol correspondence, its realization
and saturation transfers, and the model axioms for arbitrary nontrivially
valued algebraically closed fields. No valued-field QE result is assumed.
-/

open Classical FirstOrder FirstOrder.Language FirstOrder.Ring
open ValuedReduct ValuedFieldExtension

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

namespace JohnsonValuedBridge

/-- Rename Johnson's ring and comparison symbols to the reduct's symbols. -/
def johnsonToValued : Language.val →ᴸ LVal where
  onFunction := fun {_} f => match f with
    | .add => .add
    | .mul => .mul
    | .neg => .neg
    | .zero => .zero
    | .one => .one
  onRelation := fun {_} r => match r with
    | .le => .le

/-- The inverse renaming; neither language has any additional symbols. -/
def valuedToJohnson : LVal →ᴸ Language.val where
  onFunction := fun {_} f => match f with
    | .zero => .zero
    | .one => .one
    | .add => .add
    | .neg => .neg
    | .mul => .mul
  onRelation := fun {_} r => match r with
    | .le => .le

theorem function_roundtrip_johnson {n : ℕ} (f : Language.val.Functions n) :
    valuedToJohnson.onFunction (johnsonToValued.onFunction f) = f := by
  cases f <;> rfl

theorem function_roundtrip_valued {n : ℕ} (f : LVal.Functions n) :
    johnsonToValued.onFunction (valuedToJohnson.onFunction f) = f := by
  cases f <;> rfl

theorem relation_roundtrip_johnson {n : ℕ} (r : Language.val.Relations n) :
    valuedToJohnson.onRelation (johnsonToValued.onRelation r) = r := by
  cases r <;> rfl

theorem relation_roundtrip_valued {n : ℕ} (r : LVal.Relations n) :
    johnsonToValued.onRelation (valuedToJohnson.onRelation r) = r := by
  cases r <;> rfl

section Interpretation

variable {E Γ : Type} [Field E] [LinearOrderedCommGroupWithZero Γ]
  [LVal.Structure E] (v : Valuation E Γ) (hv : InterpretsValuation v)

include hv

/-- The given reduct structure and the canonical Johnson structure interpret
the renaming identically, including the direction of the comparison relation. -/
theorem interprets_expansion :
    letI : Language.val.Structure E := FirstOrder.valStructure v
    johnsonToValued.IsExpansionOn E := by
  letI : Language.val.Structure E := FirstOrder.valStructure v
  refine { map_onFunction := ?_, map_onRelation := ?_ }
  · intro n f xs
    cases f <;> exact hv.functions _ xs
  · intro n r xs
    cases r
    exact propext (hv.comparison xs)

theorem realize_rename {α : Type} (φ : Language.val.Formula α) (a : α → E) :
    Formula.Realize (johnsonToValued.onBoundedFormula φ) a ↔
      @Formula.Realize Language.val E (FirstOrder.valStructure v) α φ a := by
  letI : Language.val.Structure E := FirstOrder.valStructure v
  letI : johnsonToValued.IsExpansionOn E := interprets_expansion v hv
  simp only [Formula.Realize, LHom.realize_onBoundedFormula]

/-- Saturation is invariant under this exact renaming of the language. This
direction is the one needed to apply Johnson's theorem to the VF reduct. -/
theorem satAt_johnson {κ : Cardinal} (hSat : MarkerBridge.SatAt LVal E κ) :
    @MarkerBridge.SatAt Language.val E (FirstOrder.valStructure v) κ := by
  letI : Language.val.Structure E := FirstOrder.valStructure v
  intro A g hA p hp
  let q : MarkerBridge.TypeOver LVal A := johnsonToValued.onBoundedFormula '' p
  have hq : MarkerBridge.FinSat g q := by
    intro q₀ hfinite hsub
    let preimage : LVal.Formula (A ⊕ Unit) → Language.val.Formula (A ⊕ Unit) :=
      fun ψ => if hψ : ψ ∈ q then Classical.choose hψ else .falsum
    have hpre (ψ : LVal.Formula (A ⊕ Unit)) (hψ : ψ ∈ q) :
        preimage ψ ∈ p ∧ johnsonToValued.onBoundedFormula (preimage ψ) = ψ := by
      simp only [preimage, dif_pos hψ]
      exact Classical.choose_spec hψ
    let p₀ : MarkerBridge.TypeOver Language.val A := preimage '' q₀
    have hpfinite : p₀.Finite := hfinite.image preimage
    have hpsub : p₀ ⊆ p := by
      rintro φ ⟨ψ, hψ, rfl⟩
      exact (hpre ψ (hsub hψ)).1
    obtain ⟨b, hb⟩ := hp p₀ hpfinite hpsub
    refine ⟨b, ?_⟩
    intro ψ hψ
    have hφ := hb (preimage ψ) ⟨ψ, hψ, rfl⟩
    have ht := (realize_rename v hv (preimage ψ) (Sum.elim g (fun _ => b))).mpr hφ
    rw [(hpre ψ (hsub hψ)).2] at ht
    exact ht
  obtain ⟨b, hb⟩ := hSat A g hA q hq
  refine ⟨b, ?_⟩
  intro φ hφ
  exact (realize_rename v hv φ (Sum.elim g (fun _ => b))).mp
    (hb _ ⟨φ, hφ, rfl⟩)

end Interpretation

section Models

variable {E Γ : Type} [Field E] [LinearOrderedCommGroupWithZero Γ]

/-- Either a nontrivial value or its inverse gives the required nonzero
element of the maximal ideal. -/
theorem exists_value_lt_one (v : Valuation E Γ)
    (hnt : ∃ x : E, x ≠ 0 ∧ v x ≠ 1) :
    ∃ x : E, x ≠ 0 ∧ v x < 1 := by
  obtain ⟨x, hx0, hx⟩ := hnt
  rcases lt_or_gt_of_ne hx with hlt | hgt
  · exact ⟨x, hx0, hlt⟩
  · refine ⟨x⁻¹, inv_ne_zero hx0, ?_⟩
    rw [Valuation.map_inv]
    exact inv_lt_one_of_one_lt₀ hgt

/-- Every actual algebraically closed nontrivially valued field is a model
of the exact first-order theory used by the checked Johnson theorem. -/
theorem model_ACVF_val [IsAlgClosed E] (v : Valuation E Γ)
    (hnt : ∃ x : E, x ≠ 0 ∧ v x ≠ 1) :
    @Theory.Model Language.val E (FirstOrder.valStructure v) ValPM.ACVF_val := by
  letI : Language.val.Structure E := FirstOrder.valStructure v
  letI : CompatibleRing E := compatibleRingOfRing E
  letI : valRingHom.IsExpansionOn E :=
    { map_onFunction := by intro n f xs; cases f <;> rfl
      map_onRelation := by intro n r xs; exact isEmptyElim r }
  refine ⟨fun φ hφ => ?_⟩
  change φ ∈ ValPM.valField ∪
    ValPM.genericMonicPolyHasRoot '' {n : ℕ | 0 < n} ∪ {ValPM.axNontrivial} at hφ
  rcases hφ with (hbase | hroot) | hnontrivial
  · exact (ValPM.valStructure_model v).realize_of_mem φ hbase
  · obtain ⟨n, hn, rfl⟩ := hroot
    have hr : E ⊨ Field.genericMonicPolyHasRoot n := by
      rw [Field.realize_genericMonicPolyHasRoot]
      rintro ⟨p, _, hdeg⟩
      exact IsAlgClosed.exists_root p
        (ne_of_gt (Polynomial.natDegree_pos_iff_degree_pos.1 (by rw [hdeg]; exact hn)))
    simpa only [ValPM.genericMonicPolyHasRoot, Sentence.Realize, Formula.Realize,
      LHom.realize_onBoundedFormula] using hr
  · have hφeq : φ = ValPM.axNontrivial := hnontrivial
    rw [hφeq]
    apply ValPM.axNontrivial_realize.mpr
    obtain ⟨x, hx0, hx⟩ := exists_value_lt_one v hnt
    refine ⟨x, hx0, ?_⟩
    change ¬ v 1 ≤ v x
    rw [map_one]
    exact not_le.mpr hx

end Models

/-- Johnson's checked bounded-formula QE theorem in the semantic interface
used by the generic saturated-embedding extension proof. -/
theorem fullQE_ACVF_val : MarkerBridge.FullQE ValPM.ACVF_val := by
  intro α n φ
  obtain ⟨ψ, hqf, heq⟩ := hasQEb_ACVF_val α n φ
  refine ⟨ψ, hqf, ?_⟩
  intro E sE hE a xs
  letI := sE
  letI := hE
  letI : Nonempty E :=
    ⟨Structure.funMap (L := Language.val) ValFunc.zero (fun i => i.elim0)⟩
  have h := heq (Theory.ModelType.of (T := ValPM.ACVF_val) E) a xs
  simpa only [BoundedFormula.realize_iff] using h

end JohnsonValuedBridge

#print axioms JohnsonValuedBridge.satAt_johnson
#print axioms JohnsonValuedBridge.model_ACVF_val
#print axioms JohnsonValuedBridge.fullQE_ACVF_val
