import RVInverseOperations

/-! Package the positive-grade source as an RV reduct with its own addition and
negation functions. Both inclusion and coefficient cubing preserve the earlier
inverse-free RV signature: 0, 1, multiplication, residue addition/negation, the unit predicate,
and the value preorder. The source is not closed under the now-restored named
RV inverse. This remains an algebraic reduct, not an ACVF model. -/

namespace RVInverseObstruction.Reduct

noncomputable section
open Classical

theorem includeSource_injective : Function.Injective includeSource :=
  WithZero.map'_injective Subtype.val_injective

@[simp] theorem cubeRV_eq_zero (x : RV) : cubeRV x = 0 ↔ x = 0 := by
  constructor
  · intro h
    apply WithZero.map'_injective cube_injective
    simpa using h
  · rintro rfl
    exact map_zero _

def units (x : RV) : Prop := x ≠ 0 ∧ inK x
def sourceUnits (x : Source) : Prop := units (includeSource x)
def sourceLe (x y : Source) : Prop := grade (includeSource x) ≤ grade (includeSource y)

theorem units_preserved (x : Source) : sourceUnits x ↔ units (embed x) := by
  rw [embed_eq]
  simp only [sourceUnits, units, ne_eq, cubeRV_eq_zero, cubeRV_inK]

theorem source_kAdd_closed (x y : Source) :
    ∃ z : Source, includeSource z = kAdd (includeSource x) (includeSource y) := by
  by_cases hx : inK (includeSource x)
  · by_cases hy : inK (includeSource y)
    · rcases source_inK_cases x hx with hx | hx <;>
        rcases source_inK_cases y hy with hy | hy <;> rw [hx, hy]
      · exact ⟨0, by simp⟩
      · exact ⟨1, by simp⟩
      · exact ⟨1, by simp⟩
      · exact ⟨0, by simp⟩
    · exact ⟨0, by simp [kAdd, hy]⟩
  · exact ⟨0, by simp [kAdd, hx]⟩

theorem source_kNeg_closed (x : Source) :
    ∃ z : Source, includeSource z = kNeg (includeSource x) := by
  by_cases hx : inK (includeSource x)
  · rcases source_inK_cases x hx with hx | hx
    · exact ⟨0, by simp [hx]⟩
    · have htwo : (2 : F8) = 0 := CharP.cast_eq_zero F8 2
      have hneg : (-1 : F8) = 1 := by linear_combination -htwo
      exact ⟨1, by simp [hx, hneg]⟩
  · exact ⟨0, by simp [kNeg, hx]⟩

def sourceKAdd (x y : Source) : Source := Classical.choose (source_kAdd_closed x y)
def sourceKNeg (x : Source) : Source := Classical.choose (source_kNeg_closed x)

theorem includeSource_kAdd (x y : Source) :
    includeSource (sourceKAdd x y) = kAdd (includeSource x) (includeSource y) :=
  Classical.choose_spec (source_kAdd_closed x y)

theorem includeSource_kNeg (x : Source) :
    includeSource (sourceKNeg x) = kNeg (includeSource x) :=
  Classical.choose_spec (source_kNeg_closed x)

theorem embed_kAdd (x y : Source) : embed (sourceKAdd x y) = kAdd (embed x) (embed y) := by
  rw [embed_eq, includeSource_kAdd, kAdd_preserved]

theorem embed_kNeg (x : Source) : embed (sourceKNeg x) = kNeg (embed x) := by
  rw [embed_eq, includeSource_kNeg, kNeg_preserved]

theorem embed_le (x y : Source) : sourceLe x y ↔ grade (embed x) ≤ grade (embed y) :=
  order_preserved x y

/-- The unit guards used by the well-sorted frozen-language formula. -/
def UnitRatioAdd (t b c : RV) : Prop :=
  ∃ u v : RV, units u ∧ units v ∧ t * u = b ∧ t * v = c ∧ kAdd u 1 = v

theorem units_lift (a : F8) (ha : a ≠ 0) : units (lift a) := by
  refine ⟨?_, inK_lift a⟩
  intro h
  apply ha
  exact lift_injective (h.trans lift_zero.symm)

theorem unitRatioAdd_source (t : RV) (a : F8) (ha : a ≠ 0) (ha1 : a + 1 ≠ 0) :
    UnitRatioAdd t (t * lift a) (t * lift (a + 1)) := by
  refine ⟨lift a, lift (a + 1), units_lift a ha, units_lift (a + 1) ha1,
    rfl, rfl, ?_⟩
  simpa only [lift_one] using kAdd_lift a 1

theorem unitRatioAdd_not_target (t : RV) (ht : t ≠ 0) (a : F8)
    (ha : (a + 1) ^ 3 ≠ a ^ 3 + 1) :
    ¬ UnitRatioAdd (cubeRV t) (cubeRV (t * lift a)) (cubeRV (t * lift (a + 1))) := by
  rintro ⟨u, v, _, _, hu, hv, huv⟩
  exact ratioAdd_not_target t ht a ha ⟨u, v, hu, hv, huv⟩

theorem guarded_separating_source_tuple :
    ∃ t b c : Source,
      UnitRatioAdd (includeSource t) (includeSource b) (includeSource c) ∧
      ¬ UnitRatioAdd (embed t) (embed b) (embed c) := by
  obtain ⟨a, ha⟩ := exists_cube_add_failure
  have ha0 : a ≠ 0 := by intro h; simpa [h] using ha
  have ha1 : a + 1 ≠ 0 := by
    intro h
    have heq : a = -1 := eq_neg_of_add_eq_zero_left h
    norm_num [heq] at ha
  let u : F8ˣ := Units.mk0 a ha0
  let v : F8ˣ := Units.mk0 (a + 1) ha1
  refine ⟨ray 1, ray u, ray v, ?_, ?_⟩
  · rw [include_ray, include_ray, include_ray]
    simpa [u, v] using unitRatioAdd_source uniformizer a ha0 ha1
  · rw [embed_eq, embed_eq, embed_eq, include_ray, include_ray, include_ray]
    simpa [u, v] using unitRatioAdd_not_target uniformizer WithZero.coe_ne_zero a ha

end
end RVInverseObstruction.Reduct

#print axioms RVInverseObstruction.Reduct.source_kAdd_closed
#print axioms RVInverseObstruction.Reduct.source_kNeg_closed
#print axioms RVInverseObstruction.Reduct.units_preserved
#print axioms RVInverseObstruction.Reduct.embed_kAdd
#print axioms RVInverseObstruction.Reduct.embed_kNeg
#print axioms RVInverseObstruction.Reduct.embed_le
#print axioms RVInverseObstruction.Reduct.guarded_separating_source_tuple
