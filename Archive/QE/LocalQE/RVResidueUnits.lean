import RVValueMap

/-! Residue-unit exact sequence extracted from QE/RV_henselian.lean at fa3867c. -/
namespace RVCalc
variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]
section ResidueUnits

variable (v : Valuation K Γ₀)

/-- The value `v` and the valuation of the valuation ring agree on the ring itself. -/
theorem valuationSubring_valuation_lt_one_iff (a : ↥(v.valuationSubring)) :
    v.valuationSubring.valuation a < 1 ↔ v (a : K) < 1 := by
  have h1 : v.valuationSubring.valuation a < 1 ↔ ¬ IsUnit a := by
    constructor
    · intro h hu
      rw [((v.valuationSubring).valuation_eq_one_iff a).1 hu] at h
      exact lt_irrefl _ h
    · intro h
      rcases lt_or_eq_of_le ((v.valuationSubring).valuation_le_one a) with h' | h'
      · exact h'
      · exact absurd (((v.valuationSubring).valuation_eq_one_iff a).2 h') h
  rw [h1]
  exact (IsLocalRing.mem_maximalIdeal (x := a)).symm.trans
    (Valuation.mem_maximalIdeal_iff (K := K) v)

/-- The bridge for an element of the field that lies in the valuation ring. -/
theorem valuation_lt_one_iff {a : K} (ha : a ∈ v.valuationSubring) :
    v.valuationSubring.valuation a < 1 ↔ v a < 1 :=
  valuationSubring_valuation_lt_one_iff v ⟨a, ha⟩

/-- On the units of the valuation ring, the principal units of `v` are the principal units of
the valuation ring: this identifies `RV× = Kˣ/(1+𝔪)` on the two sides. -/
theorem mem_principalUnits_iff (x : v.valuationSubring.unitGroup) :
    (x : Kˣ) ∈ principalUnits v ↔
      x ∈ v.valuationSubring.principalUnitGroup.comap v.valuationSubring.unitGroup.subtype := by
  have hmem : (((x : Kˣ)) : K) - 1 ∈ v.valuationSubring := by
    rw [Valuation.mem_valuationSubring_iff, sub_eq_add_neg]
    refine Valuation.map_add_le v ?_ ?_
    · rw [show v (((x : Kˣ)) : K) = 1 from
        (Valuation.mem_unitGroup_iff (v := v) (x := (x : Kˣ))).1 x.2]
    · rw [Valuation.map_neg v, Valuation.map_one]
  rw [Subgroup.mem_comap, v.valuationSubring.mem_principalUnitGroup_iff, mem_principalUnits]
  simp only [Subgroup.coe_subtype]
  exact (valuation_lt_one_iff v hmem).symm


/-- The units of the valuation ring mapped into `RV×`. -/
noncomputable def unitGroupToRV (v : Valuation K Γ₀) : v.valuationSubring.unitGroup →* RVUnit v :=
  (QuotientGroup.mk' (principalUnits v)).comp v.valuationSubring.unitGroup.subtype

theorem unitGroupToRV_apply (x : v.valuationSubring.unitGroup) :
    unitGroupToRV v x = QuotientGroup.mk' (principalUnits v) (x : Kˣ) := rfl

theorem ker_unitGroupToRV (v : Valuation K Γ₀) : (unitGroupToRV v).ker =
    v.valuationSubring.principalUnitGroup.comap v.valuationSubring.unitGroup.subtype := by
  ext x
  rw [MonoidHom.mem_ker, unitGroupToRV_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff]
  exact mem_principalUnits_iff v x

theorem range_unitGroupToRV (v : Valuation K Γ₀) :
    (unitGroupToRV v).range = (vrvUnit v).ker := by
  ext t
  constructor
  · rintro ⟨x, rfl⟩
    rw [MonoidHom.mem_ker, unitGroupToRV_apply, vrvUnit_mk]
    exact (Valuation.mem_unitGroup_iff (v := v) (x := (x : Kˣ))).1 x.2
  · intro ht
    rw [MonoidHom.mem_ker] at ht
    obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective (principalUnits v) (t : RVUnit v)
    rw [← hu, vrvUnit_mk] at ht
    exact ⟨⟨u, (Valuation.mem_unitGroup_iff (v := v) (x := u)).2 ht⟩, hu⟩

/-- **The kernel of `vrv` is the multiplicative group of the residue field**:
`1 → κ^× → RV× → Γ → 1` inside the `RV` sort.  This identifies the `RV` sort built here with
the paper's `RV(K) = K^×/(1+𝔪)`, whose class of `1` is `κ^×` (axiom 4 of `ACVF`). -/
noncomputable def residueFieldUnitsEquivKernel (v : Valuation K Γ₀) :
    (IsLocalRing.ResidueField ↥(v.valuationSubring))ˣ ≃* (vrvUnit v).ker := by
  rw [← range_unitGroupToRV v]
  exact (v.valuationSubring.unitsModPrincipalUnitsEquivResidueFieldUnits).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq (ker_unitGroupToRV v).symm).trans
      (QuotientGroup.quotientKerEquivRange (unitGroupToRV v)))

end ResidueUnits
end RVCalc
#print axioms RVCalc.residueFieldUnitsEquivKernel
