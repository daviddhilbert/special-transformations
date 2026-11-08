import Section6.ConcreteHenselian
import Section6.DenefPasInterpretation

/-! The angular-component splitting presents the same native model as the
ordinary leading-term quotient with its residue-field operations. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Section6.DenefPasHenselianModels

open AngularComponent DenefPasCodes DenefPasNativeModel ConcreteRV ConcreteValued

variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]
variable (v : Valuation K Γ) (a : Data v)

private def gammaInto : Gamma v → Γ
  | none => 0
  | some g => (g.val : Γ)

private theorem gammaInto_le (g h : Gamma v) :
    gammaInto v g ≤ gammaInto v h ↔ g ≤ h := by
  cases g with
  | none =>
    change (0 : Γ) ≤ gammaInto v h ↔ (0 : Gamma v) ≤ h
    simp only [zero_le]
  | some g =>
    cases h with
    | none =>
      change (g.val : Γ) ≤ 0 ↔ (g : Gamma v) ≤ 0
      exact iff_of_false (not_le.mpr (pos_iff_ne_zero.mpr g.val.ne_zero))
        (not_le.mpr (WithZero.zero_lt_coe g))
    | some h =>
      change (g.val : Γ) ≤ (h.val : Γ) ↔ (g : Gamma v) ≤ (h : Gamma v)
      exact (WithZero.coe_le_coe (a := g) (b := h)).symm

private theorem gammaInto_one : gammaInto v (1 : Gamma v) = 1 := rfl

private theorem gammaInto_value (q : RVCalc.RV v) :
    gammaInto v (gammaValue v a q) = RVCalc.vrv v q := by
  cases q with
  | none => rfl
  | some q =>
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (RVCalc.principalUnits v) q
    change (((splitting v a _).2.val : Γ)) = _
    rw [splitting_mk]
    rfl

private theorem gammaValue_eq_one (q : RVCalc.RV v) :
    gammaValue v a q = 1 ↔ RVCalc.vrv v q = 1 := by
  rw [← gammaInto_value v a, ← gammaInto_one v]
  constructor
  · exact congrArg (gammaInto v)
  · intro h
    exact le_antisymm ((gammaInto_le v _ _).mp h.le) ((gammaInto_le v _ _).mp h.ge)

private theorem residueValue_code (r : ConcreteRV.Residue v) :
    residueValue v a (residueCode v r) = r := by
  by_cases hr : r = 0
  · subst r
    rw [residueCode_zero]
    rfl
  · obtain ⟨x, hv, hx⟩ := residue_lift_value_one v (Units.mk0 r hr)
    change IsLocalRing.residue v.valuationSubring x = r at hx
    rw [← hx, residueCode_reduction, if_pos hv, residueValue_rv, a.agrees x hv]

private theorem encode_one (r : ConcreteRV.Residue v) :
    encode v a r 1 = residueCode v r := by
  by_cases hr : r = 0
  · subst r
    rw [encode_zero, residueCode_zero]
  · have hr' : residueCode v r ≠ none := by
      intro he
      exact hr (residueCode_injective v (he.trans (residueCode_zero v).symm))
    have hγ := (gammaValue_eq_one v a _).mpr (value_residueCode v hr)
    rw [encode_ne_zero v a r hr]
    cases hq : residueCode v r with
    | none => exact (hr' hq).elim
    | some q =>
      have h₁ := residueValue_code v a r
      rw [hq] at h₁ hγ
      have hprod : splitting v a q = (Units.mk0 r hr, 1) := by
        apply Prod.ext
        · exact Units.ext h₁
        · exact Option.some.inj hγ
      rw [← hprod, MulEquiv.symm_apply_apply]

private theorem residueDomain_iff (q : RVCalc.RV v) :
    DenefPasRV.residueDomain v a q ↔ q ∈ Set.range (residueCode v) := by
  rw [DenefPasRV.residueDomain, gammaValue_eq_one, residueCode_range, Set.mem_setOf_eq]

private theorem add_eq (q r : RVCalc.RV v) :
    DenefPasRV.add v a q r = addResidue v q r := by
  by_cases h : q ∈ Set.range (residueCode v) ∧ r ∈ Set.range (residueCode v)
  · obtain ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩ := h
    rw [addResidue_code, DenefPasRV.add, if_pos ⟨(residueDomain_iff v a _).mpr ⟨x, rfl⟩,
      (residueDomain_iff v a _).mpr ⟨y, rfl⟩⟩]
    have hne (r : ConcreteRV.Residue v) (hr : r ≠ 0) : residueCode v r ≠ none := by
      intro he
      exact hr (residueCode_injective v (he.trans (residueCode_zero v).symm))
    by_cases hx : x = 0
    · simp [hx]
    by_cases hy : y = 0
    · simp [hy, hne x hx]
    rw [if_neg (hne x hx), if_neg (hne y hy), residueValue_code, residueValue_code, encode_one]
  · rw [addResidue, if_neg h, DenefPasRV.add]
    simp only [residueDomain_iff, h, if_false]

private theorem neg_eq (q : RVCalc.RV v) :
    DenefPasRV.neg v a q = negResidue v q := by
  by_cases h : q ∈ Set.range (residueCode v)
  · obtain ⟨r, rfl⟩ := h
    rw [negResidue_code, DenefPasRV.neg, if_pos ((residueDomain_iff v a _).mpr ⟨r, rfl⟩),
      residueValue_code, encode_one]
  · rw [negResidue, if_neg h, DenefPasRV.neg]
    simp only [residueDomain_iff, h, if_false]

private theorem isField_iff (z : Carrier v) :
    DenefPasLanguage.IsField z ↔ hasSort v .vf z := by
  cases z <;> simp [DenefPasLanguage.IsField, hasSort]

private theorem isRV_iff (z : Carrier v) : IsRV z ↔ hasSort v .rv z := by
  cases z <;> simp [IsRV, hasSort]

theorem nativeStructure_eq : nativeStructure v a = ConcreteValued.nativeStructure v := by
  apply FirstOrder.Language.Structure.ext
  · funext n f z
    change nativeFunction v a f z =
      if ∀ i, hasSort v (Fn.argSort f i) (z i) then functionValue v f z else zeroOf v (Fn.resSort f)
    have hf : DenefPasLanguage.fieldValue = vfValue v := by
      funext x
      cases x <;> rfl
    have hr : DenefPasNativeModel.rvValue = ConcreteValued.rvValue v := by
      funext x
      cases x <;> rfl
    cases f <;>
      simp only [nativeFunction, DenefPasLanguage.fieldFunction, liftRV, isField_iff, isRV_iff,
        functionValue, zeroOf, Fn.argSort, Fn.resSort, hf, hr] <;>
      first | rfl | split <;> try rfl
    · change Sum.inr (DenefPasRV.add v a (ConcreteValued.rvValue v (z 0))
        (ConcreteValued.rvValue v (z 1))) = _
      rw [add_eq]
    · change Sum.inr (DenefPasRV.neg v a (ConcreteValued.rvValue v (z 0))) = _
      rw [neg_eq]
    · have hz : ∀ i, z i = z 0 := fun i => congrArg z (Subsingleton.elim _ _)
      cases h : z 0 with
      | inl x => exact (‹¬ ∀ i, hasSort v .vf (z i)› (fun i => by rw [hz, h]; trivial)).elim
      | inr q => exact congrArg Sum.inr (RVCalc.rv_zero (v := v))
  · funext n r z
    apply propext
    cases r with
    | memVF =>
      change DenefPasLanguage.IsField (z 0) ↔ hasSort v .vf (z 0)
      exact isField_iff v _
    | memRV =>
      change IsRV (z 0) ↔ hasSort v .rv (z 0)
      exact isRV_iff v _
    | memUnits =>
      let q := ConcreteValued.rvValue v (z 0)
      change (IsRV (z 0) ∧ q ≠ none ∧ gammaValue v a q = 1) ↔
        (hasSort v .rv (z 0) ∧ RVCalc.vrv v q = 1)
      rw [isRV_iff, gammaValue_eq_one]
      exact ⟨fun h => ⟨h.1, h.2.2⟩,
        fun h => ⟨h.1, fun hn => zero_ne_one (by simpa only [hn, RVCalc.vrv_none] using h.2), h.2⟩⟩
    | rvLe =>
      let q := ConcreteValued.rvValue v (z 0)
      let r := ConcreteValued.rvValue v (z 1)
      change ((∀ i, IsRV (z i)) ∧ gammaValue v a r ≤ gammaValue v a q) ↔
        ((∀ i, hasSort v .rv (z i)) ∧ RVCalc.vrv v r ≤ RVCalc.vrv v q)
      simp_rw [isRV_iff, ← gammaInto_le v, gammaInto_value]

theorem ordinaryRecognition : OrdinaryRecognition := by
  intro K Γ _ _ v a _ _ _ hnt
  have hex : ∃ x : K, x ≠ 0 ∧ v x < 1 := by
    unfold Trivial at hnt
    push_neg at hnt
    obtain ⟨x, hx, hval⟩ := hnt
    rcases lt_or_gt_of_ne hval with h | h
    · exact ⟨x, hx, h⟩
    · exact ⟨x⁻¹, inv_ne_zero hx, by
        rw [map_inv₀]
        exact (inv_lt_one₀ (zero_lt_one.trans h)).mpr h⟩
  change @Theory.Model LRV _ (nativeStructure v a) HenselianTheory.canonicalHen00
  rw [nativeStructure_eq]
  exact model_canonicalHen00 v hex

end SpecialTransformations.Section6.DenefPasHenselianModels
