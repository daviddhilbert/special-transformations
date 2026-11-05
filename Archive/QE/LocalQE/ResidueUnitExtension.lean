import ResidueAlgebraicAdjoin
import BaseResidueField

/-!
Adjoin a field representative of any prescribed unit RV class.

The algebraic/transcendental split is taken over the actual base residue field.
Both branches construct the field embedding. In the algebraic branch the
source representative may change within its RV class; this theorem does not
claim to adjoin an arbitrary chosen immediate-field element.
-/

namespace ResidueAlgebraicTransport

open scoped IntermediateField
open ResidueTranscendentalTransport

variable {K L Γ Δ : Type*} [Field K] [Field L]
  [LinearOrderedCommGroupWithZero Γ] [LinearOrderedCommGroupWithZero Δ]

theorem exists_unit_representative (v : Valuation K Γ) (z : Residue v) (hz : z ≠ 0) :
    ∃ a : K, ∃ ha : v a = 1, M7.vres v a ha.le = z := by
  obtain ⟨a, har⟩ := IsLocalRing.residue_surjective (R := v.valuationSubring) z
  have ha : v (a : K) ≤ 1 := (Valuation.mem_valuationSubring_iff v _).mp a.property
  have ha1 : v (a : K) = 1 := by
    apply le_antisymm ha
    apply le_of_not_gt
    intro hlt
    apply hz
    rw [← har]
    exact (M7.vres_eq_zero_iff v _ ha).mpr hlt
  exact ⟨(a : K), ha1, har⟩

theorem exists_unit_residue_extension [IsAlgClosed K] [IsAlgClosed L]
    (v : Valuation K Γ) (w : Valuation L Δ)
    (F : Subfield K) (σ : F →+* L) (ρ : Residue v →+* Residue w)
    (R : RVCalc.RV v → RVCalc.RV w → Prop)
    (hzero : R none none)
    (hmul : ∀ a b a' b', R a a' → R b b' →
      R (RVCalc.rvMul v a b) (RVCalc.rvMul w a' b'))
    (hinv : ∀ a a', R a a' → R (rvInv v a) (rvInv w a'))
    (hintegral : ∀ a : F, v (a : K) ≤ 1 → w (σ a) ≤ 1)
    (hres : ∀ (a : F) (ha : v (a : K) ≤ 1) (hb : w (σ a) ≤ 1),
      ρ (M7.vres v (a : K) ha) = M7.vres w (σ a) hb)
    (hbase : ∀ a : F, R (RVCalc.rv v (a : K)) (RVCalc.rv w (σ a)))
    (hunit : ∀ (x : K) (y : L) (hx : v x = 1) (hy : w y = 1),
      ρ (M7.vres v x hx.le) = M7.vres w y hy.le → R (RVCalc.rv v x) (RVCalc.rv w y))
    {u : K} {a₀ : L} (hu : v u = 1) (ha₀ : w a₀ = 1)
    (hvar : ρ (M7.vres v u hu.le) = M7.vres w a₀ ha₀.le) :
    ∃ e : K, v e = 1 ∧ RVCalc.rv v e = RVCalc.rv v u ∧
      ∃ g : F⟮e⟯ →+* L,
        Function.Injective g ∧
        (∀ a : F, g (algebraMap F F⟮e⟯ a) = σ a) ∧
        RVCalc.rv w (g (IntermediateField.AdjoinSimple.gen F e)) = RVCalc.rv w a₀ ∧
        ∀ x : F⟮e⟯, R (RVCalc.rv v (x : K)) (RVCalc.rv w (g x)) := by
  rcases residue_cases v F hu with halg | htrans
  · exact exists_adjoin_embedding v w F σ ρ (baseResidueField v F)
      (baseResidueField_contains v F) (baseResidueField_surjective v F)
      R hzero hmul hintegral hres hbase hunit hu ha₀ halg hvar
  · obtain ⟨g, hinj, hbase', hgen, hrv⟩ :=
      ResidueTranscendentalTransport.exists_field_embedding v w F σ ρ R hzero hmul hinv
        hintegral hres hbase hunit hu ha₀ htrans hvar
    exact ⟨u, hu, rfl, g, hinj, hbase', by rw [hgen], hrv⟩

/-- A representative of the target residue class also exists canonically, so
the unit-class field extension needs no target-representative hypothesis. -/
theorem exists_unit_class_field_extension [IsAlgClosed K] [IsAlgClosed L]
    (v : Valuation K Γ) (w : Valuation L Δ)
    (F : Subfield K) (σ : F →+* L) (ρ : Residue v →+* Residue w)
    (R : RVCalc.RV v → RVCalc.RV w → Prop)
    (hzero : R none none)
    (hmul : ∀ a b a' b', R a a' → R b b' →
      R (RVCalc.rvMul v a b) (RVCalc.rvMul w a' b'))
    (hinv : ∀ a a', R a a' → R (rvInv v a) (rvInv w a'))
    (hintegral : ∀ a : F, v (a : K) ≤ 1 → w (σ a) ≤ 1)
    (hres : ∀ (a : F) (ha : v (a : K) ≤ 1) (hb : w (σ a) ≤ 1),
      ρ (M7.vres v (a : K) ha) = M7.vres w (σ a) hb)
    (hbase : ∀ a : F, R (RVCalc.rv v (a : K)) (RVCalc.rv w (σ a)))
    (hunit : ∀ (x : K) (y : L) (hx : v x = 1) (hy : w y = 1),
      ρ (M7.vres v x hx.le) = M7.vres w y hy.le → R (RVCalc.rv v x) (RVCalc.rv w y))
    {u : K} (hu : v u = 1) :
    ∃ e : K, v e = 1 ∧ RVCalc.rv v e = RVCalc.rv v u ∧
      ∃ g : F⟮e⟯ →+* L,
        Function.Injective g ∧
        (∀ a : F, g (algebraMap F F⟮e⟯ a) = σ a) ∧
        ∀ x : F⟮e⟯, R (RVCalc.rv v (x : K)) (RVCalc.rv w (g x)) := by
  have hz : M7.vres v u hu.le ≠ 0 := by
    intro hzero'
    have hlt := (M7.vres_eq_zero_iff v _ hu.le).mp hzero'
    rw [hu] at hlt
    exact lt_irrefl 1 hlt
  have hz' : ρ (M7.vres v u hu.le) ≠ 0 :=
    fun h => hz (ρ.injective (by simpa using h))
  obtain ⟨a₀, ha₀, hres₀⟩ := exists_unit_representative w _ hz'
  obtain ⟨e, he, herv, g, hinj, hbase', _, hrv⟩ :=
    exists_unit_residue_extension v w F σ ρ R hzero hmul hinv hintegral hres hbase hunit
      hu ha₀ hres₀.symm
  exact ⟨e, he, herv, g, hinj, hbase', hrv⟩

end ResidueAlgebraicTransport

#print axioms ResidueAlgebraicTransport.exists_unit_residue_extension
#print axioms ResidueAlgebraicTransport.exists_unit_representative
#print axioms ResidueAlgebraicTransport.exists_unit_class_field_extension
