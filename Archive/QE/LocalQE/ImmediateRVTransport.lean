import RVClassEquality
import ResidueTranscendentalTransport

/-! Immediate extensions add no RV classes. The extension of a valued field
map is an independent input (for a henselization, its universal property).
No embedding-existence theorem for arbitrary immediate extensions is assumed.
-/

namespace ImmediateRVTransport

variable {K L Γ Δ : Type*} [Field K] [Field L]
    [LinearOrderedCommGroupWithZero Γ] [LinearOrderedCommGroupWithZero Δ]

theorem residue_eq_iff (v : Valuation K Γ) {x y : K}
    (hx : v x ≤ 1) (hy : v y ≤ 1) :
    M7.vres v x hx = M7.vres v y hy ↔ v (x - y) < 1 := by
  have hxy := v.map_sub_le hx hy
  have he : M7.vres v (x - y) hxy = M7.vres v x hx - M7.vres v y hy := by
    have hsub : (⟨x - y, (Valuation.mem_valuationSubring_iff v _).mpr hxy⟩ : v.valuationSubring) =
        ⟨x, (Valuation.mem_valuationSubring_iff v _).mpr hx⟩ -
        ⟨y, (Valuation.mem_valuationSubring_iff v _).mpr hy⟩ := Subtype.ext rfl
    simp only [M7.vres, hsub, map_sub]
  rw [← sub_eq_zero, ← he, M7.vres_eq_zero_iff]

/-- Immediacy expressed by equality of the value images and residue images,
inside a fixed ambient valued field. -/
structure Immediate (v : Valuation K Γ) (F E : Subfield K) : Prop where
  base_le : F ≤ E
  values : ∀ x : E, x ≠ 0 → ∃ a : F, v (a : K) = v (x : K)
  residues : ∀ (x : E) (hx : v (x : K) ≤ 1),
    ∃ (a : F) (ha : v (a : K) ≤ 1), M7.vres v (x : K) hx = M7.vres v (a : K) ha

/-- Equality of values and residues yields a base element in each nonzero
leading-term class. -/
theorem exists_close (v : Valuation K Γ) (F E : Subfield K)
    (h : Immediate v F E) (x : E) (hx : x ≠ 0) :
    ∃ a : F, v ((x : K) - (a : K)) < v (x : K) := by
  have hxK : (x : K) ≠ 0 := fun hz => hx (Subtype.ext hz)
  have hvx : v (x : K) ≠ 0 := (Valuation.ne_zero_iff v).mpr hxK
  obtain ⟨a, ha⟩ := h.values x hx
  have hva : v (a : K) ≠ 0 := ha ▸ hvx
  have haK : (a : K) ≠ 0 := (Valuation.ne_zero_iff v).mp hva
  let aE : E := ⟨(a : K), h.base_le a.2⟩
  let y : E := x / aE
  have hy : v (y : K) = 1 := by
    change v ((x : K) / (a : K)) = 1
    rw [map_div₀, ha, div_self hvx]
  obtain ⟨b, hb, hres⟩ := h.residues y hy.le
  have hclose : v ((y : K) - (b : K)) < 1 := (residue_eq_iff v hy.le hb).mp hres
  refine ⟨a * b, ?_⟩
  have he : (x : K) - ((a * b : F) : K) = (a : K) * ((y : K) - (b : K)) := by
    change (x : K) - (a : K) * (b : K) = (a : K) * ((x : K) / (a : K) - (b : K))
    field_simp [haK]
  rw [he, map_mul, ← ha]
  simpa using mul_lt_mul_of_pos_left hclose (zero_lt_iff.mpr hva)

theorem rv_surjective_from_base (v : Valuation K Γ) (F E : Subfield K)
    (h : Immediate v F E) (x : E) :
    ∃ a : F, RVCalc.rv v (x : K) = RVCalc.rv v (a : K) := by
  by_cases hx : x = 0
  · subst x
    exact ⟨0, rfl⟩
  obtain ⟨a, ha⟩ := exists_close v F E h x hx
  have hxK : (x : K) ≠ 0 := fun hz => hx (Subtype.ext hz)
  have haK : (a : K) ≠ 0 := by
    intro hz
    simpa [hz] using ha
  exact ⟨a, (RVCalc.rv_eq_iff hxK haK).mpr ha⟩

/-- Valued field maps preserve and reflect the actual leading-term quotient. -/
theorem rv_eq_iff_map (v : Valuation K Γ) (w : Valuation L Δ)
    (E : Subfield K) (σ : E →+* L)
    (hσ : ∀ x y : E, v (x : K) ≤ v (y : K) ↔ w (σ x) ≤ w (σ y))
    (x y : E) :
    RVCalc.rv v (x : K) = RVCalc.rv v (y : K) ↔ RVCalc.rv w (σ x) = RVCalc.rv w (σ y) := by
  by_cases hx : x = 0
  · subst x
    simp only [ZeroMemClass.coe_zero, map_zero, RVCalc.rv_zero]
    rw [@eq_comm (RVCalc.RV v) none (RVCalc.rv v (y : K)),
      @eq_comm (RVCalc.RV w) none (RVCalc.rv w (σ y)),
      RVCalc.rv_eq_none_iff, RVCalc.rv_eq_none_iff]
    exact ⟨fun hz => by rw [show y = 0 from Subtype.ext hz, map_zero],
      fun hz => congrArg Subtype.val (σ.injective (hz.trans σ.map_zero.symm))⟩
  by_cases hy : y = 0
  · subst y
    simp only [ZeroMemClass.coe_zero, map_zero, RVCalc.rv_zero, RVCalc.rv_eq_none_iff]
    exact ⟨fun hz => by rw [show x = 0 from Subtype.ext hz, map_zero],
      fun hz => congrArg Subtype.val (σ.injective (hz.trans σ.map_zero.symm))⟩
  have hxK : (x : K) ≠ 0 := fun hz => hx (Subtype.ext hz)
  have hyK : (y : K) ≠ 0 := fun hz => hy (Subtype.ext hz)
  have hxL : σ x ≠ 0 := fun hz => hx (σ.injective (hz.trans σ.map_zero.symm))
  have hyL : σ y ≠ 0 := fun hz => hy (σ.injective (hz.trans σ.map_zero.symm))
  rw [RVCalc.rv_eq_iff hxK hyK, RVCalc.rv_eq_iff hxL hyL, ← map_sub]
  exact not_le.symm.trans ((not_congr (hσ x (x - y))).trans not_le)

/-- A valued extension map across a genuine immediate extension automatically
agrees with a prescribed RV relation. Existence of that map is not inferred
from immediacy. -/
theorem relation_of_immediate (v : Valuation K Γ) (w : Valuation L Δ)
    (F E : Subfield K) (h : Immediate v F E) (σ : F →+* L) (τ : E →+* L)
    (hτ : ∀ x y : E, v (x : K) ≤ v (y : K) ↔ w (τ x) ≤ w (τ y))
    (hext : ∀ a : F, τ ⟨(a : K), h.base_le a.2⟩ = σ a)
    (R : RVCalc.RV v → RVCalc.RV w → Prop)
    (hbase : ∀ a : F, R (RVCalc.rv v (a : K)) (RVCalc.rv w (σ a))) (x : E) :
    R (RVCalc.rv v (x : K)) (RVCalc.rv w (τ x)) := by
  obtain ⟨a, ha⟩ := rv_surjective_from_base v F E h x
  have hb := (rv_eq_iff_map v w E τ hτ x ⟨(a : K), h.base_le a.2⟩).mp ha
  rw [hext] at hb
  rw [ha, hb]
  exact hbase a

end ImmediateRVTransport

#print axioms ImmediateRVTransport.exists_close
#print axioms ImmediateRVTransport.rv_surjective_from_base
#print axioms ImmediateRVTransport.rv_eq_iff_map
#print axioms ImmediateRVTransport.relation_of_immediate
