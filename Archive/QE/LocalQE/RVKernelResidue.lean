import RVGroupGraph
import ResidueUnitExtension
import ImmediateRVTransport

/-! The value-one RV subgroup is naturally the multiplicative group of the
residue field. This construction includes the evaluation formula needed to
transport an actual residue-field homomorphism. -/

namespace RVKernelResidue

open ResidueTranscendentalTransport RVGroupGraph

variable {K L Γ Δ : Type*} [Field K] [Field L]
  [LinearOrderedCommGroupWithZero Γ] [LinearOrderedCommGroupWithZero Δ]

theorem residue_eq_iff_rv (v : Valuation K Γ) {x y : K}
    (hx : v x = 1) (hy : v y = 1) :
    M7.vres v x hx.le = M7.vres v y hy.le ↔ RVCalc.rv v x = RVCalc.rv v y := by
  have hx0 : x ≠ 0 := by intro h; simpa [h] using hx
  have hy0 : y ≠ 0 := by intro h; simpa [h] using hy
  rw [ImmediateRVTransport.residue_eq_iff, RVCalc.rv_eq_iff hx0 hy0, hx]

noncomputable def representative (v : Valuation K Γ) (u : (RVCalc.vrvUnit v).ker) : K :=
  Classical.choose (RVCalc.rv_surjective v (u : RVCalc.RVUnit v))

theorem representative_rv (v : Valuation K Γ) (u : (RVCalc.vrvUnit v).ker) :
    RVCalc.rv v (representative v u) = some (u : RVCalc.RVUnit v) :=
  (Classical.choose_spec (RVCalc.rv_surjective v (u : RVCalc.RVUnit v))).2

theorem representative_value (v : Valuation K Γ) (u : (RVCalc.vrvUnit v).ker) :
    v (representative v u) = 1 := by
  have h := congrArg (RVCalc.vrv v) (representative_rv v u)
  rw [RVCalc.vrv_rv, RVCalc.vrv_some] at h
  exact h.trans (MonoidHom.mem_ker.mp u.2)

noncomputable def residue (v : Valuation K Γ) (u : (RVCalc.vrvUnit v).ker) : Residue v :=
  M7.vres v (representative v u) (representative_value v u).le

theorem residue_ne_zero (v : Valuation K Γ) (u : (RVCalc.vrvUnit v).ker) : residue v u ≠ 0 := by
  intro h
  have hlt := (M7.vres_eq_zero_iff v _ _).mp h
  rw [representative_value] at hlt
  exact lt_irrefl 1 hlt

theorem residue_unitClass (v : Valuation K Γ) (x : K) (hx : v x = 1) :
    residue v (unitClass v x hx) = M7.vres v x hx.le := by
  apply (residue_eq_iff_rv v (representative_value v _) hx).mpr
  rw [representative_rv, rv_unitClass]

theorem residue_one (v : Valuation K Γ) : residue v 1 = 1 := by
  have hrv : RVCalc.rv v 1 = some 1 := by simp [RVCalc.rv, Units.mk0_one]
  have hh := (residue_eq_iff_rv v (representative_value v 1) (map_one v)).mpr
    ((representative_rv v 1).trans hrv.symm)
  exact hh.trans (M7.vres_one v _)

theorem residue_mul (v : Valuation K Γ) (u z : (RVCalc.vrvUnit v).ker) :
    residue v (u * z) = residue v u * residue v z := by
  have hv : v (representative v u * representative v z) = 1 := by
    rw [map_mul, representative_value, representative_value, one_mul]
  have hr : RVCalc.rv v (representative v (u * z)) =
      RVCalc.rv v (representative v u * representative v z) := by
    rw [representative_rv, rv_mul_all, representative_rv, representative_rv]
    rfl
  exact ((residue_eq_iff_rv v (representative_value v _) hv).mpr hr).trans
    (M7.vres_mul v (representative_value v u).le (representative_value v z).le hv.le)

noncomputable def residueHom (v : Valuation K Γ) : (RVCalc.vrvUnit v).ker →* (Residue v)ˣ where
  toFun u := Units.mk0 (residue v u) (residue_ne_zero v u)
  map_one' := Units.ext (residue_one v)
  map_mul' u z := Units.ext (residue_mul v u z)

theorem residueHom_injective (v : Valuation K Γ) : Function.Injective (residueHom v) := by
  intro u z h
  have hr := congrArg (fun a : (Residue v)ˣ => (a : Residue v)) h
  have he := (residue_eq_iff_rv v (representative_value v u) (representative_value v z)).mp hr
  rw [representative_rv, representative_rv] at he
  exact Subtype.ext (Option.some.inj he)

theorem residueHom_surjective (v : Valuation K Γ) : Function.Surjective (residueHom v) := by
  intro z
  obtain ⟨x, hx, hres⟩ := ResidueAlgebraicTransport.exists_unit_representative v (z : Residue v) z.ne_zero
  refine ⟨unitClass v x hx, Units.ext ?_⟩
  exact (residue_unitClass v x hx).trans hres

noncomputable def equiv (v : Valuation K Γ) : (RVCalc.vrvUnit v).ker ≃* (Residue v)ˣ :=
  MulEquiv.ofBijective (residueHom v) ⟨residueHom_injective v, residueHom_surjective v⟩

noncomputable def map (v : Valuation K Γ) (w : Valuation L Δ) (ρ : Residue v →+* Residue w) :
    (RVCalc.vrvUnit v).ker →* (RVCalc.vrvUnit w).ker :=
  (equiv w).symm.toMonoidHom.comp ((Units.map ρ.toMonoidHom).comp (equiv v).toMonoidHom)

theorem residue_map (v : Valuation K Γ) (w : Valuation L Δ) (ρ : Residue v →+* Residue w)
    (u : (RVCalc.vrvUnit v).ker) : residue w (map v w ρ u) = ρ (residue v u) := by
  have h := (equiv w).apply_symm_apply ((Units.map ρ.toMonoidHom) (equiv v u))
  exact congrArg (fun a : (Residue w)ˣ => (a : Residue w)) h

theorem map_unitClass_iff (v : Valuation K Γ) (w : Valuation L Δ)
    (ρ : Residue v →+* Residue w) (x : K) (y : L) (hx : v x = 1) (hy : w y = 1) :
    map v w ρ (unitClass v x hx) = unitClass w y hy ↔
      ρ (M7.vres v x hx.le) = M7.vres w y hy.le := by
  rw [← (residueHom_injective w).eq_iff, Units.ext_iff]
  change residue w (map v w ρ (unitClass v x hx)) = residue w (unitClass w y hy) ↔ _
  rw [residue_map, residue_unitClass, residue_unitClass]

end RVKernelResidue

#print axioms RVKernelResidue.equiv
#print axioms RVKernelResidue.map_unitClass_iff
