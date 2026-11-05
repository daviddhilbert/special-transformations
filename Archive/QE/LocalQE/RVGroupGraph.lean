import RVFrame
import CommutativeGroupAmalgam

/-! Add the absorbing element to the graph of an actual partial RV group map.
The result is the pointwise RV relation consumed by the field-extension proof. -/

namespace RVGroupGraph

open ResidueTranscendentalTransport

variable {K L Γ Δ : Type*} [Field K] [Field L]
  [LinearOrderedCommGroupWithZero Γ] [LinearOrderedCommGroupWithZero Δ]

def Graph (v : Valuation K Γ) (w : Valuation L Δ)
    (A : Subgroup (RVCalc.RVUnit v)) (f : A →* RVCalc.RVUnit w)
    (x : RVCalc.RV v) (y : RVCalc.RV w) : Prop :=
  (x = none ∧ y = none) ∨ ∃ a : A, x = some (a : RVCalc.RVUnit v) ∧ y = some (f a)

theorem functional (v : Valuation K Γ) (w : Valuation L Δ)
    (A : Subgroup (RVCalc.RVUnit v)) (f : A →* RVCalc.RVUnit w) :
    ∀ x y z, Graph v w A f x y → Graph v w A f x z → y = z := by
  rintro x y z (⟨rfl, rfl⟩ | ⟨a, rfl, rfl⟩) (⟨hx, rfl⟩ | ⟨b, hb, rfl⟩)
  · rfl
  · cases hb
  · cases hx
  · have hab : a = b := Subtype.ext (Option.some.inj hb)
    rw [hab]

theorem graph_some (v : Valuation K Γ) (w : Valuation L Δ)
    (A : Subgroup (RVCalc.RVUnit v)) (f : A →* RVCalc.RVUnit w)
    (a : A) (b : RVCalc.RVUnit w) :
    Graph v w A f (some (a : RVCalc.RVUnit v)) (some b) ↔ f a = b := by
  constructor
  · rintro (⟨h, _⟩ | ⟨c, hc, hb⟩)
    · cases h
    · have hac : a = c := Subtype.ext (Option.some.inj hc)
      rw [hac]
      exact (Option.some.inj hb).symm
  · intro h
    exact Or.inr ⟨a, rfl, congrArg some h.symm⟩

theorem mul (v : Valuation K Γ) (w : Valuation L Δ)
    (A : Subgroup (RVCalc.RVUnit v)) (f : A →* RVCalc.RVUnit w) :
    ∀ a b a' b', Graph v w A f a a' → Graph v w A f b b' →
      Graph v w A f (RVCalc.rvMul v a b) (RVCalc.rvMul w a' b') := by
  rintro a b a' b' (⟨rfl, rfl⟩ | ⟨a, rfl, rfl⟩) (⟨rfl, rfl⟩ | ⟨b, rfl, rfl⟩)
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨a * b, rfl, by simp only [RVCalc.rvMul_some, map_mul]⟩

theorem inv (v : Valuation K Γ) (w : Valuation L Δ)
    (A : Subgroup (RVCalc.RVUnit v)) (f : A →* RVCalc.RVUnit w) :
    ∀ a b, Graph v w A f a b → Graph v w A f (rvInv v a) (rvInv w b) := by
  rintro a b (⟨rfl, rfl⟩ | ⟨a, rfl, rfl⟩)
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨a⁻¹, rfl, by simp only [rvInv, map_inv]⟩

theorem vrvUnit_ne_zero (v : Valuation K Γ) (a : RVCalc.RVUnit v) :
    RVCalc.vrvUnit v a ≠ 0 := by
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (RVCalc.principalUnits v) a
  rw [RVCalc.vrvUnit_mk]
  exact (Valuation.ne_zero_iff v).mpr u.ne_zero

theorem order (v : Valuation K Γ) (w : Valuation L Δ)
    (A : Subgroup (RVCalc.RVUnit v)) (f : A →* RVCalc.RVUnit w)
    (hf : ∀ a b : A, RVCalc.vrvUnit v (a : RVCalc.RVUnit v) ≤ RVCalc.vrvUnit v (b : RVCalc.RVUnit v) ↔
      RVCalc.vrvUnit w (f a) ≤ RVCalc.vrvUnit w (f b)) :
    ∀ a b a' b', Graph v w A f a a' → Graph v w A f b b' →
      (RVCalc.vrv v a ≤ RVCalc.vrv v b ↔ RVCalc.vrv w a' ≤ RVCalc.vrv w b') := by
  rintro a b a' b' (⟨rfl, rfl⟩ | ⟨a, rfl, rfl⟩) (⟨rfl, rfl⟩ | ⟨b, rfl, rfl⟩)
  · simp
  · simp
  · simp only [RVCalc.vrv_some, RVCalc.vrv_none,
      not_le.mpr (zero_lt_iff.mpr (vrvUnit_ne_zero v a)),
      not_le.mpr (zero_lt_iff.mpr (vrvUnit_ne_zero w (f a)))]
  · exact hf a b

noncomputable def unitClass (v : Valuation K Γ) (x : K) (hx : v x = 1) :
    (RVCalc.vrvUnit v).ker := by
  have hx0 : x ≠ 0 := by intro h; simpa [h] using hx
  refine ⟨QuotientGroup.mk' (RVCalc.principalUnits v) (Units.mk0 x hx0), ?_⟩
  rw [MonoidHom.mem_ker, RVCalc.vrvUnit_mk, Units.val_mk0]
  exact hx

theorem rv_unitClass (v : Valuation K Γ) (x : K) (hx : v x = 1) :
    RVCalc.rv v x = some ((unitClass v x hx : (RVCalc.vrvUnit v).ker) : RVCalc.RVUnit v) := by
  have hx0 : x ≠ 0 := by intro h; simpa [h] using hx
  exact RVCalc.rv_of_ne hx0

theorem frame (v : Valuation K Γ) (w : Valuation L Δ)
    (ρ : Residue v →+* Residue w)
    (A : Subgroup (RVCalc.RVUnit v)) (f : A →* RVCalc.RVUnit w)
    (hA : (RVCalc.vrvUnit v).ker ≤ A)
    (hf : ∀ a b : A, RVCalc.vrvUnit v (a : RVCalc.RVUnit v) ≤ RVCalc.vrvUnit v (b : RVCalc.RVUnit v) ↔
      RVCalc.vrvUnit w (f a) ≤ RVCalc.vrvUnit w (f b))
    (hu : ∀ (x : K) (y : L) (hx : v x = 1) (hy : w y = 1),
      f (Subgroup.inclusion hA (unitClass v x hx)) = (unitClass w y hy : RVCalc.RVUnit w) ↔
        ρ (M7.vres v x hx.le) = M7.vres w y hy.le) :
    RVFrame v w ρ (Graph v w A f) where
  zero := Or.inl ⟨rfl, rfl⟩
  mul := mul v w A f
  inv := inv v w A f
  order := order v w A f hf
  unit x y hx hy := by
    rw [rv_unitClass v x hx, rv_unitClass w y hy]
    exact (graph_some v w A f (Subgroup.inclusion hA (unitClass v x hx)) _).trans (hu x y hx hy)

end RVGroupGraph

#print axioms RVGroupGraph.functional
#print axioms RVGroupGraph.frame
