import RVClassEquality

/-! Value map definitions and proofs from QE/RV_henselian.lean at fa3867c. -/
namespace RVCalc
variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]
section ValueMap

variable (v : Valuation K Γ₀)

theorem val_eq_one_of_mem_principalUnits {u : Kˣ} (hu : u ∈ principalUnits v) :
    v ((u : K)) = 1 := by
  have h : (u : K) = ((u : K) - 1) + 1 := by ring
  rw [h, Valuation.map_add_eq_of_lt_right v (by simpa using hu), Valuation.map_one]

/-- The valuation of a unit, as a monoid homomorphism to `Γ₀`. -/
def vrvUnitHom : Kˣ →* Γ₀ :=
  (Units.coeHom Γ₀).comp (Units.map v.toMonoidWithZeroHom.toMonoidHom)

theorem vrvUnitHom_apply (u : Kˣ) : vrvUnitHom v u = v (u : K) := by
  rw [vrvUnitHom, MonoidHom.comp_apply, Units.coeHom_apply, Units.coe_map]
  rfl

/-- `vrv : RV× → Γ`, the value of a leading term: well defined because `v` is constant on
classes modulo `1 + 𝔪`. -/
def vrvUnit : RVUnit v →* Γ₀ :=
  QuotientGroup.lift (principalUnits v) (vrvUnitHom v) (by
    intro u hu
    rw [MonoidHom.mem_ker, vrvUnitHom_apply]
    exact val_eq_one_of_mem_principalUnits v hu)

theorem vrvUnit_mk (u : Kˣ) :
    vrvUnit v (QuotientGroup.mk' (principalUnits v) u) = v (u : K) := by
  rw [vrvUnit]
  exact vrvUnitHom_apply v u

/-- `vrv : RV → Γ ∪ {∞}`, with `vrv ∞ = 0` (axiom 6 of `ACVF`). -/
def vrv : RV v → Γ₀
  | none => 0
  | some a => vrvUnit v a

@[simp] theorem vrv_none : vrv v (none : RV v) = 0 := rfl

@[simp] theorem vrv_some (a : RVUnit v) : vrv v (some a) = vrvUnit v a := rfl

/-- `vv = vrv ∘ rv`: the valuation of an element is the value of its leading term. -/
theorem vrv_rv (x : K) : vrv v (rv v x) = v x := by
  rw [rv]
  split_ifs with h
  · rw [h, Valuation.map_zero]; rfl
  · rw [vrv_some, vrvUnit_mk, Units.val_mk0]

theorem vrv_mul (t s : RV v) : vrv v (rvMul v t s) = vrv v t * vrv v s := by
  match t, s with
  | none, _ => simp
  | some _, none => simp
  | some a, some b => simp only [rvMul_some, vrv_some, map_mul]


/-- `rv` determines the value: the class of `x` modulo `1 + 𝔪` fixes `v x`. -/
theorem v_eq_of_rv_eq {x y : K} (h : rv v x = rv v y) (hx : x ≠ 0) (hy : y ≠ 0) : v x = v y := by
  have hlt : v (x - y) < v x := (rv_eq_iff hx hy).1 h
  have hneg : v (-(x - y)) < v x := by rwa [Valuation.map_neg v]
  have hsplit : y = x + (-(x - y)) := by ring
  rw [hsplit, Valuation.map_add_eq_of_lt_left v hneg]

/-- A representative of the kernel of `vrv` is a unit of the valuation ring. -/
theorem isUnit_of_vrv_eq_one {u : Kˣ} (h : vrv v (some (QuotientGroup.mk' (principalUnits v) u)) = 1) :
    v ((u : K)) = 1 := by
  rw [vrv_some, vrvUnit_mk] at h
  exact h

/-- The kernel of `vrv` is the image of the units of the valuation ring: the exact sequence
`1 → κ^× → RV^× → Γ → 1` of the `RV` sort. -/
theorem vrv_eq_one_iff (u : Kˣ) :
    vrv v (some (QuotientGroup.mk' (principalUnits v) u)) = 1 ↔ v ((u : K)) = 1 := by
  refine ⟨isUnit_of_vrv_eq_one v, ?_⟩
  intro h
  rw [vrv_some, vrvUnit_mk]
  exact h

/-- `vrv` is surjective onto the value group of `v`. -/
theorem vrv_surjective {γ : Γ₀} (hγ : γ ∈ Set.range v) : ∃ t : RV v, vrv v t = γ := by
  obtain ⟨x, rfl⟩ := hγ
  by_cases hx : x = 0
  · exact ⟨none, by rw [hx, Valuation.map_zero]; rfl⟩
  · exact ⟨rv v x, vrv_rv v x⟩


/-- Axiom 6 of `ACVF`: the valuation ring is `rv⁻¹(RV^{≥ 1})`. -/
theorem mem_valuationSubring_iff_vrv {x : K} :
    x ∈ v.valuationSubring ↔ vrv v (rv v x) ≤ 1 := by
  rw [Valuation.mem_valuationSubring_iff, vrv_rv]

/-- Restatement of `vrv_rv`: an element lies in `𝔪` exactly when its leading term is `< 1`. -/
theorem v_lt_one_iff_vrv {x : K} : v x < 1 ↔ vrv v (rv v x) < 1 := by
  rw [vrv_rv]

end ValueMap
end RVCalc
