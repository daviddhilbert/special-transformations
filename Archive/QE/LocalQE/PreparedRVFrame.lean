import RVKernelResidue

set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1000000

/-! Adjoin all residue units to an existing partial RV group map. The only
compatibility required is agreement on their actual intersection. -/

namespace PreparedRVFrame

open ResidueTranscendentalTransport RVGroupGraph CommutativeGroupAmalgam

variable {K L Γ Δ : Type*} [Field K] [Field L]
  [LinearOrderedCommGroupWithZero Γ] [LinearOrderedCommGroupWithZero Δ]

-- Use one path through the quotient's algebraic instances when forming
-- subgroup joins. This avoids expensive reduction of the group-instance diamond.
local instance (v : Valuation K Γ) : Group (RVCalc.RVUnit v) :=
  (inferInstance : CommGroup (RVCalc.RVUnit v)).toGroup
local instance (v : Valuation K Γ) : CommMonoid (RVCalc.RVUnit v) :=
  (inferInstance : CommGroup (RVCalc.RVUnit v)).toCommMonoid

noncomputable def residueUnitsMap (v : Valuation K Γ) (w : Valuation L Δ)
    (ρ : Residue v →+* Residue w) : (RVCalc.vrvUnit v).ker →* RVCalc.RVUnit w :=
  (RVCalc.vrvUnit w).ker.subtype.comp (RVKernelResidue.map v w ρ)

theorem exists_frame (v : Valuation K Γ) (w : Valuation L Δ)
    (ρ : Residue v →+* Residue w)
    (H : Subgroup (RVCalc.RVUnit v)) (f : H →* RVCalc.RVUnit w)
    (hf : ∀ a b : H, RVCalc.vrvUnit v (a : RVCalc.RVUnit v) ≤ RVCalc.vrvUnit v (b : RVCalc.RVUnit v) ↔
      RVCalc.vrvUnit w (f a) ≤ RVCalc.vrvUnit w (f b))
    (hagree : AgreeOnInf (G := RVCalc.RVUnit v) (H := RVCalc.RVUnit w)
      (RVCalc.vrvUnit v).ker H (residueUnitsMap v w ρ) f) :
    ∃ R : RVCalc.RV v → RVCalc.RV w → Prop,
      RVFrame v w ρ R ∧ (∀ x y z, R x y → R x z → y = z) ∧
        ∀ a : H, R (some (a : RVCalc.RVUnit v)) (some (f a)) := by
  let U : Subgroup (RVCalc.RVUnit v) := (RVCalc.vrvUnit v).ker
  let A : Subgroup (RVCalc.RVUnit v) := U ⊔ H
  let fU : U →* RVCalc.RVUnit w := residueUnitsMap v w ρ
  let g : A →* RVCalc.RVUnit w :=
    glue (G := RVCalc.RVUnit v) (H := RVCalc.RVUnit w) U H fU f hagree
  have hU : U ≤ A := le_sup_left
  have ho : ∀ a b : A, RVCalc.vrvUnit v (a : RVCalc.RVUnit v) ≤ RVCalc.vrvUnit v (b : RVCalc.RVUnit v) ↔
      RVCalc.vrvUnit w (g a) ≤ RVCalc.vrvUnit w (g b) := by
    apply glue_order_iff (G := RVCalc.RVUnit v) (H := RVCalc.RVUnit w)
      U H fU f hagree (RVCalc.vrvUnit v) (RVCalc.vrvUnit w)
    · intro u
      exact MonoidHom.mem_ker.mp u.2
    · intro u
      exact MonoidHom.mem_ker.mp (RVKernelResidue.map v w ρ u).2
    · exact hf
  refine ⟨Graph v w A g, ?_, functional v w A g, ?_⟩
  · apply frame v w ρ A g hU ho
    intro x y hx hy
    have he : g (Subgroup.inclusion hU (unitClass v x hx)) = fU (unitClass v x hx) :=
      glue_left (G := RVCalc.RVUnit v) (H := RVCalc.RVUnit w) U H fU f hagree (unitClass v x hx)
    rw [he]
    change ((RVKernelResidue.map v w ρ (unitClass v x hx) : (RVCalc.vrvUnit w).ker) :
        RVCalc.RVUnit w) = (unitClass w y hy : RVCalc.RVUnit w) ↔ _
    exact Subtype.ext_iff.symm.trans (RVKernelResidue.map_unitClass_iff v w ρ x y hx hy)
  · intro a
    refine Or.inr ⟨Subgroup.inclusion (show H ≤ A from le_sup_right) a, rfl, ?_⟩
    exact congrArg some (glue_right (G := RVCalc.RVUnit v) (H := RVCalc.RVUnit w) U H fU f hagree a).symm

end PreparedRVFrame

#print axioms PreparedRVFrame.exists_frame
