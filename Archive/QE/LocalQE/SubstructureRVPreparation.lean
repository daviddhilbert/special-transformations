import SubstructureResidue
import PreparedRVFrame
import ResidueEmbeddingExtension

/-! Prepare an arbitrary language substructure by adjoining the full residue
field. Agreement on the intersection is proved from the original language
embedding and the actual residue-field interpretation. -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open ResidueTranscendentalTransport

namespace SubstructureRVPreparation

variable {M N : Type} [LRV.Structure M] [LRV.Structure N]
  [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]
variable {Γ Δ : Type} [LinearOrderedCommGroupWithZero Γ] [LinearOrderedCommGroupWithZero Δ]
  (v : Valuation (VFType (M := M)) Γ) (w : Valuation (VFType (M := N)) Δ)
  (hv : ∀ a b : VFType (M := M), VFValued.predV a b ↔ v a ≤ v b)
  (hw : ∀ a b : VFType (M := N), VFValued.predV a b ↔ w a ≤ w b)

/-- The abstract kernel-residue correspondence and the interpretation inside
the tagged model send a residue unit to the same encoded RV element. -/
theorem kernel_encoding (u : (_root_.RVCalc.vrvUnit v).ker) :
    CanonicalResidue.encodeResidue v hv (RVKernelResidue.residue v u) =
      CanonicalRV.encodeUnit v hv u := by
  change (CanonicalResidue.toRV v hv
    (M7.vres v (RVKernelResidue.representative v u)
      (RVKernelResidue.representative_value v u).le)).val = _
  rw [CanonicalResidue.toRV_vres_of_unit v hv _ (RVKernelResidue.representative_value v u)]
  change (CanonicalRV.encodedRv (RVKernelResidue.representative v u)).val =
    (CanonicalRV.equiv v hv (some (u : _root_.RVCalc.RVUnit v))).val
  rw [← CanonicalRV.equiv_rv v hv, RVKernelResidue.representative_rv]

variable (S : LRV.Substructure M) (f : S ↪[LRV] N)

/-- Extending the *actual* residue subfield map forces compatibility of the
full residue-unit map with the original RV group map on their intersection. -/
theorem intersection_agrees (ρ : Residue v →+* Residue w)
    (hρ : ∀ a : SubstructureResidue.field v hv S,
      ρ a.val = SubstructureResidue.map v w hv hw S f a) :
    CommutativeGroupAmalgam.AgreeOnInf
      (G := _root_.RVCalc.RVUnit v) (H := _root_.RVCalc.RVUnit w)
      (_root_.RVCalc.vrvUnit v).ker (SubstructureRVGroup.group v hv S)
      (PreparedRVFrame.residueUnitsMap v w ρ) (SubstructureRVGroup.map v w hv hw S f) := by
  intro x
  let u : (_root_.RVCalc.vrvUnit v).ker := ⟨x.val, x.property.1⟩
  let t : SubstructureRVGroup.group v hv S := ⟨x.val, x.property.2⟩
  let z : Residue v := RVKernelResidue.residue v u
  have hz : z ∈ SubstructureResidue.field v hv S := by
    change CanonicalResidue.encodeResidue v hv (RVKernelResidue.residue v u) ∈ S
    rw [kernel_encoding v hv]
    exact x.property.2
  apply CanonicalRV.encodeUnit_injective w hw
  change CanonicalRV.encodeUnit w hw
      (RVKernelResidue.map v w ρ u : _root_.RVCalc.RVUnit w) =
    CanonicalRV.encodeUnit w hw (SubstructureRVGroup.map v w hv hw S f t)
  rw [← kernel_encoding w hw, RVKernelResidue.residue_map]
  calc
    CanonicalResidue.encodeResidue w hw (ρ (RVKernelResidue.residue v u)) =
        CanonicalResidue.encodeResidue w hw (SubstructureResidue.map v w hv hw S f ⟨z, hz⟩) :=
      congrArg (CanonicalResidue.encodeResidue w hw) (hρ ⟨z, hz⟩)
    _ = f ⟨CanonicalResidue.encodeResidue v hv z, hz⟩ :=
      SubstructureResidue.map_agrees v w hv hw S f ⟨z, hz⟩
    _ = f ⟨CanonicalRV.encodeUnit v hv t, t.property⟩ := by
      apply congrArg f
      exact Subtype.ext (kernel_encoding v hv u)
    _ = CanonicalRV.encodeUnit w hw (SubstructureRVGroup.map v w hv hw S f t) :=
      (SubstructureRVGroup.map_agrees v w hv hw S f t).symm

/-- Preparation after obtaining a full residue-field extension. No additional
RV extension assumption remains: group gluing supplies the prepared map. -/
theorem exists_frame_of_residue_extension (ρ : Residue v →+* Residue w)
    (hρ : ∀ a : SubstructureResidue.field v hv S,
      ρ a.val = SubstructureResidue.map v w hv hw S f a) :
    ∃ R : _root_.RVCalc.RV v → _root_.RVCalc.RV w → Prop,
      RVFrame v w ρ R ∧ (∀ x y z, R x y → R x z → y = z) ∧
        ∀ a : SubstructureRVGroup.group v hv S,
          R (some (a : _root_.RVCalc.RVUnit v))
            (some (SubstructureRVGroup.map v w hv hw S f a)) :=
  PreparedRVFrame.exists_frame v w ρ (SubstructureRVGroup.group v hv S)
    (SubstructureRVGroup.map v w hv hw S f)
    (SubstructureRVGroup.map_order v w hv hw S f)
    (intersection_agrees v w hv hw S f ρ hρ)

/-- Genuine tagged saturation and the two explicit standard-field quotations
produce the prepared RV frame of the extension argument. -/
theorem exists_frame
    (hEP : ResidueEmbeddingExtension.EPAlgebraicallyClosedResidue)
    (hACF : ResidueEmbeddingExtension.MarkerACFSaturatedEmbeddingExtension)
    (hSat : MarkerBridge.SatAt LRV N (Order.succ (Cardinal.mk M))) :
    ∃ (ρ : Residue v →+* Residue w) (R : _root_.RVCalc.RV v → _root_.RVCalc.RV w → Prop),
      RVFrame v w ρ R ∧ (∀ x y z, R x y → R x z → y = z) ∧
        ∀ a : SubstructureRVGroup.group v hv S,
          R (some (a : _root_.RVCalc.RVUnit v))
            (some (SubstructureRVGroup.map v w hv hw S f a)) := by
  obtain ⟨ρ, hρ⟩ := ResidueEmbeddingExtension.exists_residue_embedding v w hv hw
    hEP hACF hSat (SubstructureResidue.field v hv S) (SubstructureResidue.map v w hv hw S f)
  obtain ⟨R, hR⟩ := exists_frame_of_residue_extension v w hv hw S f ρ hρ
  exact ⟨ρ, R, hR⟩

end SubstructureRVPreparation

#print axioms SubstructureRVPreparation.kernel_encoding
#print axioms SubstructureRVPreparation.intersection_agrees
#print axioms SubstructureRVPreparation.exists_frame
