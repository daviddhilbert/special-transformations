import JohnsonValuedBridge
import JohnsonSubfield
import QESaturatedExtension

/-! The ordinary valued-field extension step used by RV quantifier elimination,
proved from the repository's Johnson theorem and genuine saturation.
No ordinary valued-field QE or embedding-extension theorem is assumed. -/

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
set_option backward.isDefEq.respectTransparency false

namespace JohnsonValuedExtension

/-- The former Marker-notes input is now a theorem, obtained from Johnson's QE
proof, a proved generic saturation argument, and the exact language translation. -/
theorem markerNotesProposition45 : ValuedFieldExtension.MarkerNotesProposition45 := by
  intro E F Γ Δ hE hF hEac hFac hΓ hΔ sE sF v w hv hw hntE hntF hSat A g hg
  letI : Language.val.Structure E := FirstOrder.valStructure v
  letI : Language.val.Structure F := FirstOrder.valStructure w
  have hExtension := QESaturatedExtension.extension_of_fullQE
    JohnsonValuedBridge.fullQE_ACVF_val
  obtain ⟨G, hG⟩ := hExtension E F
    (JohnsonValuedBridge.model_ACVF_val v hntE)
    (JohnsonValuedBridge.model_ACVF_val w hntF)
    (JohnsonValuedBridge.satAt_johnson w hw hSat)
    (subfieldSubstructure v A) (subfieldEmbedding v w A g hg)
  refine ⟨ValOneEC.ringHomOfEmbedding v w G, ?_, ?_⟩
  · intro a
    exact hG ⟨a.1, a.2⟩
  · intro a b
    exact G.map_rel' ValRel.le ![a, b]

section RVModels

variable {M N : Type} [LRV.Structure M] [LRV.Structure N]
  [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF]

/-- Extend the actual VF subfield map in the RV proof, with no ordinary
valued-field theorem supplied by the caller. -/
theorem valuedExtension_of_johnson
    (hSat : MarkerBridge.SatAt LRV N (Order.succ (Cardinal.mk M)))
    (K : Subfield (VFType (M := M))) (g : K →+* VFType (M := N))
    (hg : ∀ a b : K, VFValued.predV (g a) (g b) ↔ VFValued.predV a.1 b.1) :
    Nonempty (VFGeneratedFinish.ValuedExtension K g) :=
  ValuedFieldExtension.valuedExtension_of_notes markerNotesProposition45 hSat K g hg

end RVModels
end JohnsonValuedExtension

#print axioms JohnsonValuedExtension.markerNotesProposition45
#print axioms JohnsonValuedExtension.valuedExtension_of_johnson
