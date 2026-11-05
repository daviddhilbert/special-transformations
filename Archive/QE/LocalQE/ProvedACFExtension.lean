import JohnsonACFMain
import QESaturatedExtension
import ResidueEmbeddingExtension

/-! The pure algebraically closed field extension step, now proved.

Johnson's existing ACF proof gives full ring-language QE. The checked generic
QE-to-saturation argument then extends embeddings of subfields, viewed as
ring-language substructures. Thus the former Marker ACF extension input is a
closed theorem, without a characteristic restriction or any new hypothesis.
-/

open FirstOrder FirstOrder.Language FirstOrder.Ring

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

namespace ProvedACFExtension

/-- The checked bounded QE theorem in the semantic interface used by the
generic saturated extension argument. -/
theorem fullQE : MarkerBridge.FullQE ACFValidation.acf := by
  intro α n φ
  obtain ⟨ψ, hqf, heq⟩ := JohnsonACF.hasQEb α n φ
  refine ⟨ψ, hqf, ?_⟩
  intro K sK hK a xs
  letI := sK
  letI := hK
  letI : Nonempty K :=
    ⟨Structure.funMap (L := Language.ring) zeroFunc (fun i => i.elim0)⟩
  have h := heq (Theory.ModelType.of (T := ACFValidation.acf) K) a xs
  simpa only [BoundedFormula.realize_iff] using h

section Subfields

variable {K L : Type} [Field K] [Field L] [CompatibleRing K] [CompatibleRing L]

/-- A subfield is closed under each symbol of the ordinary ring language. -/
def subfieldSubstructure (A : Subfield K) : Language.ring.Substructure K where
  carrier := A
  fun_mem := by
    intro n f xs hxs
    cases f with
    | add => simpa using A.add_mem (hxs 0) (hxs 1)
    | mul => simpa using A.mul_mem (hxs 0) (hxs 1)
    | neg => simpa using A.neg_mem (hxs 0)
    | zero => simpa using A.zero_mem
    | one => simpa using A.one_mem

/-- A field embedding has precisely the required ring-language behavior. -/
def subfieldEmbedding (A : Subfield K) (σ : A →+* L) :
    subfieldSubstructure A ↪[Language.ring] L := by
  letI : Field (subfieldSubstructure A) := inferInstanceAs (Field A)
  letI : CompatibleRing (subfieldSubstructure A) :=
    { toStructure := Substructure.inducedStructure
      funMap_add := by
        intro xs
        apply Subtype.ext
        exact CompatibleRing.funMap_add (fun i => (xs i).1)
      funMap_mul := by
        intro xs
        apply Subtype.ext
        exact CompatibleRing.funMap_mul (fun i => (xs i).1)
      funMap_neg := by
        intro xs
        apply Subtype.ext
        exact CompatibleRing.funMap_neg (fun i => (xs i).1)
      funMap_zero := by
        intro xs
        apply Subtype.ext
        exact CompatibleRing.funMap_zero (fun i => (xs i).1)
      funMap_one := by
        intro xs
        apply Subtype.ext
        exact CompatibleRing.funMap_one (fun i => (xs i).1) }
  exact ACFValidation.embeddingOfInjectiveRingHom σ σ.injective

end Subfields

/-- The former standard ACF extension hypothesis follows from checked QE and
genuine saturation; it is not an additional assumption of the RV proof. -/
theorem markerACFSaturatedEmbeddingExtension :
    ResidueEmbeddingExtension.MarkerACFSaturatedEmbeddingExtension := by
  intro K L hK hL hKac hLac hCK hCL hSat A σ
  obtain ⟨G, hG⟩ := (QESaturatedExtension.extension_of_fullQE fullQE) K L
    (inferInstance : K ⊨ ACFValidation.acf)
    (inferInstance : L ⊨ ACFValidation.acf)
    hSat (subfieldSubstructure A) (subfieldEmbedding A σ)
  refine ⟨ACFValidation.ringHomOfEmbedding G, ?_⟩
  intro a
  exact hG ⟨a.1, a.2⟩

end ProvedACFExtension

#print axioms ProvedACFExtension.fullQE
#print axioms ProvedACFExtension.subfieldEmbedding
#print axioms ProvedACFExtension.markerACFSaturatedEmbeddingExtension
