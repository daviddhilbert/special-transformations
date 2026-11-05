import ValuedModelMap
import ValuedReduct

set_option backward.isDefEq.respectTransparency false

/-! The whole-model finish after the RV data have been represented in a VF
subfield. The existence of the whole valued-field extension is an explicit
input here. Agreement on the old RV elements is proved from representatives;
it is not inserted into the definition of saturation. -/

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer

namespace VFGeneratedFinish

variable {M N : Type} [LRV.Structure M] [LRV.Structure N]
variable [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]

/-- An actual valued-field extension of a map on a subfield. No saturation or
existence assertion is part of this data structure. -/
structure ValuedExtension (K : Subfield (VFType (M := M)))
    (g : K →+* VFType (M := N)) where
  hom : VFType (M := M) →+* VFType (M := N)
  comparison : ∀ a b, VFValued.predV (hom a) (hom b) ↔ VFValued.predV a b
  agrees : ∀ a : K, hom a.1 = g a

def ContainsVF (S : LRV.Substructure M) (K : Subfield (VFType (M := M))) : Prop :=
  ∀ (a : S) (ha : iVF (a : M)), (⟨(a : M), ha⟩ : VFType (M := M)) ∈ K

def AgreesVF (S : LRV.Substructure M) (K : Subfield (VFType (M := M)))
    (f : S ↪[LRV] N) (g : K →+* VFType (M := N)) (hK : ContainsVF S K) : Prop :=
  ∀ (a : S) (ha : iVF (a : M)), (g ⟨⟨(a : M), ha⟩, hK a ha⟩).1 = f a

/-- The field stage has supplied representatives and their prescribed images
for all old RV elements. Representatives may lie in K outside the old S. -/
def RepresentsRV (S : LRV.Substructure M) (K : Subfield (VFType (M := M)))
    (f : S ↪[LRV] N) (g : K →+* VFType (M := N)) : Prop :=
  ∀ (x : S), iRV (x : M) → ∃ a : K,
    iRv a.1.1 = (x : M) ∧ iRv (g a).1 = f x

/-- The stronger, convenient terminal condition: each old RV element already
has a VF representative in the same substructure. -/
def VFGenerated (S : LRV.Substructure M) : Prop :=
  ∀ (x : S), iRV (x : M) → ∃ a : S, iVF (a : M) ∧ iRv (a : M) = (x : M)

private theorem map_rv {A B : Type} [LRV.Structure A] [LRV.Structure B]
    (f : A ↪[LRV] B) (a : A) : f (iRv a) = iRv (f a) := by
  have hvec : (⇑f ∘ ![a]) = ![f a] := by funext i; fin_cases i; rfl
  have h := f.map_fun Fn.rvMap ![a]
  rw [hvec] at h
  exact h

theorem representsRV_of_VFGenerated (S : LRV.Substructure M)
    (K : Subfield (VFType (M := M))) (f : S ↪[LRV] N) (g : K →+* VFType (M := N))
    (hK : ContainsVF S K) (hagrees : AgreesVF S K f g hK) (hgen : VFGenerated S) :
    RepresentsRV S K f g := by
  intro x hx
  obtain ⟨a, ha, he⟩ := hgen x hx
  refine ⟨⟨⟨(a : M), ha⟩, hK a ha⟩, he, ?_⟩
  rw [hagrees a ha]
  have hs : (iRv a : S) = x :=
    Subtype.ext ((map_rv (Substructure.subtype S) a).trans he)
  exact (map_rv f a).symm.trans (congrArg f hs)

section Finish

variable {S : LRV.Substructure M} {K : Subfield (VFType (M := M))}
variable {f : S ↪[LRV] N} {g : K →+* VFType (M := N)}
variable (e : ValuedExtension K g)

noncomputable def sortedFinish : CanonicalStructure.SortedEmbedding M N :=
  ValuedModelMap.toSortedEmbedding e.hom e.comparison

theorem sortedFinish_vf (a : VFType (M := M)) :
    (sortedFinish e).toFun a.1 = (e.hom a).1 := by
  change (ValuedModelMap.components e.hom e.comparison).carrierMap a.1 = _
  exact (ValuedModelMap.components e.hom e.comparison).carrierMap_vf a.2

theorem sortedFinish_rv (a : VFType (M := M)) :
    (sortedFinish e).toFun (iRv a.1) = iRv (e.hom a).1 := by
  change (ValuedModelMap.components e.hom e.comparison).carrierMap (iRv a.1) = _
  rw [TypedModelMap.Components.carrierMap_rv _ (rv_mem hM a.2)]
  change (ValuedModelMap.rvMap e.hom (CanonicalRV.encodedRv a)).1 = _
  rw [ValuedModelMap.rvMap_encodedRv e.hom e.comparison]
  rfl

/-- Extending the valued field map also extends every old RV element whose
representative and prescribed leading term have been supplied at the field stage. -/
theorem sortedFinish_agrees (hK : ContainsVF S K) (hVF : AgreesVF S K f g hK)
    (hRV : RepresentsRV S K f g) (x : S) : (sortedFinish e).toFun (x : M) = f x := by
  rcases TypedModelMap.sort_cover (x : M) with hx | hx
  · let a : K := ⟨⟨(x : M), hx⟩, hK x hx⟩
    have hf : (sortedFinish e).toFun (x : M) = (e.hom a.1).1 := sortedFinish_vf e a.1
    rw [e.agrees a] at hf
    exact hf.trans (hVF x hx)
  · obtain ⟨a, ha, hb⟩ := hRV x hx
    rw [← ha, sortedFinish_rv e a.1, e.agrees a]
    exact hb

/-- The ordinary embedding into the canonical totalizations has the same
underlying map as the sorted finish. -/
noncomputable def normalizedFinish :
    @FirstOrder.Language.Embedding LRV M N
      (CanonicalStructure.normalize (M := M)) (CanonicalStructure.normalize (M := N)) :=
  (sortedFinish e).toCanonicalEmbedding hM hN

theorem normalizedFinish_agrees (hK : ContainsVF S K) (hVF : AgreesVF S K f g hK)
    (hRV : RepresentsRV S K f g) (x : S) : normalizedFinish e (x : M) = f x :=
  sortedFinish_agrees e hK hVF hRV x

/-- When the ambient models already satisfy the explicit canonical axioms,
the finish is an ordinary LRV embedding of those very models. -/
noncomputable def canonicalFinish (hcM : CanonicalStructure.IsCanonical (M := M))
    (hcN : CanonicalStructure.IsCanonical (M := N)) : M ↪[LRV] N :=
  (sortedFinish e).toLRVEmbedding hM hN hcM hcN

theorem canonicalFinish_agrees (hcM : CanonicalStructure.IsCanonical (M := M))
    (hcN : CanonicalStructure.IsCanonical (M := N)) (hK : ContainsVF S K)
    (hVF : AgreesVF S K f g hK) (hRV : RepresentsRV S K f g) (x : S) :
    canonicalFinish e hcM hcN (x : M) = f x :=
  sortedFinish_agrees e hK hVF hRV x

include e in
/-- Remark 3.1's final language-level step, after the valued-field extension:
RV-surjectivity inside S makes the separate old-RV agreement automatic. -/
theorem finish_VFGenerated (hcM : CanonicalStructure.IsCanonical (M := M))
    (hcN : CanonicalStructure.IsCanonical (M := N)) (hK : ContainsVF S K)
    (hVF : AgreesVF S K f g hK) (hgen : VFGenerated S) :
    ∃ F : M ↪[LRV] N, ∀ x : S, F (x : M) = f x := by
  refine ⟨canonicalFinish e hcM hcN, ?_⟩
  exact canonicalFinish_agrees e hcM hcN hK hVF
    (representsRV_of_VFGenerated S K f g hK hVF hgen)

end Finish
end VFGeneratedFinish

#print axioms VFGeneratedFinish.representsRV_of_VFGenerated
#print axioms VFGeneratedFinish.sortedFinish_agrees
#print axioms VFGeneratedFinish.normalizedFinish_agrees
#print axioms VFGeneratedFinish.finish_VFGenerated
