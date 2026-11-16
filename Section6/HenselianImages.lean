module

public import Section6.HenselianInputs
public import Section6.CanonicalEmbedding

@[expose] public section

/-! Transport the independent henselian/envelope data into a common
native ACVF model. The algebraic field, its actual henselian valuation
ring and the standard valuation-invariance input remain the original
ones. No definable-closure or elimination assertion is transported as
an assumed input.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Section6

variable {C D : Type} [LRV.Structure C] [LRV.Structure D]
variable [hC : C ⊨ Axioms.ACVF] [hD : D ⊨ Axioms.ACVF]

theorem HenselianInputs.map {X : LRV.Substructure C} (h : HenselianInputs X)
    (hc : CanonicalStructure.IsCanonical (M := C))
    (hd : CanonicalStructure.IsCanonical (M := D)) (j : C ↪ₑ[LRV] D) :
    HenselianInputs (X.map j.toEmbedding.toHom) := by
  have hsurj : ∀ t : Section5.RV (M := D), t.val ∈ X.map j.toEmbedding.toHom →
      ∃ a : Section5.VF (M := D), a.val ∈ X.map j.toEmbedding.toHom ∧ Section5.rv a = t := by
    intro t ht
    obtain ⟨u, hu, hj⟩ := ht
    have huRV : iRV u := by
      have hrel := j.map_rel (r := Rel.memRV) ![u]
      have he : j ∘ ![u] = ![j u] := by funext i; fin_cases i; rfl
      rw [he] at hrel
      exact hrel.mp (hj ▸ t.property)
    let q : Section5.RV (M := C) := ⟨u, huRV⟩
    obtain ⟨a, ha, he⟩ := h.rv_surjective q hu
    have hja : iVF (j a.val) := by
      have hr := j.map_rel (r := Rel.memVF) ![a.val]
      have he : j ∘ ![a.val] = ![j a.val] := by funext i; fin_cases i; rfl
      rw [he] at hr
      exact hr.mpr a.property
    let b : Section5.VF (M := D) := ⟨j a.val, hja⟩
    refine ⟨b, ⟨a.val, ha, rfl⟩, ?_⟩
    apply Subtype.ext
    have hf := j.map_fun Fn.rvMap ![a.val]
    have hh : j ∘ ![a.val] = ![j a.val] := by funext i; fin_cases i; rfl
    rw [hh] at hf
    have hraw : iRv a.val = u := congrArg Subtype.val he
    change iRv (j a.val) = t.val
    exact hf.symm.trans ((congrArg j hraw).trans hj)
  cases h with
  | @of_envelope N sN hN Y k himage Γ instΓ v hv K instG hK hRV hH hEP hCenters hRVsurj =>
    let k' := @ElementaryEmbedding.comp LRV N C D
      (@CanonicalStructure.normalize N sN)
      (CanonicalStructure.normalize (M := C)) (CanonicalStructure.normalize (M := D))
      (CanonicalEmbedding.normalized hc hd j) k
    have himage' : k' '' (Y : Set _) = (X.map j.toEmbedding.toHom : Set D) := by
      have he : (k' : _ → D) = j ∘ k := by
        funext x
        change (CanonicalEmbedding.normalized hc hd j) (k x) = j (k x)
        exact CanonicalEmbedding.normalized_apply hc hd j (k x)
      rw [he]
      change (j ∘ k) '' (Y : Set _) = j '' (X : Set C)
      rw [Set.image_comp, himage]
    exact HenselianInputs.of_envelope Y k' himage' v hv K hK hRV hH hEP hCenters hsurj

end SpecialTransformations.Section6
