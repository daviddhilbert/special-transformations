import Section4.RVIsoTools

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] {S : Set M} {k : ℕ}

/-- A definable bijection of domains induces an RV isomorphism when its
labels differ by a fixed weight-preserving permutation. No choice of
representatives, nor any definability of a section, is needed. -/
def rvIsoOfLabelEquiv {U V : RVObject (M := M) S k}
    (F : Map U.domain V.domain) (hF : Function.Bijective F)
    (c : (Fin k → CanonicalRV.RVSort M) ≃ (Fin k → CanonicalRV.RVSort M))
    (hw : ∀ t, rvWeight (c t) = rvWeight t)
    (hvol : ∀ a, V.value (F a) = c (U.value a)) : U ≅ V where
  hom := {
    map := F
    volumetric a := by rw [hvol a, hw]
    finite_volume_images t := by
      apply (Set.finite_singleton (c t)).subset
      rintro s ⟨a, ha, hs⟩
      exact Set.mem_singleton_iff.mpr (hs.symm.trans ((hvol a).trans (congrArg c ha))) }
  inv := {
    map := F.inverse hF
    volumetric b := by
      have h := hvol (F.inverse hF b)
      rw [Map.apply_inverse] at h
      rw [h, hw]
    finite_volume_images t := by
      apply (Set.finite_singleton (c.symm t)).subset
      rintro s ⟨b, hb, hs⟩
      have h := hvol (F.inverse hF b)
      rw [Map.apply_inverse, hb] at h
      apply Set.mem_singleton_iff.mpr
      apply c.injective
      rw [c.apply_symm_apply, ← hs]
      exact h.symm }
  hom_inv_id := by apply RVHom.ext; apply Map.ext; intro a; exact Map.inverse_apply F hF a
  inv_hom_id := by apply RVHom.ext; apply Map.ext; intro b; exact Map.apply_inverse F hF b

end SpecialTransformations.Section4

end
