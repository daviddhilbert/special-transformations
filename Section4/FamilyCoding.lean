import Section4.UniformFinite
import Section3.RawBarycentricCode

set_option backward.isDefEq.respectTransparency false

/-!
# Uniform codes for finite VF fibres

This combines the given Section 3 barycentric code with the uniform bound
proved from genuine saturation. The code depends only on the actual finite
fibre, so changing a real representative of an imaginary parameter does not
change it.
-/

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n : ℕ}

def vfFibre (R : Set ((Fin n → M) × M)) (t : Fin n → M) :
    Set (VFType (M := M)) := {x | (t, x.val) ∈ R}

theorem vfFibre_finite (R : Set ((Fin n → M) × M))
    (hfinite : ∀ t, {x | (t, x) ∈ R}.Finite) (t : Fin n → M) :
    (vfFibre R t).Finite := by
  change ((Subtype.val : VFType (M := M) → M) ⁻¹' {x | (t, x) ∈ R}).Finite
  exact (hfinite t).preimage Subtype.val_injective.injOn

noncomputable def vfFamily (R : Set ((Fin n → M) × M))
    (hfinite : ∀ t, {x | (t, x) ∈ R}.Finite) (t : Fin n → M) :
    Finset (VFType (M := M)) := (vfFibre_finite R hfinite t).toFinset

@[simp] theorem mem_vfFamily (R : Set ((Fin n → M) × M))
    (hfinite : ∀ t, {x | (t, x) ∈ R}.Finite) (t : Fin n → M) (x : VFType (M := M)) :
    x ∈ vfFamily R hfinite t ↔ (t, x.val) ∈ R := Set.Finite.mem_toFinset _

theorem vfFamily_relation (R : Set ((Fin n → M) × M))
    (hfinite : ∀ t, {x | (t, x) ∈ R}.Finite)
    (hsort : ∀ t x, (t, x) ∈ R → iVF x) :
    Barycentre.finiteFibreRelation (vfFamily R hfinite) = R := by
  ext p
  constructor
  · rintro ⟨x, hx, he⟩
    change (p.1, p.2) ∈ R
    rw [← he]
    exact (mem_vfFamily R hfinite p.1 x).mp hx
  · intro hp
    exact ⟨⟨p.2, hsort p.1 p.2 hp⟩, (mem_vfFamily R hfinite p.1 _).mpr hp, rfl⟩

theorem vfFamily_card (R : Set ((Fin n → M) × M))
    (hfinite : ∀ t, {x | (t, x) ∈ R}.Finite)
    (hsort : ∀ t x, (t, x) ∈ R → iVF x) (t : Fin n → M) :
    (vfFamily R hfinite t).card = {x | (t, x) ∈ R}.ncard := by
  have he : Subtype.val '' (vfFamily R hfinite t : Set (VFType (M := M))) =
      {x | (t, x) ∈ R} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (mem_vfFamily R hfinite t y).mp hy
    · intro hx
      exact ⟨⟨x, hsort t x hx⟩, (mem_vfFamily R hfinite t _).mpr hx, rfl⟩
  rw [← he, Set.ncard_image_of_injective _ Subtype.val_injective, Set.ncard_coe_finset]

theorem vfFamily_eq_of_fibre_eq (R : Set ((Fin n → M) × M))
    (hfinite : ∀ t, {x | (t, x) ∈ R}.Finite) (t u : Fin n → M)
    (he : ∀ x, (t, x) ∈ R ↔ (u, x) ∈ R) :
    vfFamily R hfinite t = vfFamily R hfinite u := by
  ext x
  simp only [mem_vfFamily]
  exact he x.val

theorem uniform_vf_fibre_coding (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hs : Saturated M κ) (S : Set M) (hsmall : Cardinal.mk S < κ)
    (R : Set ((Fin n → M) × M)) (hR : RawClosure.Tuple.RelationDefinable S R)
    (hfinite : ∀ t, {x | (t, x) ∈ R}.Finite)
    (hsort : ∀ t x, (t, x) ∈ R → iVF x) :
    ∃ d : ℕ,
      (∀ t, Set.InjOn (fun x : VFType (M := M) =>
        Barycentre.rawCode d (vfFamily R hfinite) t x.val) (vfFibre R t)) ∧
      (∀ j : Fin d, S.DefinableFun LRV (fun w : Fin n ⊕ Fin 1 → M =>
        Barycentre.rawCode d (vfFamily R hfinite) (w ∘ Sum.inl) (w (.inr 0)) j)) ∧
      (∀ t (x : VFType (M := M)) j,
        iRV (Barycentre.rawCode d (vfFamily R hfinite) t x.val j)) := by
  obtain ⟨d, hd⟩ := uniform_finite_fibre_bound hs S hsmall R hR hfinite
  have hb (t : Fin n → M) : (vfFamily R hfinite t).card ≤ d := by
    rw [vfFamily_card R hfinite hsort]
    exact hd t
  have hF : RawClosure.Tuple.RelationDefinable S
      (Barycentre.finiteFibreRelation (vfFamily R hfinite)) := by
    rwa [vfFamily_relation R hfinite hsort]
  refine ⟨d, ?_, ?_, ?_⟩
  · intro t x hx y hy he
    have he' : Barycentre.code d (vfFamily R hfinite t) x =
        Barycentre.code d (vfFamily R hfinite t) y := by
      simpa only [Barycentre.rawCode_eq_code] using he
    exact Barycentre.code_injective_of_card_le h00 d (vfFamily R hfinite t)
      ((hb t).trans (Nat.le_succ d))
      ((mem_vfFamily R hfinite t x).mpr hx) ((mem_vfFamily R hfinite t y).mpr hy) he'
  · exact Barycentre.rawCode_definable h00 S d (vfFamily R hfinite) hF d hb
  · intro t x j
    rw [Barycentre.rawCode_eq_code]
    exact Barycentre.code_sorted d (vfFamily R hfinite t) x j

theorem code_eq_of_fibre_eq (R : Set ((Fin n → M) × M))
    (hfinite : ∀ t, {x | (t, x) ∈ R}.Finite) (t u : Fin n → M)
    (he : ∀ x, (t, x) ∈ R ↔ (u, x) ∈ R) (d : ℕ) (x : VFType (M := M)) :
    Barycentre.rawCode d (vfFamily R hfinite) t x.val =
      Barycentre.rawCode d (vfFamily R hfinite) u x.val := by
  simp only [Barycentre.rawCode_eq_code, vfFamily_eq_of_fibre_eq R hfinite t u he]

end SpecialTransformations.Section4
