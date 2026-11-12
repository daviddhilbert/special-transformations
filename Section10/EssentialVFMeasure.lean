module

public import Section10.EssentialVFGerms

@[expose] public section

/-! Measure equations on the actual fixed-label charts of essential maps.
The chain rule and inverse rule are applied after a definable small cut. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9

noncomputable section

namespace SpecialTransformations.Section10.EssentialVFMap

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r s t : ℕ}
local notation "VF" => VFType (M := M)
local notation "Δ" => rawRVSpace (M := M) 1
local notation "X" => Fin n → VF

section Charts

variable {S : Set M}
variable {A A' : DefSet (rawMixedSpace (M := M) n r) S}
variable {B B' : DefSet (rawMixedSpace (M := M) n s) S}

private theorem jacobian_eq_of_restriction (f : Map A B) (g : Map A' B')
    (i : A' → A) (hi : ∀ p, (i p).val = p.val) (he : ∀ p, (g p).val = (f (i p)).val)
    (p : A') {J K : VF} (hJ : HasMixedVFJacobianAt f (i p) J) (hK : HasMixedVFJacobianAt g p K) :
    J = K := by
  obtain ⟨F, ⟨ρ, hρ⟩, hf⟩ := hJ
  obtain ⟨G, ⟨σ, hσ⟩, hg⟩ := hK
  have hball : Set.EqOn F G (vfBall p.val.1 (max ρ σ)) := by
    intro x hx
    obtain ⟨ha, hfa⟩ := hρ x (by rw [hi]; exact vfBall_anti (le_max_left _ _) hx)
    obtain ⟨hb, hgb⟩ := hσ x (vfBall_anti (le_max_right _ _) hx)
    let b : A' := ⟨(x, p.val.2), hb⟩
    have hab : (⟨(x, (i p).val.2), ha⟩ : A) = i b := by
      apply Subtype.ext
      change (x, (i p).val.2) = (i b).val
      rw [hi b]
      exact congrArg (Prod.mk x) (congrArg Prod.snd (hi p))
    have hf' := congrArg Prod.fst hfa
    rw [hab, ← he] at hf'
    exact hf'.symm.trans (congrArg Prod.fst hgb)
  have hf' : HasVFJacobianAt F p.val.1 J := by simpa only [hi] using hf
  exact (hf'.congr_on_vfBall hball).unique hg

private theorem identity_jacobian_of_chart {f : A → A} (hf : ∀ p, f p = p)
    (p : A) {J : VF} (hJ : HasMixedVFJacobianAt f p J) : J = 1 := by
  have hchart := hJ
  obtain ⟨_, ⟨ρ, hρ⟩, _⟩ := hchart
  have hId : IsVFChartAt f p (fun x : X => x) := by
    refine ⟨ρ, fun x hx => ?_⟩
    obtain ⟨ha, _⟩ := hρ x hx
    exact ⟨ha, by simp only [hf]⟩
  have hd : HasVFDerivativeAt (fun x : X => x) p.val.1 LinearMap.id := by
    simpa only [LinearMap.id_apply, add_zero] using
      hasVFDerivativeAt_affine (LinearMap.id : X →ₗ[VF] X) 0 p.val.1
  apply hJ.unique
  refine ⟨_, hId, ?_⟩
  simpa only [LinearMap.toMatrix'_id, Matrix.det_one] using hd.hasJacobianAt

end Charts

variable {G : Type} [CommMonoidWithZero G]
variable {S : Set M}
variable {A : DefSet (rawMixedSpace (M := M) n r) S}
variable {B : DefSet (rawMixedSpace (M := M) n s) S}

/-- The pointwise equation for an RV or Gamma weight after applying the
corresponding multiplicative homomorphism to the determinant. -/
def Preserves (j : VF →*₀ G) (a : A → G) (b : B → G) (f : EssentialVFMap A B) : Prop :=
  ∀ p : f.source, ∃ J : VF, HasMixedVFJacobianAt f.map p J ∧
    a ⟨p.val, f.source_subset p.property⟩ =
      b ⟨(f.map p).val, f.target_subset (f.map p).property⟩ * j J

variable (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal}
variable (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hS : Cardinal.mk S < κ) (hn : 0 < n)

include hs hS hn in
private theorem refine_preserves (j : VF →*₀ G) (a : A → G) (b : B → G)
    (f : EssentialVFMap A B) (Z : DefSet (rawMixedSpace (M := M) n r) S) (hZ : vfDim Δ Z < n)
    (h : ∀ p : f.source, p.val ∉ Z.carrier → ∃ J : VF, HasMixedVFJacobianAt f.map p J ∧
      a ⟨p.val, f.source_subset p.property⟩ =
        b ⟨(f.map p).val, f.target_subset (f.map p).property⟩ * j J) :
    ∃ g : EssentialVFMap A B, Preserves j a b g ∧ g.genericEquiv hc = f.genericEquiv hc := by
  obtain ⟨g, hg⟩ := exists_restriction_preserving_jacobian hc hs hS hn f.map f.bijective Z hZ
  let e := g.widen hc hs hS f.source_subset f.target_subset f.source_small f.target_small
  refine ⟨e, ?_, ?_⟩
  · intro p
    obtain ⟨hz, hv, hj⟩ := hg p
    let q : f.source := ⟨p.val, g.source_subset p.property⟩
    obtain ⟨J, hJ, hw⟩ := h q hz
    refine ⟨J, hj J hJ, ?_⟩
    have hb : (⟨(e.map p).val, e.target_subset (e.map p).property⟩ : B) =
        ⟨(f.map q).val, f.target_subset (f.map q).property⟩ := Subtype.ext hv
    rwa [hb]
  · apply Equiv.ext
    intro p
    apply Subtype.ext
    apply Subtype.ext
    exact (hg (⟨p.val.val, mem_of_small_complement hc e.source e.source_small p⟩ : e.source)).2.1

include hκ hs hS hn in
theorem exists_preserving_id [CharZero VF] (j : VF →*₀ G) (a : A → G) :
    ∃ f : EssentialVFMap A A, Preserves j a a f ∧ f.genericEquiv hc = Equiv.refl (Generic A) := by
  let f := id A hn
  obtain ⟨Z, _, hZ, hJ⟩ := lemma_9_12_ae hc hκ hs hS hn f.map f.map
    (Map.finiteFibres_of_injective f.bijective.injective)
  obtain ⟨g, hg, he⟩ := refine_preserves hc hs hS hn j a a f Z hZ (by
    intro p hp
    obtain ⟨J, _, hJ, _⟩ := hJ p hp
    have hOne := identity_jacobian_of_chart (f := f.map) (fun _ => rfl) p hJ
    exact ⟨1, hOne ▸ hJ, by simp only [map_one, mul_one]; rfl⟩)
  refine ⟨g, hg, he.trans ?_⟩
  apply Equiv.ext
  intro p
  rfl

include hκ hs hS hn in
theorem exists_preserving_symm [CharZero VF] (j : VF →*₀ G) (a : A → G) (b : B → G)
    (f : EssentialVFMap A B) (hf : Preserves j a b f) :
    ∃ g : EssentialVFMap B A, Preserves j b a g ∧ g.genericEquiv hc = (f.genericEquiv hc).symm := by
  let i := f.symm
  obtain ⟨Z, _, hZ, hJ⟩ := lemma_9_12_ae hc hκ hs hS hn i.map f.map
    (Map.finiteFibres_of_injective i.bijective.injective)
  obtain ⟨g, hg, he⟩ := refine_preserves hc hs hS hn j b a i Z hZ (by
    intro p hp
    obtain ⟨J, K, hJ, hK, hC⟩ := hJ p hp
    have hprod : K * J = 1 := identity_jacobian_of_chart (fun q => Map.apply_inverse f.map f.bijective q) p hC
    obtain ⟨L, hL, hw⟩ := hf (i.map p)
    rw [hL.unique hK] at hw
    have he : f.map (i.map p) = p := Map.apply_inverse f.map f.bijective p
    have hb : (⟨(f.map (i.map p)).val, f.target_subset (f.map (i.map p)).property⟩ : B) =
        ⟨p.val, f.target_subset p.property⟩ := Subtype.ext (congrArg (fun q : f.target => q.val) he)
    refine ⟨J, hJ, ?_⟩
    change b ⟨p.val, f.target_subset p.property⟩ =
      a ⟨(i.map p).val, f.source_subset (i.map p).property⟩ * j J
    rw [hw, hb, mul_assoc, ← map_mul, hprod, map_one, mul_one])
  exact ⟨g, hg, he.trans (genericEquiv_symm hc f)⟩

include hκ hs hS hn in
theorem exists_preserving_comp [CharZero VF] (j : VF →*₀ G)
    {C : DefSet (rawMixedSpace (M := M) n t) S} (a : A → G) (b : B → G) (c : C → G)
    (f : EssentialVFMap A B) (g : EssentialVFMap B C)
    (hf : Preserves j a b f) (hg : Preserves j b c g) :
    ∃ e : EssentialVFMap A C, Preserves j a c e ∧
      e.genericEquiv hc = (f.genericEquiv hc).trans (g.genericEquiv hc) := by
  let e := comp hc hs hS hn f g
  let m := f.compMiddle g
  obtain ⟨Z, _, hZ, hJ⟩ := lemma_9_12_ae hc hκ hs hS hn m g.map
    (Map.finiteFibres_of_injective (f.compMiddle_injective g))
  obtain ⟨e', he', he⟩ := refine_preserves hc hs hS hn j a c e Z hZ (by
    intro p hp
    obtain ⟨J, K, hJ, hK, hC⟩ := hJ p hp
    let i (x : e.source) : f.source := ⟨x.val, f.compSource_subset g x.property⟩
    obtain ⟨L, hL, hw⟩ := hf (i p)
    have hLJ := jacobian_eq_of_restriction f.map m i (fun _ => rfl) (fun _ => rfl) p hL hJ
    obtain ⟨D, hD, hv⟩ := hg (m p)
    rw [hLJ] at hw
    rw [hD.unique hK] at hv
    refine ⟨K * J, ?_, ?_⟩
    · obtain ⟨F, hF, hdet⟩ := hC
      exact ⟨F, hF, hdet⟩
    · calc
        _ = b ⟨(m p).val, g.source_subset (m p).property⟩ * j J := hw
        _ = _ := by
          rw [hv, mul_assoc, map_mul]
          rfl)
  exact ⟨e', he', he.trans (genericEquiv_comp hc hs hS hn f g)⟩

end SpecialTransformations.Section10.EssentialVFMap
