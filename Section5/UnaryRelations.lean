import Section5.UnarySets

/-!
# Transporting bounded unary obstacle families

The retained RV labels determine the original labels. On each such slice,
a unary special bijection is a translation, so finite obstacle bounds are
preserved under an arbitrary initial special bijection.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Section5

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {m l : ℕ}
variable {A : DefSet (M := M) S 1 m} {B : DefSet (M := M) S 1 l}

namespace RootFamily

theorem image_fibre_cover (R : RootFamily A) (T : SpecialBijection A B)
    (t : Fin l → RV (M := M)) :
    ∃ F : Finset (VF (M := M)),
      {x | unaryPoint x t ∈ carrier (R.imageSet T.toMap)} ⊆ (F : Set (VF (M := M))) ∧
      ∀ N : ℕ, (∀ u, (R.fibre u).card ≤ N) → F.card ≤ N := by
  by_cases hn : ∃ x : VF (M := M), unaryPoint x t ∈ carrier (R.imageSet T.toMap)
  · obtain ⟨x₀, hx₀⟩ := hn
    obtain ⟨a, ha, hea⟩ := (R.mem_imageSet T.toMap _).mp hx₀
    let c := vfAt (T.toMap a).val 0 - vfAt a.val 0
    let F := (R.fibre a.val.2).image (fun x => x + c)
    refine ⟨F, ?_, fun N hN => (Finset.card_image_le).trans (hN a.val.2)⟩
    intro x hx
    obtain ⟨b, hb, heb⟩ := (R.mem_imageSet T.toMap _).mp hx
    have ht : (T.toMap b).val.2 = (T.toMap a).val.2 :=
      (congrArg Prod.snd heb).trans (congrArg Prod.snd hea).symm
    have hlabels : b.val.2 = a.val.2 := T.chain.labels_eq_of b a ht
    have hdiff := T.chain.unary_sub b a ht
    change vfAt (T.toMap b).val 0 - vfAt (T.toMap a).val 0 = vfAt b.val 0 - vfAt a.val 0 at hdiff
    have hv : vfAt (T.toMap b).val 0 = x := congrArg (fun p : Point (M := M) 1 l => vfAt p 0) heb
    apply Finset.mem_image.mpr
    refine ⟨vfAt b.val 0, ?_, ?_⟩
    · apply (R.mem_fibre _ _).mpr
      rw [← hlabels, unaryPoint_eta]
      exact hb
    · change vfAt b.val 0 + (vfAt (T.toMap a).val 0 - vfAt a.val 0) = x
      rw [hv] at hdiff
      linear_combination -hdiff
  · refine ⟨∅, ?_, by simp⟩
    intro x hx
    exact (hn ⟨x, hx⟩).elim

def push (R : RootFamily A) (T : SpecialBijection A B) : RootFamily B where
  set := R.imageSet T.toMap
  subset := R.imageSet_subset _
  finite t := by
    obtain ⟨F, hF, _⟩ := R.image_fibre_cover T t
    exact F.finite_toSet.subset hF

theorem push_bound (R : RootFamily A) (T : SpecialBijection A B) (N : ℕ)
    (hN : ∀ t, (R.fibre t).card ≤ N) : (R.push T).Bound N := by
  intro t _
  obtain ⟨F, hF, hcard⟩ := R.image_fibre_cover T t
  have hsub : (R.push T).fibre t ⊆ F := by
    intro x hx
    exact hF ((mem_fibre _ _ _).mp hx)
  exact (Finset.card_le_card hsub).trans (hcard N hN)

end RootFamily

def RelationContractible {k : ℕ} (U : Set (Fin (k + 1) → M))
    (T : SpecialBijection A B) : Prop :=
  ∀ b c : B, SameRV b.val c.val → ∀ ys : Fin k → M, (∀ i, iRV (ys i)) →
    (Fin.cons (vfAt (T.inverseMap b).val 0).val ys ∈ U ↔
      Fin.cons (vfAt (T.inverseMap c).val 0).val ys ∈ U)

theorem relation_contractible_of_zero_obstacles {k : ℕ}
    {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VF (M := M)) Γ)
    (hv : ∀ x y : VF (M := M), VFValued.predV x y ↔ v x ≤ v y)
    (U : Set (Fin (k + 1) → M)) (Q : Finset (VF (M := M)))
    (hO : ∀ (a : VF (M := M)) (r : Section3.Balls.Radius Γ),
      (∀ x ∈ Q, x ∉ Section3.Balls.openDisc v a r) →
      ∀ x ∈ Section3.Balls.openDisc v a r, ∀ y ∈ Section3.Balls.openDisc v a r,
      ∀ ys : Fin k → M, (∀ i, iRV (ys i)) → (Fin.cons x.val ys ∈ U ↔ Fin.cons y.val ys ∈ U))
    (T : SpecialBijection A B) (hB : IsRVPullback (carrier B))
    (hz : ∀ a : A, vfAt a.val 0 ∈ Q → vfAt (T.toMap a).val 0 = 0) :
    RelationContractible U T := by
  intro b c hbc ys hys
  obtain ⟨hbcv, hbct⟩ := (sameRV_iff _ _).mp hbc
  by_cases hb : vfAt b.val 0 = 0
  · have hc : vfAt c.val 0 = 0 := (rv_eq_zero_iff _).mp
      ((hbcv 0).symm.trans (congrArg rv hb))
    have he : b = c := by
      apply Subtype.ext
      refine Prod.ext ?_ hbct
      funext i
      fin_cases i
      exact hb.trans hc.symm
    subst c
    rfl
  · obtain ⟨he, _⟩ := T.unary_inverse_fibre v hv hB b hb
    let a := vfAt (T.inverseMap b).val 0
    let ρ : Section3.Balls.Radius Γ := ↑(OrderDual.toDual (v (vfAt b.val 0)))
    have hrad : v (vfAt b.val 0) ≠ 0 := (map_ne_zero v).mpr hb
    have hmem (x : VF (M := M)) (hx : x ∈ Section3.Balls.openDisc v a ρ) :
        unaryPoint x (T.inverseMap b).val.2 ∈ T.inverseFibre b := by
      rw [he]
      refine ⟨?_, rfl⟩
      change v (x - a) < v (vfAt b.val 0)
      simpa only [Section3.Balls.openDisc, ρ, OrderDual.ofDual_toDual, if_neg hrad,
        Set.mem_ofPred_eq] using hx
    have havoid : ∀ x ∈ Q, x ∉ Section3.Balls.openDisc v a ρ := by
      intro x hx hxd
      obtain ⟨u, hu, hrv⟩ := hmem x hxd
      have hval : vfAt u.val 0 = x := congrArg (fun z : Point (M := M) 1 m => vfAt z 0) hu
      have hzero := hz u (by rwa [hval])
      have hh := ((sameRV_iff _ _).mp hrv).1 0
      change rv (vfAt (T.toMap u).val 0) = rv (vfAt b.val 0) at hh
      exact hb ((rv_eq_zero_iff _).mp (hh.symm.trans (congrArg rv hzero)))
    have hcF : (T.inverseMap c).val ∈ T.inverseFibre b :=
      ⟨T.inverseMap c, rfl, by rw [T.apply_inverse]; exact hbc.symm⟩
    rw [he] at hcF
    have hy : vfAt (T.inverseMap c).val 0 ∈ Section3.Balls.openDisc v a ρ := by
      simpa only [Section3.Balls.openDisc, ρ, OrderDual.ofDual_toDual, if_neg hrad,
        Set.mem_ofPred_eq] using hcF.1
    exact hO a ρ havoid a (Section3.Balls.centre_mem_openDisc v a ρ) _ hy ys hys

/-- Uniform preparation of an arbitrary unary definable relation with any
finite tuple of RV variables. These RV values are never named in the base. -/
theorem unary_relation_preparation (h00 : M ⊨ Axioms.ACVF00) {k : ℕ}
    (U : Set (Fin (k + 1) → M)) (hU : Section3.DefinableOver S Section3.MixedPolynomialSyntax.contextSort U)
    {a : ℕ} {A₀ : DefSet (M := M) S 1 a} (hA₀ : IsRVPullback (carrier A₀))
    (τ : SpecialBijection A₀ A) :
    ∃ r : ℕ, ∃ C : DefSet (M := M) S 1 r, ∃ T : SpecialBijection A C,
      ∃ hAlt : (τ.chain.append T.chain).Alternating none, IsRVPullback (carrier C) ∧
        RelationContractible U (τ.comp T hAlt) := by
  obtain ⟨Γ, hΓ, v, hv⟩ := VFValued.exists_valuation_predV (M := M)
  letI := hΓ
  obtain ⟨Q, _, hQ, hO, _⟩ := Section3.mixed_finite_definable_obstacles v hv S U hU
  let R₀ := (obstacleFamily S a Q hQ).restrict A₀ (Set.subset_univ _)
  have hN : ∀ t, (R₀.fibre t).card ≤ Q.card := by
    intro t
    apply Finset.card_le_card
    intro x hx
    have hh := (R₀.mem_fibre _ _).mp hx
    exact hh.1
  let R := R₀.push τ
  obtain ⟨r, C, T, hAlt, hz⟩ := R.centralize_after h00 Q.card (R₀.push_bound τ Q.card hN) τ
  let W := τ.comp T hAlt
  have hC : IsRVPullback (carrier C) := W.preserves_pullback hA₀
  refine ⟨r, C, T, hAlt, hC, ?_⟩
  apply relation_contractible_of_zero_obstacles v hv U Q hO W hC
  intro b hb
  have hR : (τ.toMap b).val ∈ carrier R.set :=
    (R₀.mem_imageSet τ.toMap _).mpr ⟨b, ⟨hb, b.property⟩, rfl⟩
  have hh := hz (τ.toMap b) hR
  have hmap : W.toMap = Map.comp T.toMap τ.toMap := τ.chain.append_toMap T.chain
  rw [hmap]
  exact hh

end SpecialTransformations.Section5
