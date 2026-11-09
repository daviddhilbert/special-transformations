import Section7.BalancedCorrespondence
import Section7.PullbackLiftRelations
import Section4.LiftMorphism
import Section4.CanonicalNormalization
import Section4.FunctionalRelations
import Section4.VFAllScissors
import Section4.VFFiniteScissors
import Section4.RVScissorPresentation
import Section4.GradedLifts

section VolumeCorrespondenceProof

/-!
# The actual volume correspondence of an RV isomorphism

The morphism's forward finite-volume condition controls the right
rows; the inverse controls the left rows. Both weight inequalities
give equality. This uses the graph of the given definable map.
-/

open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

set_option backward.isDefEq.respectTransparency false

namespace SpecialTransformations.Section7

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}
variable {U V : RVObject (M := M) S k}

def rawVolumeCorrespondence (F : Map U.domain V.domain) : Set (Fin (k + k) → M) :=
  {z | ∃ u : U.domain, z = productTuple (rvValues (U.value u)) (rvValues (V.value (F u)))}

theorem rawVolumeCorrespondence_definable (F : Map U.domain V.domain) :
    S.Definable LRV (rawVolumeCorrespondence F) := by
  let P := rawRVSpace (M := M) k
  let R := fun t s => ∃ u : U.domain, U.value u = t ∧ V.value (F u) = s
  let e : Fin k ⊕ Fin k ≃ Fin (k + k) := finSumFinEquiv
  have h : S.Definable LRV (P.relation P R) := volume_relation_definable F
  convert h.preimage_comp e using 1
  ext z
  constructor
  · rintro ⟨u, rfl⟩
    have hl : (productTuple (rvValues (U.value u)) (rvValues (V.value (F u))) ∘ e) ∘ Sum.inl =
        rvValues (U.value u) := funext (productTuple_left _ _)
    have hr : (productTuple (rvValues (U.value u)) (rvValues (V.value (F u))) ∘ e) ∘ Sum.inr =
        rvValues (V.value (F u)) := funext (productTuple_right _ _)
    change (∃ hl' : _ ∈ P.domain, ∃ hr' : _ ∈ P.domain, R _ _)
    simp only [hl, hr]
    exact ⟨⟨U.value u, rfl⟩, ⟨V.value (F u), rfl⟩, u, (decode_rvValues _).symm,
      (decode_rvValues _).symm⟩
  · rintro ⟨hl, hr, u, hL, hR⟩
    have heL : rvValues (U.value u) = (z ∘ e) ∘ Sum.inl :=
      (congrArg rvValues hL).trans (rvValues_decode ⟨_, hl⟩)
    have heR : rvValues (V.value (F u)) = (z ∘ e) ∘ Sum.inr :=
      (congrArg rvValues hR).trans (rvValues_decode ⟨_, hr⟩)
    refine ⟨u, ?_⟩
    apply productTuple_ext
    · intro i
      rw [productTuple_left]
      exact (congrFun heL i).symm
    · intro i
      rw [productTuple_right]
      exact (congrFun heR i).symm

theorem rawVolumeCorrespondence_mem (F : Map U.domain V.domain) (u : U.domain) :
    productTuple (rvValues (U.value u)) (rvValues (V.value (F u))) ∈ rawVolumeCorrespondence F :=
  ⟨u, rfl⟩

theorem rvIso_inv_apply (e : U ≅ V) (u : U.domain) :
    e.inv.map (e.hom.map u) = u :=
  congrArg (fun f : U ⟶ U => f.map u) e.hom_inv_id

theorem rvIso_apply_inv (e : U ≅ V) (v : V.domain) :
    e.hom.map (e.inv.map v) = v :=
  congrArg (fun f : V ⟶ V => f.map v) e.inv_hom_id

theorem rawVolumeCorrespondence_balanced (e : U ≅ V) (t s : Fin k → M)
    (h : productTuple t s ∈ rawVolumeCorrespondence e.hom.map) :
    rawWeight t = rawWeight s := by
  obtain ⟨u, hu⟩ := h
  have ht := funext (fun i => by simpa only [productTuple_left] using congrFun hu (productLeft k k i))
  have hs := funext (fun i => by simpa only [productTuple_right] using congrFun hu (productRight k k i))
  rw [ht, hs]
  change rvWeight (U.value u) = rvWeight (V.value (e.hom.map u))
  exact (e.hom.volumetric u).antisymm (by simpa only [rvIso_inv_apply] using
    (e.inv.volumetric (e.hom.map u)))

theorem rawVolumeCorrespondence_right_finite (f : RVHom U V) (t : Fin k → M) :
    {s : Fin k → M | productTuple t s ∈ rawVolumeCorrespondence f.map}.Finite := by
  by_cases ht : ∃ u : U.domain, rvValues (U.value u) = t
  · obtain ⟨u₀, hu₀⟩ := ht
    apply ((f.finite_volume_images (U.value u₀)).image rvValues).subset
    rintro s ⟨u, hu⟩
    have ht' : t = rvValues (U.value u) := funext (fun i => by
      simpa only [productTuple_left] using congrFun hu (productLeft k k i))
    have hs : s = rvValues (V.value (f.map u)) := funext (fun i => by
      simpa only [productTuple_right] using congrFun hu (productRight k k i))
    exact ⟨V.value (f.map u), ⟨u, rvValues_injective (ht'.symm.trans hu₀.symm), rfl⟩, hs.symm⟩
  · apply Set.finite_empty.subset
    rintro s ⟨u, hu⟩
    exact (ht ⟨u, funext (fun i => by
      simpa only [productTuple_left] using (congrFun hu (productLeft k k i)).symm)⟩).elim

theorem rawVolumeCorrespondence_left_finite (e : U ≅ V) (s : Fin k → M) :
    {t : Fin k → M | productTuple t s ∈ rawVolumeCorrespondence e.hom.map}.Finite := by
  apply (rawVolumeCorrespondence_right_finite e.inv s).subset
  rintro t ⟨u, hu⟩
  have ht : t = rvValues (U.value u) := funext (fun i => by
    simpa only [productTuple_left] using congrFun hu (productLeft k k i))
  have hs : s = rvValues (V.value (e.hom.map u)) := funext (fun i => by
    simpa only [productTuple_right] using congrFun hu (productRight k k i))
  exact ⟨e.hom.map u, by rw [ht, hs, rvIso_inv_apply]⟩

theorem rawVolumeCorrespondence_definableOverBase (hcan : CanonicalStructure.IsCanonical (M := M))
    (B : Base (M := M)) {U V : RVObject (M := M) B.real k} (F : Map U.domain V.domain) :
    DefinableOverBase B (fun _ => .rv) (rawVolumeCorrespondence F) := by
  apply real_definableOverBase B
  apply raw_definableOver_sorted hcan
  · exact rawVolumeCorrespondence_definable F
  · rintro z ⟨u, rfl⟩ j
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective j
    cases i with
    | inl i =>
      change iRV (productTuple _ _ (productLeft k k i))
      rw [productTuple_left]
      exact (U.value u i).property
    | inr i =>
      change iRV (productTuple _ _ (productRight k k i))
      rw [productTuple_right]
      exact (V.value (F u) i).property

theorem exists_rvIso_volume_lift {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (hcan : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : Base (M := M)) (hsmall : Cardinal.mk B.real < κ) (hB : VFGammaGeneratedBase B)
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)
    {U V : RVObject (M := M) B.real k} (e : U ≅ V) :
    ∃ A : Set (Fin (k + k) → M), B.real.Definable LRV A ∧
      rawVolumeCorrespondence e.hom.map ⊆ rawLiftDomain A :=
  exists_balancedCorrespondence_lift hκ hs h00 B hsmall hB v hv k _
    (rawVolumeCorrespondence_definableOverBase hcan B e.hom.map)
    (rawVolumeCorrespondence_balanced e) (rawVolumeCorrespondence_left_finite e)
    (rawVolumeCorrespondence_right_finite e.hom)

end SpecialTransformations.Section7

end VolumeCorrespondenceProof

section LiftedIsomorphismGraphProof

/-!
# The definable graph between canonical lifts

Combine the fibrewise VF bijection with the exact graph of the given
RV label map. Retaining the labels distinguishes different points
of the lift with the same volume. This constructs an isomorphism
of the actual presented sets.
-/

open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

set_option backward.isDefEq.respectTransparency false

namespace SpecialTransformations.Section7

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}
variable {U V : RVObject (M := M) S k}

def liftedGraph (F : Map U.domain V.domain) (A : Set (Fin (k + k) → M))
    (p : (rawMixedSpace (M := M) k U.arity).Carrier)
    (q : (rawMixedSpace (M := M) k V.arity).Carrier) : Prop :=
  p ∈ (rvLift U).carrier ∧ q ∈ (rvLift V).carrier ∧
    F.graph p.2 q.2 ∧ productTuple (vfValues p.1) (vfValues q.1) ∈ A

theorem liftedGraph_definable (F : Map U.domain V.domain) (A : Set (Fin (k + k) → M))
    (hA : S.Definable LRV A) :
    (rawMixedSpace (M := M) k U.arity).RelationDefinable (rawMixedSpace k V.arity) S
      (liftedGraph F A) := by
  let P := rawMixedSpace (M := M) k U.arity
  let Q := rawMixedSpace (M := M) k V.arity
  let P' := rawRVSpace (M := M) U.arity
  let Q' := rawRVSpace (M := M) V.arity
  let σ : P'.Index ⊕ Q'.Index → P.Index ⊕ Q.Index := Sum.map Sum.inr Sum.inr
  let τ : Fin (k + k) → P.Index ⊕ Q.Index :=
    productTuple (fun i => .inl (.inl i)) (fun i => .inr (.inl i))
  have h : S.Definable LRV ((P.relation Q (fun p q =>
      p ∈ (rvLift U).carrier ∧ q ∈ (rvLift V).carrier)) ∩
      {z | z ∘ σ ∈ P'.relation Q' F.graph} ∩ {z | z ∘ τ ∈ A}) := by
    have hleft := (rvLift U).definable.left_relation P Q
    have hright := ((rvLift V).definable.left_relation Q P).swap Q P
    have hdom : S.Definable LRV (P.relation Q (fun p q =>
        p ∈ (rvLift U).carrier ∧ q ∈ (rvLift V).carrier)) := hleft.inter P Q hright
    exact (hdom.inter (F.graph_definable.preimage_comp σ)).inter (hA.preimage_comp τ)
  change S.Definable LRV (P.relation Q (liftedGraph F A))
  convert h using 1
  ext z
  by_cases hp : z ∘ Sum.inl ∈ P.domain <;> by_cases hq : z ∘ Sum.inr ∈ Q.domain
  · let p := P.decode ⟨z ∘ Sum.inl, hp⟩
    let q := Q.decode ⟨z ∘ Sum.inr, hq⟩
    have hpcode := mixedValues_decode (n := k) (r := U.arity) ⟨z ∘ Sum.inl, hp⟩
    have hqcode := mixedValues_decode (n := k) (r := V.arity) ⟨z ∘ Sum.inr, hq⟩
    have hσ : z ∘ σ = Sum.elim (rvValues p.2) (rvValues q.2) := by
      funext j
      cases j with
      | inl j => exact (congrFun hpcode (.inr j)).symm
      | inr j => exact (congrFun hqcode (.inr j)).symm
    have hτ : z ∘ τ = productTuple (vfValues p.1) (vfValues q.1) := by
      apply productTuple_ext
      · intro j
        have hj : τ (productLeft k k j) = Sum.inl (Sum.inl j) := productTuple_left _ _ _
        rw [Function.comp_apply, hj, productTuple_left]
        exact (congrFun hpcode (.inl j)).symm
      · intro j
        have hj : τ (productRight k k j) = Sum.inr (Sum.inl j) := productTuple_right _ _ _
        rw [Function.comp_apply, hj, productTuple_right]
        exact (congrFun hqcode (.inl j)).symm
    have hgraph : (z ∘ σ ∈ P'.relation Q' F.graph) ↔ F.graph p.2 q.2 := by
      rw [hσ]
      simpa only [P', Q', decode_rvValues] using
        P'.relation_decode Q' F.graph ⟨rvValues p.2, ⟨p.2, rfl⟩⟩
          ⟨rvValues q.2, ⟨q.2, rfl⟩⟩
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, hτ, hgraph]
    simp only [Space.relation, Set.mem_ofPred_eq, hp, hq, exists_prop, true_and, liftedGraph]
    tauto
  · simp [Space.relation, hp, hq]
  · simp [Space.relation, hp, hq]
  · simp [Space.relation, hp, hq]

theorem liftedGraph_existsUnique_right (F : Map U.domain V.domain)
    (A : Set (Fin (k + k) → M))
    (hA : rawVolumeCorrespondence F ⊆ rawLiftDomain A) (p : rvLift U) :
    ∃! q, liftedGraph F A p.val q := by
  obtain ⟨u, hu, hvol⟩ := p.property
  let t := rvValues (U.value u)
  let s := rvValues (V.value (F u))
  have hgood := hA (rawVolumeCorrespondence_mem F u)
  have ht : productTuple t s ∘ productLeft k k = t := funext (productTuple_left t s)
  have hs : productTuple t s ∘ productRight k k = s := funext (productTuple_right t s)
  have hinput : vfValues p.val.1 ∈ rawTupleFibre t := by
    intro i
    exact ⟨(p.val.1 i).property, congrArg Subtype.val (congrFun hvol.symm i)⟩
  have hg : ∃! b, b ∈ rawTupleFibre s ∧ productTuple (vfValues p.val.1) b ∈ A := by
    have h := hgood.1
    change (∀ a ∈ rawTupleFibre (productTuple t s ∘ productLeft k k),
      ∃! b, b ∈ rawTupleFibre (productTuple t s ∘ productRight k k) ∧ productTuple a b ∈ A) at h
    rw [ht, hs] at h
    exact h _ hinput
  obtain ⟨b, hb, hbuniq⟩ := hg
  let b' : Fin k → VFType (M := M) := fun i => ⟨b i, (hb.1 i).1⟩
  have hbvol : V.value (F u) = tupleRV b' := by
    funext i
    exact Subtype.ext (hb.1 i).2.symm
  let q : (rawMixedSpace (M := M) k V.arity).Carrier := (b', (F u).val)
  refine ⟨q, ⟨p.property, ⟨F u, rfl, hbvol⟩, ⟨u, hu, rfl⟩, hb.2⟩, ?_⟩
  intro q' hq'
  obtain ⟨u', hu', hFu'⟩ := hq'.2.2.1
  have huu : u' = u := Subtype.ext (hu'.trans hu.symm)
  subst u'
  obtain ⟨v', hv', hvvol⟩ := hq'.2.1
  have hvv : v' = F u := Subtype.ext (hv'.trans hFu'.symm)
  subst v'
  have hqf : vfValues q'.1 ∈ rawTupleFibre s := by
    intro i
    exact ⟨(q'.1 i).property, congrArg Subtype.val (congrFun hvvol.symm i)⟩
  have he := hbuniq (vfValues q'.1) ⟨hqf, hq'.2.2.2⟩
  exact Prod.ext (vfValues_injective he) hFu'.symm

def swapPairCoordinates (k : ℕ) : Fin (k + k) → Fin (k + k) :=
  productTuple (productRight k k) (productLeft k k)

theorem productTuple_swapPairCoordinates {X : Type} (a b : Fin k → X) :
    productTuple a b ∘ swapPairCoordinates k = productTuple b a := by
  apply productTuple_ext
  · intro i; simp [swapPairCoordinates, Function.comp_def]
  · intro i; simp [swapPairCoordinates, Function.comp_def]

theorem rawLiftDomain_swap {A : Set (Fin (k + k) → M)} {t s : Fin k → M}
    (h : productTuple t s ∈ rawLiftDomain A) :
    productTuple s t ∈ rawLiftDomain {z | z ∘ swapPairCoordinates k ∈ A} := by
  have hp (a b : Fin k → M) :
      productTuple a b ∘ productLeft k k = a ∧ productTuple a b ∘ productRight k k = b :=
    ⟨funext (productTuple_left a b), funext (productTuple_right a b)⟩
  simp only [rawLiftDomain, Set.mem_ofPred_eq, (hp t s).1, (hp t s).2] at h
  simp only [rawLiftDomain, Set.mem_ofPred_eq, (hp s t).1, (hp s t).2, productTuple_swapPairCoordinates]
  exact ⟨h.2, h.1⟩

theorem liftedGraph_existsUnique_left (e : U ≅ V)
    (A : Set (Fin (k + k) → M))
    (hA : rawVolumeCorrespondence e.hom.map ⊆ rawLiftDomain A) (q : rvLift V) :
    ∃! p, liftedGraph e.hom.map A p q.val := by
  let A' := {z | z ∘ swapPairCoordinates k ∈ A}
  have hA' : rawVolumeCorrespondence e.inv.map ⊆ rawLiftDomain A' := by
    rintro z ⟨u, rfl⟩
    have h := hA (rawVolumeCorrespondence_mem e.hom.map (e.inv.map u))
    rw [rvIso_apply_inv] at h
    exact rawLiftDomain_swap h
  apply (existsUnique_congr (fun p => ?_)).mp
    (liftedGraph_existsUnique_right e.inv.map A' hA' q)
  unfold liftedGraph
  have hgraph : e.inv.map.graph q.val.2 p.2 ↔ e.hom.map.graph p.2 q.val.2 := by
    constructor
    · rintro ⟨u, hu, hp⟩
      exact ⟨e.inv.map u, hp, by rw [rvIso_apply_inv]; exact hu⟩
    · rintro ⟨u, hp, hu⟩
      exact ⟨e.hom.map u, hu, by rw [rvIso_inv_apply]; exact hp⟩
  simp only [A', Set.mem_ofPred_eq, productTuple_swapPairCoordinates, hgraph]
  tauto

def companionGraph (F : Map U.domain V.domain) :
    Set (((Fin k → CanonicalRV.RVSort M) × (Fin U.arity → CanonicalRV.RVSort M)) ×
      ((Fin k → CanonicalRV.RVSort M) × (Fin V.arity → CanonicalRV.RVSort M))) :=
  {p | ∃ u : U.domain,
    p.1 = (U.value u, u.val) ∧ p.2 = (V.value (F u), (F u).val)}

theorem liftedGraph_isAmbientLift (e : U ≅ V)
    (A : Set (Fin (k + k) → M))
    (hgood : rawVolumeCorrespondence e.hom.map ⊆ rawLiftDomain A) :
    IsAmbientLift mixedRVProjection mixedRVProjection (rvLift U).carrier (rvLift V).carrier
      (companionGraph e.hom.map) {p | liftedGraph e.hom.map A p.1 p.2} := by
  let F := e.hom.map
  refine ⟨rvLift_fullPullback U, rvLift_fullPullback V, (fun _ h => ⟨h.1, h.2.1⟩), ?_, ?_⟩
  · rintro p ⟨u, hu, hv⟩
    obtain ⟨a, ha⟩ := tupleRV_surjective (U.value u)
    obtain ⟨b, hb⟩ := tupleRV_surjective (V.value (F u))
    have hpa : mixedRVProjection (a, u.val) = (U.value u, u.val) := by
      change (tupleRV a, u.val) = _
      rw [ha]
    have hpb : mixedRVProjection (b, (F u).val) = (V.value (F u), (F u).val) := by
      change (tupleRV b, (F u).val) = _
      rw [hb]
    exact ⟨⟨(a, u.val), ⟨u, rfl, ha.symm⟩, hpa.trans hu.symm⟩,
      ⟨(b, (F u).val), ⟨F u, rfl, hb.symm⟩, hpb.trans hv.symm⟩⟩
  · rintro c ⟨u, hcu, hcv⟩
    constructor
    · intro p hp
      have hpu := hp.trans hcu
      let p' : rvLift U := ⟨p, u, (congrArg Prod.snd hpu).symm, (congrArg Prod.fst hpu).symm⟩
      apply (existsUnique_congr (fun q => ?_)).mp (liftedGraph_existsUnique_right F A hgood p')
      refine ⟨fun h => ⟨?_, h⟩, And.right⟩
      obtain ⟨u', hu', hqu⟩ := h.2.2.1
      have he : u' = u := Subtype.ext (hu'.trans (congrArg Prod.snd hpu))
      subst u'
      obtain ⟨v', hv', hqv⟩ := h.2.1
      have he : v' = F u := Subtype.ext (hv'.trans hqu.symm)
      subst v'
      exact (Prod.ext hqv.symm hqu.symm).trans hcv.symm
    · intro q hq
      have hqv := hq.trans hcv
      let q' : rvLift V :=
        ⟨q, F u, (congrArg Prod.snd hqv).symm, (congrArg Prod.fst hqv).symm⟩
      apply (existsUnique_congr (fun p => ?_)).mp (liftedGraph_existsUnique_left e A hgood q')
      refine ⟨fun h => ⟨?_, h⟩, And.right⟩
      obtain ⟨u', hu', hqu⟩ := h.2.2.1
      have hFu : F u' = F u := Subtype.ext (hqu.trans (congrArg Prod.snd hqv))
      have he : u' = u := by
        have hh := congrArg e.inv.map hFu
        simpa only [F, rvIso_inv_apply] using hh
      subst u'
      obtain ⟨u'', hu'', hpu⟩ := h.1
      have he : u'' = u := Subtype.ext (hu''.trans hu'.symm)
      subst u''
      exact (Prod.ext hpu.symm hu'.symm).trans hcu.symm

theorem exists_liftMap_of_volume_lift (e : U ≅ V)
    (A : Set (Fin (k + k) → M)) (hA : S.Definable LRV A)
    (hgood : rawVolumeCorrespondence e.hom.map ⊆ rawLiftDomain A) :
    ∃ f : Map (rvLift U) (rvLift V), Function.Bijective f ∧
      ∀ p : rvLift U, liftedGraph e.hom.map A p.val (f p).val := by
  let R := liftedGraph e.hom.map A
  have hd := liftedGraph_definable e.hom.map A hA
  have hdom : ∀ p q, R p q → p ∈ (rvLift U).carrier ∧ q ∈ (rvLift V).carrier :=
    fun _ _ h => ⟨h.1, h.2.1⟩
  have htotal (p : rvLift U) : ∃ q, R p.val q :=
    (liftedGraph_existsUnique_right e.hom.map A hgood p).exists
  have huniq (p q q') (hq : R p q) (hq' : R p q') : q = q' :=
    (liftedGraph_existsUnique_right e.hom.map A hgood ⟨p, hq.1⟩).unique hq hq'
  let f := Map.ofFunctionalRelation hd hdom htotal huniq
  have hf (p : rvLift U) : R p.val (f p).val :=
    Map.ofFunctionalRelation_graph hd hdom htotal huniq p
  have hb : Function.Bijective f := by
    constructor
    · intro p p' he
      apply Subtype.ext
      apply (liftedGraph_existsUnique_left e A hgood (f p)).unique (hf p)
      rw [he]
      exact hf p'
    · intro q
      obtain ⟨p, hp, _⟩ := liftedGraph_existsUnique_left e A hgood q
      let p' : rvLift U := ⟨p, hp.1⟩
      exact ⟨p', Subtype.ext (huniq p (f p').val q.val (hf p') hp)⟩
  exact ⟨f, hb, hf⟩

theorem rvLift_isomorphic_of_volume_lift (e : U ≅ V)
    (A : Set (Fin (k + k) → M)) (hA : S.Definable LRV A)
    (hgood : rawVolumeCorrespondence e.hom.map ⊆ rawLiftDomain A)
    (Δ : Space LRV M) :
    Nonempty ((rvLiftObject Δ U).obj ≅ (rvLiftObject Δ V).obj) := by
  obtain ⟨f, hb, _⟩ := exists_liftMap_of_volume_lift e A hA hgood
  exact ⟨DefinableSetCat.isoOfBijective (A := (rvLiftObject Δ U).obj)
    (B := (rvLiftObject Δ V).obj) f hb⟩

end SpecialTransformations.Section7

end LiftedIsomorphismGraphProof

section LiftScissorsProof

/-!
# The canonical lift preserves actual empty and scissors relations

The cut is always by the original RV label. The volume map on a
restricted object is inherited, so the two pieces, union and
intersection lift with exactly the same field fibres.
-/

open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

set_option backward.isDefEq.respectTransparency false

namespace SpecialTransformations.Section7

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

theorem rvLift_restrict_mem_iff (U : RVObject (M := M) S k)
    (X : DefSet (rawRVSpace (M := M) U.arity) S) (hX : X.carrier ⊆ U.domain.carrier)
    (p : (rawMixedSpace (M := M) k U.arity).Carrier) :
    p ∈ (rvLift (U.restrict X hX)).carrier ↔ p ∈ (rvLift U).carrier ∧ p.2 ∈ X.carrier := by
  constructor
  · rintro ⟨a, ha, hv⟩
    exact ⟨⟨⟨a.val, hX a.property⟩, ha, hv⟩, ha ▸ a.property⟩
  · rintro ⟨⟨a, ha, hv⟩, hX'⟩
    have hm : a.val ∈ X.carrier := ha.symm ▸ hX'
    exact ⟨⟨a.val, hm⟩, ha, hv⟩

theorem rvLift_restrict_union (U : RVObject (M := M) S k)
    (X Y : DefSet (rawRVSpace (M := M) U.arity) S)
    (hX : X.carrier ⊆ U.domain.carrier) (hY : Y.carrier ⊆ U.domain.carrier) :
    rvLift (U.restrict (X.union Y) (fun _ h => h.elim (fun hx => hX hx) (fun hy => hY hy))) =
      (rvLift (U.restrict X hX)).union (rvLift (U.restrict Y hY)) := by
  apply DefSet.eq_of_carrier_eq
  ext p
  simp only [DefSet.union, Set.mem_union, rvLift_restrict_mem_iff]
  tauto

theorem rvLift_restrict_inter (U : RVObject (M := M) S k)
    (X Y : DefSet (rawRVSpace (M := M) U.arity) S)
    (hX : X.carrier ⊆ U.domain.carrier) (hY : Y.carrier ⊆ U.domain.carrier) :
    rvLift (U.restrict (X.inter Y) (fun _ h => hX h.1)) =
      (rvLift (U.restrict X hX)).inter (rvLift (U.restrict Y hY)) := by
  apply DefSet.eq_of_carrier_eq
  ext p
  simp only [DefSet.inter, Set.mem_inter_iff, rvLift_restrict_mem_iff]
  tauto

theorem rvLift_scissor (Δ : Space LRV M) {A B C D : RVObject (M := M) S k}
    (h : RVScissor A B C D) :
    VFAllScissor (rvLiftObject Δ A).obj (rvLiftObject Δ B).obj
      (rvLiftObject Δ C).obj (rvLiftObject Δ D).obj := by
  obtain ⟨U, X, Y, hX, hY, rfl, rfl, rfl, rfl⟩ := h
  refine ⟨(k, U.arity), rvLift (U.restrict X hX), rvLift (U.restrict Y hY), rfl, rfl, ?_, ?_⟩
  · change DefinableSetCat.objOfSet (k, U.arity) _ = DefinableSetCat.objOfSet (k, U.arity) _
    rw [rvLift_restrict_union U X Y hX hY]
  · change DefinableSetCat.objOfSet (k, U.arity) _ = DefinableSetCat.objOfSet (k, U.arity) _
    rw [rvLift_restrict_inter U X Y hX hY]

noncomputable def rvLift_empty_iso (Δ : Space LRV M) :
    (rvLiftObject Δ (RVObject.empty (M := M) S k)).obj ≅ vfAllEmptyObject S :=
  vfAllEmptyIso _ (rvLift_empty_of_domain_empty _ rfl)

theorem rvLiftObject_iso_of_rvIso {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (hcan : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : Base (M := M)) (hsmall : Cardinal.mk B.real < κ) (hB : VFGammaGeneratedBase B)
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)
    (Δ : Space LRV M) {U V : RVObject (M := M) B.real k} (e : U ≅ V) :
    Nonempty ((rvLiftObject Δ U).obj ≅ (rvLiftObject Δ V).obj) := by
  obtain ⟨A, hA, hgood⟩ := exists_rvIso_volume_lift hcan hκ hs h00 B hsmall hB v hv e
  exact rvLift_isomorphic_of_volume_lift e A hA hgood Δ

end SpecialTransformations.Section7

end LiftScissorsProof
