import Section10.RVVolumeRepresentative
import Section5.VerticalObstacles
import Section9.SpecialJacobianGeneric
import Section4.VFFiniteMaps

/-! RV-valued surjectivity of the lift. Section 5 prepares the volume map
on the same RV fibres used to form the lift. Relabelling preserves the VF
coordinates, so the Jacobian-one calculation of Section 9 still applies. -/

set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.DefinableGeometry.Space.ofEmbedding
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section4.rawMixedSpace
  SpecialTransformations.Section4.rawVFSpace SpecialTransformations.Section4.rawRVSpace

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9

noncomputable section

namespace SpecialTransformations.Section10

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n r s : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "VF" => VFType (M := M)
local notation "RV" => CanonicalRV.RVSort M

omit hM in
private theorem coded_preimage (P : Space LRV M) (c : P.Carrier → P.Index → M)
    (hc : ∀ z : P.domain, c (P.decode z) = z.val) (A : Set P.Carrier) :
    P.preimage A = c '' A := by
  ext z
  constructor
  · rintro ⟨hz, ha⟩
    exact ⟨P.decode ⟨z, hz⟩, ha, hc ⟨z, hz⟩⟩
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨w, rfl⟩ := P.onto a
    rw [hc w]
    exact ⟨w.property, ha⟩

omit hM in
private theorem coded_relation (P Q : Space LRV M)
    (c : P.Carrier → P.Index → M) (d : Q.Carrier → Q.Index → M)
    (hc : ∀ z : P.domain, c (P.decode z) = z.val)
    (hd : ∀ z : Q.domain, d (Q.decode z) = z.val) (R : P.Carrier → Q.Carrier → Prop) :
    P.relation Q R = {z | ∃ x y, R x y ∧ c x = z ∘ Sum.inl ∧ d y = z ∘ Sum.inr} := by
  ext z
  constructor
  · rintro ⟨hx, hy, h⟩
    exact ⟨_, _, h, hc ⟨_, hx⟩, hd ⟨_, hy⟩⟩
  · rintro ⟨x, y, h, hx, hy⟩
    obtain ⟨a, rfl⟩ := P.onto x
    obtain ⟨b, rfl⟩ := Q.onto y
    rw [hc a] at hx
    rw [hd b] at hy
    change ∃ h₁ : z ∘ Sum.inl ∈ P.domain, ∃ h₂ : z ∘ Sum.inr ∈ Q.domain,
      R (P.decode ⟨_, h₁⟩) (Q.decode ⟨_, h₂⟩)
    exact ⟨hx ▸ a.property, hy ▸ b.property, by simpa only [← hx, ← hy] using h⟩

private theorem point_decode (z : Section5.pDomain (Section5.pointSpace (M := M) n r)) :
    mixedValues (Section5.pDecode (Section5.pointSpace n r) z) = z.val := by
  funext i
  cases i <;> rfl

private theorem normalized_definable (hc : CanonicalStructure.IsCanonical (M := M))
    {ι : Type} {E : Set (ι → M)} :
    @Set.Definable M S LRV N ι E ↔ S.Definable LRV E :=
  Iff.of_eq (congrArg (fun T : LRV.Structure M => @Set.Definable M S LRV T ι E)
    (normalize_eq_of_isCanonical hc))

private def specialInput (hc : CanonicalStructure.IsCanonical (M := M))
    (A : DefSet (rawMixedSpace (M := M) n r) S) : Section5.DefSet (M := M) S n r := by
  refine Section5.PresentedSet.mk A.carrier ?_
  have h := A.definable
  change S.Definable LRV ((rawMixedSpace n r).preimage A.carrier) at h
  rw [coded_preimage _ mixedValues mixedValues_decode] at h
  change @Set.Definable M S LRV N (Fin n ⊕ Fin r)
    (@Space.preimage LRV M N (Section5.pointSpace n r) A.carrier)
  rw [@coded_preimage M N _ mixedValues point_decode]
  exact (normalized_definable hc).mpr h

private def specialRVMap (hc : CanonicalStructure.IsCanonical (M := M)) {d : ℕ}
    {A : DefSet (rawMixedSpace (M := M) n r) S}
    (ν : Map A (DefSet.univ (rawRVSpace d) S)) :
    Section5.Map (specialInput hc A) (Section5.PresentedSet.univ (Section5.rawRVSpace d) S) := by
  let R (x : (rawMixedSpace (M := M) n r).Carrier) (y : Fin d → RV) := ν.graph x y
  refine Section5.Map.mk (fun a => ν (show A from a)) ?_
  have h := ν.graph_definable
  change S.Definable LRV ((rawMixedSpace n r).relation (rawRVSpace d) R) at h
  rw [coded_relation _ _ mixedValues rvValues mixedValues_decode rvValues_decode] at h
  change @Set.Definable M S LRV N ((Fin n ⊕ Fin r) ⊕ Fin d)
    (@Space.relation LRV M N (Section5.pointSpace n r) (Section5.rawRVSpace d) R)
  rw [@coded_relation M N _ _ mixedValues (@rvValues M N d) point_decode (@rvValues_decode M N d)]
  exact (normalized_definable hc).mpr h

private def specialRVPoint {d : ℕ} {A : Section5.DefSet (M := M) S n r}
    (ν : Section5.Map A (Section5.PresentedSet.univ (Section5.rawRVSpace d) S)) :
    Section5.Map A (Section5.PresentedSet.univ (Section5.pointSpace 0 d) S) := by
  let P := Section5.rawRVSpace (M := M) d
  let Q := @Section4.rvSpace M sM hM d
  let O := @Section4.vfSpace M sM hM 0
  letI : LRV.Structure M := N
  let g : Map (DefSet.univ P S) (DefSet.univ Q S) := Map.ofCodes _ id
    (fun z => z) (fun i => Set.DefinableFun.proj LRV) (fun z => by
      obtain ⟨x, hx⟩ := z.property
      intro i
      exact (congrFun hx i) ▸ (x i).property)
    (fun z => by
      funext i
      apply Subtype.ext
      exact (congrFun (rvValues_decode z) i).symm)
  let f := Map.toSubsingleton A O
  exact (f.pair (g.comp ν)).toUniv

private def currentRVSet (hc : CanonicalStructure.IsCanonical (M := M))
    (D : Section5.PresentedSet (Section5.rawRVSpace (M := M) r) S) :
    DefSet (rawRVSpace (M := M) r) S := by
  refine ⟨Section5.carrier D, ?_⟩
  have h := Section5.setDefinable D
  change @Set.Definable M S LRV N (Fin r)
    (@Space.preimage LRV M N (Section5.rawRVSpace r) (Section5.carrier D)) at h
  rw [@coded_preimage M N _ (@rvValues M N r) (@rvValues_decode M N r)] at h
  change @Set.Definable M S LRV sM (Fin r)
    (@Space.preimage LRV M sM (@rawRVSpace M sM r) (Section5.carrier D))
  rw [@coded_preimage M sM _ (@rvValues M sM r) (@rvValues_decode M sM r)]
  exact (normalized_definable hc).mp h

private def currentRVVolume (hc : CanonicalStructure.IsCanonical (M := M))
    (U : @RVObject M N S n) : RVObject (M := M) S n := by
  refine ⟨Section5.rvObjectArity U, currentRVSet hc (Section5.rvObjectDomain U), ?_⟩
  let f := Section5.rvObjectVolume U
  refine ⟨fun a => f a, ?_⟩
  let R := @Map.graph LRV M N _ _ S _ _ f
  have h := Section5.Map.graph_definable f
  change @Set.Definable M S LRV N _
    (@Space.relation LRV M N (Section5.rawRVSpace (Section5.rvObjectArity U))
      (Section5.rawRVSpace n) R) at h
  rw [@coded_relation M N _ _ (@rvValues M N _) (@rvValues M N n)
    (@rvValues_decode M N _) (@rvValues_decode M N n)] at h
  change @Set.Definable M S LRV sM _
    (@Space.relation LRV M sM (@rawRVSpace M sM (Section5.rvObjectArity U)) (@rawRVSpace M sM n) R)
  rw [@coded_relation M sM _ _ (@rvValues M sM _) (@rvValues M sM n)
    (@rvValues_decode M sM _) (@rvValues_decode M sM n)]
  exact (normalized_definable hc).mp h

private def currentKeyMap (hc : CanonicalStructure.IsCanonical (M := M))
    (B : Section5.DefSet (M := M) S n s) :
    Map (rawSpecialSet hc B) (DefSet.univ (rawRVSpace (n + s)) S) := by
  let f := Section5.rawKeyMap B
  let R := @Map.graph LRV M N _ _ S _ _ f
  refine ⟨fun b => f b, ?_⟩
  have h := Section5.Map.graph_definable f
  change @Set.Definable M S LRV N _
    (@Space.relation LRV M N (Section5.pointSpace n s) (Section5.rawRVSpace (n + s)) R) at h
  rw [@coded_relation M N _ _ mixedValues (@rvValues M N (n + s))
    point_decode (@rvValues_decode M N (n + s))] at h
  change S.Definable LRV ((rawMixedSpace n s).relation (rawRVSpace (n + s)) R)
  rw [coded_relation _ _ mixedValues rvValues mixedValues_decode rvValues_decode]
  exact (normalized_definable hc).mp h

private theorem currentLift_mem (hc : CanonicalStructure.IsCanonical (M := M))
    (U : @RVObject M N S n) (x : (rawMixedSpace n (Section5.rvObjectArity U)).Carrier) :
    x ∈ (rvLift (currentRVVolume hc U)).carrier ↔ x ∈ Section5.carrier (Section5.rawLift U) := by
  have he : @tupleRV M N (CanonicalStructure.normalized_model hM) n x.1 = tupleRV x.1 :=
    Section5.normalized_tupleRV x.1
  constructor <;> rintro ⟨u, hu, hv⟩
  · exact ⟨u, hu, hv.trans he.symm⟩
  · exact ⟨u, hu, hv.trans he⟩

private def currentPullbackLift (hc : CanonicalStructure.IsCanonical (M := M))
    (B : Section5.DefSet (M := M) S n s) :
    Map (rawSpecialSet hc B) (rvLift (currentRVVolume hc (Section5.pullbackObject B))) := by
  let f := Section5.pullbackLiftMap B
  let R := @Map.graph LRV M N _ _ S _ _ f
  refine ⟨fun b => ⟨(f b).val, (currentLift_mem hc _ _).mpr (f b).property⟩, ?_⟩
  have h := Section5.Map.graph_definable f
  change @Set.Definable M S LRV N _
    (@Space.relation LRV M N (Section5.pointSpace n s) (Section5.rawPointSpace n (n + s)) R) at h
  rw [@coded_relation M N _ _ mixedValues (@mixedValues M N n (n + s))
    point_decode (@mixedValues_decode M N n (n + s))] at h
  change S.Definable LRV ((rawMixedSpace n s).relation (rawMixedSpace n (n + s)) R)
  rw [coded_relation _ _ mixedValues mixedValues mixedValues_decode mixedValues_decode]
  exact (normalized_definable hc).mp h

private theorem currentPullbackLift_bijective (hc : CanonicalStructure.IsCanonical (M := M))
    (B : Section5.DefSet (M := M) S n s) (hB : Section5.IsRVPullback (Section5.carrier B)) :
    Function.Bijective (currentPullbackLift hc B) := by
  have h := Section5.pullbackLiftMap_bijective B hB
  constructor
  · intro a b he
    have hval := congrArg (fun p : rvLift (currentRVVolume hc (Section5.pullbackObject B)) => p.val) he
    exact h.1 (Subtype.ext hval)
  · intro b
    obtain ⟨a, ha⟩ := h.2 ⟨b.val, (currentLift_mem hc _ b.val).mp b.property⟩
    have hval := congrArg (fun p : Section5.rawLift (Section5.pullbackObject B) => p.val) ha
    exact ⟨a, Subtype.ext hval⟩

/-- Factor a map constant on mixed RV fibres through their keys. -/
private theorem exists_pullback_map (hc : CanonicalStructure.IsCanonical (M := M))
    (B : Section5.DefSet (M := M) S n s) {Q : Space LRV M} {D : DefSet Q S}
    (ω : Map (rawSpecialSet hc B) D)
    (hω : ∀ b c : rawSpecialSet hc B, Section5.SameRV b.val c.val → ω b = ω c) :
    ∃ η : Map (currentRVVolume hc (Section5.pullbackObject B)).domain D,
      ∀ b : rawSpecialSet hc B, η ⟨(currentKeyMap hc B b).val, ⟨b, rfl⟩⟩ = ω b := by
  let U := currentRVVolume hc (Section5.pullbackObject B)
  let K := currentKeyMap hc B
  let R (u : Fin (n + s) → RV) (v : Q.Carrier) :=
    ∃ b : rawSpecialSet hc B, (K b).val = u ∧ (ω b).val = v
  have hR : (rawRVSpace (n + s)).RelationDefinable Q S R := by
    apply ((K.graph_definable.swap _ _).comp _ _ _ ω.graph_definable).congr _ _
    intro u v
    constructor
    · rintro ⟨x, ⟨b, hb, hbu⟩, ⟨c, hc, hcv⟩⟩
      have e : b = c := Subtype.ext (hb.trans hc.symm)
      exact ⟨b, hbu, e.symm ▸ hcv⟩
    · rintro ⟨b, hu, hv⟩
      exact ⟨b.val, ⟨b, rfl, hu⟩, ⟨b, rfl, hv⟩⟩
  have hdom (u v) (h : R u v) : u ∈ U.domain.carrier ∧ v ∈ D.carrier := by
    obtain ⟨b, hu, rfl⟩ := h
    exact ⟨⟨b, hu⟩, (ω b).property⟩
  have htotal (u : U.domain) : ∃ v, R u.val v := by
    obtain ⟨b, hb⟩ := u.property
    exact ⟨_, b, hb, rfl⟩
  have hunique (u v w) (hv : R u v) (hw : R u w) : v = w := by
    obtain ⟨b, hb, rfl⟩ := hv
    obtain ⟨c, hc', rfl⟩ := hw
    have he : (Section5.rawKeyMap B b).val = (Section5.rawKeyMap B c).val := hb.trans hc'.symm
    rw [Section5.rawKeyMap_apply, Section5.rawKeyMap_apply] at he
    have hk : Section5.SameRV b.val c.val := (Section5.sameRV_iff _ _).mpr
      ⟨fun i => by simpa only [Fin.append_left, Section5.vfAt] using congrFun he (Fin.castAdd s i),
       funext (fun i => by simpa only [Fin.append_right] using congrFun he (Fin.natAdd n i))⟩
    exact congrArg Subtype.val (hω b c hk)
  let π : Map U.domain D :=
    Map.ofFunctionalRelation hR hdom htotal hunique
  have hπ (u : U.domain) : R u.val (π u).val :=
    Map.ofFunctionalRelation_graph hR hdom htotal hunique u
  refine ⟨π, fun b => Subtype.ext ?_⟩
  exact hunique _ _ _ (hπ ⟨(K b).val, ⟨b, rfl⟩⟩) ⟨b, rfl, rfl⟩

/-- Lift a finite-volume set with a map determined by definable RV data.
The map descends to the labels, and the essential bijection has Jacobian one. -/
theorem exists_lift_preserving_rv_determined_map [CharZero VF]
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {k d : ℕ} (A : DefSet (rawMixedSpace (M := M) (k + 1) r) (C.base : Set M))
    (hfin : ∀ a, {t | (a, t) ∈ A.carrier}.Finite)
    {Q : Space LRV M} {D : DefSet Q (C.base : Set M)} (ω : Map A D)
    (ν : Map A (DefSet.univ (rawRVSpace d) (C.base : Set M)))
    (hν : ∀ a b, ν a = ν b → ω a = ω b) :
    ∃ (U : RVFiniteObject (M := M) (C.base : Set M) (k + 1)) (η : Map U.obj.domain D),
      ∃ g : EssentialVFMap A (rvLift U.obj),
        (∀ u, ∃ a, η u = ω a) ∧
        ∀ a : g.source, HasMixedVFJacobianAt g.map a 1 ∧
          η (liftLabelMap U.obj ⟨(g.map a).val, g.target_subset (g.map a).property⟩) =
            ω ⟨a.val, g.source_subset a.property⟩ := by
  let S := (C.base : Set M)
  let n := k + 1
  let Δ := rawRVSpace (M := M) 1
  let A₀ := specialInput hc A
  let ν₀ := specialRVPoint (specialRVMap hc ν)
  let _ : Valued VF (Values.presentationType (M := M)) := Valued.mk' Values.presentationValuation
  let v := Values.presentationValuation (M := M)
  have hv := Values.presentation_compatible (M := M)
  have hκ := C.uncountable.le
  have hn : 0 < n := Nat.zero_lt_succ k
  obtain ⟨s, B, T, _, hB, hν₀⟩ := Section5.rvPreparation_all C.model00 v hv
    (Section5.uniformVerticalObstacles C.saturated C.small v hv) n A₀ none (by simp) ν₀
  let B' := rawSpecialSet hc B
  let e : Map A B' := rawSpecialMap hc T.toMap
  let i : Map B' A := rawSpecialMap hc T.inverseMap
  have hi : Function.Injective i := by
    intro b c he
    change T.inverseMap b = T.inverseMap c at he
    simpa only [Section5.SpecialBijection.apply_inverse] using congrArg T.toMap he
  obtain ⟨p, hp⟩ := finite_map_to_vf_of_dimension_and_finite_rv_fibres hc hκ C.saturated
    C.small Δ (rawRVSpace_rvCoded 1) A (vfDim_le_arity Δ A) hfin
  have hfinB := (dimension_and_finite_rv_fibres_of_finite_map_to_vf hc hκ C.saturated C.small
    Δ (p.comp i) (hp.comp (Map.finiteFibres_of_injective hi))).2
  let U₀ := currentRVVolume hc (Section5.pullbackObject B)
  have hfinite : U₀.volume.FiniteFibres := by
    change Section5.Map.FiniteFibres (Section5.rvObjectVolume (Section5.pullbackObject B))
    exact Section5.pullbackObject_finiteVolume B hB hfinB
  let μ := ω.comp i
  have hμ (b c : B') (hbc : Section5.SameRV b.val c.val) : μ b = μ c := by
    apply hν
    exact Subtype.ext ((Section5.sameRV_iff _ _).mp (hν₀ b c hbc)).2
  obtain ⟨η, hη⟩ := exists_pullback_map hc B μ hμ
  let U : RVFiniteObject (M := M) S n := ⟨U₀, hfinite⟩
  let f : Map A (rvLift U.obj) := (currentPullbackLift hc B).comp e
  have hf : Function.Bijective f := (currentPullbackLift_bijective hc B hB).comp T.bijective
  have hform (a : A) : η (liftLabelMap U.obj (f a)) = ω a := by
    change η ⟨(currentKeyMap hc B (e a)).val, ⟨e a, rfl⟩⟩ = ω a
    rw [hη]
    exact congrArg ω (T.inverse_apply a)
  have hVF (a : A) : (f a).val.1 = (e a).val.1 := rfl
  obtain ⟨Z, _, hZ, hJ⟩ := exists_mixedJacobianOne_exception hc C.saturated C.small hn f (by
    intro a ha
    obtain ⟨L, ⟨F, ⟨ρ, hρ⟩, hF⟩, hdet⟩ :=
      specialChain_det_one_of_independent hc hκ C.saturated C.small hv T.chain a ha
    obtain ⟨_, _, ⟨σ, hσ⟩, _⟩ :=
      mixedDifferentiableAt_of_independent hc hκ C.saturated C.small hv f a ha
    refine ⟨L, ⟨F, ⟨max ρ σ, ?_⟩, hF⟩, hdet⟩
    intro x hx
    obtain ⟨_, he⟩ := hρ x (vfBall_anti (le_max_left _ _) hx)
    obtain ⟨hxf, hf⟩ := hσ x (vfBall_anti (le_max_right _ _) hx)
    have hlabel := congrArg (fun y : (Fin n → VF) × (Fin (n + s) → RV) => y.2) hf
    refine ⟨hxf, Prod.ext ?_ hlabel⟩
    exact (hVF ⟨(x, a.val.2), hxf⟩).trans (congrArg Prod.fst he))
  obtain ⟨g, hg⟩ := EssentialVFMap.exists_restriction_preserving_jacobian hc C.saturated C.small
    hn f hf Z hZ
  refine ⟨U, η, g, ?_, ?_⟩
  · intro u
    obtain ⟨b, hb⟩ := u.property
    refine ⟨i b, ?_⟩
    have hu : (⟨(currentKeyMap hc B b).val, ⟨b, rfl⟩⟩ : U.obj.domain) = u := Subtype.ext hb
    exact hu ▸ hη b
  · intro a
    let q : A := ⟨a.val, g.source_subset a.property⟩
    obtain ⟨hz, hout, hjac⟩ := hg a
    exact ⟨hjac 1 (hJ q hz), (congrArg (η ∘ liftLabelMap U.obj) (Subtype.ext hout)).trans (hform q)⟩

/-- The RV-valued case of Theorem 10.4 in positive degree. Every object
in the finite-volume VF presentation has a measure-preserving essential
isomorphism to the lift of a finite-volume RV object over the same base. -/
theorem theorem_10_4_rv_volume [CharZero VF]
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (_hB : VFGammaGeneratedBase ⟨(C.base : Set M), Ξ⟩)
    {k : ℕ} (A : DefSet (rawMixedSpace (M := M) (k + 1) r) (C.base : Set M))
    (hfin : ∀ a, {t | (a, t) ∈ A.carrier}.Finite) (ω : RVVolumeForm A) :
    ∃ U : RVVolumeObject (M := M) (C.base : Set M) k,
      ∃ g : EssentialVFMap A (rvLift U.underlying.obj), RVMeasurePreserving g ω U.liftForm := by
  obtain ⟨U, η, g, hrange, hg⟩ :=
    exists_lift_preserving_rv_determined_map hc C A hfin ω.map ω.map (fun _ _ h => h)
  let ωU : RVVolumeForm U.obj.domain := ⟨η, fun u => by
    obtain ⟨a, ha⟩ := hrange u
    rw [ha]
    exact ω.nonzero a⟩
  refine ⟨⟨U, ωU⟩, g, fun a => ⟨1, (hg a).1, ?_⟩⟩
  rw [RVOperations.rv_one, mul_one]
  exact congrArg (fun z => z.val 0) (hg a).2.symm

end SpecialTransformations.Section10
