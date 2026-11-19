import Section9.LiftLabelRepresentatives
import Section9.GammaRawRelations
import Section9.GammaLiftGluing

/-! Gamma counterpart of `exists_liftLabelRepresentative`: for a
finite-volume RV object coded over `S ⊇ B.real` with a Gamma volume graph and
a nonzero RV map with a Gamma graph, there is a VF representative map with a
Gamma graph. The representative relation over `B.real` comes from
`exists_uniform_finiteHead_representatives`, which accepts a code set
definable over the Gamma base. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section7
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable gammaLogicInput
  gammaPointCode gammaPointSort vfAt)

namespace SpecialTransformations.Section9.GammaLift

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}

theorem gamma_exists_liftLabelRepresentative
    (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    (hB : VFGammaGeneratedBase B) {S : Set M} (hBS : B.real ⊆ S)
    (U : RVFiniteObject (M := M) S k) (hUΓ : RVMapGamma U.obj.volume B)
    (τ : Map U.obj.domain (DefSet.univ (rawRVSpace (M := M) 1) S)) (hτΓ : RVMapGamma τ B)
    (hτ : ∀ u, ((τ u).val 0).val ≠ iRVZero) :
    ∃ c : Map (rvLift U.obj) (DefSet.univ (rawVFSpace (M := M) 1) S),
      GammaGraphDefinable B (fun (p : Point (M := M) k U.obj.arity) (z : Point (M := M) 1 0) =>
        ∃ x : rvLift U.obj, x.val = p ∧ (c x).val = z.1) ∧
      ∀ p, CanonicalRV.encodedRv ((c p).val 0) = (τ (liftLabelMap U.obj p)).val 0 := by
  have L := gammaLogicInput B
  let f := τ.comp (liftLabelMap U.obj)
  let code (p : rvLift U.obj) := productTuple (vfValues p.val.1) (rvValues (f p).val)
  let C := Set.range code
  -- the relation `p ↦ (p.1, τ(label p))` and its image
  let Qrel (p : Point (M := M) k U.obj.arity) (y : Point (M := M) k 1) : Prop :=
    ∃ x : rvLift U.obj, x.val = p ∧ y = (p.1, (f x).val)
  have hQ : GammaGraphDefinable B Qrel := by
    have h1 := L.comp_graph (gamma_label_graph (B := B) (n := k) (m := U.obj.arity)) hτΓ
    have h2 := h1.preimage_maps (SpecialTransformations.Section9.GammaLift.pointCoordinateMap id id B.real)
      (pointCoordinateMap (Fin.elim0 : Fin 0 → Fin k) id B.real)
    have h3 := L.comp_graph (gamma_coordinate_graph (B := B) (n := k) (m := U.obj.arity) (u := k) (w := 0)
      id Fin.elim0) (L.swap_graph (gamma_coordinate_graph (B := B) (n := k) (m := 1) (u := k) (w := 0) id Fin.elim0))
    have h4 := L.restrict_graph (lift_gamma U.obj hUΓ)
      (SpecialTransformations.Section5.GammaGraphDefinable.inter h2 h3)
    apply SpecialTransformations.Section5.GammaGraphDefinable.congr h4
    intro p y
    constructor
    · rintro ⟨hp, ⟨z, hz, u, hu, hy⟩, ⟨w, hw, hw'⟩⟩
      refine ⟨⟨p, hp⟩, rfl, ?_⟩
      have huu : u = liftLabelMap U.obj ⟨p, hp⟩ := Subtype.ext (by rw [hu, hz]; rfl)
      subst huu
      refine Prod.ext ?_ ?_
      · have := congrArg Prod.fst (hw.symm.trans hw')
        exact this.symm
      · exact hy.symm
    · rintro ⟨x, rfl, rfl⟩
      refine ⟨x.property, ⟨(Fin.elim0, x.val.2), rfl, liftLabelMap U.obj x, rfl, rfl⟩,
        ⟨(x.val.1, Fin.elim0), Prod.ext rfl (funext (fun i => Fin.elim0 i)),
          Prod.ext rfl (funext (fun i => Fin.elim0 i))⟩⟩
  have hY := L.image_graph hQ
  have hcodeY (p : rvLift U.obj) : code p = gammaPointCode ((p.val.1, (f p).val) : Point (M := M) k 1) := by
    show productTuple _ _ = _
    rw [productTuple_eq_append]
    rfl
  have hC : DefinableOverBase B (headRVSort k) C := by
    have hsort : headRVSort k = gammaPointSort k 1 := by
      unfold headRVSort gammaPointSort
      rw [productTuple_eq_append]
    rw [hsort]
    unfold GammaSetDefinable at hY
    convert hY using 1
    ext z
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨_, ⟨p.val, p, rfl, rfl⟩, (hcodeY p).symm⟩
    · rintro ⟨y, ⟨q, x, rfl, rfl⟩, rfl⟩
      exact ⟨x, hcodeY x⟩
  have hfin (a : Fin k → M) : {b : Fin 1 → M | productTuple a b ∈ C}.Finite := by
    let Q := {b : Fin 1 → M | productTuple a b ∈ C}
    change Q.Finite
    by_cases hQ' : Q.Nonempty
    · obtain ⟨b, p₀, hp₀⟩ := hQ'
      let x := p₀.val.1
      have ha : vfValues x = a := by
        funext i
        simpa only [code, productTuple_left] using congrFun hp₀ (productLeft k 1 i)
      let T := {t | (x,t) ∈ (rvLift U.obj).carrier}
      letI : Fintype T := (rvLift_finite_rv_fibres U.obj U.property x).fintype
      let G (t : T) := rvValues (f ⟨(x,t.val), t.property⟩).val
      apply (Set.finite_range G).subset
      rintro b ⟨p, hp⟩
      have hx : p.val.1 = x := vfValues_injective (by
        rw [ha]
        funext i
        simpa only [code, productTuple_left] using congrFun hp (productLeft k 1 i))
      let t : T := ⟨p.val.2, by
        change (x, p.val.2) ∈ (rvLift U.obj).carrier
        rw [← hx]
        exact p.property⟩
      have ht : (⟨(x,t.val), t.property⟩ : rvLift U.obj) = p := Subtype.ext (Prod.ext hx.symm rfl)
      refine ⟨t, ?_⟩
      change rvValues (f ⟨(x,t.val), t.property⟩).val = b
      rw [ht]
      funext i
      simpa only [code, productTuple_right] using congrFun hp (productRight k 1 i)
    · rw [show Q = ∅ from Set.not_nonempty_iff_eq_empty.mp hQ']
      exact Set.finite_empty
  have hnz : ∀ z ∈ C, z (productRight k 1 0) ≠ iRVZero := by
    rintro _ ⟨p, rfl⟩
    simpa only [code, productTuple_right, f, rvValues, Map.comp_apply]
      using hτ (liftLabelMap U.obj p)
  obtain ⟨R, hR, hSingle, hRep₀, hExists⟩ := exists_uniform_finiteHead_representatives
    hκ hs h00 B hsmall hB C hC hfin hnz
  have hRep (p : rvLift U.obj) : ∃ c : VFType (M := M), (code p, c.val) ∈ R ∧
      CanonicalRV.encodedRv c = (τ (liftLabelMap U.obj p)).val 0 := by
    obtain ⟨z, hz⟩ := hExists (code p) (Set.mem_range_self p)
    have hz' := hRep₀ _ hz
    refine ⟨⟨z, hz'.1⟩, hz, Subtype.ext ?_⟩
    change iRv z = ((τ (liftLabelMap U.obj p)).val 0).val
    simpa only [code, productTuple_right, f, rvValues, Map.comp_apply] using hz'.2
  -- the representative map, over the code set `S`
  let P := rawMixedSpace (M := M) k U.obj.arity
  let W := rawMixedSpace (M := M) k 1
  let Q := rawVFSpace (M := M) 1
  let g := (Map.fst (rawVFSpace (M := M) k) (rawRVSpace U.obj.arity) S (rvLift U.obj)).pair f
  let T (x : W.Carrier) (y : Q.Carrier) := (productTuple (vfValues x.1) (rvValues x.2), (y 0).val) ∈ R
  let e : Fin k ⊕ Fin 1 ≃ Fin (k + 1) := finSumFinEquiv
  let σ : Fin (k + 1) ⊕ Fin 1 → W.Index ⊕ Q.Index := Sum.elim (Sum.inl ∘ e.symm) Sum.inr
  have hT : W.RelationDefinable Q S T := by
    have h := (hR.mono hBS).preimage_comp σ
    have hd := ((W.domain_definable.mono (Set.empty_subset S)).preimage_comp Sum.inl).inter
      ((Q.domain_definable.mono (Set.empty_subset S)).preimage_comp Sum.inr)
    change S.Definable LRV (W.relation Q T)
    convert hd.inter h using 1
    ext z
    change (∃ hx : z ∘ Sum.inl ∈ W.domain, ∃ hy : z ∘ Sum.inr ∈ Q.domain,
      T (W.decode ⟨_,hx⟩) (Q.decode ⟨_,hy⟩)) ↔
      (z ∘ Sum.inl ∈ W.domain ∧ z ∘ Sum.inr ∈ Q.domain) ∧
        ((z ∘ Sum.inl) ∘ e.symm, z (.inr (0 : Fin 1))) ∈ R
    have he (hx : z ∘ Sum.inl ∈ W.domain) (hy : z ∘ Sum.inr ∈ Q.domain) :
        T (W.decode ⟨_,hx⟩) (Q.decode ⟨_,hy⟩) ↔
          ((z ∘ Sum.inl) ∘ e.symm, z (.inr (0 : Fin 1))) ∈ R := by
      change (mixedValues (W.decode ⟨_,hx⟩) ∘ e.symm,
        vfValues (Q.decode ⟨_,hy⟩) 0) ∈ R ↔ _
      rw [mixedValues_decode, vfValues_decode]
      rfl
    exact ⟨by rintro ⟨hx, hy, h⟩; exact ⟨⟨hx,hy⟩, (he hx hy).mp h⟩,
      by rintro ⟨⟨hx,hy⟩, h⟩; exact ⟨hx, hy, (he hx hy).mpr h⟩⟩
  let U₀ := rvLift U.obj
  let R₀ (x : P.Carrier) (y : Q.Carrier) := ∃ p : U₀, p.val = x ∧ T (g p).val y
  have hR₀ : P.RelationDefinable Q S R₀ := (g.graph_definable.comp P W Q hT).congr P Q (by
    intro x y
    constructor
    · rintro ⟨_, ⟨p, hp, rfl⟩, h⟩
      exact ⟨p, hp, h⟩
    · rintro ⟨p, hp, h⟩
      exact ⟨(g p).val, ⟨p, hp, rfl⟩, h⟩)
  have hdom (x : P.Carrier) (y : Q.Carrier) (h : R₀ x y) : x ∈ U₀.carrier ∧ y ∈ Set.univ := by
    obtain ⟨p, rfl, _⟩ := h
    exact ⟨p.property, Set.mem_univ _⟩
  have htotal (p : U₀) : ∃ y, R₀ p.val y := by
    obtain ⟨c, hc, _⟩ := hRep p
    exact ⟨fun _ => c, p, rfl, hc⟩
  have huniq (x : P.Carrier) (y z : Q.Carrier) (hy : R₀ x y) (hz : R₀ x z) : y = z := by
    obtain ⟨p, hp, hy⟩ := hy
    obtain ⟨p', hp', hz⟩ := hz
    have he : p' = p := Subtype.ext (hp'.trans hp.symm)
    subst p'
    funext i
    fin_cases i
    exact Subtype.ext (hSingle _ _ _ hy hz)
  let c : Map U₀ (DefSet.univ Q S) := Map.ofFunctionalRelation hR₀ hdom htotal huniq
  have hcR (p : U₀) : R₀ p.val (c p).val := Map.ofFunctionalRelation_graph hR₀ hdom htotal huniq p
  refine ⟨c, ?_, fun p => ?_⟩
  · -- Gamma graph: the image relation followed by the real representative relation
    have hT' : GammaGraphDefinable B (fun (y : Point (M := M) k 1) (z : Point (M := M) 1 0) =>
        (gammaPointCode y, (z.1 0).val) ∈ R) := by
      let ι : Fin (k + 1) ⊕ Fin 1 → Fin ((k + 1) + (1 + 0)) :=
        Sum.elim (Fin.castAdd (1 + 0)) (fun _ => Fin.natAdd (k + 1) (0 : Fin (1 + 0)))
      apply gamma_graph_of_raw hc _ {w | (w ∘ Fin.castAdd (1 + 0), w (Fin.natAdd (k + 1) (0 : Fin (1 + 0)))) ∈ R}
      · have h := hR.preimage_comp ι
        convert h using 1
        ext w
        exact Iff.rfl
      · intro y z
        change _ ↔ (Fin.append (gammaPointCode y) (gammaPointCode z) ∘ Fin.castAdd (1 + 0),
          Fin.append (gammaPointCode y) (gammaPointCode z) (Fin.natAdd (k + 1) (0 : Fin (1 + 0)))) ∈ R
        rw [Fin.append_right]
        have h1 : Fin.append (gammaPointCode y) (gammaPointCode z) ∘ Fin.castAdd (1 + 0) = gammaPointCode y := by
          funext i
          exact Fin.append_left _ _ i
        rw [h1]
        rfl
    apply SpecialTransformations.Section5.GammaGraphDefinable.congr (L.comp_graph hQ hT')
    intro p z
    constructor
    · rintro ⟨y, ⟨x, rfl, rfl⟩, hy⟩
      refine ⟨x, rfl, ?_⟩
      have hR' : R₀ x.val z.1 := ⟨x, rfl, by
        change (code x, (z.1 0).val) ∈ R
        rw [hcodeY]
        exact hy⟩
      exact huniq _ _ _ (hcR x) hR'
    · rintro ⟨x, rfl, hz⟩
      refine ⟨(x.val.1, (f x).val), ⟨x, rfl, rfl⟩, ?_⟩
      obtain ⟨x', hx', hT''⟩ := hcR x
      have he : x' = x := Subtype.ext hx'
      subst he
      rw [← hz]
      change (gammaPointCode ((x'.val.1, (f x').val) : Point (M := M) k 1), ((c x').val 0).val) ∈ R
      rw [← hcodeY]
      exact hT''
  · obtain ⟨a, ha, hrv⟩ := hRep p
    have he : (c p).val = fun _ => a := huniq p.val _ _ (hcR p) ⟨p, rfl, ha⟩
    exact (congrArg CanonicalRV.encodedRv (congrFun he 0)).trans hrv

end SpecialTransformations.Section9.GammaLift
