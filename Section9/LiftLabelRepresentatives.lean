import Section9.FiniteHeadRepresentatives
import Section4.CanonicalLift
import Section4.CodeMaps
import Section4.FunctionalRelations
import Section4.MapCorestrict
import Section4.VFRealFibres

/-! RV labels in a finite-volume head lift admit uniform VF
representatives. The input to a representative is the VF head and
the RV value to be represented. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section7
open SpecialTransformations.DefinableGeometry

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

noncomputable def liftLabelMap (U : RVObject (M := M) S k) : Map (rvLift U) U.domain :=
  (Map.snd (rawVFSpace (M := M) k) (rawRVSpace U.arity) S (rvLift U)).corestrict
    (fun p => by
      obtain ⟨u, hu, _⟩ := p.property
      change p.val.2 ∈ U.domain.carrier
      exact hu ▸ u.property)

theorem exists_representatives_for_liftLabelMap
    (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    (hB : VFGammaGeneratedBase B) (U : RVFiniteObject (M := M) B.real k)
    (τ : Map U.obj.domain (DefSet.univ (rawRVSpace (M := M) 1) B.real))
    (hτ : ∀ u, ((τ u).val 0).val ≠ iRVZero) :
    ∃ R : Set ((Fin (k + 1) → M) × M), RawClosure.Tuple.RelationDefinable B.real R ∧
      RawClosure.Tuple.SingleValued R ∧
      ∀ p : rvLift U.obj, ∃ c : VFType (M := M),
        (productTuple (vfValues p.val.1) (rvValues (τ (liftLabelMap U.obj p)).val), c.val) ∈ R ∧
        CanonicalRV.encodedRv c = (τ (liftLabelMap U.obj p)).val 0 := by
  let V := rawVFSpace (M := M) k
  let W := rawMixedSpace (M := M) k 1
  let f := τ.comp (liftLabelMap U.obj)
  let g := (Map.fst V (rawRVSpace U.obj.arity) B.real (rvLift U.obj)).pair f
  let D : DefSet W B.real := g.image
  let e : Fin k ⊕ Fin 1 ≃ Fin (k + 1) := finSumFinEquiv
  let code (p : rvLift U.obj) := productTuple (vfValues p.val.1) (rvValues (f p).val)
  let C := Set.range code
  have hcode (p : rvLift U.obj) : code p ∘ e = mixedValues (g p).val := by
    funext i
    cases i with
    | inl j => exact productTuple_left _ _ j
    | inr j => exact productTuple_right _ _ j
  have hEq : C = (fun z => z ∘ e) ⁻¹' W.preimage D.carrier := by
    ext z
    constructor
    · rintro ⟨p, rfl⟩
      change code p ∘ e ∈ W.preimage D.carrier
      rw [hcode]
      refine ⟨mixedValues_mem_domain _, ?_⟩
      have hd : (g p).val ∈ D.carrier := Set.mem_range_self p
      simpa only [W, D, Map.image, decode_mixedValues] using hd
    · rintro ⟨hz, hD⟩
      obtain ⟨p, hp⟩ := hD
      refine ⟨p, ?_⟩
      have hh := (hcode p).trans ((congrArg mixedValues hp).trans (mixedValues_decode ⟨z ∘ e, hz⟩))
      funext i
      obtain ⟨j, rfl⟩ := e.surjective i
      exact congrFun hh j
  have hraw : B.real.Definable LRV C := hEq.symm ▸ D.definable.preimage_comp e
  have hC : DefinableOverBase B (headRVSort k) C := by
    apply real_definableOverBase B
    apply raw_definableOver_sorted hc _ _ _ hraw
    rintro _ ⟨p, rfl⟩ i
    obtain ⟨j, rfl⟩ := e.surjective i
    cases j with
    | inl j =>
      change sortEval (headRVSort k (productLeft k 1 j)) (code p (productLeft k 1 j))
      simpa only [headRVSort, code, productTuple_left, sortEval, iVF, vfValues] using (p.val.1 j).property
    | inr j =>
      change sortEval (headRVSort k (productRight k 1 j)) (code p (productRight k 1 j))
      simpa only [headRVSort, code, productTuple_right, sortEval, iRV, rvValues] using ((f p).val j).property
  have hfin (a : Fin k → M) : {b : Fin 1 → M | productTuple a b ∈ C}.Finite := by
    let Q := {b : Fin 1 → M | productTuple a b ∈ C}
    change Q.Finite
    by_cases hQ : Q.Nonempty
    · obtain ⟨b, p₀, hp₀⟩ := hQ
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
    · rw [show Q = ∅ from Set.not_nonempty_iff_eq_empty.mp hQ]
      exact Set.finite_empty
  have hnz : ∀ z ∈ C, z (productRight k 1 0) ≠ iRVZero := by
    rintro _ ⟨p, rfl⟩
    simpa only [code, productTuple_right, f, rvValues, Map.comp_apply]
      using hτ (liftLabelMap U.obj p)
  obtain ⟨R, hR, hSingle, hRep, hExists⟩ := exists_uniform_finiteHead_representatives
    hκ hs h00 B hsmall hB C hC hfin hnz
  refine ⟨R, hR, hSingle, fun p => ?_⟩
  obtain ⟨z, hz⟩ := hExists (code p) (Set.mem_range_self p)
  have hz' := hRep _ hz
  refine ⟨⟨z, hz'.1⟩, hz, Subtype.ext ?_⟩
  change iRv z = ((τ (liftLabelMap U.obj p)).val 0).val
  simpa only [code, productTuple_right, f, rvValues, Map.comp_apply] using hz'.2

theorem exists_liftLabelRepresentative
    (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    (hB : VFGammaGeneratedBase B) (U : RVFiniteObject (M := M) B.real k)
    (τ : Map U.obj.domain (DefSet.univ (rawRVSpace (M := M) 1) B.real))
    (hτ : ∀ u, ((τ u).val 0).val ≠ iRVZero) :
    ∃ c : Map (rvLift U.obj) (DefSet.univ (rawVFSpace (M := M) 1) B.real),
      ∀ p, CanonicalRV.encodedRv ((c p).val 0) = (τ (liftLabelMap U.obj p)).val 0 := by
  obtain ⟨R, hR, hSingle, hRep⟩ :=
    exists_representatives_for_liftLabelMap hc hκ hs h00 B hsmall hB U τ hτ
  let P := rawMixedSpace (M := M) k U.obj.arity
  let W := rawMixedSpace (M := M) k 1
  let Q := rawVFSpace (M := M) 1
  let g := (Map.fst (rawVFSpace (M := M) k) (rawRVSpace U.obj.arity) B.real (rvLift U.obj)).pair
    (τ.comp (liftLabelMap U.obj))
  let T (x : W.Carrier) (y : Q.Carrier) := (productTuple (vfValues x.1) (rvValues x.2), (y 0).val) ∈ R
  let e : Fin k ⊕ Fin 1 ≃ Fin (k + 1) := finSumFinEquiv
  let σ : Fin (k + 1) ⊕ Fin 1 → W.Index ⊕ Q.Index := Sum.elim (Sum.inl ∘ e.symm) Sum.inr
  have hT : W.RelationDefinable Q B.real T := by
    have h := hR.preimage_comp σ
    have hd := ((W.domain_definable.mono (Set.empty_subset B.real)).preimage_comp Sum.inl).inter
      ((Q.domain_definable.mono (Set.empty_subset B.real)).preimage_comp Sum.inr)
    change B.real.Definable LRV (W.relation Q T)
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
  have hR₀ : P.RelationDefinable Q B.real R₀ := (g.graph_definable.comp P W Q hT).congr P Q (by
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
  let c : Map U₀ (DefSet.univ Q B.real) := Map.ofFunctionalRelation hR₀ hdom htotal huniq
  refine ⟨c, fun p => ?_⟩
  obtain ⟨a, ha, hrv⟩ := hRep p
  have he : (c p).val = fun _ => a := huniq p.val _ _
    (Map.ofFunctionalRelation_graph hR₀ hdom htotal huniq p) ⟨p, rfl, ha⟩
  exact (congrArg CanonicalRV.encodedRv (congrFun he 0)).trans hrv

end SpecialTransformations.Section9
