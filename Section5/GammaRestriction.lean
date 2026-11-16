module

public import Section5.GammaLogic

@[expose] public section

/-! Restriction preserves complete invariant-Gamma focus graphs. The
geometric primitives and alternating chains are the existing Section 5
ones; no second language or set-theoretic transformation class is used. -/

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
variable {B : Section3.GammaParameters.Base (M := M)} (hΓ : GammaLogicInput B)
variable {S : Set M} {n m l : ℕ}

include hΓ

theorem GammaFocusDefinable.of_real {A : DefSet (M := M) B.real n m}
    {j : Fin n} {k : Fin m} (D : Focus A j k) : GammaFocusDefinable B D := by
  refine ⟨hΓ.real_set D.locus D.locus_definable, ?_⟩
  change GammaScalarGraphDefinable B
    (fun p x => p ∈ carrier A ∩ D.locus ∧ x = D.center p)
  apply GammaScalarGraphDefinable.congr (hΓ.real_scalar_graph D.centerMap)
  intro p x
  constructor
  · rintro ⟨a, rfl, he⟩
    exact ⟨a.property, he.symm⟩
  · rintro ⟨hp, he⟩
    exact ⟨⟨p, hp⟩, rfl, he.symm⟩

theorem GammaFocusDefinable.restrict {A C : DefSet (M := M) S n m}
    {j : Fin n} {k : Fin m} (D : Focus A j k) (hCA : carrier C ⊆ carrier A)
    (hD : GammaFocusDefinable B D) (hC : GammaSetDefinable B (carrier C)) :
    GammaFocusDefinable B (D.restrict hCA) := by
  refine ⟨hΓ.inter hD.1 (hΓ.hull hC), ?_⟩
  apply GammaGraphDefinable.congr (hΓ.restrict_graph hC hD.2)
  intro p z
  constructor
  · rintro ⟨hp, ⟨ha, hl⟩, he⟩
    exact ⟨⟨hp, hl, subset_hull _ hp⟩, he⟩
  · rintro ⟨⟨hp, hl, _⟩, he⟩
    exact ⟨hp, ⟨hCA hp, hl⟩, he⟩

def affineGraphMap (j : Fin n) (S : Set M) :
    Map (PresentedSet.univ (spaceProd (pointSpace (M := M) n m) (Section4.vfSpace 1)) S)
      (PresentedSet.univ (spaceProd (pointSpace n m) (pointSpace n m)) S) :=
  let H := PresentedSet.univ (spaceProd (pointSpace n m) (Section4.vfSpace 1)) S
  let fst := @DefinableGeometry.Map.fst LRV M (CanonicalStructure.normalize (M := M))
    (pointSpace n m) (Section4.vfSpace 1) S H
  Map.comp (Map.inclusion (Set.subset_univ _)) (Map.pair fst (subtractMap j H))

omit hΓ in theorem affineGraphMap_apply (j : Fin n) (S : Set M)
    (p : Point (M := M) n m) (x : VF (M := M)) :
    (affineGraphMap j S ⟨(p, ![x]), Set.mem_univ _⟩).val =
      (p, replace j p (vfAt p j - x)) := rfl

theorem gamma_eta_graph {A : DefSet (M := M) S n m} {j : Fin n} {k : Fin m}
    (D : Focus A j k) (hA : GammaSetDefinable B (carrier A)) (hD : GammaFocusDefinable B D) :
    GammaGraphDefinable B (pointMapGraph D.etaMap) := by
  have hs : GammaScalarGraphDefinable B
      (fun p x => p ∈ carrier A ∩ D.locus ∧ x = D.center p) := hD.2
  have hactive := hΓ.scalar_image_graph hs (affineGraphMap j B.real)
  have hinactive := hΓ.restrict_graph (hΓ.sdiff hA hD.1)
    (hΓ.real_map_graph (Map.id (PresentedSet.univ (pointSpace n m) B.real)))
  apply GammaGraphDefinable.congr (hΓ.union_graph hactive hinactive)
  intro p q
  constructor
  · rintro (⟨a, x, ⟨ha, hx⟩, he⟩ | ⟨hp, a, ha, he⟩)
    · have hh := (affineGraphMap_apply j B.real a x).symm.trans he
      have hp : a = p := congrArg Prod.fst hh
      subst p
      have hq := congrArg Prod.snd hh
      refine ⟨⟨a, ha.1⟩, rfl, ?_⟩
      change D.toFocusGeometry.eta a = q
      rw [FocusGeometry.eta, if_pos ha.2]
      exact (congrArg (fun y : VF (M := M) => replace j a (vfAt a j - y)) hx).symm.trans hq
    · have heq : p = q := ha.symm.trans he
      refine ⟨⟨p, hp.1⟩, rfl, ?_⟩
      change D.toFocusGeometry.eta p = q
      rw [FocusGeometry.eta, if_neg hp.2]
      exact heq
  · rintro ⟨a, rfl, he⟩
    change D.toFocusGeometry.eta a.val = q at he
    by_cases hl : a.val ∈ D.locus
    · left
      refine ⟨a.val, D.center a.val, ⟨⟨a.property, hl⟩, rfl⟩, ?_⟩
      have heta : D.toFocusGeometry.eta a.val =
          replace j a.val (vfAt a.val j - D.center a.val) := by
        rw [FocusGeometry.eta, if_pos hl]
        rfl
      exact (affineGraphMap_apply j B.real a.val (D.center a.val)).trans
        (Prod.ext rfl (heta.symm.trans he))
    · right
      refine ⟨⟨a.property, hl⟩, ⟨a.val, Set.mem_univ _⟩, rfl, ?_⟩
      have heta : D.toFocusGeometry.eta a.val = a.val := by rw [FocusGeometry.eta, if_neg hl]
      exact heta.symm.trans he

theorem GammaPrimitiveDefinable.source {A : DefSet (M := M) S n m}
    {C : DefSet (M := M) S n l} (p : Primitive S n A C)
    (hp : GammaPrimitiveDefinable B p) : GammaSetDefinable B (carrier A) := by
  cases p <;> first | exact hp | exact hp.1

theorem GammaPrimitiveDefinable.graph {A : DefSet (M := M) S n m}
    {C : DefSet (M := M) S n l} (p : Primitive S n A C)
    (hp : GammaPrimitiveDefinable B p) : GammaGraphDefinable B (pointMapGraph p.toMap) := by
  cases p with
  | canonical A =>
    have hc := hΓ.restrict_graph hp
      (hΓ.real_map_graph (canonicalMap (PresentedSet.univ (pointSpace n m) B.real)))
    apply GammaGraphDefinable.congr hc
    intro p q
    constructor
    · rintro ⟨hp, a, rfl, he⟩
      exact ⟨⟨a.val, hp⟩, rfl, he⟩
    · rintro ⟨a, rfl, he⟩
      exact ⟨a.property, ⟨a.val, Set.mem_univ _⟩, rfl, he⟩
  | centripetal D => exact gamma_eta_graph hΓ D hp.1 hp.2

theorem GammaPrimitiveDefinable.target {A : DefSet (M := M) S n m}
    {C : DefSet (M := M) S n l} (p : Primitive S n A C)
    (hp : GammaPrimitiveDefinable B p) : GammaSetDefinable B (carrier C) := by
  have hh := hΓ.image_graph (GammaPrimitiveDefinable.graph hΓ p hp)
  convert hh using 1
  ext q
  constructor
  · intro hq
    obtain ⟨a, ha⟩ := p.bijective.2 ⟨q, hq⟩
    exact ⟨a.val, a, rfl, congrArg Subtype.val ha⟩
  · rintro ⟨z, a, _, he⟩
    exact he ▸ (p.toMap a).property

theorem GammaPrimitiveDefinable.of_real {A : DefSet (M := M) B.real n m}
    {C : DefSet (M := M) B.real n l} (p : Primitive B.real n A C) :
    GammaPrimitiveDefinable B p := by
  cases p with
  | canonical A => exact hΓ.real_set _ (setDefinable A)
  | centripetal D => exact ⟨hΓ.real_set _ (setDefinable A), GammaFocusDefinable.of_real hΓ D⟩

theorem GammaChainDefinable.of_real {A : DefSet (M := M) B.real n m}
    {C : DefSet (M := M) B.real n l} (T : Chain B.real n A C) : GammaChainDefinable B T := by
  induction T with
  | nil A => exact hΓ.real_set _ (setDefinable A)
  | cons p tail ih => exact ⟨GammaPrimitiveDefinable.of_real hΓ p, ih⟩

theorem gamma_restrict_primitive {A : DefSet (M := M) S n m}
    {C : DefSet (M := M) S n l} (p : Primitive S n A C)
    (hp : GammaPrimitiveDefinable B p) (D : DefSet (M := M) S n m)
    (hDA : carrier D ⊆ carrier A) (hD : GammaSetDefinable B (carrier D)) :
    ∃ E : DefSet (M := M) S n l, ∃ q : Primitive S n D E,
      q.kind = p.kind ∧ carrier E ⊆ carrier C ∧ GammaPrimitiveDefinable B q ∧
        GammaSetDefinable B (carrier E) ∧
        ∀ a : D, (q.toMap a).val = (p.toMap ⟨a.val, hDA a.property⟩).val := by
  cases p with
  | canonical A =>
    let q := Primitive.canonical D
    refine ⟨canonicalImage D, q, rfl, ?_, hD, GammaPrimitiveDefinable.target hΓ q hD, fun _ => rfl⟩
    rw [canonicalImage_carrier, canonicalImage_carrier]
    exact Set.image_mono hDA
  | centripetal F =>
    let q := Primitive.centripetal (F.restrict hDA)
    have hq : GammaPrimitiveDefinable B q :=
      ⟨hD, GammaFocusDefinable.restrict hΓ F hDA hp.2 hD⟩
    exact ⟨(F.restrict hDA).etaImage, q, rfl, F.restrict_image_subset hDA,
      hq, GammaPrimitiveDefinable.target hΓ q hq, fun a => F.restrict_eta hDA a.val a.property⟩

theorem gamma_restrict_chain {A : DefSet (M := M) S n m}
    {C : DefSet (M := M) S n l} (T : Chain S n A C) :
    ∀ (hT : GammaChainDefinable B T) (D : DefSet (M := M) S n m)
      (hDA : carrier D ⊆ carrier A), GammaSetDefinable B (carrier D) →
    ∀ previous : Option Bool, T.Alternating previous →
    ∃ E : DefSet (M := M) S n l, ∃ U : Chain S n D E,
      U.Alternating previous ∧ GammaChainDefinable B U ∧ carrier E ⊆ carrier C ∧
        ∀ a : D, (U.toMap a).val = (T.toMap ⟨a.val, hDA a.property⟩).val := by
  induction T with
  | nil A =>
    intro hT D hDA hD previous _
    exact ⟨D, .nil D, trivial, hD, hDA, fun _ => rfl⟩
  | cons p tail ih =>
    intro hT D hDA hD previous hAlt
    obtain ⟨hprev, htail⟩ := (Chain.cons_alternating_iff p tail previous).mp hAlt
    obtain ⟨D', q, hkind, hsub, hq, hD', hc⟩ := gamma_restrict_primitive hΓ p hT.1 D hDA hD
    obtain ⟨E, U, hU, hUG, hE, hu⟩ := ih hT.2 D' hsub hD' (some p.kind) htail
    refine ⟨E, .cons q U, ?_, ⟨hq, hUG⟩, hE, ?_⟩
    · apply (Chain.cons_alternating_iff q U previous).mpr
      simpa only [hkind] using And.intro hprev hU
    · intro a
      change (U.toMap (q.toMap a)).val = (tail.toMap (p.toMap ⟨a.val, hDA a.property⟩)).val
      have he : (⟨(q.toMap a).val, hsub (q.toMap a).property⟩ : _) =
          p.toMap ⟨a.val, hDA a.property⟩ := Subtype.ext (hc a)
      rw [hu (q.toMap a), he]

theorem SpecialBijection.restrict_gamma_at {A : DefSet (M := M) S n m}
    {C : DefSet (M := M) S n l} (T : SpecialBijection A C)
    (hT : GammaChainDefinable B T.chain) (D : DefSet (M := M) S n m)
    (hDA : carrier D ⊆ carrier A) (hD : GammaSetDefinable B (carrier D))
    (previous : Option Bool) (hAlt : T.chain.Alternating previous) :
    ∃ E : DefSet (M := M) S n l, ∃ U : SpecialBijection D E,
      U.chain.Alternating previous ∧ GammaChainDefinable B U.chain ∧
        carrier E ⊆ carrier C ∧
        carrier E = {q | ∃ a : D, (T.toMap ⟨a.val, hDA a.property⟩).val = q} ∧
        ∀ a : D, (U.toMap a).val = (T.toMap ⟨a.val, hDA a.property⟩).val := by
  obtain ⟨E, V, hV, hVG, hEC, hc⟩ := gamma_restrict_chain hΓ T.chain hT D hDA hD previous hAlt
  let U : SpecialBijection D E := ⟨V, V.alternating_none previous hV⟩
  refine ⟨E, U, hV, hVG, hEC, ?_, hc⟩
  ext q
  constructor
  · intro hq
    obtain ⟨a, ha⟩ := U.bijective.2 ⟨q, hq⟩
    exact ⟨a, (hc a).symm.trans (congrArg Subtype.val ha)⟩
  · rintro ⟨a, ha⟩
    have he : (U.toMap a).val = q := (hc a).trans ha
    exact he ▸ (U.toMap a).property

theorem GammaChainDefinable.graph {A : DefSet (M := M) S n m}
    {C : DefSet (M := M) S n l} (T : Chain S n A C) :
    GammaChainDefinable B T → GammaGraphDefinable B (pointMapGraph T.toMap) := by
  induction T with
  | @nil a A =>
    intro hA
    have hh := hΓ.restrict_graph hA
      (hΓ.real_map_graph (Map.id (PresentedSet.univ (pointSpace n a) B.real)))
    apply GammaGraphDefinable.congr hh
    intro p q
    constructor
    · rintro ⟨hp, a, rfl, he⟩
      exact ⟨⟨a.val, hp⟩, rfl, he⟩
    · rintro ⟨a, rfl, he⟩
      exact ⟨a.property, ⟨a.val, Set.mem_univ _⟩, rfl, he⟩
  | cons p tail ih =>
    intro hT
    have hh := hΓ.comp_graph (GammaPrimitiveDefinable.graph hΓ p hT.1) (ih hT.2)
    apply GammaGraphDefinable.congr hh
    intro x y
    constructor
    · rintro ⟨z, ⟨a, ha, hz⟩, ⟨b, hb, hy⟩⟩
      have he : b = p.toMap a := Subtype.ext (hb.trans hz.symm)
      refine ⟨a, ha, ?_⟩
      exact (congrArg (fun b => (tail.toMap b).val) he).symm.trans hy
    · rintro ⟨a, ha, hy⟩
      exact ⟨(p.toMap a).val, ⟨a, ha, rfl⟩, ⟨p.toMap a, rfl, hy⟩⟩

theorem gamma_inverse_graph {A : DefSet (M := M) S n m}
    {C : DefSet (M := M) S n l} (T : SpecialBijection A C)
    (hT : GammaChainDefinable B T.chain) : GammaGraphDefinable B (pointMapGraph T.inverseMap) := by
  apply GammaGraphDefinable.congr (hΓ.swap_graph (GammaChainDefinable.graph hΓ T.chain hT))
  intro q p
  constructor
  · rintro ⟨a, ha, hq⟩
    refine ⟨T.toMap a, hq, ?_⟩
    rw [T.inverse_apply]
    exact ha
  · rintro ⟨b, hb, hp⟩
    exact ⟨T.inverseMap b, hp, (congrArg Subtype.val (T.apply_inverse b)).trans hb⟩

end SpecialTransformations.Section5
