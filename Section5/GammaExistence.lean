module

public import Section5.GammaRestriction
public import Section5.TaggedAmbient
public import Section5.PolynomialPreparation

@[expose] public section

/-!
# Preparation over an actual named-Gamma base

Earlier QE supplies finite VF polynomial support for invariant graph
preimages. Those polynomials are prepared over the real base. The resulting
chain is extended only internally to the real presentation and restricted
with the invariant-focus certificate. Gamma representatives never enter the
named base of the conclusion.
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
variable {B : Section3.GammaParameters.Base (M := M)}
variable {S : Set M} {n m l k : ℕ}

/-- Earlier QE support for the full invariant graph, with all RV variables
left free. No transformation, locus or contraction is assumed here. -/
def GammaPolynomialSupportInput (B : Section3.GammaParameters.Base (M := M)) : Prop :=
  ∀ {n m k : ℕ} (r : Point (M := M) n m → Point (M := M) 0 k → Prop),
    GammaGraphDefinable B r →
  ∃ d : ℕ, ∃ p : Fin d → MvPolynomial (Fin n) (VF (M := M)),
    (∀ i e, ((p i).coeff e).val ∈ B.real) ∧
    ∀ x y : Point (M := M) n m, x.2 = y.2 →
      (∀ i, rv (MvPolynomial.eval (vfAt x) (p i)) = rv (MvPolynomial.eval (vfAt y) (p i))) →
      ∀ z : Point (M := M) 0 k, r x z ↔ r y z

theorem gamma_restrict_prepared_map (hΓ : GammaLogicInput B)
    {A D : DefSet (M := M) S n m} {C : DefSet (M := M) S n l}
    (hDA : carrier D ⊆ carrier A) (hD : GammaSetDefinable B (carrier D))
    (T : SpecialBijection A C) (hTG : GammaChainDefinable B T.chain)
    (hC : IsRVPullback (carrier C)) (previous : Option Bool) (hTa : T.chain.Alternating previous)
    (f : Map D (PresentedSet.univ (pointSpace (M := M) 0 k) S))
    (hc : ∀ b c : C, SameRV b.val c.val →
      ((T.inverseMap b).val ∈ carrier D ↔ (T.inverseMap c).val ∈ carrier D) ∧
      ∀ d e : D, d.val = (T.inverseMap b).val → e.val = (T.inverseMap c).val →
        (f d).val.2 = (f e).val.2) :
    ∃ E : DefSet (M := M) S n l, ∃ V : SpecialBijection D E,
      V.chain.Alternating previous ∧ GammaChainDefinable B V.chain ∧
        IsRVPullback (carrier E) ∧ Contractible (Map.comp f V.inverseMap) := by
  obtain ⟨E, V, hVa, hVG, hEC, hImage, hcomm⟩ :=
    SpecialBijection.restrict_gamma_at hΓ T hTG D hDA hD previous hTa
  have hInv (b : E) : (T.inverseMap ⟨b.val, hEC b.property⟩).val = (V.inverseMap b).val := by
    have he : T.toMap ⟨(V.inverseMap b).val, hDA (V.inverseMap b).property⟩ =
        (⟨b.val, hEC b.property⟩ : C) := by
      apply Subtype.ext
      exact (hcomm (V.inverseMap b)).symm.trans (congrArg Subtype.val (V.apply_inverse b))
    rw [← he, T.inverse_apply]
  refine ⟨E, V, hVa, hVG, (isRVPullback_iff _).mpr ?_, ?_⟩
  · intro p hp q he
    let b : C := ⟨p, hEC hp⟩
    have hqC := (isRVPullback_iff _).mp hC p b.property q he
    let c : C := ⟨q, hqC⟩
    have hbD : (T.inverseMap b).val ∈ carrier D :=
      (hInv ⟨p, hp⟩).symm ▸ (V.inverseMap ⟨p, hp⟩).property
    have hcD := (hc b c he).1.mp hbD
    have hqI : q ∈ {z | ∃ d : D, (T.toMap ⟨d.val, hDA d.property⟩).val = z} := by
      refine ⟨⟨(T.inverseMap c).val, hcD⟩, ?_⟩
      have heq : (⟨(T.inverseMap c).val, hDA hcD⟩ : A) = T.inverseMap c := Subtype.ext rfl
      rw [heq, T.apply_inverse]
    exact hImage.symm ▸ hqI
  · intro b c he
    have hv := (hc ⟨b.val, hEC b.property⟩ ⟨c.val, hEC c.property⟩ he).2
      (V.inverseMap b) (V.inverseMap c) (hInv b).symm (hInv c).symm
    exact (sameRV_iff _ _).mpr ⟨fun i => i.elim0, hv⟩

theorem gamma_rvMap_preparation_at_boundary {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (h00 : M ⊨ Axioms.ACVF00) (v : Valuation (VF (M := M)) Γ)
    (hv : ∀ x y : VF (M := M), VFValued.predV x y ↔ v x ≤ v y)
    (hObstacles : ∀ N, UniformVerticalObstacles v B.real N)
    (hΓ : GammaLogicInput B) (hSupport : GammaPolynomialSupportInput B)
    (hBS : B.real ⊆ S) (A : DefSet (M := M) S n m)
    (hA : GammaSetDefinable B (carrier A))
    (f : Map A (PresentedSet.univ (pointSpace (M := M) 0 k) S))
    (hf : GammaGraphDefinable B (pointMapGraph f)) (previous : Option Bool)
    (hTags : previous = some false → AllTagged A) :
    ∃ r : ℕ, ∃ D : DefSet (M := M) S n r, ∃ U : SpecialBijection A D,
      U.chain.Alternating previous ∧ GammaChainDefinable B U.chain ∧
        IsRVPullback (carrier D) ∧ Contractible (Map.comp f U.inverseMap) := by
  obtain ⟨d, p, hcoeff, hcontrol⟩ := hSupport (pointMapGraph f) hf
  have hambient : ∃ E : DefSet (M := M) B.real n m,
      carrier A ⊆ carrier E ∧ (previous = some false → AllTagged E) := by
    by_cases hprev : previous = some false
    · obtain ⟨E, hAE, hEt, _⟩ := exists_taggedAmbient (S := B.real) (carrier A) (hTags hprev)
      exact ⟨E, hAE, fun _ => hEt⟩
    · exact ⟨PresentedSet.univ (pointSpace n m) B.real, Set.subset_univ _,
        fun h => False.elim (hprev h)⟩
  obtain ⟨E, hAE, hEt⟩ := hambient
  let g := mvPolynomialTupleMap E p hcoeff
  obtain ⟨r, C, T, hTa, hC, hg⟩ := map_preparation_at_boundary h00 v hv hObstacles previous hEt g
  let W := T.extendBase hBS
  have hWa := T.chain.extendBase_alternating hBS previous hTa
  have hWG : GammaChainDefinable B W.chain :=
    GammaChainDefinable.extendBase B T.chain hBS (GammaChainDefinable.of_real hΓ T.chain)
  have hprepared : ∀ b c : extendBase C hBS, SameRV b.val c.val →
      ((W.inverseMap b).val ∈ carrier A ↔ (W.inverseMap c).val ∈ carrier A) ∧
      ∀ a e : A, a.val = (W.inverseMap b).val → e.val = (W.inverseMap c).val →
        (f a).val.2 = (f e).val.2 := by
    intro b c he
    let b₀ : C := ⟨b.val, b.property⟩
    let c₀ : C := ⟨c.val, c.property⟩
    have hInvb := T.extendBase_inverse hBS b
    have hInvc := T.extendBase_inverse hBS c
    have hpoly : ∀ i, rv (MvPolynomial.eval (vfAt (W.inverseMap b).val) (p i)) =
        rv (MvPolynomial.eval (vfAt (W.inverseMap c).val) (p i)) := by
      intro i
      have hh := ((sameRV_iff _ _).mp (hg b₀ c₀ he)).1 i
      change rv (MvPolynomial.eval (vfAt (T.inverseMap b₀).val) (p i)) =
        rv (MvPolynomial.eval (vfAt (T.inverseMap c₀).val) (p i)) at hh
      exact (congrArg (fun z : Point (M := M) n m => rv (MvPolynomial.eval (vfAt z) (p i))) hInvb).trans
        (hh.trans (congrArg (fun z : Point (M := M) n m => rv (MvPolynomial.eval (vfAt z) (p i))) hInvc).symm)
    have hlabels := ((sameRV_iff _ _).mp (W.inverse_contractible b c he)).2
    have hc := hcontrol (W.inverseMap b).val (W.inverseMap c).val hlabels hpoly
    constructor
    · constructor
      · intro hb
        let a : A := ⟨(W.inverseMap b).val, hb⟩
        obtain ⟨e, he, _⟩ := (hc (f a).val).mp ⟨a, rfl, rfl⟩
        exact he ▸ e.property
      · intro hc'
        let e : A := ⟨(W.inverseMap c).val, hc'⟩
        obtain ⟨a, ha, _⟩ := (hc (f e).val).mpr ⟨e, rfl, rfl⟩
        exact ha ▸ a.property
    · intro a e ha he
      obtain ⟨z, hz, hzf⟩ := (hc (f a).val).mp ⟨a, ha, rfl⟩
      have hze : z = e := Subtype.ext (hz.trans he.symm)
      have hh : (f e).val = (f a).val := hze ▸ hzf
      exact (congrArg Prod.snd hh).symm
  obtain ⟨D, U, hUa, hUG, hD, hf⟩ := gamma_restrict_prepared_map hΓ hAE hA W hWG hC previous hWa f hprepared
  exact ⟨r, D, U, hUa, hUG, hD, hf⟩

def postcomposeRealMap {u w a b : ℕ} {A : DefSet (M := M) S n m}
    {D : DefSet (M := M) S u w} (f : Map A D)
    (g : Map (PresentedSet.univ (pointSpace (M := M) u w) B.real)
      (PresentedSet.univ (pointSpace a b) B.real)) (hBS : B.real ⊆ S) :
    Map A (PresentedSet.univ (pointSpace a b) S) :=
  Map.comp
    (@DefinableGeometry.Map.extend LRV M (CanonicalStructure.normalize (M := M))
      (pointSpace u w) (pointSpace a b) B.real S _ _ g hBS)
    (Map.comp (Map.inclusion (Set.subset_univ _)) f)

theorem postcomposeRealMap_apply {u w a b : ℕ} {A : DefSet (M := M) S n m}
    {D : DefSet (M := M) S u w} (f : Map A D)
    (g : Map (PresentedSet.univ (pointSpace (M := M) u w) B.real)
      (PresentedSet.univ (pointSpace a b) B.real)) (hBS : B.real ⊆ S) (x : A) :
    (postcomposeRealMap f g hBS x).val = (g ⟨(f x).val, Set.mem_univ _⟩).val := rfl

theorem gamma_postcompose_real (hΓ : GammaLogicInput B) {u w a b : ℕ}
    {A : DefSet (M := M) S n m} {D : DefSet (M := M) S u w} (f : Map A D)
    (hf : GammaGraphDefinable B (pointMapGraph f))
    (g : Map (PresentedSet.univ (pointSpace (M := M) u w) B.real)
      (PresentedSet.univ (pointSpace a b) B.real)) (hBS : B.real ⊆ S) :
    GammaGraphDefinable B (pointMapGraph (postcomposeRealMap f g hBS)) := by
  apply GammaGraphDefinable.congr (hΓ.comp_graph hf (hΓ.real_map_graph g))
  intro p q
  constructor
  · rintro ⟨z, ⟨x, hx, hz⟩, ⟨y, hy, hq⟩⟩
    have he : y = (⟨(f x).val, Set.mem_univ _⟩ : PresentedSet.univ (pointSpace u w) B.real) :=
      Subtype.ext (hy.trans hz.symm)
    refine ⟨x, hx, ?_⟩
    exact (postcomposeRealMap_apply f g hBS x).trans
      ((congrArg (fun y => (g y).val) he).symm.trans hq)
  · rintro ⟨x, hx, hq⟩
    exact ⟨(f x).val, ⟨x, hx, rfl⟩, ⟨⟨(f x).val, Set.mem_univ _⟩, rfl,
      (postcomposeRealMap_apply f g hBS x).symm.trans hq⟩⟩

theorem gamma_map_preparation_at_boundary {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (h00 : M ⊨ Axioms.ACVF00) (v : Valuation (VF (M := M)) Γ)
    (hv : ∀ x y : VF (M := M), VFValued.predV x y ↔ v x ≤ v y)
    (hObstacles : ∀ N, UniformVerticalObstacles v B.real N)
    (hΓ : GammaLogicInput B) (hSupport : GammaPolynomialSupportInput B)
    (hBS : B.real ⊆ S) {u w : ℕ} (A : DefSet (M := M) S n m)
    (hA : GammaSetDefinable B (carrier A)) {D : DefSet (M := M) S u w}
    (f : Map A D) (hf : GammaGraphDefinable B (pointMapGraph f)) (previous : Option Bool)
    (hTags : previous = some false → AllTagged A) :
    ∃ r : ℕ, ∃ E : DefSet (M := M) S n r, ∃ U : SpecialBijection A E,
      U.chain.Alternating previous ∧ GammaChainDefinable B U.chain ∧
        IsRVPullback (carrier E) ∧ Contractible (Map.comp f U.inverseMap) := by
  let g := Map.comp (flattenKeyMap (PresentedSet.univ (keySpace u w) B.real))
    (keyMap (PresentedSet.univ (pointSpace u w) B.real))
  let F := postcomposeRealMap f g hBS
  have hF := gamma_postcompose_real hΓ f hf g hBS
  obtain ⟨r, E, U, hUa, hUG, hE, hc⟩ := gamma_rvMap_preparation_at_boundary
    h00 v hv hObstacles hΓ hSupport hBS A hA F hF previous hTags
  refine ⟨r, E, U, hUa, hUG, hE, ?_⟩
  intro b c he
  change SameRV (f (U.inverseMap b)).val (f (U.inverseMap c)).val
  have hh := ((sameRV_iff _ _).mp (hc b c he)).2
  change Fin.append (key (f (U.inverseMap b)).val).1 (key (f (U.inverseMap b)).val).2 =
    Fin.append (key (f (U.inverseMap c)).val).1 (key (f (U.inverseMap c)).val).2 at hh
  apply Prod.ext
  · funext i
    simpa only [Fin.append_left] using congrFun hh (Fin.castAdd w i)
  · funext i
    simpa only [Fin.append_right] using congrFun hh (Fin.natAdd u i)

theorem gamma_map_preparation {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (h00 : M ⊨ Axioms.ACVF00) (v : Valuation (VF (M := M)) Γ)
    (hv : ∀ x y : VF (M := M), VFValued.predV x y ↔ v x ≤ v y)
    (hObstacles : ∀ N, UniformVerticalObstacles v B.real N)
    (hΓ : GammaLogicInput B) (hSupport : GammaPolynomialSupportInput B)
    (hBS : B.real ⊆ S) {a u w : ℕ} {A₀ : DefSet (M := M) S n a}
    {A : DefSet (M := M) S n m} {D : DefSet (M := M) S u w}
    (τ : SpecialBijection A₀ A) (hτ : GammaChainDefinable B τ.chain)
    (f : Map A D) (hf : GammaGraphDefinable B (pointMapGraph f)) :
    ∃ r : ℕ, ∃ E : DefSet (M := M) S n r, ∃ U : SpecialBijection A E,
      (τ.chain.append U.chain).Alternating none ∧ GammaChainDefinable B U.chain ∧
        IsRVPullback (carrier E) ∧ Contractible (Map.comp f U.inverseMap) := by
  obtain ⟨r, E, U, hUa, hUG, hE, hc⟩ := gamma_map_preparation_at_boundary h00 v hv hObstacles
    hΓ hSupport hBS A (GammaChainDefinable.target B τ.chain hτ) f hf (τ.chain.lastKind none)
    (fun h => τ.chain.lastKind_allTagged none (by intro he; cases he) h)
  exact ⟨r, E, U, τ.chain.append_alternating U.chain none τ.alternating hUa, hUG, hE, hc⟩

/-- The earlier specialization bridge uses finitely many proper Gamma codes
internally. Their Gamma values are already names in the original base. -/
def GammaPresentationInput (B : Section3.GammaParameters.Base (M := M)) : Prop :=
  ∀ {n m : ℕ} (A : Set (Point (M := M) n m)), GammaSetDefinable B A →
  ∃ d : ℕ, ∃ t : Fin d → Section3.GammaParameters.Code (M := M),
    (∀ i, Section3.GammaParameters.value (t i) ∈ B.gamma) ∧
    ∃ D : DefSet (M := M) (B.real ∪ Set.range (Section3.GammaParameters.rawTuple t)) n m,
      carrier D = A

def GammaIsDeformedRVPullback (B : Section3.GammaParameters.Base (M := M))
    (A : Set (Point (M := M) n m)) : Prop :=
  ∃ r : ℕ, ∃ C : Set (Point (M := M) n r), Nonempty (GammaSpecialBijection B A C) ∧ IsRVPullback C

theorem corollary_5_6_gamma {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (h00 : M ⊨ Axioms.ACVF00) (v : Valuation (VF (M := M)) Γ)
    (hv : ∀ x y : VF (M := M), VFValued.predV x y ↔ v x ≤ v y)
    (hObstacles : ∀ N, UniformVerticalObstacles v B.real N)
    (hΓ : GammaLogicInput B) (hSupport : GammaPolynomialSupportInput B)
    (hPresent : GammaPresentationInput B) (A : Set (Point (M := M) n m))
    (hA : GammaSetDefinable B A) : GammaIsDeformedRVPullback B A := by
  obtain ⟨d, t, _, D, hDA⟩ := hPresent A hA
  let R := B.real ∪ Set.range (Section3.GammaParameters.rawTuple t)
  have hBR : B.real ⊆ R := Set.subset_union_left
  have hD : GammaSetDefinable B (carrier D) := hDA.symm ▸ hA
  let f := constantRVMap D 0
  have hf : GammaGraphDefinable B (pointMapGraph f) := by
    have hh := hΓ.restrict_graph hD (hΓ.real_map_graph
      (constantRVMap (PresentedSet.univ (pointSpace n m) B.real) 0))
    apply GammaGraphDefinable.congr hh
    intro p q
    constructor
    · rintro ⟨hp, _⟩
      exact ⟨⟨p, hp⟩, rfl, Subsingleton.elim _ _⟩
    · rintro ⟨a, rfl, _⟩
      exact ⟨a.property, ⟨a.val, Set.mem_univ _⟩, rfl, Subsingleton.elim _ _⟩
  obtain ⟨r, E, U, _, hUG, hE, _⟩ := gamma_rvMap_preparation_at_boundary h00 v hv hObstacles
    hΓ hSupport hBR D hD f hf none (by intro h; cases h)
  exact ⟨r, carrier E, ⟨⟨R, hBR, D, E, hDA, rfl, U, hUG⟩⟩, hE⟩

theorem theorem_5_5_finite_gamma {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (h00 : M ⊨ Axioms.ACVF00) (v : Valuation (VF (M := M)) Γ)
    (hv : ∀ x y : VF (M := M), VFValued.predV x y ↔ v x ≤ v y)
    (hObstacles : ∀ N, UniformVerticalObstacles v B.real N)
    (hΓ : GammaLogicInput B) (hSupport : GammaPolynomialSupportInput B)
    (hBS : B.real ⊆ S) {A₀ : DefSet (M := M) S n 0} {A : DefSet (M := M) S n m}
    (τ : SpecialBijection A₀ A) (hτ : GammaChainDefinable B τ.chain)
    (p : Fin k → MvPolynomial (Fin n) (VF (M := M)))
    (hc : ∀ i e, ((p i).coeff e).val ∈ B.real) :
    ∃ r : ℕ, ∃ E : DefSet (M := M) S n r, ∃ U : SpecialBijection A E,
      (τ.chain.append U.chain).Alternating none ∧ GammaChainDefinable B U.chain ∧
        IsRVPullback (carrier E) ∧
        ∀ b c : E, SameRV b.val c.val → ∀ i,
          rv (MvPolynomial.eval (vfAt (τ.inverseMap (U.inverseMap b)).val) (p i)) =
          rv (MvPolynomial.eval (vfAt (τ.inverseMap (U.inverseMap c)).val) (p i)) := by
  let g := mvPolynomialTupleMap (PresentedSet.univ (pointSpace n 0) B.real) p hc
  let f := postcomposeRealMap τ.inverseMap g hBS
  have hf := gamma_postcompose_real hΓ τ.inverseMap (gamma_inverse_graph hΓ τ hτ) g hBS
  obtain ⟨r, E, U, hUa, hUG, hE, hcontract⟩ :=
    gamma_map_preparation h00 v hv hObstacles hΓ hSupport hBS τ hτ f hf
  refine ⟨r, E, U, hUa, hUG, hE, ?_⟩
  intro b c he i
  exact ((sameRV_iff _ _).mp (hcontract b c he)).1 i

theorem theorem_5_5_gamma {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (h00 : M ⊨ Axioms.ACVF00) (v : Valuation (VF (M := M)) Γ)
    (hv : ∀ x y : VF (M := M), VFValued.predV x y ↔ v x ≤ v y)
    (hObstacles : ∀ N, UniformVerticalObstacles v B.real N)
    (hΓ : GammaLogicInput B) (hSupport : GammaPolynomialSupportInput B)
    (hBS : B.real ⊆ S) {A₀ : DefSet (M := M) S n 0} {A : DefSet (M := M) S n m}
    (τ : SpecialBijection A₀ A) (hτ : GammaChainDefinable B τ.chain)
    (p : MvPolynomial (Fin n) (VF (M := M))) (hc : ∀ e, (p.coeff e).val ∈ B.real) :
    ∃ r : ℕ, ∃ E : DefSet (M := M) S n r, ∃ U : SpecialBijection A E,
      (τ.chain.append U.chain).Alternating none ∧ GammaChainDefinable B U.chain ∧
        IsRVPullback (carrier E) ∧
        ∀ b c : E, SameRV b.val c.val →
          rv (MvPolynomial.eval (vfAt (τ.inverseMap (U.inverseMap b)).val) p) =
          rv (MvPolynomial.eval (vfAt (τ.inverseMap (U.inverseMap c)).val) p) := by
  obtain ⟨r, E, U, hUa, hUG, hE, hcontract⟩ := theorem_5_5_finite_gamma h00 v hv hObstacles
    hΓ hSupport hBS τ hτ (fun _ : Fin 1 => p) (fun _ => hc)
  exact ⟨r, E, U, hUa, hUG, hE, fun b c he => hcontract b c he 0⟩

theorem theorem_5_4_gamma {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (h00 : M ⊨ Axioms.ACVF00) (v : Valuation (VF (M := M)) Γ)
    (hv : ∀ x y : VF (M := M), VFValued.predV x y ↔ v x ≤ v y)
    (hObstacles : ∀ N, UniformVerticalObstacles v B.real N)
    (hΓ : GammaLogicInput B) (hSupport : GammaPolynomialSupportInput B)
    (hBS : B.real ⊆ S) {A₀ : DefSet (M := M) S n 0} {A : DefSet (M := M) S n m}
    (u : Fin n → RV (M := M)) (_hFibre : carrier A₀ = {p | ∀ i, rv (vfAt p i) = u i})
    (τ : SpecialBijection A₀ A) (hτ : GammaChainDefinable B τ.chain)
    (p : MvPolynomial (Fin n) (VF (M := M))) (hc : ∀ e, (p.coeff e).val ∈ B.real) :
    ∃ r : ℕ, ∃ E : DefSet (M := M) S n r, ∃ U : SpecialBijection A E,
      (τ.chain.append U.chain).Alternating none ∧ GammaChainDefinable B U.chain ∧
        ∀ b c : E, SameRV b.val c.val →
          rv (MvPolynomial.eval (vfAt (τ.inverseMap (U.inverseMap b)).val) p) =
          rv (MvPolynomial.eval (vfAt (τ.inverseMap (U.inverseMap c)).val) p) := by
  obtain ⟨r, E, U, hUa, hUG, _, hc⟩ := theorem_5_5_gamma h00 v hv hObstacles hΓ hSupport hBS τ hτ p hc
  exact ⟨r, E, U, hUa, hUG, hc⟩

end SpecialTransformations.Section5
