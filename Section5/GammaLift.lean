module

public import Section5.GammaExistence
public import Section5.CategoryLift

@[expose] public section

/-!
# Lifting over the original Gamma base

The objects below retain Section 4's actual RV object and lift. The extra
certificates state that its domain, volume and isomorphism have full
invariant graphs over the original base. Internal real presentations do
not add names to that base.
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
variable {B : Section3.GammaParameters.Base (M := M)} {S : Set M}
variable {n m u w a b k : ℕ}

/-- An isomorphism is an actual bijection with its complete original-base
graph, rather than a new predicate declared to mean isomorphism. -/
structure GammaIso (B : Section3.GammaParameters.Base (M := M))
    (A : Set (Point (M := M) n m)) (C : Set (Point (M := M) u w)) where
  equiv : A ≃ C
  graph : GammaGraphDefinable B (fun p q => ∃ x : A, x.val = p ∧ (equiv x).val = q)

def GammaIso.congr {A A' : Set (Point (M := M) n m)}
    {C C' : Set (Point (M := M) u w)} (e : GammaIso B A C)
    (hA : A = A') (hC : C = C') : GammaIso B A' C' := by
  cases hA
  cases hC
  exact e

def GammaIso.trans (hΓ : GammaLogicInput B)
    {A : Set (Point (M := M) n m)} {C : Set (Point (M := M) u w)}
    {D : Set (Point (M := M) a b)} (e : GammaIso B A C) (f : GammaIso B C D) :
    GammaIso B A D where
  equiv := e.equiv.trans f.equiv
  graph := by
    apply GammaGraphDefinable.congr (hΓ.comp_graph e.graph f.graph)
    intro p q
    constructor
    · rintro ⟨z, ⟨x, hx, hz⟩, ⟨y, hy, hq⟩⟩
      have he : y = e.equiv x := Subtype.ext (hy.trans hz.symm)
      exact ⟨x, hx, (congrArg (fun y => (f.equiv y).val) he).symm.trans hq⟩
    · rintro ⟨x, hx, hq⟩
      exact ⟨(e.equiv x).val, ⟨x, hx, rfl⟩, ⟨e.equiv x, rfl, hq⟩⟩

def GammaIso.symm (hΓ : GammaLogicInput B)
    {A : Set (Point (M := M) n m)} {C : Set (Point (M := M) u w)} (e : GammaIso B A C) :
    GammaIso B C A where
  equiv := e.equiv.symm
  graph := by
    apply GammaGraphDefinable.congr (hΓ.swap_graph e.graph)
    intro q p
    constructor
    · rintro ⟨x, hx, hq⟩
      refine ⟨e.equiv x, hq, ?_⟩
      simpa only [Equiv.symm_apply_apply] using hx
    · rintro ⟨y, hy, hp⟩
      exact ⟨e.equiv.symm y, hp,
        (congrArg Subtype.val (e.equiv.apply_symm_apply y)).trans hy⟩

def GammaSpecialBijection.iso (hΓ : GammaLogicInput B)
    {A : Set (Point (M := M) n m)} {C : Set (Point (M := M) n w)}
    (T : GammaSpecialBijection B A C) : GammaIso B A C :=
  (show GammaIso B (carrier T.source) (carrier T.target) from
    ⟨T.special.equiv, GammaChainDefinable.graph hΓ T.special.chain T.invariant_graphs⟩).congr
      T.source_eq T.target_eq

def rvCoordinatePointMap (ρ : Fin k → Fin m) (S : Set M) :
    Map (PresentedSet.univ (pointSpace (M := M) 0 m) S)
      (PresentedSet.univ (pointSpace 0 k) S) :=
  Map.ofCodes _ (fun p => (Fin.elim0, p.2 ∘ ρ))
    (fun z => Sum.elim Fin.elim0 (fun i => z (.inr (ρ i))))
    (by intro i; cases i with
        | inl i => exact i.elim0
        | inr i => exact rawProj S (.inr (ρ i) : Fin 0 ⊕ Fin m))
    (by intro c; exact ⟨fun i => i.elim0, fun i => c.property.2 (ρ i)⟩)
    (by intro c; exact Prod.ext (Subsingleton.elim _ _) rfl)

structure GammaRVObject (B : Section3.GammaParameters.Base (M := M)) (k : ℕ) where
  codes : Set M
  real_contains : B.real ⊆ codes
  object : @Section4.RVObject M (CanonicalStructure.normalize (M := M)) codes k
  domain_graph : GammaSetDefinable B
    {p : Point (M := M) 0 (rvObjectArity object) | p.2 ∈ carrier (rvObjectDomain object)}
  volume_graph : GammaGraphDefinable B
    (fun (p : Point (M := M) 0 (rvObjectArity object)) (q : Point (M := M) 0 k) =>
      ∃ x : rvObjectDomain object, x.val = p.2 ∧ (rvObjectVolume object x).val = q.2)

def GammaRVObject.lift (U : GammaRVObject B k) :
    Set (Point (M := M) k (rvObjectArity U.object)) := carrier (rawLift U.object)

structure GammaRVFiniteObject (B : Section3.GammaParameters.Base (M := M)) (k : ℕ)
    extends GammaRVObject B k where
  finite_volume : Map.FiniteFibres (rvObjectVolume object)

theorem gamma_pullback_domain (hΓ : GammaLogicInput B) (A : DefSet (M := M) S n m)
    (hA : GammaSetDefinable B (carrier A)) : GammaSetDefinable B
    {p : Point (M := M) 0 (n + m) | p.2 ∈ carrier (rvObjectDomain (pullbackObject A))} := by
  let g := Map.comp (flattenKeyMap (PresentedSet.univ (keySpace n m) B.real))
    (keyMap (PresentedSet.univ (pointSpace n m) B.real))
  have hh := hΓ.image_real g hA
  convert hh using 1
  ext q
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨⟨x.val, Set.mem_univ _⟩, x.property,
      Prod.ext (Subsingleton.elim _ _) hx⟩
  · rintro ⟨x, hx, he⟩
    exact ⟨⟨x.val, hx⟩, congrArg Prod.snd he⟩

def gammaPullbackObject (hΓ : GammaLogicInput B) (hBS : B.real ⊆ S)
    (A : DefSet (M := M) S n m) (hA : GammaSetDefinable B (carrier A)) : GammaRVObject B n where
  codes := S
  real_contains := hBS
  object := pullbackObject A
  domain_graph := gamma_pullback_domain hΓ A hA
  volume_graph := by
    let g := rvCoordinatePointMap (fun i : Fin n => Fin.castAdd m i) B.real
    have hd := (gamma_pullback_domain hΓ A hA)
    apply GammaGraphDefinable.congr (hΓ.restrict_graph hd (hΓ.real_map_graph g))
    intro p q
    constructor
    · rintro ⟨hp, x, hx, hq⟩
      refine ⟨⟨p.2, hp⟩, rfl, ?_⟩
      exact (congrArg (fun z : Point (M := M) 0 (n + m) => z.2 ∘ (fun i => Fin.castAdd m i)) hx).symm.trans
        (congrArg Prod.snd hq)
    · rintro ⟨x, hx, hq⟩
      refine ⟨(show p.2 ∈ carrier (rvObjectDomain (pullbackObject A)) from hx ▸ x.property),
        ⟨p, Set.mem_univ _⟩, rfl, ?_⟩
      exact Prod.ext (Subsingleton.elim _ _) ((congrArg (fun t => t ∘ (fun i => Fin.castAdd m i)) hx).symm.trans hq)

theorem GammaIso.target_definable (hΓ : GammaLogicInput B)
    {A : Set (Point (M := M) n m)} {C : Set (Point (M := M) u w)} (e : GammaIso B A C) :
    GammaSetDefinable B C := by
  have hh := hΓ.image_graph e.graph
  convert hh using 1
  ext q
  constructor
  · intro hq
    let y : C := ⟨q, hq⟩
    exact ⟨(e.equiv.symm y).val, e.equiv.symm y, rfl,
      congrArg Subtype.val (e.equiv.apply_symm_apply y)⟩
  · rintro ⟨p, x, hx, hq⟩
    exact hq ▸ (e.equiv x).property

def gamma_pullback_iso (hΓ : GammaLogicInput B) (hBS : B.real ⊆ S)
    (A : DefSet (M := M) S n m) (hA : GammaSetDefinable B (carrier A))
    (hP : IsRVPullback (carrier A)) :
    GammaIso B (carrier A) (gammaPullbackObject hΓ hBS A hA).lift where
  equiv := Equiv.ofBijective (pullbackLiftMap A) (pullbackLiftMap_bijective A hP)
  graph := GammaPrimitiveDefinable.graph hΓ (.canonical A) hA

theorem gamma_deformed_pullback_is_lift {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (h00 : M ⊨ Axioms.ACVF00) (v : Valuation (VF (M := M)) Γ)
    (hv : ∀ x y : VF (M := M), VFValued.predV x y ↔ v x ≤ v y)
    (hObstacles : ∀ N, UniformVerticalObstacles v B.real N)
    (hΓ : GammaLogicInput B) (hSupport : GammaPolynomialSupportInput B)
    (hPresent : GammaPresentationInput B) (A : Set (Point (M := M) n m))
    (hA : GammaSetDefinable B A) :
    ∃ U : GammaRVObject B n, Nonempty (GammaIso B A U.lift) := by
  obtain ⟨r, C, ⟨T⟩, hC⟩ := corollary_5_6_gamma h00 v hv hObstacles hΓ hSupport hPresent A hA
  have hT := GammaChainDefinable.target B T.special.chain T.invariant_graphs
  let U := gammaPullbackObject hΓ T.real_contains T.target hT
  have hP : IsRVPullback (carrier T.target) := T.target_eq.symm ▸ hC
  let e := (T.iso hΓ).congr rfl T.target_eq.symm
  exact ⟨U, ⟨e.trans hΓ (gamma_pullback_iso hΓ T.real_contains T.target hT hP)⟩⟩

/-- The Gamma-base form of 5.7. The given dimensional reduction is a
Gamma-definable bijection, not an assumed lift representation. The result
is an actual original-base isomorphism to Section 4's actual lift. -/
theorem corollary_5_7_gamma {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (h00 : M ⊨ Axioms.ACVF00) (v : Valuation (VF (M := M)) Γ)
    (hv : ∀ x y : VF (M := M), VFValued.predV x y ↔ v x ≤ v y)
    (hObstacles : ∀ N, UniformVerticalObstacles v B.real N)
    (hΓ : GammaLogicInput B) (hSupport : GammaPolynomialSupportInput B)
    (hPresent : GammaPresentationInput B) (A : Set (Point (M := M) n m))
    (hreduce : ∃ l : ℕ, ∃ D : Set (Point (M := M) k l), Nonempty (GammaIso B A D)) :
    ∃ U : GammaRVObject B k, Nonempty (GammaIso B A U.lift) := by
  obtain ⟨l, D, ⟨e⟩⟩ := hreduce
  obtain ⟨U, ⟨f⟩⟩ := gamma_deformed_pullback_is_lift h00 v hv hObstacles
    hΓ hSupport hPresent D (e.target_definable hΓ)
  exact ⟨U, ⟨e.trans hΓ f⟩⟩

/-- Finite-volume variant. The only extra earlier input is invariance of
finite RV fibres under an original-base definable bijection (Section 4.13). -/
theorem corollary_5_7_finite_gamma {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (h00 : M ⊨ Axioms.ACVF00) (v : Valuation (VF (M := M)) Γ)
    (hv : ∀ x y : VF (M := M), VFValued.predV x y ↔ v x ≤ v y)
    (hObstacles : ∀ N, UniformVerticalObstacles v B.real N)
    (hΓ : GammaLogicInput B) (hSupport : GammaPolynomialSupportInput B)
    (hPresent : GammaPresentationInput B) (A : Set (Point (M := M) n m))
    (hreduce : ∃ l : ℕ, ∃ D : Set (Point (M := M) k l), Nonempty (GammaIso B A D))
    (hfinite : ∀ {l : ℕ} (D : Set (Point (M := M) k l)), GammaIso B A D →
      ∀ x : Fin k → VF (M := M), {t : Fin l → RV (M := M) | (x, t) ∈ D}.Finite) :
    ∃ U : GammaRVFiniteObject B k, Nonempty (GammaIso B A U.toGammaRVObject.lift) := by
  obtain ⟨l, D, ⟨e⟩⟩ := hreduce
  obtain ⟨r, C, ⟨T⟩, hC⟩ := corollary_5_6_gamma h00 v hv hObstacles
    hΓ hSupport hPresent D (e.target_definable hΓ)
  have hT := GammaChainDefinable.target B T.special.chain T.invariant_graphs
  let U := gammaPullbackObject hΓ T.real_contains T.target hT
  have hP : IsRVPullback (carrier T.target) := T.target_eq.symm ▸ hC
  let f := (e.trans hΓ (T.iso hΓ)).congr rfl T.target_eq.symm
  have hfin := pullbackObject_finiteVolume T.target hP (hfinite (carrier T.target) f)
  exact ⟨⟨U, hfin⟩, ⟨f.trans hΓ (gamma_pullback_iso hΓ T.real_contains T.target hT hP)⟩⟩

end SpecialTransformations.Section5
