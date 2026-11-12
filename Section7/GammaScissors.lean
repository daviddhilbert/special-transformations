module

public import Section7.GammaLiftEquivalence
public import Section5.GammaDimensionCriterion
public import Section4.RVRestrictions
public import Section4.PositiveAdditivePresentation
public import Section5.GammaSurjectivity

@[expose] public section

/-! The positive additive presentations over a named Gamma base and
the surjectivity of the canonical lift on both quotients. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5

noncomputable section

namespace SpecialTransformations.Section7

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {k : ℕ}

structure GammaVFObject (B : Base (M := M)) (k : ℕ) where
  arity : ℕ × ℕ
  domain : Set (Point (M := M) arity.1 arity.2)
  definable : GammaSetDefinable B domain
  dimension : GammaHasVFDimLE B domain k

def GammaVFObject.finiteFibres (A : GammaVFObject B k) : Prop :=
  ∀ x : Fin A.arity.1 → VF (M := M),
    {t : Fin A.arity.2 → RV (M := M) | (x,t) ∈ A.domain}.Finite

def GammaRVFiniteVolumes (U : GammaRVObject B k) : Prop :=
  Map.FiniteFibres (rvObjectVolume U.object)

def gammaLiftVF (U : GammaRVObject B k) : GammaVFObject B k :=
  ⟨(k, rvObjectArity U.object), U.lift, U.lift_definable,
    (Classical.choice (GammaIso.refl U.lift_definable)).dimension_le⟩

theorem gammaLiftVF_finite (U : GammaRVObject B k) (h : GammaRVFiniteVolumes U) :
    (gammaLiftVF U).finiteFibres := by
  intro x
  let N := @CanonicalStructure.normalize M sM
  have hn : @Theory.Model LRV M N Axioms.ACVF := @CanonicalStructure.normalized_model M sM hM
  exact @rvLift_finite_rv_fibres M N hn (@GammaRVObject.codes M sM hM B k U) k
    (@GammaRVObject.object M sM hM B k U) h x

private abbrev PackedVFPoint (M : Type) [LRV.Structure M] :=
  Σ a : ℕ × ℕ, Point (M := M) a.1 a.2

private abbrev PackedRVPoint (M : Type) [LRV.Structure M] (k : ℕ) :=
  Σ m : ℕ, (Fin m → RV (M := M)) × (Fin k → RV (M := M))

private def vfPacked (A : GammaVFObject B k) : Set (PackedVFPoint M) :=
  Set.range (fun x : A.domain => ⟨A.arity, x.val⟩)

private def rvPacked (U : GammaRVObject B k) : Set (Option (PackedRVPoint M k)) :=
  Set.range (fun u : rvObjectDomain U.object => some ⟨rvObjectArity U.object, u.val, gammaVolumeValue U u⟩)

private def packVolume (k : ℕ) : PackedVFPoint M → Option (PackedRVPoint M k)
  | ⟨(n, m), (x, t)⟩ =>
    if h : n = k then some ⟨m, t, fun i => rv (x (Fin.cast h.symm i))⟩ else none

private theorem packed_lift_eq (U : GammaRVObject B k) :
    vfPacked (gammaLiftVF U) = packVolume k ⁻¹' rvPacked U := by
  ext z
  constructor
  · rintro ⟨p, rfl⟩
    obtain ⟨u, hu, hv⟩ := volume_of_lift U p
    refine ⟨u, ?_⟩
    simp only [packVolume, gammaLiftVF, dite_true, Fin.cast_refl, id_eq, hu, hv]
  · rintro ⟨u, hu⟩
    obtain ⟨⟨n, m⟩, x, t⟩ := z
    by_cases h : n = k
    · subst n
      simp only [packVolume, dite_true, Fin.cast_refl, Option.some.injEq] at hu
      have hm : rvObjectArity U.object = m := congrArg Sigma.fst hu
      subst m
      have hp : (u.val, gammaVolumeValue U u) = (t, fun i => rv (x i)) :=
        eq_of_heq (Sigma.mk.inj_iff.mp hu).2
      let p : U.lift := ⟨(x,t), mem_lift_of_volume U (x,t) u
        (congrArg Prod.fst hp) (congrArg Prod.snd hp)⟩
      exact ⟨p, rfl⟩
    · simp [packVolume, h] at hu

/-- Scissors relate four actual subsets in a common mixed arity. -/
def GammaVFScissor (A C D E : GammaVFObject B k) : Prop :=
  A.arity = C.arity ∧ A.arity = D.arity ∧ A.arity = E.arity ∧
    vfPacked D = vfPacked A ∪ vfPacked C ∧ vfPacked E = vfPacked A ∩ vfPacked C

/-- Companion graphs retain the restriction of the same volume on
the union and intersection. -/
def GammaRVScissor (U V W X : GammaRVObject B k) : Prop :=
  rvObjectArity U.object = rvObjectArity V.object ∧
    rvObjectArity U.object = rvObjectArity W.object ∧
    rvObjectArity U.object = rvObjectArity X.object ∧
    rvPacked W = rvPacked U ∪ rvPacked V ∧ rvPacked X = rvPacked U ∩ rvPacked V

theorem GammaRVScissor.lift {U V W X : GammaRVObject B k} (h : GammaRVScissor U V W X) :
    GammaVFScissor (gammaLiftVF U) (gammaLiftVF V) (gammaLiftVF W) (gammaLiftVF X) := by
  obtain ⟨hv, hw, hx, hW, hX⟩ := h
  exact ⟨Prod.ext rfl hv, Prod.ext rfl hw, Prod.ext rfl hx,
    by simp only [packed_lift_eq, hW, Set.preimage_union],
    by simp only [packed_lift_eq, hX, Set.preimage_inter]⟩

private def gammaRVEmpty (B : Base (M := M)) (k : ℕ) : GammaRVObject B k := by
  let N := @CanonicalStructure.normalize M sM
  let S := @Base.real M sM hM B
  let U := @RVObject.empty M N S k
  refine @GammaRVObject.mk M sM hM B k S Set.Subset.rfl U ?_ ?_
  · unfold GammaSetDefinable
    convert @DefinableOverBase.empty M sM hM B _ (gammaPointSort 0 0) using 1
    all_goals first | rfl | (
      ext z
      simp only [Set.mem_empty_iff_false, iff_false]
      rintro ⟨p, hp, _⟩
      exact hp)
  · unfold GammaGraphDefinable
    convert @DefinableOverBase.empty M sM hM B _
      (Fin.append (gammaPointSort 0 0) (gammaPointSort 0 k)) using 1
    all_goals first | rfl | (
      ext z
      simp only [Set.mem_empty_iff_false, iff_false]
      rintro ⟨p, q, ⟨u, _, _⟩, _⟩
      exact u.property)

private theorem gammaRVEmpty_finite (B : Base (M := M)) (k : ℕ) :
    GammaRVFiniteVolumes (gammaRVEmpty B k) := by
  intro v
  exact Set.finite_empty.subset (fun u _ => False.elim u.property)

open PositiveAdditiveGrothendieck

def gammaRVPresentation (B : Base (M := M)) (k : ℕ) :
    Presentation (GammaRVObject B k) where
  iso U V := Nonempty (GammaRVIso U V)
  empty := gammaRVEmpty B k
  scissor := GammaRVScissor

def gammaVFPresentation (B : Base (M := M)) (k : ℕ) :
    Presentation (GammaVFObject B k) where
  iso A C := Nonempty (GammaIso B A.domain C.domain)
  empty := gammaLiftVF (gammaRVEmpty B k)
  scissor := GammaVFScissor

private def restrictPresentation {X : Type} (P : Presentation X)
    (p : X → Prop) (h : p P.empty) : Presentation {x : X // p x} where
  iso x y := P.iso x.val y.val
  empty := ⟨P.empty, h⟩
  scissor x y z w := P.scissor x.val y.val z.val w.val

def gammaRVFinitePresentation (B : Base (M := M)) (k : ℕ) :=
  restrictPresentation (gammaRVPresentation B k) GammaRVFiniteVolumes (gammaRVEmpty_finite B k)

def gammaVFFinitePresentation (B : Base (M := M)) (k : ℕ) :=
  restrictPresentation (gammaVFPresentation B k) GammaVFObject.finiteFibres
    (gammaLiftVF_finite (gammaRVEmpty B k) (gammaRVEmpty_finite B k))

variable (hcan : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal}
variable (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
variable (hsmall : Cardinal.mk B.real < κ) (hB : VFGammaGeneratedBase B)

def gammaPositiveLift :
    KPlus (gammaRVPresentation B k) →+ KPlus (gammaVFPresentation B k) :=
  lift (gammaRVPresentation B k) {
    toFun := fun U => of (gammaVFPresentation B k) (gammaLiftVF U)
    iso := fun ⟨e⟩ => of_iso (gammaVFPresentation B k) (e.liftIso hcan hκ hs h00 hsmall hB)
    empty := of_empty (gammaVFPresentation B k)
    scissor := fun h => of_scissor (gammaVFPresentation B k) (GammaRVScissor.lift h)
  }

def gammaPositiveFiniteLift :
    KPlus (gammaRVFinitePresentation B k) →+ KPlus (gammaVFFinitePresentation B k) :=
  lift (gammaRVFinitePresentation B k) {
    toFun := fun U => of (gammaVFFinitePresentation B k) ⟨gammaLiftVF U.val, gammaLiftVF_finite U.val U.property⟩
    iso := fun ⟨e⟩ => of_iso (gammaVFFinitePresentation B k) (e.liftIso hcan hκ hs h00 hsmall hB)
    empty := of_empty (gammaVFFinitePresentation B k)
    scissor := fun h => of_scissor (gammaVFFinitePresentation B k) (GammaRVScissor.lift h)
  }

private theorem surjective_of_generators {X Y : Type} {P : Presentation X} {Q : Presentation Y}
    (F : KPlus P →+ KPlus Q) (h : ∀ y, ∃ x, F x = of Q y) : Function.Surjective F := by
  intro q
  obtain ⟨z, rfl⟩ := (congruence Q).mk'_surjective q
  change ∃ x, F x = quotientHom Q z
  induction z using Finsupp.induction_linear with
  | zero => exact ⟨0, (map_zero F).trans (map_zero (quotientHom Q)).symm⟩
  | add a b ha hb =>
    obtain ⟨x, hx⟩ := ha
    obtain ⟨y, hy⟩ := hb
    exact ⟨x + y, by rw [map_add, map_add, hx, hy]⟩
  | single y n =>
    obtain ⟨x, hx⟩ := h y
    have he : Finsupp.single y n = n • generator y := by
      ext a
      by_cases h : a = y <;> simp [h, generator]
    exact ⟨n • x, by rw [map_nsmul, hx, he, map_nsmul]; rfl⟩

private def generatedFieldBase (B : Base (M := M)) (hB : VFGammaGeneratedBase B) :
    VFFieldBase B.real := by
  refine ⟨vfDefinableClosureFieldBase B, fun x => ?_⟩
  have hr := congrArg Base.real hB.closure_eq_self
  change DefinableClosureAtBase B .vf x.val ↔ x.val ∈ B.real
  rw [← hr]
  constructor
  · exact fun h => ⟨.vf, h⟩
  · rintro ⟨σ, hσ⟩
    cases σ with
    | vf => exact hσ
    | rv =>
      change DefinableAtBase B .rv {x.val} at hσ
      exact (TypedModelMap.not_rv_of_vf x.property
        (hσ.proper _ (Set.mem_singleton _))).elim

theorem gammaPositiveLift_surjective :
    Function.Surjective (gammaPositiveLift (k := k) hcan hκ hs h00 hsmall hB) := by
  apply surjective_of_generators
  intro A
  obtain ⟨U, he⟩ := Section5.Paper.corollary_5_7_gamma hκ hs h00 B hsmall
    (generatedFieldBase B hB) A.domain A.definable A.dimension
  exact ⟨of (gammaRVPresentation B k) U,
    (lift_of _ _ U).trans
      (of_iso (gammaVFPresentation B k) (a := A) (b := gammaLiftVF U) he).symm⟩

theorem gammaPositiveFiniteLift_surjective :
    Function.Surjective (gammaPositiveFiniteLift (k := k) hcan hκ hs h00 hsmall hB) := by
  apply surjective_of_generators
  intro A
  obtain ⟨U, he⟩ := Section5.Paper.corollary_5_7_finite_gamma hκ hs h00 B hsmall
    (generatedFieldBase B hB) A.val.domain A.val.definable A.val.dimension A.property
  let V := U.toGammaRVObject
  let W : {x : GammaRVObject B k // GammaRVFiniteVolumes x} := ⟨V, U.finite_volume⟩
  let Z : {x : GammaVFObject B k // x.finiteFibres} :=
    ⟨gammaLiftVF V, gammaLiftVF_finite V U.finite_volume⟩
  exact ⟨of (gammaRVFinitePresentation B k) W,
    (lift_of _ _ W).trans
      (of_iso (gammaVFFinitePresentation B k) (a := A) (b := Z) he).symm⟩

end SpecialTransformations.Section7

namespace SpecialTransformations.Section7.Paper

open PositiveAdditiveGrothendieck

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem corollary_7_7_gamma {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : @Base M N hN) (hsmall : Cardinal.mk (@Base.real M N hN B) < κ)
    (hB : @VFGammaGeneratedBase M N hN B) (k : ℕ) :
    letI : LRV.Structure M := N
    letI : M ⊨ Axioms.ACVF := hN
    ∃ F : KPlus (@gammaRVPresentation M N hN B k) →+ KPlus (@gammaVFPresentation M N hN B k),
      Function.Surjective F ∧ ∀ U, F (of (@gammaRVPresentation M N hN B k) U) =
        of (@gammaVFPresentation M N hN B k) (gammaLiftVF U) := by
  let hc := @CanonicalStructure.normalize_isCanonical M sM
  let hsN := hs.normalize
  let h00N := @normalized_model00 M sM hM h00
  exact ⟨@gammaPositiveLift M N hN B k hc κ hκ hsN h00N hsmall hB,
    @gammaPositiveLift_surjective M N hN B k hc κ hκ hsN h00N hsmall hB,
    fun U => lift_of _ _ U⟩

theorem corollary_7_7_finite_gamma {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : @Base M N hN) (hsmall : Cardinal.mk (@Base.real M N hN B) < κ)
    (hB : @VFGammaGeneratedBase M N hN B) (k : ℕ) :
    letI : LRV.Structure M := N
    letI : M ⊨ Axioms.ACVF := hN
    ∃ F : KPlus (@gammaRVFinitePresentation M N hN B k) →+
      KPlus (@gammaVFFinitePresentation M N hN B k),
      Function.Surjective F ∧ ∀ U, F (of (@gammaRVFinitePresentation M N hN B k) U) =
        of (@gammaVFFinitePresentation M N hN B k)
          ⟨gammaLiftVF U.val, gammaLiftVF_finite U.val U.property⟩ := by
  let hc := @CanonicalStructure.normalize_isCanonical M sM
  let hsN := hs.normalize
  let h00N := @normalized_model00 M sM hM h00
  exact ⟨@gammaPositiveFiniteLift M N hN B k hc κ hκ hsN h00N hsmall hB,
    @gammaPositiveFiniteLift_surjective M N hN B k hc κ hκ hsN h00N hsmall hB,
    fun U => lift_of _ _ U⟩

end SpecialTransformations.Section7.Paper
