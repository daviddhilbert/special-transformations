module

public import Section5.GeneralExistence
public import Section4.CanonicalLift

@[expose] public section

/-!
# RV data of a pullback

The RV object retains the full mixed key, including the old RV labels.
Its volume is the projection to the VF RV coordinates. The presentation
uses Section 4's actual RV objects in the normalized released language.
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
variable {S : Set M} {n m l : ℕ}

abbrev rawRVSpace (r : ℕ) : PresentedSpace (M := M) :=
  @Section4.rawRVSpace M (CanonicalStructure.normalize (M := M)) r

abbrev rawVFSpace (r : ℕ) : PresentedSpace (M := M) :=
  @Section4.rawVFSpace M (CanonicalStructure.normalize (M := M)) r

abbrev rawPointSpace (a b : ℕ) : PresentedSpace (M := M) :=
  @Section4.rawMixedSpace M (CanonicalStructure.normalize (M := M)) a b

theorem rawRV_decode_values (c : pDomain (rawRVSpace (M := M) m)) :
    (fun i => (pDecode (rawRVSpace m) c i).val) = c.val := by
  exact @DefinableGeometry.Space.ofEmbedding_decode LRV M (CanonicalStructure.normalize (M := M))
    (Fin m → @CanonicalRV.RVSort M (CanonicalStructure.normalize (M := M))) (Fin m) inferInstance
    (@Section4.rvValues M (CanonicalStructure.normalize (M := M)) m)
    (@Section4.rvValues_injective M (CanonicalStructure.normalize (M := M)) m)
    (@DefinableGeometry.Space.domain_definable LRV M (CanonicalStructure.normalize (M := M)) (rawRVSpace m)) c

theorem rawVF_decode_values (c : pDomain (rawVFSpace (M := M) n)) :
    (fun i => (pDecode (rawVFSpace n) c i).val) = c.val := by
  exact @DefinableGeometry.Space.ofEmbedding_decode LRV M (CanonicalStructure.normalize (M := M))
    (Fin n → @VF M (CanonicalStructure.normalize (M := M))) (Fin n) inferInstance
    (@Section4.vfValues M (CanonicalStructure.normalize (M := M)) n)
    (@Section4.vfValues_injective M (CanonicalStructure.normalize (M := M)) n)
    (@DefinableGeometry.Space.domain_definable LRV M (CanonicalStructure.normalize (M := M)) (rawVFSpace n)) c

theorem rawPointCode_domain (c : pDomain (pointSpace (M := M) n m)) :
    c.val ∈ pDomain (rawPointSpace n m) := by
  exact ⟨⟨(pDecode (pointSpace n m) c).1, rfl⟩,
    ⟨(pDecode (pointSpace n m) c).2, rfl⟩⟩

def rawPointMap (A : DefSet (M := M) S n m) :
    Map A (PresentedSet.univ (rawPointSpace n m) S) :=
  Map.ofCodes A (fun p => p) (fun z => z) (fun i => rawProj S i) rawPointCode_domain
    (by
      intro c
      have hv := rawVF_decode_values
        (⟨c.val ∘ Sum.inl, (rawPointCode_domain c).1⟩ : pDomain (rawVFSpace n))
      have ht := rawRV_decode_values
        (⟨c.val ∘ Sum.inr, (rawPointCode_domain c).2⟩ : pDomain (rawRVSpace m))
      refine Prod.ext ?_ ?_
      · funext i
        apply Subtype.ext
        exact congrFun hv i
      · funext i
        apply Subtype.ext
        exact congrFun ht i)

def rawKeyFlattenMap (D : PresentedSet (keySpace (M := M) n m) S) :
    Map D (PresentedSet.univ (rawRVSpace (n + m)) S) :=
  Map.ofCodes D (fun p => Fin.append p.1 p.2)
    (fun z => Fin.append (z ∘ Sum.inl) (z ∘ Sum.inr))
    (by
      intro i
      cases i using Fin.addCases with
      | left i => simpa only [Fin.append_left, Function.comp_apply] using rawProj S (Sum.inl i : Fin n ⊕ Fin m)
      | right i => simpa only [Fin.append_right, Function.comp_apply] using rawProj S (Sum.inr i : Fin n ⊕ Fin m))
    (by
      intro c
      refine ⟨Fin.append (pDecode (keySpace n m) c).1 (pDecode (keySpace n m) c).2, ?_⟩
      funext i
      cases i using Fin.addCases <;> simp only [Section4.rvValues, Fin.append_left, Fin.append_right, Function.comp_apply, Sum.elim_inl, Sum.elim_inr])
    (by
      intro c
      have hv := rawRV_decode_values (m := n + m)
        (⟨Fin.append (c.val ∘ Sum.inl) (c.val ∘ Sum.inr), by
          refine ⟨Fin.append (pDecode (keySpace n m) c).1 (pDecode (keySpace n m) c).2, ?_⟩
          funext i
          cases i using Fin.addCases <;> simp only [Section4.rvValues, Fin.append_left, Fin.append_right, Function.comp_apply, Sum.elim_inl, Sum.elim_inr]⟩)
      funext i
      apply Subtype.ext
      refine (congrFun hv i).trans ?_
      cases i using Fin.addCases <;> simp only [Fin.append_left, Fin.append_right, Function.comp_apply])

def rawKeyMap (A : DefSet (M := M) S n m) :=
  Map.comp (rawKeyFlattenMap (PresentedSet.univ (keySpace n m) S)) (keyMap A)

theorem rawKeyMap_apply (A : DefSet (M := M) S n m) (a : A) :
    (rawKeyMap A a).val =
      (Fin.append (fun i => rv (vfAt a.val i)) a.val.2 : Fin (n + m) → RV (M := M)) := rfl

def rawRVProjectionMap (ρ : Fin l → Fin m) (D : PresentedSet (rawRVSpace (M := M) m) S) :
    Map D (PresentedSet.univ (rawRVSpace l) S) :=
  Map.ofCodes D (fun p => p ∘ ρ) (fun z => z ∘ ρ)
    (fun i => rawProj S (ρ i))
    (by
      intro c
      refine ⟨pDecode (rawRVSpace m) c ∘ ρ, ?_⟩
      funext i
      exact congrFun (rawRV_decode_values c) (ρ i))
    (by
      intro c
      funext i
      apply Subtype.ext
      have hleft := rawRV_decode_values
        (⟨c.val ∘ ρ, ⟨pDecode (rawRVSpace m) c ∘ ρ,
          funext (fun i => congrFun (rawRV_decode_values c) (ρ i))⟩⟩ : pDomain (rawRVSpace l))
      exact (congrFun hleft i).trans (congrFun (rawRV_decode_values c) (ρ i)).symm)

def pullbackObject (A : DefSet (M := M) S n m) :
    @Section4.RVObject M (CanonicalStructure.normalize (M := M)) S n :=
  @Section4.RVObject.mk M (CanonicalStructure.normalize (M := M)) S n (n + m)
    (Map.image (rawKeyMap A))
    (rawRVProjectionMap (fun i => Fin.castAdd m i) (Map.image (rawKeyMap A)))

abbrev rvObjectArity (U : @Section4.RVObject M (CanonicalStructure.normalize (M := M)) S n) :=
  @Section4.RVObject.arity M (CanonicalStructure.normalize (M := M)) S n U

abbrev rvObjectDomain (U : @Section4.RVObject M (CanonicalStructure.normalize (M := M)) S n) :=
  @Section4.RVObject.domain M (CanonicalStructure.normalize (M := M)) S n U

abbrev rvObjectVolume (U : @Section4.RVObject M (CanonicalStructure.normalize (M := M)) S n) :=
  @Section4.RVObject.volume M (CanonicalStructure.normalize (M := M)) S n U

def rvFiniteObject (U : @Section4.RVFiniteObject M (CanonicalStructure.normalize (M := M)) S n) :
    @Section4.RVObject M (CanonicalStructure.normalize (M := M)) S n := by
  letI := @CanonicalStructure.normalize M sM
  exact U.obj

abbrev rawLift (U : @Section4.RVObject M (CanonicalStructure.normalize (M := M)) S n) :
    PresentedSet (rawPointSpace n (rvObjectArity U)) S :=
  @Section4.rvLift M (CanonicalStructure.normalize (M := M))
    (CanonicalStructure.normalized_model hM) S n U

theorem normalized_tupleRV (x : Fin n → VF (M := M)) :
    @Section4.tupleRV M (CanonicalStructure.normalize (M := M))
      (CanonicalStructure.normalized_model hM) n x = (fun i => rv (x i)) := by
  funext i
  apply Subtype.ext
  exact rvCode_eq (x i).val (x i).property

def canonicalRawMap (A : DefSet (M := M) S n m) :=
  Map.comp (rawPointMap (PresentedSet.univ (pointSpace n (n + m)) S)) (canonicalMap A)

theorem canonicalRawMap_mem_lift (A : DefSet (M := M) S n m) (a : A) :
    (canonicalRawMap A a).val ∈ carrier (rawLift (pullbackObject A)) := by
  refine ⟨Map.toImage (rawKeyMap A) a, rfl, ?_⟩
  funext i
  change Fin.append (fun j => rv (vfAt a.val j)) a.val.2 (Fin.castAdd m i) = _
  rw [Fin.append_left]
  apply Subtype.ext
  change (rv (vfAt a.val i)).val = rvCode (vfAt a.val i).val
  exact (rvCode_eq _ (vfAt a.val i).property).symm

namespace Map
abbrev FiniteFibres := @DefinableGeometry.Map.FiniteFibres LRV M (CanonicalStructure.normalize (M := M))
/-- The generic corestriction constructor from Section4.MapCorestrict,
at the current normalized presentation boundary. -/
def corestrict {P Q : PresentedSpace (M := M)} {A : PresentedSet P S}
    {B D : PresentedSet Q S} (f : Map A B) (h : ∀ a, (f a).val ∈ carrier D) : Map A D :=
  Map.mk (fun a => ⟨(f a).val, h a⟩) (Map.graph_definable f)
end Map

def pullbackLiftMap (A : DefSet (M := M) S n m) : Map A (rawLift (pullbackObject A)) :=
  Map.corestrict (canonicalRawMap A) (canonicalRawMap_mem_lift A)

/-- A genuine RV-pullback is definably bijective, over the original base,
to the lift of its actual mixed RV key data. -/
theorem pullbackLiftMap_bijective (A : DefSet (M := M) S n m)
    (hA : IsRVPullback (carrier A)) : Function.Bijective (pullbackLiftMap A) := by
  constructor
  · intro a b he
    exact Subtype.ext (canonical_injective (congrArg Subtype.val he))
  · intro b
    obtain ⟨u, hu, hv⟩ := b.property
    obtain ⟨a, ha⟩ := u.property
    have ha' := (rawKeyMap_apply A a).symm.trans ha
    have hkey : Fin.append (fun i => rv (vfAt a.val i)) a.val.2 = b.val.2 := ha'.trans hu
    let x : Fin n → VF (M := M) := b.val.1
    have htuple := normalized_tupleRV x
    let p : Point (M := M) n m := (x, fun i => b.val.2 (Fin.natAdd n i))
    have hap : SameRV a.val p := by
      apply (sameRV_iff _ _).mpr
      refine ⟨?_, ?_⟩
      · intro i
        have hi := congrFun ha' (Fin.castAdd m i)
        have hj := congrFun hv i
        change Fin.append (fun i => rv (vfAt a.val i)) a.val.2 (Fin.castAdd m i) = _ at hi
        simp only [Fin.append_left] at hi
        exact hi.trans (hj.trans (congrFun htuple i))
      · funext i
        simpa only [Fin.append_right, p] using congrFun hkey (Fin.natAdd n i)
    have hp := (isRVPullback_iff _).mp hA a.val a.property p hap
    refine ⟨⟨p, hp⟩, Subtype.ext ?_⟩
    change canonical p = b.val
    refine Prod.ext rfl ?_
    funext i
    cases i using Fin.addCases with
    | left i =>
      have hi := congrFun hv i
      have hj := congrFun hu (Fin.castAdd m i)
      change _ = b.val.2 (Fin.castAdd m i)
      exact (canonical_new p i).trans ((congrFun htuple i).symm.trans (hi.symm.trans hj))
    | right i => exact canonical_old p i

theorem pullbackObject_finiteVolume (A : DefSet (M := M) S n m)
    (hA : IsRVPullback (carrier A))
    (hfin : ∀ x : Fin n → VF (M := M),
      {t : Fin m → RV (M := M) | (x, t) ∈ carrier A}.Finite) :
    Map.FiniteFibres (rvObjectVolume (pullbackObject A)) := by
  intro t
  choose x hx using fun i => @CanonicalRV.encodedRv_surjective M sM hM (t.val i)
  have hx' (i : Fin n) : rv (x i) = t.val i := hx i
  let R : Set (Fin m → RV (M := M)) := {s | (x, s) ∈ carrier A}
  haveI : Finite R := (hfin x).to_subtype
  let F : R → rvObjectDomain (pullbackObject A) :=
    fun s => Map.toImage (rawKeyMap A) ⟨(x, s.val), s.property⟩
  apply (Set.finite_range F).subset
  intro u hu
  let s : Fin m → RV (M := M) := fun i => u.val (Fin.natAdd n i)
  obtain ⟨a, ha⟩ := u.property
  have ha' := (rawKeyMap_apply A a).symm.trans ha
  have hvol (i : Fin n) : u.val (Fin.castAdd m i) = t.val i :=
    congrArg (fun z : PresentedSet.univ (rawRVSpace n) S => z.val i) hu
  have hs : (x, s) ∈ carrier A := by
    apply (isRVPullback_iff _).mp hA a.val a.property (x, s)
    apply (sameRV_iff _ _).mpr
    refine ⟨?_, ?_⟩
    · intro i
      have hi := congrFun ha' (Fin.castAdd m i)
      change Fin.append (fun i => rv (vfAt a.val i)) a.val.2 (Fin.castAdd m i) = _ at hi
      simp only [Fin.append_left] at hi
      exact hi.trans ((hvol i).trans (hx' i).symm)
    · funext i
      have hi := congrFun ha' (Fin.natAdd n i)
      simpa only [Fin.append_right, s] using hi
  refine ⟨⟨s, hs⟩, Subtype.ext ?_⟩
  change Fin.append (fun i => rv (x i)) s = u.val
  funext i
  cases i using Fin.addCases with
  | left i => simpa only [Fin.append_left] using (hx' i).trans (hvol i).symm
  | right i => exact Fin.append_right _ _ i

theorem deformed_pullback_is_lift {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (h00 : M ⊨ Axioms.ACVF00) (v : Valuation (VF (M := M)) Γ)
    (hv : ∀ x y : VF (M := M), VFValued.predV x y ↔ v x ≤ v y)
    (hObstacles : ∀ N, UniformVerticalObstacles v S N) (A : DefSet (M := M) S n m) :
    ∃ U : @Section4.RVObject M (CanonicalStructure.normalize (M := M)) S n,
      ∃ f : Map A (rawLift U), Function.Bijective f := by
  obtain ⟨r, B, ⟨T⟩, hB⟩ := corollary_5_6 h00 v hv hObstacles A
  exact ⟨pullbackObject B, Map.comp (pullbackLiftMap B) T.toMap,
    (pullbackLiftMap_bijective B hB).comp T.bijective⟩

end SpecialTransformations.Section5
