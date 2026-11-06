import Section6.HenselianClosure
import Section6.DefinableMaps
import Section5.GeneralExistence

/-!
# Descent of a prepared RV-pullback to a functionally closed substructure

The geometric step of Lemma 6.3, using the actual Section 5 maps, inverse
maps, pullbacks and contractions. Surjectivity of rv on the substructure
realizes every finite key, including degenerate fibres. The final predicate
on RV is arbitrary, so its interpretation may include additional RV
structure; no preservation of its quantifiers in the ACVF overfield is used.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5

namespace SpecialTransformations.Section6

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S X : Set M} {n m l k : ℕ}

abbrev RealRepresentedIn (P : PresentedSpace (M := M)) (X : Set M) (p : Carrier P) :=
  @RepresentedIn LRV M (CanonicalStructure.normalize (M := M)) P X p

def PointIn (X : Set M) (p : Point (M := M) n m) : Prop :=
  ∀ i, pointValues p i ∈ X

def KeyIn (X : Set M) (u : Key (M := M) n m) : Prop :=
  (∀ i, (u.1 i).val ∈ X) ∧ ∀ j, (u.2 j).val ∈ X

theorem pointIn_iff_represented (X : Set M) (p : Point (M := M) n m) :
    PointIn X p ↔ RealRepresentedIn (pointSpace n m) X p := by
  constructor
  · intro hp
    exact ⟨⟨pointValues p, pointValues_domain p⟩, decode_pointValues p, hp⟩
  · rintro ⟨c, rfl, hc⟩ i
    rw [show pointValues (pDecode (pointSpace n m) c) = c.val from pointValues_decode c]
    exact hc i

theorem pointSpace_decode_injective :
    Function.Injective (pDecode (pointSpace (M := M) n m)) := by
  intro a b he
  apply Subtype.ext
  exact (pointValues_decode a).symm.trans
    ((congrArg pointValues he).trans (pointValues_decode b))

theorem keyIn_iff_represented (X : Set M) (u : Key (M := M) n m) :
    KeyIn X u ↔ RealRepresentedIn (keySpace n m) X u := by
  constructor
  · rintro ⟨hu, hv⟩
    refine ⟨⟨Sum.elim (fun i => (u.1 i).val) (fun j => (u.2 j).val),
      ⟨fun i => (u.1 i).property, fun j => (u.2 j).property⟩⟩, rfl, ?_⟩
    exact Sum.rec hu hv
  · rintro ⟨c, rfl, hc⟩
    exact ⟨fun i => hc (.inl i), fun j => hc (.inr j)⟩

theorem keySpace_decode_injective :
    Function.Injective (pDecode (keySpace (M := M) n m)) := by
  intro a b he
  apply Subtype.ext
  funext i
  cases i with
  | inl i => exact congrArg (fun u : Key (M := M) n m => (u.1 i).val) he
  | inr i => exact congrArg (fun u : Key (M := M) n m => (u.2 i).val) he

theorem map_preserves_pointIn
    (hX : NormalizedDclClosed X) (hSX : S ⊆ X)
    {A : DefSet (M := M) S n m} {B : DefSet (M := M) S l k}
    (f : Map A B) (a : A) (ha : PointIn X a.val) : PointIn X (f a).val := by
  apply (pointIn_iff_represented X _).mpr
  exact @map_preserves_represented LRV M (CanonicalStructure.normalize (M := M))
    (pointSpace n m) (pointSpace l k) S X hX hSX pointSpace_decode_injective A B f a
    ((pointIn_iff_represented X _).mp ha)

theorem map_preserves_keyIn
    (hX : NormalizedDclClosed X) (hSX : S ⊆ X)
    {A : PresentedSet (keySpace (M := M) n m) S}
    {B : PresentedSet (keySpace (M := M) l k) S}
    (f : Map A B) (a : A) (ha : KeyIn X a.val) : KeyIn X (f a).val := by
  apply (keyIn_iff_represented X _).mpr
  exact @map_preserves_represented LRV M (CanonicalStructure.normalize (M := M))
    (keySpace n m) (keySpace l k) S X hX hSX keySpace_decode_injective A B f a
    ((keyIn_iff_represented X _).mp ha)

/-- The actual special bijection and its actual definable inverse restrict
to inverse bijections on the substructure's points. -/
def restrictSpecialBijection
    (hX : NormalizedDclClosed X) (hSX : S ⊆ X)
    {A : DefSet (M := M) S n m} {B : DefSet (M := M) S n l}
    (T : SpecialBijection A B) :
    {a : A // PointIn X a.val} ≃ {b : B // PointIn X b.val} where
  toFun a := ⟨T.toMap a.val, map_preserves_pointIn hX hSX T.toMap a.val a.property⟩
  invFun b := ⟨T.inverseMap b.val, map_preserves_pointIn hX hSX T.inverseMap b.val b.property⟩
  left_inv a := Subtype.ext (T.inverse_apply a.val)
  right_inv b := Subtype.ext (T.apply_inverse b.val)

theorem keyIn_of_pointIn
    (hrv : ∀ a : VF (M := M), a.val ∈ X → (rv a).val ∈ X)
    {p : Point (M := M) n m} (hp : PointIn X p) : KeyIn X (key p) :=
  ⟨fun i => hrv (p.1 i) (hp (.inl i)), fun j => hp (.inr j)⟩

/-- Every key in the substructure has a point in the substructure's part
of the entire pullback. This includes rv(0) and zero-dimensional tuples. -/
theorem pullback_key_realized
    (hRV : ∀ t : RV (M := M), t.val ∈ X →
      ∃ a : VF (M := M), a.val ∈ X ∧ rv a = t)
    {A : DefSet (M := M) S n m} (hA : IsRVPullback (carrier A))
    (u : keyImage A) (hu : KeyIn X u.val) :
    ∃ a : A, PointIn X a.val ∧ toKeyImage A a = u := by
  choose a ha harv using fun i => hRV (u.val.1 i) (hu.1 i)
  let p : Point (M := M) n m := (a, u.val.2)
  have hpkey : key p = u.val := Prod.ext (funext harv) rfl
  obtain ⟨b, hb⟩ := u.property
  have hp : p ∈ carrier A :=
    (isRVPullback_iff _).mp hA b.val b.property p (hb.trans hpkey.symm)
  refine ⟨⟨p, hp⟩, ?_, Subtype.ext hpkey⟩
  intro i
  cases i with
  | inl i => exact ha i
  | inr j => exact hu.2 j

/-- The semantic descent identity of Lemma 6.3. The predicate P is
arbitrary on the henselian model's RV tuples. The right-hand side has
only RV witnesses, and both the key and the contraction output lie in X. -/
theorem prepared_exists_descends
    (hX : NormalizedDclClosed X) (hSX : S ⊆ X)
    (hrv : ∀ a : VF (M := M), a.val ∈ X → (rv a).val ∈ X)
    (hRV : ∀ t : RV (M := M), t.val ∈ X →
      ∃ a : VF (M := M), a.val ∈ X ∧ rv a = t)
    {A : DefSet (M := M) S n m} {B : DefSet (M := M) S n l}
    {D : DefSet (M := M) S 0 k}
    (T : SpecialBijection A B) (hB : IsRVPullback (carrier B))
    (f : Map A D) (hf : Contractible (Map.comp f T.inverseMap))
    (P : (Fin k → RV (M := M)) → Prop) :
    (∃ a : A, PointIn X a.val ∧ P (f a).val.2) ↔
      ∃ u : keyImage B, KeyIn X u.val ∧
        KeyIn X (contractionFun (Map.comp f T.inverseMap) u).val ∧
        P (contractionFun (Map.comp f T.inverseMap) u).val.2 := by
  constructor
  · rintro ⟨a, ha, hP⟩
    let b := T.toMap a
    have hb : PointIn X b.val := map_preserves_pointIn hX hSX T.toMap a ha
    have he : contractionFun (Map.comp f T.inverseMap) (toKeyImage B b) =
        toKeyImage D (f a) := by
      rw [contractionFun_spec _ hf]
      change toKeyImage D (f (T.inverseMap b)) = toKeyImage D (f a)
      rw [show T.inverseMap b = a from T.inverse_apply a]
    refine ⟨toKeyImage B b, keyIn_of_pointIn hrv hb, ?_, ?_⟩
    · rw [he]
      exact keyIn_of_pointIn hrv (map_preserves_pointIn hX hSX f a ha)
    · rw [he]
      exact hP
  · rintro ⟨u, hu, _, hP⟩
    obtain ⟨b, hb, hbu⟩ := pullback_key_realized hRV hB u hu
    let a := T.inverseMap b
    have ha : PointIn X a.val := map_preserves_pointIn hX hSX T.inverseMap b hb
    have he : contractionFun (Map.comp f T.inverseMap) u = toKeyImage D (f a) := by
      rw [← hbu, contractionFun_spec _ hf]
      rfl
    exact ⟨a, ha, by rw [he] at hP; exact hP⟩

/-- Section 5 supplies the preparation; Section 6 proves descent. The
only geometric preparation input here is the accepted earlier root-free
interface already present in Section 5's theorem. -/
theorem exists_preparation_with_descent
    {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (h00 : M ⊨ Axioms.ACVF00) (v : Valuation (VF (M := M)) Γ)
    (hv : ∀ a b, VFValued.predV a b ↔ v a ≤ v b)
    (hObstacles : ∀ N, UniformVerticalObstacles v S N)
    (hX : NormalizedDclClosed X) (hSX : S ⊆ X)
    (hrv : ∀ a : VF (M := M), a.val ∈ X → (rv a).val ∈ X)
    (hRV : ∀ t : RV (M := M), t.val ∈ X →
      ∃ a : VF (M := M), a.val ∈ X ∧ rv a = t)
    {A : DefSet (M := M) S n m} {D : DefSet (M := M) S 0 k} (f : Map A D) :
    ∃ l : ℕ, ∃ B : DefSet (M := M) S n l, ∃ T : SpecialBijection A B,
      IsRVPullback (carrier B) ∧ Contractible (Map.comp f T.inverseMap) ∧
      ∀ P : (Fin k → RV (M := M)) → Prop,
        ((∃ a : A, PointIn X a.val ∧ P (f a).val.2) ↔
          ∃ u : keyImage B, KeyIn X u.val ∧
            KeyIn X (contractionFun (Map.comp f T.inverseMap) u).val ∧
            P (contractionFun (Map.comp f T.inverseMap) u).val.2) := by
  obtain ⟨l, B, T, _, hB, hf⟩ :=
    map_preparation h00 v hv hObstacles (SpecialBijection.refl A) f
  exact ⟨l, B, T, hB, hf, prepared_exists_descends hX hSX hrv hRV T hB f hf⟩

end SpecialTransformations.Section6
