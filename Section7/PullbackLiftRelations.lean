import Section7.LiftRelations
import Section4.CanonicalLift

/-!
# Definition 7.3 on arbitrary ambient RV-pullbacks

Keep the ambient pullbacks and the actual image of their product.
Each specified pair of complete fibres carries the graph of a bijection.
The mixed projection retains the original RV labels, and the Section 4
canonical lift is exactly the pullback of the companion under it.
-/

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section4

namespace SpecialTransformations.Section7

section Fibres

variable {X Y I J : Type*} (f : X → I) (g : Y → J)

def IsFullPullback (B : Set X) : Prop :=
  ∀ x ∈ B, ∀ y, f y = f x → y ∈ B

theorem isFullPullback_iff_preimage_image (B : Set X) :
    IsFullPullback f B ↔ f ⁻¹' (f '' B) = B := by
  constructor
  · intro h
    ext x
    exact ⟨fun ⟨y, hy, hyx⟩ => h y hy x hyx.symm, fun hx => ⟨x, hx, rfl⟩⟩
  · intro h x hx y hy
    have hm : y ∈ f ⁻¹' (f '' B) := ⟨x, hx, hy.symm⟩
    rwa [h] at hm

theorem isFullPullback_preimage (D : Set I) : IsFullPullback f (f ⁻¹' D) := by
  intro x hx y hy
  change f y ∈ D
  rwa [hy]

def ProjectionFibreBijection (A : Set (X × Y)) (t : I) (s : J) : Prop :=
  (∀ x, f x = t → ∃! y, g y = s ∧ (x, y) ∈ A) ∧
  (∀ y, g y = s → ∃! x, f x = t ∧ (x, y) ∈ A)

namespace ProjectionFibreBijection

variable {f g} {A : Set (X × Y)} {t : I} {s : J}

noncomputable def equiv (h : ProjectionFibreBijection f g A t s) :
    {x // f x = t} ≃ {y // g y = s} where
  toFun x := ⟨Classical.choose (h.1 x.val x.property),
    (Classical.choose_spec (h.1 x.val x.property)).1.1⟩
  invFun y := ⟨Classical.choose (h.2 y.val y.property),
    (Classical.choose_spec (h.2 y.val y.property)).1.1⟩
  left_inv x := by
    apply Subtype.ext
    have hxy := (Classical.choose_spec (h.1 x.val x.property)).1
    exact ((Classical.choose_spec (h.2 _ hxy.1)).2 x.val ⟨x.property, hxy.2⟩).symm
  right_inv y := by
    apply Subtype.ext
    have hxy := (Classical.choose_spec (h.2 y.val y.property)).1
    exact ((Classical.choose_spec (h.1 _ hxy.1)).2 y.val ⟨y.property, hxy.2⟩).symm

theorem equiv_graph (h : ProjectionFibreBijection f g A t s)
    (x : {x // f x = t}) (y : {y // g y = s}) :
    h.equiv x = y ↔ (x.val, y.val) ∈ A := by
  constructor
  · rintro rfl
    exact (Classical.choose_spec (h.1 x.val x.property)).1.2
  · intro hxy
    apply Subtype.ext
    exact ((Classical.choose_spec (h.1 x.val x.property)).2 y.val ⟨y.property, hxy⟩).symm

end ProjectionFibreBijection

def IsAmbientLift (B : Set X) (C : Set Y) (U : Set (I × J)) (A : Set (X × Y)) : Prop :=
  IsFullPullback f B ∧ IsFullPullback g C ∧
  A ⊆ B ×ˢ C ∧ U ⊆ (f '' B) ×ˢ (g '' C) ∧
  ∀ p ∈ U, ProjectionFibreBijection f g A p.1 p.2

def IsPartialAmbientLift (B : Set X) (C : Set Y) (U : Set (I × J)) (A : Set (X × Y)) : Prop :=
  ∃ U' ⊆ U, IsAmbientLift f g B C U' A

theorem IsAmbientLift.restrict {B : Set X} {C : Set Y} {U U' : Set (I × J)} {A : Set (X × Y)}
    (h : IsAmbientLift f g B C U A) (hU : U' ⊆ U) : IsAmbientLift f g B C U' A :=
  ⟨h.1, h.2.1, h.2.2.1, hU.trans h.2.2.2.1, fun p hp => h.2.2.2.2 p (hU hp)⟩

theorem ambientLift_of_full_fibres (B : Set X) (C : Set Y) (U : Set (I × J))
    (A : Set (X × Y)) (hB : IsFullPullback f B) (hC : IsFullPullback g C)
    (hU : U ⊆ (f '' B) ×ˢ (g '' C))
    (hA : ∀ p ∈ U, ProjectionFibreBijection f g A p.1 p.2) :
    IsAmbientLift f g B C U (A ∩ (B ×ˢ C)) := by
  refine ⟨hB, hC, Set.inter_subset_right, hU, ?_⟩
  intro p hp
  obtain ⟨⟨x₀, hx₀, ht⟩, ⟨y₀, hy₀, hs⟩⟩ := hU hp
  have h := hA p hp
  constructor
  · intro x hx
    have hxB := hB x₀ hx₀ x (hx.trans ht.symm)
    refine (existsUnique_congr (fun y => and_congr_right (fun hy => ?_))).mp (h.1 x hx)
    exact ⟨fun hxy => ⟨hxy, hxB, hC y₀ hy₀ y (hy.trans hs.symm)⟩, And.left⟩
  · intro y hy
    have hyC := hC y₀ hy₀ y (hy.trans hs.symm)
    refine (existsUnique_congr (fun x => and_congr_right (fun hx => ?_))).mp (h.2 y hy)
    exact ⟨fun hxy => ⟨hxy, hB x₀ hx₀ x (hx.trans ht.symm), hyC⟩, And.left⟩

end Fibres

theorem isLift_iff_projectionFibreBijection {K Γ : Type*} [Field K]
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) {m n : ℕ}
    (U : Set ((Fin m → RVCalc.RV v) × (Fin n → RVCalc.RV v)))
    (A : Set ((Fin m → K) × (Fin n → K))) :
    IsLift v U A ↔
      ∀ p ∈ U, ProjectionFibreBijection
        (fun a : Fin m → K => fun i => RVCalc.rv v (a i))
        (fun b : Fin n → K => fun i => RVCalc.rv v (b i)) A p.1 p.2 := by
  have he {d : ℕ} (a : Fin d → K) (t : Fin d → RVCalc.RV v) :
      a ∈ RVFibre v t ↔ (fun i => RVCalc.rv v (a i)) = t := ⟨funext, congrFun⟩
  simp only [IsLift, FibreBijection, ProjectionFibreBijection, he]

theorem isAmbientLift_univ_iff {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) {m n : ℕ}
    (U : Set ((Fin m → RVCalc.RV v) × (Fin n → RVCalc.RV v)))
    (A : Set ((Fin m → K) × (Fin n → K))) :
    IsAmbientLift
      (fun a : Fin m → K => fun i => RVCalc.rv v (a i))
      (fun b : Fin n → K => fun i => RVCalc.rv v (b i))
      Set.univ Set.univ U A ↔ IsLift v U A := by
  rw [isLift_iff_projectionFibreBijection v U A]
  constructor
  · exact fun h => h.2.2.2.2
  · intro h
    refine ⟨fun _ _ _ _ => Set.mem_univ _, fun _ _ _ _ => Set.mem_univ _,
      (fun _ _ => ⟨Set.mem_univ _, Set.mem_univ _⟩), ?_, h⟩
    intro p _
    obtain ⟨a, ha⟩ := rvFibre_nonempty v p.1
    obtain ⟨b, hb⟩ := rvFibre_nonempty v p.2
    exact ⟨⟨a, Set.mem_univ _, funext ha⟩, ⟨b, Set.mem_univ _, funext hb⟩⟩

section Canonical

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

def mixedRVProjection {n m : ℕ}
    (p : (Fin n → VFType (M := M)) × (Fin m → CanonicalRV.RVSort M)) :
    (Fin n → CanonicalRV.RVSort M) × (Fin m → CanonicalRV.RVSort M) :=
  (tupleRV p.1, p.2)

theorem rvLift_eq_companion_preimage (U : RVObject (M := M) S k) :
    (rvLift U).carrier = mixedRVProjection ⁻¹' U.companion.carrier := by
  ext p
  constructor
  · rintro ⟨u, hu, hv⟩
    exact ⟨u, Prod.ext hv hu⟩
  · rintro ⟨u, hu⟩
    exact ⟨u, congrArg Prod.snd hu, congrArg Prod.fst hu⟩

theorem rvLift_fullPullback (U : RVObject (M := M) S k) :
    IsFullPullback mixedRVProjection (rvLift U).carrier := by
  rw [rvLift_eq_companion_preimage]
  exact isFullPullback_preimage _ _

end Canonical

end SpecialTransformations.Section7
