import Section5.TransformGeometry
import Section3.DefinableMeans
import Section3.MeanInBalls
import Section3.CanonicalContext
import Section3.PolynomialRoots

/-!
# Reusing finite definable means in the normalized presentations

The earlier-section theorem is used directly. The bridge below proves that
normalizing off-sort symbols preserves the actual VF field and its means;
it introduces no new parameters and no additional mathematical hypothesis.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer

namespace SpecialTransformations.Section5

private theorem map_finite_average {K K' : Type} [Field K] [Field K']
    (e : K ≃+* K') (F : Finset K) :
    e ((∑ x ∈ F, x) / (F.card : K)) =
      (∑ x ∈ F.image e, x) / ((F.image e).card : K') := by
  rw [map_div₀, map_sum, map_natCast, Finset.card_image_of_injective _ e.injective]
  congr 1
  symm
  exact Finset.sum_image (fun _ _ _ _ h => e.injective h)

def normalizeVFEquiv {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] :
    @RingEquiv (VF (M := M)) (@VFType M (CanonicalStructure.normalize (M := M)))
      (@vfInstMul M sM hM)
      (@vfInstMul M (CanonicalStructure.normalize (M := M)) (CanonicalStructure.normalized_model hM))
      (@vfInstAdd M sM hM)
      (@vfInstAdd M (CanonicalStructure.normalize (M := M)) (CanonicalStructure.normalized_model hM)) := by
  refine @RingEquiv.mk (@VFType M sM) (@VFType M (CanonicalStructure.normalize (M := M)))
    (@vfInstMul M sM hM)
    (@vfInstMul M (CanonicalStructure.normalize (M := M)) (CanonicalStructure.normalized_model hM))
    (@vfInstAdd M sM hM)
    (@vfInstAdd M (CanonicalStructure.normalize (M := M)) (CanonicalStructure.normalized_model hM))
    ⟨(fun x => ⟨x.val, x.property⟩), (fun x => ⟨x.val, x.property⟩),
      (fun _ => rfl), (fun _ => rfl)⟩ ?_ ?_
  · intro x y
    apply Subtype.ext
    exact (CanonicalStructure.normalize_fun Fn.vfMul ![x.val, y.val]
      (by intro i; fin_cases i; exact x.property; exact y.property)).symm
  · intro x y
    apply Subtype.ext
    exact (CanonicalStructure.normalize_fun Fn.vfAdd ![x.val, y.val]
      (by intro i; fin_cases i; exact x.property; exact y.property)).symm

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem mean_normalize (F : Finset (VF (M := M))) :
    (@Section3.Barycentre.mean M (CanonicalStructure.normalize (M := M))
      (CanonicalStructure.normalized_model hM) F).val = (Section3.Barycentre.mean F).val := by
  let N := @CanonicalStructure.normalize M sM
  let hN := @CanonicalStructure.normalized_model M sM hM
  let e := @normalizeVFEquiv M sM hM
  have he : F.image e = F := by
    change F.image id = F
    exact Finset.image_id
  have hm := @map_finite_average (@VFType M sM) (@VFType M N)
    (@VFValued.instFieldVFType M sM hM) (@VFValued.instFieldVFType M N hN) e F
  rw [he] at hm
  have hv := congrArg Subtype.val hm
  change (@Section3.Barycentre.mean M sM hM F).val = (@Section3.Barycentre.mean M N hN F).val at hv
  exact hv.symm

theorem mean_definable_normalized (h00 : M ⊨ Axioms.ACVF00) (S : Set M) {m : ℕ}
    (F : (Fin m → M) → Finset (VF (M := M)))
    (hF : @Section3.RawClosure.Tuple.RelationDefinable M (CanonicalStructure.normalize (M := M)) m S
      (@Section3.Barycentre.finiteFibreRelation M (CanonicalStructure.normalize (M := M)) m F))
    (N : ℕ) (hb : ∀ t, (F t).card ≤ N) :
    RawFun S (Fin m) (fun t => (Section3.Barycentre.mean (F t)).val) := by
  have hn := @Section3.Barycentre.mean_definable M (CanonicalStructure.normalize (M := M))
    (CanonicalStructure.normalized_model hM) m (Section3.normalized_model00 h00) S F hF N hb
  have he :
      (fun t => (@Section3.Barycentre.mean M (CanonicalStructure.normalize (M := M))
        (CanonicalStructure.normalized_model hM) (F t)).val) =
      (fun t => (Section3.Barycentre.mean (F t)).val) := funext (fun t => mean_normalize (F t))
  exact he ▸ hn

end SpecialTransformations.Section5

#check @SpecialTransformations.Section5.mean_definable_normalized
#print axioms SpecialTransformations.Section5.mean_definable_normalized


/-!
# Uniform finite-root centering in one VF coordinate

The finite combinatorial and geometric construction in the unary part of
Theorem 5.4. Its centres are means of whole retained-label fibres, rather
than chosen roots. Original-base definability is supplied separately by the
earlier-section definable-mean theorem.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer

namespace SpecialTransformations.Section5

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem rv_eq_zero_iff (x : VF (M := M)) : rv x = rv (0 : VF (M := M)) ↔ x = 0 := by
  constructor
  · intro h
    exact (CanonicalRV.encodedRv_zero_iff x).mp
      ((congrArg Subtype.val h).trans (RVCalc.rv_zero_eq hM))
  · rintro rfl
    rfl

theorem mean_sameRV (h00 : M ⊨ Axioms.ACVF00) (F : Finset (VF (M := M)))
    (hne : F.Nonempty) (a : VF (M := M)) (hF : ∀ x ∈ F, rv x = rv a) :
    rv (Section3.Barycentre.mean F) = rv a := by
  by_cases ha : a = 0
  · subst a
    have he : F = {0} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      constructor
      · obtain ⟨x, hx⟩ := hne
        exact ((rv_eq_zero_iff x).mp (hF x hx)) ▸ hx
      · intro x hx
        exact (rv_eq_zero_iff x).mp (hF x hx)
    simp [he, Section3.Barycentre.mean]
  · obtain ⟨Γ, hΓ, v, hv⟩ := VFValued.exists_valuation_predV (M := M)
    letI := hΓ
    have hball := Section3.Balls.rvFibre_eq_openDisc v hv a ha
    have hmem (x : VF (M := M)) (hx : x ∈ F) :
        x ∈ Section3.Balls.openDisc v a (↑(OrderDual.toDual (v a))) := by
      rw [← hball]
      exact congrArg Subtype.val (hF x hx)
    have hm := Section3.Barycentre.mean_mem_openDisc v hv h00 F hne a _ hmem
    rw [← hball] at hm
    exact Subtype.ext hm

def unaryPoint {m : ℕ} (x : VF (M := M)) (t : Fin m → RV (M := M)) :
    Point (M := M) 1 m := (![x], t)

theorem unaryPoint_eta {m : ℕ} (p : Point (M := M) 1 m) :
    unaryPoint (vfAt p 0) p.2 = p := by
  refine Prod.ext ?_ rfl
  funext i
  fin_cases i
  rfl

def rootFibre {m : ℕ} (Q : Finset (Point (M := M) 1 m)) (t : Fin m → RV (M := M)) :
    Finset (VF (M := M)) :=
  (Q.filter (fun p => p.2 = t)).image (fun p => vfAt p 0)

theorem mem_rootFibre {m : ℕ} (Q : Finset (Point (M := M) 1 m))
    (t : Fin m → RV (M := M)) (x : VF (M := M)) :
    x ∈ rootFibre Q t ↔ unaryPoint x t ∈ Q := by
  constructor
  · intro hx
    obtain ⟨p, hp, he⟩ := Finset.mem_image.mp hx
    obtain ⟨hpQ, hpt⟩ := Finset.mem_filter.mp hp
    have hp : unaryPoint x t = p := by rw [← he, ← hpt]; exact unaryPoint_eta p
    rwa [← hp] at hpQ
  · intro hx
    exact Finset.mem_image.mpr ⟨unaryPoint x t, Finset.mem_filter.mpr ⟨hx, rfl⟩, rfl⟩

theorem rootFibre_card_le {m : ℕ} (Q : Finset (Point (M := M) 1 m))
    (t : Fin m → RV (M := M)) : (rootFibre Q t).card ≤ Q.card :=
  (Finset.card_image_le).trans (Finset.card_filter_le _ _)

def RootBound {m : ℕ} (Q : Finset (Point (M := M) 1 m)) (d : ℕ) : Prop :=
  ∀ t, (∃ x ∈ rootFibre Q t, x ≠ 0) → (rootFibre Q t).card ≤ d

theorem rootBound_card {m : ℕ} (Q : Finset (Point (M := M) 1 m)) : RootBound Q Q.card :=
  fun t _ => rootFibre_card_le Q t

theorem rootBound_zero {m : ℕ} (Q : Finset (Point (M := M) 1 m))
    (hQ : RootBound Q 0) : ∀ p ∈ Q, vfAt p 0 = 0 := by
  intro p hp
  by_contra hne
  have hmem : vfAt p 0 ∈ rootFibre Q p.2 :=
    (mem_rootFibre Q p.2 _).mpr ((unaryPoint_eta p).symm ▸ hp)
  have := hQ p.2 ⟨vfAt p 0, hmem, hne⟩
  have := Finset.card_pos.mpr ⟨vfAt p 0, hmem⟩
  omega

def rootFocusGeometry {m : ℕ} {A : Set (Point (M := M) 1 m)} {k : Fin m}
    (h00 : M ⊨ Axioms.ACVF00) (hA : Tagged A 0 k)
    (Q : Finset (Point (M := M) 1 m)) (hQ : (Q : Set _) ⊆ A) : FocusGeometry A 0 k where
  tagged := hA
  locus := hull (Q : Set _)
  locus_pullback := hull_idem _
  locus_subset := hull_mono hQ
  center p := Section3.Barycentre.mean (rootFibre Q p.2)
  independent := by
    intro p hp q hq he
    have ht : p.2 = q.2 := by
      simpa [erase, replace] using congrArg (fun z : Point (M := M) 1 m => z.2) he
    rw [ht]
  center_mem := by
    intro p hp
    obtain ⟨q, hq, he⟩ := hp.2
    have hqp := (sameRV_iff q p).mp he
    have hne : (rootFibre Q p.2).Nonempty := by
      refine ⟨vfAt q 0, (mem_rootFibre Q p.2 _).mpr ?_⟩
      rw [← hqp.2, unaryPoint_eta]
      exact hq
    have hrv : ∀ x ∈ rootFibre Q p.2, rv x = rv (vfAt p 0) := by
      intro x hx
      have hxr := hQ ((mem_rootFibre Q p.2 x).mp hx)
      exact (hA (unaryPoint x p.2) hxr).symm.trans (hA p hp.1)
    have hm := mean_sameRV h00 (rootFibre Q p.2) hne (vfAt p 0) hrv
    refine ⟨q, hq, he.trans ?_⟩
    apply (sameRV_iff _ _).mpr
    refine ⟨?_, rfl⟩
    intro i
    fin_cases i
    simpa [replace, vfAt] using hm.symm

@[simp] theorem rootFocus_center {m : ℕ} {A : Set (Point (M := M) 1 m)} {k : Fin m}
    (h00 : M ⊨ Axioms.ACVF00) (hA : Tagged A 0 k)
    (Q : Finset (Point (M := M) 1 m)) (hQ : (Q : Set _) ⊆ A) (p : Point (M := M) 1 m) :
    (rootFocusGeometry h00 hA Q hQ).center p = Section3.Barycentre.mean (rootFibre Q p.2) := rfl

def nextRootSet {m : ℕ} {A : Set (Point (M := M) 1 m)} {k : Fin m}
    (D : FocusGeometry A 0 k) (Q : Finset (Point (M := M) 1 m)) :
    Finset (Point (M := M) 1 (1 + m)) := Q.image (fun q => canonical (D.eta q))

/-- Each new label fibre is contained in one translated child of an old
root fibre. This inclusion is enough for the uniform cardinality decrease. -/
theorem nextRoot_fibre_subset {m : ℕ} {A : Set (Point (M := M) 1 m)} {k : Fin m}
    (h00 : M ⊨ Axioms.ACVF00) (hA : Tagged A 0 k)
    (Q : Finset (Point (M := M) 1 m)) (hQ : (Q : Set _) ⊆ A)
    (t : Fin (1 + m) → RV (M := M)) :
    rootFibre (nextRootSet (rootFocusGeometry h00 hA Q hQ) Q) t ⊆
      ((rootFibre Q (fun i => t (Fin.natAdd 1 i))).filter
        (fun x => rv (x - Section3.Barycentre.mean (rootFibre Q (fun i => t (Fin.natAdd 1 i)))) = t 0)).image
          (fun x => x - Section3.Barycentre.mean (rootFibre Q (fun i => t (Fin.natAdd 1 i)))) := by
  intro x hx
  have hxQ := (mem_rootFibre _ t x).mp hx
  obtain ⟨q, hq, he⟩ := Finset.mem_image.mp hxQ
  let D := rootFocusGeometry h00 hA Q hQ
  have hqc : q ∈ D.locus := by
    change q ∈ hull (Q : Set (Point (M := M) 1 m))
    exact subset_hull _ hq
  have ht : q.2 = fun i => t (Fin.natAdd 1 i) := by
    funext i
    have hh := congrArg (fun z : Point (M := M) 1 (1 + m) => z.2 (Fin.natAdd 1 i)) he
    simpa [nextRootSet, D, unaryPoint] using hh
  have hxv : vfAt q 0 - Section3.Barycentre.mean (rootFibre Q q.2) = x := by
    have hh := congrArg (fun z : Point (M := M) 1 (1 + m) => vfAt z 0) he
    simpa [D, canonical, FocusGeometry.eta, hqc, replace, vfAt, unaryPoint] using hh
  refine Finset.mem_image.mpr ⟨vfAt q 0, Finset.mem_filter.mpr ⟨?_, ?_⟩, ?_⟩
  · apply (mem_rootFibre _ _ _).mpr
    rw [← ht, unaryPoint_eta]
    exact hq
  · have hh := (canonical_new (D.eta q) (0 : Fin 1)).symm.trans
      (congrArg (fun z : Point (M := M) 1 (1 + m) => z.2 0) he)
    have hh' : rv (vfAt q 0 - Section3.Barycentre.mean (rootFibre Q q.2)) = t 0 := by
      simpa [D, FocusGeometry.eta, hqc, replace, vfAt, unaryPoint] using hh
    rwa [ht] at hh'
  · rwa [ht] at hxv

/-- One simultaneous mean-centering step lowers the bound on every
nondegenerate root fibre. Singleton root fibres become the zero fibre. -/
theorem rootBound_step {m : ℕ} {A : Set (Point (M := M) 1 m)} {k : Fin m}
    (h00 : M ⊨ Axioms.ACVF00) (hA : Tagged A 0 k)
    (Q : Finset (Point (M := M) 1 m)) (hQ : (Q : Set _) ⊆ A)
    (d : ℕ) (hd : RootBound Q (d + 1)) :
    RootBound (nextRootSet (rootFocusGeometry h00 hA Q hQ) Q) d := by
  intro t hne
  let F := rootFibre Q (fun i => t (Fin.natAdd 1 i))
  let C := F.filter (fun x => rv (x - Section3.Barycentre.mean F) = t 0)
  have hsub := nextRoot_fibre_subset h00 hA Q hQ t
  obtain ⟨x, hx, hx0⟩ := hne
  obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp (hsub hx)
  have hyF : y ∈ F := (Finset.mem_filter.mp hy).1
  have htwo : 2 ≤ F.card := by
    by_contra hsmall
    have hcard : F.card ≤ 1 := by omega
    have he : F = {y} := Finset.eq_singleton_iff_unique_mem.mpr
      ⟨hyF, fun z hz => (Finset.card_le_one_iff.mp hcard) hz hyF⟩
    have hm : Section3.Barycentre.mean F = y := by simp [he, Section3.Barycentre.mean]
    apply hx0
    rw [← hyx, hm, sub_self]
  have hnonzero : ∃ y ∈ F, y ≠ 0 := by
    by_contra! hz
    have hs : F ⊆ {0} := fun y hy => Finset.mem_singleton.mpr (hz y hy)
    have := Finset.card_le_card hs
    simp only [Finset.card_singleton] at this
    omega
  have hb : F.card ≤ d + 1 := hd _ hnonzero
  have hc : C.card < F.card := by
    have he : C = F.filter (fun x => iRv (x - Section3.Barycentre.mean F).val = (t 0).val) := by
      ext x
      simp only [C, Finset.mem_filter, Subtype.ext_iff]
      rfl
    rw [he]
    exact Section3.Barycentre.fibre_card_lt h00 F htwo (t 0).val
  have hbound : (rootFibre (nextRootSet (rootFocusGeometry h00 hA Q hQ) Q) t).card ≤ C.card :=
    (Finset.card_le_card hsub).trans Finset.card_image_le
  omega

end SpecialTransformations.Section5

#check @SpecialTransformations.Section5.rootBound_step
#print axioms SpecialTransformations.Section5.rootBound_step

namespace SpecialTransformations.Section5

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {m : ℕ}

abbrev pDomain (P : PresentedSpace (M := M)) :=
  @DefinableGeometry.Space.domain LRV M (CanonicalStructure.normalize (M := M)) P

abbrev pDecode (P : PresentedSpace (M := M)) (z : pDomain P) : Carrier P :=
  @DefinableGeometry.Space.decode LRV M (CanonicalStructure.normalize (M := M)) P z

theorem unary_code_iff (R : DefSet (M := M) S 1 m) (z : Fin 1 ⊕ Fin m → M) :
    z ∈ @DefinableGeometry.Space.preimage LRV M (CanonicalStructure.normalize (M := M))
      (pointSpace 1 m) (carrier R) ↔
    ∃ x : VF (M := M), ∃ t : Fin m → RV (M := M), x.val = z (.inl 0) ∧
      (∀ i, (t i).val = z (.inr i)) ∧ unaryPoint x t ∈ carrier R := by
  constructor
  · rintro ⟨hz, hR⟩
    let p := pDecode (pointSpace (M := M) 1 m) ⟨z, hz⟩
    refine ⟨vfAt p 0, p.2, rfl, fun _ => rfl, ?_⟩
    rw [unaryPoint_eta]
    exact hR
  · rintro ⟨x, t, hx, ht, hR⟩
    have hz : z ∈ pDomain (pointSpace (M := M) 1 m) := by
      constructor
      · intro i
        fin_cases i
        change iVF (z (.inl 0))
        rw [← hx]
        exact x.property
      · intro i
        change iRV (z (.inr i))
        rw [← ht i]
        exact (t i).property
    refine ⟨hz, ?_⟩
    have he : pDecode (pointSpace (M := M) 1 m) ⟨z, hz⟩ = unaryPoint x t := by
      refine Prod.ext ?_ ?_
      · funext i
        fin_cases i
        exact Subtype.ext hx.symm
      · funext i
        exact Subtype.ext (ht i).symm
    change pDecode (pointSpace (M := M) 1 m) ⟨z, hz⟩ ∈ carrier R
    rwa [he]

/-- A genuine finite definable subset of the current domain. No separation,
contraction, or special-bijection conclusion is part of this data. -/
structure FiniteRootSet (A : DefSet (M := M) S 1 m) where
  set : DefSet (M := M) S 1 m
  finite : (carrier set).Finite
  subset : carrier set ⊆ carrier A

namespace FiniteRootSet

variable {A : DefSet (M := M) S 1 m}

def points (R : FiniteRootSet A) : Finset (Point (M := M) 1 m) := R.finite.toFinset

@[simp] theorem mem_points (R : FiniteRootSet A) (p : Point (M := M) 1 m) :
    p ∈ R.points ↔ p ∈ carrier R.set := Set.Finite.mem_toFinset _

theorem points_subset (R : FiniteRootSet A) :
    (R.points : Set (Point (M := M) 1 m)) ⊆ carrier A :=
  fun p hp => R.subset ((R.mem_points p).mp hp)

def rawFamily (R : FiniteRootSet A) (z : Fin m → M) : Finset (VF (M := M)) :=
  if hz : ∀ i, iRV (z i) then rootFibre R.points (fun i => ⟨z i, hz i⟩) else ∅

theorem rawFamily_labels (R : FiniteRootSet A) (t : Fin m → RV (M := M)) :
    R.rawFamily (fun i => (t i).val) = rootFibre R.points t := by
  unfold rawFamily
  rw [dif_pos (fun i => (t i).property)]

theorem rawFamily_bound (R : FiniteRootSet A) (z : Fin m → M) :
    (R.rawFamily z).card ≤ R.points.card := by
  unfold rawFamily
  split_ifs
  · exact rootFibre_card_le _ _
  · simp

theorem rawFamily_definable (R : FiniteRootSet A) :
    @Section3.RawClosure.Tuple.RelationDefinable M (CanonicalStructure.normalize (M := M)) m S
      (@Section3.Barycentre.finiteFibreRelation M (CanonicalStructure.normalize (M := M)) m R.rawFamily) := by
  let σ : Fin 1 ⊕ Fin m → Fin m ⊕ Fin 1 := Sum.elim (fun _ => Sum.inr 0) Sum.inl
  have h := @Set.Definable.preimage_comp M S LRV (CanonicalStructure.normalize (M := M))
    (Fin 1 ⊕ Fin m) (Fin m ⊕ Fin 1) σ _ (setDefinable R.set)
  change @Set.Definable M S LRV (CanonicalStructure.normalize (M := M)) (Fin m ⊕ Fin 1)
    {z | ∃ x ∈ R.rawFamily (z ∘ Sum.inl), x.val = z (.inr 0)}
  convert h using 1
  ext z
  rw [Set.mem_preimage, unary_code_iff]
  constructor
  · rintro ⟨x, hx, he⟩
    by_cases ht : ∀ i, iRV (z (.inl i))
    · have hx' : x ∈ rootFibre R.points (fun i => ⟨z (.inl i), ht i⟩) := by
        simpa only [rawFamily, Function.comp_apply, dif_pos ht] using hx
      refine ⟨x, (fun i => ⟨z (.inl i), ht i⟩), he, fun _ => rfl, ?_⟩
      exact (R.mem_points _).mp ((mem_rootFibre _ _ _).mp hx')
    · have hh : R.rawFamily (z ∘ Sum.inl) = ∅ := dif_neg ht
      rw [hh] at hx
      exact (Finset.notMem_empty _ hx).elim
  · rintro ⟨x, t, hx, ht, hR⟩
    refine ⟨x, ?_, hx⟩
    have htv : (fun i => (t i).val) = z ∘ Sum.inl := funext ht
    rw [← htv, R.rawFamily_labels]
    exact (mem_rootFibre _ _ _).mpr ((R.mem_points _).mpr hR)

def meanMap (R : FiniteRootSet A) (h00 : M ⊨ Axioms.ACVF00)
    (B : DefSet (M := M) S 1 m) : Map B (PresentedSet.univ (Section4.vfSpace 1) S) :=
  Map.ofCodes (M := M) (sM := sM) (P := pointSpace 1 m) (Q := Section4.vfSpace 1) B
    (fun p => ![Section3.Barycentre.mean (rootFibre R.points p.2)])
    (fun z _ => (Section3.Barycentre.mean (R.rawFamily (z ∘ Sum.inr))).val)
    (by
      intro i
      have hf := @mean_definable_normalized M sM hM h00 S m R.rawFamily R.rawFamily_definable
        R.points.card R.rawFamily_bound
      exact @Set.DefinableFun.comp M LRV (CanonicalStructure.normalize (M := M))
        (Fin m) (Fin 1 ⊕ Fin m) S _ inferInstance
        (fun z => z ∘ Sum.inr) (fun j => rawProj S (Sum.inr j : Fin 1 ⊕ Fin m)) hf)
    (by
      intro c i
      exact (Section3.Barycentre.mean (R.rawFamily (c.val ∘ Sum.inr))).property)
    (by
      intro c
      funext i
      fin_cases i
      apply Subtype.ext
      exact congrArg (fun F => (Section3.Barycentre.mean F).val)
        (R.rawFamily_labels (pDecode (pointSpace (M := M) 1 m) c).2))

def focus (R : FiniteRootSet A) (h00 : M ⊨ Axioms.ACVF00) {k : Fin m}
    (hA : Tagged (carrier A) 0 k) : Focus A 0 k :=
  let D := rootFocusGeometry h00 hA R.points R.points_subset
  { toFocusGeometry := D
    locus_definable := by
      have he : (R.points : Set (Point (M := M) 1 m)) = carrier R.set := by ext p; exact R.mem_points p
      change SetDefinable (pointSpace 1 m) S (hull (R.points : Set (Point (M := M) 1 m)))
      rw [he]
      exact hull_definable R.set
    center_graph := by
      let C : DefSet (M := M) S 1 m := PresentedSet.mk (carrier A ∩ D.locus)
        (SetDefinable.inter _ (setDefinable A) (by
          have he : (R.points : Set (Point (M := M) 1 m)) = carrier R.set := by ext p; exact R.mem_points p
          change SetDefinable (pointSpace 1 m) S (hull (R.points : Set (Point (M := M) 1 m)))
          rw [he]
          exact hull_definable R.set))
      apply RelationDefinable.congr _ _ (Map.graph_definable (R.meanMap h00 C))
      intro p z
      constructor
      · rintro ⟨a, rfl, he⟩
        exact ⟨a.property, (congrFun he 0).symm⟩
      · rintro ⟨hp, he⟩
        refine ⟨⟨p, hp⟩, rfl, ?_⟩
        funext i
        fin_cases i
        exact he.symm }

end FiniteRootSet
end SpecialTransformations.Section5

namespace SpecialTransformations.Section5

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

namespace Chain

variable {S : Set M} {n m l k : ℕ}
variable {A : DefSet (M := M) S n m} {B : DefSet (M := M) S n l} {C : DefSet (M := M) S n k}

def lastKind {m₁ m₂ : ℕ} {X : DefSet (M := M) S n m₁} {Y : DefSet (M := M) S n m₂}
    (previous : Option Bool) : Chain S n X Y → Option Bool
  | .nil _ => previous
  | .cons (.canonical _) tail => tail.lastKind (some false)
  | .cons (.centripetal _) tail => tail.lastKind (some true)

theorem alternating_none (T : Chain S n A B) (previous : Option Bool)
    (hT : T.Alternating previous) : T.Alternating none := by
  cases T with
  | nil => trivial
  | cons p tail =>
    cases p <;> exact ⟨by decide, hT.2⟩

theorem append_alternating (T : Chain S n A B) (U : Chain S n B C)
    (previous : Option Bool) (hT : T.Alternating previous)
    (hU : U.Alternating (T.lastKind previous)) : (T.append U).Alternating previous := by
  induction T generalizing previous with
  | nil => exact hU
  | cons p tail ih =>
    cases p with
    | canonical A => exact ⟨hT.1, ih U (some false) hT.2 hU⟩
    | centripetal D => exact ⟨hT.1, ih U (some true) hT.2 hU⟩

theorem append_toMap (T : Chain S n A B) (U : Chain S n B C) :
    (T.append U).toMap = Map.comp U.toMap T.toMap := by
  apply Map.ext
  intro a
  induction T with
  | nil => rfl
  | cons p tail ih => exact ih U (p.toMap a)

theorem lastKind_tagged {A : DefSet (M := M) S 1 m} {B : DefSet (M := M) S 1 l}
    (T : Chain S 1 A B) (previous : Option Bool)
    (hA : previous = some false → ∃ k : Fin m, Tagged (carrier A) 0 k)
    (hT : T.lastKind previous = some false) : ∃ k : Fin l, Tagged (carrier B) 0 k := by
  induction T generalizing previous with
  | nil A => exact hA hT
  | cons p tail ih =>
    cases p with
    | canonical A =>
      apply ih (some false) ?_ hT
      intro _
      refine ⟨Fin.castAdd _ (0 : Fin 1), ?_⟩
      rw [canonicalImage_carrier]
      exact canonical_tagged _ _
    | centripetal D => exact ih (some true) (by intro h; cases h) hT

end Chain

namespace FiniteRootSet

variable {S : Set M} {m l k : ℕ}
variable {A : DefSet (M := M) S 1 m} {B : DefSet (M := M) S 1 l} {C : DefSet (M := M) S 1 k}

def push (R : FiniteRootSet A) (f : Map A B) : FiniteRootSet B where
  set := Map.image (Map.comp f (Map.inclusion R.subset))
  finite := by
    haveI : Finite R.set := R.finite.to_subtype
    exact Set.finite_range (fun r : R.set => (f ⟨r.val, R.subset r.property⟩).val)
  subset := by
    rintro p ⟨r, rfl⟩
    exact (f ⟨r.val, R.subset r.property⟩).property

theorem mem_push_points (R : FiniteRootSet A) (f : Map A B) (b : Point (M := M) 1 l) :
    b ∈ (R.push f).points ↔ ∃ a : A, a.val ∈ R.points ∧ (f a).val = b := by
  rw [mem_points]
  change (∃ r : R.set, (f ⟨r.val, R.subset r.property⟩).val = b) ↔ _
  constructor
  · rintro ⟨r, he⟩
    exact ⟨⟨r.val, R.subset r.property⟩, (R.mem_points _).mpr r.property, he⟩
  · rintro ⟨a, ha, he⟩
    exact ⟨⟨a.val, (R.mem_points _).mp ha⟩, he⟩

theorem push_id_points (R : FiniteRootSet A) : (R.push (Map.id A)).points = R.points := by
  ext p
  rw [mem_push_points]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ha
  · intro hp
    exact ⟨⟨p, R.points_subset hp⟩, hp, rfl⟩

theorem push_comp_points (R : FiniteRootSet A) (f : Map A B) (g : Map B C) :
    ((R.push f).push g).points = (R.push (Map.comp g f)).points := by
  ext c
  simp only [mem_push_points]
  constructor
  · rintro ⟨b, ⟨a, ha, he⟩, hc⟩
    have hab : f a = b := Subtype.ext he
    refine ⟨a, ha, ?_⟩
    change (g (f a)).val = c
    rw [hab]
    exact hc
  · rintro ⟨a, ha, hc⟩
    exact ⟨f a, ⟨a, ha, rfl⟩, hc⟩

def stepTarget (R : FiniteRootSet A) (h00 : M ⊨ Axioms.ACVF00) {j : Fin m}
    (hA : Tagged (carrier A) 0 j) := canonicalImage (R.focus h00 hA).etaImage

def step (R : FiniteRootSet A) (h00 : M ⊨ Axioms.ACVF00) {j : Fin m}
    (hA : Tagged (carrier A) 0 j) : SpecialBijection A (R.stepTarget h00 hA) :=
  ⟨.cons (.centripetal (R.focus h00 hA))
    (.cons (.canonical _) (.nil _)), by decide, by decide, trivial⟩

theorem step_points (R : FiniteRootSet A) (h00 : M ⊨ Axioms.ACVF00) {j : Fin m}
    (hA : Tagged (carrier A) 0 j) :
    (R.push (R.step h00 hA).toMap).points =
      nextRootSet (rootFocusGeometry h00 hA R.points R.points_subset) R.points := by
  ext q
  rw [mem_push_points]
  constructor
  · rintro ⟨a, ha, he⟩
    exact Finset.mem_image.mpr ⟨a.val, ha, he⟩
  · intro hq
    obtain ⟨p, hp, he⟩ := Finset.mem_image.mp hq
    exact ⟨⟨p, R.points_subset hp⟩, hp, he⟩

theorem step_bound (R : FiniteRootSet A) (h00 : M ⊨ Axioms.ACVF00) {j : Fin m}
    (hA : Tagged (carrier A) 0 j) (d : ℕ) (hd : RootBound R.points (d + 1)) :
    RootBound (R.push (R.step h00 hA).toMap).points d := by
  rw [R.step_points h00 hA]
  exact rootBound_step h00 hA R.points R.points_subset d hd

theorem step_tagged (R : FiniteRootSet A) (h00 : M ⊨ Axioms.ACVF00) {j : Fin m}
    (hA : Tagged (carrier A) 0 j) :
    Tagged (carrier (R.stepTarget h00 hA)) 0 (Fin.castAdd m (0 : Fin 1)) := by
  have hset : carrier (R.stepTarget h00 hA) = canonical '' carrier (R.focus h00 hA).etaImage :=
    canonicalImage_carrier _
  rw [hset]
  exact canonical_tagged _ _

theorem iterate (h00 : M ⊨ Axioms.ACVF00) (d : ℕ) :
    ∀ {m : ℕ} {A : DefSet (M := M) S 1 m} (R : FiniteRootSet A)
      (j : Fin m) (hA : Tagged (carrier A) 0 j), RootBound R.points d →
      ∃ l : ℕ, ∃ B : DefSet (M := M) S 1 l, ∃ T : Chain S 1 A B,
        T.Alternating (some false) ∧ RootBound (R.push T.toMap).points 0 := by
  induction d with
  | zero =>
    intro m A R j hA hd
    refine ⟨m, A, .nil A, trivial, ?_⟩
    simpa only [Chain.toMap, R.push_id_points] using hd
  | succ d ih =>
    intro m A R j hA hd
    let V := R.step h00 hA
    let Q := R.push V.toMap
    obtain ⟨l, B, U, hU, hroot⟩ := ih Q (Fin.castAdd m (0 : Fin 1))
      (R.step_tagged h00 hA) (R.step_bound h00 hA d hd)
    let T : Chain S 1 A B := .cons (.centripetal (R.focus h00 hA)) (.cons (.canonical _) U)
    refine ⟨l, B, T, ⟨by decide, by decide, hU⟩, ?_⟩
    have hmap : T.toMap = Map.comp U.toMap V.toMap := by
      apply Map.ext
      intro a
      rfl
    have he := R.push_comp_points V.toMap U.toMap
    rw [← hmap] at he
    rw [← he]
    exact hroot

/-- The finite iteration is an actual definable special bijection. It has
the stronger boundary condition needed to append it after a canonical step. -/
theorem centralize_tagged (h00 : M ⊨ Axioms.ACVF00) (R : FiniteRootSet A)
    (j : Fin m) (hA : Tagged (carrier A) 0 j) :
    ∃ l : ℕ, ∃ B : DefSet (M := M) S 1 l, ∃ T : Chain S 1 A B,
      T.Alternating (some false) ∧ ∀ a : A, a.val ∈ carrier R.set → vfAt (T.toMap a).val 0 = 0 := by
  obtain ⟨l, B, T, hT, hz⟩ := iterate h00 R.points.card R j hA (rootBound_card _)
  refine ⟨l, B, T, hT, ?_⟩
  intro a ha
  apply rootBound_zero (R.push T.toMap).points hz
  exact (R.mem_push_points T.toMap _).mpr ⟨a, (R.mem_points _).mpr ha, rfl⟩

end FiniteRootSet
end SpecialTransformations.Section5

#check @SpecialTransformations.Section5.FiniteRootSet.centralize_tagged
#print axioms SpecialTransformations.Section5.FiniteRootSet.centralize_tagged

namespace SpecialTransformations.Section5.FiniteRootSet

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {m l : ℕ}
variable {A₀ : DefSet (M := M) S 1 l} {A : DefSet (M := M) S 1 m}

/-- Root centering can follow any initial special bijection while keeping
the concatenation genuinely alternating. An existing terminal canonical
step is used directly; otherwise a canonical step is inserted first. -/
theorem centralize_after (h00 : M ⊨ Axioms.ACVF00) (R : FiniteRootSet A)
    (τ : SpecialBijection A₀ A) :
    ∃ r : ℕ, ∃ B : DefSet (M := M) S 1 r, ∃ T : SpecialBijection A B,
      (τ.chain.append T.chain).Alternating none ∧
        ∀ a : A, a.val ∈ carrier R.set → vfAt (T.toMap a).val 0 = 0 := by
  by_cases hlast : τ.chain.lastKind none = some false
  · obtain ⟨j, hj⟩ := τ.chain.lastKind_tagged none (by intro h; cases h) hlast
    obtain ⟨r, B, U, hU, hz⟩ := centralize_tagged h00 R j hj
    let T : SpecialBijection A B := ⟨U, U.alternating_none (some false) hU⟩
    refine ⟨r, B, T, ?_, hz⟩
    apply τ.chain.append_alternating U none τ.alternating
    simpa only [hlast] using hU
  · let f := Map.toImage (canonicalMap A)
    let Q := R.push f
    have htag : Tagged (carrier (canonicalImage A)) 0 (Fin.castAdd m (0 : Fin 1)) := by
      rw [canonicalImage_carrier]
      exact canonical_tagged _ _
    obtain ⟨r, B, U, hU, hz⟩ := centralize_tagged h00 Q (Fin.castAdd m (0 : Fin 1)) htag
    let T : SpecialBijection A B := ⟨.cons (.canonical A) U, by decide, hU⟩
    refine ⟨r, B, T, ?_, ?_⟩
    · apply τ.chain.append_alternating T.chain none τ.alternating
      exact ⟨hlast, hU⟩
    · intro a ha
      apply hz (f a)
      apply (Q.mem_points _).mp
      exact (R.mem_push_points f _).mpr ⟨a, (R.mem_points _).mpr ha, rfl⟩

end SpecialTransformations.Section5.FiniteRootSet

#check @SpecialTransformations.Section5.FiniteRootSet.centralize_after
#print axioms SpecialTransformations.Section5.FiniteRootSet.centralize_after

namespace SpecialTransformations.Section5

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {m l : ℕ}

def ScalarContractible {A : DefSet (M := M) S 1 m} (f : A → VF (M := M)) : Prop :=
  ∀ a b : A, SameRV a.val b.val → rv (f a) = rv (f b)

theorem scalarContractible_iff {A : DefSet (M := M) S 1 m} (f : A → VF (M := M)) :
    ScalarContractible f ↔
      Contractible (fun a : A => (⟨unaryPoint (f a) Fin.elim0, Set.mem_univ _⟩ :
        PresentedSet.univ (pointSpace (M := M) 1 0) S)) := by
  constructor
  · intro hf a b he
    apply (sameRV_iff _ _).mpr
    refine ⟨?_, rfl⟩
    intro i
    fin_cases i
    exact hf a b he
  · intro hf a b he
    exact ((sameRV_iff _ _).mp (hf a b he)).1 0

/-- Once all polynomial roots are on zero VF fibres, every nonzero final
fibre has a root-free open-ball inverse image, hence constant polynomial RV. -/
theorem polynomial_contractible_of_zero_roots
    {A₀ : DefSet (M := M) S 1 0} {B : DefSet (M := M) S 1 m}
    (U : SpecialBijection A₀ B) (hB : IsRVPullback (carrier B))
    (p : Polynomial (VF (M := M)))
    (hz : ∀ a : A₀, p.eval (vfAt a.val 0) = 0 → vfAt (U.toMap a).val 0 = 0) :
    ScalarContractible (fun b : B => p.eval (vfAt (U.inverseMap b).val 0)) := by
  intro b c hbc
  obtain ⟨hbcv, hbct⟩ := (sameRV_iff _ _).mp hbc
  by_cases hb : vfAt b.val 0 = 0
  · have hc : vfAt c.val 0 = 0 := (rv_eq_zero_iff _).mp (by
      change rv (vfAt c.val 0) = rv (0 : VF (M := M))
      exact (hbcv 0).symm.trans (congrArg rv hb))
    have he : b = c := by
      apply Subtype.ext
      refine Prod.ext ?_ hbct
      funext i
      fin_cases i
      exact hb.trans hc.symm
    subst c
    rfl
  · obtain ⟨Γ, hΓ, v, hv⟩ := VFValued.exists_valuation_predV (M := M)
    letI := hΓ
    obtain ⟨he, _⟩ := U.unary_inverse_fibre v hv hB b hb
    let a := vfAt (U.inverseMap b).val 0
    let ρ : Section3.Balls.Radius Γ := ↑(OrderDual.toDual (v (vfAt b.val 0)))
    have hrad : v (vfAt b.val 0) ≠ 0 := (map_ne_zero v).mpr hb
    have hmem (x : VF (M := M)) (hx : x ∈ Section3.Balls.openDisc v a ρ) :
        unaryPoint x (U.inverseMap b).val.2 ∈ U.inverseFibre b := by
      rw [he]
      refine ⟨?_, rfl⟩
      change v (x - a) < v (vfAt b.val 0)
      simpa only [Section3.Balls.openDisc, ρ, OrderDual.ofDual_toDual, if_neg hrad,
        Set.mem_ofPred_eq] using hx
    have hroot : ∀ r ∈ p.roots, r ∉ Section3.Balls.openDisc v a ρ := by
      intro r hr hrd
      obtain ⟨a₀, ha₀, hrv⟩ := hmem r hrd
      have hval : vfAt a₀.val 0 = r := congrArg (fun q : Point (M := M) 1 0 => vfAt q 0) ha₀
      have hpr : p.eval r = 0 := by
        by_cases hp : p = 0
        · simp [hp]
        · exact (Polynomial.mem_roots hp).mp hr
      have hzero := hz a₀ (by rwa [hval])
      have hrb := ((sameRV_iff _ _).mp hrv).1 0
      change rv (vfAt (U.toMap a₀).val 0) = rv (vfAt b.val 0) at hrb
      rw [hzero] at hrb
      exact hb ((rv_eq_zero_iff _).mp hrb.symm)
    have hcF : (U.inverseMap c).val ∈ U.inverseFibre b :=
      ⟨U.inverseMap c, rfl, by rw [U.apply_inverse]; exact hbc.symm⟩
    rw [he] at hcF
    have hy : vfAt (U.inverseMap c).val 0 ∈ Section3.Balls.openDisc v a ρ := by
      simpa only [Section3.Balls.openDisc, ρ, OrderDual.ofDual_toDual, if_neg hrad,
        Set.mem_ofPred_eq] using hcF.1
    exact Subtype.ext (Section3.polynomial_rv_constant_openDisc v hv p a ρ hroot _ _
      (Section3.Balls.centre_mem_openDisc v a ρ) hy)

def polynomialCode (p : Polynomial (VF (M := M))) (z : Fin 1 ⊕ Fin m → M) : M :=
  @Term.realize LRV M (CanonicalStructure.normalize (M := M)) (Fin (p.natDegree + 1) ⊕ Fin 1)
    (Sum.elim (fun i => (p.coeff i.val).val) ![z (.inl 0)])
    (Section3.PolynomialRoots.term (p.natDegree + 1))

theorem polynomialCode_eq (p : Polynomial (VF (M := M))) (z : Fin 1 ⊕ Fin m → M)
    (x : VF (M := M)) (hx : z (.inl 0) = x.val) : polynomialCode p z = (p.eval x).val := by
  unfold polynomialCode
  rw [hx]
  rw [CanonicalStructure.term_normalize hM (fun _ => .vf) (fun _ => .vf)
    (fun i : Fin (p.natDegree + 1) => (p.coeff i.val).val) ![x.val]
    (fun i => (p.coeff i.val).property) (by intro i; fin_cases i; exact x.property)
    _ (Section3.PolynomialRoots.term_sorted _)]
  rw [Section3.PolynomialRoots.term_realize]
  apply congrArg Subtype.val
  symm
  change p.eval₂ (RingHom.id _) x = _
  rw [Polynomial.eval₂_eq_sum_range]
  exact (Fin.sum_univ_eq_sum_range (fun i : ℕ => p.coeff i * x ^ i) (p.natDegree + 1)).symm

theorem polynomialCode_definable (p : Polynomial (VF (M := M)))
    (hc : ∀ i : ℕ, (p.coeff i).val ∈ S) : RawFun S (Fin 1 ⊕ Fin m) (polynomialCode p) := by
  let k := p.natDegree + 1
  let cs : Fin k → M := fun i => (p.coeff i.val).val
  let g : (Fin 1 ⊕ Fin m → M) → Fin k ⊕ Fin 1 → M :=
    fun z => Sum.elim cs ![z (.inl 0)]
  let t := Section3.PolynomialRoots.term k
  let N := @CanonicalStructure.normalize M sM
  letI := N
  have ht : (∅ : Set M).DefinableFun LRV (fun z => @Term.realize LRV M N _ z t) :=
    t.definableFun_realize (M := M)
  have hg : ∀ i, @Set.DefinableFun M LRV N (Fin 1 ⊕ Fin m) S (fun z => g z i) := by
    intro i
    cases i with
    | inl i => exact LRV.definableFun_const _ (hc i.val)
    | inr i =>
      fin_cases i
      exact Set.DefinableFun.proj LRV
  exact @Set.DefinableFun.comp M LRV N (Fin k ⊕ Fin 1) (Fin 1 ⊕ Fin m) S _ inferInstance g hg ht.of_empty

theorem zeroCode_definable (S : Set M) {α : Type} : RawFun (M := M) S α (fun _ => iVFZero) := by
  let N := @CanonicalStructure.normalize M sM
  have he : @Structure.funMap LRV M N 0 Fn.vfZero Fin.elim0 = @iVFZero M sM :=
    @CanonicalStructure.normalize_fun M sM 0 Fn.vfZero Fin.elim0 (fun i => i.elim0)
  have h := @DefinableConstants.function_symbol M LRV N S 0 Fn.vfZero Fin.elim0 (fun i => i.elim0)
  rw [he] at h
  exact @DefinableConstants.constant M LRV N S _ h α

def polynomialZeroSet (A : DefSet (M := M) S 1 m) (p : Polynomial (VF (M := M)))
    (hc : ∀ i : ℕ, (p.coeff i).val ∈ S) : DefSet (M := M) S 1 m :=
  PresentedSet.mk {a | a ∈ carrier A ∧ p.eval (vfAt a 0) = 0} (by
    have hf := polynomialCode_definable (m := m) p hc
    have hzero := zeroCode_definable (M := M) (α := Fin 1 ⊕ Fin m) S
    have hz : @Set.Definable M S LRV (CanonicalStructure.normalize (M := M)) (Fin 1 ⊕ Fin m)
        {z | polynomialCode p z = iVFZero} := by
      letI := @CanonicalStructure.normalize M sM
      exact hf.ofPred_eq hzero
    have h := @Set.Definable.inter M S LRV (CanonicalStructure.normalize (M := M))
      (Fin 1 ⊕ Fin m) _ _ (setDefinable A) hz
    change @Set.Definable M S LRV (CanonicalStructure.normalize (M := M)) (Fin 1 ⊕ Fin m)
      {z | ∃ hd : z ∈ pDomain (pointSpace 1 m),
        pDecode (pointSpace 1 m) ⟨z, hd⟩ ∈ carrier A ∧
          p.eval (vfAt (pDecode (pointSpace 1 m) ⟨z, hd⟩) 0) = 0}
    convert h using 1
    ext z
    constructor
    · rintro ⟨hd, ha, hp⟩
      refine ⟨⟨hd, ha⟩, ?_⟩
      change polynomialCode p z = iVFZero
      rw [polynomialCode_eq p z (vfAt (pDecode (pointSpace 1 m) ⟨z, hd⟩) 0) rfl]
      exact congrArg Subtype.val hp
    · rintro ⟨⟨hd, ha⟩, hp⟩
      refine ⟨hd, ha, ?_⟩
      change polynomialCode p z = iVFZero at hp
      apply Subtype.ext
      rwa [polynomialCode_eq p z (vfAt (pDecode (pointSpace 1 m) ⟨z, hd⟩) 0) rfl] at hp)

theorem polynomialZeroSet_finite (A : DefSet (M := M) S 1 0) (p : Polynomial (VF (M := M)))
    (hc : ∀ i : ℕ, (p.coeff i).val ∈ S) (hp : p ≠ 0) : (carrier (polynomialZeroSet A p hc)).Finite := by
  have hf : {x : VF (M := M) | p.eval x = 0}.Finite := Polynomial.finite_setOfPred_isRoot hp
  have hi : Function.Injective (fun q : Point (M := M) 1 0 => vfAt q 0) := by
    intro q r he
    refine Prod.ext ?_ (Subsingleton.elim _ _)
    funext i
    fin_cases i
    exact he
  exact (hf.preimage hi.injOn).subset (fun _ h => h.2)

def polynomialRoots (A : DefSet (M := M) S 1 0) (p : Polynomial (VF (M := M)))
    (hc : ∀ i : ℕ, (p.coeff i).val ∈ S) (hp : p ≠ 0) : FiniteRootSet A :=
  ⟨polynomialZeroSet A p hc, polynomialZeroSet_finite A p hc hp, fun _ h => h.1⟩

/-- The unary case of Theorem 5.4, including an arbitrary initial special
bijection. The polynomial has coefficients in the original named base.
The initial domain may be any unary RV-pullback, with no extra RV labels. -/
theorem theorem_5_4_unary (h00 : M ⊨ Axioms.ACVF00)
    {A₀ : DefSet (M := M) S 1 0} {A : DefSet (M := M) S 1 m}
    (hA₀ : IsRVPullback (carrier A₀)) (τ : SpecialBijection A₀ A)
    (p : Polynomial (VF (M := M))) (hc : ∀ i : ℕ, (p.coeff i).val ∈ S) :
    ∃ r : ℕ, ∃ B : DefSet (M := M) S 1 r, ∃ T : SpecialBijection A B,
      IsRVPullback (carrier B) ∧
        ScalarContractible (fun b : B => p.eval (vfAt (τ.inverseMap (T.inverseMap b)).val 0)) := by
  by_cases hp : p = 0
  · refine ⟨m, A, SpecialBijection.refl A, τ.preserves_pullback hA₀, ?_⟩
    intro b c _
    simp only [hp, Polynomial.eval_zero]
  · let R₀ := polynomialRoots A₀ p hc hp
    let R := R₀.push τ.toMap
    obtain ⟨r, B, T, halt, hz⟩ := R.centralize_after h00 τ
    let U : SpecialBijection A₀ B := ⟨τ.chain.append T.chain, halt⟩
    have hmap : U.toMap = Map.comp T.toMap τ.toMap := τ.chain.append_toMap T.chain
    have hB : IsRVPullback (carrier B) := U.preserves_pullback hA₀
    have hzero : ∀ a : A₀, p.eval (vfAt a.val 0) = 0 → vfAt (U.toMap a).val 0 = 0 := by
      intro a ha
      rw [hmap]
      apply hz (τ.toMap a)
      apply (R.mem_points _).mp
      apply (R₀.mem_push_points τ.toMap _).mpr
      exact ⟨a, (R₀.mem_points _).mpr ⟨a.property, ha⟩, rfl⟩
    have hi (b : B) : U.inverseMap b = τ.inverseMap (T.inverseMap b) := by
      apply U.bijective.1
      rw [U.apply_inverse, hmap]
      change b = T.toMap (τ.toMap (τ.inverseMap (T.inverseMap b)))
      rw [τ.apply_inverse, T.apply_inverse]
    refine ⟨r, B, T, hB, ?_⟩
    have hh := polynomial_contractible_of_zero_roots U hB p hzero
    intro b c he
    simpa only [hi] using hh b c he

end SpecialTransformations.Section5

#check @SpecialTransformations.Section5.theorem_5_4_unary
#print axioms SpecialTransformations.Section5.theorem_5_4_unary
