import Section5.CoordinateLift

/-!
# Finite root families with complementary VF coordinates

The vertical hull uses equality of the complementary coordinates. Its
being an RV-pullback is a separate preparation condition, rather than an
implicit consequence of finite fibres. Once prepared, its barycentre is
a valid focus in the full mixed space.
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
variable {S : Set M} {n m : ℕ}

def pointValues (p : Point (M := M) n m) : Fin n ⊕ Fin m → M :=
  Sum.elim (fun i => (p.1 i).val) (fun i => (p.2 i).val)

theorem pointValues_domain (p : Point (M := M) n m) :
    pointValues p ∈ pDomain (pointSpace n m) := ⟨fun i => (p.1 i).property, fun i => (p.2 i).property⟩

theorem pointValues_decode (c : pDomain (pointSpace (M := M) n m)) :
    pointValues (pDecode (pointSpace n m) c) = c.val := by
  funext i
  cases i <;> rfl

theorem decode_pointValues (p : Point (M := M) n m) :
    pDecode (pointSpace n m) ⟨pointValues p, pointValues_domain p⟩ = p := rfl

theorem point_code_iff (A : DefSet (M := M) S n m) (z : Fin n ⊕ Fin m → M) :
    z ∈ @DefinableGeometry.Space.preimage LRV M (CanonicalStructure.normalize (M := M))
      (pointSpace n m) (carrier A) ↔
      ∃ p : Point (M := M) n m, pointValues p = z ∧ p ∈ carrier A := by
  constructor
  · rintro ⟨hz, ha⟩
    exact ⟨pDecode (pointSpace n m) ⟨z, hz⟩, pointValues_decode _, ha⟩
  · rintro ⟨p, rfl, hp⟩
    exact ⟨pointValues_domain p, hp⟩

theorem mean_definable_index {ι : Type} [Fintype ι] (h00 : M ⊨ Axioms.ACVF00)
    (F : (ι → M) → Finset (VF (M := M)))
    (hF : @Set.Definable M S LRV (CanonicalStructure.normalize (M := M)) (ι ⊕ Fin 1)
      {z | ∃ x ∈ F (z ∘ Sum.inl), x.val = z (.inr 0)})
    (N : ℕ) (hN : ∀ z, (F z).card ≤ N) :
    RawFun S ι (fun z => (Section3.Barycentre.mean (F z)).val) := by
  let e := Fintype.equivFin ι
  let G (z : Fin (Fintype.card ι) → M) := F (z ∘ e)
  have hG : @Section3.RawClosure.Tuple.RelationDefinable M (CanonicalStructure.normalize (M := M))
      (Fintype.card ι) S
      (@Section3.Barycentre.finiteFibreRelation M (CanonicalStructure.normalize (M := M)) _ G) := by
    exact @Set.Definable.preimage_comp M S LRV (CanonicalStructure.normalize (M := M))
      (ι ⊕ Fin 1) (Fin (Fintype.card ι) ⊕ Fin 1) (Sum.map e id) _ hF
  have hf := mean_definable_normalized h00 S G hG N (fun z => hN (z ∘ e))
  have hh := @Set.DefinableFun.comp M LRV (CanonicalStructure.normalize (M := M))
    (Fin (Fintype.card ι)) ι S _ inferInstance (fun z => z ∘ e.symm)
    (fun i => rawProj S (e.symm i)) hf
  simpa only [G, Function.comp_assoc, e.symm_comp_self, Function.comp_id] using hh

def headKeyProjection : Fin (1 + m) → Fin ((n + 1) + m) :=
  Fin.addCases (fun _ : Fin 1 => Fin.castAdd m (0 : Fin (n + 1))) (Fin.natAdd (n + 1))

def headKeyMap (A : DefSet (M := M) S (n + 1) m) :
    Map A (PresentedSet.univ (pointSpace n (1 + m)) S) :=
  Map.comp (dropHeadMap (headKeyProjection (n := n) (m := m)) (canonicalImage A))
    (SpecialBijection.canonical A).toMap

theorem headKeyMap_apply (A : DefSet (M := M) S (n + 1) m) (a : A) :
    (headKeyMap A a).val = headKey a.val := by
  refine Prod.ext rfl ?_
  funext i
  cases i using Fin.addCases with
  | left i =>
    fin_cases i
    exact canonical_new a.val 0
  | right i =>
    change (canonical a.val).2 (headKeyProjection (n := n) (Fin.natAdd 1 i)) =
      (headKey a.val).2 (Fin.natAdd 1 i)
    simpa only [headKeyProjection, Fin.addCases_right, headKey, Fin.append_right] using canonical_old a.val i

def insertHead (x : VF (M := M)) (p : Point (M := M) n m) : Point (M := M) (n + 1) m :=
  (Fin.cons x p.1, p.2)

@[simp] theorem dropHead_insertHead (x : VF (M := M)) (p : Point (M := M) n m) :
    dropHead id (insertHead x p) = p := by
  refine Prod.ext ?_ rfl
  funext i
  rfl

@[simp] theorem insertHead_dropHead (p : Point (M := M) (n + 1) m) :
    insertHead (vfAt p 0) (dropHead id p) = p := by
  refine Prod.ext ?_ rfl
  funext i
  cases i using Fin.cases <;> rfl

theorem dropHead_erase_zero (p : Point (M := M) (n + 1) m) :
    dropHead id (erase 0 p) = dropHead id p := dropHead_replace_zero id p 0

structure VerticalRootFamily (A : DefSet (M := M) S (n + 1) m) where
  set : DefSet (M := M) S (n + 1) m
  subset : carrier set ⊆ carrier A
  finite : ∀ p : Point (M := M) n m, {x : VF (M := M) | insertHead x p ∈ carrier set}.Finite

namespace VerticalRootFamily

variable {A : DefSet (M := M) S (n + 1) m}

def fibre (R : VerticalRootFamily A) (p : Point (M := M) n m) : Finset (VF (M := M)) :=
  (R.finite p).toFinset

@[simp] theorem mem_fibre (R : VerticalRootFamily A) (p : Point (M := M) n m) (x : VF (M := M)) :
    x ∈ R.fibre p ↔ insertHead x p ∈ carrier R.set := Set.Finite.mem_toFinset _

def verticalHull (R : VerticalRootFamily A) : Set (Point (M := M) (n + 1) m) :=
  {p | ∃ x ∈ R.fibre (dropHead id p), rv x = rv (vfAt p 0)}

theorem subset_verticalHull (R : VerticalRootFamily A) : carrier R.set ⊆ R.verticalHull := by
  intro p hp
  refine ⟨vfAt p 0, (R.mem_fibre _ _).mpr ?_, rfl⟩
  rwa [insertHead_dropHead]

theorem verticalHull_subset_hull (R : VerticalRootFamily A) : R.verticalHull ⊆ hull (carrier A) := by
  rintro p ⟨x, hx, he⟩
  refine ⟨insertHead x (dropHead id p), R.subset ((R.mem_fibre _ _).mp hx), ?_⟩
  apply (sameRV_iff _ _).mpr
  refine ⟨?_, rfl⟩
  intro i
  cases i using Fin.cases with
  | zero => exact he
  | succ i => rfl

theorem verticalHull_definable (R : VerticalRootFamily A) :
    SetDefinable (pointSpace (n + 1) m) S R.verticalHull := by
  have hh := Map.definable_preimage
    (headKeyMap (PresentedSet.univ (pointSpace (n + 1) m) S))
    (Map.definable_image (headKeyMap R.set))
  have he : R.verticalHull =
      {p | ∃ a : PresentedSet.univ (pointSpace (M := M) (n + 1) m) S, a.val = p ∧
        (headKeyMap _ a).val ∈ Set.range (fun r : R.set => (headKeyMap R.set r).val)} := by
    ext p
    constructor
    · rintro ⟨x, hx, he⟩
      refine ⟨⟨p, Set.mem_univ _⟩, rfl, ⟨⟨insertHead x (dropHead id p), (R.mem_fibre _ _).mp hx⟩, ?_⟩⟩
      calc
        _ = headKey (insertHead x (dropHead id p)) := headKeyMap_apply _ _
        _ = headKey p := by
          refine Prod.ext rfl ?_
          change Fin.append (fun _ : Fin 1 => rv x) p.2 = Fin.append (fun _ : Fin 1 => rv (vfAt p 0)) p.2
          rw [he]
        _ = _ := (headKeyMap_apply
          (PresentedSet.univ (pointSpace (M := M) (n + 1) m) S) ⟨p, Set.mem_univ _⟩).symm
    · rintro ⟨a, rfl, r, hr⟩
      have hr : headKey r.val = headKey a.val :=
        (headKeyMap_apply R.set r).symm.trans (hr.trans (headKeyMap_apply _ a))
      have htail := congrArg Prod.fst hr
      have hlabels : r.val.2 = a.val.2 := by
        funext i
        simpa only [headKey, Fin.append_right] using
          congrArg (fun q : Point (M := M) n (1 + m) => q.2 (Fin.natAdd 1 i)) hr
      have hhead : rv (vfAt r.val 0) = rv (vfAt a.val 0) :=
        congrArg (fun q : Point (M := M) n (1 + m) => q.2 (Fin.castAdd m (0 : Fin 1))) hr
      refine ⟨vfAt r.val 0, (R.mem_fibre _ _).mpr ?_, hhead⟩
      have hb : dropHead id r.val = dropHead id a.val := Prod.ext htail hlabels
      rw [← hb, insertHead_dropHead]
      exact r.property
  exact (congrArg (fun Z : Set (Point (M := M) (n + 1) m) =>
    SetDefinable (pointSpace (n + 1) m) S Z) he).mpr hh

def Bound (R : VerticalRootFamily A) (d : ℕ) : Prop :=
  ∀ p, (∃ x ∈ R.fibre p, x ≠ 0) → (R.fibre p).card ≤ d

theorem card_bound (R : VerticalRootFamily A) (d : ℕ) (hd : R.Bound d) (p : Point (M := M) n m) :
    (R.fibre p).card ≤ d + 1 := by
  by_cases hn : ∃ x ∈ R.fibre p, x ≠ 0
  · exact (hd p hn).trans (Nat.le_succ d)
  · have hs : R.fibre p ⊆ {0} := by
      intro x hx
      apply Finset.mem_singleton.mpr
      by_contra hx0
      exact hn ⟨x, hx, hx0⟩
    have hh := Finset.card_le_card hs
    simp only [Finset.card_singleton] at hh
    omega

theorem bound_zero (R : VerticalRootFamily A) (hd : R.Bound 0) :
    ∀ p ∈ carrier R.set, vfAt p 0 = 0 := by
  intro p hp
  have hx : vfAt p 0 ∈ R.fibre (dropHead id p) := (R.mem_fibre _ _).mpr (by rwa [insertHead_dropHead])
  by_contra hne
  have hh := hd (dropHead id p) ⟨vfAt p 0, hx, hne⟩
  have hc := Finset.card_pos.mpr ⟨vfAt p 0, hx⟩
  omega

/-- The mean is a focus after the vertical root locus has been prepared
in the complementary coordinates. No prepared-locus assertion is hidden
in the definition of finite root family. -/
def geometry (h00 : M ⊨ Axioms.ACVF00) (R : VerticalRootFamily A)
    (k : Fin m) (hTag : Tagged (carrier A) 0 k)
    (hHull : IsRVPullback R.verticalHull) : FocusGeometry (carrier A) 0 k where
  tagged := hTag
  locus := R.verticalHull
  locus_pullback := hHull
  locus_subset := R.verticalHull_subset_hull
  center p := Section3.Barycentre.mean (R.fibre (dropHead id p))
  independent p hp q hq he := by
    have hb := congrArg (dropHead (n := n) id) he
    rw [dropHead_erase_zero, dropHead_erase_zero] at hb
    rw [hb]
  center_mem := by
    intro p hp
    obtain ⟨x, hx, hxp⟩ := hp.2
    have hroots : ∀ y ∈ R.fibre (dropHead id p), rv y = rv x := by
      intro y hy
      have hyt := hTag _ (R.subset ((R.mem_fibre _ _).mp hy))
      have hxt := hTag _ (R.subset ((R.mem_fibre _ _).mp hx))
      exact hyt.symm.trans hxt
    have hm := mean_sameRV h00 (R.fibre (dropHead id p)) ⟨x, hx⟩ x hroots
    refine ⟨x, ?_, hm.symm⟩
    simpa only [dropHead_replace_zero] using hx

def rawFamily (R : VerticalRootFamily A) (z : Fin n ⊕ Fin m → M) : Finset (VF (M := M)) :=
  if hz : z ∈ pDomain (pointSpace n m) then R.fibre (pDecode (pointSpace n m) ⟨z, hz⟩) else ∅

theorem rawFamily_values (R : VerticalRootFamily A) (p : Point (M := M) n m) :
    R.rawFamily (pointValues p) = R.fibre p := by
  unfold rawFamily
  rw [dif_pos (pointValues_domain p), decode_pointValues]

theorem rawFamily_mem_iff (R : VerticalRootFamily A) (z : Fin n ⊕ Fin m → M) (x : VF (M := M)) :
    x ∈ R.rawFamily z ↔
      ∃ p : Point (M := M) n m, pointValues p = z ∧ insertHead x p ∈ carrier R.set := by
  constructor
  · intro hx
    by_cases hz : z ∈ pDomain (pointSpace n m)
    · exact ⟨pDecode (pointSpace n m) ⟨z, hz⟩, pointValues_decode _,
        (R.mem_fibre _ _).mp (by simpa only [rawFamily, dif_pos hz] using hx)⟩
    · have he : R.rawFamily z = ∅ := dif_neg hz
      rw [he] at hx
      exact (Finset.notMem_empty _ hx).elim
  · rintro ⟨p, rfl, hp⟩
    rw [R.rawFamily_values]
    exact (R.mem_fibre _ _).mpr hp

theorem rawFamily_bound (R : VerticalRootFamily A) (N : ℕ)
    (hN : ∀ p, (R.fibre p).card ≤ N) (z : Fin n ⊕ Fin m → M) : (R.rawFamily z).card ≤ N := by
  unfold rawFamily
  split_ifs
  · exact hN _
  · simp

theorem rawFamily_definable (R : VerticalRootFamily A) :
    @Set.Definable M S LRV (CanonicalStructure.normalize (M := M)) ((Fin n ⊕ Fin m) ⊕ Fin 1)
      {z | ∃ x ∈ R.rawFamily (z ∘ Sum.inl), x.val = z (.inr 0)} := by
  let σ : Fin (n + 1) ⊕ Fin m → (Fin n ⊕ Fin m) ⊕ Fin 1 :=
    Sum.elim (Fin.cases (Sum.inr 0) (fun i => Sum.inl (Sum.inl i))) (fun i => Sum.inl (Sum.inr i))
  have hh := @Set.Definable.preimage_comp M S LRV (CanonicalStructure.normalize (M := M))
    (Fin (n + 1) ⊕ Fin m) ((Fin n ⊕ Fin m) ⊕ Fin 1) σ _ (setDefinable R.set)
  convert hh using 1
  ext z
  rw [Set.mem_preimage, point_code_iff]
  constructor
  · rintro ⟨x, hx, he⟩
    obtain ⟨p, hp, hr⟩ := (R.rawFamily_mem_iff _ _).mp hx
    refine ⟨insertHead x p, ?_, hr⟩
    funext i
    cases i with
    | inl i =>
      cases i using Fin.cases with
      | zero => exact he
      | succ i => exact congrFun hp (.inl i)
    | inr i => exact congrFun hp (.inr i)
  · rintro ⟨p, hp, hr⟩
    refine ⟨vfAt p 0, (R.rawFamily_mem_iff _ _).mpr ⟨dropHead id p, ?_, ?_⟩, ?_⟩
    · funext i
      cases i with
      | inl i => exact congrFun hp (.inl i.succ)
      | inr i => exact congrFun hp (.inr i)
    · rwa [insertHead_dropHead]
    · exact congrFun hp (.inl 0)

def meanMap (R : VerticalRootFamily A) (h00 : M ⊨ Axioms.ACVF00) (N : ℕ)
    (hN : ∀ p, (R.fibre p).card ≤ N) (B : DefSet (M := M) S (n + 1) m) :
    Map B (PresentedSet.univ (Section4.vfSpace 1) S) :=
  Map.ofCodes B (fun p => ![Section3.Barycentre.mean (R.fibre (dropHead id p))])
    (fun z _ => (Section3.Barycentre.mean (R.rawFamily (z ∘ Sum.map Fin.succ id))).val)
    (by
      intro i
      have hf := mean_definable_index h00 R.rawFamily R.rawFamily_definable N (R.rawFamily_bound N hN)
      exact @Set.DefinableFun.comp M LRV (CanonicalStructure.normalize (M := M))
        (Fin n ⊕ Fin m) (Fin (n + 1) ⊕ Fin m) S _ inferInstance
        (fun z => z ∘ Sum.map Fin.succ id) (fun j => rawProj S (Sum.map Fin.succ id j)) hf)
    (by intro c i; exact (Section3.Barycentre.mean (R.rawFamily (c.val ∘ Sum.map Fin.succ id))).property)
    (by
      intro c
      funext i
      fin_cases i
      apply Subtype.ext
      exact congrArg (fun F => (Section3.Barycentre.mean F).val)
        (R.rawFamily_values (dropHead id (pDecode (pointSpace (n + 1) m) c))))

def focus (R : VerticalRootFamily A) (h00 : M ⊨ Axioms.ACVF00) (N : ℕ)
    (hN : ∀ p, (R.fibre p).card ≤ N) (k : Fin m) (hTag : Tagged (carrier A) 0 k)
    (hHull : IsRVPullback R.verticalHull) : Focus A 0 k :=
  let D := R.geometry h00 k hTag hHull
  { toFocusGeometry := D
    locus_definable := R.verticalHull_definable
    center_graph := by
      let C : DefSet (M := M) S (n + 1) m := PresentedSet.mk (carrier A ∩ D.locus)
        (SetDefinable.inter _ (setDefinable A) R.verticalHull_definable)
      apply RelationDefinable.congr _ _ (Map.graph_definable (R.meanMap h00 N hN C))
      intro p z
      constructor
      · rintro ⟨a, rfl, he⟩
        exact ⟨a.property, (congrFun he 0).symm⟩
      · rintro ⟨hp, he⟩
        refine ⟨⟨p, hp⟩, rfl, ?_⟩
        funext i
        fin_cases i
        exact he.symm }

end VerticalRootFamily

theorem finite_mean_child_bound (h00 : M ⊨ Axioms.ACVF00) (F U : Finset (VF (M := M)))
    (t : RV (M := M)) (d : ℕ) (hd : (∃ y ∈ F, y ≠ 0) → F.card ≤ d + 1)
    (hsub : U ⊆ (F.filter (fun y => rv (y - Section3.Barycentre.mean F) = t)).image
      (fun y => y - Section3.Barycentre.mean F))
    (hne : ∃ x ∈ U, x ≠ 0) : U.card ≤ d := by
  obtain ⟨x, hx, hx0⟩ := hne
  obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp (hsub hx)
  have hyF := (Finset.mem_filter.mp hy).1
  have htwo : 2 ≤ F.card := by
    by_contra hsmall
    have hcard : F.card ≤ 1 := by omega
    have he : F = {y} := Finset.eq_singleton_iff_unique_mem.mpr
      ⟨hyF, fun z hz => (Finset.card_le_one_iff.mp hcard) hz hyF⟩
    have hm : Section3.Barycentre.mean F = y := by simp [he, Section3.Barycentre.mean]
    apply hx0
    rw [← hyx, hm, sub_self]
  have hn : ∃ y ∈ F, y ≠ 0 := by
    by_contra! hz
    have hs : F ⊆ {0} := fun y hy => Finset.mem_singleton.mpr (hz y hy)
    have := Finset.card_le_card hs
    simp only [Finset.card_singleton] at this
    omega
  have hb := hd hn
  have hc : (F.filter (fun y => rv (y - Section3.Barycentre.mean F) = t)).card < F.card := by
    have he : F.filter (fun y => rv (y - Section3.Barycentre.mean F) = t) =
        F.filter (fun y => iRv (y - Section3.Barycentre.mean F).val = t.val) := by
      ext y
      simp only [Finset.mem_filter, Subtype.ext_iff]
      rfl
    rw [he]
    exact Section3.Barycentre.fibre_card_lt h00 F htwo t.val
  have hcard := (Finset.card_le_card hsub).trans Finset.card_image_le
  omega

end SpecialTransformations.Section5


/-!
# Strict root-count reduction with complementary VF coordinates

This is one actual centripetal/canonical step on a prepared vertical locus.
Preparing each subsequent locus remains a separate part of the dimensional
induction.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Section5.VerticalRootFamily

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n m l : ℕ}
variable {A : DefSet (M := M) S (n + 1) m} {B : DefSet (M := M) S (n + 1) l}

def imageSet (R : VerticalRootFamily A) (f : Map A B) : DefSet (M := M) S (n + 1) l :=
  Map.image (Map.comp f (Map.inclusion R.subset))

theorem mem_imageSet (R : VerticalRootFamily A) (f : Map A B) (b : Point (M := M) (n + 1) l) :
    b ∈ carrier (R.imageSet f) ↔ ∃ a : A, a.val ∈ carrier R.set ∧ (f a).val = b := by
  change (∃ r : R.set, (f ⟨r.val, R.subset r.property⟩).val = b) ↔ _
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨⟨r.val, R.subset r.property⟩, r.property, hr⟩
  · rintro ⟨a, ha, he⟩
    exact ⟨⟨a.val, ha⟩, he⟩

theorem imageSet_subset (R : VerticalRootFamily A) (f : Map A B) : carrier (R.imageSet f) ⊆ carrier B := by
  intro b hb
  obtain ⟨a, _, rfl⟩ := (R.mem_imageSet f b).mp hb
  exact (f a).property

def stepTarget (R : VerticalRootFamily A) (h00 : M ⊨ Axioms.ACVF00) (d : ℕ) (hd : R.Bound d)
    (k : Fin m) (hTag : Tagged (carrier A) 0 k) (hHull : IsRVPullback R.verticalHull) :=
  canonicalImage (R.focus h00 (d + 1) (R.card_bound d hd) k hTag hHull).etaImage

def step (R : VerticalRootFamily A) (h00 : M ⊨ Axioms.ACVF00) (d : ℕ) (hd : R.Bound d)
    (k : Fin m) (hTag : Tagged (carrier A) 0 k) (hHull : IsRVPullback R.verticalHull) :
    SpecialBijection A (R.stepTarget h00 d hd k hTag hHull) :=
  ⟨.cons (.centripetal (R.focus h00 (d + 1) (R.card_bound d hd) k hTag hHull))
    (.cons (.canonical _) (.nil _)), by decide, by decide, trivial⟩

def parentBase (q : Point (M := M) n ((n + 1) + m)) : Point (M := M) n m :=
  (q.1, fun i => q.2 (Fin.natAdd (n + 1) i))

theorem step_fibre_subset (R : VerticalRootFamily A) (h00 : M ⊨ Axioms.ACVF00)
    (d : ℕ) (hd : R.Bound d) (k : Fin m) (hTag : Tagged (carrier A) 0 k)
    (hHull : IsRVPullback R.verticalHull) (q : Point (M := M) n ((n + 1) + m)) (x : VF (M := M))
    (hx : insertHead x q ∈ carrier (R.imageSet (R.step h00 d hd k hTag hHull).toMap)) :
    x ∈ ((R.fibre (parentBase q)).filter
      (fun y => rv (y - Section3.Barycentre.mean (R.fibre (parentBase q))) =
        q.2 (Fin.castAdd m (0 : Fin (n + 1))))).image
      (fun y => y - Section3.Barycentre.mean (R.fibre (parentBase q))) := by
  obtain ⟨a, ha, he⟩ := (R.mem_imageSet _ _).mp hx
  let D := R.geometry h00 k hTag hHull
  change canonical (D.eta a.val) = insertHead x q at he
  have hac : a.val ∈ D.locus := R.subset_verticalHull ha
  have hbase : dropHead id a.val = parentBase q := by
    refine Prod.ext ?_ ?_
    · funext i
      have hh := congrArg (fun p : Point (M := M) (n + 1) ((n + 1) + m) => vfAt p i.succ) he
      exact (D.eta_other a.val i.succ (Fin.succ_ne_zero i)).symm.trans hh
    · funext i
      change a.val.2 i = q.2 (Fin.natAdd (n + 1) i)
      have hh := congrArg (fun p : Point (M := M) (n + 1) ((n + 1) + m) =>
        p.2 (Fin.natAdd (n + 1) i)) he
      simpa only [canonical_old, FocusGeometry.eta_labels, insertHead, parentBase, dropHead] using hh
  have heta : vfAt (D.eta a.val) 0 =
      vfAt a.val 0 - Section3.Barycentre.mean (R.fibre (dropHead id a.val)) := by
    rw [FocusGeometry.eta, if_pos hac]
    simp [replace, D, geometry, vfAt]
  have hv : vfAt a.val 0 - Section3.Barycentre.mean (R.fibre (dropHead id a.val)) = x := by
    have hh := congrArg (fun p : Point (M := M) (n + 1) ((n + 1) + m) => vfAt p 0) he
    change vfAt (D.eta a.val) 0 = x at hh
    rwa [heta] at hh
  refine Finset.mem_image.mpr ⟨vfAt a.val 0, Finset.mem_filter.mpr ⟨?_, ?_⟩, ?_⟩
  · apply (R.mem_fibre _ _).mpr
    rw [← hbase, insertHead_dropHead]
    exact ha
  · have hh := (canonical_new (D.eta a.val) (0 : Fin (n + 1))).symm.trans
      (congrArg (fun p : Point (M := M) (n + 1) ((n + 1) + m) => p.2 (Fin.castAdd m 0)) he)
    change rv (vfAt (D.eta a.val) 0) = q.2 (Fin.castAdd m 0) at hh
    rwa [heta, hbase] at hh
  · rwa [hbase] at hv

def stepFamily (R : VerticalRootFamily A) (h00 : M ⊨ Axioms.ACVF00)
    (d : ℕ) (hd : R.Bound d) (k : Fin m) (hTag : Tagged (carrier A) 0 k)
    (hHull : IsRVPullback R.verticalHull) : VerticalRootFamily (R.stepTarget h00 d hd k hTag hHull) where
  set := R.imageSet (R.step h00 d hd k hTag hHull).toMap
  subset := R.imageSet_subset _
  finite q := by
    let F := R.fibre (parentBase q)
    let C := F.filter (fun y => rv (y - Section3.Barycentre.mean F) = q.2 (Fin.castAdd m 0))
    exact (C.image (fun y => y - Section3.Barycentre.mean F)).finite_toSet.subset
      (fun x hx => R.step_fibre_subset h00 d hd k hTag hHull q x hx)

theorem step_bound (R : VerticalRootFamily A) (h00 : M ⊨ Axioms.ACVF00)
    (d : ℕ) (hd : R.Bound (d + 1)) (k : Fin m) (hTag : Tagged (carrier A) 0 k)
    (hHull : IsRVPullback R.verticalHull) :
    (R.stepFamily h00 (d + 1) hd k hTag hHull).Bound d := by
  intro q hn
  apply finite_mean_child_bound h00 (R.fibre (parentBase q))
    ((R.stepFamily h00 (d + 1) hd k hTag hHull).fibre q) (q.2 (Fin.castAdd m 0)) d
    (hd (parentBase q))
    (fun x hx => R.step_fibre_subset h00 (d + 1) hd k hTag hHull q x
      (((R.stepFamily h00 (d + 1) hd k hTag hHull).mem_fibre q x).mp hx)) hn

theorem step_tagged (R : VerticalRootFamily A) (h00 : M ⊨ Axioms.ACVF00)
    (d : ℕ) (hd : R.Bound d) (k : Fin m) (hTag : Tagged (carrier A) 0 k)
    (hHull : IsRVPullback R.verticalHull) :
    Tagged (carrier (R.stepTarget h00 d hd k hTag hHull)) 0 (Fin.castAdd m (0 : Fin (n + 1))) := by
  have he : carrier (R.stepTarget h00 d hd k hTag hHull) =
      canonical '' carrier (R.focus h00 (d + 1) (R.card_bound d hd) k hTag hHull).etaImage :=
    canonicalImage_carrier _
  exact (congrArg (fun Z : Set (Point (M := M) (n + 1) ((n + 1) + m)) =>
    Tagged Z 0 (Fin.castAdd m (0 : Fin (n + 1)))) he).mpr (canonical_tagged _ _)

end SpecialTransformations.Section5.VerticalRootFamily



/-!
# Coordinate-compatible transformation programs

Compatibility is a condition on the primitive focus dependencies. It does
not store an inverse-ball lemma or a contraction conclusion. Those facts
are derived from the actual transformations.
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

def TailEq (p q : Point (M := M) (n + 1) m) : Prop :=
  ∀ i : Fin n, vfAt p i.succ = vfAt q i.succ

theorem erase_idem {N : ℕ} (j : Fin N) (p : Point (M := M) N m) :
    erase j (erase j p) = erase j p := by
  refine Prod.ext ?_ rfl
  exact Function.update_idem _ _ _

namespace FocusGeometry

variable {A : Set (Point (M := M) (n + 1) m)} {j : Fin (n + 1)} {k : Fin m}

def HeadBlind (D : FocusGeometry A j k) : Prop :=
  ∀ p ∈ A ∩ D.locus, ∀ q ∈ A ∩ D.locus,
    erase 0 (erase j p) = erase 0 (erase j q) → D.center p = D.center q

theorem headBlind_zero (D : FocusGeometry A 0 k) : D.HeadBlind := by
  intro p hp q hq he
  apply D.independent p hp q hq
  simpa only [erase_idem] using he

theorem headBlind_sub (D : FocusGeometry A j k) (hD : D.HeadBlind)
    {p q : Point (M := M) (n + 1) m} (hp : p ∈ A) (hq : q ∈ A)
    (he : SameRV (D.eta p) (D.eta q)) (ht : TailEq (D.eta p) (D.eta q)) :
    TailEq p q ∧ vfAt (D.eta p) 0 - vfAt (D.eta q) 0 = vfAt p 0 - vfAt q 0 := by
  have hab := D.sameRV_of_eta hp hq he
  have hlabels := ((sameRV_iff _ _).mp hab).2
  have hd : erase 0 (erase j p) = erase 0 (erase j q) := by
    refine Prod.ext ?_ hlabels
    funext i
    cases i using Fin.cases with
    | zero => simp [erase, replace]
    | succ i =>
      by_cases hij : i.succ = j
      · have hj0 : j ≠ 0 := by rw [← hij]; exact Fin.succ_ne_zero i
        simp [erase, replace, hij, hj0]
      · have hv : p.1 i.succ = q.1 i.succ :=
          (D.eta_other p i.succ hij).symm.trans ((ht i).trans (D.eta_other q i.succ hij))
        simp [erase, replace, hij, Fin.succ_ne_zero, hv]
  by_cases hpc : p ∈ D.locus
  · have hqc := (mem_iff_sameRV D.locus_pullback hab).mp hpc
    have hc := hD p ⟨hp, hpc⟩ q ⟨hq, hqc⟩ hd
    refine ⟨?_, ?_⟩
    · intro i
      by_cases hij : i.succ = j
      · have hh : p.1 i.succ - D.center p = q.1 i.succ - D.center q := by
          simpa [eta, hpc, hqc, replace, hij, vfAt] using ht i
        rw [hc] at hh
        exact sub_left_inj.mp hh
      · exact (D.eta_other p i.succ hij).symm.trans ((ht i).trans (D.eta_other q i.succ hij))
    · by_cases hj : j = 0
      · subst j
        simp only [eta, if_pos hpc, if_pos hqc, vfAt, replace, Function.update_self, hc]
        abel
      · have h1 := D.eta_other p 0 (Ne.symm hj)
        have h2 := D.eta_other q 0 (Ne.symm hj)
        change (D.eta p).1 0 - (D.eta q).1 0 = p.1 0 - q.1 0
        rw [h1, h2]
  · have hqc : q ∉ D.locus := fun h => hpc ((mem_iff_sameRV D.locus_pullback hab).mpr h)
    have hep : D.eta p = p := by rw [eta, if_neg hpc]
    have heq : D.eta q = q := by rw [eta, if_neg hqc]
    exact ⟨by simpa only [hep, heq] using ht, by rw [hep, heq]⟩

end FocusGeometry

namespace Focus

variable {A : DefSet (M := M) S n m} {H : DefSet (M := M) S (n + 1) l}
variable {j : Fin n} {k : Fin m}

theorem lift_headBlind (D : Focus A j k) (ρ : Fin m → Fin l)
    (hHA : ∀ p ∈ carrier H, dropHead ρ p ∈ carrier A) :
    (D.lift ρ hHA).toFocusGeometry.HeadBlind := by
  intro p hp q hq he
  apply D.independent (dropHead ρ p) ⟨hHA p hp.1, hp.2.1⟩
    (dropHead ρ q) ⟨hHA q hq.1, hq.2.1⟩
  have hh := congrArg (dropHead ρ) he
  simpa only [erase, dropHead_replace_zero, dropHead_replace] using hh

end Focus

namespace Primitive

variable {A : DefSet (M := M) S (n + 1) m} {B : DefSet (M := M) S (n + 1) l}

def HeadCompatible : Primitive S (n + 1) A B → Prop
  | .canonical _ => True
  | .centripetal D => D.toFocusGeometry.HeadBlind

def HeadFixed (P : Primitive S (n + 1) A B) : Prop :=
  ∀ a : A, vfAt (P.toMap a).val 0 = vfAt a.val 0

theorem headCompatible_sub (P : Primitive S (n + 1) A B) (hP : P.HeadCompatible)
    (a b : A) (he : SameRV (P.toMap a).val (P.toMap b).val)
    (ht : TailEq (P.toMap a).val (P.toMap b).val) :
    TailEq a.val b.val ∧
      vfAt (P.toMap a).val 0 - vfAt (P.toMap b).val 0 = vfAt a.val 0 - vfAt b.val 0 := by
  cases P with
  | canonical A => exact ⟨ht, rfl⟩
  | centripetal D => exact D.toFocusGeometry.headBlind_sub hP a.property b.property he ht

theorem tail_forward (P : Primitive S (n + 1) A B) (hP : P.HeadCompatible) (hFix : P.HeadFixed)
    (a b : A) (he : SameRV a.val b.val) (ht : TailEq a.val b.val) :
    SameRV (P.toMap a).val (P.toMap b).val ∧ TailEq (P.toMap a).val (P.toMap b).val := by
  cases P with
  | canonical A => exact ⟨(canonical_sameRV_iff _ _).mpr he, ht⟩
  | @centripetal m j k D =>
    have hlabels := ((sameRV_iff _ _).mp he).2
    have htail : TailEq (D.toFocusGeometry.eta a.val) (D.toFocusGeometry.eta b.val) := by
      by_cases ha : a.val ∈ D.locus
      · have hb := (mem_iff_sameRV D.locus_pullback he).mp ha
        have herase : erase 0 (erase j a.val) = erase 0 (erase j b.val) := by
          refine Prod.ext ?_ hlabels
          funext i
          cases i using Fin.cases with
          | zero => simp [erase, replace]
          | succ i =>
            by_cases hij : i.succ = j
            · have hj0 : j ≠ 0 := by rw [← hij]; exact Fin.succ_ne_zero i
              simp [erase, replace, hij, hj0]
            · have hv := ht i
              change a.val.1 i.succ = b.val.1 i.succ at hv
              simp [erase, replace, hij, Fin.succ_ne_zero, hv]
        have hc := hP a.val ⟨a.property, ha⟩ b.val ⟨b.property, hb⟩ herase
        intro i
        have hv := ht i
        change a.val.1 i.succ = b.val.1 i.succ at hv
        by_cases hij : i.succ = j
        · simp [FocusGeometry.eta, ha, hb, replace, vfAt, hij, hc]
          exact (congrArg a.val.1 hij).symm.trans (hv.trans (congrArg b.val.1 hij))
        · exact (D.toFocusGeometry.eta_other a.val i.succ hij).trans
            (hv.trans (D.toFocusGeometry.eta_other b.val i.succ hij).symm)
      · have hb : b.val ∉ D.locus := fun h => ha ((mem_iff_sameRV D.locus_pullback he).mpr h)
        simpa only [FocusGeometry.eta, if_neg ha, if_neg hb] using ht
    refine ⟨(sameRV_iff _ _).mpr ⟨?_, ?_⟩, htail⟩
    · intro i
      cases i using Fin.cases with
      | zero =>
        exact (congrArg rv (hFix a)).trans
          ((((sameRV_iff _ _).mp he).1 0).trans (congrArg rv (hFix b)).symm)
      | succ i => exact congrArg rv (htail i)
    · exact (D.toFocusGeometry.eta_labels a.val).trans
        (hlabels.trans (D.toFocusGeometry.eta_labels b.val).symm)

end Primitive

namespace Chain

def HeadCompatible {a b : ℕ} {A : DefSet (M := M) S (n + 1) a} {B : DefSet (M := M) S (n + 1) b} :
    Chain S (n + 1) A B → Prop
  | .nil _ => True
  | .cons p tail => p.HeadCompatible ∧ tail.HeadCompatible

def TailProgram {a b : ℕ} {A : DefSet (M := M) S (n + 1) a} {B : DefSet (M := M) S (n + 1) b} :
    Chain S (n + 1) A B → Prop
  | .nil _ => True
  | .cons p tail => p.HeadCompatible ∧ p.HeadFixed ∧ tail.TailProgram

theorem TailProgram.headCompatible {A : DefSet (M := M) S (n + 1) m} {B : DefSet (M := M) S (n + 1) l}
    (T : Chain S (n + 1) A B) (hT : T.TailProgram) : T.HeadCompatible := by
  induction T with
  | nil _ => trivial
  | cons p tail ih => exact ⟨hT.1, ih hT.2.2⟩

theorem TailProgram.headFixed {A : DefSet (M := M) S (n + 1) m} {B : DefSet (M := M) S (n + 1) l}
    (T : Chain S (n + 1) A B) (hT : T.TailProgram) (a : A) :
    vfAt (T.toMap a).val 0 = vfAt a.val 0 := by
  induction T with
  | nil _ => rfl
  | cons p tail ih => exact (ih hT.2.2 (p.toMap a)).trans (hT.2.1 a)

theorem TailProgram.forward {A : DefSet (M := M) S (n + 1) m} {B : DefSet (M := M) S (n + 1) l}
    (T : Chain S (n + 1) A B) (hT : T.TailProgram) (a b : A)
    (he : SameRV a.val b.val) (ht : TailEq a.val b.val) :
    SameRV (T.toMap a).val (T.toMap b).val ∧ TailEq (T.toMap a).val (T.toMap b).val := by
  induction T with
  | nil _ => exact ⟨he, ht⟩
  | cons p tail ih =>
    obtain ⟨hp, ht'⟩ := p.tail_forward hT.1 hT.2.1 a b he ht
    exact ih hT.2.2 (p.toMap a) (p.toMap b) hp ht'

theorem TailProgram.replace_head {A : DefSet (M := M) S (n + 1) m} {B : DefSet (M := M) S (n + 1) l}
    (T : Chain S (n + 1) A B) (hT : T.TailProgram) (a : A) (x : VF (M := M))
    (hx : rv x = rv (vfAt a.val 0)) (hxA : replace 0 a.val x ∈ carrier A) :
    (T.toMap ⟨replace 0 a.val x, hxA⟩).val = replace 0 (T.toMap a).val x := by
  let b : A := ⟨replace 0 a.val x, hxA⟩
  have ht : TailEq b.val a.val := by
    intro i
    simp [b, TailEq, vfAt, replace, Fin.succ_ne_zero]
  have he : SameRV b.val a.val := (sameRV_replace 0 a.val x hx).symm
  obtain ⟨hh, htail⟩ := TailProgram.forward T hT b a he ht
  refine Prod.ext ?_ ?_
  · funext i
    cases i using Fin.cases with
    | zero => simpa only [b, vfAt, replace, Function.update_self] using TailProgram.headFixed T hT b
    | succ i =>
      change vfAt (T.toMap b).val i.succ = vfAt (replace 0 (T.toMap a).val x) i.succ
      exact (htail i).trans (by simp [replace, vfAt, Fin.succ_ne_zero])
  · exact ((sameRV_iff _ _).mp hh).2

theorem headCompatible_sub {A : DefSet (M := M) S (n + 1) m} {B : DefSet (M := M) S (n + 1) l}
    (T : Chain S (n + 1) A B) (hT : T.HeadCompatible) (a b : A)
    (he : SameRV (T.toMap a).val (T.toMap b).val)
    (ht : TailEq (T.toMap a).val (T.toMap b).val) :
    TailEq a.val b.val ∧
      vfAt (T.toMap a).val 0 - vfAt (T.toMap b).val 0 = vfAt a.val 0 - vfAt b.val 0 := by
  induction T with
  | nil _ => exact ⟨ht, rfl⟩
  | cons p tail ih =>
    have hmid := ih hT.2 (p.toMap a) (p.toMap b) he ht
    have hp := p.headCompatible_sub hT.1 a b (tail.sameRV_of _ _ he) hmid.1
    exact ⟨hp.1, hmid.2.trans hp.2⟩

end Chain

end SpecialTransformations.Section5

/-!
# Lifting transformations while retaining a VF coordinate

A lower-dimensional transformation is lifted using coordinate projections.
Every canonical step in the lift is the genuine full canonical step; the
extra RV coordinate is retained, and the projection is updated to skip it.
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

namespace Chain

variable {a b : ℕ} {A : DefSet (M := M) S n a} {B : DefSet (M := M) S n b}

/-- Lift a genuine alternating chain. Extra canonical RV labels are kept
in the output and skipped only by the comparison projection. -/
theorem lift_dropHead_compatible (T : Chain S n A B) :
    ∀ {l : ℕ} (H : DefSet (M := M) S (n + 1) l) (ρ : Fin a → Fin l)
      (hHA : ∀ p ∈ carrier H, dropHead ρ p ∈ carrier A)
      (previous : Option Bool), T.Alternating previous →
    ∃ r : ℕ, ∃ K : DefSet (M := M) S (n + 1) r, ∃ σ : Fin b → Fin r,
      ∃ W : Chain S (n + 1) H K, W.Alternating previous ∧ W.TailProgram ∧
        (∀ p : H, dropHead σ (W.toMap p).val =
          (T.toMap ⟨dropHead ρ p.val, hHA p.val p.property⟩).val) ∧
        ∀ p : H, vfAt (W.toMap p).val 0 = vfAt p.val 0 := by
  induction T with
  | nil A =>
    intro l H ρ hHA previous _
    exact ⟨l, H, ρ, .nil H, trivial, trivial, fun _ => rfl, fun _ => rfl⟩
  | @cons a' b' c' A' B' C' step tail ih =>
    cases step with
    | canonical =>
      intro l H ρ hHA previous hAlt
      let H' := canonicalImage H
      let ρ' := canonicalProjection (n := n) ρ
      have hsub : ∀ p ∈ carrier H', dropHead ρ' p ∈ carrier (canonicalImage A') := by
        intro p hp
        change p ∈ carrier (canonicalImage H) at hp
        rw [canonicalImage_carrier] at hp
        obtain ⟨q, hq, rfl⟩ := hp
        rw [dropHead_canonical]
        rw [canonicalImage_carrier]
        exact ⟨dropHead ρ q, hHA q hq, rfl⟩
      obtain ⟨r, K, σ, U, hU, hUc, hu, hh⟩ := ih H' ρ' hsub (some false) hAlt.2
      let W : Chain S (n + 1) H K := .cons (.canonical H) U
      refine ⟨r, K, σ, W, ⟨hAlt.1, hU⟩, ⟨trivial, (fun _ => rfl), hUc⟩, ?_, ?_⟩
      · intro p
        change dropHead σ (U.toMap ((SpecialBijection.canonical H).toMap p)).val = _
        rw [hu]
        have he : (⟨dropHead ρ' ((SpecialBijection.canonical H).toMap p).val,
            hsub _ ((SpecialBijection.canonical H).toMap p).property⟩ : canonicalImage A') =
            (SpecialBijection.canonical A').toMap ⟨dropHead ρ p.val, hHA _ p.property⟩ := by
          apply Subtype.ext
          exact dropHead_canonical ρ p.val
        rw [he]
        rfl
      · intro p
        exact hh ((SpecialBijection.canonical H).toMap p)
    | centripetal D =>
      intro l H ρ hHA previous hAlt
      let F := D.lift ρ hHA
      have hsub : ∀ p ∈ carrier F.etaImage, dropHead ρ p ∈ carrier D.etaImage := by
        intro p hp
        rw [Focus.etaImage_carrier] at hp
        obtain ⟨q, hq, rfl⟩ := hp
        rw [Focus.lift_eta D ρ hHA q hq]
        rw [Focus.etaImage_carrier]
        exact ⟨dropHead ρ q, hHA q hq, rfl⟩
      obtain ⟨r, K, σ, U, hU, hUc, hu, hh⟩ := ih F.etaImage ρ hsub (some true) hAlt.2
      let W : Chain S (n + 1) H K := .cons (.centripetal F) U
      refine ⟨r, K, σ, W, ⟨hAlt.1, hU⟩, ⟨D.lift_headBlind ρ hHA, (fun p => D.lift_eta_head ρ hHA p.val), hUc⟩, ?_, ?_⟩
      · intro p
        change dropHead σ (U.toMap ((SpecialBijection.centripetal F).toMap p)).val = _
        rw [hu]
        have he : (⟨dropHead ρ ((SpecialBijection.centripetal F).toMap p).val,
            hsub _ ((SpecialBijection.centripetal F).toMap p).property⟩ : D.etaImage) =
            (SpecialBijection.centripetal D).toMap ⟨dropHead ρ p.val, hHA _ p.property⟩ := by
          apply Subtype.ext
          exact D.lift_eta ρ hHA p.val p.property
        rw [he]
        rfl
      · intro p
        exact (hh ((SpecialBijection.centripetal F).toMap p)).trans (D.lift_eta_head ρ hHA p.val)

end Chain
end SpecialTransformations.Section5


/-!
# Inverse balls with fixed complementary coordinates

The compatibility of the primitive focus dependencies is sufficient for
the inverse of a head RV slice to be an ordinary open ball, with all other
original coordinates fixed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Section5.SpecialBijection

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n m l : ℕ}
variable {A : DefSet (M := M) S (n + 1) m} {B : DefSet (M := M) S (n + 1) l}

def inverseSlice (T : SpecialBijection A B) (b : B) : Set (Point (M := M) (n + 1) m) :=
  {p | ∃ a : A, a.val = p ∧ SameRV (T.toMap a).val b.val ∧ TailEq (T.toMap a).val b.val}

theorem compatible_inverse_pair (T : SpecialBijection A B) (hT : T.chain.HeadCompatible)
    (a b : B) (he : SameRV a.val b.val) (ht : TailEq a.val b.val) :
    TailEq (T.inverseMap a).val (T.inverseMap b).val ∧
      vfAt (T.inverseMap a).val 0 - vfAt (T.inverseMap b).val 0 = vfAt a.val 0 - vfAt b.val 0 := by
  have he' : SameRV (T.chain.toMap (T.inverseMap a)).val (T.chain.toMap (T.inverseMap b)).val := by
    change SameRV (T.toMap (T.inverseMap a)).val (T.toMap (T.inverseMap b)).val
    simpa only [T.apply_inverse] using he
  have ht' : TailEq (T.chain.toMap (T.inverseMap a)).val (T.chain.toMap (T.inverseMap b)).val := by
    change TailEq (T.toMap (T.inverseMap a)).val (T.toMap (T.inverseMap b)).val
    simpa only [T.apply_inverse] using ht
  have hh := T.chain.headCompatible_sub hT (T.inverseMap a) (T.inverseMap b) he' ht'
  refine ⟨hh.1, ?_⟩
  have hd := hh.2
  change vfAt (T.toMap (T.inverseMap a)).val 0 - vfAt (T.toMap (T.inverseMap b)).val 0 = _ at hd
  simpa only [T.apply_inverse] using hd.symm

theorem compatible_inverse_slice {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VF (M := M)) Γ)
    (hv : ∀ x y : VF (M := M), VFValued.predV x y ↔ v x ≤ v y)
    (T : SpecialBijection A B) (hT : T.chain.HeadCompatible)
    (hB : IsRVPullback (carrier B)) (b : B) (hb : vfAt b.val 0 ≠ 0) :
    T.inverseSlice b =
      {p | v (vfAt p 0 - vfAt (T.inverseMap b).val 0) < v (vfAt b.val 0) ∧
        TailEq p (T.inverseMap b).val ∧ p.2 = (T.inverseMap b).val.2} ∧
      T.inverseSlice b ⊆ {p | SameRV p (T.inverseMap b).val} := by
  have hlabel (a c : B) (he : a.val.2 = c.val.2) :
      (T.inverseMap a).val.2 = (T.inverseMap c).val.2 := by
    apply T.chain.labels_eq_of (T.inverseMap a) (T.inverseMap c)
    change (T.toMap (T.inverseMap a)).val.2 = (T.toMap (T.inverseMap c)).val.2
    simpa only [T.apply_inverse] using he
  have hclose (x : VF (M := M)) :
      rv x = rv (vfAt b.val 0) ↔ v (x - vfAt b.val 0) < v (vfAt b.val 0) := by
    rw [Subtype.ext_iff]
    change iRv x.val = iRv (vfAt b.val 0).val ↔ _
    rw [CanonicalRV.encoded_eq_iff_close x.property (vfAt b.val 0).property
      (fun he => hb (Subtype.ext he))]
    change (¬ VFValued.predV (vfAt b.val 0) (x - vfAt b.val 0)) ↔ _
    rw [hv, not_le]
  constructor
  · ext p
    constructor
    · rintro ⟨a, rfl, he, ht⟩
      have hh := T.compatible_inverse_pair hT (T.toMap a) b he ht
      rw [T.inverse_apply] at hh
      have hl := hlabel (T.toMap a) b ((sameRV_iff _ _).mp he).2
      rw [T.inverse_apply] at hl
      refine ⟨?_, hh.1, hl⟩
      rw [hh.2]
      exact (hclose _).mp (((sameRV_iff _ _).mp he).1 0)
    · rintro ⟨hpv, hptail, hplabels⟩
      let q : Point (M := M) (n + 1) l :=
        replace 0 b.val (vfAt p 0 - vfAt (T.inverseMap b).val 0 + vfAt b.val 0)
      have hq : SameRV q b.val := by
        apply (sameRV_replace 0 b.val _ ?_).symm
        apply (hclose _).mpr
        simpa only [add_sub_cancel_right] using hpv
      have htail : TailEq q b.val := by
        intro i
        simp [q, TailEq, vfAt, replace, Fin.succ_ne_zero]
      have hqB : q ∈ carrier B := (isRVPullback_iff _).mp hB b.val b.property q hq.symm
      let c : B := ⟨q, hqB⟩
      have hh := T.compatible_inverse_pair hT c b hq htail
      have hc : (T.inverseMap c).val = p := by
        refine Prod.ext ?_ ((hlabel c b rfl).trans hplabels.symm)
        funext i
        cases i using Fin.cases with
        | zero =>
          have hd := hh.2
          change vfAt (T.inverseMap c).val 0 - vfAt (T.inverseMap b).val 0 =
            vfAt p 0 - vfAt (T.inverseMap b).val 0 + vfAt b.val 0 - vfAt b.val 0 at hd
          have hd' : vfAt (T.inverseMap c).val 0 - vfAt (T.inverseMap b).val 0 =
              vfAt p 0 - vfAt (T.inverseMap b).val 0 := by simpa only [add_sub_cancel_right] using hd
          have hevf : vfAt (T.inverseMap c).val 0 = vfAt p 0 := sub_left_inj.mp hd'
          exact hevf
        | succ i => exact (hh.1 i).trans (hptail i).symm
      exact ⟨T.inverseMap c, hc, by simpa only [T.apply_inverse] using hq,
        by simpa only [T.apply_inverse] using htail⟩
  · rintro p ⟨a, rfl, he, _⟩
    have hh := T.inverse_contractible (T.toMap a) b he
    change SameRV a.val (T.inverseMap b).val
    simpa only [T.inverse_apply] using hh

end SpecialTransformations.Section5.SpecialBijection

namespace SpecialTransformations.Section5.VerticalRootFamily

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n m l : ℕ}
variable {A : DefSet (M := M) S (n + 1) m} {B : DefSet (M := M) S (n + 1) l}

/-- A tail program changes complementary coordinates and their labels,
while preserving the finite VF fibre bound exactly. -/
theorem tail_image_fibre_cover (R : VerticalRootFamily A) (T : SpecialBijection A B)
    (hT : T.chain.TailProgram) (k : Fin l) (hTag : Tagged (carrier B) 0 k)
    (q : Point (M := M) n l) :
    ∃ p : Point (M := M) n m,
      {x | insertHead x q ∈ carrier (R.imageSet T.toMap)} ⊆ (R.fibre p : Set (VF (M := M))) := by
  by_cases hn : ∃ x : VF (M := M), insertHead x q ∈ carrier (R.imageSet T.toMap)
  · obtain ⟨x₀, hx₀⟩ := hn
    obtain ⟨a, ha, hea⟩ := (R.mem_imageSet T.toMap _).mp hx₀
    refine ⟨dropHead id a.val, ?_⟩
    intro x hx
    obtain ⟨b, hb, heb⟩ := (R.mem_imageSet T.toMap _).mp hx
    have hlabels : (T.toMap b).val.2 = (T.toMap a).val.2 :=
      (congrArg Prod.snd heb).trans (congrArg Prod.snd hea).symm
    have htail : TailEq (T.toMap b).val (T.toMap a).val := by
      intro i
      exact (congrArg (fun p : Point (M := M) (n + 1) l => vfAt p i.succ) heb).trans
        (congrArg (fun p : Point (M := M) (n + 1) l => vfAt p i.succ) hea).symm
    have he : SameRV (T.toMap b).val (T.toMap a).val := by
      apply (sameRV_iff _ _).mpr
      refine ⟨?_, hlabels⟩
      intro i
      cases i using Fin.cases with
      | zero =>
        exact (hTag _ (T.toMap b).property).symm.trans
          ((congrFun hlabels k).trans (hTag _ (T.toMap a).property))
      | succ i => exact congrArg rv (htail i)
    have hsource := T.chain.headCompatible_sub (Chain.TailProgram.headCompatible T.chain hT) b a he htail
    have hbase : dropHead id b.val = dropHead id a.val :=
      Prod.ext (funext hsource.1) (T.chain.labels_eq_of b a hlabels)
    have hv : vfAt b.val 0 = x := by
      have hh := Chain.TailProgram.headFixed T.chain hT b
      have hx' := congrArg (fun p : Point (M := M) (n + 1) l => vfAt p 0) heb
      exact hh.symm.trans hx'
    apply (R.mem_fibre _ _).mpr
    rw [← hbase, ← hv, insertHead_dropHead]
    exact hb
  · refine ⟨(fun _ => 0, fun _ => rv 0), ?_⟩
    intro x hx
    exact (hn ⟨x, hx⟩).elim

def pushTail (R : VerticalRootFamily A) (T : SpecialBijection A B)
    (hT : T.chain.TailProgram) (k : Fin l) (hTag : Tagged (carrier B) 0 k) : VerticalRootFamily B where
  set := R.imageSet T.toMap
  subset := R.imageSet_subset _
  finite q := by
    obtain ⟨p, hp⟩ := R.tail_image_fibre_cover T hT k hTag q
    exact (R.fibre p).finite_toSet.subset hp

theorem pushTail_bound (R : VerticalRootFamily A) (T : SpecialBijection A B)
    (hT : T.chain.TailProgram) (k : Fin l) (hTag : Tagged (carrier B) 0 k)
    (d : ℕ) (hd : R.Bound d) : (R.pushTail T hT k hTag).Bound d := by
  intro q hn
  obtain ⟨p, hp⟩ := R.tail_image_fibre_cover T hT k hTag q
  have hsub : (R.pushTail T hT k hTag).fibre q ⊆ R.fibre p := by
    intro x hx
    exact hp (((R.pushTail T hT k hTag).mem_fibre q x).mp hx)
  obtain ⟨x, hx, hx0⟩ := hn
  exact (Finset.card_le_card hsub).trans (hd p ⟨x, hsub hx, hx0⟩)

end SpecialTransformations.Section5.VerticalRootFamily

namespace SpecialTransformations.Section5.Chain

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {N a b : ℕ}
variable {A : DefSet (M := M) S N a} {B : DefSet (M := M) S N b}

theorem lastKind_tagged_at (T : Chain S N A B) (j : Fin N) (previous : Option Bool)
    (hA : previous = some false → ∃ k : Fin a, Tagged (carrier A) j k)
    (hT : T.lastKind previous = some false) : ∃ k : Fin b, Tagged (carrier B) j k := by
  induction T generalizing previous with
  | nil A => exact hA hT
  | @cons a' b' c' A' B' C' p tail ih =>
    cases p with
    | canonical =>
      apply ih (some false) ?_ hT
      intro _
      refine ⟨Fin.castAdd _ j, ?_⟩
      have he := canonicalImage_carrier A'
      exact (congrArg (fun Z : Set (Point (M := M) N (N + _)) => Tagged Z j (Fin.castAdd _ j)) he).mpr
        (canonical_tagged _ _)
    | centripetal D => exact ih (some true) (by intro h; cases h) hT

def labelIndex {a b : ℕ} {A : DefSet (M := M) S N a} {B : DefSet (M := M) S N b} :
    Chain S N A B → Fin a → Fin b
  | .nil _, i => i
  | .cons (.canonical _) tail, i => tail.labelIndex (Fin.natAdd N i)
  | .cons (.centripetal _) tail, i => tail.labelIndex i

theorem labelIndex_apply (T : Chain S N A B) (x : A) (i : Fin a) :
    (T.toMap x).val.2 (T.labelIndex i) = x.val.2 i := by
  induction T with
  | nil _ => rfl
  | @cons a' b' c' A' B' C' p tail ih =>
    cases p with
    | canonical =>
      exact (ih ((SpecialBijection.canonical A').toMap x) (Fin.natAdd N i)).trans (canonical_old x.val i)
    | centripetal D =>
      exact (ih ((SpecialBijection.centripetal D).toMap x) i).trans
        (congrFun (D.toFocusGeometry.eta_labels x.val) i)

theorem TailProgram.tagged {n a b : ℕ} {A : DefSet (M := M) S (n + 1) a}
    {B : DefSet (M := M) S (n + 1) b} (T : Chain S (n + 1) A B) (hT : T.TailProgram)
    (k : Fin a) (hA : Tagged (carrier A) 0 k) : Tagged (carrier B) 0 (T.labelIndex k) := by
  intro p hp
  obtain ⟨x, hx⟩ := T.bijective.2 ⟨p, hp⟩
  have hout : (T.toMap x).val = p := congrArg Subtype.val hx
  change p.2 (T.labelIndex k) = rv (vfAt p 0)
  calc
    _ = (T.toMap x).val.2 (T.labelIndex k) :=
      congrArg (fun q : Point (M := M) (n + 1) b => q.2 (T.labelIndex k)) hout.symm
    _ = x.val.2 k := T.labelIndex_apply x k
    _ = rv (vfAt x.val 0) := hA _ x.property
    _ = rv (vfAt (T.toMap x).val 0) := (congrArg rv (TailProgram.headFixed T hT x)).symm
    _ = _ := congrArg (fun q : Point (M := M) (n + 1) b => rv (vfAt q 0)) hout

end SpecialTransformations.Section5.Chain

