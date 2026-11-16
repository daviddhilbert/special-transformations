module

public import Section5.RootConstruction
public import Section3.MixedRootFree

@[expose] public section

/-!
# Restricting special bijections to definable subsets

The locus is intersected with the hull of the smaller source. This retains
the original map on that source and keeps the locus condition in Definition
5.1, including when the smaller source is not itself an RV-pullback.
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

namespace RelationDefinable
abbrev inter := @DefinableGeometry.Space.RelationDefinable.inter LRV M (CanonicalStructure.normalize (M := M))
end RelationDefinable

namespace SetDefinable
abbrev left_relation := @DefinableGeometry.Space.Definable.left_relation LRV M (CanonicalStructure.normalize (M := M))
end SetDefinable

theorem isRVPullback_inter {n m : ℕ} {A B : Set (Point (M := M) n m)}
    (hA : IsRVPullback A) (hB : IsRVPullback B) : IsRVPullback (A ∩ B) := by
  apply (isRVPullback_iff _).mpr
  intro p hp q he
  exact ⟨(isRVPullback_iff _).mp hA p hp.1 q he, (isRVPullback_iff _).mp hB p hp.2 q he⟩

theorem sameRV_replace {n m : ℕ} (j : Fin n) (p : Point (M := M) n m) (x : VF (M := M))
    (hx : rv x = rv (p.1 j)) : SameRV p (replace j p x) := by
  apply (sameRV_iff _ _).mpr
  refine ⟨?_, rfl⟩
  intro i
  by_cases hi : i = j
  · subst i
    simpa [replace] using hx.symm
  · simp [replace, hi]

namespace Focus

variable {S : Set M} {n m : ℕ} {A B : DefSet (M := M) S n m} {j : Fin n} {k : Fin m}

def restrict (D : Focus A j k) (hBA : carrier B ⊆ carrier A) : Focus B j k where
  tagged p hp := D.tagged p (hBA hp)
  locus := D.locus ∩ hull (carrier B)
  locus_pullback := isRVPullback_inter D.locus_pullback (hull_idem _)
  locus_subset := Set.inter_subset_right
  center := D.center
  independent p hp q hq he := D.independent p ⟨hBA hp.1, hp.2.1⟩ q ⟨hBA hq.1, hq.2.1⟩ he
  center_mem := by
    intro p hp
    have hpc := D.center_mem p ⟨hBA hp.1, hp.2.1⟩
    have hr := D.toFocusGeometry.center_sameRV p ⟨hBA hp.1, hp.2.1⟩
    exact ⟨hpc, p, hp.1, sameRV_replace j p _ hr⟩
  locus_definable := SetDefinable.inter _ D.locus_definable (hull_definable B)
  center_graph := by
    have hb := SetDefinable.left_relation (pointSpace (M := M) n m) (Section4.vfSpace 1)
      (setDefinable B)
    have hh := RelationDefinable.inter _ _ D.center_graph hb
    apply RelationDefinable.congr _ _ hh
    intro p z
    constructor
    · rintro ⟨⟨⟨ha, hc⟩, hz⟩, hp⟩
      exact ⟨⟨hp, hc, subset_hull _ hp⟩, hz⟩
    · rintro ⟨⟨hp, hc, _⟩, hz⟩
      exact ⟨⟨⟨hBA hp, hc⟩, hz⟩, hp⟩

theorem restrict_eta (D : Focus A j k) (hBA : carrier B ⊆ carrier A)
    (p : Point (M := M) n m) (hp : p ∈ carrier B) :
    (D.restrict hBA).toFocusGeometry.eta p = D.toFocusGeometry.eta p := by
  have hh := subset_hull (carrier B) hp
  by_cases hc : p ∈ D.locus <;> simp [FocusGeometry.eta, restrict, hc, hh]

theorem restrict_image_subset (D : Focus A j k) (hBA : carrier B ⊆ carrier A) :
    carrier (D.restrict hBA).etaImage ⊆ carrier D.etaImage := by
  rw [etaImage_carrier, etaImage_carrier]
  rintro q ⟨p, hp, rfl⟩
  exact ⟨p, hBA hp, (D.restrict_eta hBA p hp).symm⟩

end Focus

namespace Primitive

variable {S : Set M} {n m l : ℕ} {A : DefSet (M := M) S n m} {C : DefSet (M := M) S n l}

def kind : Primitive S n A C → Bool
  | .canonical _ => false
  | .centripetal _ => true

theorem restrict (p : Primitive S n A C) (B : DefSet (M := M) S n m)
    (hBA : carrier B ⊆ carrier A) :
    ∃ D : DefSet (M := M) S n l, ∃ q : Primitive S n B D,
      q.kind = p.kind ∧ carrier D ⊆ carrier C ∧
        ∀ b : B, (q.toMap b).val = (p.toMap ⟨b.val, hBA b.property⟩).val := by
  cases p with
  | canonical A =>
    refine ⟨canonicalImage B, .canonical B, rfl, ?_, fun _ => rfl⟩
    rw [canonicalImage_carrier, canonicalImage_carrier]
    exact Set.image_mono hBA
  | centripetal F =>
    refine ⟨(F.restrict hBA).etaImage, .centripetal (F.restrict hBA), rfl,
      F.restrict_image_subset hBA, ?_⟩
    intro b
    exact F.restrict_eta hBA b.val b.property

end Primitive

namespace Chain

variable {S : Set M} {n m l k : ℕ}
variable {A : DefSet (M := M) S n m} {C : DefSet (M := M) S n l}

theorem cons_alternating_iff {D : DefSet (M := M) S n k} (p : Primitive S n A D)
    (T : Chain S n D C) (previous : Option Bool) :
    (Chain.cons p T).Alternating previous ↔
      previous ≠ some p.kind ∧ T.Alternating (some p.kind) := by
  cases p <;> rfl

theorem restrict (T : Chain S n A C) (B : DefSet (M := M) S n m)
    (hBA : carrier B ⊆ carrier A) (previous : Option Bool) (hT : T.Alternating previous) :
    ∃ D : DefSet (M := M) S n l, ∃ U : Chain S n B D,
      U.Alternating previous ∧ carrier D ⊆ carrier C ∧
        ∀ b : B, (U.toMap b).val = (T.toMap ⟨b.val, hBA b.property⟩).val := by
  induction T generalizing previous with
  | nil A => exact ⟨B, .nil B, trivial, hBA, fun _ => rfl⟩
  | cons p tail ih =>
    obtain ⟨hprev, htail⟩ := (cons_alternating_iff p tail previous).mp hT
    obtain ⟨B', q, hkind, hsub, hq⟩ := p.restrict B hBA
    obtain ⟨D, U, hU, hD, hu⟩ := ih B' hsub (some p.kind) htail
    refine ⟨D, .cons q U, ?_, hD, ?_⟩
    · apply (cons_alternating_iff q U previous).mpr
      simpa only [hkind] using (And.intro hprev hU)
    · intro b
      change (U.toMap (q.toMap b)).val = (tail.toMap (p.toMap ⟨b.val, hBA b.property⟩)).val
      have he : (⟨(q.toMap b).val, hsub (q.toMap b).property⟩ : _) =
          p.toMap ⟨b.val, hBA b.property⟩ := Subtype.ext (hq b)
      rw [hu (q.toMap b), he]

end Chain

namespace SpecialBijection

variable {S : Set M} {n m l : ℕ} {A : DefSet (M := M) S n m} {C : DefSet (M := M) S n l}

theorem restrict_at (T : SpecialBijection A C) (B : DefSet (M := M) S n m)
    (hBA : carrier B ⊆ carrier A) (previous : Option Bool) (hT : T.chain.Alternating previous) :
    ∃ D : DefSet (M := M) S n l, ∃ U : SpecialBijection B D,
      U.chain.Alternating previous ∧ carrier D ⊆ carrier C ∧
        carrier D = {c | ∃ b : B, (T.toMap ⟨b.val, hBA b.property⟩).val = c} ∧
          ∀ b : B, (U.toMap b).val = (T.toMap ⟨b.val, hBA b.property⟩).val := by
  obtain ⟨D, U, hU, hsub, hc⟩ := T.chain.restrict B hBA previous hT
  let V : SpecialBijection B D := ⟨U, U.alternating_none previous hU⟩
  refine ⟨D, V, hU, hsub, ?_, hc⟩
  ext c
  constructor
  · intro hd
    obtain ⟨b, hb⟩ := V.bijective.2 ⟨c, hd⟩
    exact ⟨b, (hc b).symm.trans (congrArg Subtype.val hb)⟩
  · rintro ⟨b, hb⟩
    have he : (V.toMap b).val = c := (hc b).trans hb
    exact he ▸ (V.toMap b).property

theorem restrict (T : SpecialBijection A C) (B : DefSet (M := M) S n m)
    (hBA : carrier B ⊆ carrier A) :
    ∃ D : DefSet (M := M) S n l, ∃ U : SpecialBijection B D,
      carrier D ⊆ carrier C ∧
        carrier D = {c | ∃ b : B, (T.toMap ⟨b.val, hBA b.property⟩).val = c} ∧
          ∀ b : B, (U.toMap b).val = (T.toMap ⟨b.val, hBA b.property⟩).val := by
  obtain ⟨D, U, _, hsub, himg, hcomm⟩ := T.restrict_at B hBA none T.alternating
  exact ⟨D, U, hsub, himg, hcomm⟩

end SpecialBijection
end SpecialTransformations.Section5

#check @SpecialTransformations.Section5.SpecialBijection.restrict
#print axioms SpecialTransformations.Section5.SpecialBijection.restrict


/-!
# Uniform root centering over arbitrary RV labels

Unlike a finite root set, the whole definable family may be infinite. The
VF fibre over each retained RV tuple is finite and the nonzero fibres have
an explicit common bound. The zero fibre contributes at most one point.
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
variable {S : Set M} {m : ℕ}

structure RootFamily (A : DefSet (M := M) S 1 m) where
  set : DefSet (M := M) S 1 m
  subset : carrier set ⊆ carrier A
  finite : ∀ t : Fin m → RV (M := M),
    {x : VF (M := M) | unaryPoint x t ∈ carrier set}.Finite

namespace RootFamily

variable {A : DefSet (M := M) S 1 m}

def fibre (R : RootFamily A) (t : Fin m → RV (M := M)) : Finset (VF (M := M)) :=
  (R.finite t).toFinset

@[simp] theorem mem_fibre (R : RootFamily A) (t : Fin m → RV (M := M)) (x : VF (M := M)) :
    x ∈ R.fibre t ↔ unaryPoint x t ∈ carrier R.set := Set.Finite.mem_toFinset _

def Bound (R : RootFamily A) (d : ℕ) : Prop :=
  ∀ t, (∃ x ∈ R.fibre t, x ≠ 0) → (R.fibre t).card ≤ d

theorem card_bound (R : RootFamily A) (d : ℕ) (hd : R.Bound d) (t : Fin m → RV (M := M)) :
    (R.fibre t).card ≤ d + 1 := by
  by_cases hn : ∃ x ∈ R.fibre t, x ≠ 0
  · exact (hd t hn).trans (Nat.le_succ d)
  · have hs : R.fibre t ⊆ {0} := by
      intro x hx
      apply Finset.mem_singleton.mpr
      by_contra hx0
      exact hn ⟨x, hx, hx0⟩
    have hh := Finset.card_le_card hs
    simp only [Finset.card_singleton] at hh
    omega

theorem bound_zero (R : RootFamily A) (hd : R.Bound 0) :
    ∀ a ∈ carrier R.set, vfAt a 0 = 0 := by
  intro a ha
  have hx : vfAt a 0 ∈ R.fibre a.2 := (R.mem_fibre _ _).mpr (by rwa [unaryPoint_eta])
  by_contra hne
  have := hd a.2 ⟨_, hx, hne⟩
  have := Finset.card_pos.mpr ⟨_, hx⟩
  omega

def geometry (R : RootFamily A) (h00 : M ⊨ Axioms.ACVF00) {k : Fin m}
    (hA : Tagged (carrier A) 0 k) : FocusGeometry (carrier A) 0 k where
  tagged := hA
  locus := hull (carrier R.set)
  locus_pullback := hull_idem _
  locus_subset := hull_mono R.subset
  center p := Section3.Barycentre.mean (R.fibre p.2)
  independent := by
    intro p hp q hq he
    have ht : p.2 = q.2 := by
      simpa [erase, replace] using congrArg (fun z : Point (M := M) 1 m => z.2) he
    rw [ht]
  center_mem := by
    intro p hp
    obtain ⟨q, hq, he⟩ := hp.2
    have hqp := (sameRV_iff q p).mp he
    have hne : (R.fibre p.2).Nonempty := by
      refine ⟨vfAt q 0, (R.mem_fibre _ _).mpr ?_⟩
      rw [← hqp.2, unaryPoint_eta]
      exact hq
    have hrv : ∀ x ∈ R.fibre p.2, rv x = rv (vfAt p 0) := by
      intro x hx
      have hxr := R.subset ((R.mem_fibre _ _).mp hx)
      exact (hA (unaryPoint x p.2) hxr).symm.trans (hA p hp.1)
    have hm := mean_sameRV h00 (R.fibre p.2) hne (vfAt p 0) hrv
    exact ⟨q, hq, he.trans (sameRV_replace 0 p _ hm)⟩

def rawFamily (R : RootFamily A) (z : Fin m → M) : Finset (VF (M := M)) :=
  if hz : ∀ i, iRV (z i) then R.fibre (fun i => ⟨z i, hz i⟩) else ∅

theorem rawFamily_labels (R : RootFamily A) (t : Fin m → RV (M := M)) :
    R.rawFamily (fun i => (t i).val) = R.fibre t := by
  unfold rawFamily
  rw [dif_pos (fun i => (t i).property)]

theorem rawFamily_bound (R : RootFamily A) (d : ℕ) (hd : R.Bound d) (z : Fin m → M) :
    (R.rawFamily z).card ≤ d + 1 := by
  unfold rawFamily
  split_ifs
  · exact R.card_bound d hd _
  · simp

theorem rawFamily_definable (R : RootFamily A) :
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
    · have hx' : x ∈ R.fibre (fun i => ⟨z (.inl i), ht i⟩) := by
        simpa only [rawFamily, Function.comp_apply, dif_pos ht] using hx
      exact ⟨x, (fun i => ⟨z (.inl i), ht i⟩), he, fun _ => rfl, (R.mem_fibre _ _).mp hx'⟩
    · have hh : R.rawFamily (z ∘ Sum.inl) = ∅ := dif_neg ht
      rw [hh] at hx
      exact (Finset.notMem_empty _ hx).elim
  · rintro ⟨x, t, hx, ht, hR⟩
    refine ⟨x, ?_, hx⟩
    have htv : (fun i => (t i).val) = z ∘ Sum.inl := funext ht
    rw [← htv, R.rawFamily_labels]
    exact (R.mem_fibre _ _).mpr hR

def meanMap (R : RootFamily A) (h00 : M ⊨ Axioms.ACVF00) (d : ℕ) (hd : R.Bound d)
    (B : DefSet (M := M) S 1 m) : Map B (PresentedSet.univ (Section4.vfSpace 1) S) :=
  Map.ofCodes (M := M) (sM := sM) (P := pointSpace 1 m) (Q := Section4.vfSpace 1) B
    (fun p => ![Section3.Barycentre.mean (R.fibre p.2)])
    (fun z _ => (Section3.Barycentre.mean (R.rawFamily (z ∘ Sum.inr))).val)
    (by
      intro i
      have hf := @mean_definable_normalized M sM hM h00 S m R.rawFamily R.rawFamily_definable
        (d + 1) (R.rawFamily_bound d hd)
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

def focus (R : RootFamily A) (h00 : M ⊨ Axioms.ACVF00) (d : ℕ) (hd : R.Bound d)
    {k : Fin m} (hA : Tagged (carrier A) 0 k) : Focus A 0 k :=
  let D := R.geometry h00 hA
  { toFocusGeometry := D
    locus_definable := hull_definable R.set
    center_graph := by
      let C : DefSet (M := M) S 1 m := PresentedSet.mk (carrier A ∩ D.locus)
        (SetDefinable.inter _ (setDefinable A) (hull_definable R.set))
      apply RelationDefinable.congr _ _ (Map.graph_definable (R.meanMap h00 d hd C))
      intro p z
      constructor
      · rintro ⟨a, rfl, he⟩
        exact ⟨a.property, (congrFun he 0).symm⟩
      · rintro ⟨hp, he⟩
        refine ⟨⟨p, hp⟩, rfl, ?_⟩
        funext i
        fin_cases i
        exact he.symm }

end RootFamily
end SpecialTransformations.Section5

namespace SpecialTransformations.Section5.RootFamily

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {m l : ℕ} {A : DefSet (M := M) S 1 m} {B : DefSet (M := M) S 1 l}

def imageSet (R : RootFamily A) (f : Map A B) : DefSet (M := M) S 1 l :=
  Map.image (Map.comp f (Map.inclusion R.subset))

theorem mem_imageSet (R : RootFamily A) (f : Map A B) (b : Point (M := M) 1 l) :
    b ∈ carrier (R.imageSet f) ↔ ∃ a : A, a.val ∈ carrier R.set ∧ (f a).val = b := by
  change (∃ r : R.set, (f ⟨r.val, R.subset r.property⟩).val = b) ↔ _
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨⟨r.val, R.subset r.property⟩, r.property, hr⟩
  · rintro ⟨a, ha, he⟩
    exact ⟨⟨a.val, ha⟩, he⟩

theorem imageSet_subset (R : RootFamily A) (f : Map A B) : carrier (R.imageSet f) ⊆ carrier B := by
  intro b hb
  obtain ⟨a, _, rfl⟩ := (R.mem_imageSet f b).mp hb
  exact (f a).property

def stepTarget (R : RootFamily A) (h00 : M ⊨ Axioms.ACVF00) (d : ℕ) (hd : R.Bound d)
    {k : Fin m} (hA : Tagged (carrier A) 0 k) := canonicalImage (R.focus h00 d hd hA).etaImage

def step (R : RootFamily A) (h00 : M ⊨ Axioms.ACVF00) (d : ℕ) (hd : R.Bound d)
    {k : Fin m} (hA : Tagged (carrier A) 0 k) : SpecialBijection A (R.stepTarget h00 d hd hA) :=
  ⟨.cons (.centripetal (R.focus h00 d hd hA)) (.cons (.canonical _) (.nil _)),
    by decide, by decide, trivial⟩

theorem step_fibre_subset (R : RootFamily A) (h00 : M ⊨ Axioms.ACVF00) (d : ℕ) (hd : R.Bound d)
    {k : Fin m} (hA : Tagged (carrier A) 0 k) (t : Fin (1 + m) → RV (M := M))
    (x : VF (M := M)) (hx : unaryPoint x t ∈ carrier (R.imageSet (R.step h00 d hd hA).toMap)) :
    x ∈ ((R.fibre (fun i => t (Fin.natAdd 1 i))).filter
      (fun y => rv (y - Section3.Barycentre.mean (R.fibre (fun i => t (Fin.natAdd 1 i)))) = t 0)).image
        (fun y => y - Section3.Barycentre.mean (R.fibre (fun i => t (Fin.natAdd 1 i)))) := by
  obtain ⟨a, ha, he⟩ := (R.mem_imageSet _ _).mp hx
  let D := R.geometry h00 hA
  change canonical (D.eta a.val) = unaryPoint x t at he
  have hac : a.val ∈ D.locus := by
    change a.val ∈ hull (carrier R.set)
    exact subset_hull _ ha
  have ht : a.val.2 = fun i => t (Fin.natAdd 1 i) := by
    funext i
    have hh := congrArg (fun q : Point (M := M) 1 (1 + m) => q.2 (Fin.natAdd 1 i)) he
    simpa only [canonical_old, FocusGeometry.eta_labels, unaryPoint] using hh
  have heta : vfAt (D.eta a.val) 0 =
      vfAt a.val 0 - Section3.Barycentre.mean (R.fibre a.val.2) := by
    rw [FocusGeometry.eta, if_pos hac]
    simp [replace, D, geometry, vfAt]
  have hv : vfAt a.val 0 - Section3.Barycentre.mean (R.fibre a.val.2) = x := by
    have hh := congrArg (fun q : Point (M := M) 1 (1 + m) => vfAt q 0) he
    change vfAt (D.eta a.val) 0 = x at hh
    rwa [heta] at hh
  refine Finset.mem_image.mpr ⟨vfAt a.val 0, Finset.mem_filter.mpr ⟨?_, ?_⟩, ?_⟩
  · apply (R.mem_fibre _ _).mpr
    rw [← ht, unaryPoint_eta]
    exact ha
  · have hh := (canonical_new (D.eta a.val) (0 : Fin 1)).symm.trans
      (congrArg (fun q : Point (M := M) 1 (1 + m) => q.2 0) he)
    have hh' : rv (vfAt a.val 0 - Section3.Barycentre.mean (R.fibre a.val.2)) = t 0 := by
      change rv (vfAt (D.eta a.val) 0) = t 0 at hh
      rwa [heta] at hh
    rwa [ht] at hh'
  · rwa [ht] at hv

def stepFamily (R : RootFamily A) (h00 : M ⊨ Axioms.ACVF00) (d : ℕ) (hd : R.Bound d)
    {k : Fin m} (hA : Tagged (carrier A) 0 k) : RootFamily (R.stepTarget h00 d hd hA) where
  set := R.imageSet (R.step h00 d hd hA).toMap
  subset := R.imageSet_subset _
  finite t := by
    let F := R.fibre (fun i => t (Fin.natAdd 1 i))
    let C := F.filter (fun y => rv (y - Section3.Barycentre.mean F) = t 0)
    exact (C.image (fun y => y - Section3.Barycentre.mean F)).finite_toSet.subset
      (fun x hx => R.step_fibre_subset h00 d hd hA t x hx)

private theorem child_bound (h00 : M ⊨ Axioms.ACVF00) (F U : Finset (VF (M := M)))
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

theorem step_bound (R : RootFamily A) (h00 : M ⊨ Axioms.ACVF00) (d : ℕ) (hd : R.Bound (d + 1))
    {k : Fin m} (hA : Tagged (carrier A) 0 k) : (R.stepFamily h00 (d + 1) hd hA).Bound d := by
  intro t hn
  apply child_bound h00 (R.fibre (fun i => t (Fin.natAdd 1 i)))
    ((R.stepFamily h00 (d + 1) hd hA).fibre t) (t 0) d (hd _)
      (fun x hx => R.step_fibre_subset h00 (d + 1) hd hA t x
        (((R.stepFamily h00 (d + 1) hd hA).mem_fibre t x).mp hx)) hn

theorem step_tagged (R : RootFamily A) (h00 : M ⊨ Axioms.ACVF00) (d : ℕ) (hd : R.Bound d)
    {k : Fin m} (hA : Tagged (carrier A) 0 k) :
    Tagged (carrier (R.stepTarget h00 d hd hA)) 0 (Fin.castAdd m (0 : Fin 1)) := by
  have he : carrier (R.stepTarget h00 d hd hA) =
      canonical '' carrier (R.focus h00 d hd hA).etaImage := canonicalImage_carrier _
  rw [he]
  exact canonical_tagged _ _

theorem iterate (h00 : M ⊨ Axioms.ACVF00) (d : ℕ) :
    ∀ {m : ℕ} {A : DefSet (M := M) S 1 m} (R : RootFamily A)
      (k : Fin m) (hA : Tagged (carrier A) 0 k), R.Bound d →
      ∃ l : ℕ, ∃ B : DefSet (M := M) S 1 l, ∃ T : Chain S 1 A B,
        T.Alternating (some false) ∧ ∀ a : A, a.val ∈ carrier R.set → vfAt (T.toMap a).val 0 = 0 := by
  induction d with
  | zero =>
    intro m A R k hA hd
    exact ⟨m, A, .nil A, trivial, fun a ha => R.bound_zero hd a.val ha⟩
  | succ d ih =>
    intro m A R k hA hd
    let V := R.step h00 (d + 1) hd hA
    let Q := R.stepFamily h00 (d + 1) hd hA
    obtain ⟨l, B, U, hU, hz⟩ := ih Q (Fin.castAdd m (0 : Fin 1))
      (R.step_tagged h00 (d + 1) hd hA) (R.step_bound h00 d hd hA)
    let T : Chain S 1 A B := .cons (.centripetal (R.focus h00 (d + 1) hd hA)) (.cons (.canonical _) U)
    refine ⟨l, B, T, ⟨by decide, by decide, hU⟩, ?_⟩
    intro a ha
    apply hz (V.toMap a)
    exact (R.mem_imageSet V.toMap _).mpr ⟨a, ha, rfl⟩

end SpecialTransformations.Section5.RootFamily

#check @SpecialTransformations.Section5.RootFamily.iterate
#print axioms SpecialTransformations.Section5.RootFamily.iterate

namespace SpecialTransformations.Section5.RootFamily

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {m l : ℕ}
variable {A : DefSet (M := M) S 1 m} {A₀ : DefSet (M := M) S 1 l}

theorem canonical_fibre_subset (R : RootFamily A) (t : Fin (1 + m) → RV (M := M))
    (x : VF (M := M))
    (hx : unaryPoint x t ∈ carrier (R.imageSet (Map.toImage (canonicalMap A)))) :
    x ∈ R.fibre (fun i => t (Fin.natAdd 1 i)) := by
  obtain ⟨a, ha, he⟩ := (R.mem_imageSet _ _).mp hx
  change canonical a.val = unaryPoint x t at he
  have ht : a.val.2 = fun i => t (Fin.natAdd 1 i) := by
    funext i
    have hh := congrArg (fun q : Point (M := M) 1 (1 + m) => q.2 (Fin.natAdd 1 i)) he
    simpa only [canonical_old, unaryPoint] using hh
  have hv : vfAt a.val 0 = x := congrArg (fun q : Point (M := M) 1 (1 + m) => vfAt q 0) he
  apply (R.mem_fibre _ _).mpr
  rw [← hv, ← ht, unaryPoint_eta]
  exact ha

def canonicalFamily (R : RootFamily A) : RootFamily (canonicalImage A) where
  set := R.imageSet (Map.toImage (canonicalMap A))
  subset := R.imageSet_subset _
  finite t := (R.fibre (fun i => t (Fin.natAdd 1 i))).finite_toSet.subset
    (fun x hx => R.canonical_fibre_subset t x hx)

theorem canonical_bound (R : RootFamily A) (d : ℕ) (hd : R.Bound d) : R.canonicalFamily.Bound d := by
  intro t hn
  have hs : R.canonicalFamily.fibre t ⊆ R.fibre (fun i => t (Fin.natAdd 1 i)) := by
    intro x hx
    exact R.canonical_fibre_subset t x ((R.canonicalFamily.mem_fibre t x).mp hx)
  obtain ⟨x, hx, hx0⟩ := hn
  exact (Finset.card_le_card hs).trans (hd _ ⟨x, hs hx, hx0⟩)

/-- The bounded-family construction is uniform over all RV tuples and can
follow any initial special bijection with genuine alternation. -/
theorem centralize_after (h00 : M ⊨ Axioms.ACVF00) (R : RootFamily A) (d : ℕ) (hd : R.Bound d)
    (τ : SpecialBijection A₀ A) :
    ∃ r : ℕ, ∃ B : DefSet (M := M) S 1 r, ∃ T : SpecialBijection A B,
      (τ.chain.append T.chain).Alternating none ∧
        ∀ a : A, a.val ∈ carrier R.set → vfAt (T.toMap a).val 0 = 0 := by
  by_cases hlast : τ.chain.lastKind none = some false
  · obtain ⟨k, hk⟩ := τ.chain.lastKind_tagged none (by intro h; cases h) hlast
    obtain ⟨r, B, U, hU, hz⟩ := iterate h00 d R k hk hd
    let T : SpecialBijection A B := ⟨U, U.alternating_none (some false) hU⟩
    refine ⟨r, B, T, ?_, hz⟩
    apply τ.chain.append_alternating U none τ.alternating
    simpa only [hlast] using hU
  · let f := Map.toImage (canonicalMap A)
    let Q := R.canonicalFamily
    have htag : Tagged (carrier (canonicalImage A)) 0 (Fin.castAdd m (0 : Fin 1)) := by
      rw [canonicalImage_carrier]
      exact canonical_tagged _ _
    obtain ⟨r, B, U, hU, hz⟩ := iterate h00 d Q (Fin.castAdd m (0 : Fin 1)) htag
      (R.canonical_bound d hd)
    let T : SpecialBijection A B := ⟨.cons (.canonical A) U, by decide, hU⟩
    refine ⟨r, B, T, ?_, ?_⟩
    · apply τ.chain.append_alternating T.chain none τ.alternating
      exact ⟨hlast, hU⟩
    · intro a ha
      apply hz (f a)
      exact (R.mem_imageSet f _).mpr ⟨a, ha, rfl⟩

end SpecialTransformations.Section5.RootFamily

#check @SpecialTransformations.Section5.RootFamily.centralize_after
#print axioms SpecialTransformations.Section5.RootFamily.centralize_after

namespace SpecialTransformations.Section5.RootFamily

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {m : ℕ} {A : DefSet (M := M) S 1 m}

def restrict (R : RootFamily A) (B : DefSet (M := M) S 1 m)
    (_hBA : carrier B ⊆ carrier A) : RootFamily B where
  set := PresentedSet.mk (carrier R.set ∩ carrier B)
    (SetDefinable.inter _ (setDefinable R.set) (setDefinable B))
  subset := Set.inter_subset_right
  finite t := (R.finite t).subset (fun _ h => h.1)

theorem restrict_bound (R : RootFamily A) (B : DefSet (M := M) S 1 m)
    (hBA : carrier B ⊆ carrier A) (d : ℕ) (hd : R.Bound d) : (R.restrict B hBA).Bound d := by
  intro t hn
  have hs : (R.restrict B hBA).fibre t ⊆ R.fibre t := by
    intro x hx
    exact (R.mem_fibre t x).mpr (((R.restrict B hBA).mem_fibre t x).mp hx).1
  obtain ⟨x, hx, hx0⟩ := hn
  exact (Finset.card_le_card hs).trans (hd t ⟨x, hs hx, hx0⟩)

theorem centralize_boundary (h00 : M ⊨ Axioms.ACVF00) (R : RootFamily A) (d : ℕ) (hd : R.Bound d)
    (previous : Option Bool) (hTag : previous = some false → ∃ k : Fin m, Tagged (carrier A) 0 k) :
    ∃ r : ℕ, ∃ B : DefSet (M := M) S 1 r, ∃ T : Chain S 1 A B,
      T.Alternating previous ∧ ∀ a : A, a.val ∈ carrier R.set → vfAt (T.toMap a).val 0 = 0 := by
  by_cases hprev : previous = some false
  · obtain ⟨k, hk⟩ := hTag hprev
    obtain ⟨r, B, U, hU, hz⟩ := iterate h00 d R k hk hd
    exact ⟨r, B, U, by simpa only [hprev] using hU, hz⟩
  · let f := Map.toImage (canonicalMap A)
    let Q := R.canonicalFamily
    have htag : Tagged (carrier (canonicalImage A)) 0 (Fin.castAdd m (0 : Fin 1)) := by
      rw [canonicalImage_carrier]
      exact canonical_tagged _ _
    obtain ⟨r, B, U, hU, hz⟩ := iterate h00 d Q (Fin.castAdd m (0 : Fin 1)) htag
      (R.canonical_bound d hd)
    let T : Chain S 1 A B := .cons (.canonical A) U
    refine ⟨r, B, T, ⟨hprev, hU⟩, ?_⟩
    intro a ha
    apply hz (f a)
    exact (R.mem_imageSet f _).mpr ⟨a, ha, rfl⟩

end SpecialTransformations.Section5.RootFamily

namespace SpecialTransformations.Section5

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {m : ℕ}

def rawUnaryValues (p : Point (M := M) 1 m) : Fin (m + 1) → M :=
  Fin.cons (vfAt p 0).val (fun i => (p.2 i).val)

theorem rawUnaryValues_injective : Function.Injective (rawUnaryValues (M := M) (m := m)) := by
  intro p q he
  refine Prod.ext ?_ ?_
  · funext i
    fin_cases i
    exact Subtype.ext (congrFun he 0)
  · funext i
    exact Subtype.ext (congrFun he i.succ)

def rawUnarySet (A : DefSet (M := M) S 1 m) : Set (Fin (m + 1) → M) :=
  rawUnaryValues '' carrier A

theorem mem_rawUnarySet_values (A : DefSet (M := M) S 1 m) (p : Point (M := M) 1 m) :
    rawUnaryValues p ∈ rawUnarySet A ↔ p ∈ carrier A := by
  constructor
  · rintro ⟨q, hq, he⟩
    exact (rawUnaryValues_injective he) ▸ hq
  · intro hp
    exact ⟨p, hp, rfl⟩

theorem rawUnarySet_definable (A : DefSet (M := M) S 1 m) :
    Section3.DefinableOver S Section3.MixedPolynomialSyntax.contextSort (rawUnarySet A) := by
  apply (Section3.definableOver_iff_normalized_raw S Section3.MixedPolynomialSyntax.contextSort _).mpr
  constructor
  · let σ : Fin 1 ⊕ Fin m → Fin (m + 1) := Sum.elim (fun _ => 0) Fin.succ
    have h := @Set.Definable.preimage_comp M S LRV (CanonicalStructure.normalize (M := M))
      (Fin 1 ⊕ Fin m) (Fin (m + 1)) σ _ (setDefinable A)
    convert h using 1
    ext z
    rw [Set.mem_preimage, unary_code_iff]
    constructor
    · rintro ⟨p, hp, he⟩
      refine ⟨vfAt p 0, p.2, congrFun he 0, (fun i => congrFun he i.succ), ?_⟩
      rwa [unaryPoint_eta]
    · rintro ⟨x, t, hx, ht, hA⟩
      refine ⟨unaryPoint x t, hA, ?_⟩
      funext i
      exact Fin.cases hx (fun j => ht j) i
  · rintro z ⟨p, hp, rfl⟩ i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact (vfAt p 0).property
    · exact (p.2 j).property

def obstacleSet (S : Set M) (m : ℕ) (Q : Finset (VF (M := M)))
    (hQ : Section3.DefinableAt S .vf (Subtype.val '' (Q : Set (VF (M := M))))) :
    DefSet (M := M) S 1 m :=
  PresentedSet.mk {p | vfAt p 0 ∈ Q} (by
    have hraw := ((Section3.definableAt_iff_normalized_raw S .vf _).mp hQ).1
    have hcoord := @Set.Definable.preimage_comp M S LRV (CanonicalStructure.normalize (M := M))
      (Fin 1) (Fin 1 ⊕ Fin m) (fun _ => Sum.inl 0) _ hraw
    have hdom := @DefinableGeometry.Space.definable_domain LRV M (CanonicalStructure.normalize (M := M))
      (pointSpace 1 m) S
    change @Set.Definable M S LRV (CanonicalStructure.normalize (M := M)) (Fin 1 ⊕ Fin m)
      {z | ∃ hd : z ∈ pDomain (pointSpace 1 m), vfAt (pDecode (pointSpace 1 m) ⟨z, hd⟩) 0 ∈ Q}
    convert (@Set.Definable.inter M S LRV (CanonicalStructure.normalize (M := M))
      (Fin 1 ⊕ Fin m) _ _ hdom hcoord) using 1
    ext z
    constructor
    · rintro ⟨hd, hq⟩
      exact ⟨hd, vfAt (pDecode (pointSpace 1 m) ⟨z, hd⟩) 0, hq, rfl⟩
    · rintro ⟨hd, q, hq, he⟩
      refine ⟨hd, ?_⟩
      have hqeq : q = vfAt (pDecode (pointSpace 1 m) ⟨z, hd⟩) 0 := Subtype.ext he
      exact hqeq ▸ hq)

def obstacleFamily (S : Set M) (m : ℕ) (Q : Finset (VF (M := M)))
    (hQ : Section3.DefinableAt S .vf (Subtype.val '' (Q : Set (VF (M := M))))) :
    RootFamily (PresentedSet.univ (pointSpace (M := M) 1 m) S) where
  set := obstacleSet S m Q hQ
  subset := Set.subset_univ _
  finite _ := Q.finite_toSet

theorem obstacleFamily_bound (S : Set M) (m : ℕ) (Q : Finset (VF (M := M)))
    (hQ : Section3.DefinableAt S .vf (Subtype.val '' (Q : Set (VF (M := M))))) :
    (obstacleFamily S m Q hQ).Bound Q.card := by
  intro t _
  have he : (obstacleFamily S m Q hQ).fibre t = Q := by
    ext x
    rw [RootFamily.mem_fibre]
    rfl
  rw [he]

/-- Lemma 5.2. The earlier-section finite definable obstacle set controls
all original RV tuples simultaneously. No companion-paper lemma is assumed. -/
theorem lemma_5_2_at_boundary (h00 : M ⊨ Axioms.ACVF00) (A : DefSet (M := M) S 1 m)
    (previous : Option Bool)
    (hTag : previous = some false → ∃ k : Fin m, Tagged (carrier A) 0 k) :
    ∃ r : ℕ, ∃ B : DefSet (M := M) S 1 r, ∃ T : SpecialBijection A B,
      T.chain.Alternating previous ∧ IsRVPullback (carrier B) := by
  obtain ⟨Γ, hΓ, v, hv⟩ := VFValued.exists_valuation_predV (M := M)
  letI := hΓ
  obtain ⟨Q, _, hQ, hO, _⟩ := Section3.mixed_finite_definable_obstacles v hv S
    (rawUnarySet A) (rawUnarySet_definable A)
  let E : DefSet (M := M) S 1 m := PresentedSet.mk (hull (carrier A)) (hull_definable A)
  have hAE : carrier A ⊆ carrier E := subset_hull _
  let R₀ := obstacleFamily S m Q hQ
  let R := R₀.restrict E (Set.subset_univ _)
  have hTagE : previous = some false → ∃ k : Fin m, Tagged (carrier E) 0 k := by
    intro he
    obtain ⟨k, hk⟩ := hTag he
    exact ⟨k, tagged_hull hk⟩
  obtain ⟨r, B, W, hW, hz⟩ := R.centralize_boundary h00 Q.card
    (R₀.restrict_bound E (Set.subset_univ _) Q.card (obstacleFamily_bound S m Q hQ)) previous hTagE
  let T : SpecialBijection E B := ⟨W, W.alternating_none previous hW⟩
  have hE : IsRVPullback (carrier E) := hull_idem _
  have hB := T.preserves_pullback hE
  obtain ⟨C, V, hV, hCB, hImage, _⟩ := T.restrict_at A hAE previous hW
  refine ⟨r, C, V, hV, (isRVPullback_iff _).mpr ?_⟩
  intro p hp q hpq
  by_cases hp0 : vfAt p 0 = 0
  · obtain ⟨hvv, htt⟩ := (sameRV_iff _ _).mp hpq
    have hq0 : vfAt q 0 = 0 := (rv_eq_zero_iff _).mp ((hvv 0).symm.trans (congrArg rv hp0))
    have he : p = q := by
      refine Prod.ext ?_ htt
      funext i
      fin_cases i
      exact hp0.trans hq0.symm
    exact he ▸ hp
  · have hqB := (isRVPullback_iff _).mp hB p (hCB hp) q hpq
    have hpImage : ∃ a : A, (T.toMap ⟨a.val, hAE a.property⟩).val = p := by
      change p ∈ {c | ∃ a : A, (T.toMap ⟨a.val, hAE a.property⟩).val = c}
      rw [← hImage]
      exact hp
    obtain ⟨a, hap⟩ := hpImage
    let aE : E := ⟨a.val, hAE a.property⟩
    let b := T.toMap aE
    let c : B := ⟨q, hqB⟩
    have hbval : b.val = p := hap
    have hb : vfAt b.val 0 ≠ 0 := by rw [hbval]; exact hp0
    have hbc : SameRV b.val c.val := by change SameRV b.val q; rw [hbval]; exact hpq
    obtain ⟨he, _⟩ := T.unary_inverse_fibre v hv hB b hb
    rw [T.inverse_apply] at he
    let centre := vfAt a.val 0
    have hrad : v (vfAt b.val 0) ≠ 0 := (map_ne_zero v).mpr hb
    let ρ : Section3.Balls.OpenRadius Γ := Section3.Balls.openRadius (v (vfAt b.val 0)) hrad
    have hmem (x : VF (M := M)) (hx : x ∈ Section3.Balls.openDisc v centre ρ) :
        unaryPoint x a.val.2 ∈ T.inverseFibre b := by
      rw [he]
      refine ⟨?_, rfl⟩
      change v (x - centre) < v (vfAt b.val 0)
      simpa only [ρ, Section3.Balls.openDisc_openRadius,
        Set.mem_ofPred_eq] using hx
    have havoid : ∀ x ∈ Q, x ∉ Section3.Balls.openDisc v centre ρ := by
      intro x hx hxd
      obtain ⟨u, hu, hrv⟩ := hmem x hxd
      have hval : vfAt u.val 0 = x := congrArg (fun z : Point (M := M) 1 m => vfAt z 0) hu
      have huR : u.val ∈ carrier R.set := by
        change vfAt u.val 0 ∈ Q ∧ u.val ∈ carrier E
        exact ⟨by rwa [hval], u.property⟩
      have hzero := hz u huR
      have hh := ((sameRV_iff _ _).mp hrv).1 0
      change rv (vfAt (T.toMap u).val 0) = rv (vfAt b.val 0) at hh
      have hz' : vfAt (T.toMap u).val 0 = 0 := hzero
      exact hb ((rv_eq_zero_iff _).mp (hh.symm.trans (congrArg rv hz')))
    let u := T.inverseMap c
    have huF : u.val ∈ T.inverseFibre b :=
      ⟨u, rfl, by rw [T.apply_inverse]; exact hbc.symm⟩
    rw [he] at huF
    have hy : vfAt u.val 0 ∈ Section3.Balls.openDisc v centre ρ := by
      simpa only [ρ, Section3.Balls.openDisc_openRadius,
        Set.mem_ofPred_eq] using huF.1
    have hconst := hO centre ρ havoid centre (Section3.Balls.centre_mem_openDisc v centre ρ)
      (vfAt u.val 0) hy (fun i => (a.val.2 i).val) (fun i => (a.val.2 i).property)
    have haRaw : rawUnaryValues a.val ∈ rawUnarySet A := (mem_rawUnarySet_values A a.val).mpr a.property
    have huRaw : rawUnaryValues u.val ∈ rawUnarySet A := by
      change Fin.cons (vfAt u.val 0).val (fun i => (u.val.2 i).val) ∈ rawUnarySet A
      rw [huF.2]
      exact hconst.mp haRaw
    have huA := (mem_rawUnarySet_values A u.val).mp huRaw
    rw [hImage]
    refine ⟨⟨u.val, huA⟩, ?_⟩
    change (T.toMap u).val = q
    exact congrArg Subtype.val (T.apply_inverse c)

theorem lemma_5_2 (h00 : M ⊨ Axioms.ACVF00) (A : DefSet (M := M) S 1 m) :
    IsDeformedRVPullback A := by
  obtain ⟨r, B, T, _, hB⟩ := lemma_5_2_at_boundary h00 A none (by intro h; cases h)
  exact ⟨r, B, ⟨T⟩, hB⟩

theorem lemma_5_2_after (h00 : M ⊨ Axioms.ACVF00)
    {l : ℕ} {A₀ : DefSet (M := M) S 1 l} {A : DefSet (M := M) S 1 m}
    (τ : SpecialBijection A₀ A) :
    ∃ r : ℕ, ∃ B : DefSet (M := M) S 1 r, ∃ T : SpecialBijection A B,
      (τ.chain.append T.chain).Alternating none ∧ IsRVPullback (carrier B) := by
  obtain ⟨r, B, T, hT, hB⟩ := lemma_5_2_at_boundary h00 A (τ.chain.lastKind none)
    (fun h => τ.chain.lastKind_tagged none (by intro he; cases he) h)
  exact ⟨r, B, T, τ.chain.append_alternating T.chain none τ.alternating hT, hB⟩

namespace Chain

variable {S : Set M} {n a b c d : ℕ}
variable {A : DefSet (M := M) S n a} {B : DefSet (M := M) S n b}
variable {C : DefSet (M := M) S n c} {D : DefSet (M := M) S n d}

theorem append_assoc (T : Chain S n A B) (U : Chain S n B C) (V : Chain S n C D) :
    (T.append U).append V = T.append (U.append V) := by
  induction T with
  | nil _ => rfl
  | cons p tail ih => exact congrArg (Chain.cons p) (ih U)

theorem append_suffix_alternating (T : Chain S n A B) (U : Chain S n B C)
    (previous : Option Bool) (h : (T.append U).Alternating previous) :
    U.Alternating none := by
  induction T generalizing previous with
  | nil _ => exact U.alternating_none previous h
  | cons p tail ih =>
    apply ih U (some p.kind)
    exact ((cons_alternating_iff p (tail.append U) previous).mp h).2

end Chain

/-- Unary Theorem 5.5. The original domain is an arbitrary definable set,
and the supplied initial special bijection is retained. -/
theorem theorem_5_5_unary (h00 : M ⊨ Axioms.ACVF00)
    {A₀ : DefSet (M := M) S 1 0} {A : DefSet (M := M) S 1 m}
    (τ : SpecialBijection A₀ A) (p : Polynomial (VF (M := M)))
    (hc : ∀ i : ℕ, (p.coeff i).val ∈ S) :
    ∃ r : ℕ, ∃ B : DefSet (M := M) S 1 r, ∃ T : SpecialBijection A B,
      (τ.chain.append T.chain).Alternating none ∧ IsRVPullback (carrier B) ∧
        ScalarContractible (fun b : B => p.eval (vfAt (τ.inverseMap (T.inverseMap b)).val 0)) := by
  obtain ⟨l, C, V, hV, hC⟩ := lemma_5_2_after h00 τ
  by_cases hp : p = 0
  · refine ⟨l, C, V, hV, hC, ?_⟩
    intro b c _
    simp only [hp, Polynomial.eval_zero]
  · let U₀ : SpecialBijection A₀ C := ⟨τ.chain.append V.chain, hV⟩
    let R₀ := polynomialRoots A₀ p hc hp
    let R := R₀.push U₀.toMap
    obtain ⟨r, B, W, hW, hz⟩ := R.centralize_after h00 U₀
    have halt : (τ.chain.append (V.chain.append W.chain)).Alternating none := by
      rw [← Chain.append_assoc]
      exact hW
    let T : SpecialBijection A B :=
      ⟨V.chain.append W.chain, τ.chain.append_suffix_alternating _ none halt⟩
    let U : SpecialBijection A₀ B := ⟨τ.chain.append T.chain, halt⟩
    have hmap : U.toMap = Map.comp W.toMap U₀.toMap := by
      change (τ.chain.append (V.chain.append W.chain)).toMap = _
      rw [← Chain.append_assoc]
      exact U₀.chain.append_toMap W.chain
    have hB : IsRVPullback (carrier B) := W.preserves_pullback hC
    have hzero : ∀ a : A₀, p.eval (vfAt a.val 0) = 0 → vfAt (U.toMap a).val 0 = 0 := by
      intro a ha
      rw [hmap]
      apply hz (U₀.toMap a)
      apply (R.mem_points _).mp
      apply (R₀.mem_push_points U₀.toMap _).mpr
      exact ⟨a, (R₀.mem_points _).mpr ⟨a.property, ha⟩, rfl⟩
    have hi (b : B) : U.inverseMap b = τ.inverseMap (T.inverseMap b) := by
      apply U.bijective.1
      have hmap' : U.toMap = Map.comp T.toMap τ.toMap := τ.chain.append_toMap T.chain
      rw [U.apply_inverse, hmap']
      change b = T.toMap (τ.toMap (τ.inverseMap (T.inverseMap b)))
      rw [τ.apply_inverse, T.apply_inverse]
    refine ⟨r, B, T, halt, hB, ?_⟩
    have hh := polynomial_contractible_of_zero_roots U hB p hzero
    intro b c he
    simpa only [hi] using hh b c he

end SpecialTransformations.Section5

#check @SpecialTransformations.Section5.lemma_5_2
#print axioms SpecialTransformations.Section5.lemma_5_2
#check @SpecialTransformations.Section5.theorem_5_5_unary
#print axioms SpecialTransformations.Section5.theorem_5_5_unary
