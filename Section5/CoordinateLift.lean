import Section5.UnarySets

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

def dropHead (ρ : Fin m → Fin l) (p : Point (M := M) (n + 1) l) : Point (M := M) n m :=
  (fun i => p.1 i.succ, fun i => p.2 (ρ i))

theorem sameRV_dropHead (ρ : Fin m → Fin l) {p q : Point (M := M) (n + 1) l}
    (h : SameRV p q) : SameRV (dropHead ρ p) (dropHead ρ q) := by
  obtain ⟨hv, ht⟩ := (sameRV_iff _ _).mp h
  exact (sameRV_iff _ _).mpr ⟨fun i => hv i.succ, by simp only [dropHead, ht]⟩

theorem dropHead_replace (ρ : Fin m → Fin l) (j : Fin n)
    (p : Point (M := M) (n + 1) l) (x : VF (M := M)) :
    dropHead ρ (replace j.succ p x) = replace j (dropHead ρ p) x := by
  apply Prod.ext
  · funext i
    by_cases hi : i = j
    · subst i; simp [dropHead, replace]
    · simp [dropHead, replace, hi, Fin.succ_inj.ne.mpr hi]
  · rfl

theorem dropHead_replace_zero (ρ : Fin m → Fin l)
    (p : Point (M := M) (n + 1) l) (x : VF (M := M)) :
    dropHead ρ (replace 0 p x) = dropHead ρ p := by
  refine Prod.ext ?_ rfl
  funext i
  simp [dropHead, replace, Fin.succ_ne_zero]

theorem replace_head_comm (j : Fin n) (p : Point (M := M) (n + 1) l)
    (x y : VF (M := M)) :
    replace j.succ (replace 0 p x) y = replace 0 (replace j.succ p y) x := by
  refine Prod.ext ?_ rfl
  exact Function.update_comm (Fin.succ_ne_zero j).symm x y p.1

def dropHeadCodes (ρ : Fin m → Fin l) (z : Fin (n + 1) ⊕ Fin l → M) : Fin n ⊕ Fin m → M :=
  Sum.elim (fun i => z (.inl i.succ)) (fun i => z (.inr (ρ i)))

def dropHeadMap (ρ : Fin m → Fin l) (A : DefSet (M := M) S (n + 1) l) :
    Map A (PresentedSet.univ (pointSpace n m) S) :=
  Map.ofCodes A (dropHead ρ) (dropHeadCodes ρ)
    (by intro i; cases i <;> exact rawProj S _)
    (by intro c; exact ⟨fun i => c.property.1 i.succ, fun i => c.property.2 (ρ i)⟩)
    (by intro c; rfl)

theorem dropHead_preimage_definable (ρ : Fin m → Fin l) (D : Set (Point (M := M) n m))
    (hD : SetDefinable (pointSpace n m) S D) :
    SetDefinable (pointSpace (n + 1) l) S {p | dropHead ρ p ∈ D} := by
  have hh := Map.definable_preimage
    (dropHeadMap ρ (PresentedSet.univ (pointSpace (n + 1) l) S)) hD
  have he : {p : Point (M := M) (n + 1) l | dropHead ρ p ∈ D} =
      {p | ∃ a : PresentedSet.univ (pointSpace (M := M) (n + 1) l) S,
        a.val = p ∧ (dropHeadMap ρ (PresentedSet.univ (pointSpace (n + 1) l) S) a).val ∈ D} := by
    ext p
    exact ⟨fun hd => ⟨⟨p, Set.mem_univ _⟩, rfl, hd⟩, fun ⟨a, ha, hd⟩ => ha ▸ hd⟩
  exact (congrArg (fun Z : Set (Point (M := M) (n + 1) l) =>
    SetDefinable (pointSpace (n + 1) l) S Z) he).mpr hh

namespace Focus

variable {A : DefSet (M := M) S n m} {H : DefSet (M := M) S (n + 1) l}
variable {j : Fin n} {k : Fin m}

def liftGeometry (D : Focus A j k) (ρ : Fin m → Fin l)
    (hHA : ∀ p ∈ carrier H, dropHead ρ p ∈ carrier A) :
    FocusGeometry (carrier H) j.succ (ρ k) where
  tagged p hp := D.tagged (dropHead ρ p) (hHA p hp)
  locus := {p | dropHead ρ p ∈ D.locus} ∩ hull (carrier H)
  locus_pullback := isRVPullback_inter ((isRVPullback_iff _).mpr (by
    intro p hp q he
    exact (isRVPullback_iff _).mp D.locus_pullback _ hp _ (sameRV_dropHead ρ he))) (hull_idem _)
  locus_subset := Set.inter_subset_right
  center p := D.center (dropHead ρ p)
  independent p hp q hq he := by
    apply D.independent (dropHead ρ p) ⟨hHA p hp.1, hp.2.1⟩
      (dropHead ρ q) ⟨hHA q hq.1, hq.2.1⟩
    have hh := congrArg (dropHead ρ) he
    simpa only [erase, dropHead_replace] using hh
  center_mem := by
    intro p hp
    have hlow := D.center_mem (dropHead ρ p) ⟨hHA p hp.1, hp.2.1⟩
    have hr := D.toFocusGeometry.center_sameRV (dropHead ρ p) ⟨hHA p hp.1, hp.2.1⟩
    refine ⟨?_, p, hp.1, sameRV_replace j.succ p _ hr⟩
    change dropHead ρ (replace j.succ p (D.center (dropHead ρ p))) ∈ D.locus
    rwa [dropHead_replace]

def liftActive (D : Focus A j k) (ρ : Fin m → Fin l)
    (hHA : ∀ p ∈ carrier H, dropHead ρ p ∈ carrier A) : DefSet (M := M) S (n + 1) l :=
  PresentedSet.mk (carrier H ∩ (D.liftGeometry ρ hHA).locus)
    (SetDefinable.inter _ (setDefinable H)
      (SetDefinable.inter _ (dropHead_preimage_definable ρ D.locus D.locus_definable) (hull_definable H)))

def liftActiveMap (D : Focus A j k) (ρ : Fin m → Fin l)
    (hHA : ∀ p ∈ carrier H, dropHead ρ p ∈ carrier A) :
    Map (D.liftActive ρ hHA) D.active :=
  Map.mk (fun p => ⟨dropHead ρ p.val, hHA _ p.property.1, p.property.2.1⟩)
    (Map.graph_definable (dropHeadMap ρ (D.liftActive ρ hHA)))

def lift (D : Focus A j k) (ρ : Fin m → Fin l)
    (hHA : ∀ p ∈ carrier H, dropHead ρ p ∈ carrier A) : Focus H j.succ (ρ k) where
  toFocusGeometry := D.liftGeometry ρ hHA
  locus_definable := SetDefinable.inter _
    (dropHead_preimage_definable ρ D.locus D.locus_definable) (hull_definable H)
  center_graph := by
    have hh := Map.graph_definable (Map.comp D.centerMap (D.liftActiveMap ρ hHA))
    apply RelationDefinable.congr _ _ hh
    intro p z
    constructor
    · rintro ⟨a, rfl, hz⟩
      exact ⟨a.property, (congrFun hz 0).symm⟩
    · rintro ⟨hp, hz⟩
      refine ⟨⟨p, hp⟩, rfl, ?_⟩
      funext i
      fin_cases i
      exact hz.symm

theorem lift_eta (D : Focus A j k) (ρ : Fin m → Fin l)
    (hHA : ∀ p ∈ carrier H, dropHead ρ p ∈ carrier A)
    (p : Point (M := M) (n + 1) l) (hp : p ∈ carrier H) :
    dropHead ρ ((D.lift ρ hHA).toFocusGeometry.eta p) = D.toFocusGeometry.eta (dropHead ρ p) := by
  have hh := subset_hull (carrier H) hp
  by_cases hc : dropHead ρ p ∈ D.locus <;>
    simp [FocusGeometry.eta, lift, liftGeometry, hc, hh, dropHead_replace] <;> rfl

theorem lift_eta_head (D : Focus A j k) (ρ : Fin m → Fin l)
    (hHA : ∀ p ∈ carrier H, dropHead ρ p ∈ carrier A)
    (p : Point (M := M) (n + 1) l) :
    vfAt ((D.lift ρ hHA).toFocusGeometry.eta p) 0 = vfAt p 0 := by
  exact (D.lift ρ hHA).toFocusGeometry.eta_other p 0 (Fin.succ_ne_zero j).symm

theorem lift_eta_replace_head (D : Focus A j k) (ρ : Fin m → Fin l)
    (hHA : ∀ p ∈ carrier H, dropHead ρ p ∈ carrier A)
    (p : Point (M := M) (n + 1) l) (x : VF (M := M))
    (hx : rv x = rv (vfAt p 0)) :
    (D.lift ρ hHA).toFocusGeometry.eta (replace 0 p x) =
      replace 0 ((D.lift ρ hHA).toFocusGeometry.eta p) x := by
  let F := (D.lift ρ hHA).toFocusGeometry
  have hm := mem_iff_sameRV F.locus_pullback (sameRV_replace 0 p x hx)
  have hcoord : (replace 0 p x).1 j.succ = p.1 j.succ := by
    simp [replace, Fin.succ_ne_zero]
  have hcenter : F.center (replace 0 p x) = F.center p := by
    change D.center (dropHead ρ (replace 0 p x)) = D.center (dropHead ρ p)
    rw [dropHead_replace_zero]
  change F.eta (replace 0 p x) = replace 0 (F.eta p) x
  by_cases hp : p ∈ F.locus
  · rw [FocusGeometry.eta, if_pos (hm.mp hp), FocusGeometry.eta, if_pos hp,
      hcoord, hcenter, replace_head_comm]
  · rw [FocusGeometry.eta, if_neg (fun h => hp (hm.mpr h)), FocusGeometry.eta, if_neg hp]

end Focus

def canonicalProjection (ρ : Fin m → Fin l) : Fin (n + m) → Fin ((n + 1) + l) :=
  Fin.addCases (fun i => Fin.castAdd l i.succ) (fun i => Fin.natAdd (n + 1) (ρ i))

theorem dropHead_canonical (ρ : Fin m → Fin l) (p : Point (M := M) (n + 1) l) :
    dropHead (canonicalProjection (n := n) ρ) (canonical p) = canonical (dropHead ρ p) := by
  refine Prod.ext rfl ?_
  funext i
  cases i using Fin.addCases with
  | left i => simp [dropHead, canonicalProjection, canonical]
  | right i => simp [dropHead, canonicalProjection, canonical]

namespace Chain

variable {a b : ℕ} {A : DefSet (M := M) S n a} {B : DefSet (M := M) S n b}

/-- Lift a genuine alternating chain. Extra canonical RV labels are kept
in the output and skipped only by the comparison projection. -/
theorem lift_dropHead (T : Chain S n A B) :
    ∀ {l : ℕ} (H : DefSet (M := M) S (n + 1) l) (ρ : Fin a → Fin l)
      (hHA : ∀ p ∈ carrier H, dropHead ρ p ∈ carrier A)
      (previous : Option Bool), T.Alternating previous →
    ∃ r : ℕ, ∃ K : DefSet (M := M) S (n + 1) r, ∃ σ : Fin b → Fin r,
      ∃ W : Chain S (n + 1) H K, W.Alternating previous ∧
        (∀ p : H, dropHead σ (W.toMap p).val =
          (T.toMap ⟨dropHead ρ p.val, hHA p.val p.property⟩).val) ∧
        ∀ p : H, vfAt (W.toMap p).val 0 = vfAt p.val 0 := by
  induction T with
  | nil A =>
    intro l H ρ hHA previous _
    exact ⟨l, H, ρ, .nil H, trivial, fun _ => rfl, fun _ => rfl⟩
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
      obtain ⟨r, K, σ, U, hU, hu, hh⟩ := ih H' ρ' hsub (some false) hAlt.2
      let W : Chain S (n + 1) H K := .cons (.canonical H) U
      refine ⟨r, K, σ, W, ⟨hAlt.1, hU⟩, ?_, ?_⟩
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
      obtain ⟨r, K, σ, U, hU, hu, hh⟩ := ih F.etaImage ρ hsub (some true) hAlt.2
      let W : Chain S (n + 1) H K := .cons (.centripetal F) U
      refine ⟨r, K, σ, W, ⟨hAlt.1, hU⟩, ?_, ?_⟩
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

def headKey (p : Point (M := M) (n + 1) m) : Point (M := M) n (1 + m) :=
  (fun i => p.1 i.succ, Fin.append (fun _ : Fin 1 => rv (vfAt p 0)) p.2)

def HeadSaturated (A : Set (Point (M := M) (n + 1) m)) : Prop :=
  ∀ p ∈ A, ∀ x : VF (M := M), rv x = rv (vfAt p 0) → replace 0 p x ∈ A

theorem headKey_sameRV {p q : Point (M := M) (n + 1) m} (h : SameRV p q) :
    SameRV (headKey p) (headKey q) := by
  obtain ⟨hv, ht⟩ := (sameRV_iff _ _).mp h
  apply (sameRV_iff _ _).mpr
  refine ⟨fun i => hv i.succ, ?_⟩
  change Fin.append (fun _ : Fin 1 => rv (p.1 0)) p.2 =
    Fin.append (fun _ : Fin 1 => rv (q.1 0)) q.2
  rw [hv 0, ht]

theorem headSaturated_of_pullback {A : Set (Point (M := M) (n + 1) m)}
    (hA : IsRVPullback A) : HeadSaturated A := by
  intro p hp x hx
  exact (isRVPullback_iff _).mp hA p hp _ (sameRV_replace 0 p x hx)

theorem pullback_of_headKey_image {A : Set (Point (M := M) (n + 1) m)}
    (hA : HeadSaturated A) (hK : IsRVPullback (headKey '' A)) : IsRVPullback A := by
  apply (isRVPullback_iff _).mpr
  intro p hp q hpq
  have hkq := (isRVPullback_iff _).mp hK (headKey p) ⟨p, hp, rfl⟩
    (headKey q) (headKey_sameRV hpq)
  obtain ⟨a, ha, he⟩ := hkq
  have htail := congrArg Prod.fst he
  have hlabels : a.2 = q.2 := by
    funext i
    simpa only [headKey, Fin.append_right] using
      congrArg (fun z : Point (M := M) n (1 + m) => z.2 (Fin.natAdd 1 i)) he
  have hhead : rv (vfAt a 0) = rv (vfAt q 0) :=
    congrArg (fun z : Point (M := M) n (1 + m) => z.2 (Fin.castAdd m (0 : Fin 1))) he
  have hh := hA a ha (vfAt q 0) hhead.symm
  have heq : replace 0 a (vfAt q 0) = q := by
    refine Prod.ext ?_ hlabels
    funext i
    cases i using Fin.cases with
    | zero => simp [replace, vfAt]
    | succ i => simpa [replace, headKey, Fin.succ_ne_zero] using congrFun htail i
  exact heq ▸ hh

end SpecialTransformations.Section5
