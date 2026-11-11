import Section5.Centering
import Section5.UnaryMaps

/-!
# Assembly of higher-dimensional graph preparation

The finite obstacle-family interface below belongs to the earlier QE and
root-free-ball layer. It contains no special transformation or contraction
existence assertion. The dimensional induction is separate Section 5 work.
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
variable {S : Set M} {n m l k : ℕ}

/-- Explicit earlier-section uniform obstacle-family input. All RV variables
are free; only the complementary VF coordinates index the finite root sets.
The requested ambient domain is allowed to restrict the root family. -/
def UniformVerticalObstacles {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VF (M := M)) Γ) (S : Set M) (n : ℕ) : Prop :=
  ∀ {m k : ℕ} (U : DefSet (M := M) S (n + 1) k)
    (A : DefSet (M := M) S (n + 1) m), IsRVPullback (carrier A) →
  ∃ R : VerticalRootFamily A, ∃ d : ℕ, R.Bound d ∧
    ∀ (p : Point (M := M) n m) (a : VF (M := M)) (r : Section3.Balls.OpenRadius Γ),
      (∀ x ∈ Section3.Balls.openDisc v a r, insertHead x p ∈ carrier A) →
      (∀ x ∈ R.fibre p, x ∉ Section3.Balls.openDisc v a r) →
      ∀ x ∈ Section3.Balls.openDisc v a r, ∀ y ∈ Section3.Balls.openDisc v a r,
      ∀ ys : Fin k → RV (M := M),
        (((insertHead x p).1, ys) ∈ carrier U ↔ ((insertHead y p).1, ys) ∈ carrier U)

theorem allTagged_hull (A : DefSet (M := M) S (n + 1) m) (hA : AllTagged A) :
    AllTagged (PresentedSet.mk (hull (carrier A)) (hull_definable A)) := by
  intro j
  obtain ⟨k, hk⟩ := hA j
  exact ⟨k, tagged_hull hk⟩

theorem headKey_mem_iff {D : DefSet (M := M) S (n + 1) m}
    (hD : HeadSaturated (carrier D)) (p : Point (M := M) (n + 1) m) :
    p ∈ carrier D ↔ headKey p ∈ carrier (headImage D) := by
  rw [headImage_carrier]
  constructor
  · exact fun hp => ⟨p, hp, rfl⟩
  · rintro ⟨a, ha, he⟩
    obtain ⟨ht, hr⟩ := (headKey_eq_iff _ _).mp he
    have hx := ((sameRV_iff _ _).mp hr).1 0
    have hp := hD a ha (vfAt p 0) hx.symm
    have heq : replace 0 a (vfAt p 0) = p := by
      refine Prod.ext ?_ (((sameRV_iff _ _).mp hr).2)
      funext i
      cases i using Fin.cases with
      | zero => simp [replace, vfAt]
      | succ i => simpa only [replace, vfAt, Function.update_of_ne (Fin.succ_ne_zero i)] using ht i
    exact heq ▸ hp

theorem dropHead_headTag (p : Point (M := M) (n + 1) m) (k : Fin m)
    (hk : p.2 k = rv (vfAt p 0)) :
    dropHead (Fin.append (fun _ : Fin 1 => k) id) p = headKey p := by
  refine Prod.ext rfl ?_
  funext i
  cases i using Fin.addCases with
  | left i => fin_cases i; simpa only [dropHead, headKey, Fin.append_left] using hk
  | right i => simp only [dropHead, headKey, Fin.append_right, id_eq]

theorem vertical_rvGraph_transfer {A E : DefSet (M := M) S (n + 1) m}
    {D : DefSet (M := M) S 0 k} {B : DefSet (M := M) S (n + 1) l}
    (f : Map A D) (hAE : carrier A ⊆ carrier E) (T : SpecialBijection E B)
    (hT : VerticalRelationContractible (carrier (rvGraph f)) T)
    (a : A) (b : B)
    (he : SameRV (T.toMap ⟨a.val, hAE a.property⟩).val b.val)
    (ht : TailEq (T.toMap ⟨a.val, hAE a.property⟩).val b.val) :
    ∃ d : A, d.val = (T.inverseMap b).val ∧ (f d).val.2 = (f a).val.2 := by
  let aE : E := ⟨a.val, hAE a.property⟩
  let ys := Fin.append a.val.2 (f a).val.2
  have hh := hT (T.toMap aE) b he ht ys
  rw [T.inverse_apply] at hh
  have haG : attachRV a.val (f a).val.2 ∈ carrier (rvGraph f) :=
    (mem_rvGraph f _ _).mpr ⟨a, rfl, rfl⟩
  have hlabels : (T.inverseMap b).val.2 = a.val.2 := by
    have h := ((sameRV_iff _ _).mp (T.inverse_contractible (T.toMap aE) b he)).2
    rw [T.inverse_apply] at h
    exact h.symm
  have hdG : attachRV (T.inverseMap b).val (f a).val.2 ∈ carrier (rvGraph f) := by
    change ((T.inverseMap b).val.1, Fin.append (T.inverseMap b).val.2 (f a).val.2) ∈ _
    rw [hlabels]
    exact hh.mp haG
  exact (mem_rvGraph f _ _).mp hdG

namespace Map

def transportImage {u v : ℕ} {A : DefSet (M := M) S (n + 1) m}
    {B : DefSet (M := M) S (n + 1) l} {D : DefSet (M := M) S u v}
    (q : Map A B) (f : Map A D) (hq : Function.Injective q) : Map (Map.image q) D :=
  Map.descend q f (fun a b he => congrArg f (hq (Subtype.ext he)))

theorem transportImage_apply {u v : ℕ} {A : DefSet (M := M) S (n + 1) m}
    {B : DefSet (M := M) S (n + 1) l} {D : DefSet (M := M) S u v}
    (q : Map A B) (f : Map A D) (hq : Function.Injective q) (a : A) :
    Map.transportImage q f hq (Map.toImage q a) = f a := Map.descend_apply _ _ _ _

end Map

theorem restricted_map_injective {A E : DefSet (M := M) S (n + 1) m}
    {B : DefSet (M := M) S (n + 1) l} (hAE : carrier A ⊆ carrier E)
    (T : SpecialBijection E B) :
    Function.Injective (Map.comp T.toMap (Map.inclusion hAE)) := by
  intro a b he
  have hh := T.bijective.1 he
  exact Subtype.ext (congrArg (fun z : E => z.val) hh)

theorem restricted_image_mem_iff {A E : DefSet (M := M) S (n + 1) m}
    {B : DefSet (M := M) S (n + 1) l} (hAE : carrier A ⊆ carrier E)
    (T : SpecialBijection E B) (b : B) :
    b.val ∈ carrier (Map.image (Map.comp T.toMap (Map.inclusion hAE))) ↔
      (T.inverseMap b).val ∈ carrier A := by
  constructor
  · rintro ⟨a, ha⟩
    have he : T.toMap ⟨a.val, hAE a.property⟩ = b := Subtype.ext ha
    rw [← he, T.inverse_apply]
    exact a.property
  · intro hb
    refine ⟨⟨(T.inverseMap b).val, hb⟩, ?_⟩
    have he : (⟨(T.inverseMap b).val, hAE hb⟩ : E) = T.inverseMap b := Subtype.ext rfl
    change (T.toMap ⟨(T.inverseMap b).val, hAE hb⟩).val = b.val
    rw [he, T.apply_inverse]

/-- A prepared graph gives head saturation of its actual transformed domain,
and the induced definable function is constant on head-key fibres. -/
theorem vertical_graph_image {A E : DefSet (M := M) S (n + 1) m}
    {D : DefSet (M := M) S 0 k} {B : DefSet (M := M) S (n + 1) l}
    (f : Map A D) (hAE : carrier A ⊆ carrier E) (T : SpecialBijection E B)
    (hB : IsRVPullback (carrier B))
    (hT : VerticalRelationContractible (carrier (rvGraph f)) T) :
    let q := Map.comp T.toMap (Map.inclusion hAE)
    let F := Map.transportImage q f (restricted_map_injective hAE T)
    HeadSaturated (carrier (Map.image q)) ∧
      ∀ b c : Map.image q, SameRV b.val c.val → TailEq b.val c.val → F b = F c := by
  let q := Map.comp T.toMap (Map.inclusion hAE)
  let hq := restricted_map_injective hAE T
  let F := Map.transportImage q f hq
  constructor
  · intro p hp x hx
    obtain ⟨a, ha⟩ := hp
    have hpB : p ∈ carrier B := ha ▸ (q a).property
    have hpq : SameRV p (replace 0 p x) := sameRV_replace 0 p x hx
    have hqB := (isRVPullback_iff _).mp hB p hpB _ hpq
    let b : B := ⟨replace 0 p x, hqB⟩
    have he : SameRV (T.toMap ⟨a.val, hAE a.property⟩).val b.val := by
      change SameRV (q a).val (replace 0 p x)
      exact (congrArg (fun z : Point (M := M) (n + 1) l => SameRV z (replace 0 p x)) ha).mpr hpq
    have ht : TailEq (T.toMap ⟨a.val, hAE a.property⟩).val b.val := by
      intro i
      change vfAt (q a).val i.succ = vfAt (replace 0 p x) i.succ
      exact (congrArg (fun z : Point (M := M) (n + 1) l => vfAt z i.succ) ha).trans
        (by simp [replace, vfAt, Fin.succ_ne_zero])
    obtain ⟨d, hd, _⟩ := vertical_rvGraph_transfer f hAE T hT a b he ht
    refine ⟨d, ?_⟩
    have hd' : (⟨d.val, hAE d.property⟩ : E) = T.inverseMap b := Subtype.ext hd
    change (T.toMap ⟨d.val, hAE d.property⟩).val = b.val
    rw [hd', T.apply_inverse]
  · intro b c he ht
    obtain ⟨a, ha⟩ := b.property
    obtain ⟨d, hd⟩ := c.property
    have he' : SameRV (T.toMap ⟨a.val, hAE a.property⟩).val (q d).val := by
      change SameRV (q a).val (q d).val
      exact (congrArg₂ (fun p q : Point (M := M) (n + 1) l => SameRV p q) ha hd).mpr he
    have ht' : TailEq (T.toMap ⟨a.val, hAE a.property⟩).val (q d).val := by
      change TailEq (q a).val (q d).val
      exact (congrArg₂ (fun p q : Point (M := M) (n + 1) l => TailEq p q) ha hd).mpr ht
    obtain ⟨e, heval, hef⟩ := vertical_rvGraph_transfer f hAE T hT a (q d) he' ht'
    change e.val = (T.inverseMap (T.toMap ⟨d.val, hAE d.property⟩)).val at heval
    rw [T.inverse_apply] at heval
    have hed : e = d := Subtype.ext heval
    have hfd : (f d).val.2 = (f a).val.2 := hed ▸ hef
    have hb : Map.toImage q a = b := Subtype.ext ha
    have hc : Map.toImage q d = c := Subtype.ext hd
    change Map.transportImage q f hq b = Map.transportImage q f hq c
    rw [← hb, ← hc, Map.transportImage_apply, Map.transportImage_apply]
    apply Subtype.ext
    exact Prod.ext (Subsingleton.elim _ _) hfd.symm

/-- After preparation in the head direction, descend the function and its
domain indicator, prepare them in lower dimension, and lift the actual
lower-dimensional chain to the full ambient domain. -/
theorem complete_head_preparation (ih : RVPreparation (M := M) S n)
    {B D : DefSet (M := M) S (n + 1) m}
    (hB : IsRVPullback (carrier B)) (hAll : AllTagged B)
    (hDB : carrier D ⊆ carrier B) (hD : HeadSaturated (carrier D))
    (f : Map D (PresentedSet.univ (pointSpace (M := M) 0 k) S))
    (hf : ∀ a b : D, SameRV a.val b.val → TailEq a.val b.val → f a = f b) :
    ∃ r : ℕ, ∃ E : DefSet (M := M) S (n + 1) r, ∃ W : SpecialBijection B E,
      W.chain.Alternating (some false) ∧ IsRVPullback (carrier E) ∧
      ∀ b c : E, SameRV b.val c.val →
        ((W.inverseMap b).val ∈ carrier D ↔ (W.inverseMap c).val ∈ carrier D) ∧
        ∀ a d : D, a.val = (W.inverseMap b).val → d.val = (W.inverseMap c).val →
          (f a).val.2 = (f d).val.2 := by
  let L := headImage B
  let K := headImage D
  have hKL : carrier K ⊆ carrier L := headImage_mono hDB
  let g := headDescend f hf
  let g' := Map.extend g (constantRVMap L k) hKL
  let flag := membershipMap L K
  let pair := pairRVMaps flag g'
  obtain ⟨t, C, T, hTa, _, hpair⟩ := ih L (some false)
    (fun _ => headImage_allTagged B hAll) pair
  obtain ⟨j, hj⟩ := hAll 0
  let ρ : Fin (1 + m) → Fin m := Fin.append (fun _ : Fin 1 => j) id
  let q : Map B L := Map.toImage (headKeyMap B)
  have hkey (b : B) : dropHead ρ b.val = (q b).val :=
    (dropHead_headTag b.val j (hj b.val b.property)).trans (headKeyMap_apply B b).symm
  have hsub : ∀ p ∈ carrier B, dropHead ρ p ∈ carrier L := by
    intro p hp
    exact (hkey ⟨p, hp⟩).symm ▸ (q ⟨p, hp⟩).property
  obtain ⟨r, E, σ, V, hVa, hV, hcomm, _⟩ :=
    T.chain.lift_dropHead_compatible B ρ hsub (some false) hTa
  let W : SpecialBijection B E := ⟨V, V.alternating_none (some false) hVa⟩
  have hproj (b : B) : dropHead σ (W.toMap b).val = (T.toMap (q b)).val := by
    have he : (⟨dropHead ρ b.val, hsub _ b.property⟩ : L) = q b := Subtype.ext (hkey b)
    exact (hcomm b).trans (congrArg (fun z : L => (T.toMap z).val) he)
  have hpair' (b c : E) (he : SameRV b.val c.val) :
      SameRV (pair (q (W.inverseMap b))).val (pair (q (W.inverseMap c))).val := by
    have hb : (T.toMap (q (W.inverseMap b))).val = dropHead σ b.val :=
      (hproj (W.inverseMap b)).symm.trans (congrArg (dropHead σ) (congrArg Subtype.val (W.apply_inverse b)))
    have hc : (T.toMap (q (W.inverseMap c))).val = dropHead σ c.val :=
      (hproj (W.inverseMap c)).symm.trans (congrArg (dropHead σ) (congrArg Subtype.val (W.apply_inverse c)))
    have hlow : SameRV (T.toMap (q (W.inverseMap b))).val (T.toMap (q (W.inverseMap c))).val := by
      rw [hb, hc]
      exact sameRV_dropHead σ he
    have hh := hpair (T.toMap (q (W.inverseMap b))) (T.toMap (q (W.inverseMap c))) hlow
    change SameRV (pair (T.inverseMap (T.toMap (q (W.inverseMap b))))).val
      (pair (T.inverseMap (T.toMap (q (W.inverseMap c))))).val at hh
    simpa only [T.inverse_apply] using hh
  have hg (b : E) (a : D) (ha : a.val = (W.inverseMap b).val) :
      g' (q (W.inverseMap b)) = f a := by
    let aK : K := Map.toImage (headKeyMap D) a
    have he : q (W.inverseMap b) = (⟨aK.val, hKL aK.property⟩ : L) := by
      apply Subtype.ext
      exact (headKeyMap_apply B (W.inverseMap b)).trans
        ((congrArg headKey ha.symm).trans (headKeyMap_apply D a).symm)
    rw [he]
    exact (Map.extend_apply g (constantRVMap L k) hKL aK).trans (headDescend_apply f hf a)
  refine ⟨r, E, W, hVa, W.preserves_pullback hB, ?_⟩
  intro b c he
  have hh := ((sameRV_iff _ _).mp (hpair' b c he)).2
  constructor
  · have hflag := congrFun hh (Fin.castAdd k (0 : Fin 1))
    change Fin.append (flag (q (W.inverseMap b))).val.2 (g' (q (W.inverseMap b))).val.2
      (Fin.castAdd k 0) =
      Fin.append (flag (q (W.inverseMap c))).val.2 (g' (q (W.inverseMap c))).val.2
      (Fin.castAdd k 0) at hflag
    simp only [Fin.append_left] at hflag
    have hm := (membershipMap_eq_iff L K (q (W.inverseMap b)) (q (W.inverseMap c))).mp hflag
    change ((q (W.inverseMap b)).val ∈ carrier (headImage D) ↔
      (q (W.inverseMap c)).val ∈ carrier (headImage D)) at hm
    have hkeys := congrArg₂
      (fun p q : Point (M := M) n (1 + m) => p ∈ carrier (headImage D) ↔ q ∈ carrier (headImage D))
      (headKeyMap_apply B (W.inverseMap b)) (headKeyMap_apply B (W.inverseMap c))
    have hm' := hkeys.mp hm
    exact (headKey_mem_iff hD (W.inverseMap b).val).trans
      (hm'.trans (headKey_mem_iff hD (W.inverseMap c).val).symm)
  · intro a d ha hd
    have hga := hg b a ha
    have hgd := hg c d hd
    funext i
    have hv := congrFun hh (Fin.natAdd 1 i)
    change Fin.append (flag (q (W.inverseMap b))).val.2 (g' (q (W.inverseMap b))).val.2
      (Fin.natAdd 1 i) =
      Fin.append (flag (q (W.inverseMap c))).val.2 (g' (q (W.inverseMap c))).val.2
      (Fin.natAdd 1 i) at hv
    simpa only [Fin.append_right, hga, hgd] using hv

theorem restrict_prepared_map {A D : DefSet (M := M) S (n + 1) m}
    {B : DefSet (M := M) S (n + 1) l}
    (hDA : carrier D ⊆ carrier A) (T : SpecialBijection A B)
    (hB : IsRVPullback (carrier B)) (previous : Option Bool) (hTa : T.chain.Alternating previous)
    (f : Map D (PresentedSet.univ (pointSpace (M := M) 0 k) S))
    (hc : ∀ b c : B, SameRV b.val c.val →
      ((T.inverseMap b).val ∈ carrier D ↔ (T.inverseMap c).val ∈ carrier D) ∧
      ∀ d e : D, d.val = (T.inverseMap b).val → e.val = (T.inverseMap c).val →
        (f d).val.2 = (f e).val.2) :
    ∃ E : DefSet (M := M) S (n + 1) l, ∃ V : SpecialBijection D E,
      V.chain.Alternating previous ∧ IsRVPullback (carrier E) ∧
        Contractible (Map.comp f V.inverseMap) := by
  obtain ⟨E, V, hVa, hEB, hImage, hcomm⟩ := T.restrict_at D hDA previous hTa
  have hInv (b : E) : (T.inverseMap ⟨b.val, hEB b.property⟩).val = (V.inverseMap b).val := by
    have he : T.toMap ⟨(V.inverseMap b).val, hDA (V.inverseMap b).property⟩ =
        (⟨b.val, hEB b.property⟩ : B) := by
      apply Subtype.ext
      exact (hcomm (V.inverseMap b)).symm.trans (congrArg Subtype.val (V.apply_inverse b))
    rw [← he, T.inverse_apply]
  refine ⟨E, V, hVa, (isRVPullback_iff _).mpr ?_, ?_⟩
  · intro p hp q he
    let b : B := ⟨p, hEB hp⟩
    have hqB := (isRVPullback_iff _).mp hB p b.property q he
    let c : B := ⟨q, hqB⟩
    have hbD : (T.inverseMap b).val ∈ carrier D := by
      have hb := hInv ⟨p, hp⟩
      exact hb.symm ▸ (V.inverseMap ⟨p, hp⟩).property
    have hcD := (hc b c he).1.mp hbD
    have hqI : q ∈ {z | ∃ d : D, (T.toMap ⟨d.val, hDA d.property⟩).val = z} := by
      refine ⟨⟨(T.inverseMap c).val, hcD⟩, ?_⟩
      have heq : (⟨(T.inverseMap c).val, hDA hcD⟩ : A) = T.inverseMap c := Subtype.ext rfl
      rw [heq, T.apply_inverse]
    exact hImage.symm ▸ hqI
  · intro b c he
    have hv := (hc ⟨b.val, hEB b.property⟩ ⟨c.val, hEB c.property⟩ he).2
      (V.inverseMap b) (V.inverseMap c) (hInv b).symm (hInv c).symm
    exact (sameRV_iff _ _).mpr ⟨fun i => i.elim0, hv⟩

/-- The successor construction at a canonical boundary. Every Section 5
existence step here is constructed from the lower-dimensional induction. -/
theorem tagged_rvMap_preparation {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (h00 : M ⊨ Axioms.ACVF00) (v : Valuation (VF (M := M)) Γ)
    (hv : ∀ x y : VF (M := M), VFValued.predV x y ↔ v x ≤ v y)
    (hObstacles : UniformVerticalObstacles v S n) (ih : RVPreparation (M := M) S n)
    (A : DefSet (M := M) S (n + 1) m) (hAll : AllTagged A)
    (f : Map A (PresentedSet.univ (pointSpace (M := M) 0 k) S)) :
    ∃ r : ℕ, ∃ B : DefSet (M := M) S (n + 1) r, ∃ V : SpecialBijection A B,
      V.chain.Alternating (some false) ∧ IsRVPullback (carrier B) ∧
        Contractible (Map.comp f V.inverseMap) := by
  let H : DefSet (M := M) S (n + 1) m :=
    PresentedSet.mk (hull (carrier A)) (hull_definable A)
  have hAH : carrier A ⊆ carrier H := subset_hull _
  have hH : IsRVPullback (carrier H) := hull_idem _
  obtain ⟨R, d, hd, hO⟩ := hObstacles (rvGraph f) H hH
  obtain ⟨l, C, T, hTa, hTc, hTl, htags, hC, hz⟩ :=
    vertical_centralize h00 ih d H R hH (allTagged_hull A hAll) hd
  have hRel := vertical_relation_of_zero_obstacles v hv (carrier (rvGraph f)) R hO T hTc hC hz
  let q := Map.comp T.toMap (Map.inclusion hAH)
  let hq := restricted_map_injective hAH T
  let D := Map.image q
  let g := Map.transportImage q f hq
  obtain ⟨hD, hg⟩ := vertical_graph_image f hAH T hC hRel
  have hDC : carrier D ⊆ carrier C := by
    rintro p ⟨a, ha⟩
    exact ha ▸ (q a).property
  obtain ⟨r, E, W, hWa, hE, hw⟩ := complete_head_preparation ih hC htags hDC hD g hg
  have hVa := T.chain.append_alternating W.chain (some false) hTa (by simpa only [hTl] using hWa)
  let V := T.comp W ((T.chain.append W.chain).alternating_none (some false) hVa)
  have hprepared : ∀ b c : E, SameRV b.val c.val →
      ((V.inverseMap b).val ∈ carrier A ↔ (V.inverseMap c).val ∈ carrier A) ∧
      ∀ a d : A, a.val = (V.inverseMap b).val → d.val = (V.inverseMap c).val →
        (f a).val.2 = (f d).val.2 := by
    intro b c he
    obtain ⟨hm, hvalue⟩ := hw b c he
    have hInv (b : E) : V.inverseMap b = T.inverseMap (W.inverseMap b) :=
      SpecialBijection.comp_inverseMap T W V.alternating b
    constructor
    · rw [hInv b, hInv c]
      exact (restricted_image_mem_iff hAH T (W.inverseMap b)).symm.trans
        (hm.trans (restricted_image_mem_iff hAH T (W.inverseMap c)))
    · intro a d ha hd
      have hqa : (q a).val = (W.inverseMap b).val := by
        have hi : (⟨a.val, hAH a.property⟩ : H) = T.inverseMap (W.inverseMap b) := by
          apply Subtype.ext
          exact ha.trans (congrArg Subtype.val (hInv b))
        change (T.toMap ⟨a.val, hAH a.property⟩).val = _
        rw [hi, T.apply_inverse]
      have hqd : (q d).val = (W.inverseMap c).val := by
        have hi : (⟨d.val, hAH d.property⟩ : H) = T.inverseMap (W.inverseMap c) := by
          apply Subtype.ext
          exact hd.trans (congrArg Subtype.val (hInv c))
        change (T.toMap ⟨d.val, hAH d.property⟩).val = _
        rw [hi, T.apply_inverse]
      have hh := hvalue (Map.toImage q a) (Map.toImage q d) hqa hqd
      change (g (Map.toImage q a)).val.2 = (g (Map.toImage q d)).val.2 at hh
      simpa only [g, Map.transportImage_apply] using hh
  obtain ⟨B, U, hUa, hB, hf⟩ := restrict_prepared_map hAH V hE (some false) hVa f hprepared
  exact ⟨r, B, U, hUa, hB, hf⟩

theorem rvPreparation_zero : RVPreparation (M := M) S 0 := by
  intro a k D previous _ f
  exact zero_map_preparation_at_boundary D previous f

theorem rvPreparation_succ {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (h00 : M ⊨ Axioms.ACVF00) (v : Valuation (VF (M := M)) Γ)
    (hv : ∀ x y : VF (M := M), VFValued.predV x y ↔ v x ≤ v y)
    (hObstacles : UniformVerticalObstacles v S n) (ih : RVPreparation (M := M) S n) :
    RVPreparation (M := M) S (n + 1) := by
  intro m k A previous hTags f
  by_cases hprev : previous = some false
  · obtain ⟨r, B, V, hVa, hB, hf⟩ := tagged_rvMap_preparation h00 v hv hObstacles ih A (hTags hprev) f
    exact ⟨r, B, V, by simpa only [hprev] using hVa, hB, hf⟩
  · let U := SpecialBijection.canonical A
    let g := Map.comp f U.inverseMap
    obtain ⟨r, B, V, hVa, hB, hf⟩ := tagged_rvMap_preparation h00 v hv hObstacles ih
      (canonicalImage A) (canonicalImage_allTagged A) g
    have hTa : (U.chain.append V.chain).Alternating previous := ⟨hprev, hVa⟩
    let T := U.comp V ((U.chain.append V.chain).alternating_none previous hTa)
    refine ⟨r, B, T, hTa, hB, ?_⟩
    intro b c he
    change SameRV (f (T.inverseMap b)).val (f (T.inverseMap c)).val
    rw [SpecialBijection.comp_inverseMap, SpecialBijection.comp_inverseMap]
    exact hf b c he

theorem rvPreparation_all {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (h00 : M ⊨ Axioms.ACVF00) (v : Valuation (VF (M := M)) Γ)
    (hv : ∀ x y : VF (M := M), VFValued.predV x y ↔ v x ≤ v y)
    (hObstacles : ∀ n, UniformVerticalObstacles v S n) (N : ℕ) :
    RVPreparation (M := M) S N := by
  induction N with
  | zero => exact rvPreparation_zero
  | succ n ih => exact rvPreparation_succ h00 v hv (hObstacles n) ih

end SpecialTransformations.Section5
