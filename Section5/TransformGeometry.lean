import Section5.Core

/-!
# Special bijections preserve RV-pullbacks

The assertion immediately after Definition 5.1. The proof treats the zero
RV fibre as a singleton; it does not impose a nonzero-coordinate hypothesis.
Comparisons below use the paper's RV order directly, through `iLe`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer

namespace SpecialTransformations.Section5

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

private theorem rv_zero_iff (a : VF (M := M)) : rv a = rv (0 : VF (M := M)) ↔ a = 0 := by
  constructor
  · intro h
    exact (CanonicalRV.encodedRv_zero_iff a).mp
      ((congrArg Subtype.val h).trans (RVCalc.rv_zero_eq hM))
  · rintro rfl
    rfl

private theorem rv_sub_strict (a b : VF (M := M)) (ha : a ≠ 0) (hb : rv b = rv a) :
    ¬ iLe (rv (a - b)).val (rv a).val := by
  have hb0 : b ≠ 0 := by
    intro he
    apply ha
    apply (rv_zero_iff a).mp
    simpa [he] using hb.symm
  have h := (CanonicalRV.encoded_eq_iff_close a.property b.property
    (fun he => hb0 (Subtype.ext he))).mp (congrArg Subtype.val hb.symm)
  change ¬ iLe (rv (a - b)).val (rv b).val at h
  rwa [hb] at h

private theorem rv_add_small (a z : VF (M := M)) (ha : a ≠ 0)
    (hz : ¬ iLe (rv z).val (rv a).val) : rv (a + z) = rv a := by
  apply Subtype.ext
  apply (CanonicalRV.encoded_eq_iff_close (a + z).property a.property
    (fun he => ha (Subtype.ext he))).mpr
  change ¬ iLe (rv ((a + z) - a)).val (rv a).val
  have he : (a + z) - a = z := by abel
  rwa [he]

/-- Restore the original RV fibre after a centripetal subtraction, allowing
the restored centre to vary within that original fibre. -/
theorem rv_add_back (a b c z : VF (M := M))
    (hb : rv b = rv a) (hc : rv c = rv a) (hz : rv z = rv (a - b)) :
    rv (z + c) = rv a := by
  by_cases ha : a = 0
  · subst a
    have hb0 := (rv_zero_iff b).mp hb
    have hc0 := (rv_zero_iff c).mp hc
    have hz0 : z = 0 := (rv_zero_iff z).mp (by rwa [hb0, sub_self] at hz)
    rw [hz0, hc0, zero_add]
  · have hc0 : c ≠ 0 := by
      intro he
      apply ha
      apply (rv_zero_iff a).mp
      simpa [he] using hc.symm
    have hs : ¬ iLe (rv z).val (rv c).val := by
      rw [hz, hc]
      exact rv_sub_strict a b ha hb
    have he : rv (z + c) = rv c := by
      rw [add_comm z c]
      exact rv_add_small c z hc0 hs
    exact he.trans hc

namespace FocusGeometry

variable {n m : ℕ} {A : Set (Point (M := M) n m)} {j : Fin n} {k : Fin m}

/-- The strict-radius part of the printed C-sharp codomain, on a nonzero
targeted fibre. The zero fibre is treated separately as a singleton. -/
theorem eta_target_strict (D : FocusGeometry A j k) (a : Point (M := M) n m)
    (ha : a ∈ A ∩ D.locus) (ha0 : a.1 j ≠ 0) :
    ¬ iLe (rv ((D.eta a).1 j)).val (rv (a.1 j)).val := by
  have he : (D.eta a).1 j = a.1 j - D.center a := by simp [eta, ha.2, replace]
  rw [he]
  exact rv_sub_strict _ _ ha0 (D.center_sameRV a ha)

/-- The geometric preservation assertion needs no additional choice,
definability, characteristic or saturation hypothesis. -/
theorem image_pullback (D : FocusGeometry A j k) (hA : IsRVPullback A) :
    IsRVPullback (D.eta '' A) := by
  apply (isRVPullback_iff _).mpr
  rintro _ ⟨a, ha, rfl⟩ q hq
  obtain ⟨hv, ht⟩ := (sameRV_iff (D.eta a) q).mp hq
  have hlabels : a.2 = q.2 := (D.eta_labels a).symm.trans ht
  have hmake (v : VF (M := M)) (he : rv v = rv (a.1 j)) :
      SameRV a (replace j q v) := by
    apply (sameRV_iff _ _).mpr
    refine ⟨?_, hlabels⟩
    intro i
    by_cases hi : i = j
    · subst i
      simpa [replace] using he.symm
    · simpa [replace, hi] using
        (congrArg rv (D.eta_other a i hi)).symm.trans (hv i)
  by_cases hac : a ∈ D.locus
  · let r := replace j q (a.1 j)
    have har : SameRV a r := hmake _ rfl
    have hrA : r ∈ A := (isRVPullback_iff A).mp hA a ha r har
    have hrC : r ∈ D.locus := (mem_iff_sameRV D.locus_pullback har).mp hac
    have hb := D.center_sameRV a ⟨ha, hac⟩
    have hc : rv (D.center r) = rv (a.1 j) := by
      simpa [r, replace] using D.center_sameRV r ⟨hrA, hrC⟩
    have hz : rv (q.1 j) = rv (a.1 j - D.center a) := by
      simpa [eta, replace, hac] using (hv j).symm
    let x := replace j q (q.1 j + D.center r)
    have hax : SameRV a x := hmake _ (rv_add_back _ _ _ _ hb hc hz)
    have hxA : x ∈ A := (isRVPullback_iff A).mp hA a ha x hax
    have hxC : x ∈ D.locus := (mem_iff_sameRV D.locus_pullback hax).mp hac
    have hrow : erase j x = erase j r := by
      refine Prod.ext ?_ ?_
      · funext i
        by_cases hi : i = j
        · subst i
          simp [erase, replace]
        · simp [x, r, erase, replace, hi]
      · rfl
    have hcenter := D.independent x ⟨hxA, hxC⟩ r ⟨hrA, hrC⟩ hrow
    refine ⟨x, hxA, ?_⟩
    refine Prod.ext ?_ ?_
    · funext i
      by_cases hi : i = j
      · subst i
        rw [eta, if_pos hxC]
        have href : (replace j x (x.1 j - D.center x)).1 j = x.1 j - D.center x := by
          simp [replace]
        rw [href, hcenter]
        have hxj : x.1 j = q.1 j + D.center r := by simp [x, replace]
        rw [hxj]
        exact add_sub_cancel_right _ _
      · exact (D.eta_other x i hi).trans (by simp [x, replace, hi])
    · simpa [x, replace] using D.eta_labels x
  · have haq : SameRV a q := by simpa [eta, hac] using hq
    have hqA := (isRVPullback_iff A).mp hA a ha q haq
    have hqC : q ∉ D.locus := fun hc => hac ((mem_iff_sameRV D.locus_pullback haq).mpr hc)
    exact ⟨q, hqA, by simp [eta, hqC]⟩

end FocusGeometry

namespace Focus

variable {S : Set M} {n m : ℕ} {A : DefSet (M := M) S n m} {j : Fin n} {k : Fin m}

theorem etaImage_carrier (D : Focus A j k) :
    carrier D.etaImage = D.toFocusGeometry.eta '' carrier A := by
  ext q
  exact ⟨fun ⟨a, he⟩ => ⟨a.val, a.property, he⟩,
    fun ⟨a, ha, he⟩ => ⟨⟨a, ha⟩, he⟩⟩

theorem etaImage_pullback (D : Focus A j k) (hA : IsRVPullback (carrier A)) :
    IsRVPullback (carrier D.etaImage) := by
  rw [etaImage_carrier]
  exact D.toFocusGeometry.image_pullback hA

end Focus

namespace Primitive

variable {S : Set M} {n m l : ℕ} {A : DefSet (M := M) S n m} {B : DefSet (M := M) S n l}

theorem preserves_pullback (p : Primitive S n A B) (hA : IsRVPullback (carrier A)) :
    IsRVPullback (carrier B) := by
  cases p with
  | canonical A =>
    rw [canonicalImage_carrier]
    exact canonical_image_pullback hA
  | centripetal D => exact D.etaImage_pullback hA

end Primitive

theorem Chain.preserves_pullback {S : Set M} {n m l : ℕ}
    {A : DefSet (M := M) S n m} {B : DefSet (M := M) S n l}
    (T : Chain S n A B) (hA : IsRVPullback (carrier A)) : IsRVPullback (carrier B) := by
  induction T with
  | nil A => exact hA
  | cons p tail ih => exact ih (p.preserves_pullback hA)

/-- The assertion after Definition 5.1, with full finite mixed arities. -/
theorem SpecialBijection.preserves_pullback {S : Set M} {n m l : ℕ}
    {A : DefSet (M := M) S n m} {B : DefSet (M := M) S n l}
    (T : SpecialBijection A B) (hA : IsRVPullback (carrier A)) :
    IsRVPullback (carrier B) := T.chain.preserves_pullback hA

end SpecialTransformations.Section5

/-!
## Inverse fibres in one VF coordinate

Retained labels recover the original RV class. On a fixed final-label
slice, a unary special bijection preserves differences of VF coordinates.
These two facts give the open-ball statement of Remark 5.3.
-/

namespace SpecialTransformations.Section5

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

namespace FocusGeometry

theorem sameRV_of_eta {n m : ℕ} {A : Set (Point (M := M) n m)} {j : Fin n} {k : Fin m}
    (D : FocusGeometry A j k) {a b : Point (M := M) n m} (ha : a ∈ A) (hb : b ∈ A)
    (he : SameRV (D.eta a) (D.eta b)) : SameRV a b := by
  obtain ⟨hv, ht⟩ := (sameRV_iff _ _).mp he
  have hab : a.2 = b.2 := (D.eta_labels a).symm.trans (ht.trans (D.eta_labels b))
  apply (sameRV_iff _ _).mpr
  refine ⟨fun i => ?_, hab⟩
  by_cases hi : i = j
  · subst i
    exact (D.tagged a ha).symm.trans ((congrFun hab k).trans (D.tagged b hb))
  · simpa only [D.eta_other a i hi, D.eta_other b i hi] using hv i

theorem unary_sub {m : ℕ} {A : Set (Point (M := M) 1 m)} {j : Fin 1} {k : Fin m}
    (D : FocusGeometry A j k) {a b : Point (M := M) 1 m} (ha : a ∈ A) (hb : b ∈ A)
    (ht : a.2 = b.2) : (D.eta a).1 0 - (D.eta b).1 0 = a.1 0 - b.1 0 := by
  have hj : j = 0 := Subsingleton.elim _ _
  subst j
  have hab : SameRV a b := by
    apply (sameRV_iff _ _).mpr
    refine ⟨?_, ht⟩
    intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact (D.tagged a ha).symm.trans ((congrFun ht k).trans (D.tagged b hb))
  have herase : erase 0 a = erase 0 b := by
    refine Prod.ext ?_ ht
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp [erase, replace]
  by_cases hac : a ∈ D.locus
  · have hbc := (mem_iff_sameRV D.locus_pullback hab).mp hac
    have hc := D.independent a ⟨ha, hac⟩ b ⟨hb, hbc⟩ herase
    have haeta : (D.eta a).1 0 = a.1 0 - D.center a := by simp [eta, hac, replace]
    have hbeta : (D.eta b).1 0 = b.1 0 - D.center b := by simp [eta, hbc, replace]
    rw [haeta, hbeta, hc]
    abel
  · have hbc : b ∉ D.locus := fun h => hac ((mem_iff_sameRV D.locus_pullback hab).mpr h)
    simp [eta, hac, hbc]

end FocusGeometry

/-- A typed coordinate accessor keeps the shared VF field instance visible
when a point is carried by a definable presentation. -/
def vfAt {n m : ℕ} (p : Point (M := M) n m) (i : Fin n) : VF (M := M) := p.1 i

/-- An ordinary open ball in the VF coordinate, with fixed RV coordinates.
The radius is finite: its VF representative is explicitly nonzero. -/
def IsUnaryOpenPolydisc {m : ℕ} (E : Set (Point (M := M) 1 m)) : Prop :=
  ∃ c r : VF (M := M), r ≠ 0 ∧ ∃ t : Fin m → RV (M := M),
    E = {p | ¬ iLe (rv (vfAt p 0 - c)).val (rv r).val ∧ p.2 = t}

namespace Primitive

variable {S : Set M} {n m l : ℕ} {A : DefSet (M := M) S n m} {B : DefSet (M := M) S n l}

theorem labels_eq_of (p : Primitive S n A B) (a b : A)
    (he : (p.toMap a).val.2 = (p.toMap b).val.2) : a.val.2 = b.val.2 := by
  cases p with
  | canonical A =>
    change (SpecialTransformations.Section5.canonical a.val).2 =
      (SpecialTransformations.Section5.canonical b.val).2 at he
    funext i
    simpa using congrFun he (Fin.natAdd n i)
  | centripetal D =>
    change (D.toFocusGeometry.eta a.val).2 = (D.toFocusGeometry.eta b.val).2 at he
    simpa only [FocusGeometry.eta_labels] using he

theorem sameRV_of (p : Primitive S n A B) (a b : A)
    (he : SameRV (p.toMap a).val (p.toMap b).val) : SameRV a.val b.val := by
  cases p with
  | canonical A => exact (canonical_sameRV_iff _ _).mp he
  | centripetal D => exact D.toFocusGeometry.sameRV_of_eta a.property b.property he

theorem unary_sub {A : DefSet (M := M) S 1 m} {B : DefSet (M := M) S 1 l}
    (p : Primitive S 1 A B) (a b : A)
    (he : (p.toMap a).val.2 = (p.toMap b).val.2) :
    vfAt (p.toMap a).val 0 - vfAt (p.toMap b).val 0 = vfAt a.val 0 - vfAt b.val 0 := by
  cases p with
  | canonical A => rfl
  | centripetal D =>
    exact D.toFocusGeometry.unary_sub a.property b.property
      ((D.toFocusGeometry.eta_labels a.val).symm.trans
        (he.trans (D.toFocusGeometry.eta_labels b.val)))

end Primitive

namespace Chain

variable {S : Set M} {n m l : ℕ} {A : DefSet (M := M) S n m} {B : DefSet (M := M) S n l}

theorem labels_eq_of (T : Chain S n A B) (a b : A)
    (he : (T.toMap a).val.2 = (T.toMap b).val.2) : a.val.2 = b.val.2 := by
  induction T with
  | nil A => exact he
  | cons p tail ih => exact p.labels_eq_of a b (ih (p.toMap a) (p.toMap b) he)

theorem sameRV_of (T : Chain S n A B) (a b : A)
    (he : SameRV (T.toMap a).val (T.toMap b).val) : SameRV a.val b.val := by
  induction T with
  | nil A => exact he
  | cons p tail ih => exact p.sameRV_of a b (ih (p.toMap a) (p.toMap b) he)

theorem unary_sub {A : DefSet (M := M) S 1 m} {B : DefSet (M := M) S 1 l}
    (T : Chain S 1 A B) (a b : A)
    (he : (T.toMap a).val.2 = (T.toMap b).val.2) :
    vfAt (T.toMap a).val 0 - vfAt (T.toMap b).val 0 = vfAt a.val 0 - vfAt b.val 0 := by
  induction T with
  | nil A => rfl
  | cons p tail ih =>
    exact (ih (p.toMap a) (p.toMap b) he).trans
      (p.unary_sub a b (tail.labels_eq_of _ _ he))

end Chain

namespace SpecialBijection

variable {S : Set M} {n m l : ℕ} {A : DefSet (M := M) S n m} {B : DefSet (M := M) S n l}

/-- Inverse special bijections are contractible, in every finite arity. -/
theorem inverse_contractible (T : SpecialBijection A B) : Contractible T.inverseMap := by
  intro a b he
  apply T.chain.sameRV_of (T.inverseMap a) (T.inverseMap b)
  change SameRV (T.toMap (T.inverseMap a)).val (T.toMap (T.inverseMap b)).val
  simpa only [T.apply_inverse] using he

def inverseFibre {A : DefSet (M := M) S 1 m} {B : DefSet (M := M) S 1 l}
    (T : SpecialBijection A B) (b : B) : Set (Point (M := M) 1 m) :=
  {p | ∃ a : A, a.val = p ∧ SameRV (T.toMap a).val b.val}

/-- Remark 5.3. The radius uses the reversed, multiplicative valuation order:
the displayed strict inequality is precisely an open ball in that order.
Its RV labels are fixed, and it lies in the original RV-polydisc. -/
theorem unary_inverse_fibre {A : DefSet (M := M) S 1 m} {B : DefSet (M := M) S 1 l}
    {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VF (M := M)) Γ)
    (hv : ∀ x y : VF (M := M), VFValued.predV x y ↔ v x ≤ v y)
    (T : SpecialBijection A B) (hB : IsRVPullback (carrier B)) (b : B)
    (hb : vfAt b.val 0 ≠ 0) :
    T.inverseFibre b =
      {p | v (vfAt p 0 - vfAt (T.inverseMap b).val 0) < v (vfAt b.val 0) ∧
        p.2 = (T.inverseMap b).val.2} ∧
    T.inverseFibre b ⊆ {p | SameRV p (T.inverseMap b).val} := by
  have hlabel (a c : B) (he : a.val.2 = c.val.2) :
      (T.inverseMap a).val.2 = (T.inverseMap c).val.2 := by
    apply T.chain.labels_eq_of (T.inverseMap a) (T.inverseMap c)
    change (T.toMap (T.inverseMap a)).val.2 = (T.toMap (T.inverseMap c)).val.2
    simpa only [T.apply_inverse] using he
  have hdiff (a c : B) (he : a.val.2 = c.val.2) :
      vfAt (T.inverseMap a).val 0 - vfAt (T.inverseMap c).val 0 =
        vfAt a.val 0 - vfAt c.val 0 := by
    have hout : (T.chain.toMap (T.inverseMap a)).val.2 =
        (T.chain.toMap (T.inverseMap c)).val.2 := by
      change (T.toMap (T.inverseMap a)).val.2 = (T.toMap (T.inverseMap c)).val.2
      simpa only [T.apply_inverse] using he
    have hh := T.chain.unary_sub (T.inverseMap a) (T.inverseMap c) hout
    change vfAt (T.toMap (T.inverseMap a)).val 0 - vfAt (T.toMap (T.inverseMap c)).val 0 = _ at hh
    simpa only [T.apply_inverse] using hh.symm
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
    · rintro ⟨a, rfl, he⟩
      obtain ⟨hvv, htt⟩ := (sameRV_iff _ _).mp he
      have hai : T.inverseMap (T.toMap a) = a := T.inverse_apply a
      have hd := hdiff (T.toMap a) b htt
      have hl := hlabel (T.toMap a) b htt
      rw [hai] at hd hl
      exact ⟨by rw [hd]; exact (hclose _).mp (hvv 0), hl⟩
    · rintro ⟨hpv, hpt⟩
      let q : Point (M := M) 1 l :=
        (![vfAt p 0 - vfAt (T.inverseMap b).val 0 + vfAt b.val 0], b.val.2)
      have hq : SameRV q b.val := by
        apply (sameRV_iff _ _).mpr
        refine ⟨?_, rfl⟩
        intro i
        have hi : i = 0 := Subsingleton.elim _ _
        subst i
        apply (hclose _).mpr
        simpa only [q, vfAt, Matrix.cons_val_zero, add_sub_cancel_right] using hpv
      have hqB : q ∈ carrier B := (isRVPullback_iff _).mp hB b.val b.property q hq.symm
      let c : B := ⟨q, hqB⟩
      have hc : (T.inverseMap c).val = p := by
        refine Prod.ext ?_ ?_
        · funext i
          have hi : i = 0 := Subsingleton.elim _ _
          subst i
          have hd := hdiff c b rfl
          change vfAt (T.inverseMap c).val 0 - vfAt (T.inverseMap b).val 0 =
            vfAt p 0 - vfAt (T.inverseMap b).val 0 + vfAt b.val 0 - vfAt b.val 0 at hd
          have hd' : vfAt (T.inverseMap c).val 0 - vfAt (T.inverseMap b).val 0 =
              vfAt p 0 - vfAt (T.inverseMap b).val 0 := by simpa only [add_sub_cancel_right] using hd
          have hevf : vfAt (T.inverseMap c).val 0 = vfAt p 0 := sub_left_inj.mp hd'
          exact hevf
        · exact (hlabel c b rfl).trans hpt.symm
      exact ⟨T.inverseMap c, hc, by simpa only [T.apply_inverse] using hq⟩
  · rintro p ⟨a, rfl, he⟩
    have hh := T.inverse_contractible (T.toMap a) b he
    change SameRV a.val (T.inverseMap b).val
    simpa only [T.inverse_apply] using hh

/-- Remark 5.3 in the released language, without an auxiliary valuation
hypothesis. The final RV fibre is nondegenerate; the full input set need
not itself be an RV-pullback. -/
theorem remark_5_3 {A : DefSet (M := M) S 1 m} {B : DefSet (M := M) S 1 l}
    (T : SpecialBijection A B) (hB : IsRVPullback (carrier B)) (b : B)
    (hb : vfAt b.val 0 ≠ 0) :
    IsUnaryOpenPolydisc (T.inverseFibre b) ∧
      T.inverseFibre b ⊆ {p | SameRV p (T.inverseMap b).val} := by
  obtain ⟨Γ, hΓ, v, hv⟩ := VFValued.exists_valuation_predV (M := M)
  letI := hΓ
  obtain ⟨he, hs⟩ := T.unary_inverse_fibre v hv hB b hb
  refine ⟨⟨vfAt (T.inverseMap b).val 0, vfAt b.val 0, hb, (T.inverseMap b).val.2, ?_⟩, hs⟩
  rw [he]
  ext p
  apply and_congr ?_ Iff.rfl
  change v (vfAt p 0 - vfAt (T.inverseMap b).val 0) < v (vfAt b.val 0) ↔
    ¬ VFValued.predV (vfAt b.val 0) (vfAt p 0 - vfAt (T.inverseMap b).val 0)
  rw [hv, not_le]

end SpecialBijection
end SpecialTransformations.Section5

#check @SpecialTransformations.Section5.SpecialBijection.preserves_pullback
#print axioms SpecialTransformations.Section5.SpecialBijection.preserves_pullback
#check @SpecialTransformations.Section5.SpecialBijection.remark_5_3
#print axioms SpecialTransformations.Section5.SpecialBijection.remark_5_3
