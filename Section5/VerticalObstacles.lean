module

public import Section5.GeneralAssembly
public import Section3.ClosedClassCodes
public import Section3.FibrePromotion
public import Section3.NormalizationSaturation
public import Section4.FiniteCover
public import Mathlib.Data.Set.Card.Arithmetic

@[expose] public section

/-! The uniform obstacle family follows from unary QE and genuine saturation.
A finite real code for a closed ball makes the root-avoidance criterion first
order. A closed ball through two points of an open ball suffices for the
comparison, even if the open radius is not realized in the field. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace

open Classical FirstOrder FirstOrder.Language
open scoped BigOperators
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3

namespace SpecialTransformations.Section5

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n m k : ℕ}

local notation "N" => (@CanonicalStructure.normalize M sM)

private abbrev uCode (a : Fin n → M) (x : M) (ys : Fin k → M) :
    Fin (n + 1) ⊕ Fin k → M := Sum.elim (Fin.cons x a) ys

private abbrev uRaw (U : DefSet (M := M) S (n + 1) k) :=
  @DefinableGeometry.Space.preimage LRV M N (pointSpace (M := M) (n + 1) k) (carrier U)

private theorem uRaw_definable (U : DefSet (M := M) S (n + 1) k) :
    @Set.Definable M S LRV N (Fin (n + 1) ⊕ Fin k) (uRaw U) := setDefinable U

private theorem uRaw_iff (U : DefSet (M := M) S (n + 1) k)
    (a : Fin n → VF (M := M)) (x : VF (M := M)) (ys : Fin k → RV (M := M)) :
    uCode (fun i => (a i).val) x.val (fun i => (ys i).val) ∈ uRaw U ↔
      (Fin.cons x a, ys) ∈ carrier U := by
  let vs : Fin (n + 1) → M := Fin.cons x.val (fun i => (a i).val)
  have hs : ∀ i, iVF (vs i) := by
    intro i
    cases i using Fin.cases with
    | zero => exact x.property
    | succ i => exact (a i).property
  have hd : uCode (fun i => (a i).val) x.val (fun i => (ys i).val) ∈
      pDomain (pointSpace (M := M) (n + 1) k) := ⟨hs, fun i => (ys i).property⟩
  have he : pDecode (pointSpace (M := M) (n + 1) k) ⟨_, hd⟩ = (Fin.cons x a, ys) := by
    refine Prod.ext ?_ rfl
    funext i
    cases i using Fin.cases <;> rfl
  exact (@DefinableGeometry.Space.preimage_decode LRV M N (pointSpace (M := M) (n + 1) k)
    (carrier U) ⟨_, hd⟩).trans
    (Iff.of_eq (congrArg (fun p : Point (M := M) (n + 1) k => p ∈ carrier U) he))

private abbrev RawBall (b : Fin 3 → M) := @ClosedBallCodes.rawBall M N b

private theorem rawBall_iff (b : Fin 3 → M) (x : M) :
    x ∈ RawBall b ↔ x ∈ ClosedBallCodes.rawBall b :=
  Set.ext_iff.mp (ClosedBallCodes.rawBall_normalize b) x

private def controls (U : DefSet (M := M) S (n + 1) k)
    (R : Set ((Fin n → M) × M)) (a : Fin n → M) : Prop :=
  ∀ (b : Fin 3 → M) (x y : M) (ys : Fin k → M),
    x ∈ RawBall b → y ∈ RawBall b →
    (∀ c ∈ RawBall b, (a, c) ∉ R) →
    (uCode a x ys ∈ uRaw U ↔ uCode a y ys ∈ uRaw U)

private theorem controls_definable (U : DefSet (M := M) S (n + 1) k)
    (R : Set ((Fin n → M) × M)) (hR : @RawClosure.Tuple.RelationDefinable M N n S R) :
    @Set.Definable M S LRV N (Fin n) {a | controls U R a} := by
  let ballDef := @ClosedClassCodes.rawBall_definable M N S
  let UD := uRaw_definable U
  letI : LRV.Structure M := N
  let I := Fin n ⊕ (Fin 3 ⊕ (Fin 2 ⊕ Fin k))
  let bi (i : Fin 3) : I := .inr (.inl i)
  let xi (i : Fin 2) : I := .inr (.inr (.inl i))
  let yi (i : Fin k) : I := .inr (.inr (.inr i))
  have hb (i : Fin 2) := ballDef.preimage_comp
    (Sum.elim bi (fun _ : Fin 1 => xi i))
  have hu (i : Fin 2) := UD.preimage_comp
    (Sum.elim (Fin.cons (xi i) (Sum.inl : Fin n → I)) yi)
  have hr := hR.preimage_comp
    (Sum.elim (fun i => Sum.inl (Sum.inl i : I)) (Sum.inr : Fin 1 → I ⊕ Fin 1))
  have hc := ballDef.preimage_comp
    (Sum.elim (fun i => Sum.inl (bi i)) (Sum.inr : Fin 1 → I ⊕ Fin 1))
  have hd := (hc.himp hr.compl).forall_of_finite
  have hall := ((hb 0).inter ((hb 1).inter hd)).himp
    (((hu 0).himp (hu 1)).inter ((hu 1).himp (hu 0)))
  convert hall.forall_of_finite using 1
  ext a
  have reindex (z : I → M) (i : Fin 2) :
      z ∘ Sum.elim (Fin.cons (xi i) (Sum.inl : Fin n → I)) yi =
        uCode (z ∘ Sum.inl) (z (xi i)) (z ∘ yi) := by
    funext j
    cases j with
    | inl j => cases j using Fin.cases <;> rfl
    | inr j => rfl
  simp only [controls, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_inter_iff,
    Set.mem_himp_iff, Set.mem_compl_iff, reindex, Function.comp_def, Sum.elim_inl,
    Sum.elim_inr, bi, xi, yi, and_imp]
  constructor
  · intro h z hx hy hd
    have hc := h (z ∘ Sum.inl) (z (.inr (.inl 0))) (z (.inr (.inl 1)))
      (fun i => z (.inr (.inr i))) hx hy (fun c hc => hd (fun _ => c) hc)
    exact ⟨hc.mp, hc.mpr⟩
  · intro h b x y ys hx hy hd
    obtain ⟨hxy, hyx⟩ := h (Sum.elim b (Sum.elim ![x,y] ys)) hx hy (fun c => hd (c 0))
    exact ⟨hxy, hyx⟩

private theorem unary_slice_definable (U : DefSet (M := M) S (n + 1) k)
    (a : Fin n → M) :
    DefinableOver (S ∪ Set.range a) (MixedPolynomialSyntax.contextSort (m := k))
      {w : Fin (k + 1) → M | uCode a (w 0) (w ∘ Fin.succ) ∈ uRaw U} := by
  apply (definableOver_iff_normalized_raw _ _ _).mpr
  refine ⟨?_, ?_⟩
  · have hU := uRaw_definable U
    letI : LRV.Structure M := N
    apply (hU.mono Set.subset_union_left).preimage_map
    intro i
    cases i with
    | inl i =>
      cases i using Fin.cases with
      | zero => exact Set.DefinableFun.proj LRV
      | succ i => exact LRV.definableFun_const _ (Or.inr (Set.mem_range_self i))
    | inr i => exact Set.DefinableFun.proj LRV
  · rintro w ⟨hd, _⟩ i
    cases i using Fin.cases with
    | zero => exact hd.1 0
    | succ i => exact hd.2 i

private theorem exists_controlling_fibre {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VF (M := M)) Γ)
    (hv : ∀ x y : VF (M := M), VFValued.predV x y ↔ v x ≤ v y)
    (U : DefSet (M := M) S (n + 1) k) (a : Fin n → M) :
    ∃ (R : Set ((Fin n → M) × M)) (d : ℕ),
      @RawClosure.Tuple.RelationDefinable M N n S R ∧
      a ∉ @RawClosure.Tuple.HasMore M n R d ∧ controls U R a := by
  obtain ⟨T, _, hT, _, hclosed⟩ := mixed_finite_definable_obstacles v hv
    (S ∪ Set.range a) _ (unary_slice_definable U a)
  let C := Subtype.val '' (T : Set (VF (M := M)))
  have hc := ((definableAt_iff_normalized_raw _ .vf C).mp hT).1
  obtain ⟨R, hR, hf⟩ := @RawClosure.Tuple.promote_definable_fibre M N n S a C hc
  have hfin : C.Finite := T.finite_toSet.image Subtype.val
  refine ⟨R, C.ncard, hR, ?_, ?_⟩
  · change ¬∃ u : Fin (C.ncard + 1) → M, Function.Injective u ∧
      ∀ i, u i ∈ {x | (a, x) ∈ R}
    apply (RawClosure.no_inj_iff_finite_ncard_le).mpr
    rw [hf]
    exact ⟨hfin, le_rfl⟩
  · intro b x y ys hx hy havoid
    by_cases hys : ∀ i, iRV (ys i)
    · have hx' := (rawBall_iff b x).mp hx
      have hy' := (rawBall_iff b y).mp hy
      let x' : VF (M := M) := ⟨x, hx'.2.1⟩
      let y' : VF (M := M) := ⟨y, hy'.2.1⟩
      have hex : ∃ (o : VF (M := M)) (r : Balls.Radius Γ),
          ClosedBallCodes.ball b = Balls.closedDisc v o r := by
        let o : VF (M := M) := ⟨b 0, hx'.1 0⟩
        by_cases hflag : b 2 = iVFZero
        · exact ⟨o, ⊥, ClosedBallCodes.ball_eq_univ b hx'.1 hflag⟩
        · exact ⟨o, ↑(OrderDual.toDual (v ⟨b 1, hx'.1 1⟩)),
            ClosedBallCodes.ball_eq_closed v hv b hx'.1 hflag⟩
      obtain ⟨o, r, hr⟩ := hex
      have havoid' : ∀ c ∈ T, c ∉ Balls.closedDisc v o r := by
        intro c hc hmem
        apply havoid c.val ((rawBall_iff b c.val).mpr ((Set.ext_iff.mp hr c).mpr hmem))
        have hmem' : c.val ∈ C := ⟨c, hc, rfl⟩
        exact (Set.ext_iff.mp hf c.val).mpr hmem'
      have h := hclosed o r havoid' x' ((Set.ext_iff.mp hr x').mp hx')
        y' ((Set.ext_iff.mp hr y').mp hy') ys hys
      have e (z : M) : Fin.cons z ys ∘ Fin.succ = ys := rfl
      simpa only [Set.mem_ofPred_eq, Fin.cons_zero, e, x', y'] using h
    · push Not at hys
      obtain ⟨j, hj⟩ := hys
      exact iff_of_false (fun h => hj (h.1.2 j)) (fun h => hj (h.1.2 j))

private theorem closed_through_pair_subset {K Γ : Type} [Field K]
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) (a x y : K)
    (r : Balls.OpenRadius Γ) (hx : x ∈ Balls.openDisc v a r)
    (hy : y ∈ Balls.openDisc v a r) :
    Balls.closedDisc v x (↑(OrderDual.toDual (v (y - x)))) ⊆ Balls.openDisc v a r := by
  intro z hz
  change v (z - x) ≤ v (y - x) at hz
  change v (x - a) < (OrderDual.ofDual r : Γˣ).val at hx
  change v (y - a) < (OrderDual.ofDual r : Γˣ).val at hy
  change v (z - a) < (OrderDual.ofDual r : Γˣ).val
  have hyx : v (y - x) < (OrderDual.ofDual r : Γˣ).val := by
    rw [show y - x = (y - a) - (x - a) by ring]
    exact v.map_sub_lt hy hx
  rw [show z - a = (z - x) + (x - a) by ring]
  exact v.map_add_lt (hz.trans_lt hyx) hx

private theorem uniformControllingRelation {κ : Cardinal} (hs : Saturated M κ)
    (hsmall : Cardinal.mk S < κ) {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VF (M := M)) Γ)
    (hv : ∀ x y : VF (M := M), VFValued.predV x y ↔ v x ≤ v y)
    (U : DefSet (M := M) S (n + 1) k) :
    ∃ (R : Set ((Fin n → M) × M)) (d : ℕ),
      @RawClosure.Tuple.RelationDefinable M N n S R ∧
      (∀ a : Fin n → M, {x | (a, x) ∈ R}.Finite ∧ {x | (a, x) ∈ R}.ncard ≤ d) ∧
      ∀ a, controls U R a := by
  let hsN : @Saturated M N κ := hs.normalize
  let hsupply := exists_controlling_fibre v hv U
  let hdef := controls_definable U
  let Ctl := @controls M sM hM S n k U
  letI : LRV.Structure M := N
  let Data := {R : Set ((Fin n → M) × M) // RawClosure.Tuple.RelationDefinable S R} × ℕ
  let good (D : Data) : Set (Fin n → M) :=
    {a | a ∉ RawClosure.Tuple.HasMore D.1.val D.2 ∧ Ctl D.1.val a}
  have hg (D : Data) : S.Definable LRV (good D) :=
    (RawClosure.Tuple.hasMore_definable S D.1.val D.1.property D.2).compl.inter
      (hdef D.1.val D.1.property)
  have hc (a : Fin n → M) (_ : a ∈ Set.univ) : ∃ c ∈ Set.range good, a ∈ c := by
    obtain ⟨R, d, hR, ha, hh⟩ := hsupply a
    exact ⟨good (⟨R, hR⟩, d), Set.mem_range_self _, ha, hh⟩
  obtain ⟨J, hJ, hsub, hcov⟩ := Section4.definable_finite_subcover_index hsN S hsmall
    Set.univ Set.definable_univ (Set.range good)
    (by rintro _ ⟨D, rfl⟩; exact hg D) hc
  letI : Fintype J := hJ.fintype
  have chooseData (i : J) : ∃ D : Data, good D = i.val := hsub i.property
  let D (i : J) := Classical.choose (chooseData i)
  have hD (i : J) : good (D i) = i.val := Classical.choose_spec (chooseData i)
  let F (a : Fin n → M) (i : J) : Set M :=
    {x | a ∈ good (D i) ∧ (a, x) ∈ (D i).1.val}
  have hF (a : Fin n → M) (i : J) : (F a i).Finite ∧ (F a i).ncard ≤ (D i).2 := by
    by_cases ha : a ∈ good (D i)
    · have hf : ¬∃ u : Fin ((D i).2 + 1) → M, Function.Injective u ∧
          ∀ j, u j ∈ {x | (a, x) ∈ (D i).1.val} := ha.1
      simpa only [F, ha, true_and] using (RawClosure.no_inj_iff_finite_ncard_le.mp hf)
    · simp [F, ha]
  let R (a : Fin n → M) : Set M := ⋃ i, F a i
  have hR (a : Fin n → M) : (R a).Finite := Set.finite_iUnion (fun i => (hF a i).1)
  have hbound (a : Fin n → M) : (R a).ncard ≤ ∑ i, (D i).2 :=
    (Set.ncard_iUnion_le_of_fintype (F a)).trans
      (Finset.sum_le_sum fun i _ => (hF a i).2)
  refine ⟨{p | p.2 ∈ R p.1}, ∑ i, (D i).2, ?_, fun a => ⟨hR a, hbound a⟩, ?_⟩
  · have hi (i : J) := ((hg (D i)).preimage_comp (Sum.inl : Fin n → Fin n ⊕ Fin 1)).inter
      (D i).1.property
    have h := Set.definable_iUnion_of_finite hi
    change S.Definable LRV {z : Fin n ⊕ Fin 1 → M | z (.inr 0) ∈ R (z ∘ Sum.inl)}
    convert h using 1
    ext z
    simp only [R, F, Set.mem_iUnion, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage]
  · intro z b x y ys hx hy havoid
    obtain ⟨j, hj, hz⟩ := hcov z (Set.mem_univ _)
    let j' : J := ⟨j, hj⟩
    have hgood : z ∈ good (D j') := (hD j').symm ▸ hz
    exact hgood.2 b x y ys hx hy (fun c hc hmem =>
      havoid c hc (Set.mem_iUnion.mpr ⟨j', hgood, hmem⟩))

theorem uniformVerticalObstacles {κ : Cardinal} (hs : Saturated M κ)
    (hsmall : Cardinal.mk S < κ) {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VF (M := M)) Γ)
    (hv : ∀ x y : VF (M := M), VFValued.predV x y ↔ v x ≤ v y) (n : ℕ) :
    UniformVerticalObstacles v S n := by
  intro m k U A _
  obtain ⟨R, d, hR, hfin, hcontrol⟩ := uniformControllingRelation hs hsmall v hv U
  let Z : Set (Point (M := M) (n + 1) m) :=
    {p | p ∈ carrier A ∧ ((fun i => (p.1 i.succ).val), (p.1 0).val) ∈ R}
  have hZ : SetDefinable (pointSpace (n + 1) m) S Z := by
    let I := Fin (n + 1) ⊕ Fin m
    let tail : Fin n → I := fun i => .inl i.succ
    let head : Fin 1 → I := fun _ => .inl 0
    have ha := uRaw_definable A
    change @Set.Definable M S LRV N I
      (@DefinableGeometry.Space.preimage LRV M N (pointSpace (M := M) (n + 1) m) Z)
    letI : LRV.Structure M := N
    have h := ha.inter (hR.preimage_comp (Sum.elim tail head))
    convert h using 1
    ext z
    constructor
    · rintro ⟨hz, ha, hr⟩
      exact ⟨⟨hz, ha⟩, hr⟩
    · rintro ⟨⟨hz, ha⟩, hr⟩
      exact ⟨hz, ha, hr⟩
  have hZsub (p : Point (M := M) n m) :
      {x | insertHead x p ∈ Z} ⊆
        Subtype.val ⁻¹' {c | ((fun i => (p.1 i).val), c) ∈ R} :=
    fun _ hx => hx.2
  let Q : VerticalRootFamily A := ⟨PresentedSet.mk Z hZ, fun _ hp => hp.1,
    fun p => ((hfin _).1.preimage Subtype.val_injective.injOn).subset (hZsub p)⟩
  refine ⟨Q, d, ?_, ?_⟩
  · intro p _
    change (Q.finite p).toFinset.card ≤ d
    rw [← Set.ncard_eq_toFinset_card _ (Q.finite p)]
    exact (Set.ncard_le_ncard_of_injOn Subtype.val (hZsub p)
      Subtype.val_injective.injOn (hfin _).1).trans (hfin _).2
  · intro p a r hA havoid x hx y hy ys
    let z : Fin n → M := fun i => (p.1 i).val
    let V := Balls.closedDisc v x (↑(OrderDual.toDual (v (y - x))))
    have hV : V ⊆ Balls.openDisc v a r := closed_through_pair_subset v a x y r hx hy
    obtain ⟨b, _, hb⟩ := ClosedBallCodes.exists_code_of_closed v hv V (Or.inr ⟨x, y - x, rfl⟩)
    have hbmem (c : VF (M := M)) : c.val ∈ RawBall b ↔ c ∈ V := by
      rw [rawBall_iff b c.val]
      change c ∈ ClosedBallCodes.ball b ↔ c ∈ V
      rw [hb]
    have hdisj : ∀ c ∈ RawBall b, (z, c) ∉ R := by
      intro c hc hRj
      have hcvf := ((rawBall_iff b c).mp hc).2.1
      let c' : VF (M := M) := ⟨c, hcvf⟩
      have hcV := (hbmem c').mp hc
      have hcopen := hV hcV
      exact havoid c' ((Q.mem_fibre _ _).mpr ⟨hA c' hcopen, hRj⟩) hcopen
    have hxV : x ∈ V := Balls.centre_mem_closedDisc v x _
    have hyV : y ∈ V := le_rfl
    exact (uRaw_iff U p.1 x ys).symm.trans
      ((hcontrol z b x.val y.val (fun i => (ys i).val)
        ((hbmem x).mpr hxV) ((hbmem y).mpr hyV) hdisj).trans (uRaw_iff U p.1 y ys))

end SpecialTransformations.Section5
