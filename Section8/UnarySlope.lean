import Section4.GammaMultiplicationSyntax
import Section3.GammaSpecialization
import Section3.GammaThresholdGeometry
import Section8.IsolationRadius
import Mathlib.Algebra.Order.Group.Basic
import Section8.UniformBalls
import Section4.GammaPredicates
import Section3.SortedTuples
import Section8.UnaryGerm

/-! Lemma 8.3 and its definable constants in the actual Gamma quotient. -/

section DefinableRadius

/-! A nonempty definable upper ray of valid open-ball radii has a radius
definable over the same base. Its finite endpoint is allowed when the law
holds on the union of the open balls at all larger radii. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace SpecialTransformations.Section8

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem gamma_upper_ray_has_definable_radius (h00 : M ⊨ Axioms.ACVF00)
    {S : Set M} {A : Set (Values.Gamma (M := M))}
    (hA : Values.GammaDefinable S A) (hne : A.Nonempty)
    (hup : ∀ x ∈ A, ∀ y, x ≤ y → y ∈ A)
    (hclosed : ∀ x, (∀ y, x < y → y ∈ A) → x ∈ A) :
    ∃ r ∈ A, Values.GammaDefinable S {r} := by
  by_cases hcomp : Aᶜ.Nonempty
  · let B : GammaParameters.Base (M := M) := ⟨S, ∅⟩
    have hAB : GammaParameters.GammaDefinableOverBase B A :=
      GammaParameters.real_definableAtBase B .rv _ hA
    obtain ⟨r, hr⟩ := GammaParameters.gamma_canonical_endpoint_exists h00 B A hAB hne hcomp
    have hlower (b : Values.Gamma (M := M)) (hb : b ∉ A) : ∀ x ∈ A, b ≤ x := by
      intro x hx
      exact le_of_not_gt (fun h => hb (hup x hx b h.le))
    have hbounded : FiniteThresholds.BoundedBelow A :=
      ⟨hcomp.choose, hlower hcomp.choose hcomp.choose_spec⟩
    have hrinf := (hr.resolve_right (fun h => h.1 hbounded)).2
    have hrA : r ∈ A := hclosed r (fun x hx => by
      by_contra hnot
      exact (not_le_of_gt hx) (hrinf.2 x (hlower x hnot)))
    refine ⟨r, hrA, ?_⟩
    let I := Fin 1 ⊕ Fin 1
    have hsmaller := (GammaSyntax.unary_at hA (Sum.inr 0 : I)).and
      (GammaSyntax.lt_definable S (Sum.inr 0 : I) (Sum.inl 0))
    have hd := (GammaSyntax.unary_at hA (0 : Fin 1)).and hsmaller.exists_block.not
    apply (GammaSyntax.scalar_definable_iff {r}).mp
    refine hd.congr (fun z => ?_)
    change (z 0 ∈ A ∧ ¬ ∃ y : Fin 1 → Values.Gamma (M := M), y 0 ∈ A ∧ y 0 < z 0) ↔ z 0 = r
    constructor
    · rintro ⟨hz, hn⟩
      exact le_antisymm (le_of_not_gt (fun h => hn ⟨fun _ => r, hrA, h⟩)) (hrinf.1 _ hz)
    · intro hz
      rw [hz]
      exact ⟨hrA, fun ⟨y, hy, hylt⟩ => (not_le_of_gt hylt) (hrinf.1 _ hy)⟩
  · refine ⟨1, ?_, GammaSyntax.one_definable S⟩
    by_contra h
    exact hcomp ⟨1, h⟩

end SpecialTransformations.Section8
end DefinableRadius

section GammaPuncturedBall

/-! Punctured neighbourhood laws may be stated in the paper's Gamma order.
The strict ball inequality gives the endpoint property of valid radii. -/

set_option backward.isDefEq.respectTransparency false

open Filter Topology FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace SpecialTransformations.Section8

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def gammaPuncturedBallHolds (a : VFType (M := M)) (P : VFType (M := M) → Prop)
    (r : Values.Gamma (M := M)) : Prop :=
  ∀ x : VFType (M := M), x ≠ a → r.val < Values.vfValueHom (x - a) → P x

theorem gammaPuncturedBallHolds_mono {a : VFType (M := M)} {P : VFType (M := M) → Prop}
    {r s : Values.Gamma (M := M)} (hr : gammaPuncturedBallHolds a P r) (hrs : r ≤ s) :
    gammaPuncturedBallHolds a P s :=
  fun x hxa hx => hr x hxa (lt_of_le_of_lt hrs hx)

theorem gammaPuncturedBallHolds_of_larger {a : VFType (M := M)} {P : VFType (M := M) → Prop}
    (r : Values.Gamma (M := M))
    (hr : ∀ s : Values.Gamma (M := M), r < s → gammaPuncturedBallHolds a P s) :
    gammaPuncturedBallHolds a P r := by
  intro x hxa hx
  let γ := GammaThresholdGeometry.vfGamma (x - a) (sub_ne_zero.mpr hxa)
  have hγ : r < γ := hx
  obtain ⟨s, hrs, hsγ⟩ := exists_between hγ
  exact hr s hrs x hxa hsγ

variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ] [Valued (VFType (M := M)) Γ]

theorem exists_gammaPuncturedBallHolds_iff_eventually
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (a : VFType (M := M)) (P : VFType (M := M) → Prop) :
    (∃ r : Values.Gamma (M := M), gammaPuncturedBallHolds a P r) ↔
      ∀ᶠ x in 𝓝 a, x ≠ a → P x := by
  let v : Valuation (VFType (M := M)) Γ := Valued.v
  constructor
  · rintro ⟨γ, hγ⟩
    obtain ⟨r, hr, hval⟩ := gamma_has_vf_representative γ
    let D : ValuedPolydisc v 1 := ⟨fun _ => a, fun _ => r, fun _ => hr⟩
    filter_upwards [D.side_mem_nhds 0] with x hx hxa
    have he := (GammaThresholdGeometry.value_lt_gamma v hv (x - a) r (sub_ne_zero.mpr hxa) hr).mp hx
    apply hγ x hxa
    rwa [← hval]
  · intro h
    obtain ⟨r, hr, hsub⟩ := exists_nonzero_ball_subset a h
    let γ := GammaThresholdGeometry.vfGamma r hr
    refine ⟨γ, fun x hxa hx => hsub ?_ hxa⟩
    exact (GammaThresholdGeometry.value_lt_gamma v hv (x - a) r (sub_ne_zero.mpr hxa) hr).mpr hx

end SpecialTransformations.Section8
end GammaPuncturedBall

section GammaPowerGerm

/-! A positive power law in the compatible valuation becomes a law on
the actual Gamma quotient. Its intercept is unique on a punctured germ. -/

set_option backward.isDefEq.respectTransparency false

open Filter Topology FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3

namespace SpecialTransformations.Section8

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def gammaPowerGerm (f : VFType (M := M) → VFType (M := M)) (a : VFType (M := M))
    (p q : ℕ) (c r : Values.Gamma (M := M)) : Prop :=
  gammaPuncturedBallHolds a
    (fun x => f x ≠ 0 ∧ Values.vfValueHom (f x) ^ q = c.val ^ q * Values.vfValueHom (x - a) ^ p) r

theorem exists_gammaPowerGerm {Γ : Type} [LinearOrderedCommGroupWithZero Γ] [Valued (VFType (M := M)) Γ]
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (f : VFType (M := M) → VFType (M := M)) (a s : VFType (M := M)) (hs : s ≠ 0)
    (p q : ℕ) (hq : q ≠ 0)
    (h : ∀ᶠ x in 𝓝 a, x ≠ a → f x ≠ 0 ∧ Valued.v (f x) ^ q = Valued.v s * Valued.v (x - a) ^ p) :
    ∃ c r : Values.Gamma (M := M), gammaPowerGerm f a p q c r := by
  let v : Valuation (VFType (M := M)) Γ := Valued.v
  let b := GammaThresholdGeometry.vfGamma s hs
  obtain ⟨c, hc⟩ := Values.gamma_pow_surjective q hq b
  have he : c.val ^ q = Values.vfValueHom s :=
    (map_pow Values.gammaValHom c q).symm.trans (congrArg Subtype.val hc)
  refine ⟨c, (exists_gammaPuncturedBallHolds_iff_eventually hv a _).mpr ?_⟩
  filter_upwards [h] with x hx hxa
  have hvalue : v (f x ^ q) = v (s * (x - a) ^ p) := by
    simpa only [map_pow, map_mul] using (hx hxa).2
  have hΓ := (Values.vf_value_eq_iff v hv _ _).mpr hvalue
  change Values.vfValueHom (f x ^ q) = Values.vfValueHom (s * (x - a) ^ p) at hΓ
  rw [map_pow, map_mul, map_pow] at hΓ
  refine ⟨(hx hxa).1, ?_⟩
  rw [he]
  exact hΓ

/-- Two open radii for the same powers have a common noncentral point.
At that point the nonzero input factor cancels and fixes the intercept. -/
theorem gammaPowerGerm_intercept_unique
    {f : VFType (M := M) → VFType (M := M)} {a : VFType (M := M)} {p q : ℕ}
    (hq : 0 < q) {c d r s : Values.Gamma (M := M)}
    (hc : gammaPowerGerm f a p q c r) (hd : gammaPowerGerm f a p q d s) : c = d := by
  obtain ⟨γ, hγ⟩ := exists_gt (max r s)
  obtain ⟨u, hu, hval⟩ := gamma_has_vf_representative γ
  let x := a + u
  have hxa : x - a = u := by simp only [x, add_sub_cancel_left]
  have hne : x ≠ a := fun h => hu (by rw [← hxa, h, sub_self])
  have hr : r.val < Values.vfValueHom (x - a) := by
    rw [hxa, hval]
    exact lt_of_le_of_lt (le_max_left r s) hγ
  have hs : s.val < Values.vfValueHom (x - a) := by
    rw [hxa, hval]
    exact lt_of_le_of_lt (le_max_right r s) hγ
  have hnonzero : Values.vfValueHom (x - a) ≠ 0 := by
    rw [hxa, hval, ← Values.infinity_eq_zero]
    exact γ.property
  have he := (hc x hne hr).2.symm.trans (hd x hne hs).2
  have hp := mul_right_cancel₀ (pow_ne_zero p hnonzero) he
  have hpow : c ^ q = d ^ q := by
    apply Subtype.ext
    change Values.gammaValHom (c ^ q) = Values.gammaValHom (d ^ q)
    exact (map_pow Values.gammaValHom c q).trans (hp.trans (map_pow Values.gammaValHom d q).symm)
  have hqz : 0 < (q : ℤ) := by exact_mod_cast hq
  apply (zpow_left_strictMono (Values.Gamma (M := M)) hqz).injective
  simpa only [zpow_natCast] using hpow

end SpecialTransformations.Section8
end GammaPowerGerm

section PuncturedBallFormula

/-! Express a universal graph condition on a punctured open ball, while
keeping arbitrary extra law parameters as free coordinates. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace SpecialTransformations.Section8

variable {M : Type} [LRV.Structure M] {ι : Type}

def puncturedBallFormula (a : M) (G : Set (Fin 2 → M)) (C : Set (ι ⊕ Fin 2 → M)) :
    Set (ι ⊕ Fin 1 → M) :=
  {z | ¬ ∃ w ∈ G, w 0 ≠ a ∧ w 0 ∈ rawOpenBall a (z (.inr 0)) ∧
    Sum.elim (z ∘ Sum.inl) w ∉ C}

theorem puncturedBallFormula_definable {S : Set M} {a : M} (ha : a ∈ S)
    {G : Set (Fin 2 → M)} (hG : S.Definable LRV G)
    {C : Set (ι ⊕ Fin 2 → M)} (hC : S.Definable LRV C) :
    S.Definable LRV (puncturedBallFormula a G C) := by
  let Z := ι ⊕ Fin 1
  let W := Z ⊕ Fin 2
  let x : W := .inr 0
  let r : W := .inl (.inr 0)
  let H : ι ⊕ Fin 2 → W := Sum.elim (Sum.inl ∘ Sum.inl) Sum.inr
  let F (z : W → M) : Fin 3 → M := ![a, z r, z x]
  have hF : S.DefinableMap LRV F := by
    intro i
    fin_cases i
    · exact LRV.definableFun_const _ ha
    · exact Set.DefinableFun.proj LRV
    · exact Set.DefinableFun.proj LRV
  have hball : S.Definable LRV {z : W → M | z x ∈ rawOpenBall a (z r)} := by
    convert (OpenBallCodes.membership_raw_definable S).preimage_map hF using 1
    ext z
    have hinit : Fin.init (F z) = ![a, z r] := by
      funext i
      fin_cases i <;> rfl
    change z x ∈ rawOpenBall a (z r) ↔ F z (Fin.last 2) ∈ OpenBallCodes.rawBall (Fin.init (F z))
    rw [hinit]
    rfl
  have hneq := ((Set.DefinableFun.proj LRV (i := x)).ofPred_eq (LRV.definableFun_const W ha)).compl
  have hbad := ((hG.preimage_comp (Sum.inr : Fin 2 → W)).inter
    (hneq.inter (hball.inter (hC.preimage_comp H).compl))).exists_of_finite
  convert hbad.compl using 1
  ext z
  have htuple (w : Fin 2 → M) : Sum.elim (z ∘ Sum.inl) w = Sum.elim z w ∘ H := by
    funext i
    cases i <;> rfl
  simp only [puncturedBallFormula, Set.mem_ofPred_eq, Set.mem_setOf_eq, Set.mem_compl_iff,
    Set.mem_inter_iff, Set.mem_preimage, htuple, x, r, Function.comp_apply, Sum.elim_inl, Sum.elim_inr] <;> rfl

end SpecialTransformations.Section8
end PuncturedBallFormula

section GammaRepresentativeFormula

/-! A formula for a predicate on nonzero VF representatives yields the
full definable preimage of the predicate on actual Gamma values. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4

namespace SpecialTransformations.Section8

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n : ℕ}

def vfGammaPullback (P : (Fin n → Values.Gamma (M := M)) → Prop) : Set (Fin n → M) :=
  {z | ∃ a : Fin n → VFType (M := M), vfValues a = z ∧
    ∃ h : ∀ i, a i ≠ 0, P (fun i => GammaThresholdGeometry.vfGamma (a i) (h i))}

private theorem rv_sameScalar_vfGamma_iff (t : M) (ht : NonzeroRV t)
    (x : VFType (M := M)) (hx : x ≠ 0) :
    SameScalar t (iRv x.val) ↔ codeValue t = GammaThresholdGeometry.vfGamma x hx := by
  have hx0 : (CanonicalRV.encodedRv x).val ≠ iRVZero :=
    fun h => hx ((CanonicalRV.encodedRv_zero_iff x).mp h)
  let a : Code (M := M) := ⟨⟨t, ht.1⟩, ht.2⟩
  let b : Code (M := M) := ⟨CanonicalRV.encodedRv x, hx0⟩
  change SameScalar (raw a) (raw b) ↔ codeValue (raw a) = value b
  rw [codeValue_raw, value_eq_iff]
  exact ⟨fun h => h.2.2, fun h => ⟨ht, ⟨(CanonicalRV.encodedRv x).property, hx0⟩, h⟩⟩

theorem gammaPredicate_of_vfGammaPullback (hc : CanonicalStructure.IsCanonical (M := M))
    {S : Set M} {P : (Fin n → Values.Gamma (M := M)) → Prop}
    (hP : S.Definable LRV (vfGammaPullback P)) : GammaSyntax.Definable S P := by
  let I := Fin n ⊕ Fin n
  let t (i : Fin n) : LRV.Term I := .func Fn.rvMap ![.var (.inr i)]
  have hmap (i : Fin n) : S.DefinableMap LRV (fun z : I → M => ![z (.inl i), (t i).realize z]) := by
    intro j
    fin_cases j
    · exact Set.DefinableFun.proj LRV
    · exact (t i).definableFun_realize.mono (Set.empty_subset S)
  have hs : S.Definable LRV {z : I → M | ∀ i, SameScalar (z (.inl i)) (iRv (z (.inr i)))} := by
    rw [Set.ofPred_forall]
    apply Set.definable_iInter_of_finite
    intro i
    convert (same_scalar_definable S).preimage_map (hmap i) using 1
    ext z
    change SameScalar (z (.inl i)) (iRv (z (.inr i))) ↔ SameScalar (z (.inl i)) ((t i).realize z)
    have ht : (t i).realize z = iRv (z (.inr i)) := by
      dsimp only [t, Term.realize, iRv]
      congr 1
      funext l
      fin_cases l
      rfl
    rw [ht]
  let A : Set (Fin n → M) := {z | GammaSyntax.Proper z ∧ P (GammaSyntax.decode z)}
  have h : S.Definable LRV A := by
    convert (hs.inter (hP.preimage_comp (Sum.inr : Fin n → I))).exists_of_finite using 1
    ext z
    change (GammaSyntax.Proper z ∧ P (GammaSyntax.decode z)) ↔
      ∃ w : Fin n → M, (∀ i, SameScalar (z i) (iRv (w i))) ∧ w ∈ vfGammaPullback P
    constructor
    · rintro ⟨hz, hp⟩
      choose a ha he using fun i => gamma_has_vf_representative (GammaSyntax.decode z i)
      have hdecode : (fun i => GammaThresholdGeometry.vfGamma (a i) (ha i)) = GammaSyntax.decode z :=
        funext (fun i => Subtype.ext (he i))
      refine ⟨vfValues a, ?_, ⟨a, rfl, ha, hdecode.symm ▸ hp⟩⟩
      intro i
      exact (rv_sameScalar_vfGamma_iff (z i) (hz i) (a i) (ha i)).mpr (congrFun hdecode i).symm
    · rintro ⟨_, hs, a, rfl, ha, hp⟩
      have hz : GammaSyntax.Proper z := fun i => (hs i).1
      have hdecode : GammaSyntax.decode z = fun i => GammaThresholdGeometry.vfGamma (a i) (ha i) :=
        funext (fun i => (rv_sameScalar_vfGamma_iff (z i) (hz i) (a i) (ha i)).mp (hs i))
      exact ⟨hz, hdecode.symm ▸ hp⟩
  have hsorted := raw_definableOver_sorted hc S (fun _ => .rv) A h (fun z hz i => (hz.1 i).1)
  exact ((definableOver_iff_normalized_raw S (fun _ => .rv) A).mp hsorted).1

end SpecialTransformations.Section8
end GammaRepresentativeFormula

section GammaLawFormula

/-! The actual Gamma intercept and radius are free coordinates of one
definable relation. Their VF representatives are quantified. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace SpecialTransformations.Section8

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

private noncomputable def lawLeft (q : ℕ) : LRV.Term (Fin 4) :=
  RingSyntax.ofRingTerm (FirstOrder.Ring.termOfFreeCommRing (FreeCommRing.of (3 : Fin 4) ^ q))

private noncomputable def lawRight (p q : ℕ) : LRV.Term (Fin 4) :=
  let v : Fin 4 → FreeCommRing (Fin 4) := FreeCommRing.of
  RingSyntax.ofRingTerm (FirstOrder.Ring.termOfFreeCommRing (v 0 ^ q * (v 2 - v 1) ^ p))

private def lawTuple (a : M) (z : Fin 1 ⊕ Fin 2 → M) : Fin 4 → M :=
  ![z (.inl 0), a, z (.inr 0), z (.inr 1)]

private def powerClause (a : M) (p q : ℕ) : Set (Fin 1 ⊕ Fin 2 → M) :=
  {z | termValueEq (lawLeft q) (lawRight p q) (lawTuple a z) ∧ z (.inr 1) ≠ iVFZero}

private theorem powerClause_definable {S : Set M} {a : M} (ha : a ∈ S) (p q : ℕ) :
    S.Definable LRV (powerClause a p q) := by
  let I := Fin 1 ⊕ Fin 2
  have hmap : S.DefinableMap LRV (lawTuple a) := by
    intro i
    fin_cases i
    · exact Set.DefinableFun.proj LRV
    · exact LRV.definableFun_const I ha
    · exact Set.DefinableFun.proj LRV
    · exact Set.DefinableFun.proj LRV
  have hzero : S.DefinableFun LRV (fun _ : I → M => iVFZero) :=
    DefinableConstants.constant (DefinableConstants.function_symbol
      (L := LRV) Fn.vfZero Fin.elim0 (fun k => k.elim0))
  exact ((termValueEq_definable S (lawLeft q) (lawRight p q)).preimage_map hmap).inter
    (((Set.DefinableFun.proj LRV (i := (Sum.inr 1 : I))).ofPred_eq hzero).compl)

private theorem mem_powerClause_iff (a s x y : VFType (M := M)) (p q : ℕ) :
    Sum.elim (fun _ : Fin 1 => s.val) ![x.val, y.val] ∈ powerClause a.val p q ↔
      y ≠ 0 ∧ Values.vfValueHom y ^ q = Values.vfValueHom s ^ q * Values.vfValueHom (x - a) ^ p := by
  let z : Fin 4 → VFType (M := M) := ![s, a, x, y]
  have hz : lawTuple a.val (Sum.elim (fun _ : Fin 1 => s.val) ![x.val, y.val]) = fun i => (z i).val := by
    funext i
    fin_cases i <;> rfl
  have hl : (lawLeft q).realize (fun i => (z i).val) = (y ^ q).val := by
    dsimp only [lawLeft]
    rw [RingSyntax.realizes, FirstOrder.Ring.realize_termOfFreeCommRing]
    simp only [map_pow, FreeCommRing.lift_of] <;> rfl
  have hr : (lawRight p q).realize (fun i => (z i).val) = (s ^ q * (x - a) ^ p).val := by
    dsimp only [lawRight]
    rw [RingSyntax.realizes, FirstOrder.Ring.realize_termOfFreeCommRing]
    simp only [map_pow, map_mul, map_sub, FreeCommRing.lift_of] <;> rfl
  change (termValueEq (lawLeft q) (lawRight p q) (lawTuple a.val _) ∧ y.val ≠ iVFZero) ↔ _
  rw [hz]
  simp only [termValueEq_realize]
  rw [hl, hr]
  change ((VFValued.predV (s ^ q * (x - a) ^ p) (y ^ q) ∧
    VFValued.predV (y ^ q) (s ^ q * (x - a) ^ p)) ∧ y.val ≠ iVFZero) ↔ _
  rw [Values.vf_pred_iff_gamma_le, Values.vf_pred_iff_gamma_le]
  simp only [map_pow, map_mul]
  exact ⟨fun h => ⟨fun he => h.2 (congrArg Subtype.val he), le_antisymm h.1.1 h.1.2⟩,
    fun h => ⟨⟨h.2.le, h.2.ge⟩, fun he => h.1 (Subtype.ext he)⟩⟩

theorem puncturedBallFormula_iff_gamma {ι : Type} (f : VFType (M := M) → VFType (M := M))
    (a r : VFType (M := M)) (hr : r ≠ 0) (c : ι → M) {C : Set (ι ⊕ Fin 2 → M)}
    {P : VFType (M := M) → Prop} (hC : ∀ x, Sum.elim c ![x.val, (f x).val] ∈ C ↔ P x) :
    Sum.elim c (fun _ : Fin 1 => r.val) ∈ puncturedBallFormula a.val (unaryScalarGraph f) C ↔
      gammaPuncturedBallHolds a P (GammaThresholdGeometry.vfGamma r hr) := by
  have hball (x : VFType (M := M)) (hx : x ≠ a) :
      x.val ∈ rawOpenBall a.val r.val ↔ Values.vfValueHom r < Values.vfValueHom (x - a) :=
    (mem_rawOpenBall_iff Values.presentationValuation Values.presentation_compatible a r x hr).trans
      (GammaThresholdGeometry.value_lt_gamma _ Values.presentation_compatible (x - a) r (sub_ne_zero.mpr hx) hr)
  constructor
  · intro h x hxa hx
    apply (hC x).mp
    by_contra hnot
    exact h ⟨![x.val, (f x).val], ⟨x, rfl, rfl⟩, fun he => hxa (Subtype.ext he),
      (hball x hxa).mpr hx, hnot⟩
  · intro h
    rintro ⟨w, ⟨x, hx, hy⟩, hxa, hw, hnot⟩
    have he : (![x.val, (f x).val] : Fin 2 → M) = w := by
      funext i
      fin_cases i <;> assumption
    subst w
    have hne : x ≠ a := fun he => hxa (congrArg Subtype.val he)
    exact hnot ((hC x).mpr (h x hne ((hball x hne).mp hw)))

private theorem nonzero_vf_tuple_definable (S : Set M) (n : ℕ) :
    S.Definable LRV {z : Fin n → M | ∀ i, iVF (z i) ∧ z i ≠ iVFZero} := by
  have hzero : S.DefinableFun LRV (fun _ : Fin n → M => iVFZero) :=
    DefinableConstants.constant (DefinableConstants.function_symbol
      (L := LRV) Fn.vfZero Fin.elim0 (fun k => k.elim0))
  rw [Set.ofPred_forall]
  exact Set.definable_iInter_of_finite (fun i =>
    (((definableAt_sort S .vf).raw_definable).preimage_comp (fun _ : Fin 1 => i)).inter
      (((Set.DefinableFun.proj LRV (i := i)).ofPred_eq hzero).compl))

theorem gammaPowerGerm_definable (hc : CanonicalStructure.IsCanonical (M := M))
    {S : Set M} {f : VFType (M := M) → VFType (M := M)}
    (hf : S.Definable LRV (unaryScalarGraph f)) (a : VFType (M := M)) (p q : ℕ) :
    GammaSyntax.Definable (insert a.val S)
      (fun γ : Fin 2 → Values.Gamma (M := M) => gammaPowerGerm f a p q (γ 0) (γ 1)) := by
  let T := insert a.val S
  have ha : a.val ∈ T := Set.mem_insert _ _
  let idx : Fin 1 ⊕ Fin 1 → Fin 2 := Sum.elim (fun _ => 0) (fun _ => 1)
  let W := puncturedBallFormula a.val (unaryScalarGraph f) (powerClause a.val p q)
  have hW : T.Definable LRV W := puncturedBallFormula_definable ha
    (hf.mono (Set.subset_insert _ _)) (powerClause_definable ha p q)
  have hsem (b : Fin 2 → VFType (M := M)) (hb : ∀ i, b i ≠ 0) :
      vfValues b ∘ idx ∈ W ↔ gammaPowerGerm f a p q
        (GammaThresholdGeometry.vfGamma (b 0) (hb 0)) (GammaThresholdGeometry.vfGamma (b 1) (hb 1)) := by
    have he : vfValues b ∘ idx = Sum.elim (fun _ : Fin 1 => (b 0).val) (fun _ : Fin 1 => (b 1).val) := by
      funext i
      cases i <;> rfl
    rw [he]
    exact puncturedBallFormula_iff_gamma f a (b 1) (hb 1) _
      (fun x => mem_powerClause_iff a (b 0) x (f x) p q)
  apply gammaPredicate_of_vfGammaPullback hc
  convert (hW.preimage_comp idx).inter (nonzero_vf_tuple_definable T 2) using 1
  ext z
  change (∃ b : Fin 2 → VFType (M := M), vfValues b = z ∧ ∃ hb : ∀ i, b i ≠ 0,
    gammaPowerGerm f a p q (GammaThresholdGeometry.vfGamma (b 0) (hb 0))
      (GammaThresholdGeometry.vfGamma (b 1) (hb 1))) ↔
    z ∘ idx ∈ W ∧ ∀ i, iVF (z i) ∧ z i ≠ iVFZero
  constructor
  · rintro ⟨b, rfl, hb, h⟩
    exact ⟨(hsem b hb).mpr h, fun i => ⟨(b i).property, fun hz => hb i (Subtype.ext hz)⟩⟩
  · rintro ⟨hW, hz⟩
    let b : Fin 2 → VFType (M := M) := fun i => ⟨z i, (hz i).1⟩
    have hb : ∀ i, b i ≠ 0 := fun i he => (hz i).2 (congrArg Subtype.val he)
    exact ⟨b, rfl, hb, (hsem b hb).mp hW⟩

theorem gammaPuncturedBallHolds_definable (hc : CanonicalStructure.IsCanonical (M := M))
    {S : Set M} {f : VFType (M := M) → VFType (M := M)}
    (hf : S.Definable LRV (unaryScalarGraph f)) {C : Set (Fin 2 → M)} (hC : S.Definable LRV C)
    (a : VFType (M := M)) {P : VFType (M := M) → Prop}
    (hsem : ∀ x, (![x.val, (f x).val] : Fin 2 → M) ∈ C ↔ P x) :
    Values.GammaDefinable (insert a.val S) {r | gammaPuncturedBallHolds a P r} := by
  let T := insert a.val S
  let C' := (fun z : Fin 0 ⊕ Fin 2 → M => z ∘ Sum.inr) ⁻¹' C
  let W := puncturedBallFormula a.val (unaryScalarGraph f) C'
  let idx : Fin 0 ⊕ Fin 1 → Fin 1 := Sum.elim Fin.elim0 id
  have hW : T.Definable LRV W := puncturedBallFormula_definable (Set.mem_insert _ _)
    (hf.mono (Set.subset_insert _ _)) ((hC.mono (Set.subset_insert _ _)).preimage_comp Sum.inr)
  have hball (b : Fin 1 → VFType (M := M)) (hb : ∀ i, b i ≠ 0) :
      vfValues b ∘ idx ∈ W ↔ gammaPuncturedBallHolds a P (GammaThresholdGeometry.vfGamma (b 0) (hb 0)) := by
    have he : vfValues b ∘ idx = Sum.elim Fin.elim0 (fun _ : Fin 1 => (b 0).val) := by
      funext i
      rcases i with i | i
      · exact i.elim0
      · fin_cases i
        rfl
    rw [he]
    exact puncturedBallFormula_iff_gamma f a (b 0) (hb 0) Fin.elim0 hsem
  apply (GammaSyntax.scalar_definable_iff _).mp
  apply gammaPredicate_of_vfGammaPullback hc
  convert (hW.preimage_comp idx).inter (nonzero_vf_tuple_definable T 1) using 1
  ext z
  constructor
  · rintro ⟨b, rfl, hb, h⟩
    exact ⟨(hball b hb).mpr h, fun i => ⟨(b i).property, fun hz => hb i (Subtype.ext hz)⟩⟩
  · rintro ⟨hW, hz⟩
    let b : Fin 1 → VFType (M := M) := fun i => ⟨z i, (hz i).1⟩
    have hb : ∀ i, b i ≠ 0 := fun i he => (hz i).2 (congrArg Subtype.val he)
    exact ⟨b, rfl, hb, (hball b hb).mp hW⟩

theorem gammaConstantGerm_definable (hc : CanonicalStructure.IsCanonical (M := M))
    {S : Set M} {f : VFType (M := M) → VFType (M := M)}
    (hf : S.Definable LRV (unaryScalarGraph f)) (a : VFType (M := M)) :
    Values.GammaDefinable (insert a.val S) {r | gammaPuncturedBallHolds a (fun x => f x = 0) r} := by
  have hzero : S.DefinableFun LRV (fun _ : Fin 2 → M => iVFZero) :=
    DefinableConstants.constant (DefinableConstants.function_symbol
      (L := LRV) Fn.vfZero Fin.elim0 (fun k => k.elim0))
  have hC := (Set.DefinableFun.proj LRV (i := (1 : Fin 2))).ofPred_eq hzero
  apply gammaPuncturedBallHolds_definable hc hf hC a
  intro x
  change (f x).val = iVFZero ↔ f x = 0
  exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

end SpecialTransformations.Section8
end GammaLawFormula

section NamedGermConstants

/-! Choose the Gamma witnesses over the graph's parameter set and the
centre. The intercept is fixed by uniqueness and the radius by the
definable upper ray of radii on which that law holds. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace SpecialTransformations.Section8

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem gammaConstantGerm_has_named_radius (h00 : M ⊨ Axioms.ACVF00)
    (hc : CanonicalStructure.IsCanonical (M := M))
    {S : Set M} {f : VFType (M := M) → VFType (M := M)}
    (hf : S.Definable LRV (unaryScalarGraph f)) (a : VFType (M := M))
    (h : ∃ r, gammaPuncturedBallHolds a (fun x => f x = 0) r) :
    ∃ r, gammaPuncturedBallHolds a (fun x => f x = 0) r ∧
      Values.GammaDefinable (insert a.val S) {r} :=
  gamma_upper_ray_has_definable_radius h00 (gammaConstantGerm_definable hc hf a) h
    (fun _ hx _ hle => gammaPuncturedBallHolds_mono hx hle)
    (fun r hr => gammaPuncturedBallHolds_of_larger r hr)

theorem gammaPowerGerm_has_named_witnesses (h00 : M ⊨ Axioms.ACVF00)
    (hc : CanonicalStructure.IsCanonical (M := M))
    {S : Set M} {f : VFType (M := M) → VFType (M := M)}
    (hf : S.Definable LRV (unaryScalarGraph f)) (a : VFType (M := M)) (p q : ℕ) (hq : 0 < q)
    (h : ∃ c r, gammaPowerGerm f a p q c r) :
    ∃ c r, gammaPowerGerm f a p q c r ∧
      Values.GammaDefinable (insert a.val S) {c} ∧ Values.GammaDefinable (insert a.val S) {r} := by
  obtain ⟨c, r, hcr⟩ := h
  let I := Fin 1 ⊕ Fin 1
  let left : Fin 2 → I := ![.inl 0, .inr 0]
  let right : Fin 2 → I := ![.inr 0, .inl 0]
  let G := Values.Gamma (M := M)
  let T := insert a.val S
  have hdef := gammaPowerGerm_definable hc hf a p q
  have hcd : Values.GammaDefinable T {c} := by
    apply (GammaSyntax.scalar_definable_iff {c}).mp
    refine ((hdef.reindex left).exists_block).congr (fun z => ?_)
    change (∃ t : Fin 1 → G, gammaPowerGerm f a p q (z 0) (t 0)) ↔ z 0 = c
    constructor
    · rintro ⟨t, ht⟩
      exact gammaPowerGerm_intercept_unique hq ht hcr
    · intro hz
      exact ⟨fun _ => r, hz.symm ▸ hcr⟩
  have hrd : Values.GammaDefinable T {s | gammaPowerGerm f a p q c s} := by
    apply (GammaSyntax.scalar_definable_iff _).mp
    have h := ((hdef.reindex right).and (GammaSyntax.unary_at hcd (Sum.inr 0 : I))).exists_block
    refine h.congr (fun z => ?_)
    change (∃ t : Fin 1 → G, gammaPowerGerm f a p q (t 0) (z 0) ∧ t 0 = c) ↔
      gammaPowerGerm f a p q c (z 0)
    constructor
    · rintro ⟨t, ht, he⟩
      rwa [he] at ht
    · exact fun hz => ⟨fun _ => c, hz, rfl⟩
  obtain ⟨s, hs, hsd⟩ := gamma_upper_ray_has_definable_radius h00 hrd ⟨r, hcr⟩
    (fun _ hx _ hle => gammaPuncturedBallHolds_mono hx hle)
    (fun t ht => gammaPuncturedBallHolds_of_larger t ht)
  exact ⟨c, s, hs, hcd, hsd⟩

end SpecialTransformations.Section8
end NamedGermConstants

section UnarySlope

/-! Lemma 8.3 for the canonical VF/RV presentation over a real base.
The rational slope is written as a positive integer power equation in
the actual Gamma quotient. -/

set_option backward.isDefEq.respectTransparency false

open Filter Topology FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace SpecialTransformations.Section8

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {k m : ℕ}

/-- The minimum of the coordinate values in the paper's order. -/
noncomputable def vfTupleValue (x : Fin m → VFType (M := M)) : Values.GammaTop (M := M) :=
  if hm : 0 < m then Values.vfValueHom (dominantCoordinate Values.presentationValuation x hm)
  else Values.infinity

theorem vfTupleValue_le_component (x : Fin m → VFType (M := M)) (i : Fin m) :
    vfTupleValue x ≤ Values.vfValueHom (x i) := by
  have hm := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  rw [vfTupleValue, dif_pos hm]
  exact (Values.vf_pred_iff_gamma_le _ _).mp
    ((Values.presentation_compatible _ _).mpr (value_le_dominantCoordinate _ x hm i))

theorem vfTupleValue_eq_component (x : Fin m → VFType (M := M)) (hm : 0 < m) :
    ∃ i, vfTupleValue x = Values.vfValueHom (x i) := by
  exact ⟨dominantIndex Values.presentationValuation x hm, by rw [vfTupleValue, dif_pos hm] <;> rfl⟩

theorem vfTupleValue_zero : vfTupleValue (0 : Fin m → VFType (M := M)) = 0 := by
  by_cases hm : 0 < m
  · rw [vfTupleValue, dif_pos hm]
    exact map_zero Values.vfValueHom
  · rw [vfTupleValue, dif_neg hm, Values.infinity_eq_zero]

def unaryLocalSlope (T : Set M) (R : Finset ℚ) (a : VFType (M := M))
    (f : VFType (M := M) → Fin m → VFType (M := M)) : Prop :=
  ∃ c r : Values.Gamma (M := M), Values.GammaDefinable T {c} ∧ Values.GammaDefinable T {r} ∧
    ∃ p q : ℕ, 0 < p ∧ 0 < q ∧ (p : ℚ) / q ∈ R ∧
      ((∀ x, r.val < Values.vfValueHom (x - a) → f x = f a) ∨
        ∀ x, r.val < Values.vfValueHom (x - a) →
          vfTupleValue (f x - f a) ^ q = c.val ^ q * Values.vfValueHom (x - a) ^ p)

theorem lemma_8_3_canonical (h00 : M ⊨ Axioms.ACVF00)
    (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    {S : Set M} (hsmall : Cardinal.mk S < κ)
    (f : (Fin k → VFType (M := M)) → (Fin 1 → VFType (M := M)) → (Fin m → VFType (M := M)))
    (hf : S.Definable LRV (unaryFamilyGraph f)) :
    ∃ U : Set (Fin k ⊕ Fin 1 → M), S.Definable LRV U ∧ (∀ z ∈ U, ∀ i, iVF (z i)) ∧
      (∀ b : Fin k → VFType (M := M), {a : VFType (M := M) |
        Sum.elim (vfValues b) (vfValues ![a]) ∉ U}.Finite) ∧
      ∃ R : Finset ℚ, (∀ s ∈ R, 0 < s) ∧ ∀ (b : Fin k → VFType (M := M)) (a : VFType (M := M)),
        Sum.elim (vfValues b) (vfValues ![a]) ∈ U →
        unaryLocalSlope (insert a.val (S ∪ Set.range (vfValues b))) R a (fun x => f b ![x]) := by
  let U := unaryGoodLocus f
  have hfinite (b : Fin k → VFType (M := M)) : {a : VFType (M := M) |
      Sum.elim (vfValues b) (vfValues ![a]) ∉ U}.Finite := by
    have h := unaryGoodLocus_finite_exception hc hκ hs hsmall (rawRVSpace (M := M) 1)
      (rawRVSpace_rvCoded 1) hf b
    have hinj : Function.Injective (fun a : VFType (M := M) => (![a] : Fin 1 → VFType (M := M))) :=
      fun _ _ he => congrFun he 0
    exact h.preimage hinj.injOn
  refine ⟨U, unaryGoodLocus_definable hf, fun z hz => hz.1, hfinite, ?_⟩
  by_cases hm : 0 < m
  · let v := Values.presentationValuation (M := M)
    letI : Valued (VFType (M := M)) (Values.presentationType (M := M)) := Valued.mk' v
    have hv := Values.presentation_compatible (M := M)
    obtain ⟨N, D, hND⟩ := unary_family_uniform_positive_power_germ hc hκ hs hsmall hv hm f hf
    let F := ((Finset.Icc 1 N).product (Finset.Icc 1 D)).image (fun t : ℕ × ℕ => (t.1 : ℚ) / t.2)
    let R := insert 1 F
    refine ⟨R, ?_, fun b a ha => ?_⟩
    · intro t ht
      rcases Finset.mem_insert.mp ht with rfl | ht
      · exact zero_lt_one
      obtain ⟨⟨p, q⟩, hpq, rfl⟩ := Finset.mem_image.mp ht
      obtain ⟨hp, hq⟩ := Finset.mem_product.mp hpq
      have hp' : 0 < p := (Finset.mem_Icc.mp hp).1
      have hq' : 0 < q := (Finset.mem_Icc.mp hq).1
      exact div_pos (by exact_mod_cast hp') (by exact_mod_cast hq')
    let B := S ∪ Set.range (vfValues b)
    let T := insert a.val B
    let u : Fin (k + 1) → VFType (M := M) := Fin.snoc b a
    let g := centeredUnaryFamily v hm f u
    have hgraph : T.Definable LRV (unaryScalarGraph g) := by
      apply (unaryScalarFamilyGraph_fibre_definable (centeredUnaryFamily_definable v hv hm hf) u).mono
      rintro z (hz | ⟨i, rfl⟩)
      · exact Set.mem_insert_of_mem _ (Or.inl hz)
      · refine Fin.lastCases ?_ (fun i => ?_) i
        · simpa only [vfValues, u, Fin.snoc_last] using (Set.mem_insert a.val B)
        · simpa only [vfValues, u, Fin.snoc_castSucc] using
            (Set.mem_insert_of_mem a.val (show (b i).val ∈ B from Or.inr (Set.mem_range_self i)))
    have he (x : VFType (M := M)) :
        vfTupleValue (f b ![x] - f b ![a]) = Values.vfValueHom (g x) := by
      simp only [vfTupleValue, dif_pos hm, g, u, centeredUnaryFamily, Fin.init_snoc, Fin.snoc_last] <;> rfl
    rcases hND b a ha with hzero | hp
    · have hR : (1 : ℚ) / (1 : ℕ) ∈ R := by simp only [Nat.cast_one, div_one, R, Finset.mem_insert_self]
      have hzero' : ∀ᶠ x in 𝓝 a, x ≠ a → g x = 0 := by
        filter_upwards [hzero] with x hx _
        simp only [g, u, centeredUnaryFamily, Fin.init_snoc, Fin.snoc_last, hx, sub_self] <;> rfl
      obtain ⟨r, hr, hrd⟩ := gammaConstantGerm_has_named_radius h00 hc hgraph a
        ((exists_gammaPuncturedBallHolds_iff_eventually hv a _).mpr hzero')
      refine ⟨1, r, GammaSyntax.one_definable _, by simpa only [T, Set.insert_idem] using hrd,
        1, 1, zero_lt_one, zero_lt_one, hR, Or.inl (fun x hx => ?_)⟩
      by_cases hxa : x = a
      · rw [hxa]
      · have hval := hr x hxa hx
        funext i
        have hi := value_le_dominantCoordinate v (f b ![x] - f b ![a]) hm i
        have hgi : dominantCoordinate v (f b ![x] - f b ![a]) hm = g x := by
          simp only [g, u, centeredUnaryFamily, Fin.init_snoc, Fin.snoc_last]
        rw [hgi, hval, map_zero] at hi
        by_contra hn
        exact (v.ne_zero_iff.mpr (sub_ne_zero.mpr hn)) (le_antisymm hi zero_le)
    · obtain ⟨p, q, hp, hpN, hq, hqD, s, hs', hg⟩ := hp
      obtain ⟨c, r, hcr, hcd, hrd⟩ := gammaPowerGerm_has_named_witnesses h00 hc hgraph a p q hq
        (exists_gammaPowerGerm hv g a s hs' p q hq.ne' hg)
      have hF : (p : ℚ) / q ∈ F := Finset.mem_image.mpr
        ⟨(p, q), Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hp, hpN⟩, Finset.mem_Icc.mpr ⟨hq, hqD⟩⟩, rfl⟩
      have hR : (p : ℚ) / q ∈ R := Finset.mem_insert.mpr (Or.inr hF)
      refine ⟨c, r, ?_, ?_, p, q, hp, hq, hR, Or.inr (fun x hx => ?_)⟩
      · simpa only [T, Set.insert_idem] using hcd
      · simpa only [T, Set.insert_idem] using hrd
      · by_cases hxa : x = a
        · simp only [hxa, sub_self, vfTupleValue_zero, map_zero,
            zero_pow hq.ne', zero_pow hp.ne', mul_zero]
        · rw [he]
          exact (hcr x hxa hx).2
  · have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
    subst m
    refine ⟨{1}, by simp, fun b a ha => ⟨1, 1, GammaSyntax.one_definable _, GammaSyntax.one_definable _,
      1, 1, zero_lt_one, zero_lt_one, by simp, Or.inl (fun x hx => ?_)⟩⟩
    funext i
    exact i.elim0

end SpecialTransformations.Section8
end UnarySlope
