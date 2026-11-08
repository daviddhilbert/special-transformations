import Section8.PairedDifference
import Section8.GammaRadiusBase
import Section3.GammaRealMap
import Section8.BijectionSlope

section

/-! Select the multiplier and a valid radius over the original Gamma
base from a first-order relation of all pairwise witnesses. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

namespace SpecialTransformations.Section8

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem named_pairwiseGammaLaw_of_definable_witnesses (h00 : M ⊨ Axioms.ACVF00)
    (B : Base (M := M)) (A : Set M) (f : VFType (M := M) → VFType (M := M))
    (a : VFType (M := M)) (P : Set (Fin 2 → M))
    (hP : DefinableOverBase B (fun _ => .rv) P) (hne : P.Nonempty)
    (hProper : ∀ z ∈ P, Proper z)
    (hsem : ∀ z : Fin 2 → M, ∀ h : Proper z,
      z ∈ P ↔ rvPairwiseGammaLaw A f a (⟨z 1, (h 1).1⟩ : CanonicalRV.RVSort M) (codeValue (z 0))) :
    ∃ (r : Values.Gamma (M := M)) (t : CanonicalRV.RVSort M), t ≠ 0 ∧
      GammaDefinableClosureAtBase B r ∧ DefinableClosureAtBase B .rv t.val ∧
      rvPairwiseGammaLaw A f a t r := by
  obtain ⟨w, hw⟩ := hne
  let t : CanonicalRV.RVSort M := ⟨w 1, (hProper w hw 1).1⟩
  have ht : t ≠ 0 := fun h =>
    (hProper w hw 1).2 ((congrArg Subtype.val h).trans RVOperations.zero_val)
  let r₀ := codeValue (w 0)
  have hr₀ : rvPairwiseGammaLaw A f a t r₀ := (hsem w (hProper w hw)).mp hw
  have htd : DefinableClosureAtBase B .rv t.val := by
    have h := hP.image_real (fun _ : Fin 1 => (1 : Fin 2))
    change DefinableOverBase B (fun _ : Fin 1 => .rv) {z | z 0 ∈ ({t.val} : Set M)}
    convert h using 1 <;> try rfl
    ext z
    constructor
    · intro hz
      refine ⟨w, hw, ?_⟩
      funext i
      fin_cases i
      exact hz.symm
    · rintro ⟨u, hu, he⟩
      let t' : CanonicalRV.RVSort M := ⟨u 1, (hProper u hu 1).1⟩
      have hr : rvPairwiseGammaLaw A f a t' (codeValue (u 0)) := (hsem u (hProper u hu)).mp hu
      exact (congrFun he 0).symm.trans (congrArg Subtype.val (rvPairwiseGammaLaw_unique hr hr₀))
  let R : Set (Values.Gamma (M := M)) := {r | rvPairwiseGammaLaw A f a t r}
  have hR : GammaDefinableOverBase B R := by
    have ht' := htd.preimage_real (fun _ : Fin 2 => .rv) (fun _ : Fin 1 => (1 : Fin 2))
    have hp := (hP.inter ht').image_real (fun _ : Fin 1 => (0 : Fin 2))
    change DefinableOverBase B (fun _ : Fin 1 => .rv) {z | z 0 ∈ Values.gammaPullback R}
    convert hp using 1 <;> try rfl
    ext z
    constructor
    · intro hz
      let hz₀ : NonzeroRV (z 0) := ⟨hz.choose, hz.choose_spec.choose⟩
      have hr := (gammaPullback_mem_codeValue_iff R (z 0) hz₀).mp hz
      let u : Fin 2 → M := ![z 0, t.val]
      have hu : Proper u := by
        intro i
        fin_cases i
        · exact hz₀
        · exact ⟨t.property, (hProper w hw 1).2⟩
      refine ⟨u, ⟨(hsem u hu).mpr hr, ⟨rfl, fun i => (hu i).1⟩⟩, ?_⟩
      funext i
      fin_cases i
      rfl
    · rintro ⟨u, ⟨hu, ⟨htu, _⟩⟩, he⟩
      have hz : z 0 = u 0 := (congrFun he 0).symm
      change z 0 ∈ Values.gammaPullback R
      rw [hz]
      apply (gammaPullback_mem_codeValue_iff R (u 0) (hProper u hu 0)).mpr
      let t' : CanonicalRV.RVSort M := ⟨u 1, (hProper u hu 1).1⟩
      have h : t' = t := Subtype.ext htu
      change rvPairwiseGammaLaw A f a t (codeValue (u 0))
      rw [← h]
      exact (hsem u (hProper u hu)).mp hu
  obtain ⟨r, hr, hrd⟩ := gamma_upper_ray_has_definable_radius_base h00 B hR ⟨r₀, hr₀⟩
    (by
      intro x hx y hxy
      have he : x.val ≤ y.val := hxy
      exact ⟨fun b hb => hx.1 b (he.trans_lt hb), fun b b' hb hb' => hx.2 b b' (he.trans_lt hb) (he.trans_lt hb')⟩)
    (fun r h => rvPairwiseGammaLaw_of_larger r h)
  exact ⟨r, t, ht, hrd, htd, hr⟩

end SpecialTransformations.Section8

end

section

/-! The paired-law witness formula over the original Gamma base.
Every first-order operation uses the sorted graph or a definable real
relation of balls and differences. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

namespace SpecialTransformations.Section8

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def rvWitnessSort : Fin 3 → SortTag := ![.vf, .rv, .rv]

def rvWitnessUnpack (z : Fin 3 → M) : Fin 1 ⊕ Fin 2 → M :=
  Sum.elim (fun _ => z 0) ![z 1, z 2]

private theorem rvDifferenceWitnesses_gamma_definable (hc : CanonicalStructure.IsCanonical (M := M))
    {B : Base (M := M)} {G : Set (Fin 2 → M)}
    (hG : DefinableOverBase B (fun _ => .vf) G) :
    DefinableOverBase B rvWitnessSort {z | z ∈ sortedUniverse rvWitnessSort ∧ rvWitnessUnpack z ∈ rvDifferenceWitnesses G} := by
  let sz : Fin 4 → SortTag := ![.vf, .rv, .rv, .vf]
  let sw : Fin 6 → SortTag := ![.vf, .rv, .rv, .vf, .vf, .vf]
  let takeZ : Fin 4 → Fin 6 := Fin.castAdd 2
  let takeP : Fin 3 → Fin 4 := Fin.castSucc
  let pickGraph : Fin 2 → Fin 6 := ![4, 5]
  let pickCentre : Fin 2 → Fin 4 := ![0, 3]
  let box : (Fin 1 ⊕ Fin 1) ⊕ Fin 1 → Fin 6 :=
    Sum.elim (Sum.elim (fun _ => 0) (fun _ => 4)) (fun _ => 1)
  let R : Set (Fin 6 → M) := {w | w ∈ sortedUniverse sw ∧
    (![w 4] : Fin 1 → M) ∈ rvUniformBall (fun _ => w 0) (w 1) ∧
    ¬ rvDifferenceClause (w 0) (w 3) (w 4) (w 5) (w 2)}
  have hR : DefinableOver B.real sw R := by
    have hSort := (sortedUniverse_definable B.real sw).raw_definable
    have hBox := (rvUniformBallRelation_definable B.real 1).preimage_comp box
    have hClause := (rvDifferenceClause_definable B.real (0 : Fin 6) 3 4 5 2).compl
    apply raw_definableOver_sorted hc B.real sw R _ (fun _ h => h.1)
    convert hSort.inter (hBox.inter hClause) using 1
    ext w
    have h₁ : (![w 4] : Fin 1 → M) = fun _ => w 4 := by funext i; fin_cases i; rfl
    simp only [R, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_preimage,
      h₁, box, Function.comp_apply, Sum.elim_inl, Sum.elim_inr]
  have hBad := (hG.inter_real_preimage sw R hR pickGraph).image_real takeZ
  have hs : sw ∘ takeZ = sz := by funext i; fin_cases i <;> rfl
  rw [hs] at hBad
  have hCentre := hG.preimage_real sz pickCentre
  let S : Set (Fin 4 → M) := {z | z ∈ sortedUniverse sz ∧ NonzeroRV (z 1) ∧ NonzeroRV (z 2)}
  have hS : DefinableOver B.real sz S :=
    raw_definableOver_sorted hc B.real sz S
      ((sortedUniverse_definable B.real sz).raw_definable.inter
        (((nonzero_rv_definable B.real).preimage_comp (fun _ : Fin 1 => (1 : Fin 4))).inter
          ((nonzero_rv_definable B.real).preimage_comp (fun _ : Fin 1 => (2 : Fin 4)))))
      (fun _ h => h.1)
  have h := ((hCentre.inter (real_definableOverBase B sz S hS)).inter hBad.compl).image_real takeP
  have hsp : sz ∘ takeP = rvWitnessSort := by funext i; fin_cases i <;> rfl
  rw [hsp] at h
  convert h using 1
  ext z
  -- The finite vectors record the centre output and the two possible competitors.
  have htake (w : Fin 4 → M) : w ∘ takeP = z ↔
      w 0 = z 0 ∧ w 1 = z 1 ∧ w 2 = z 2 := by
    constructor
    · intro h
      exact ⟨congrFun h 0, congrFun h 1, congrFun h 2⟩
    · rintro ⟨h₀, h₁, h₂⟩
      funext i
      fin_cases i <;> assumption
  have htakeZ (w : Fin 6 → M) (z : Fin 4 → M) :
      w ∘ takeZ = z ↔ w 0 = z 0 ∧ w 1 = z 1 ∧ w 2 = z 2 ∧ w 3 = z 3 := by
    constructor
    · intro h
      exact ⟨congrFun h 0, congrFun h 1, congrFun h 2, congrFun h 3⟩
    · rintro ⟨h₀, h₁, h₂, h₃⟩
      funext i
      fin_cases i <;> assumption
  have hgraph (x : Fin 2 → M) (hx : x ∈ G) : ∀ i, iVF (x i) := hG.proper x hx
  simp only [Set.mem_ofPred_eq, Set.mem_image, Set.mem_inter_iff, Set.mem_compl_iff, htake, htakeZ]
  -- The remaining equality is by explicit construction of the typed witnesses.
  constructor
  · rintro ⟨hz, u, hu, hr, ht, hbad⟩
    let w : Fin 4 → M := ![z 0, z 1, z 2, u 0]
    have hw : w ∈ sortedUniverse sz := by
      intro i
      fin_cases i
      · exact hz 0
      · exact hz 1
      · exact hz 2
      · exact hgraph _ hu 1
    have hcentre : w ∘ pickCentre = ![z 0, u 0] := by funext i; fin_cases i <;> rfl
    refine ⟨w, ⟨⟨⟨by rwa [hcentre], hw⟩, ⟨hw, hr, ht⟩⟩, ⟨hw, ?_⟩⟩, rfl, rfl, rfl⟩
    rintro ⟨v, ⟨hv, _, hb, hfail⟩, he⟩
    obtain ⟨h₀, h₁, h₂, h₃⟩ := (htakeZ v w).mp he
    change v 0 = z 0 at h₀
    change v 1 = z 1 at h₁
    change v 2 = z 2 at h₂
    change v 3 = u 0 at h₃
    apply hbad
    have hv' : v ∘ pickGraph = ![v 4, v 5] := by funext i; fin_cases i <;> rfl
    refine ⟨![v 4, v 5], hv' ▸ hv, ?_, ?_⟩
    · change (![v 4] : Fin 1 → M) ∈ rvUniformBall (fun _ => z 0) (z 1)
      rw [← h₀, ← h₁]
      exact hb
    · change ¬ rvDifferenceClause (z 0) (u 0) (v 4) (v 5) (z 2)
      rw [← h₀, ← h₂, ← h₃]
      exact hfail
  · rintro ⟨w, ⟨⟨⟨hw, hsort⟩, _, hr, ht⟩, _, hno⟩, h₀, h₁, h₂⟩
    have hz : z ∈ sortedUniverse rvWitnessSort := by
      intro i
      fin_cases i
      · exact h₀ ▸ hsort 0
      · exact h₁ ▸ hsort 1
      · exact h₂ ▸ hsort 2
    have hcentre : w ∘ pickCentre = ![z 0, w 3] := by
      funext i
      fin_cases i
      · exact h₀
      · rfl
    refine ⟨hz, ![w 3], ?_, ?_, ?_, ?_⟩
    · rwa [hcentre] at hw
    · change NonzeroRV (z 1)
      exact h₁ ▸ hr
    · change NonzeroRV (z 2)
      exact h₂ ▸ ht
    rintro ⟨x, hx, hb, hfail⟩
    let v : Fin 6 → M := ![w 0, w 1, w 2, w 3, x 0, x 1]
    have hv : v ∈ sortedUniverse sw := by
      intro i
      fin_cases i
      · exact hsort 0
      · exact hsort 1
      · exact hsort 2
      · exact hsort 3
      · exact hgraph _ hx 0
      · exact hgraph _ hx 1
    have hx' : v ∘ pickGraph = x := by funext i; fin_cases i <;> rfl
    refine hno ⟨v, ⟨by rwa [hx'], hv, ?_, ?_⟩, (htakeZ v w).mpr ⟨rfl, rfl, rfl, rfl⟩⟩
    · change (![x 0] : Fin 1 → M) ∈ rvUniformBall (fun _ => w 0) (w 1)
      simpa [rvWitnessUnpack, h₀, h₁] using hb
    · change ¬ rvDifferenceClause (w 0) (w 3) (x 0) (x 1) (w 2)
      simpa [rvWitnessUnpack, h₀, h₂] using hfail

theorem rvPairwiseWitnesses_gamma_definable (hc : CanonicalStructure.IsCanonical (M := M))
    {B : Base (M := M)} {G : Set (Fin 2 → M)} {A : Set M}
    (hG : DefinableOverBase B (fun _ => .vf) G) (hA : DefinableAtBase B .vf A) :
    DefinableOverBase B rvWitnessSort
      {z | z ∈ sortedUniverse rvWitnessSort ∧ rvWitnessUnpack z ∈ rvPairwiseWitnesses A G} := by
  let s : Fin 4 → SortTag := ![.vf, .rv, .rv, .vf]
  let keep : Fin 3 → Fin 4 := Fin.castSucc
  let atCompetitor : Fin 3 → Fin 4 := ![3, 1, 2]
  let box : (Fin 1 ⊕ Fin 1) ⊕ Fin 1 → Fin 4 :=
    Sum.elim (Sum.elim (fun _ => 0) (fun _ => 3)) (fun _ => 1)
  let C : Set (Fin 4 → M) := {w | w ∈ sortedUniverse s ∧
    (fun _ : Fin 1 => w 3) ∈ rvUniformBall (fun _ => w 0) (w 1)}
  have hC : DefinableOver B.real s C := by
    apply raw_definableOver_sorted hc B.real s C _ (fun _ h => h.1)
    convert (sortedUniverse_definable B.real s).raw_definable.inter
      ((rvUniformBallRelation_definable B.real 1).preimage_comp box) using 1
    ext w
    rfl
  have hW := rvDifferenceWitnesses_gamma_definable hc hG
  have hD := hA.preimage_real s (fun _ : Fin 1 => (3 : Fin 4))
  have hQ := hW.preimage_real s atCompetitor
  have hBad := ((real_definableOverBase B s C hC).inter (hD.inter hQ).compl).image_real keep
  have hkeep : s ∘ keep = rvWitnessSort := by funext i; fin_cases i <;> rfl
  rw [hkeep] at hBad
  convert hW.inter hBad.compl using 1
  ext z
  have hkeep' (w : Fin 4 → M) : w ∘ keep = z ↔
      w 0 = z 0 ∧ w 1 = z 1 ∧ w 2 = z 2 := by
    constructor
    · intro h
      exact ⟨congrFun h 0, congrFun h 1, congrFun h 2⟩
    · rintro ⟨h₀, h₁, h₂⟩
      funext i
      fin_cases i <;> assumption
  have hcomp (w : Fin 4 → M) : rvWitnessUnpack (w ∘ atCompetitor) =
      Sum.elim (fun _ : Fin 1 => w 3) (![w 1, w 2] : Fin 2 → M) := by
    rfl
  constructor
  · rintro ⟨hz, hcentre, hall⟩
    refine ⟨⟨hz, hcentre⟩, hz, ?_⟩
    rintro ⟨w, ⟨⟨hw, hb⟩, _, hfail⟩, he⟩
    obtain ⟨h₀, h₁, h₂⟩ := (hkeep' w).mp he
    have hb' : (fun _ : Fin 1 => w 3) ∈
        rvUniformBall (rvWitnessUnpack z ∘ Sum.inl) (rvWitnessUnpack z (.inr 0)) := by
      simpa [rvWitnessUnpack, h₀, h₁] using hb
    obtain ⟨ha, hdiff⟩ := hall _ hb'
    have hs : w ∘ atCompetitor ∈ sortedUniverse rvWitnessSort := by
      intro i
      fin_cases i
      · exact hw 3
      · exact hw 1
      · exact hw 2
    apply hfail
    refine ⟨⟨ha, hw⟩, ⟨hs, ?_⟩, hw⟩
    simpa [hcomp, rvWitnessUnpack, atCompetitor, h₁, h₂] using hdiff
  · rintro ⟨⟨hz, hcentre⟩, _, hno⟩
    refine ⟨hz, hcentre, ?_⟩
    intro b hb
    have hs : iVF (b 0) := by
      obtain ⟨_, _, _, _, h⟩ := hb
      exact (h 0).2.1
    have he : (fun _ : Fin 1 => b 0) = b := by
      funext i
      fin_cases i
      rfl
    let w : Fin 4 → M := ![z 0, z 1, z 2, b 0]
    have hw : w ∈ sortedUniverse s := by
      intro i
      fin_cases i
      · exact hz 0
      · exact hz 1
      · exact hz 2
      · exact hs
    by_contra hfail
    apply hno
    refine ⟨w, ⟨⟨hw, ?_⟩, hw, ?_⟩, (hkeep' w).mpr ⟨rfl, rfl, rfl⟩⟩
    · simpa [w, rvWitnessUnpack, he] using hb
    · rintro ⟨⟨ha, _⟩, ⟨_, hdiff⟩, _⟩
      exact hfail ⟨ha, by simpa [hcomp, w, rvWitnessUnpack, atCompetitor, he] using hdiff⟩

end SpecialTransformations.Section8

end

section

/-! The paired law on a cofinite unary locus over the original Gamma base. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4

namespace SpecialTransformations.Section8

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ] [Valued (VFType (M := M)) Γ]

/-- Name the centre in the real sort and retain the original Gamma names. -/
def pairwisePointBase (B : Base (M := M)) (a : VFType (M := M)) : Base (M := M) :=
  ⟨insert a.val B.real, B.gamma⟩

private theorem pairwiseWitness_proper {G : Set (Fin 2 → M)} {A : Set M} {z : Fin 3 → M}
    (h : rvWitnessUnpack z ∈ rvPairwiseWitnesses A G) :
    NonzeroRV (z 1) ∧ NonzeroRV (z 2) := by
  obtain ⟨⟨_, _, hr, ht, _⟩, _⟩ := h
  exact ⟨hr, ht⟩

private theorem named_pairwise_at_gamma_base (h00 : M ⊨ Axioms.ACVF00)
    (hc : CanonicalStructure.IsCanonical (M := M))
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {B : Base (M := M)} {A : Set M} {f : VFType (M := M) → VFType (M := M)}
    (hW : DefinableOverBase B rvWitnessSort {z | z ∈ sortedUniverse rvWitnessSort ∧
      rvWitnessUnpack z ∈ rvPairwiseWitnesses A (unaryScalarGraph f)})
    (a : VFType (M := M)) (ha : vfValues (![a] : Fin 1 → VFType (M := M)) ∈ rvPairwiseGood A f) :
    ∃ (r : Values.Gamma (M := M)) (t : CanonicalRV.RVSort M), t ≠ 0 ∧
      GammaDefinableClosureAtBase (pairwisePointBase B a) r ∧
      DefinableClosureAtBase (pairwisePointBase B a) .rv t.val ∧ rvPairwiseGammaLaw A f a t r := by
  let T := pairwisePointBase B a
  let e (z : Fin 2 → M) : Fin 3 → M := ![a.val, z 0, z 1]
  let W := rvPairwiseWitnesses A (unaryScalarGraph f)
  let P : Set (Fin 2 → M) := {z | rvWitnessUnpack (e z) ∈ W}
  have he (z : Fin 2 → M) : rvWitnessUnpack (e z) =
      Sum.elim (vfValues (![a] : Fin 1 → VFType (M := M))) z := by
    funext i
    rcases i with i | i <;> fin_cases i <;> rfl
  have hp : ∀ z ∈ P, Proper z := by
    intro z hz i
    obtain ⟨h₁, h₂⟩ := pairwiseWitness_proper hz
    fin_cases i
    · exact h₁
    · exact h₂
  have hP : DefinableOverBase T (fun _ => .rv) P := by
    have hW' := hW.mono (C := T) (Set.subset_insert _ _) Set.Subset.rfl
    have he' : @Set.DefinableMap M LRV (CanonicalStructure.normalize (M := M))
        (Fin 2) (Fin 3) T.real e := by
      rw [normalize_eq_of_isCanonical hc]
      intro i
      fin_cases i
      · exact LRV.definableFun_const _ (Set.mem_insert _ _)
      · exact Set.DefinableFun.proj LRV
      · exact Set.DefinableFun.proj LRV
    convert hW'.preimage_real_map (fun _ => .rv) e he' using 1
    ext z
    constructor
    · intro hz
      have hs : e z ∈ sortedUniverse rvWitnessSort := by
        intro i
        fin_cases i
        · exact a.property
        · exact (hp z hz 0).1
        · exact (hp z hz 1).1
      exact ⟨⟨hs, hz⟩, fun i => (hp z hz i).1⟩
    · exact fun h => h.1.2
  refine named_pairwiseGammaLaw_of_definable_witnesses h00 T A f a P hP ?_ hp ?_
  · obtain ⟨z, hz⟩ := ha.2
    refine ⟨z, ?_⟩
    change rvWitnessUnpack (e z) ∈ W
    rwa [he]
  · intro z hz
    obtain ⟨r, hr⟩ := CanonicalRV.encodedRv_surjective ⟨z 0, (hz 0).1⟩
    have hr' := congrArg Subtype.val hr
    have hr₀ : r ≠ 0 := fun h => (hz 0).2
      (hr'.symm.trans ((CanonicalRV.encodedRv_zero_iff r).mpr h))
    let t : CanonicalRV.RVSort M := ⟨z 1, (hz 1).1⟩
    have ht : t ≠ 0 := fun h => (hz 1).2 ((congrArg Subtype.val h).trans RVOperations.zero_val)
    have hrγ : GammaThresholdGeometry.vfGamma r hr₀ = codeValue (z 0) := by
      have hproper : NonzeroRV (z 0) := hz 0
      rw [codeValue, dif_pos hproper]
      exact Subtype.ext (congrArg Values.vrv hr)
    have hraw : rvValues (![CanonicalRV.encodedRv r, t] : Fin 2 → CanonicalRV.RVSort M) = z := by
      funext i
      fin_cases i
      · exact hr'
      · rfl
    rw [← hrγ, ← rvPairwiseGammaLaw_witness_iff hv A f a r hr₀ t ht]
    change rvWitnessUnpack (e z) ∈ W ↔
      Sum.elim (vfValues (![a] : Fin 1 → VFType (M := M))) _ ∈ W
    rw [he, hraw]

private theorem rvPairwiseGood_gamma_definable {B : Base (M := M)} {A : Set M}
    {f : VFType (M := M) → VFType (M := M)} (hA : DefinableAtBase B .vf A)
    (h : DefinableOverBase B rvWitnessSort {z | z ∈ sortedUniverse rvWitnessSort ∧
      rvWitnessUnpack z ∈ rvPairwiseWitnesses A (unaryScalarGraph f)}) :
    DefinableOverBase B (fun _ => .vf) (rvPairwiseGood A f) := by
    let keep : Fin 1 → Fin 3 := fun _ => 0
    have hW := h.image_real keep
    have h : rvWitnessSort ∘ keep = (fun _ : Fin 1 => .vf) := rfl
    rw [h] at hW
    have h' : DefinableOverBase B (fun _ : Fin 1 => .vf) {z | z 0 ∈ A} := hA
    convert h'.inter hW using 1
    ext z
    constructor
    · rintro ⟨ha, d, hd⟩
      let w : Fin 3 → M := ![z 0, d 0, d 1]
      have hw : rvWitnessUnpack w = Sum.elim z d := by
        funext i
        rcases i with i | i <;> fin_cases i <;> rfl
      have hmem : rvWitnessUnpack w ∈ rvPairwiseWitnesses A (unaryScalarGraph f) := hw.symm ▸ hd
      obtain ⟨hr, ht⟩ := pairwiseWitness_proper hmem
      have hs : w ∈ sortedUniverse rvWitnessSort := by
        intro i
        fin_cases i
        · exact hA.proper _ ha
        · exact hr.1
        · exact ht.1
      refine ⟨ha, w, ⟨hs, hmem⟩, ?_⟩
      funext i
      fin_cases i
      rfl
    · rintro ⟨ha, w, ⟨_, hw⟩, he⟩
      refine ⟨ha, ![w 1, w 2], ?_⟩
      have hz : (fun _ : Fin 1 => w 0) = z := he
      simpa only [rvWitnessUnpack, hz] using hw
theorem lemma_8_5_gamma_base [CharZero (VFType (M := M))]
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    {B : Base (M := M)} (hsmall : Cardinal.mk ↥B.real < κ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hEP : ∀ E : Subfield (VFType (M := M)), ∃ H, E ≤ H ∧ ImmediateHenselianExtension Valued.v E H)
    (f g : VFType (M := M) → VFType (M := M))
    (hf : DefinableOverBase B (fun _ => .vf) (unaryScalarGraph f))
    (hg : DefinableOverBase B (fun _ => .vf) (unaryScalarGraph g))
    (A : Set M) (hA : DefinableAtBase B .vf A) (hInv : ∀ x : VFType (M := M), x.val ∈ A → g (f x) = x) :
    DefinableOverBase B (fun _ => .vf) (rvPairwiseGood A f) ∧
      ({z : Fin 1 → M | z 0 ∈ A} \ rvPairwiseGood A f).Finite ∧
      ∀ a : VFType (M := M), vfValues (![a] : Fin 1 → VFType (M := M)) ∈ rvPairwiseGood A f →
        ∃ (r : Values.Gamma (M := M)) (t : CanonicalRV.RVSort M), t ≠ 0 ∧
          GammaDefinableClosureAtBase (pairwisePointBase B a) r ∧
          DefinableClosureAtBase (pairwisePointBase B a) .rv t.val ∧ rvPairwiseGammaLaw A f a t r := by
    have hW := rvPairwiseWitnesses_gamma_definable hc hf hA
    refine ⟨rvPairwiseGood_gamma_definable hA hW, ?_, named_pairwise_at_gamma_base h00 hc hv hW⟩
    obtain ⟨_, u, hu⟩ := hf.specialize
    obtain ⟨_, v, hv'⟩ := hg.specialize
    obtain ⟨_, w, hw⟩ := hA.specialize
    let S := ((B.real ∪ Set.range (rawTuple u)) ∪ Set.range (rawTuple v)) ∪ Set.range (rawTuple w)
    have hS : Cardinal.mk S < κ := small_union_range hκ _ (small_union_range hκ _
      (small_union_range hκ _ hsmall _) _) _
    have hu' : S.Definable LRV (unaryScalarGraph f) :=
      hu.raw_definable.mono (Set.subset_union_left.trans Set.subset_union_left)
    have hv'' : S.Definable LRV (unaryScalarGraph g) :=
      hv'.raw_definable.mono
        (Set.union_subset (Set.subset_union_left.trans (Set.subset_union_left.trans Set.subset_union_left))
          (Set.subset_union_right.trans Set.subset_union_left))
    have hw' : DefinableAt S .vf A :=
      ⟨hw.1.mono (Set.union_subset (Set.subset_union_left.trans
        (Set.subset_union_left.trans Set.subset_union_left))
        Set.subset_union_right), hw.2⟩
    exact rvPairwiseGood_finite_exception hc hκ hs hS hv hEP f g hu' hv'' A hw' hInv

theorem lemma_8_5_partial_gamma_base [CharZero (VFType (M := M))]
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    {B : Base (M := M)} (hsmall : Cardinal.mk ↥B.real < κ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hEP : ∀ E : Subfield (VFType (M := M)), ∃ H, E ≤ H ∧ ImmediateHenselianExtension Valued.v E H)
    (f : VFType (M := M) → VFType (M := M)) (A C : Set M)
    (hA : A ⊆ {x | iVF x}) (hC : C ⊆ {x | iVF x})
    (hf : DefinableOverBase B (fun _ => .vf) (partialUnaryGraph A f))
    (hbij : Set.BijOn f {x | x.val ∈ A} {y | y.val ∈ C}) :
    DefinableOverBase B (fun _ => .vf) (rvPairwiseGood A f) ∧
      ({z : Fin 1 → M | z 0 ∈ A} \ rvPairwiseGood A f).Finite ∧
      ∀ a : VFType (M := M), vfValues (![a] : Fin 1 → VFType (M := M)) ∈ rvPairwiseGood A f →
        ∃ (r : Values.Gamma (M := M)) (t : CanonicalRV.RVSort M), t ≠ 0 ∧
          GammaDefinableClosureAtBase (pairwisePointBase B a) r ∧
          DefinableClosureAtBase (pairwisePointBase B a) .rv t.val ∧ rvPairwiseGammaLaw A f a t r := by
  have hAd : DefinableAtBase B .vf A := by
    have h := hf.image_real (fun _ : Fin 1 => (0 : Fin 2))
    change DefinableOverBase B (fun _ : Fin 1 => .vf) {z | z 0 ∈ A}
    convert h using 1 <;> try rfl
    ext z
    constructor
    · intro hz
      let x : VFType (M := M) := ⟨z 0, hA hz⟩
      exact ⟨![x.val, (f x).val], ⟨hz, x, rfl, rfl⟩, funext (fun i => by fin_cases i; rfl)⟩
    · rintro ⟨w, hw, rfl⟩
      exact hw.1
  have hGraphVF (F : VFType (M := M) → VFType (M := M)) :
      ∀ w ∈ unaryScalarGraph F, iVF (w 0) := by
    rintro w ⟨x, hx, _⟩
    exact hx ▸ x.property
  have hW := rvPairwiseWitnesses_gamma_definable hc hf hAd
  have heq : rvPairwiseWitnesses A (partialUnaryGraph A f) = rvPairwiseWitnesses A (unaryScalarGraph f) :=
    rvPairwiseWitnesses_congr_on_domain Valued.v hv A
    (fun w hw => hA hw.1) (hGraphVF f) (fun w hw => and_iff_right hw)
  rw [heq] at hW
  refine ⟨rvPairwiseGood_gamma_definable hAd hW, ?_, named_pairwise_at_gamma_base h00 hc hv hW⟩
  obtain ⟨_, d, hd⟩ := hf.specialize
  let S := B.real ∪ Set.range (rawTuple d)
  have hS : Cardinal.mk S < κ := small_union_range hκ B.real hsmall _
  obtain ⟨F, G, hF, hG, hFG⟩ := unaryPartialBijection_definable_extensions hA hC hbij hd.raw_definable
  have hAS : DefinableAt S .vf A := raw_definable_sorted hc S A .vf
    (partialUnaryGraph_domain_definable hA hd.raw_definable) hA
  have hEq : rvPairwiseWitnesses A (unaryScalarGraph f) = rvPairwiseWitnesses A (unaryScalarGraph F) := by
    apply rvPairwiseWitnesses_congr_on_domain Valued.v hv A (hGraphVF f) (hGraphVF F)
    intro w hw
    constructor
    · rintro ⟨x, hx, hy⟩
      exact ⟨x, hx, (congrArg Subtype.val (hFG x (hx.symm ▸ hw)).1).trans hy⟩
    · rintro ⟨x, hx, hy⟩
      exact ⟨x, hx, (congrArg Subtype.val (hFG x (hx.symm ▸ hw)).1).symm.trans hy⟩
  have hgood : rvPairwiseGood A f = rvPairwiseGood A F := by
    unfold rvPairwiseGood
    rw [hEq]
  rw [hgood]
  exact rvPairwiseGood_finite_exception hc hκ hs hS hv hEP F G hF hG A hAS (fun x hx => (hFG x hx).2)

end SpecialTransformations.Section8

end
