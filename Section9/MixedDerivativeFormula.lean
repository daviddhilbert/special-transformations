import Section9.MixedJacobian
import Section9.PartialDerivativeFormula

/-! A formula for full differentiation on a fixed-label mixed fibre.
The labels stay among the free variables. The quantifiers over small
increments also check that the graph is defined throughout the ball. -/

set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.DefinableGeometry.Space.ofEmbedding
  SpecialTransformations.Section4.rawVFSpace SpecialTransformations.Section4.rawRVSpace
  SpecialTransformations.Section4.rawMixedSpace

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8
open SpecialTransformations.DefinableGeometry

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r s : ℕ}

local notation "VF" => VFType (M := M)
local notation "V" => Fin n → VF
local notation "v" => Values.vfValueHom (M := M)

private abbrev Pair (n r s : ℕ) := (Fin n ⊕ Fin r) ⊕ (Fin n ⊕ Fin s)
private abbrev Entry (n : ℕ) := Fin n × Fin n
private abbrev LinearCode (n r s : ℕ) := Pair n r s ⊕ Entry n
private abbrev TolCode (n r s : ℕ) := LinearCode n r s ⊕ Fin 1
private abbrev RadCode (n r s : ℕ) := TolCode n r s ⊕ Fin 1
private abbrev InputCode (n r s : ℕ) := RadCode n r s ⊕ Fin n
private abbrev TestCode (n r s : ℕ) := InputCode n r s ⊕ Fin n
private abbrev Arithmetic (n : ℕ) :=
  (Fin n ⊕ Fin n) ⊕ ((Fin n ⊕ Fin n) ⊕ (Entry n ⊕ Fin 1))

private def atBase : Pair n r s → TestCode n r s :=
  Sum.inl ∘ Sum.inl ∘ Sum.inl ∘ Sum.inl ∘ Sum.inl

private def atInput : Fin n → TestCode n r s := Sum.inl ∘ Sum.inr

private def atBranch : Pair n r s → TestCode n r s :=
  Sum.elim (Sum.elim atInput (atBase ∘ Sum.inl ∘ Sum.inr))
    (Sum.elim Sum.inr (atBase ∘ Sum.inr ∘ Sum.inr))

private def atArithmetic : Arithmetic n → TestCode n r s :=
  Sum.elim (Sum.elim (atBase ∘ Sum.inl ∘ Sum.inl) atInput)
    (Sum.elim (Sum.elim (atBase ∘ Sum.inr ∘ Sum.inl) Sum.inr)
      (Sum.elim (Sum.inl ∘ Sum.inl ∘ Sum.inl ∘ Sum.inl ∘ Sum.inr)
        (Sum.inl ∘ Sum.inl ∘ Sum.inl ∘ Sum.inr)))

private def aTerm (j : Fin n) : FreeCommRing (Arithmetic n) := FreeCommRing.of (.inl (.inl j))
private def bTerm (j : Fin n) : FreeCommRing (Arithmetic n) := FreeCommRing.of (.inl (.inr j))

private noncomputable def residualTerm (i : Fin n) : LRV.Term (Arithmetic n) :=
  RingSyntax.ofRingTerm (FirstOrder.Ring.termOfFreeCommRing
    (FreeCommRing.of (.inr (.inl (.inr i))) - FreeCommRing.of (.inr (.inl (.inl i))) -
      ∑ k, FreeCommRing.of (.inr (.inr (.inl (i, k)))) * (bTerm k - aTerm k)))

private noncomputable def scaleTerm (j : Fin n) : LRV.Term (Arithmetic n) :=
  RingSyntax.ofRingTerm (FirstOrder.Ring.termOfFreeCommRing
    (FreeCommRing.of (.inr (.inr (.inr 0))) * (bTerm j - aTerm j)))

private def passesRemainder (z : Arithmetic n → M) : Prop :=
  (∀ j, z (.inl (.inl j)) = z (.inl (.inr j))) ∨
    ∀ i, ∃ j, ¬ termValueLe (scaleTerm j) (residualTerm i) z

private theorem passesRemainder_definable (S : Set M) :
    S.Definable LRV {z : Arithmetic n → M | passesRemainder z} := by
  change S.Definable LRV
    ({z : Arithmetic n → M | ∀ j, z (.inl (.inl j)) = z (.inl (.inr j))} ∪
      {z : Arithmetic n → M | ∀ i, ∃ j, ¬ termValueLe (scaleTerm j) (residualTerm i) z})
  apply Set.Definable.union
  · simp only [Set.ofPred_forall]
    exact Set.definable_iInter_of_finite (fun j =>
      (Set.DefinableFun.proj LRV (i := (Sum.inl (.inl j) : Arithmetic n))).ofPred_eq
        (Set.DefinableFun.proj LRV (i := (Sum.inl (.inr j) : Arithmetic n))))
  · simp only [Set.ofPred_forall, Set.ofPred_exists]
    exact Set.definable_iInter_of_finite (fun i => Set.definable_iUnion_of_finite
      (fun j => (termValueLe_definable S (scaleTerm j) (residualTerm i)).compl))

private def passesAtRadius (G : Set (Pair n r s → M)) (z : RadCode n r s → M) : Prop :=
  ∀ b : Fin n → M, b ∈ uniformBall (fun i => z (.inl (.inl (.inl (.inl (.inl i))))))
    (z (.inr 0)) → ∃ y : Fin n → M,
      Sum.elim (Sum.elim z b) y ∘ atBranch ∈ G ∧
      passesRemainder (Sum.elim (Sum.elim z b) y ∘ atArithmetic)

private theorem passesAtRadius_definable {S : Set M} {G : Set (Pair n r s → M)}
    (hG : S.Definable LRV G) : S.Definable LRV {z | passesAtRadius G z} := by
  let box : (Fin n ⊕ Fin n) ⊕ Fin 1 → InputCode n r s :=
    Sum.elim (Sum.elim (fun i => .inl (.inl (.inl (.inl (.inl (.inl i)))))) Sum.inr)
      (fun _ => .inl (.inr 0))
  exact (((uniformBallRelation_definable S n).preimage_comp box).himp
    (((hG.preimage_comp atBranch).inter
      ((passesRemainder_definable S).preimage_comp atArithmetic)).exists_of_finite)).forall_of_finite

private def derivativeTests (G : Set (Pair n r s → M)) (z : LinearCode n r s → M) : Prop :=
  ∀ e : Fin 1 → M, (iVF (e 0) ∧ e 0 ≠ iVFZero) →
    ∃ d : Fin 1 → M, (iVF (d 0) ∧ d 0 ≠ iVFZero) ∧ passesAtRadius G (Sum.elim (Sum.elim z e) d)

private theorem derivativeTests_definable {S : Set M} {G : Set (Pair n r s → M)}
    (hG : S.Definable LRV G) : S.Definable LRV {z | derivativeTests G z} :=
  ((properRadiusAt_definable S (.inr 0 : TolCode n r s)).himp
    (((properRadiusAt_definable S (.inr 0 : RadCode n r s)).inter
      (passesAtRadius_definable hG)).exists_of_finite)).forall_of_finite

private def linearCode (a : V × (Fin r → CanonicalRV.RVSort M))
    (y : V × (Fin s → CanonicalRV.RVSort M)) (D : Matrix (Fin n) (Fin n) VF) :
    LinearCode n r s → M :=
  Sum.elim (Sum.elim (mixedValues a) (mixedValues y)) (fun i => (D i.1 i.2).val)

attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

private theorem passesRemainder_iff (hn : 0 < n) (a b y z : V) (D : Matrix (Fin n) (Fin n) VF) (e : VF) :
    let w : Arithmetic n → VF := Sum.elim (Sum.elim a b)
      (Sum.elim (Sum.elim y z) (Sum.elim (fun i => D i.1 i.2) (fun _ => e)))
    passesRemainder (fun k => (w k).val) ↔
      b = a ∨ v e * vfTupleValue (b - a) < vfTupleValue (z - y - Matrix.toLin' D (b - a)) := by
  intro w
  let err := z - y - Matrix.toLin' D (b - a)
  have hres (i : Fin n) : (residualTerm i).realize (fun k => (w k).val) = (err i).val := by
    dsimp only [residualTerm]
    rw [RingSyntax.realizes, FirstOrder.Ring.realize_termOfFreeCommRing]
    simp only [map_sub, map_sum, map_mul, aTerm, bTerm, FreeCommRing.lift_of]
    change (z i - y i - ∑ k, D i k * (b k - a k)).val = (err i).val
    have he : err i = z i - y i - ∑ k, D i k * (b k - a k) := by
      simp only [err, Pi.sub_apply, Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
    rw [he]
  have hscale (j : Fin n) : (scaleTerm j).realize (fun k => (w k).val) = (e * (b j - a j)).val := by
    dsimp only [scaleTerm]
    rw [RingSyntax.realizes, FirstOrder.Ring.realize_termOfFreeCommRing]
    simp only [map_sub, map_mul, aTerm, bTerm, FreeCommRing.lift_of]
    rfl
  have hval (i j : Fin n) : (¬ termValueLe (scaleTerm j) (residualTerm i) (fun k => (w k).val)) ↔
      v e * v ((b - a) j) < v (err i) := by
    rw [termValueLe_iff_vfValue _ _ (hscale j) (hres i), not_le, map_mul]
    rfl
  change ((∀ j, (a j).val = (b j).val) ∨
    ∀ i, ∃ j, ¬ termValueLe (scaleTerm j) (residualTerm i) (fun k => (w k).val)) ↔
    b = a ∨ v e * vfTupleValue (b - a) < vfTupleValue err
  simp only [hval]
  refine or_congr ⟨fun h => funext fun j => (Subtype.ext (h j)).symm, fun h j => by rw [h]⟩ ⟨?_, ?_⟩
  · intro h
    obtain ⟨i, hi⟩ := vfTupleValue_eq_component err hn
    obtain ⟨j, hj⟩ := h i
    rw [hi]
    exact (mul_le_mul' le_rfl (vfTupleValue_le_component _ j)).trans_lt hj
  · intro h i
    obtain ⟨j, hj⟩ := vfTupleValue_eq_component (b - a) hn
    exact ⟨j, hj ▸ h.trans_le (vfTupleValue_le_component err i)⟩

section

variable {S : Set M}
variable {A : DefSet (rawMixedSpace (M := M) n r) S}
variable {B : DefSet (rawMixedSpace (M := M) n s) S}

private abbrev rawGraph (f : Map A B) : Set (Pair n r s → M) :=
  (rawMixedSpace n r).relation (rawMixedSpace n s) f.graph

private theorem mem_rawGraph_iff (f : Map A B) (x : (rawMixedSpace (M := M) n r).Carrier)
    (y : (rawMixedSpace (M := M) n s).Carrier) :
    Sum.elim (mixedValues x) (mixedValues y) ∈ rawGraph f ↔ f.graph x y := by
  let xc : (rawMixedSpace (M := M) n r).domain := ⟨mixedValues x, mixedValues_mem_domain x⟩
  let yc : (rawMixedSpace (M := M) n s).domain := ⟨mixedValues y, mixedValues_mem_domain y⟩
  have hx : (rawMixedSpace n r).decode xc = x := decode_mixedValues x
  have hy : (rawMixedSpace n s).decode yc = y := decode_mixedValues y
  have h := (rawMixedSpace n r).relation_decode (rawMixedSpace n s) f.graph xc yc
  rw [hx, hy] at h
  exact h

private theorem passesAtRadius_iff (hn : 0 < n) (f : Map A B) (p : A)
    (D : Matrix (Fin n) (Fin n) VF) (e d : VF) (hd : d ≠ 0) :
    passesAtRadius (rawGraph f) (Sum.elim (Sum.elim (linearCode p.val (f p).val D) ![e.val]) ![d.val]) ↔
    ∀ b : V, v d < vfTupleValue (b - p.val.1) →
      ∃ hb : (b, p.val.2) ∈ A.carrier,
        let q : A := ⟨(b, p.val.2), hb⟩
        (f q).val.2 = (f p).val.2 ∧
          (b = p.val.1 ∨ v e * vfTupleValue (b - p.val.1) <
            vfTupleValue ((f q).val.1 - (f p).val.1 - Matrix.toLin' D (b - p.val.1))) := by
  let z := Sum.elim (Sum.elim (linearCode p.val (f p).val D) ![e.val]) ![d.val]
  have hbranch (b y : V) : Sum.elim (Sum.elim z (vfValues b)) (vfValues y) ∘ atBranch =
      Sum.elim (mixedValues (b, p.val.2)) (mixedValues (y, (f p).val.2)) := by
    funext k
    rcases k with ((k | k) | (k | k)) <;> rfl
  have htest (b y : V) :
      passesRemainder (Sum.elim (Sum.elim z (vfValues b)) (vfValues y) ∘ atArithmetic) ↔
        b = p.val.1 ∨ v e * vfTupleValue (b - p.val.1) <
          vfTupleValue (y - (f p).val.1 - Matrix.toLin' D (b - p.val.1)) := by
    let w : Arithmetic n → VF := Sum.elim (Sum.elim p.val.1 b)
      (Sum.elim (Sum.elim (f p).val.1 y) (Sum.elim (fun i => D i.1 i.2) (fun _ => e)))
    have hw : Sum.elim (Sum.elim z (vfValues b)) (vfValues y) ∘ atArithmetic =
        fun i => (w i).val := by
      funext i
      rcases i with ((i | i) | ((i | i) | (i | i))) <;> first | rfl | (fin_cases i; rfl)
    rw [hw]
    exact passesRemainder_iff hn p.val.1 b (f p).val.1 y D e
  constructor
  · intro h b hb
    obtain ⟨yr, hg, ht⟩ := h (vfValues b)
      ((mem_uniformBall_iff_tupleValue hn p.val.1 b d hd).mpr hb)
    have hy := hg.choose_spec.choose
    obtain ⟨y, hy⟩ := hy.1
    change vfValues y = yr at hy
    subst yr
    rw [hbranch, mem_rawGraph_iff] at hg
    obtain ⟨q, hq, he⟩ := hg
    have hq' : q = ⟨(b, p.val.2), hq ▸ q.property⟩ := Subtype.ext hq
    refine ⟨hq ▸ q.property, ?_⟩
    rw [← hq']
    have hLabel := congrArg (fun z : V × (Fin s → CanonicalRV.RVSort M) => z.2) he
    have hValue := congrArg (fun z : V × (Fin s → CanonicalRV.RVSort M) => z.1) he
    change (f q).val.1 = y at hValue
    exact ⟨hLabel, hValue.symm ▸ (htest b y).mp ht⟩
  · intro h br hbr
    let b : V := fun i => ⟨br i, (hbr i).2.1⟩
    have hb := (mem_uniformBall_iff_tupleValue hn p.val.1 b d hd).mp hbr
    obtain ⟨ha, hl, ht⟩ := h b hb
    let q : A := ⟨(b, p.val.2), ha⟩
    refine ⟨vfValues (f q).val.1, ?_, (htest b (f q).val.1).mpr ht⟩
    rw [show br = vfValues b from rfl, hbranch, mem_rawGraph_iff]
    exact ⟨q, rfl, Prod.ext rfl hl⟩

private theorem derivativeTests_iff (hn : 0 < n) (f : Map A B) (p : A)
    (D : Matrix (Fin n) (Fin n) VF) :
    derivativeTests (rawGraph f) (linearCode p.val (f p).val D) ↔
      HasMixedVFDerivativeAt f p (Matrix.toLin' D) := by
  classical
  let a : V := p.val.1
  let t : Fin r → CanonicalRV.RVSort M := p.val.2
  let u : Fin s → CanonicalRV.RVSort M := (f p).val.2
  have hnear (δ : Values.Gamma (M := M)) (x : V) :
      x ∈ vfBall a δ ↔ δ.val < vfTupleValue (x - a) := by
    constructor
    · intro h
      obtain ⟨j, hj⟩ := vfTupleValue_eq_component (x - a) hn
      rw [hj]
      exact h j
    · exact fun h j => h.trans_le (vfTupleValue_le_component (x - a) j)
  constructor
  · intro h
    have htest (ε : Values.Gamma (M := M)) :
        ∃ δ : Values.Gamma (M := M), ∀ b ∈ vfBall a δ,
          ∃ hb : (b, t) ∈ A.carrier, let q : A := ⟨(b,t), hb⟩
          (f q).val.2 = u ∧
            (b = a ∨ ε.val * vfTupleValue (b - a) <
              vfTupleValue ((f q).val.1 - (f p).val.1 - Matrix.toLin' D (b - a))) := by
      obtain ⟨e, he, hve⟩ := gamma_has_vf_representative ε
      obtain ⟨ds, hd, ht⟩ := h ![e.val] ⟨e.property, fun he' => he (Subtype.ext he')⟩
      let d : VF := ⟨ds 0, hd.1⟩
      have hd₀ : d ≠ 0 := fun h => hd.2 (congrArg Subtype.val h)
      have hds : ds = ![d.val] := funext fun i => by fin_cases i; rfl
      rw [hds] at ht
      refine ⟨GammaThresholdGeometry.vfGamma d hd₀, fun b hb => ?_⟩
      have h := (passesAtRadius_iff hn f p D e d hd₀).mp ht b ((hnear _ b).mp hb)
      simpa only [hve] using h
    let F (b : V) : V := if hb : (b,t) ∈ A.carrier then (f ⟨(b,t), hb⟩).val.1 else 0
    obtain ⟨δ, hδ⟩ := htest 1
    have hChart : IsVFChartAt f p F := by
      refine ⟨δ, fun b hb => ?_⟩
      obtain ⟨hA, hl, _⟩ := hδ b hb
      have he : F b = (f ⟨(b,t), hA⟩).val.1 := dif_pos hA
      exact ⟨hA, Prod.ext he.symm hl⟩
    refine ⟨F, hChart, fun ε => ?_⟩
    obtain ⟨r, hr⟩ := htest ε
    refine ⟨r, fun x hx hclose => ?_⟩
    have hdx : (a + x) - a = x := add_sub_cancel_left a x
    have hb : a + x ∈ vfBall a r := (hnear _ _).mpr (by rwa [hdx])
    obtain ⟨hA, _, ht⟩ := hr (a + x) hb
    have h := ht.resolve_left (fun he => hx (by rw [← hdx, he, sub_self]))
    rw [hdx] at h
    rw [show F (a + x) = (f ⟨(a + x, t), hA⟩).val.1 from dif_pos hA, hChart.center]
    exact h
  · rintro ⟨F, hChart, hF⟩ e he
    have hc := hChart.center
    obtain ⟨ρ, hρ⟩ := hChart
    let c : VF := ⟨e 0, he.1⟩
    have hc₀ : c ≠ 0 := fun h => he.2 (congrArg Subtype.val h)
    obtain ⟨δ, hδ⟩ := hF (GammaThresholdGeometry.vfGamma c hc₀)
    obtain ⟨d, hd, hvd⟩ := gamma_has_vf_representative (max ρ δ)
    have hes : e = ![c.val] := funext fun i => by fin_cases i; rfl
    rw [hes]
    refine ⟨![d.val], ⟨d.property, fun hd' => hd (Subtype.ext hd')⟩,
      (passesAtRadius_iff hn f p D c d hd).mpr fun b hb => ?_⟩
    have hball : b ∈ vfBall a (max ρ δ) := (hnear _ _).mpr (hvd ▸ hb)
    obtain ⟨hA, heq⟩ := hρ b (vfBall_anti (le_max_left _ _) hball)
    have hlabel := congrArg (fun q : V × (Fin s → CanonicalRV.RVSort M) => q.2) heq
    refine ⟨hA, hlabel, ?_⟩
    by_cases ha : b = a
    · exact Or.inl ha
    · right
      have h := hδ (b - a) (sub_ne_zero.mpr ha)
        ((show δ.val ≤ (max ρ δ).val from le_max_right _ _).trans_lt ((hnear _ _).mp hball))
      have he : (p.val.1 : V) + (b - a) = b := by change a + (b - a) = b; abel
      have hVF := congrArg (fun q : V × (Fin s → CanonicalRV.RVSort M) => q.1) heq
      change (f ⟨(b,p.val.2),hA⟩).val.1 = F b at hVF
      rwa [he, hc, ← hVF] at h

/-- The derivative locus can be restricted by any same-base definable
condition on its matrix. This permits the determinant-one restriction
for special bijections. -/
def mixedDerivativeLocus (f : Map A B) (Q : Matrix (Fin n) (Fin n) VF → Prop) :
    Set (rawMixedSpace (M := M) n r).Carrier :=
  {x | ∃ p : A, p.val = x ∧ ∃ D, Q D ∧ HasMixedVFDerivativeAt f p (Matrix.toLin' D)}

theorem mixedDerivativeLocus_definable (hn : 0 < n) (f : Map A B)
    (Q : Matrix (Fin n) (Fin n) VF → Prop)
    (hQ : S.Definable LRV {z : Entry n → M | ∃ D, Q D ∧ (fun i => (D i.1 i.2).val) = z}) :
    (rawMixedSpace (M := M) n r).Definable S (mixedDerivativeLocus f Q) := by
  let E : Set (LinearCode n r s → M) := {z |
    z ∘ Sum.inl ∈ rawGraph f ∧ z ∘ Sum.inr ∈
      {w : Entry n → M | ∃ D, Q D ∧ (fun i => (D i.1 i.2).val) = w} ∧
    derivativeTests (rawGraph f) z}
  have hG : S.Definable LRV (rawGraph f) := f.graph_definable
  have hE : S.Definable LRV E := (hG.preimage_comp Sum.inl).inter
    ((hQ.preimage_comp Sum.inr).inter (derivativeTests_definable hG))
  let π : Fin n ⊕ Fin r → LinearCode n r s := Sum.inl ∘ Sum.inl
  have hproj := hE.image_comp π
  have he : (rawMixedSpace (M := M) n r).preimage (mixedDerivativeLocus f Q) =
      (fun z => z ∘ π) '' E := by
    ext x
    constructor
    · rintro ⟨hx, p, hp, D, hD, hd⟩
      refine ⟨linearCode p.val (f p).val D,
        ⟨?_, ⟨D, hD, rfl⟩, (derivativeTests_iff hn f p D).mpr hd⟩, ?_⟩
      · exact (mem_rawGraph_iff f _ _).mpr ⟨p, rfl, rfl⟩
      · exact (congrArg mixedValues hp).trans (mixedValues_decode ⟨x,hx⟩)
    · rintro ⟨z, ⟨hg, ⟨D, hD, hmat⟩, ht⟩, rfl⟩
      obtain ⟨hx, hy, p, hp, hpy⟩ := hg
      have hcode : linearCode p.val (f p).val D = z := by
        funext i
        rcases i with ((i | i) | i)
        · exact (congrFun (congrArg mixedValues hp) i).trans (congrFun (mixedValues_decode ⟨_,hx⟩) i)
        · exact (congrFun (congrArg mixedValues hpy) i).trans (congrFun (mixedValues_decode ⟨_,hy⟩) i)
        · exact congrFun hmat i
      exact ⟨hx, p, hp, D, hD, (derivativeTests_iff hn f p D).mp (hcode.symm ▸ ht)⟩
  change S.Definable LRV ((rawMixedSpace (M := M) n r).preimage _)
  rw [he]
  exact hproj

private theorem matrixCode_vf_definable (S : Set M) :
    S.Definable LRV {z : Entry n → M | ∀ i, iVF (z i)} := by
  simp only [Set.ofPred_forall]
  exact Set.definable_iInter_of_finite (fun i =>
    ((definableAt_sort S .vf).raw_definable).preimage_comp (fun _ : Fin 1 => i))

theorem mixedDifferentiabilityLocus_definable (hn : 0 < n) (f : Map A B) :
    (rawMixedSpace (M := M) n r).Definable S
      {x | ∃ p : A, p.val = x ∧ ∃ L, HasMixedVFDerivativeAt f p L} := by
  have hQ : S.Definable LRV {z : Entry n → M |
      ∃ D : Matrix (Fin n) (Fin n) VF, True ∧ (fun i => (D i.1 i.2).val) = z} := by
    convert matrixCode_vf_definable (n := n) S using 1
    ext z
    exact ⟨by rintro ⟨D, _, rfl⟩ i; exact (D i.1 i.2).property,
      fun h => ⟨fun i j => ⟨z (i,j), h (i,j)⟩, trivial, funext fun _ => rfl⟩⟩
  convert mixedDerivativeLocus_definable hn f (fun _ => True) hQ using 1
  ext x
  constructor
  · rintro ⟨p, hp, L, hL⟩
    exact ⟨p, hp, LinearMap.toMatrix' L, trivial, by
      simpa only [Matrix.toLin'_toMatrix'] using hL⟩
  · rintro ⟨p, hp, D, _, hD⟩
    exact ⟨p, hp, Matrix.toLin' D, hD⟩

private noncomputable def determinantTerm (n : ℕ) : LRV.Term (Entry n) :=
  let P : Matrix (Fin n) (Fin n) (FreeCommRing (Entry n)) := fun i j => FreeCommRing.of (i,j)
  RingSyntax.ofRingTerm (FirstOrder.Ring.termOfFreeCommRing P.det)

private theorem determinantTerm_realizes (D : Matrix (Fin n) (Fin n) VF) :
    (determinantTerm n).realize (fun i => (D i.1 i.2).val) = D.det.val := by
  dsimp only [determinantTerm]
  rw [RingSyntax.realizes, FirstOrder.Ring.realize_termOfFreeCommRing, RingHom.map_det]
  congr 1
  congr 1
  ext i j
  exact FreeCommRing.lift_of _ _

private theorem determinantOneCodes_definable (S : Set M) :
    S.Definable LRV {z : Entry n → M |
      ∃ D : Matrix (Fin n) (Fin n) VF, D.det = 1 ∧ (fun i => (D i.1 i.2).val) = z} := by
  let t := determinantTerm n
  have hone : S.DefinableFun LRV (fun _ : Entry n → M => iVFOne) :=
    DefinableConstants.constant (DefinableConstants.function_symbol
      (L := LRV) Fn.vfOne Fin.elim0 (fun i => i.elim0))
  have hdef := (matrixCode_vf_definable (n := n) S).inter
    ((t.definableFun_realize.mono (Set.empty_subset S)).ofPred_eq hone)
  convert hdef using 1
  ext z
  constructor
  · rintro ⟨D, hD, rfl⟩
    exact ⟨fun i => (D i.1 i.2).property, (determinantTerm_realizes D).trans (congrArg Subtype.val hD)⟩
  · rintro ⟨hVF, he⟩
    let D : Matrix (Fin n) (Fin n) VF := fun i j => ⟨z (i,j), hVF (i,j)⟩
    exact ⟨D, Subtype.ext ((determinantTerm_realizes D).symm.trans he), rfl⟩

theorem mixedJacobianOneLocus_definable (hn : 0 < n) (f : Map A B) :
    (rawMixedSpace (M := M) n r).Definable S
      (mixedDerivativeLocus f (fun D => D.det = 1)) :=
  mixedDerivativeLocus_definable hn f _ (determinantOneCodes_definable S)

/-- The determinant of the full derivative in a fixed-label chart,
with its value left as a free VF coordinate. -/
def mixedJacobianCodes (f : Map A B) : Set (((Fin n ⊕ Fin r) ⊕ Fin 1) → M) :=
  {z | ∃ p : A, mixedValues p.val = z ∘ Sum.inl ∧
    ∃ L, HasMixedVFDerivativeAt f p L ∧ (LinearMap.toMatrix' L).det.val = z (.inr 0)}

theorem mixedJacobianCodes_definable (hn : 0 < n) (f : Map A B) :
    S.Definable LRV (mixedJacobianCodes f) := by
  let E₀ : Set (LinearCode n r s → M) := {z | z ∘ Sum.inl ∈ rawGraph f ∧
    (∀ i, iVF (z (.inr i))) ∧ derivativeTests (rawGraph f) z}
  have hG : S.Definable LRV (rawGraph f) := f.graph_definable
  have h₀ : S.Definable LRV E₀ := (hG.preimage_comp Sum.inl).inter
    (((matrixCode_vf_definable (n := n) S).preimage_comp Sum.inr).inter
      (derivativeTests_definable hG))
  let η : Entry n → LinearCode n r s ⊕ Fin 1 := Sum.inl ∘ Sum.inr
  let E : Set ((LinearCode n r s ⊕ Fin 1) → M) := {z | z ∘ Sum.inl ∈ E₀ ∧
    (determinantTerm n).realize (z ∘ η) = z (.inr 0)}
  have hterm : S.DefinableFun LRV (fun z : (LinearCode n r s ⊕ Fin 1) → M =>
      (determinantTerm n).realize (z ∘ η)) := by
    let g (z : (LinearCode n r s ⊕ Fin 1) → M) := z ∘ η
    have hg : S.DefinableMap LRV g := fun _ => Set.DefinableFun.proj LRV
    exact @Set.DefinableFun.comp M LRV _ (Entry n) (LinearCode n r s ⊕ Fin 1) S _
      inferInstance g hg ((determinantTerm n).definableFun_realize.mono (Set.empty_subset S))
  have hE : S.Definable LRV E := (h₀.preimage_comp Sum.inl).inter
    (hterm.ofPred_eq (Set.DefinableFun.proj LRV))
  let π : (Fin n ⊕ Fin r) ⊕ Fin 1 → LinearCode n r s ⊕ Fin 1 :=
    Sum.elim (Sum.inl ∘ Sum.inl ∘ Sum.inl) Sum.inr
  have he : mixedJacobianCodes f = (fun z => z ∘ π) '' E := by
    ext z
    constructor
    · rintro ⟨p, hp, L, hL, hJ⟩
      let D := LinearMap.toMatrix' L
      let w := Sum.elim (linearCode p.val (f p).val D) (z ∘ Sum.inr)
      have hd : HasMixedVFDerivativeAt f p (Matrix.toLin' D) := by
        simpa only [D, Matrix.toLin'_toMatrix'] using hL
      refine ⟨w, ⟨⟨?_, fun i => (D i.1 i.2).property, (derivativeTests_iff hn f p D).mpr hd⟩,
        (determinantTerm_realizes D).trans hJ⟩, ?_⟩
      · exact (mem_rawGraph_iff f _ _).mpr ⟨p, rfl, rfl⟩
      · funext i
        cases i with
        | inl i => exact congrFun hp i
        | inr i => rfl
    · rintro ⟨w, ⟨⟨hg, hVF, ht⟩, hJ⟩, rfl⟩
      obtain ⟨hx, hy, p, hp, hpy⟩ := hg
      let D : Matrix (Fin n) (Fin n) VF := fun i j => ⟨w (η (i,j)), hVF (i,j)⟩
      have hcode : linearCode p.val (f p).val D = w ∘ Sum.inl := by
        funext i
        rcases i with ((i | i) | i)
        · exact (congrFun (congrArg mixedValues hp) i).trans (congrFun (mixedValues_decode ⟨_,hx⟩) i)
        · exact (congrFun (congrArg mixedValues hpy) i).trans (congrFun (mixedValues_decode ⟨_,hy⟩) i)
        · rfl
      refine ⟨p, ?_, Matrix.toLin' D, (derivativeTests_iff hn f p D).mp (hcode.symm ▸ ht), ?_⟩
      · exact (congrArg mixedValues hp).trans (mixedValues_decode ⟨_,hx⟩)
      · rw [LinearMap.toMatrix'_toLin']
        exact (determinantTerm_realizes D).symm.trans hJ
  rw [he]
  exact hE.image_comp π

end

end SpecialTransformations.Section9
