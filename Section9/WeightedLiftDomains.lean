module

public import Section9.GoodLiftGluing
public import Section9.WeightedJacobian
public import Section9.PartialDerivativeFormula
public import Section7.CorrespondenceLifting

@[expose] public section

/-! Definable domains for weighted polynomial lifts. On such a domain
the two Jacobian blocks are nonsingular and have the required ratio
throughout the VF fibres. Row weights are witnesses in the construction
of the domains and are absent from their defining formula. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language MvPolynomial
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section7 SpecialTransformations.Section8
open scoped BigOperators

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n d : ℕ}
local notation "VF" => VFType (M := M)

attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

private noncomputable def namedPolynomialTerm {E : Subfield VF} (P : MvPolynomial (Fin d) E) :
    LRV.Term (Fin P.support.card ⊕ Fin d) :=
  RingSyntax.ofRingTerm (FirstOrder.Ring.termOfFreeCommRing (PolynomialZero.expression P))

private noncomputable def namedPolynomialArguments {E : Subfield VF}
    (P : MvPolynomial (Fin d) E) (x : Fin d → M) : Fin P.support.card ⊕ Fin d → M :=
  Sum.elim (fun j => (P.coeff (PolynomialZero.enumeration P j).val).val.val) x

private noncomputable def rawPolynomialValue {E : Subfield VF}
    (P : MvPolynomial (Fin d) E) (x : Fin d → M) : M :=
  (namedPolynomialTerm P).realize (namedPolynomialArguments P x)

private theorem rawPolynomialValue_definable {E : Subfield VF} {S : Set M}
    (hE : ∀ c : E, c.val.val ∈ S) (P : MvPolynomial (Fin d) E) :
    S.DefinableFun LRV (rawPolynomialValue P) := by
  have harg : S.DefinableMap LRV (namedPolynomialArguments P) := by
    rintro (i | i)
    · exact LRV.definableFun_const _ (hE (P.coeff (PolynomialZero.enumeration P i).val))
    · exact Set.DefinableFun.proj LRV
  change S.DefinableFun LRV ((namedPolynomialTerm P).realize ∘ namedPolynomialArguments P)
  exact Set.DefinableFun.comp (g := namedPolynomialArguments P) harg
    ((namedPolynomialTerm P).definableFun_realize.mono (Set.empty_subset S))

private theorem rawPolynomialValue_realizes {E : Subfield VF}
    (P : MvPolynomial (Fin d) E) (x : Fin d → VF) :
    rawPolynomialValue P (rawVF x) = ((P.map E.subtype).eval x).val := by
  let y : Fin P.support.card ⊕ Fin d → VF :=
    Sum.elim (fun j => (P.coeff (PolynomialZero.enumeration P j).val).val) x
  have hy : namedPolynomialArguments P (rawVF x) = fun i => (y i).val := by
    funext i
    cases i <;> rfl
  rw [rawPolynomialValue, hy, namedPolynomialTerm, RingSyntax.realizes,
    FirstOrder.Ring.realize_termOfFreeCommRing, eval_map]
  exact congrArg Subtype.val (PolynomialZero.expression_eval P E.subtype x)

private noncomputable def blockProduct {E : Subfield VF}
    (H : Fin n → MvPolynomial (Fin (n + n)) E) (f : Fin n ↪ Fin (n + n)) :
    MvPolynomial (Fin (n + n)) E :=
  partialJacobianPolynomial f H * ∏ j, X (f j)

private theorem blockProduct_realizes {E : Subfield VF}
    (H : Fin n → MvPolynomial (Fin (n + n)) E) (f : Fin n ↪ Fin (n + n))
    (x : Fin (n + n) → VF) :
    ((blockProduct H f).map E.subtype).eval x =
      (partialJacobianPolynomial f (fun i => (H i).map E.subtype)).eval x * ∏ j, x (f j) := by
  have hmap : (partialJacobianPolynomial f H).map E.subtype =
      partialJacobianPolynomial f (fun i => (H i).map E.subtype) := by
    rw [partialJacobianPolynomial, RingHom.map_det, partialJacobianPolynomial]
    congr 1
    apply Matrix.ext
    intro i j
    change ((pderiv (f j)) (H i)).map E.subtype = (pderiv (f j)) ((H i).map E.subtype)
    rw [pderiv_map]
  rw [blockProduct, map_mul, map_prod, hmap]
  simp only [map_X, map_mul, map_prod, eval_X]

private def polynomialLiftGraph {E : Subfield VF} (H : Fin n → MvPolynomial (Fin (n + n)) E) :
    Set (Fin (n + n) → M) := {x | ∀ i, x ∈ PolynomialZero.zeroSet E (H i)}

private theorem polynomialLiftGraph_definable {E : Subfield VF} {S : Set M}
    (hE : ∀ c : E, c.val.val ∈ S) (H : Fin n → MvPolynomial (Fin (n + n)) E) :
    S.Definable LRV (polynomialLiftGraph H) := by
  simp only [polynomialLiftGraph, Set.ofPred_forall]
  exact Set.definable_iInter_of_finite (fun i =>
    (PolynomialZero.zeroSet_named_definable S E hE (H i)).raw_definable)

private theorem polynomialLiftGraph_iff {E : Subfield VF}
    (H : Fin n → MvPolynomial (Fin (n + n)) E) (a b : Fin n → VF) :
    productTuple (rawVF a) (rawVF b) ∈ polynomialLiftGraph H ↔
      ∀ i, ((H i).map E.subtype).eval (productTuple a b) = 0 := by
  have he : productTuple (rawVF a) (rawVF b) = rawVF (productTuple a b) := by
    apply productTuple_ext
    · intro i; simp [rawVF]
    · intro i; simp [rawVF]
  rw [he]
  apply forall_congr'
  intro i
  rw [eval_map]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨fun j => (productTuple a b j).property, h⟩⟩

private def hasWeightedBlocks {E : Subfield VF} (H : Fin n → MvPolynomial (Fin (n + n)) E)
    (x : Fin (n + n) → M) : Prop :=
  let a := rawPolynomialValue (blockProduct H (productLeft n n)) x
  let b := rawPolynomialValue (blockProduct H (productRight n n)) x
  b ≠ iVFZero ∧ iLe (iRv a) (iRv b) ∧ iLe (iRv b) (iRv a)

private theorem hasWeightedBlocks_definable {E : Subfield VF} {S : Set M}
    (hE : ∀ c : E, c.val.val ∈ S) (H : Fin n → MvPolynomial (Fin (n + n)) E) :
    S.Definable LRV {x | hasWeightedBlocks H x} := by
  let P := blockProduct H (productLeft n n)
  let Q := blockProduct H (productRight n n)
  have hzero : S.DefinableFun LRV (fun _ : Fin (n + n) → M => iVFZero) :=
    DefinableConstants.constant (DefinableConstants.function_symbol
      (L := LRV) Fn.vfZero Fin.elim0 (fun i => i.elim0))
  have hval : S.DefinableMap LRV (fun x : Fin (n + n) → M =>
      ![rawPolynomialValue P x, rawPolynomialValue Q x]) := by
    intro i
    fin_cases i
    · exact rawPolynomialValue_definable hE P
    · exact rawPolynomialValue_definable hE Q
  have he := (termValueEq_definable S (.var (0 : Fin 2)) (.var 1)).preimage_map hval
  have hp := ((rawPolynomialValue_definable hE Q).ofPred_eq hzero).compl
  convert hp.inter he using 1
  ext x
  change hasWeightedBlocks H x ↔ _ ∧ termValueEq _ _ _
  rw [termValueEq_realize]
  rfl

private def weightedLiftDomain {E : Subfield VF} (H : Fin n → MvPolynomial (Fin (n + n)) E) :
    Set (Fin (n + n) → M) :=
  rawLiftDomain (polynomialLiftGraph H) ∩
    {z | ∀ x ∈ polynomialLiftGraph H, iRv ∘ x = z → hasWeightedBlocks H x}

private theorem weightedLiftDomain_definable {E : Subfield VF} {S : Set M}
    (hE : ∀ c : E, c.val.val ∈ S) (H : Fin n → MvPolynomial (Fin (n + n)) E) :
    S.Definable LRV (weightedLiftDomain H) := by
  let ι := Fin (n + n)
  have hA := polynomialLiftGraph_definable hE H
  have heq : S.Definable LRV {w : ι ⊕ ι → M | iRv ∘ w ∘ Sum.inr = w ∘ Sum.inl} := by
    simp only [funext_iff, Set.ofPred_forall, Function.comp_apply]
    exact Set.definable_iInter_of_finite (fun i =>
      ((definable_rvTuple S (ι := ι ⊕ ι)) (.inr i)).ofPred_eq (Set.DefinableFun.proj LRV))
  have hbad := (((hA.preimage_comp (Sum.inr : ι → ι ⊕ ι)).inter heq).inter
    ((hasWeightedBlocks_definable hE H).compl.preimage_comp Sum.inr)).exists_of_finite
  convert (rawLiftDomain_definable S _ hA).inter hbad.compl using 1
  ext z
  change (z ∈ rawLiftDomain (polynomialLiftGraph H) ∧
    (∀ x ∈ polynomialLiftGraph H, iRv ∘ x = z → hasWeightedBlocks H x)) ↔
    z ∈ rawLiftDomain (polynomialLiftGraph H) ∧
      ¬ ∃ x, (x ∈ polynomialLiftGraph H ∧ iRv ∘ x = z) ∧ ¬ hasWeightedBlocks H x
  exact and_congr_right (fun _ => by push Not; tauto)

section

variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
variable (w : Valuation (VFType (M := M)) Γ)
variable (hw : ∀ x y : VFType (M := M), VFValued.predV x y ↔ w x ≤ w y)

include hw in
private theorem hasWeightedBlocks_iff {E : Subfield VF}
    (H : Fin n → MvPolynomial (Fin (n + n)) E) (x : Fin (n + n) → VF) :
    hasWeightedBlocks H (rawVF x) ↔
      let Z := fun i => (H i).map E.subtype
      let A := (partialJacobianPolynomial (productLeft n n) Z).eval x
      let B := (partialJacobianPolynomial (productRight n n) Z).eval x
      let left := A * ∏ j, x (productLeft n n j)
      let right := B * ∏ j, x (productRight n n j)
      right ≠ 0 ∧ w left = w right := by
  simp only [hasWeightedBlocks, rawPolynomialValue_realizes, blockProduct_realizes]
  refine and_congr ?_ ⟨fun h =>
    le_antisymm ((hw _ _).mp h.2) ((hw _ _).mp h.1),
    fun h => ⟨(hw _ _).mpr h.ge, (hw _ _).mpr h.le⟩⟩
  change (_ : VF).val ≠ (0 : VF).val ↔ _
  exact not_congr Subtype.val_inj

private theorem mem_weightedLiftDomain_of_blocks {E : Subfield VF}
    (t s : Fin n → _root_.RVCalc.RV w) (ht : ∀ i, t i ≠ none) (hs : ∀ i, s i ≠ none)
    (H : Fin n → MvPolynomial (Fin (n + n)) E) (α : Fin n → Γ)
    (hH : let u := productTuple t s
      let Z := fun i => (H i).map E.subtype
      (∀ i, IsGammaPolynomial w (fun j => _root_.RVCalc.vrv w (u j)) (α i) (Z i)) ∧
      ¬ IsResidueRoot w u (jacobianValue (fun j => _root_.RVCalc.vrv w (t j)) α)
        (partialJacobianPolynomial (productLeft n n) Z) ∧
      ¬ IsResidueRoot w u (jacobianValue (fun j => _root_.RVCalc.vrv w (s j)) α)
        (partialJacobianPolynomial (productRight n n) Z) ∧
      FibreBijection w {p | ∀ i, (Z i).eval (productTuple p.1 p.2) = 0} t s) :
    productTuple (rawRV w hw t) (rawRV w hw s) ∈ weightedLiftDomain H := by
  let u := productTuple t s
  let Z := fun i => (H i).map E.subtype
  have hu (j : Fin (n + n)) : u j ≠ none := by
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective j
    cases i with
    | inl i =>
      change u (productLeft n n i) ≠ none
      simpa only [u, productTuple_left] using ht i
    | inr i =>
      change u (productRight n n i) ≠ none
      simpa only [u, productTuple_right] using hs i
  refine ⟨?_, fun x hx he => ?_⟩
  · apply (rawLiftDomain_mem_iff w hw (polynomialLiftGraph H) t s).mpr
    have he : {p : (Fin n → VF) × (Fin n → VF) |
        productTuple (rawVF p.1) (rawVF p.2) ∈ polynomialLiftGraph H} =
        {p | ∀ i, (Z i).eval (productTuple p.1 p.2) = 0} :=
      Set.ext (fun p => polynomialLiftGraph_iff H p.1 p.2)
    rw [he]
    exact hH.2.2.2
  · let a : Fin (n + n) → VF := fun j => ⟨x j, by
      have hn : 0 < n := by have := j.isLt; omega
      exact (hx ⟨0, hn⟩).choose j⟩
    have ha : a ∈ RVFibre w u := by
      intro j
      apply (CanonicalRV.equiv w hw).injective
      apply Subtype.ext
      rw [CanonicalRV.equiv_rv]
      have hj := congrFun he j
      have hcode : productTuple (rawRV w hw t) (rawRV w hw s) j =
          (CanonicalRV.equiv w hw (u j)).val := by
        obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective j
        cases i with
        | inl i =>
          change productTuple (rawRV w hw t) (rawRV w hw s) (productLeft n n i) =
            (CanonicalRV.equiv w hw (u (productLeft n n i))).val
          simp only [u, productTuple_left, rawRV]
        | inr i =>
          change productTuple (rawRV w hw t) (rawRV w hw s) (productRight n n i) =
            (CanonicalRV.equiv w hw (u (productRight n n i))).val
          simp only [u, productTuple_right, rawRV]
      exact hj.trans hcode
    have hleft := weightedBlock_value_mul_columns w u hu Z hH.1 (productLeft n n)
      (by simpa only [u, productTuple_left] using hH.2.1) ha
    have hright := weightedBlock_value_mul_columns w u hu Z hH.1 (productRight n n)
      (by simpa only [u, productTuple_right] using hH.2.2.1) ha
    apply (hasWeightedBlocks_iff w hw H a).mpr
    exact ⟨w.ne_zero_iff.mp (hright.trans_ne
      (Finset.prod_ne_zero_iff.mpr fun i _ => (hH.1 i).2.1)), hleft.trans hright.symm⟩

/-- On a finite-to-finite RV correspondence, choose a same-base lift
that agrees, on each pair of RV fibres, with a polynomial system
whose evaluated Jacobian blocks have the weighted determinant ratio.
The chosen system may vary with the RV pair. -/
theorem exists_lift_with_weighted_blocks
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hsat : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    (hB : VFGammaGeneratedBase B)
    (C : Set (Fin (n + n) → M)) (hC : DefinableOverBase B (fun _ => .rv) C)
    (h0 : ∀ z ∈ C, ∀ i, z i ≠ iRVZero)
    (hleft : ∀ b : Fin n → M, {a : Fin n → M | productTuple a b ∈ C}.Finite)
    (hright : ∀ a : Fin n → M, {b : Fin n → M | productTuple a b ∈ C}.Finite) :
    let E := vfDefinableClosureFieldBase B
    ∃ F : Set (Fin (n + n) → M), B.real.Definable LRV F ∧ C ⊆ rawLiftDomain F ∧
      ∀ t s : Fin n → _root_.RVCalc.RV w,
        productTuple (rawRV w hw t) (rawRV w hw s) ∈ C →
        ∃ H : Fin n → MvPolynomial (Fin (n + n)) E,
          ∀ a ∈ RVFibre w t, ∀ b ∈ RVFibre w s,
            let Z := fun i => (H i).map E.subtype
            let z := productTuple a b
            let A := (partialJacobianPolynomial (productLeft n n) Z).eval z * ∏ i, a i
            let D := (partialJacobianPolynomial (productRight n n) Z).eval z * ∏ i, b i
            (productTuple (rawVF a) (rawVF b) ∈ F ↔ ∀ i, (Z i).eval z = 0) ∧
            (productTuple (rawVF a) (rawVF b) ∈ F → D ≠ 0 ∧ w A = w D) := by
  classical
  let E := vfDefinableClosureFieldBase B
  have hE (c : E) : c.val.val ∈ B.real := (mem_generatedBase_vfField B hB c.val).mp c.property
  let Good (z : Fin (n + n) → M) (A : Set (Fin (n + n) → M)) : Prop :=
    ∃ H : Fin n → MvPolynomial (Fin (n + n)) E, A = polynomialLiftGraph H ∧ z ∈ weightedLiftDomain H
  have hloc (z : Fin (n + n) → M) (hz : z ∈ C) :
      ∃ A D : Set (Fin (n + n) → M), B.real.Definable LRV A ∧ B.real.Definable LRV D ∧
        z ∈ D ∧ D ⊆ rawLiftDomain A ∧ ∀ q ∈ D, Good q A := by
    let t (i : Fin n) : _root_.RVCalc.RV w := (CanonicalRV.equiv w hw).symm
      ⟨z (productLeft n n i), by simpa only [sortEval, iRV] using hC.proper z hz (productLeft n n i)⟩
    let s (i : Fin n) : _root_.RVCalc.RV w := (CanonicalRV.equiv w hw).symm
      ⟨z (productRight n n i), by simpa only [sortEval, iRV] using hC.proper z hz (productRight n n i)⟩
    have ht (i : Fin n) : rawRV w hw t i = z (productLeft n n i) := by simp [rawRV, t]
    have hs (i : Fin n) : rawRV w hw s i = z (productRight n n i) := by simp [rawRV, s]
    have he : productTuple (rawRV w hw t) (rawRV w hw s) = z := by
      apply productTuple_ext
      · intro i; simpa only [productTuple_left] using ht i
      · intro i; simpa only [productTuple_right] using hs i
    have hnone : (CanonicalRV.equiv w hw (none : _root_.RVCalc.RV w)).val = iRVZero := by
      rw [← _root_.RVCalc.rv_zero, CanonicalRV.equiv_rv]
      exact RVCalc.rv_zero_eq ‹M ⊨ Axioms.ACVF›
    have ht₀ (i : Fin n) : t i ≠ none := by
      intro h
      have hh := ht i
      rw [rawRV, h, hnone] at hh
      exact h0 z hz _ hh.symm
    have hs₀ (i : Fin n) : s i ≠ none := by
      intro h
      have hh := hs i
      rw [rawRV, h, hnone] at hh
      exact h0 z hz _ hh.symm
    obtain ⟨H, α, hH⟩ := exists_correspondence_weighted_local_polynomials
      hκ hsat h00 B hsmall hB w hw C hC t s ht₀ hs₀ (he.symm ▸ hz) (hright _) (hleft _)
    refine ⟨polynomialLiftGraph H, weightedLiftDomain H, polynomialLiftGraph_definable hE H,
      weightedLiftDomain_definable hE H, ?_, fun _ h => h.1, fun q hq => ⟨H, rfl, hq⟩⟩
    exact he ▸ mem_weightedLiftDomain_of_blocks w hw t s ht₀ hs₀ H α hH
  obtain ⟨k, c, hc⟩ := hC.specialize
  obtain ⟨F, hF, hlift, hGood⟩ := exists_gluedLift_on_good_domains hsat
    B.real (B.real ∪ Set.range (rawTuple c)) Set.subset_union_left
    (small_union_range hκ B.real hsmall (rawTuple c)) C hc.raw_definable
    (fun z hz i => by simpa only [sortEval, iRV] using hC.proper z hz i) Good hloc
  refine ⟨F, hF, hlift, fun t s hz => ?_⟩
  obtain ⟨_, ⟨H, rfl, hD⟩, hGraph⟩ := hGood _ hz
  refine ⟨H, fun a ha b hb => ?_⟩
  have ha' : rawVF a ∈ rawTupleFibre ((productTuple (rawRV w hw t) (rawRV w hw s)) ∘
      productLeft n n) := by
    simpa only [Function.comp_def, productTuple_left] using (rawVF_mem_rawTupleFibre_iff w hw t a).mpr ha
  have hb' : rawVF b ∈ rawTupleFibre ((productTuple (rawRV w hw t) (rawRV w hw s)) ∘
      productRight n n) := by
    simpa only [Function.comp_def, productTuple_right] using (rawVF_mem_rawTupleFibre_iff w hw s b).mpr hb
  have he := hGraph _ ha' _ hb'
  refine ⟨he.trans (polynomialLiftGraph_iff H a b), fun hf => ?_⟩
  have hrv := productTuple_rv_of_rawTupleFibre ha' hb'
  have h := hD.2 _ (he.mp hf) hrv
  have hraw : productTuple (rawVF a) (rawVF b) = rawVF (productTuple a b) := by
    apply productTuple_ext
    · intro i; simp [rawVF]
    · intro i; simp [rawVF]
  rw [hraw] at h
  simpa only [productTuple_left, productTuple_right] using
    (hasWeightedBlocks_iff w hw H (productTuple a b)).mp h

end

end SpecialTransformations.Section9
