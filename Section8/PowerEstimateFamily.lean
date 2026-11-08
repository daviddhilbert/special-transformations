import Section8.UnaryGerm
import Section8.PowerEstimateCore
import Mathlib.Data.Nat.Factorial.Basic
import Section8.MixedLocalFormula
import Section8.GenericOutputBall
import Section4.GammaDefinablePoint
import Section8.GammaRadiusBase
import Section3.GammaRealMap
import Section3.GammaSpecialization

section

/-! Move one or more VF coordinates between the arguments and the
parameters of a family by a coordinate equivalence. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section4

namespace SpecialTransformations.Section8

variable {M : Type} [LRV.Structure M] {k n m k' n' : ℕ}

def reindexVFFamily (e : Fin k ⊕ Fin n ≃ Fin k' ⊕ Fin n')
    (f : (Fin k → VFType (M := M)) → (Fin n → VFType (M := M)) → (Fin m → VFType (M := M)))
    (b : Fin k' → VFType (M := M)) (a : Fin n' → VFType (M := M)) :
    Fin m → VFType (M := M) :=
  f (Sum.elim b a ∘ e ∘ Sum.inl) (Sum.elim b a ∘ e ∘ Sum.inr)

theorem reindexVFFamily_definable (e : Fin k ⊕ Fin n ≃ Fin k' ⊕ Fin n') {S : Set M}
    {f : (Fin k → VFType (M := M)) → (Fin n → VFType (M := M)) → (Fin m → VFType (M := M))}
    (hf : S.Definable LRV (vfFamilyGraph f)) :
    S.Definable LRV (vfFamilyGraph (reindexVFFamily e f)) := by
  let encode : Fin k ⊕ (Fin n ⊕ Fin m) → (Fin k ⊕ Fin n) ⊕ Fin m :=
    Sum.elim (Sum.inl ∘ Sum.inl) (Sum.elim (Sum.inl ∘ Sum.inr) Sum.inr)
  let decode : (Fin k' ⊕ Fin n') ⊕ Fin m → Fin k' ⊕ (Fin n' ⊕ Fin m) :=
    Sum.elim (Sum.elim Sum.inl (Sum.inr ∘ Sum.inl)) (Sum.inr ∘ Sum.inr)
  let i := decode ∘ Sum.map e id ∘ encode
  convert hf.preimage_comp i using 1
  ext z
  constructor
  · rintro ⟨⟨b, a⟩, rfl⟩
    refine ⟨(Sum.elim b a ∘ e ∘ Sum.inl, Sum.elim b a ∘ e ∘ Sum.inr), ?_⟩
    funext j
    rcases j with j | (j | j)
    · cases he : e (.inl j) <;> simp [i, encode, decode, vfValues, he]
    · cases he : e (.inr j) <;> simp [i, encode, decode, vfValues, he]
    · rfl
  · rintro ⟨⟨b, a⟩, h⟩
    let c := Sum.elim b a ∘ e.symm
    let b' := c ∘ Sum.inl
    let a' := c ∘ Sum.inr
    have hc : Sum.elim b' a' = c := by
      funext j
      cases j <;> rfl
    have he : c ∘ e = Sum.elim b a := by
      funext j
      exact congrArg (Sum.elim b a) (e.symm_apply_apply j)
    have hout : reindexVFFamily e f b' a' = f b a := by
      unfold reindexVFFamily
      rw [hc]
      simp only [← Function.comp_assoc, he, Sum.elim_comp_inl, Sum.elim_comp_inr]
    refine ⟨(b', a'), ?_⟩
    funext j
    rcases j with j | (j | j)
    · rcases hidx : e.symm (.inl j) with l | l
      · have he' : e (.inl l) = .inl j := (e.symm_apply_eq.mp hidx).symm
        simpa [vfValues, b', c, hidx, i, encode, decode, he']
          using congrFun h (.inl l)
      · have he' : e (.inr l) = .inl j := (e.symm_apply_eq.mp hidx).symm
        simpa [vfValues, b', c, hidx, i, encode, decode, he']
          using congrFun h (.inr (.inl l))
    · rcases hidx : e.symm (.inr j) with l | l
      · have he' : e (.inl l) = .inr j := (e.symm_apply_eq.mp hidx).symm
        simpa [vfValues, a', c, hidx, i, encode, decode, he']
          using congrFun h (.inl l)
      · have he' : e (.inr l) = .inr j := (e.symm_apply_eq.mp hidx).symm
        simpa [vfValues, a', c, hidx, i, encode, decode, he']
          using congrFun h (.inr (.inl l))
    · change (reindexVFFamily e f b' a' j).val = z (.inr (.inr j))
      rw [hout]
      exact congrFun h (.inr (.inr j))

def horizontalIndices (k n : ℕ) : Fin k ⊕ Fin (n + 1) ≃ Fin (k + 1) ⊕ Fin n :=
  (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv.symm).trans
    ((Equiv.sumCongr (Equiv.refl _) (Equiv.sumComm _ _)).trans
      ((Equiv.sumAssoc _ _ _).symm.trans (Equiv.sumCongr finSumFinEquiv (Equiv.refl _))))

def verticalIndices (k n : ℕ) : Fin k ⊕ Fin (n + 1) ≃ Fin (k + n) ⊕ Fin 1 :=
  (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv.symm).trans
    ((Equiv.sumAssoc _ _ _).symm.trans (Equiv.sumCongr finSumFinEquiv (Equiv.refl _)))

theorem horizontalFamily_eq
    (f : (Fin k → VFType (M := M)) → (Fin (n + 1) → VFType (M := M)) → (Fin m → VFType (M := M)))
    (t : Fin k → VFType (M := M)) (a : Fin n → VFType (M := M)) (b : VFType (M := M)) :
    reindexVFFamily (horizontalIndices k n) f (Fin.snoc t b) a = f t (Fin.snoc a b) := by
  unfold reindexVFFamily
  congr 1
  · funext i
    simp [horizontalIndices, finSumFinEquiv_apply_left]
    exact Fin.snoc_castSucc (α := fun _ => VFType (M := M)) b t i
  · funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · have hlast : Fin.last n = (finSumFinEquiv : Fin n ⊕ Fin 1 ≃ Fin (n + 1)) (.inr 0) := by
        apply Fin.ext
        simp [finSumFinEquiv_apply_right]
      have hparam : (finSumFinEquiv : Fin k ⊕ Fin 1 ≃ Fin (k + 1)) (.inr 0) = Fin.last k := by
        apply Fin.ext
        simp [finSumFinEquiv_apply_right]
      have hidx : horizontalIndices k n (.inr (Fin.last n)) = .inl (Fin.last k) := by
        rw [hlast]
        let E : Fin n ⊕ Fin 1 ≃ Fin (n + 1) := finSumFinEquiv
        change Sum.map finSumFinEquiv id ((Equiv.sumAssoc (Fin k) (Fin 1) (Fin n)).symm
          (.inr ((Equiv.sumComm (Fin n) (Fin 1)) (E.symm (E (.inr 0)))))) = _
        rw [E.symm_apply_apply]
        change Sum.inl (finSumFinEquiv (.inr 0)) = _
        rw [hparam]
      change Sum.elim (Fin.snoc t b) a (horizontalIndices k n (.inr (Fin.last n))) =
        Fin.snoc (α := fun _ => VFType (M := M)) a b (Fin.last n)
      simp only [hidx, Sum.elim_inl, Fin.snoc_last]
    · have hcast : j.castSucc = (finSumFinEquiv : Fin n ⊕ Fin 1 ≃ Fin (n + 1)) (.inl j) := rfl
      rw [hcast]
      simp [horizontalIndices, finSumFinEquiv_apply_left]
      exact (Fin.snoc_castSucc (α := fun _ => VFType (M := M)) b a j).symm

theorem verticalFamily_eq
    (f : (Fin k → VFType (M := M)) → (Fin (n + 1) → VFType (M := M)) → (Fin m → VFType (M := M)))
    (t : Fin k → VFType (M := M)) (a : Fin n → VFType (M := M)) (b : Fin 1 → VFType (M := M)) :
    reindexVFFamily (verticalIndices k n) f (Fin.append t a) b = f t (Fin.snoc a (b 0)) := by
  unfold reindexVFFamily
  congr 1
  · funext i
    simp [verticalIndices, finSumFinEquiv_apply_left]
  · funext i
    rw [← Fin.append_right_eq_snoc a b]
    obtain ⟨j, rfl⟩ := (finSumFinEquiv : Fin n ⊕ Fin 1 ≃ Fin (n + 1)).surjective i
    cases j <;> simp [verticalIndices, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]

end SpecialTransformations.Section8

end

section

/-! The unary base of 8.6. The factorial of the uniform denominator
bound puts all positive unary slopes above one common unit numerator. -/

set_option backward.isDefEq.respectTransparency false

open Filter Topology FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace SpecialTransformations.Section8

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k m : ℕ}

theorem vfTupleValue_unary (x : Fin 1 → VFType (M := M)) :
    vfTupleValue x = Values.vfValueHom (x 0) := by
  obtain ⟨i, hi⟩ := vfTupleValue_eq_component x (by decide)
  fin_cases i
  exact hi

theorem uniform_unary_power_estimate_of_independent (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    {S : Set M} (hsmall : Cardinal.mk S < κ)
    (f : (Fin k → VFType (M := M)) → (Fin 1 → VFType (M := M)) → (Fin m → VFType (M := M)))
    (hf : S.Definable LRV (vfFamilyGraph f)) :
    ∃ Q : ℕ, 0 < Q ∧ ∀ (t : Fin k → VFType (M := M)) (a : Fin 1 → VFType (M := M)),
      AlgebraicIndependent (vfParameterField (S ∪ Set.range (vfValues t))) a →
      ∃ c r, vfPositivePowerEstimate (f t) a 1 Q c r := by
  let v := Values.presentationValuation (M := M)
  letI : Valued (VFType (M := M)) (Values.presentationType (M := M)) := Valued.mk' v
  have hv := Values.presentation_compatible (M := M)
  by_cases hm : 0 < m
  · obtain ⟨N, D, hD⟩ := unary_family_uniform_positive_power_germ hc hκ hs hsmall hv hm f hf
    refine ⟨D.factorial, Nat.factorial_pos D, fun t a ha => ?_⟩
    have hgood : Sum.elim (vfValues t) (vfValues ![a 0]) ∈ unaryGoodLocus f := by
      have hvec : (![a 0] : Fin 1 → VFType (M := M)) = a := by
        funext i
        fin_cases i
        rfl
      rw [hvec]
      refine ⟨?_, ?_⟩
      · rintro (i | i)
        · exact (t i).property
        · exact (a i).property
      · change vfValues a ∉ isolatedInputs {z | Sum.elim (vfValues t) z ∈ vfFamilyGraph f}
        rw [vfFamilyGraph_fibre]
        rintro ⟨radii, h⟩
        exact independent_not_isolated hv hc (vfFamilyGraph_fibre_definable hf t) (by decide) a ha radii h
    have hvec (b : Fin 1 → VFType (M := M)) : (![b 0] : Fin 1 → VFType (M := M)) = b := by
      funext i
      fin_cases i
      rfl
    rcases hD t (a 0) hgood with hconstant | hpower
    · obtain ⟨r, hr⟩ := (exists_gammaPuncturedBallHolds_iff_eventually hv (a 0)
        (fun x => f t ![x] = f t ![a 0])).mpr (hconstant.mono (fun _ h _ => h))
      refine ⟨1, r, fun x hx => ?_⟩
      have he : f t x = f t a := by
        by_cases h : x 0 = a 0
        · rw [← hvec x, ← hvec a, h]
        · rw [vfTupleValue_unary] at hx
          simpa only [hvec] using hr (x 0) h hx
      rw [he, sub_self, vfTupleValue_zero, zero_pow (Nat.factorial_pos D).ne']
      rw [← Values.infinity_eq_zero]
      exact Values.le_infinity (M := M) _
    · obtain ⟨p, q, hp, hpN, hq, hqD, s, hs₀, hg⟩ := hpower
      let g := centeredUnaryFamily v hm f (Fin.snoc t (a 0))
      obtain ⟨c, r, hcr⟩ := exists_gammaPowerGerm hv g (a 0) s hs₀ p q hq.ne' hg
      have hpow : vfPositivePowerEstimate (f t) a p q c r := by
        intro x hx
        rw [vfTupleValue_unary] at hx ⊢
        by_cases h : x 0 = a 0
        · have he : x = a := by rw [← hvec x, ← hvec a, h]
          rw [he, sub_self, Pi.zero_apply, map_zero, zero_pow hp.ne', mul_zero,
            sub_self, vfTupleValue_zero, zero_pow hq.ne']
        · have he : vfTupleValue (f t x - f t a) = Values.vfValueHom (g (x 0)) := by
            rw [← hvec x, ← hvec a]
            simp only [vfTupleValue, dif_pos hm, g, centeredUnaryFamily, Fin.init_snoc, Fin.snoc_last,
              Matrix.cons_val_zero]
            rfl
          rw [he]
          exact (hcr (x 0) h hx).2.ge
      obtain ⟨d, hd⟩ := Nat.dvd_factorial hq hqD
      have hd₀ : 0 < d := Nat.pos_of_ne_zero (by
        intro he
        exact (Nat.factorial_pos D).ne' (by simpa only [he, mul_zero] using hd))
      exact ⟨c, max r 1, hd.symm ▸ vfPositivePowerEstimate_to_unit_numerator hp hd₀ hpow⟩
  · have hm₀ : m = 0 := Nat.eq_zero_of_not_pos hm
    subst m
    refine ⟨1, by decide, fun t a _ => ⟨1, 1, fun x _ => ?_⟩⟩
    have he : f t x = f t a := funext (fun i => i.elim0)
    simp only [he, sub_self, vfTupleValue_zero, pow_one, ← Values.infinity_eq_zero (M := M)]
    exact Values.le_infinity (M := M) _

end SpecialTransformations.Section8

end

section

/-! A horizontal estimate survives a small change in the last
coordinate because the entire RV fibre of valid witnesses is locally
constant. Combine this estimate with the vertical unary estimate. -/

set_option backward.isDefEq.respectTransparency false

open Filter Topology FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace SpecialTransformations.Section8

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k n m : ℕ}

private theorem vfNames_append (t : Fin k → VFType (M := M)) (a : Fin n → VFType (M := M)) :
    Set.range (vfValues (Fin.append t a)) = Set.range (vfValues t) ∪ Set.range (vfValues a) := by
  ext z
  constructor
  · rintro ⟨i, rfl⟩
    obtain ⟨j, rfl⟩ := (finSumFinEquiv : Fin k ⊕ Fin n ≃ Fin (k + n)).surjective i
    cases j with
    | inl j => exact Or.inl ⟨j, by simp [vfValues, finSumFinEquiv_apply_left]⟩
    | inr j => exact Or.inr ⟨j, by simp [vfValues, finSumFinEquiv_apply_right]⟩
  · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact ⟨Fin.castAdd n i, by simp [vfValues]⟩
    · exact ⟨Fin.natAdd k i, by simp [vfValues]⟩

private theorem horizontal_estimate_uniform (hc : CanonicalStructure.IsCanonical (M := M))
    {S : Set M} (hn : 0 < n) (hm : 0 < m)
    (f : (Fin k → VFType (M := M)) → (Fin (n + 1) → VFType (M := M)) → (Fin m → VFType (M := M)))
    (hf : S.Definable LRV (vfFamilyGraph f))
    (t : Fin k → VFType (M := M)) (a : Fin n → VFType (M := M)) (b : VFType (M := M))
    (hb : AlgebraicIndependent (vfParameterField ((S ∪ Set.range (vfValues t)) ∪ Set.range (vfValues a)))
      (![b] : Fin 1 → VFType (M := M)))
    (q : ℕ) (c r : Values.Gamma (M := M))
    (h : vfPositivePowerEstimate (fun x => f t (Fin.snoc x b)) a 1 q c r) :
    ∃ s : Values.Gamma (M := M), ∀ y : VFType (M := M), s.val < Values.vfValueHom (y - b) →
      vfPositivePowerEstimate (fun x => f t (Fin.snoc x y)) a 1 q c r := by
  let B := (S ∪ Set.range (vfValues t)) ∪ Set.range (vfValues a)
  let F := reindexVFFamily (horizontalIndices k n) f
  have hF := reindexVFFamily_definable (horizontalIndices k n) hf
  let encode (z : Fin 1 ⊕ Fin 2 → M) : (Fin (k + 1) ⊕ Fin n) ⊕ Fin 2 → M :=
    Sum.elim (Sum.elim (Fin.snoc (vfValues t) (z (.inl 0))) (vfValues a)) (z ∘ Sum.inr)
  have hencode : B.DefinableMap LRV encode := by
    rintro ((i | i) | i)
    · refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa [encode] using (Set.DefinableFun.proj LRV (A := B) (i := (Sum.inl 0 : Fin 1 ⊕ Fin 2)))
      · simpa [encode] using (LRV.definableFun_const (Fin 1 ⊕ Fin 2)
          (A := B) (Or.inl (Or.inr (Set.mem_range_self j))))
    · exact LRV.definableFun_const _ (Or.inr (Set.mem_range_self i))
    · exact Set.DefinableFun.proj LRV
  let P := encode ⁻¹' estimateRVCodes (vfFamilyGraph F) 1 q
  have hP : B.Definable LRV P := ((estimateRVCodes_definable hF 1 q).mono
    (Set.subset_union_left.trans Set.subset_union_left)).preimage_map hencode
  let γ : Fin 2 → Values.Gamma (M := M) := ![c, r]
  let d := fun i : Fin 2 => (GammaParameters.representatives γ i).val
  have hd (i : Fin 2) : (d i).val ≠ iRVZero := (GammaParameters.representatives γ i).property
  have hγ (i : Fin 2) : Values.gammaOf (d i) (hd i) = γ i :=
    congrFun (GammaParameters.representatives_values γ) i
  have hsem (y : VFType (M := M)) :
      d ∈ rvFibre P ![y] ↔ vfPositivePowerEstimate (fun x => f t (Fin.snoc x y)) a 1 q c r := by
    have he : encode (Sum.elim (vfValues ![y]) (rvValues d)) =
        Sum.elim (Sum.elim (vfValues (Fin.snoc t y)) (vfValues a)) (rvValues d) := by
      funext i
      rcases i with (i | i) | i
      · refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [encode, vfValues]
      · rfl
      · rfl
    change encode (Sum.elim (vfValues ![y]) (rvValues d)) ∈
      estimateRVCodes (vfFamilyGraph F) 1 q ↔ _
    rw [he, mem_estimateRVCodes_iff hn hm F (Fin.snoc t y) a d hd 1 q, hγ 0, hγ 1]
    simp only [γ, Matrix.cons_val_zero, Matrix.cons_val_one]
    have he' : F (Fin.snoc t y) = fun x => f t (Fin.snoc x y) :=
      funext (fun x => horizontalFamily_eq f t x y)
    rw [he']
    rfl
  let v := Values.presentationValuation (M := M)
  letI : Valued (VFType (M := M)) (Values.presentationType (M := M)) := Valued.mk' v
  have hv := Values.presentation_compatible (M := M)
  obtain ⟨s, hs, hstay⟩ := (rvLocallyConstantAt_iff_uniformBall hv (rvFibre P) ![b]).mp
    (rvFibre_locallyConstant_of_independent hc hv hP ![b] hb)
  refine ⟨GammaThresholdGeometry.vfGamma s hs, fun y hy => (hsem y).mp ?_⟩
  have hy' : vfValues (![y] : Fin 1 → VFType (M := M)) ∈ uniformBall (vfValues ![b]) s.val :=
    (mem_uniformBall_iff_tupleValue (by decide) ![b] ![y] s hs).mpr (by
      rw [vfTupleValue_unary]
      exact hy)
  rw [hstay ![y] hy']
  exact (hsem b).mpr h

theorem uniform_power_estimate_of_independent (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    {S : Set M} (hsmall : Cardinal.mk S < κ) (hn : 0 < n)
    (f : (Fin k → VFType (M := M)) → (Fin n → VFType (M := M)) → (Fin m → VFType (M := M)))
    (hf : S.Definable LRV (vfFamilyGraph f)) :
    ∃ Q : ℕ, 0 < Q ∧ ∀ (t : Fin k → VFType (M := M)) (a : Fin n → VFType (M := M)),
      AlgebraicIndependent (vfParameterField (S ∪ Set.range (vfValues t))) a →
      ∃ c r, vfPositivePowerEstimate (f t) a 1 Q c r := by
  induction n generalizing k with
  | zero => omega
  | succ n ih =>
    by_cases hn₀ : n = 0
    · subst n
      exact uniform_unary_power_estimate_of_independent hc hκ hs hsmall f hf
    by_cases hm : 0 < m
    · let H := reindexVFFamily (horizontalIndices k n) f
      let V := reindexVFFamily (verticalIndices k n) f
      have hH := reindexVFFamily_definable (horizontalIndices k n) hf
      have hV := reindexVFFamily_definable (verticalIndices k n) hf
      obtain ⟨QH, hQH, hHlaw⟩ := ih (Nat.pos_of_ne_zero hn₀) H hH
      obtain ⟨QV, hQV, hVlaw⟩ := uniform_unary_power_estimate_of_independent hc hκ hs hsmall V hV
      refine ⟨QH * QV, Nat.mul_pos hQH hQV, fun t z hz => ?_⟩
      let a := Fin.init z
      let b := z (Fin.last n)
      have he : Fin.snoc a b = z := Fin.snoc_init_self z
      have hz' : AlgebraicIndependent (vfParameterField (S ∪ Set.range (vfValues t))) (Fin.snoc a b) :=
        he.symm ▸ hz
      obtain ⟨ha, hb⟩ := independent_snoc_slices _ a b hz'
      have ha' : AlgebraicIndependent (vfParameterField (S ∪ Set.range (vfValues (Fin.snoc t b)))) a := by
        rw [Fin.snoc_eq_append, vfNames_append, ← Set.union_assoc, vfParameterField_union_tuple]
        exact ha
      have hb' : AlgebraicIndependent
          (vfParameterField ((S ∪ Set.range (vfValues t)) ∪ Set.range (vfValues a))) ![b] := by
        rw [vfParameterField_union_tuple]
        exact hb
      have hb'' : AlgebraicIndependent (vfParameterField (S ∪ Set.range (vfValues (Fin.append t a)))) ![b] := by
        rw [vfNames_append, ← Set.union_assoc]
        exact hb'
      obtain ⟨cH, rH, hH'⟩ := hHlaw (Fin.snoc t b) a ha'
      obtain ⟨cV, rV, hV'⟩ := hVlaw (Fin.append t a) ![b] hb''
      have hHL := vfPositivePowerEstimate_to_unit_numerator (p := 1) one_pos hQV hH'
      have hVL := vfPositivePowerEstimate_to_unit_numerator (p := 1) one_pos hQH hV'
      rw [Nat.mul_comm QV QH] at hVL
      have hhor : vfPositivePowerEstimate (fun x => f t (Fin.snoc x b)) a 1 (QH * QV) cH (max rH 1) :=
        (show H (Fin.snoc t b) = (fun x => f t (Fin.snoc x b)) from
          funext (fun x => horizontalFamily_eq f t x b)) ▸ hHL
      obtain ⟨s, hstay⟩ := horizontal_estimate_uniform hc (Nat.pos_of_ne_zero hn₀) hm f hf
        t a b hb' (QH * QV) cH (max rH 1) hhor
      let r := max s (max rV 1)
      refine ⟨min cH cV, max (max rH 1) r, he ▸
        vfPositivePowerEstimate_snoc_of_uniform_slices (f t) a b (QH * QV)
          cH (max rH 1) cV r (fun y hy => hstay y ((show s.val ≤ r.val from le_max_left _ _).trans_lt hy)) ?_⟩
      intro y hy
      have hy' : (max rV 1).val < vfTupleValue ((![y] : Fin 1 → VFType (M := M)) - ![b]) := by
        rw [vfTupleValue_unary]
        exact (show (max rV 1).val ≤ r.val from le_max_right _ _).trans_lt hy
      have h := hVL ![y] hy'
      rw [vfTupleValue_unary, pow_one] at h
      simpa only [V, verticalFamily_eq, Pi.sub_apply, Matrix.cons_val_zero] using h
    · have hm₀ : m = 0 := Nat.eq_zero_of_not_pos hm
      subst m
      refine ⟨1, one_pos, fun t z _ => ⟨1, 1, fun x _ => ?_⟩⟩
      have he : f t x = f t z := funext (fun i => i.elim0)
      simp only [he, sub_self, vfTupleValue_zero, pow_one, ← Values.infinity_eq_zero (M := M)]
      exact Values.le_infinity (M := M) _

end SpecialTransformations.Section8

end

section

/-! The powered estimate has an original real-base definable good locus.
At each point of that locus the two actual Gamma witnesses can be named. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace SpecialTransformations.Section8

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k n m : ℕ}

private theorem gamma_decode_of_proper (d : Fin 2 → M) (h : GammaSyntax.Proper d) (i : Fin 2) :
    GammaSyntax.decode d i = Values.gammaOf ⟨d i, (h i).1⟩ (h i).2 := by
  unfold GammaSyntax.decode GammaParameters.codeValue
  rw [dif_pos (h i)]
  rfl

private theorem estimate_gamma_pair_definable (hc : CanonicalStructure.IsCanonical (M := M))
    {S : Set M} (hn : 0 < n) (hm : 0 < m)
    (f : (Fin k → VFType (M := M)) → (Fin n → VFType (M := M)) → (Fin m → VFType (M := M)))
    (hf : S.Definable LRV (vfFamilyGraph f))
    (t : Fin k → VFType (M := M)) (a : Fin n → VFType (M := M)) (p q : ℕ) :
    GammaSyntax.Definable ((S ∪ Set.range (vfValues t)) ∪ Set.range (vfValues a))
      (fun γ : Fin 2 → Values.Gamma (M := M) => vfPositivePowerEstimate (f t) a p q (γ 0) (γ 1)) := by
  let T := (S ∪ Set.range (vfValues t)) ∪ Set.range (vfValues a)
  let e (d : Fin 2 → M) := Sum.elim (Sum.elim (vfValues t) (vfValues a)) d
  let P := e ⁻¹' estimateRVCodes (vfFamilyGraph f) p q
  have he : T.DefinableMap LRV e := by
    rintro ((i | i) | i)
    · exact LRV.definableFun_const _ (Or.inl (Or.inr (Set.mem_range_self i)))
    · exact LRV.definableFun_const _ (Or.inr (Set.mem_range_self i))
    · exact Set.DefinableFun.proj LRV
  have hP : T.Definable LRV P :=
    ((estimateRVCodes_definable hf p q).mono
      (Set.subset_union_left.trans Set.subset_union_left)).preimage_map he
  have hproper (d : Fin 2 → M) (hd : d ∈ P) : GammaSyntax.Proper d :=
    estimateRVCodes_rv_proper (z := e d) hd
  have hsorted := raw_definableOver_sorted hc T (fun _ => .rv) P hP (fun d hd i => (hproper d hd i).1)
  have hPN := (definableOver_iff_normalized_raw T (fun _ => .rv) P).mp hsorted
  change @Set.Definable M T LRV (CanonicalStructure.normalize (M := M)) (Fin 2)
    {d | GammaSyntax.Proper d ∧ vfPositivePowerEstimate (f t) a p q
      (GammaSyntax.decode d 0) (GammaSyntax.decode d 1)}
  convert hPN.1 using 1
  ext d
  constructor
  · rintro ⟨hd, hp⟩
    let w : Fin 2 → CanonicalRV.RVSort M := fun i => ⟨d i, (hd i).1⟩
    rw [gamma_decode_of_proper d hd 0, gamma_decode_of_proper d hd 1] at hp
    exact (mem_estimateRVCodes_iff hn hm f t a w (fun i => (hd i).2) p q).mpr hp
  · intro hd
    let h := hproper d hd
    let w : Fin 2 → CanonicalRV.RVSort M := fun i => ⟨d i, (h i).1⟩
    refine ⟨h, ?_⟩
    rw [gamma_decode_of_proper d h 0, gamma_decode_of_proper d h 1]
    exact (mem_estimateRVCodes_iff hn hm f t a w (fun i => (h i).2) p q).mp hd

theorem lemma_8_6_canonical (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    {S : Set M} (hsmall : Cardinal.mk S < κ)
    (δ : Values.Gamma (M := M)) (hδ : Values.GammaDefinable S {δ}) (hδ₁ : 1 < δ) (hn : 0 < n)
    (f : (Fin k → VFType (M := M)) → (Fin n → VFType (M := M)) → (Fin m → VFType (M := M)))
    (hf : S.Definable LRV (vfFamilyGraph f)) :
    ∃ Q : ℕ, 0 < Q ∧ ∃ U : Set (Fin k ⊕ Fin n → M), S.Definable LRV U ∧
      ∀ t : Fin k → VFType (M := M),
        (∃ hE : (S ∪ Set.range (vfValues t)).Definable LRV
          {a | a ∈ vfRawUniverse n ∧ Sum.elim (vfValues t) a ∉ U},
          vfDim (rawRVSpace (M := M) 1) (vfObjectOfRaw hE) < n) ∧
        ∀ a : Fin n → VFType (M := M), Sum.elim (vfValues t) (vfValues a) ∈ U →
          ∃ c r : Values.Gamma (M := M),
            Values.GammaDefinable ((S ∪ Set.range (vfValues t)) ∪ Set.range (vfValues a)) {c} ∧
            Values.GammaDefinable ((S ∪ Set.range (vfValues t)) ∪ Set.range (vfValues a)) {r} ∧
            vfPositivePowerEstimate (f t) a 1 Q c r := by
  by_cases hm : 0 < m
  · obtain ⟨Q, hQ, hgeneric⟩ := uniform_power_estimate_of_independent hc hκ hs hsmall hn f hf
    let P := estimateRVCodes (vfFamilyGraph f) 1 Q
    let U : Set (Fin k ⊕ Fin n → M) := {z | ∃ d : Fin 2 → M, Sum.elim z d ∈ P}
    have hU : S.Definable LRV U := (estimateRVCodes_definable hf 1 Q).exists_of_finite
    refine ⟨Q, hQ, U, hU, fun t => ?_⟩
    let B := S ∪ Set.range (vfValues t)
    have hft : B.DefinableMap LRV (fun a : Fin n → M => Sum.elim (vfValues t) a) := by
      rintro (i | i)
      · exact LRV.definableFun_const _ (Or.inr (Set.mem_range_self i))
      · exact Set.DefinableFun.proj LRV
    have hE := (vfRawUniverse_definable B n).inter ((hU.mono Set.subset_union_left).preimage_map hft).compl
    constructor
    · refine ⟨hE, ?_⟩
      apply vfDim_lt_of_no_independent hc hs (small_union_range hκ S hsmall _) _
        (rawRVSpace_rvCoded 1) hn
      intro a ha hind
      obtain ⟨c, r, h⟩ := hgeneric t a hind
      let γ : Fin 2 → Values.Gamma (M := M) := ![c, r]
      let d := fun i => (GammaParameters.representatives γ i).val
      have hd (i : Fin 2) : (d i).val ≠ iRVZero := (GammaParameters.representatives γ i).property
      have hγ (i : Fin 2) : Values.gammaOf (d i) (hd i) = γ i :=
        congrFun (GammaParameters.representatives_values γ) i
      apply ha.2
      refine ⟨rvValues d, (mem_estimateRVCodes_iff hn hm f t a d hd 1 Q).mpr ?_⟩
      rwa [hγ 0, hγ 1]
    · intro a ha
      let T := B ∪ Set.range (vfValues a)
      let A : Set (Fin 2 → Values.Gamma (M := M)) :=
        {γ | vfPositivePowerEstimate (f t) a 1 Q (γ 0) (γ 1)}
      have hA : GammaSyntax.Definable T (fun γ => γ ∈ A) := estimate_gamma_pair_definable hc hn hm f hf t a 1 Q
      have hne : A.Nonempty := by
        obtain ⟨z, hz⟩ := ha
        have hsort : GammaSyntax.Proper z := estimateRVCodes_rv_proper (z := Sum.elim _ z) hz
        let d : Fin 2 → CanonicalRV.RVSort M := fun i => ⟨z i, (hsort i).1⟩
        refine ⟨GammaSyntax.decode z, ?_⟩
        change vfPositivePowerEstimate (f t) a 1 Q (GammaSyntax.decode z 0) (GammaSyntax.decode z 1)
        rw [gamma_decode_of_proper z hsort 0, gamma_decode_of_proper z hsort 1]
        exact (mem_estimateRVCodes_iff hn hm f t a d (fun i => (hsort i).2) 1 Q).mp hz
      have hδ' : Values.GammaDefinable T {δ} :=
        DefinableAt.mono (Set.subset_union_left.trans Set.subset_union_left) hδ
      obtain ⟨γ, hγ, hnamed⟩ := gamma_tuple_definable_point h00 δ hδ' hδ₁ A hA hne
      exact ⟨γ 0, γ 1, hnamed 0, hnamed 1, hγ⟩
  · have hm₀ := Nat.eq_zero_of_not_pos hm
    subst m
    refine ⟨1, one_pos, Set.univ, Set.definable_univ, fun t => ⟨?_, ?_⟩⟩
    · have he : {a | a ∈ vfRawUniverse n ∧ Sum.elim (vfValues t) a ∉ (Set.univ : Set (Fin k ⊕ Fin n → M))} =
          ∅ := by ext a; simp
      let E : Set (Fin n → M) := ∅
      have hE : (S ∪ Set.range (vfValues t)).Definable LRV E := Set.definable_empty
      refine ⟨he.symm ▸ hE, ?_⟩
      apply vfDim_lt_of_no_independent hc hs (small_union_range hκ S hsmall _) _
        (rawRVSpace_rvCoded 1) hn
      intro a ha _
      exact ha.2 (Set.mem_univ _)
    · intro a _
      refine ⟨1, 1, GammaSyntax.one_definable _, GammaSyntax.one_definable _, fun x _ => ?_⟩
      have he : f t x = f t a := funext (fun i => i.elim0)
      simp only [he, sub_self, vfTupleValue_zero, pow_one, ← Values.infinity_eq_zero (M := M)]
      exact Values.le_infinity (M := M) _

end SpecialTransformations.Section8

end

section

/-! Select a pair of witnesses over an original Gamma base. The shift
set is a lower ray. For a fixed shift, the valid open radii form an
upper ray containing its endpoint. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section3.GammaParameters.EndpointLogic (codeValue_surjective)
open SpecialTransformations.Section4

namespace SpecialTransformations.Section8

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n m : ℕ}

theorem vfPowerEstimate_gamma_base_named_pair (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M))
    (δ : Values.Gamma (M := M)) (hδ : GammaDefinableClosureAtBase B δ) (hδ₁ : 1 < δ)
    (f : (Fin n → VFType (M := M)) → Fin m → VFType (M := M))
    (a : Fin n → VFType (M := M)) (p q : ℕ)
    (P : Set (Fin 2 → M)) (hP : DefinableOverBase B (fun _ => .rv) P)
    (hproper : ∀ z ∈ P, Proper z)
    (hsem : ∀ z : Fin 2 → M, Proper z →
      (z ∈ P ↔ vfPositivePowerEstimate f a p q (codeValue (z 0)) (codeValue (z 1))))
    (hne : ∃ c r, vfPositivePowerEstimate f a p q c r) :
    ∃ c r, GammaDefinableClosureAtBase B c ∧ GammaDefinableClosureAtBase B r ∧
      vfPositivePowerEstimate f a p q c r := by
  let A : Set (Values.Gamma (M := M)) := {c | ∃ r, vfPositivePowerEstimate f a p q c r}
  have hA : GammaDefinableOverBase B A := by
    have hp := hP.image_real (fun _ : Fin 1 => (0 : Fin 2))
    change DefinableOverBase B (fun _ : Fin 1 => .rv) {z | z 0 ∈ Values.gammaPullback A}
    convert hp using 1 <;> try rfl
    ext z
    constructor
    · intro hz
      let hz₀ : NonzeroRV (z 0) := ⟨hz.choose, hz.choose_spec.choose⟩
      obtain ⟨r, hr⟩ := (gammaPullback_mem_codeValue_iff A (z 0) hz₀).mp hz
      obtain ⟨t, ht, he⟩ := codeValue_surjective r
      let w : Fin 2 → M := ![z 0, t]
      have hw : Proper w := by intro i; fin_cases i; exact hz₀; exact ht
      refine ⟨w, (hsem w hw).mpr ?_, funext (fun i => by fin_cases i; rfl)⟩
      change vfPositivePowerEstimate f a p q (codeValue (z 0)) (codeValue t)
      rwa [he]
    · rintro ⟨w, hw, he⟩
      have hz : z 0 = w 0 := (congrFun he 0).symm
      change z 0 ∈ Values.gammaPullback A
      rw [hz]
      exact (gammaPullback_mem_codeValue_iff A (w 0) (hproper _ hw 0)).mpr
        ⟨codeValue (w 1), (hsem w (hproper _ hw)).mp hw⟩
  have hdown : ∀ c ∈ A, ∀ d, d ≤ c → d ∈ A := by
    rintro c ⟨r, hr⟩ d hdc
    refine ⟨r, fun x hx => ?_⟩
    exact (mul_le_mul'
      (pow_le_pow_left' (show d.val ≤ c.val from hdc) q) le_rfl).trans (hr x hx)
  obtain ⟨c, ⟨r₀, hr₀⟩, hc⟩ := gamma_lower_ray_has_named_point h00 B hA hne hdown δ hδ hδ₁
  let R : Set (Values.Gamma (M := M)) := {r | vfPositivePowerEstimate f a p q c r}
  have hR : GammaDefinableOverBase B R := by
    have hc' := hc.preimage_real (fun _ : Fin 2 => .rv) (fun _ : Fin 1 => (0 : Fin 2))
    have hp := (hP.inter hc').image_real (fun _ : Fin 1 => (1 : Fin 2))
    change DefinableOverBase B (fun _ : Fin 1 => .rv) {z | z 0 ∈ Values.gammaPullback R}
    convert hp using 1 <;> try rfl
    ext z
    constructor
    · intro hz
      let hz₀ : NonzeroRV (z 0) := ⟨hz.choose, hz.choose_spec.choose⟩
      have hr := (gammaPullback_mem_codeValue_iff R (z 0) hz₀).mp hz
      obtain ⟨t, ht, he⟩ := codeValue_surjective c
      let w : Fin 2 → M := ![t, z 0]
      have hw : Proper w := by intro i; fin_cases i; exact ht; exact hz₀
      refine ⟨w, ⟨(hsem w hw).mpr ?_,
        ⟨(gammaPullback_mem_codeValue_iff _ t ht).mpr he, fun i => (hw i).1⟩⟩,
        funext (fun i => by fin_cases i; rfl)⟩
      change vfPositivePowerEstimate f a p q (codeValue t) (codeValue (z 0))
      rwa [he]
    · rintro ⟨w, ⟨hw, ⟨hcw, _⟩⟩, he⟩
      have hz : z 0 = w 1 := (congrFun he 0).symm
      change z 0 ∈ Values.gammaPullback R
      rw [hz]
      apply (gammaPullback_mem_codeValue_iff R (w 1) (hproper _ hw 1)).mpr
      have hc' : codeValue (w 0) = c := (gammaPullback_mem_codeValue_iff _ (w 0) (hproper _ hw 0)).mp hcw
      have hp' := (hsem w (hproper _ hw)).mp hw
      change vfPositivePowerEstimate f a p q c (codeValue (w 1))
      rwa [← hc']
  obtain ⟨r, hr, hrd⟩ := gamma_upper_ray_has_definable_radius_base h00 B hR ⟨r₀, hr₀⟩
    (fun r hr s hrs x hx => hr x ((show r.val ≤ s.val from hrs).trans_lt hx)) (by
      intro r hr x hx
      have hstep : ∃ s : Values.Gamma (M := M), r < s ∧ s.val < vfTupleValue (x - a) := by
        by_cases he : vfTupleValue (x - a) = Values.infinity
        · obtain ⟨s, hs⟩ := exists_gt r
          exact ⟨s, hs, he.symm ▸ lt_of_le_of_ne (Values.le_infinity _) s.property⟩
        · let d : Values.Gamma (M := M) := ⟨vfTupleValue (x - a), he⟩
          exact exists_between (show r < d from hx)
      obtain ⟨s, hs, hsx⟩ := hstep
      exact hr s hs x hsx)
  exact ⟨c, r, hc, hrd, hr⟩

end SpecialTransformations.Section8

end

section

/-! The full relation of power-estimate witnesses retains the original
Gamma base. Only representatives of the same fixed Gamma tuple are
used in the internal parameter block. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4

namespace SpecialTransformations.Section8

variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF] {k n m g : ℕ}

def vfFamilyIndexEquiv (k n m : ℕ) : Fin k ⊕ (Fin n ⊕ Fin m) ≃ Fin (k + (n + m)) :=
  (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans finSumFinEquiv

def estimateWitnessIndexEquiv (k n : ℕ) : (Fin k ⊕ Fin n) ⊕ Fin 2 ≃ Fin (k + n + 2) :=
  (Equiv.sumCongr finSumFinEquiv (Equiv.refl _)).trans finSumFinEquiv

def estimateWitnessSort (k n : ℕ) : Fin (k + n + 2) → SortTag :=
  Sum.elim (fun _ => .vf) (fun _ => .rv) ∘
    (finSumFinEquiv : Fin (k + n) ⊕ Fin 2 ≃ Fin (k + n + 2)).symm

private def estimatePrefixGraph {S : Set M}
    (Q : Relation S g (k + (n + m)) (fun _ => .vf)) :
    Set ((Fin g ⊕ Fin k) ⊕ (Fin n ⊕ Fin m) → M) :=
  {z | ((fun i => z (.inl (.inl i))),
    Sum.elim (fun i => z (.inl (.inr i))) (z ∘ Sum.inr) ∘ (vfFamilyIndexEquiv k n m).symm) ∈ Q.carrier}

private theorem estimatePrefixGraph_definable {S : Set M}
    (hc : CanonicalStructure.IsCanonical (M := M))
    (Q : Relation S g (k + (n + m)) (fun _ => .vf)) :
    S.Definable LRV (estimatePrefixGraph Q) := by
  let e : Fin g ⊕ Fin (k + (n + m)) → (Fin g ⊕ Fin k) ⊕ (Fin n ⊕ Fin m) :=
    Sum.elim (Sum.inl ∘ Sum.inl)
      (Sum.elim (Sum.inl ∘ Sum.inr) Sum.inr ∘ (vfFamilyIndexEquiv k n m).symm)
  have hQ := Q.definable
  rw [normalize_eq_of_isCanonical hc] at hQ
  convert hQ.preimage_comp e using 1
  ext z
  have hz : (z ∘ e) ∘ Sum.inr =
      Sum.elim (fun i => z (.inl (.inr i))) (z ∘ Sum.inr) ∘ (vfFamilyIndexEquiv k n m).symm := by
    funext i
    cases h : (vfFamilyIndexEquiv k n m).symm i <;> simp [e, h]
  change (_, _) ∈ Q.carrier ↔ (_, (z ∘ e) ∘ Sum.inr) ∈ Q.carrier
  rw [hz]
  rfl

private def estimateWitnessRelation {S : Set M} (hc : CanonicalStructure.IsCanonical (M := M))
    (Q : Relation S g (k + (n + m)) (fun _ => .vf)) (p q : ℕ) (mode : PowerComparison) :
    Relation S g (k + n + 2) (estimateWitnessSort k n) where
  carrier := {z | Proper z.1 ∧ z.2 ∈ sortedUniverse (estimateWitnessSort k n) ∧
    z.2 ∘ estimateWitnessIndexEquiv k n ∈
      estimateRVCodes {w | attachEstimatePrefix z.1 w ∈ estimatePrefixGraph Q} p q mode}
  definable := by
    rw [normalize_eq_of_isCanonical hc]
    let E := estimateWitnessIndexEquiv k n
    let idx : ((Fin g ⊕ Fin k) ⊕ Fin n) ⊕ Fin 2 → Fin g ⊕ Fin (k + n + 2) :=
      Sum.elim (Sum.elim (Sum.elim Sum.inl (Sum.inr ∘ E ∘ Sum.inl ∘ Sum.inl))
        (Sum.inr ∘ E ∘ Sum.inl ∘ Sum.inr)) (Sum.inr ∘ E ∘ Sum.inr)
    have hE := (estimateRVCodes_definable (estimatePrefixGraph_definable hc Q) p q mode).preimage_comp idx
    have hP : S.Definable LRV {z : Fin g → M | Proper z} := by
      change S.Definable LRV {z : Fin g → M | ∀ i, NonzeroRV (z i)}
      rw [Set.ofPred_forall]
      exact Set.definable_iInter_of_finite (fun i =>
        (nonzero_rv_definable S).preimage_comp (fun _ : Fin 1 => i))
    have hSort := (sortedUniverse_definable S (estimateWitnessSort k n)).raw_definable
    convert (hP.preimage_comp (Sum.inl : Fin g → Fin g ⊕ Fin (k + n + 2))).inter
      ((hSort.preimage_comp (Sum.inr : Fin (k + n + 2) → Fin g ⊕ Fin (k + n + 2))).inter hE) using 1
    ext z
    have he : z ∘ idx = Sum.elim
        (attachEstimatePrefix (z ∘ Sum.inl) (((z ∘ Sum.inr) ∘ E) ∘ Sum.inl))
        (((z ∘ Sum.inr) ∘ E) ∘ Sum.inr) := by
      funext i
      rcases i with ((i | i) | i) | i <;> rfl
    change (Proper (z ∘ Sum.inl) ∧ (z ∘ Sum.inr) ∈ sortedUniverse _ ∧ _) ↔
      Proper (z ∘ Sum.inl) ∧ (z ∘ Sum.inr) ∈ sortedUniverse _ ∧
        z ∘ idx ∈ estimateRVCodes (estimatePrefixGraph Q) p q mode
    rw [he, mem_estimateRVCodes_attachPrefix _ _ _ _ _ mode]
  proper := fun _ hz => ⟨hz.1, hz.2.1⟩
  invariant := by
    intro t u he z
    have hRow : {w | attachEstimatePrefix (rawTuple t) w ∈ estimatePrefixGraph Q} =
        {w | attachEstimatePrefix (rawTuple u) w ∈ estimatePrefixGraph Q} := by
      ext w
      change (rawTuple t, _) ∈ Q.carrier ↔ (rawTuple u, _) ∈ Q.carrier
      exact Q.invariant t u he _
    change Proper (rawTuple t) ∧ z ∈ sortedUniverse _ ∧ _ ↔
      Proper (rawTuple u) ∧ z ∈ sortedUniverse _ ∧ _
    rw [hRow]
    exact and_congr (iff_of_true (rawTuple_proper t) (rawTuple_proper u)) Iff.rfl

theorem estimateRVCodes_gamma_base_definable (hc : CanonicalStructure.IsCanonical (M := M))
    {B : Base (M := M)} {G : Set (Fin k ⊕ (Fin n ⊕ Fin m) → M)}
    (hG : DefinableOverBase B (fun _ : Fin (k + (n + m)) => .vf)
      {z | z ∘ vfFamilyIndexEquiv k n m ∈ G}) (p q : ℕ)
    (mode : PowerComparison := .lowerBound) :
    DefinableOverBase B (estimateWitnessSort k n)
      {z | z ∈ sortedUniverse (estimateWitnessSort k n) ∧
        z ∘ estimateWitnessIndexEquiv k n ∈ estimateRVCodes G p q mode} := by
  obtain ⟨g, γ, hγ, Q, hQ⟩ := hG
  refine ⟨g, γ, hγ, estimateWitnessRelation hc Q p q mode, ?_⟩
  let e := vfFamilyIndexEquiv k n m
  have he : {w | attachEstimatePrefix (rawTuple (representatives γ)) w ∈ estimatePrefixGraph Q} = G := by
    ext w
    have hw : Sum.elim (w ∘ Sum.inl) (w ∘ Sum.inr) = w := by funext i; cases i <;> rfl
    change (Sum.elim (w ∘ Sum.inl) (w ∘ Sum.inr) ∘ e.symm) ∈ Q.fibre γ ↔ w ∈ G
    rw [hw, hQ]
    change (w ∘ e.symm) ∘ e ∈ G ↔ w ∈ G
    rw [show (w ∘ e.symm) ∘ e = w from funext (fun i => congrArg w (e.symm_apply_apply i))]
  ext z
  change Proper (rawTuple (representatives γ)) ∧ z ∈ sortedUniverse _ ∧ _ ↔ _
  rw [he]
  exact and_iff_right (rawTuple_proper _)

def powerEstimatePointBase (B : Base (M := M))
    (t : Fin k → VFType (M := M)) (a : Fin n → VFType (M := M)) : Base (M := M) :=
  ⟨(B.real ∪ Set.range (vfValues t)) ∪ Set.range (vfValues a), B.gamma⟩

theorem powerWitness_slice_gamma_base
    (hc : CanonicalStructure.IsCanonical (M := M)) {B : Base (M := M)}
    (hn : 0 < n) (hm : 0 < m)
    (f : (Fin k → VFType (M := M)) → (Fin n → VFType (M := M)) → Fin m → VFType (M := M))
    (hG : DefinableOverBase B (fun _ : Fin (k + (n + m)) => .vf)
      {z | z ∘ vfFamilyIndexEquiv k n m ∈ vfFamilyGraph f})
    (t : Fin k → VFType (M := M)) (a : Fin n → VFType (M := M)) (p q : ℕ)
    (mode : PowerComparison) :
    ∃ P : Set (Fin 2 → M), DefinableOverBase (powerEstimatePointBase B t a) (fun _ => .rv) P ∧
      (∀ w ∈ P, Proper w) ∧ ∀ w : Fin 2 → M, Proper w →
        (w ∈ P ↔ mode.onBall (f t) a p q (codeValue (w 0)) (codeValue (w 1))) := by
  let T := powerEstimatePointBase B t a
  have hBT : B.real ⊆ T.real := Set.subset_union_left.trans Set.subset_union_left
  let E := estimateWitnessIndexEquiv k n
  let e (w : Fin 2 → M) := Sum.elim (Sum.elim (vfValues t) (vfValues a)) w ∘ E.symm
  have he : @Set.DefinableMap M LRV (CanonicalStructure.normalize (M := M))
      (Fin 2) (Fin (k + n + 2)) T.real e := by
    rw [normalize_eq_of_isCanonical hc]
    intro i
    rcases hi : E.symm i with (j | j) | j
    · change T.real.DefinableFun LRV (fun w : Fin 2 → M =>
        Sum.elim (Sum.elim (vfValues t) (vfValues a)) w (E.symm i))
      rw [hi]
      exact LRV.definableFun_const _ (Or.inl (Or.inr (Set.mem_range_self j)))
    · change T.real.DefinableFun LRV (fun w : Fin 2 → M =>
        Sum.elim (Sum.elim (vfValues t) (vfValues a)) w (E.symm i))
      rw [hi]
      exact LRV.definableFun_const _ (Or.inr (Set.mem_range_self j))
    · change T.real.DefinableFun LRV (fun w : Fin 2 → M =>
        Sum.elim (Sum.elim (vfValues t) (vfValues a)) w (E.symm i))
      rw [hi]
      exact Set.DefinableFun.proj LRV
  have hmap (w : Fin 2 → M) :
      e w ∘ E = Sum.elim (Sum.elim (vfValues t) (vfValues a)) w :=
    funext (fun i => congrArg (Sum.elim (Sum.elim (vfValues t) (vfValues a)) w) (E.symm_apply_apply i))
  have hsort (w : Fin 2 → M) (hw : Proper w) : e w ∈ sortedUniverse (estimateWitnessSort k n) := by
    intro i
    obtain ⟨j, rfl⟩ := E.surjective i
    have he' : e w (E j) = Sum.elim (Sum.elim (vfValues t) (vfValues a)) w j := congrFun (hmap w) j
    rw [he']
    rcases j with (j | j) | j
    · simpa [estimateWitnessSort, E, estimateWitnessIndexEquiv, sortEval, vfValues, iVF] using (t j).property
    · simpa [estimateWitnessSort, E, estimateWitnessIndexEquiv, sortEval, vfValues, iVF] using (a j).property
    · simpa [estimateWitnessSort, E, estimateWitnessIndexEquiv, sortEval, iRV] using (hw j).1
  let P : Set (Fin 2 → M) := {w | (e w ∈ sortedUniverse (estimateWitnessSort k n) ∧
    e w ∘ E ∈ estimateRVCodes (vfFamilyGraph f) p q mode) ∧ w ∈ sortedUniverse (fun _ => .rv)}
  have hP : DefinableOverBase T (fun _ => .rv) P :=
    ((estimateRVCodes_gamma_base_definable hc hG p q mode).mono hBT (Set.Subset.refl _)).preimage_real_map _ _ he
  have hProper (w : Fin 2 → M) (hw : w ∈ P) : Proper w := by
    have h := hw.1.2
    rw [hmap] at h
    exact estimateRVCodes_rv_proper h
  refine ⟨P, hP, hProper, ?_⟩
  intro w hw
  let d : Fin 2 → CanonicalRV.RVSort M := fun i => ⟨w i, (hw i).1⟩
  have hγ (i : Fin 2) : Values.gammaOf (d i) (hw i).2 = codeValue (w i) := by
    have hp : NonzeroRV (w i) := hw i
    rw [codeValue, dif_pos hp]
    rfl
  have hm' := mem_estimateRVCodes_iff hn hm f t a d (fun i => (hw i).2) p q mode
  rw [hγ 0, hγ 1] at hm'
  change w ∈ P ↔ _
  rw [← hm']
  constructor
  · intro h
    rw [← hmap]
    exact h.1.2
  · intro h
    exact ⟨⟨hsort w hw, (hmap w).symm ▸ h⟩, fun i => (hw i).1⟩

theorem named_powerEstimate_gamma_base (h00 : M ⊨ Axioms.ACVF00)
    (hc : CanonicalStructure.IsCanonical (M := M)) {B : Base (M := M)}
    (δ : Values.Gamma (M := M)) (hδ : GammaDefinableClosureAtBase B δ) (hδ₁ : 1 < δ)
    (hn : 0 < n) (hm : 0 < m)
    (f : (Fin k → VFType (M := M)) → (Fin n → VFType (M := M)) → (Fin m → VFType (M := M)))
    (hG : DefinableOverBase B (fun _ : Fin (k + (n + m)) => .vf)
      {z | z ∘ vfFamilyIndexEquiv k n m ∈ vfFamilyGraph f})
    (t : Fin k → VFType (M := M)) (a : Fin n → VFType (M := M)) (p q : ℕ)
    (hne : ∃ c r, vfPositivePowerEstimate (f t) a p q c r) :
    ∃ c r, GammaDefinableClosureAtBase (powerEstimatePointBase B t a) c ∧
      GammaDefinableClosureAtBase (powerEstimatePointBase B t a) r ∧
      vfPositivePowerEstimate (f t) a p q c r := by
  obtain ⟨P, hP, hp, hsem⟩ := powerWitness_slice_gamma_base hc hn hm f hG t a p q .lowerBound
  have hBT : B.real ⊆ (powerEstimatePointBase B t a).real := Set.subset_union_left.trans Set.subset_union_left
  exact vfPowerEstimate_gamma_base_named_pair h00 _ δ (hδ.mono hBT (Set.Subset.refl _)) hδ₁
    (f t) a p q P hP hp hsem hne

end SpecialTransformations.Section8

end

section

/-! Lemma 8.6 over the original real and Gamma parameters. The full
witness relation is projected to obtain a common good locus. The
finite real specialization is used only to compute the VF dimension. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace SpecialTransformations.Section8

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {k n m : ℕ}

noncomputable def canonicalGammaSpace (hc : CanonicalStructure.IsCanonical (M := M)) : Space LRV M :=
  (normalize_eq_of_isCanonical hc) ▸ (@gammaSpace M sM hM)

private theorem transported_rvCoded {s t : LRV.Structure M} (h : s = t)
    (D : @Space LRV M s) (hd : @Space.RVCoded M s D) : @Space.RVCoded M t (h ▸ D) := by
  subst t
  exact hd

private theorem canonicalGammaSpace_rvCoded (hc : CanonicalStructure.IsCanonical (M := M)) :
    (canonicalGammaSpace hc).RVCoded :=
  transported_rvCoded (normalize_eq_of_isCanonical hc) _ (@gammaSpace_rvCoded M sM hM)

private def powerWitnessRows (G : Set (Fin k ⊕ (Fin n ⊕ Fin m) → M)) (q : ℕ) :
    Set (Fin (k + n + 2) → M) :=
  {z | z ∈ sortedUniverse (estimateWitnessSort k n) ∧
    z ∘ estimateWitnessIndexEquiv k n ∈ estimateRVCodes G 1 q}

private def powerWitnessCentreIndex (k n : ℕ) : Fin (k + n) → Fin (k + n + 2) :=
  fun i => (finSumFinEquiv : Fin (k + n) ⊕ Fin 2 ≃ Fin (k + n + 2)) (.inl i)

/-- List the VF parameter coordinates followed by the source coordinates. -/
def flattenFamilyCentre (t : Fin k → M) (a : Fin n → M) : Fin (k + n) → M :=
  Sum.elim t a ∘ (finSumFinEquiv : Fin k ⊕ Fin n ≃ Fin (k + n)).symm

private def powerEstimateGoodGamma (G : Set (Fin k ⊕ (Fin n ⊕ Fin m) → M)) (q : ℕ) :
    Set (Fin (k + n) → M) :=
  (fun z => z ∘ powerWitnessCentreIndex k n) '' powerWitnessRows G q

private theorem powerWitnessCentre_sort (k n : ℕ) :
    estimateWitnessSort k n ∘ powerWitnessCentreIndex k n = fun _ => .vf := by
  funext i
  simp [estimateWitnessSort, powerWitnessCentreIndex]

private theorem mem_powerEstimateGoodGamma_iff (hn : 0 < n) (hm : 0 < m)
    (f : (Fin k → VFType (M := M)) → (Fin n → VFType (M := M)) → Fin m → VFType (M := M))
    (t : Fin k → VFType (M := M)) (a : Fin n → VFType (M := M)) (q : ℕ) :
    flattenFamilyCentre (vfValues t) (vfValues a) ∈ powerEstimateGoodGamma (vfFamilyGraph f) q ↔
      ∃ c r, vfPositivePowerEstimate (f t) a 1 q c r := by
  let E := estimateWitnessIndexEquiv k n
  let b := flattenFamilyCentre (vfValues t) (vfValues a)
  have hE (j : Fin k ⊕ Fin n) :
      E (.inl j) = powerWitnessCentreIndex k n ((finSumFinEquiv : Fin k ⊕ Fin n ≃ Fin (k + n)) j) := rfl
  constructor
  · rintro ⟨z, hz, he⟩
    let w := (z ∘ E) ∘ Sum.inr
    have hz' : z ∘ E = Sum.elim (Sum.elim (vfValues t) (vfValues a)) w := by
      funext i
      rcases i with i | i
      · change z (E (.inl i)) = Sum.elim (vfValues t) (vfValues a) i
        rw [hE]
        simpa only [Function.comp_apply, flattenFamilyCentre, Equiv.symm_apply_apply] using
          congrFun he ((finSumFinEquiv : Fin k ⊕ Fin n ≃ Fin (k + n)) i)
      · rfl
    have hproper : Proper w := estimateRVCodes_rv_proper hz.2
    let d : Fin 2 → CanonicalRV.RVSort M := fun i => ⟨w i, (hproper i).1⟩
    have hd (i : Fin 2) : (d i).val ≠ iRVZero := (hproper i).2
    have h := hz.2
    rw [hz'] at h
    exact ⟨Values.gammaOf (d 0) (hd 0), Values.gammaOf (d 1) (hd 1),
      (mem_estimateRVCodes_iff hn hm f t a d hd 1 q).mp h⟩
  · rintro ⟨c, r, h⟩
    let γ : Fin 2 → Values.Gamma (M := M) := ![c, r]
    let d : Fin 2 → CanonicalRV.RVSort M := fun i => (representatives γ i).val
    have hd (i : Fin 2) : (d i).val ≠ iRVZero := (representatives γ i).property
    have hγ (i : Fin 2) : Values.gammaOf (d i) (hd i) = γ i := congrFun (representatives_values γ) i
    let z := Sum.elim (Sum.elim (vfValues t) (vfValues a)) (rvValues d) ∘ E.symm
    have hz : z ∘ E = Sum.elim (Sum.elim (vfValues t) (vfValues a)) (rvValues d) :=
      funext (fun i => congrArg _ (E.symm_apply_apply i))
    refine ⟨z, ⟨?_, ?_⟩, ?_⟩
    · intro i
      obtain ⟨j, rfl⟩ := E.surjective i
      change sortEval (estimateWitnessSort k n (E j)) ((z ∘ E) j)
      rw [hz]
      rcases j with (j | j) | j
      · simpa [estimateWitnessSort, E, estimateWitnessIndexEquiv, sortEval, vfValues, iVF] using (t j).property
      · simpa [estimateWitnessSort, E, estimateWitnessIndexEquiv, sortEval, vfValues, iVF] using (a j).property
      · simpa [estimateWitnessSort, E, estimateWitnessIndexEquiv, sortEval, rvValues, iRV] using (d j).property
    · rw [hz]
      apply (mem_estimateRVCodes_iff hn hm f t a d hd 1 q).mpr
      rwa [hγ 0, hγ 1]
    · funext i
      obtain ⟨j, rfl⟩ := (finSumFinEquiv : Fin k ⊕ Fin n ≃ Fin (k + n)).surjective i
      change z (powerWitnessCentreIndex k n ((finSumFinEquiv : Fin k ⊕ Fin n ≃ Fin (k + n)) j)) = b _
      rw [← hE]
      exact (congrFun hz (.inl j)).trans (by simp [b, flattenFamilyCentre])

theorem lemma_8_6_gamma_base (h00 : M ⊨ Axioms.ACVF00)
    (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    {B : Base (M := M)} (hsmall : Cardinal.mk ↥B.real < κ)
    (δ : Values.Gamma (M := M)) (hδ : GammaDefinableClosureAtBase B δ) (hδ₁ : 1 < δ) (hn : 0 < n)
    (f : (Fin k → VFType (M := M)) → (Fin n → VFType (M := M)) → Fin m → VFType (M := M))
    (hf : DefinableOverBase B (fun _ : Fin (k + (n + m)) => .vf)
      {z | z ∘ vfFamilyIndexEquiv k n m ∈ vfFamilyGraph f}) :
    ∃ Q : ℕ, 0 < Q ∧ ∃ U : Set (Fin (k + n) → M), DefinableOverBase B (fun _ => .vf) U ∧
      ∃ g, ∃ d : Fin g → Code (M := M),
        ∀ t : Fin k → VFType (M := M),
          (∃ hE : ((B.real ∪ Set.range (rawTuple d)) ∪ Set.range (vfValues t)).Definable LRV
            {a | a ∈ vfRawUniverse n ∧ flattenFamilyCentre (vfValues t) a ∉ U},
            vfDim (canonicalGammaSpace hc) (vfObjectOfRaw hE) < n) ∧
          ∀ a : Fin n → VFType (M := M), flattenFamilyCentre (vfValues t) (vfValues a) ∈ U →
            ∃ c r, GammaDefinableClosureAtBase (powerEstimatePointBase B t a) c ∧
              GammaDefinableClosureAtBase (powerEstimatePointBase B t a) r ∧
              vfPositivePowerEstimate (f t) a 1 Q c r := by
  obtain ⟨g, d, hd⟩ := DefinableOverBase.specialize hf
  let S := B.real ∪ Set.range (rawTuple d)
  let e := vfFamilyIndexEquiv k n m
  have hsmallS : Cardinal.mk S < κ := small_union_range hκ B.real hsmall _
  have hGraph : S.Definable LRV (vfFamilyGraph f) := by
    convert hd.raw_definable.preimage_comp e.symm using 1
    ext z
    change z ∈ vfFamilyGraph f ↔ (z ∘ e.symm) ∘ e ∈ vfFamilyGraph f
    rw [show (z ∘ e.symm) ∘ e = z from funext (fun i => congrArg z (e.symm_apply_apply i))]
  by_cases hm : 0 < m
  · obtain ⟨Q, hQ, hgeneric⟩ := uniform_power_estimate_of_independent hc hκ hs hsmallS hn f hGraph
    let U := powerEstimateGoodGamma (vfFamilyGraph f) Q
    have hUG := (estimateRVCodes_gamma_base_definable hc hf 1 Q).image_real (powerWitnessCentreIndex k n)
    rw [powerWitnessCentre_sort] at hUG
    have hU : S.Definable LRV U := by
      have hSort := (sortedUniverse_definable S (estimateWitnessSort k n)).raw_definable
      exact (hSort.inter ((estimateRVCodes_definable hGraph 1 Q).preimage_comp
        (estimateWitnessIndexEquiv k n))).image_comp (powerWitnessCentreIndex k n)
    refine ⟨Q, hQ, U, hUG, g, d, fun t => ?_⟩
    let T := S ∪ Set.range (vfValues t)
    have hflat : T.DefinableMap LRV (flattenFamilyCentre (n := n) (vfValues t)) := by
      intro i
      obtain ⟨j, rfl⟩ := (finSumFinEquiv : Fin k ⊕ Fin n ≃ Fin (k + n)).surjective i
      unfold flattenFamilyCentre
      simp only [Function.comp_apply, Equiv.symm_apply_apply]
      cases j with
      | inl j => exact LRV.definableFun_const _ (Or.inr (Set.mem_range_self j))
      | inr j => exact Set.DefinableFun.proj LRV
    have hE := (vfRawUniverse_definable T n).inter ((hU.mono Set.subset_union_left).preimage_map hflat).compl
    constructor
    · refine ⟨hE, ?_⟩
      apply vfDim_lt_of_no_independent hc hs (small_union_range hκ S hsmallS _) _
        (canonicalGammaSpace_rvCoded hc) hn
      intro a ha hind
      exact ha.2 ((mem_powerEstimateGoodGamma_iff hn hm f t a Q).mpr (hgeneric t a hind))
    · intro a ha
      exact named_powerEstimate_gamma_base h00 hc δ hδ hδ₁ hn hm f hf t a 1 Q
        ((mem_powerEstimateGoodGamma_iff hn hm f t a Q).mp ha)
  · have hm₀ : m = 0 := Nat.eq_zero_of_not_pos hm
    subst m
    let U := sortedUniverse (M := M) (fun _ : Fin (k + n) => .vf)
    have hU : DefinableOverBase B (fun _ => .vf) U :=
      real_definableOverBase B _ _ (sortedUniverse_definable B.real _)
    refine ⟨1, one_pos, U, hU, g, d, fun t => ⟨?_, ?_⟩⟩
    · have he : {a | a ∈ vfRawUniverse n ∧ flattenFamilyCentre (vfValues t) a ∉ U} = ∅ := by
        ext a
        constructor
        · rintro ⟨ha, hn⟩
          apply hn
          intro i
          let e : Fin k ⊕ Fin n ≃ Fin (k + n) := finSumFinEquiv
          change iVF (Sum.elim (vfValues t) a (e.symm i))
          cases hi : e.symm i with
          | inl j => exact (t j).property
          | inr j => exact ha j
        · simp
      have hE : (S ∪ Set.range (vfValues t)).Definable LRV
          {a | a ∈ vfRawUniverse n ∧ flattenFamilyCentre (vfValues t) a ∉ U} := he.symm ▸ Set.definable_empty
      refine ⟨hE, ?_⟩
      apply vfDim_lt_of_no_independent hc hs (small_union_range hκ S hsmallS _) _
        (canonicalGammaSpace_rvCoded hc) hn
      intro a ha
      rw [he] at ha
      exact ha.elim
    · intro a _
      let T := powerEstimatePointBase B t a
      have hOne : GammaDefinableClosureAtBase T 1 :=
        real_definableAtBase T .rv _ (GammaSyntax.one_definable T.real)
      refine ⟨1, 1, hOne, hOne, fun x _ => ?_⟩
      have he : f t x = f t a := funext (fun i => i.elim0)
      simp only [he, sub_self, vfTupleValue_zero, pow_one, ← Values.infinity_eq_zero (M := M)]
      exact Values.le_infinity (M := M) _

end SpecialTransformations.Section8

end
