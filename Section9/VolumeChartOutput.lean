import Section9.VolumeChartCertificates
import Section9.RVScaleRatio
import Section9.ResidueChartJacobian

/-! The residue determinant, corrected by the ratio of scales, is a
same-base definable graph for each supported chart. -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open FirstOrder FirstOrder.Language MvPolynomial
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section4.ResiduePurity
open SpecialTransformations.Section7 SpecialTransformations.DefinableGeometry

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ} {S : Set M}
local notation "RV" => CanonicalRV.RVSort M
local notation "k" => ModelResidue M
local notation "I" => Fin (n+n)
local notation "O" => Fin 1

private abbrev Witness (σ : VolumeChartSupport n) := (I ⊕ σ.Index) ⊕ (I ⊕ Unit)

private def rawChartWitnesses (σ : VolumeChartSupport n)
    (C : DefSet (rawRVSpace (M := M) (n+n)) S) (T : LRV.Term (I ⊕ Unit)) :
    Set ((I ⊕ O) ⊕ Witness σ → M) :=
  {w |
      let v := w ∘ Sum.inr
      let a := v ∘ Sum.inl ∘ Sum.inl
      let c := v ∘ Sum.inl ∘ Sum.inr
      let z := v ∘ Sum.inr ∘ Sum.inl
      let d := v ∘ Sum.inr ∘ Sum.inr
      (∀ i, NonzeroRV (a i)) ∧
      (v ∘ Sum.inl ∈ rawVolumeChart σ C) ∧
      (Sum.elim a z ∈ rawVolumeNormalized C) ∧
      (Sum.elim (Sum.elim c z) d ∈ rawVolumeChartEvaluation (M := M) σ) ∧
      (∀ i, w (.inl (.inl i)) = iRVMul (a i) (z i)) ∧
      w (.inl (.inr 0)) = T.realize (Sum.elim a d)}

private theorem raw_chart_codes_definable
    (hc : CanonicalStructure.IsCanonical (M := M)) (σ : VolumeChartSupport n)
    (C : DefSet (rawRVSpace (M := M) (n+n)) S) (T : LRV.Term (I ⊕ Unit)) :
    S.Definable LRV (rawChartWitnesses σ C T) := by
  let J := (I ⊕ O) ⊕ Witness σ
  let a : I → J := Sum.inr ∘ Sum.inl ∘ Sum.inl
  let c : σ.Index → J := Sum.inr ∘ Sum.inl ∘ Sum.inr
  let z : I → J := Sum.inr ∘ Sum.inr ∘ Sum.inl
  let d : Unit → J := Sum.inr ∘ Sum.inr ∘ Sum.inr
  let t : I → J := Sum.inl ∘ Sum.inl
  let o : J := .inl (.inr 0)
  have h₁ (i : I) : S.Definable LRV {w : J → M | NonzeroRV (w (a i))} :=
    (nonzero_rv_definable S).preimage_comp (fun _ : O => a i)
  have h₂ := (rawVolumeChart_definable σ hc C).preimage_comp (Sum.inr ∘ Sum.inl : I ⊕ σ.Index → J)
  have h₃ := (rawVolumeNormalized_definable hc C).preimage_comp (Sum.elim a z)
  have h₄ := (rawVolumeChartEvaluation_definable (S := S) σ hc).preimage_comp (Sum.elim (Sum.elim c z) d)
  have h₅ (i : I) : S.Definable LRV {w : J → M | w (t i) = iRVMul (w (a i)) (w (z i))} := by
    have hd := (Set.DefinableFun.of_empty (A := S)
      (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.rvMul)).comp
      (show S.DefinableMap LRV (fun w : J → M => ![w (a i), w (z i)]) from
        fun j => by fin_cases j <;> exact Set.DefinableFun.proj LRV)
    exact (Set.DefinableFun.proj (L := LRV) (A := S) (i := t i)).ofPred_eq hd
  have h₆ : S.Definable LRV {w : J → M | w o = T.realize (Sum.elim (w ∘ a) (w ∘ d))} := by
    have h := (Set.DefinableFun.of_empty (A := S) (T.definableFun_realize (M := M))).comp
      (show S.DefinableMap LRV (fun w : J → M => w ∘ Sum.elim a d) from fun i => Set.DefinableFun.proj LRV)
    have he (w : J → M) : w ∘ Sum.elim a d = Sum.elim (w ∘ a) (w ∘ d) := by
      funext i
      cases i <;> rfl
    simpa only [he] using (Set.DefinableFun.proj (L := LRV) (A := S) (i := o)).ofPred_eq h
  have h := (Set.definable_iInter_of_finite h₁).inter
    (h₂.inter (h₃.inter (h₄.inter ((Set.definable_iInter_of_finite h₅).inter h₆))))
  convert h using 1
  ext w
  have h₃' : w ∘ Sum.elim a z = Sum.elim (w ∘ a) (w ∘ z) := by
    funext i
    cases i <;> rfl
  have h₄' : w ∘ Sum.elim (Sum.elim c z) d = Sum.elim (Sum.elim (w ∘ c) (w ∘ z)) (w ∘ d) := by
    funext i
    rcases i with (i | i) | i <;> rfl
  simp only [rawChartWitnesses, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq, Set.mem_preimage, h₃', h₄']
  rfl

def VolumeChartValue (σ : VolumeChartSupport n) (C : Set (I → RV)) (t : I → RV) (ω : O → RV) : Prop :=
  ∃ (a b : Fin n → RV) (c : σ.Index → k) (z : I → k),
    (∀ i, a i ≠ 0) ∧ (∀ i, b i ≠ 0) ∧ IsVolumeChart σ C a b c ∧ z ∈ normalizedCorrespondence C a b ∧
    (chartInputCut σ.inputCut c).eval (z ∘ productLeft n n) ≠ 0 ∧
    t = residueScale (productTuple a b) z ∧
    ω 0 = ((∏ i, b i) / ∏ i, a i) * residueRV (volumeChartDeterminant σ (Sum.elim c z))

theorem VolumeChartValue.isRVJacobianAt [IsAlgClosed k] {σ : VolumeChartSupport n}
    {C : Set (I → RV)} {t : I → RV} {ω : O → RV} (h : VolumeChartValue σ C t ω) :
    IsRVJacobianAt C (t ∘ productLeft n n) (t ∘ productRight n n) (ω 0) := by
  obtain ⟨a, b, c, z, ha, hb, hcert, hz, hcut, ht, hω⟩ := h
  obtain ⟨_, hP, hcontains, hcovers⟩ := (isVolumeChart_iff σ C a b c).mp hcert
  let P := chartEquation σ.equations c
  let T := chartExtraOpen σ.extraOpen c
  let x := z ∘ productLeft n n
  let y := z ∘ productRight n n
  have hxy : productTuple x y = z := by
    apply productTuple_ext
    · intro i; exact productTuple_left _ _ _
    · intro i; exact productTuple_right _ _ _
  have he (p : I → k) : (residueOutputJacobian P * T).eval p =
      (Matrix.of fun i j => (pderiv (productRight n n j) (P i)).eval p).det * T.eval p := by
    rw [map_mul, eval_residueOutputJacobian]
  have hQ := (hcovers z hz hcut).1
  have hB := (hcovers z hz hcut).2
  have hj := isRVJacobianAt_of_certified_chart C a b x y ha hb
    (fun i => hz.2 (productLeft n n i)) (fun i => hz.2 (productRight n n i)) P T
    (hxy.symm ▸ hz) (fun i p hp => hP p hp i) (by rwa [hxy, he])
    (fun p hp hQ' => hcontains p hp ((he p) ▸ hQ')) (by rwa [hxy])
  rw [ht, hω]
  have hl : residueScale (productTuple a b) z ∘ productLeft n n = residueScale a x := by
    funext i
    simp only [residueScale, Function.comp_apply, productTuple_left, x]
  have hr : residueScale (productTuple a b) z ∘ productRight n n = residueScale b y := by
    funext i
    simp only [residueScale, Function.comp_apply, productTuple_right, y]
  rw [hl, hr, volumeChartDeterminant, chartDerivativeBlock_eq, chartDerivativeBlock_eq]
  simpa only [hxy] using hj

theorem volumeChartValue_relationDefinable (hc : CanonicalStructure.IsCanonical (M := M))
    (σ : VolumeChartSupport n) (C : DefSet (rawRVSpace (M := M) (n+n)) S) :
    (rawRVSpace (M := M) (n+n)).RelationDefinable (rawRVSpace (M := M) 1) S
      (VolumeChartValue σ C.carrier) := by
  let P := rawRVSpace (M := M) (n+n)
  let Q := rawRVSpace (M := M) 1
  obtain ⟨T, hT⟩ := exists_rv_scale_ratio_term (M := M) (n := n)
  have hA := raw_chart_codes_definable hc σ C T
  have hD := (P.domain_definable.mono (Set.empty_subset S)).preimage_comp (Sum.inl : I → I ⊕ O)
  have hE := (Q.domain_definable.mono (Set.empty_subset S)).preimage_comp (Sum.inr : O → I ⊕ O)
  have h : S.Definable LRV {w : I ⊕ O → M |
      w ∘ Sum.inl ∈ P.domain ∧ w ∘ Sum.inr ∈ Q.domain ∧
        ∃ v : Witness σ → M, Sum.elim w v ∈ rawChartWitnesses σ C T} :=
    hD.inter (hE.inter hA.exists_of_finite)
  change S.Definable LRV (P.relation Q (VolumeChartValue σ C.carrier))
  suffices he : P.relation Q (VolumeChartValue σ C.carrier) = {w : I ⊕ O → M |
      w ∘ Sum.inl ∈ P.domain ∧ w ∘ Sum.inr ∈ Q.domain ∧
        ∃ v : Witness σ → M, Sum.elim w v ∈ rawChartWitnesses σ C T} by
    rw [he]
    exact h
  ext w
  constructor
  · rintro ⟨ht, hω, a, b, c, z, ha, hb, hChart, hz, hcut, hval, hJ⟩
    let u := rvValues (productTuple a b)
    let d := volumeChartDeterminant σ (Sum.elim c z)
    let v : Witness σ → M := Sum.elim (Sum.elim u (residueRaw ∘ c))
      (Sum.elim (residueRaw ∘ z) (fun _ => residueRaw d))
    refine ⟨ht, hω, v, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      obtain ⟨j | j, rfl⟩ := finSumFinEquiv.surjective i
      · change NonzeroRV (productTuple a b (productLeft n n j)).val
        rw [productTuple_left]
        exact ⟨(a j).property, fun h₀ => ha j (Subtype.ext (h₀.trans RVOperations.zero_val.symm))⟩
      · change NonzeroRV (productTuple a b (productRight n n j)).val
        rw [productTuple_right]
        exact ⟨(b j).property, fun h₀ => hb j (Subtype.ext (h₀.trans RVOperations.zero_val.symm))⟩
    · exact (mem_rawVolumeChart_iff σ C a b c).mpr hChart
    · exact (mem_rawVolumeNormalized C a b z).mpr hz
    · change Sum.elim (Sum.elim (residueRaw ∘ c) (residueRaw ∘ z))
        (fun _ => residueRaw d) ∈ rawVolumeChartEvaluation σ
      have he : Sum.elim (residueRaw ∘ c) (residueRaw ∘ z) = residueRaw ∘ Sum.elim c z := by
        funext i
        cases i <;> rfl
      rw [he]
      apply (mem_rawVolumeChartEvaluation_iff σ (Sum.elim c z) d).mpr
      exact ⟨hcut, rfl⟩
    · intro i
      have he := congrArg (fun p : I → RV => (p i).val) hval
      change w (.inl i) = iRVMul (u i) (residueRaw (z i))
      have hdecode : (P.decode ⟨w ∘ Sum.inl, ht⟩ i).val = w (.inl i) :=
        congrFun (rvValues_decode ⟨w ∘ Sum.inl, ht⟩) i
      exact hdecode.symm.trans (he.trans (RVOperations.mul_val _ _))
    · change w (.inr (0 : O)) = T.realize (Sum.elim u (fun _ => residueRaw d))
      have hdecode : (Q.decode ⟨w ∘ Sum.inr, hω⟩ 0).val = w (.inr (0 : O)) :=
        congrFun (rvValues_decode ⟨w ∘ Sum.inr, hω⟩) (0 : O)
      exact hdecode.symm.trans ((congrArg Subtype.val hJ).trans (hT a b (residueRV d)).symm)
  · rintro ⟨ht, hω, v, hne, hcert, hmem, heval, hval, hJ⟩
    let u := v ∘ Sum.inl ∘ Sum.inl
    let q (i : I) : RV := ⟨u i, (hne i).1⟩
    let a := q ∘ productLeft n n
    let b := q ∘ productRight n n
    have hq : productTuple a b = q := by
      apply productTuple_ext
      · intro i; exact productTuple_left _ _ _
      · intro i; exact productTuple_right _ _ _
    have hu : u = rvValues (productTuple a b) := by rw [hq]; rfl
    obtain ⟨p, hp, hcode⟩ := heval
    let c := p ∘ Sum.inl ∘ Sum.inl
    let z := p ∘ Sum.inl ∘ Sum.inr
    let d := p (.inr ())
    have hc' : residueRaw ∘ c = v ∘ Sum.inl ∘ Sum.inr :=
      funext fun i => congrFun hcode (.inl (.inl i))
    have hz' : residueRaw ∘ z = v ∘ Sum.inr ∘ Sum.inl :=
      funext fun i => congrFun hcode (.inl (.inr i))
    have hd' : (fun _ : Unit => residueRaw d) = v ∘ Sum.inr ∘ Sum.inr := by
      funext i
      cases i
      exact congrFun hcode (.inr ())
    have hcert' : Sum.elim u (residueRaw ∘ c) = v ∘ Sum.inl := by
      rw [hc']
      funext i
      cases i <;> rfl
    have hEval : Sum.elim (residueRaw ∘ Sum.elim c z) (fun _ => residueRaw d) ∈
        rawVolumeChartEvaluation (M := M) σ := by
      refine ⟨p, hp, ?_⟩
      funext i
      rcases i with (i | i) | ⟨⟩ <;> rfl
    obtain ⟨hcut, hd⟩ := (mem_rawVolumeChartEvaluation_iff σ (Sum.elim c z) d).mp hEval
    have hq₀ (i : I) : q i ≠ 0 := fun h₀ => (hne i).2 ((congrArg Subtype.val h₀).trans RVOperations.zero_val)
    refine ⟨ht, hω, a, b, c, z, fun i => hq₀ _, fun i => hq₀ _, ?_, ?_, hcut, ?_, ?_⟩
    · apply (mem_rawVolumeChart_iff σ C a b c).mp
      rwa [← hu, hcert']
    · apply (mem_rawVolumeNormalized C a b z).mp
      rwa [← hu, hz']
    · funext i
      apply Subtype.ext
      have hdecode : (P.decode ⟨w ∘ Sum.inl, ht⟩ i).val = w (.inl i) :=
        congrFun (rvValues_decode ⟨w ∘ Sum.inl, ht⟩) i
      have he : w (.inl i) = iRVMul (u i) ((v ∘ Sum.inr ∘ Sum.inl) i) := hval i
      refine hdecode.trans (he.trans ?_)
      rw [← hz', hu]
      exact (RVOperations.mul_val _ _).symm
    · apply Subtype.ext
      have hdecode : (Q.decode ⟨w ∘ Sum.inr, hω⟩ 0).val = w (.inr (0 : O)) :=
        congrFun (rvValues_decode ⟨w ∘ Sum.inr, hω⟩) (0 : O)
      have he : w (.inr (0 : O)) = T.realize (Sum.elim u (v ∘ Sum.inr ∘ Sum.inr)) := hJ
      refine hdecode.trans (he.trans ?_)
      rw [hu, ← hd']
      exact (hT a b (residueRV d)).trans
        (congrArg (fun e : k => ((((∏ i, b i) / ∏ i, a i) * residueRV e) : RV).val) hd.symm)

end SpecialTransformations.Section9
