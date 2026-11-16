module

public import Section9.VolumeChartCertificates
public import Section9.VolumeChartExistence
public import Section4.FiniteCover
public import Section7.IntegerAvoidance

@[expose] public section

/-! Saturation selects finitely many support patterns. Both the scales
and all polynomial coefficients remain variables in each pattern. -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open FirstOrder FirstOrder.Language CategoryTheory MvPolynomial
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section4.ResiduePurity
open SpecialTransformations.Section7

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}
local notation "RV" => CanonicalRV.RVSort M
local notation "k" => ModelResidue M

theorem exists_supported_volume_chart
    (hc : CanonicalStructure.IsCanonical (M := M)) (B : BaseContext M)
    {U V : RVObject (M := M) (B.base : Set M) n} (e : U ≅ V)
    (a b : Fin n → RV) (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0) :
    ∃ σ : VolumeChartSupport n, ∃ c : σ.Index → k,
      IsVolumeChart σ (volumeCorrespondence e.hom.map).carrier a b c := by
  let C := (volumeCorrespondence e.hom.map).carrier
  obtain ⟨E, _, _, P, T, D, hD, hP, hcontains, hcovers⟩ := exists_volume_residue_chart hc B e a b ha hb
  let F := residueParameterField E
  let P' (i : Fin n) := (P i).map F.subtype
  let T' := T.map F.subtype
  let D' := D.map F.subtype
  obtain ⟨l, s, cP, hs⟩ := exists_common_polynomial_support P'
  obtain ⟨m, t, cT, ht⟩ := exists_polynomial_support T'
  obtain ⟨r, d, cD, hd⟩ := exists_polynomial_support D'
  let σ : VolumeChartSupport n := ⟨l, m, r, s, t, d⟩
  let c : σ.Index → k := Sum.elim (Sum.elim (fun i => cP i.1 i.2) cT) cD
  have hP' (i : Fin n) : chartEquation σ.equations c i = P' i := hs i
  have hT' : chartExtraOpen σ.extraOpen c = T' := ht
  have hD' : chartInputCut σ.inputCut c = D' := hd
  refine ⟨σ, c, (isVolumeChart_iff σ C a b c).mpr ?_⟩
  dsimp only
  simp only [hP', hT', hD']
  have hEval (z : Fin (n+n) → k) (f : MvPolynomial (Fin (n+n)) F) :
      (f.map F.subtype).eval z = aeval z f := by rw [MvPolynomial.eval_map]; rfl
  have hCut (x : Fin n → k) : D'.eval x = aeval x D := by
    change (D.map F.subtype).eval x = aeval x D
    rw [MvPolynomial.eval_map]
    rfl
  have hBlock (j : Fin n → Fin (n+n)) (z : Fin (n+n) → k) :
      (Matrix.of fun i l => (pderiv (j l) (P' i)).eval z).det =
      aeval z (Matrix.of fun i l => pderiv (j l) (P i)).det := by
    change _ = (aeval z).toRingHom _
    rw [RingHom.map_det]
    congr 1
    apply Matrix.ext
    intro i l
    change (pderiv (j l) ((P i).map F.subtype)).eval z = aeval z (pderiv (j l) (P i))
    rw [pderiv_map, hEval]
  simp only [hBlock, hCut, P', T', hEval]
  letI : CharZero k := residueField_charZero_of_model00 Values.presentationValuation
    Values.presentation_compatible B.model00
  have hD'₀ : D' ≠ 0 := fun h => hD ((map_injective _ F.subtype.injective) (h.trans (map_zero _).symm))
  obtain ⟨x, hx⟩ := exists_integer_eval_ne_zero hD'₀
  let z : Fin (n+n) → k := productTuple (fun i => (x i : k)) (fun _ : Fin n => 0)
  have hz : z ∘ productLeft n n = fun i => (x i : k) := funext (productTuple_left _ _)
  refine ⟨⟨z, ?_⟩, hP, ?_, ?_⟩
  · rw [← hCut, hz]
    exact hx
  · intro p hp hQ
    exact hcontains p hp (by simpa only [map_mul, residueOutputJacobian] using hQ)
  · intro p hp hcut
    obtain ⟨hQ, hR⟩ := hcovers p hp hcut
    exact ⟨by simpa only [map_mul, residueOutputJacobian] using hQ, hR⟩

theorem exists_finite_volume_chart_cover
    (hc : CanonicalStructure.IsCanonical (M := M)) (B : BaseContext M)
    {U V : RVObject (M := M) (B.base : Set M) n} (e : U ≅ V) :
    ∃ A : Finset (VolumeChartSupport n), ∀ a b : Fin n → RV,
      (∀ i, a i ≠ 0) → (∀ i, b i ≠ 0) →
      ∃ σ ∈ A, ∃ c : σ.Index → k, IsVolumeChart σ (volumeCorrespondence e.hom.map).carrier a b c := by
  classical
  let S := (B.base : Set M)
  let C := volumeCorrespondence e.hom.map
  let X : Set (Fin (n+n) → M) := {z | ∀ i, NonzeroRV (z i)}
  have hX : S.Definable LRV X := by
    rw [show X = ⋂ i : Fin (n+n), {z | NonzeroRV (z i)} by ext z; simp [X] ]
    exact Set.definable_iInter_of_finite (fun i => (nonzero_rv_definable S).preimage_comp (fun _ : Fin 1 => i))
  let F (σ : VolumeChartSupport n) := rawVolumeChartScales σ C
  have hcov (z) (hz : z ∈ X) : ∃ Y ∈ Set.range F, z ∈ Y := by
    let q (i : Fin (n+n)) : RV := ⟨z i, (hz i).1⟩
    let a := q ∘ productLeft n n
    let b := q ∘ productRight n n
    have he : productTuple a b = q := by
      apply productTuple_ext
      · intro i
        exact productTuple_left _ _ _
      · intro i
        exact productTuple_right _ _ _
    have hq (i) : q i ≠ 0 := fun h => (hz i).2 ((congrArg Subtype.val h).trans RVOperations.zero_val)
    obtain ⟨σ, c, hc'⟩ := exists_supported_volume_chart hc B e a b (fun i => hq _) (fun i => hq _)
    refine ⟨F σ, Set.mem_range_self σ, ?_⟩
    have h := (mem_rawVolumeChartScales_iff σ C a b).mpr ⟨c, hc'⟩
    rwa [he] at h
  obtain ⟨D, hD, hsub, hDcov⟩ := definable_finite_subcover_index B.saturated S B.small X hX (Set.range F)
    (by rintro _ ⟨σ, rfl⟩; exact rawVolumeChartScales_definable σ hc C) hcov
  choose select hselect using fun Y : D => hsub Y.property
  letI : Fintype D := hD.fintype
  refine ⟨Finset.univ.image select, fun a b ha hb => ?_⟩
  let z := rvValues (productTuple a b)
  have hXz : z ∈ X := by
    intro i
    obtain ⟨j | j, rfl⟩ := finSumFinEquiv.surjective i
    · change NonzeroRV (productTuple a b (productLeft n n j)).val
      rw [productTuple_left]
      exact ⟨(a j).property, fun h => ha j (Subtype.ext (h.trans RVOperations.zero_val.symm))⟩
    · change NonzeroRV (productTuple a b (productRight n n j)).val
      rw [productTuple_right]
      exact ⟨(b j).property, fun h => hb j (Subtype.ext (h.trans RVOperations.zero_val.symm))⟩
  obtain ⟨Y, hY, hz⟩ := hDcov z hXz
  let Y' : D := ⟨Y, hY⟩
  refine ⟨select Y', Finset.mem_image.mpr ⟨Y', Finset.mem_univ _, rfl⟩, ?_⟩
  apply (mem_rawVolumeChartScales_iff (select Y') C a b).mp
  change z ∈ F (select Y')
  rw [hselect Y']
  exact hz

end SpecialTransformations.Section9
