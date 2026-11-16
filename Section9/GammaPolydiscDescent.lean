module

public import Section9.GammaDescentBaseExtension
public import Section9.AffineMixedDerivative
public import Section9.PolydiscNormalization
public import Section3.SmallFiniteParameters

@[expose] public section

/-! Affine transport of intrinsic Gamma descent back to arbitrary
nonzero RV polydiscs. The scales and the translation are named only in
the auxiliary base for this fibrewise statement. -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7
open SpecialTransformations.DefinableGeometry

namespace SpecialTransformations.Section9

variable {M Γ : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable [LinearOrderedCommGroupWithZero Γ] {n r s : ℕ} {S : Set M}
local notation "VF" => VFType (M := M)
local notation "V" => Fin n → VF

private theorem normalized_projection
    (v : Valuation VF Γ) (a : V) (ha : ∀ i, a i ≠ 0)
    {A : DefSet (rawMixedSpace (M := M) n r) S}
    (hA : ∀ x : V, (∃ p : A, p.val.1 = x) ↔
      x ∈ RVFibre v (fun i => RVCalc.rv v (a i)))
    (hname : ∀ i, ((a i)⁻¹).val ∈ S) (hneg : ∀ _ : Fin n, (-1 : VF).val ∈ S)
    (x : V) :
    (∃ p : (affineMixedMap A (fun i => (a i)⁻¹) (fun _ => -1) hname hneg).image,
      p.val.1 = x) ↔ ∀ i, v (x i) < 1 := by
  let F := affineMixedMap A (fun i => (a i)⁻¹) (fun _ => -1) hname hneg
  have he (p : A) (i : Fin n) :
      (F p).val.1 i = (a i)⁻¹ * p.val.1 i - 1 := by
    rw [affineMixedMap_apply, sub_eq_add_neg]
  have hcancel (z : VF) (i : Fin n) :
      (a i)⁻¹ * (a i * z + a i) - 1 = z := by
    rw [mul_add, ← mul_assoc, inv_mul_cancel₀ (ha i), one_mul, add_sub_cancel_right]
  constructor
  · rintro ⟨⟨p, q, rfl⟩, rfl⟩
    obtain ⟨z, hz, hez⟩ := (normalizePolydisc_bijOn v a ha).surjOn ((hA q.val.1).mp ⟨q, rfl⟩)
    have hEq : (F q).val.1 = z := funext fun i => by
      rw [he, ← congrFun hez i, hcancel]
    rwa [hEq]
  · intro hx
    obtain ⟨p, hp⟩ := (hA (fun i => a i * x i + a i)).mpr
      ((normalizePolydisc_bijOn v a ha).mapsTo hx)
    refine ⟨⟨(F p).val, Set.mem_range_self p⟩, funext fun i => ?_⟩
    change (F p).val.1 i = _
    rw [he, congrFun hp i, hcancel]

theorem gammaDescent_polydiscs_of_reference_input [CharZero VF]
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk S < κ) (v : Valuation VF Γ)
    (hv : ∀ a b : VF, VFValued.predV a b ↔ v a ≤ v b)
    {A : DefSet (rawMixedSpace (M := M) n r) S}
    {B : DefSet (rawMixedSpace (M := M) n s) S}
    (f : Map A B) (hf : Function.Bijective f) (a b : V)
    (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0)
    (hA : ∀ x : V, (∃ p : A, p.val.1 = x) ↔
      x ∈ RVFibre v (fun i => RVCalc.rv v (a i)))
    (hB : ∀ x : V, (∃ p : B, p.val.1 = x) ↔
      x ∈ RVFibre v (fun i => RVCalc.rv v (b i)))
    (aName : ∀ i, ((a i)⁻¹).val ∈ S) (bName : ∀ i, ((b i)⁻¹).val ∈ S)
    (negName : (-1 : VF).val ∈ S) (c : VF) (hc₀ : c ≠ 0)
    (hconst : ∀ p : A, AlgebraicIndependent (vfParameterField S) p.val.1 →
      ∃ J : VF, HasMixedVFJacobianAt f p J ∧ v J = v c)
    (hgraph : HenselizedGaussGraphInput VF) :
    v c = (∏ i, v (b i)) / ∏ i, v (a i) := by
  let u := affineMixedImage A (fun i => (a i)⁻¹) (fun _ => -1) aName (fun _ => negName)
  let w := affineMixedImage B (fun i => (b i)⁻¹) (fun _ => -1) bName (fun _ => negName)
  have hu := affineMixedImage_bijective A _ _ aName (fun _ => negName) (fun i => inv_ne_zero (ha i))
  have hw := affineMixedImage_bijective B _ _ bName (fun _ => negName) (fun i => inv_ne_zero (hb i))
  let u' := u.inverse hu
  let F := w.comp (f.comp u')
  have hu' : Function.Bijective u' := (Equiv.ofBijective u hu).symm.bijective
  have hF : Function.Bijective F := hw.comp (hf.comp hu')
  let G := F.inverse hF
  let c' := ((∏ i, (b i)⁻¹) * c) * ∏ i, a i
  have hc' : c' ≠ 0 := mul_ne_zero
    (mul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun i _ => inv_ne_zero (hb i))) hc₀)
    (Finset.prod_ne_zero_iff.mpr (fun i _ => ha i))
  letI : Valued VF Γ := Valued.mk' v
  have hconstant (p : (affineMixedMap A _ _ aName (fun _ => negName)).image)
      (hp : AlgebraicIndependent (vfParameterField S) p.val.1) :
      ∃ J : VF, HasMixedVFJacobianAt F p J ∧ v J = v c' := by
    have hp' := independent_map_of_finiteFibres hc u' (Map.finiteFibres_of_injective hu'.injective) p hp
    have hfp := independent_map_of_finiteFibres hc f (Map.finiteFibres_of_injective hf.injective) (u' p) hp'
    obtain ⟨L, hL⟩ := mixedDifferentiableAt_of_independent hc hκ.le hs hsmall hv f (u' p) hp'
    obtain ⟨J, hJ, hval⟩ := hconst (u' p) hp'
    have huDer := hasMixedVFDerivativeAt_of_affine_formula hc hκ.le hs hsmall hv u' p hp a a
      (fun q => by
        funext i
        have h := congrFun (congrArg Prod.fst (affineMixedImage_inverse_apply A _ _ aName
          (fun _ => negName) (fun j => inv_ne_zero (ha j)) q)) i
        simpa only [inv_inv, mul_neg, mul_one, neg_neg] using h)
    have hwDer := hasMixedVFDerivativeAt_of_affine_formula hc hκ.le hs hsmall hv w (f (u' p)) hfp
      (fun i => (b i)⁻¹) (fun _ => -1) (fun q => congrArg Prod.fst
        (affineMixedMap_apply B (fun i => (b i)⁻¹) (fun _ => -1) bName (fun _ => negName) q))
    obtain ⟨K, hK⟩ := mixedDifferentiableAt_of_independent hc hκ.le hs hsmall hv (f.comp u') p hp
    obtain ⟨_, hfdet, hfirst⟩ := mixedVFJacobian_comp_of_full_derivative huDer hL
    obtain ⟨hKdet, _, hlast⟩ := mixedVFJacobian_comp_of_full_derivative hK hwDer
    have h₁ := hKdet.unique hfirst
    have h₂ := hfdet.unique hJ
    refine ⟨_, hlast, ?_⟩
    simp only [h₁, h₂, det_vfDiagonalLinear, c', map_mul, hval, mul_assoc]
  have h := normalizedGammaDescent_of_reference_input hc hκ hs h00 hsmall v hv F G
    (Map.inverse_apply F hF) (Map.apply_inverse F hF)
    (normalized_projection v a ha hA aName (fun _ => negName))
    (normalized_projection v b hb hB bName (fun _ => negName)) c' hc' hconstant hgraph
  have hne (a : V) (ha : ∀ i, a i ≠ 0) : (∏ i, v (a i)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => v.ne_zero_iff.mpr (ha i))
  have hbprod : (∏ i, (b i)⁻¹) = (∏ i, b i)⁻¹ := by
    exact Finset.prod_inv_distrib b
  change v (((∏ i, (b i)⁻¹) * c) * ∏ i, a i) = 1 at h
  rw [hbprod, map_mul, map_mul, map_inv₀, map_prod, map_prod] at h
  apply (eq_div_iff (hne a ha)).mpr
  have he : (∏ i, v (b i))⁻¹ * (v c * ∏ i, v (a i)) = 1 := by rwa [← mul_assoc]
  simpa only [mul_one] using (inv_mul_eq_iff_eq_mul₀ (hne b hb)).mp he

theorem gammaDescent_polydiscs_of_vfSmall_exception [CharZero VF]
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk S < κ) (v : Valuation VF Γ)
    (hv : ∀ a b : VF, VFValued.predV a b ↔ v a ≤ v b)
    {A : DefSet (rawMixedSpace (M := M) n r) S}
    {B : DefSet (rawMixedSpace (M := M) n s) S}
    (f : Map A B) (hf : Function.Bijective f) (a b : V)
    (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0)
    (hA : ∀ x : V, (∃ p : A, p.val.1 = x) ↔ x ∈ RVFibre v (fun i => RVCalc.rv v (a i)))
    (hB : ∀ x : V, (∃ p : B, p.val.1 = x) ↔ x ∈ RVFibre v (fun i => RVCalc.rv v (b i)))
    (c : VF) (hc₀ : c ≠ 0) (Z : DefSet (rawMixedSpace (M := M) n r) S)
    (hZ : vfDim (rawRVSpace (M := M) 1) Z < n)
    (hconst : ∀ p : A, p.val ∉ Z.carrier → ∃ J : VF, HasMixedVFJacobianAt f p J ∧ v J = v c)
    (hgraph : HenselizedGaussGraphInput VF) :
    v c = (∏ i, v (b i)) / ∏ i, v (a i) := by
  let a₀ (i : Fin n) := ((a i)⁻¹).val
  let b₀ (i : Fin n) := ((b i)⁻¹).val
  let N := insert (-1 : VF).val (Set.range a₀ ∪ Set.range b₀)
  let T := S ∪ N
  let hST : S ⊆ T := Set.subset_union_left
  have hT : Cardinal.mk T < κ := small_union_finite hκ.le S hsmall N
    (((Set.finite_range a₀).union (Set.finite_range b₀)).insert _)
  have hSF : vfParameterField S ≤ vfParameterField T := Subfield.closure_mono (fun _ h => hST h)
  have hconst' (p : A.extend hST) (hp : AlgebraicIndependent (vfParameterField T) p.val.1) :
      ∃ J : VF, HasMixedVFJacobianAt (f.extend hST) p J ∧ v J = v c := by
    apply hconst p
    intro hz
    let q : Z := ⟨p.val, hz⟩
    have hq : AlgebraicIndependent (vfParameterField S) q.val.1 :=
      algebraicIndependent_of_subfield_le hSF q.val.1 hp
    have h := vfTupleTrdeg_le_vfDim hc (rawRVSpace (M := M) 1) (rawRVSpace_rvCoded 1) Z q
    have hqd : vfTupleTrdeg S q.val.1 = (n : Cardinal) :=
      (tupleField_trdeg_eq_arity_iff (vfParameterField S) q.val.1).mpr hq
    rw [hqd] at h
    exact (not_le_of_gt hZ) (by exact_mod_cast h)
  exact gammaDescent_polydiscs_of_reference_input hc hκ hs h00 hT v hv (f.extend hST) hf a b ha hb hA hB
    (fun i => Or.inr (Set.mem_insert_of_mem _ (Or.inl (Set.mem_range_self i))))
    (fun i => Or.inr (Set.mem_insert_of_mem _ (Or.inr (Set.mem_range_self i))))
    (Or.inr (Set.mem_insert _ _)) c hc₀ hconst' hgraph

end SpecialTransformations.Section9
