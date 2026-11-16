module

public import Section6.HenselianModel
public import Section3.MeanInBalls

@[expose] public section

/-! A definable RV singleton descends by averaging the finite Galois
orbit of any nonzero representative in the algebraic envelope. -/

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SpecialTransformations.Section6

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

private theorem finite_conjugates (K : Subfield (VFType (M := M)))
    [IsGalois K (VFType (M := M))] (a : VFType (M := M)) :
    (Set.range (fun σ : VFType (M := M) ≃ₐ[K] VFType (M := M) => σ a)).Finite := by
  let p := minpoly K a
  refine (p.rootSet_finite _).subset ?_
  rintro _ ⟨σ, rfl⟩
  have ha : IsIntegral K a := Algebra.IsIntegral.isIntegral a
  change σ a ∈ (minpoly K a).rootSet _
  apply (Polynomial.mem_rootSet_of_ne (minpoly.ne_zero ha)).mpr
  rw [Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]

private theorem mean_fixed_of_conjugates (K : Subfield (VFType (M := M)))
    (a : VFType (M := M)) (A : Finset (VFType (M := M)))
    (hA : ∀ b, b ∈ A ↔ ∃ σ : VFType (M := M) ≃ₐ[K] VFType (M := M), σ a = b)
    (σ : VFType (M := M) ≃ₐ[K] VFType (M := M)) :
    σ (Barycentre.mean A) = Barycentre.mean A := by
  let e := σ.toEquiv.toEmbedding
  have he : A.map e = A := by
    ext b
    simp only [Finset.mem_map, hA]
    constructor
    · rintro ⟨_, ⟨τ, rfl⟩, rfl⟩
      exact ⟨τ.trans σ, rfl⟩
    · rintro ⟨τ, rfl⟩
      exact ⟨σ.symm (τ a), ⟨τ.trans σ.symm, rfl⟩, σ.apply_symm_apply _⟩
  have hsum : ∑ b ∈ A, σ b = ∑ b ∈ A, b := by
    conv_rhs => rw [← he]
    rw [Finset.sum_map]
    rfl
  simp only [Barycentre.mean, map_div₀, map_natCast, map_sum, hsum]

theorem henselian_rv_dcl_of_algebraic_envelope
    {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ a b, VFValued.predV a b ↔ v a ≤ v b)
    (h00 : M ⊨ Axioms.ACVF00)
    (K : Subfield (VFType (M := M))) [IsGalois K (VFType (M := M))]
    (X : Set M) (hK : ∀ a : VFType (M := M), a ∈ K ↔ a.val ∈ X)
    (hRV : ∀ t ∈ X, iRV t → ∃ a : K, iRv a.val.val = t)
    (hrv : ∀ a : VFType (M := M), a.val ∈ X → iRv a.val ∈ X)
    (hH : HenselianLocalRing (v.comap K.subtype).valuationSubring)
    (hEP : HenselianAutomorphismInvariance v K)
    (t : M) (ht : iRV t)
    (hd : @Set.Definable₁ M X LRV (CanonicalStructure.normalize (M := M)) {t}) : t ∈ X := by
  obtain ⟨a, ha⟩ := CanonicalRV.encodedRv_surjective ⟨t, ht⟩
  have hrvA : iRv a.val = t := congrArg Subtype.val ha
  by_cases hzero : a = 0
  · exact hrvA ▸ hrv a ((hK a).mp (hzero ▸ K.zero_mem))
  let hfinite := finite_conjugates K a
  let A := hfinite.toFinset
  have hA (b) : b ∈ A ↔ ∃ σ : VFType (M := M) ≃ₐ[K] VFType (M := M), σ a = b :=
    hfinite.mem_toFinset
  have hne : A.Nonempty := ⟨a, (hA a).mpr ⟨AlgEquiv.refl, rfl⟩⟩
  have hfixed (σ : VFType (M := M) ≃ₐ[K] VFType (M := M)) :
      iRv (σ a).val = iRv a.val := by
    have hp : ∀ x y, VFValued.predV (σ x) (σ y) ↔ VFValued.predV x y :=
      fun x y => (hv _ _).trans ((hEP hH σ x y).trans (hv _ _).symm)
    let e := valuedAutomorphism σ.toRingEquiv hp
    let ee := @FirstOrder.Language.Equiv.toElementaryEmbedding LRV M M
      (CanonicalStructure.normalize (M := M)) (CanonicalStructure.normalize (M := M)) e
    have he := @definable_singleton_fixed LRV M (CanonicalStructure.normalize (M := M))
      X t hd ee (valuedAutomorphism_fixes_base K X hK hRV σ hp)
    calc
      iRv (σ a).val = e (iRv a.val) := (valuedAutomorphism_rv σ.toRingEquiv hp a).symm
      _ = e t := congrArg e hrvA
      _ = t := he
      _ = iRv a.val := hrvA.symm
  have hball (b) (hb : b ∈ A) : v (b - a) < v a := by
    obtain ⟨σ, rfl⟩ := (hA b).mp hb
    have hrv' := (CanonicalRV.same_fibers v hv a (σ a)).mpr
      (Subtype.ext (hfixed σ).symm)
    have hs := (_root_.RVCalc.rv_eq_iff hzero ((map_ne_zero σ).mpr hzero)).mp hrv'
    rwa [← neg_sub (σ a) a, Valuation.map_neg] at hs
  let c := Barycentre.mean A
  have hc : v (c - a) < v a := by
    change v (Barycentre.mean A - a) < v a
    rw [Barycentre.mean_sub_eq h00 A hne a, map_div₀,
      Barycentre.natCast_value_one v hv h00 A.card (Finset.card_ne_zero.mpr hne), div_one]
    exact v.map_sum_lt (v.ne_zero_iff.mpr hzero) hball
  have hcz : c ≠ 0 := by
    intro hz
    exact lt_irrefl _ (by simpa only [hz, zero_sub, Valuation.map_neg] using hc)
  have hrvC : iRv c.val = t := by
    have hca : _root_.RVCalc.rv v a = _root_.RVCalc.rv v c :=
      (_root_.RVCalc.rv_eq_iff hzero hcz).mpr (by rwa [← neg_sub c a, Valuation.map_neg])
    exact (congrArg Subtype.val ((CanonicalRV.same_fibers v hv a c).mp hca)).symm.trans hrvA
  obtain ⟨u, hu⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed c).mpr
    (mean_fixed_of_conjugates K a A hA)
  exact hrvC ▸ hrv c ((hK c).mp (hu ▸ u.property))

theorem lemma_6_2_in_algebraic_envelope_pure
    {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ a b, VFValued.predV a b ↔ v a ≤ v b)
    (h00 : M ⊨ Axioms.ACVF00)
    (K : Subfield (VFType (M := M))) [IsGalois K (VFType (M := M))]
    (X : Set M) (hK : ∀ a : VFType (M := M), a ∈ K ↔ a.val ∈ X)
    (hRV : ∀ t ∈ X, iRV t → ∃ a : K, iRv a.val.val = t)
    (hrv : ∀ a : VFType (M := M), a.val ∈ X → iRv a.val ∈ X)
    (hH : HenselianLocalRing (v.comap K.subtype).valuationSubring)
    (hEP : HenselianAutomorphismInvariance v K) :
    NormalizedFunctionallyClosed X := by
  apply @functionallyClosed_of_dclClosed LRV M (CanonicalStructure.normalize (M := M)) X
  intro b hb
  rcases TypedModelMap.sort_cover b with hvb | hrb
  · exact henselian_vf_dcl v hv K X hK hRV hH hEP ⟨b, hvb⟩ hb
  · exact henselian_rv_dcl_of_algebraic_envelope v hv h00 K X hK hRV hrv hH hEP b hrb hb

end SpecialTransformations.Section6

namespace SpecialTransformations.Section6.Paper

/-- Functional closure in the ambient model, over each original base
contained in the image of the algebraic envelope. -/
theorem lemma_6_2_of_algebraic_envelope
    {N M : Type} [LRV.Structure N] [LRV.Structure M]
    [N ⊨ Axioms.ACVF] [M ⊨ Axioms.ACVF]
    {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (h00 : N ⊨ Axioms.ACVF00)
    (X : LRV.Substructure M) (Y : LRV.Substructure N)
    (j : @ElementaryEmbedding LRV N M
      (CanonicalStructure.normalize (M := N)) (CanonicalStructure.normalize (M := M)))
    (himage : j '' (Y : Set N) = (X : Set M))
    (v : Valuation (VFType (M := N)) Γ)
    (hv : ∀ a b, VFValued.predV a b ↔ v a ≤ v b)
    (K : Subfield (VFType (M := N))) [IsGalois K (VFType (M := N))]
    (hK : ∀ a : VFType (M := N), a ∈ K ↔ a.val ∈ Y)
    (hRV : ∀ t ∈ Y, iRV t → ∃ a : K, iRv a.val.val = t)
    (hH : HenselianLocalRing (v.comap K.subtype).valuationSubring)
    (hEP : HenselianAutomorphismInvariance v K) {S : Set M} (hSX : S ⊆ X) :
    @FunctionallyClosedOver LRV M (CanonicalStructure.normalize (M := M)) S (X : Set M) := by
  have hrv (a : VFType (M := N)) (ha : a.val ∈ Y) : iRv a.val ∈ Y :=
    Y.fun_mem Fn.rvMap ![a.val] (by intro i; fin_cases i; exact ha)
  have hY := lemma_6_2_in_algebraic_envelope_pure v hv h00 K (Y : Set N) hK hRV hrv hH hEP
  have hI := @FunctionallyClosed.image LRV N M
    (CanonicalStructure.normalize (M := N)) (CanonicalStructure.normalize (M := M))
    (Y : Set N) hY j
  exact @FunctionallyClosed.over LRV M (CanonicalStructure.normalize (M := M))
    S (X : Set M) (himage ▸ hI) hSX

end SpecialTransformations.Section6.Paper
