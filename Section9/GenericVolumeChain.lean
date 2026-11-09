import Section9.GenericVolumeChainPoint
import Section9.GenericVolumePair
import Section9.VolumeTripleMap
import Section9.FullRVValueFibre
import Section9.ResidueCoefficientBase
import Section4.SmallGeneratedBase
import Section7.ResidueCharacteristic

/-! A full-dimensional subset of the source labels contains a common
generic point for the three volume correspondences. -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open FirstOrder FirstOrder.Language CategoryTheory IsLocalRing
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section4.ResiduePurity SpecialTransformations.Section7
open SpecialTransformations.DefinableGeometry

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}
local notation "RV" => CanonicalRV.RVSort M
local notation "k" => ModelResidue M
local notation "v" => Values.presentationValuation (M := M)

private theorem exists_residue_parameter_sandwich {κ : Cardinal}
    (hκ : Cardinal.aleph0 < κ) (B₀ : LRV.Substructure M) (hB₀ : Cardinal.mk B₀ < κ) :
    ∃ B₁ : LRV.Substructure M, B₀ ≤ B₁ ∧ Cardinal.mk B₁ < κ ∧
      ∃ E : Subfield k, IsAlgClosed E ∧ residueParameterField B₀ ≤ E ∧ E ≤ residueParameterField B₁ := by
  obtain ⟨T, hT₀, hT, hF, hclosed, hres⟩ := exists_residueCoefficient_extension hκ B₀ hB₀
  let F := vfParameterField T
  let E := residueCoefficientField F
  let R := ((v).comap F.subtype).valuationSubring
  have hE : Cardinal.mk E < κ :=
    (Cardinal.mk_congr (residueFieldInclusion v F).rangeRestrictFieldEquiv.symm.toEquiv).le.trans_lt
      ((Cardinal.mk_le_of_surjective (f := residue R) residue_surjective).trans_lt
        ((Cardinal.mk_subtype_le _).trans_lt hF))
  let N := Set.range (fun x : E => residueRaw x.val)
  let B₁ := Substructure.closure LRV (T ∪ N)
  have hB₁ : Cardinal.mk B₁ < κ := small_generated_substructure hκ _
    ((Cardinal.mk_union_le _ _).trans_lt (Cardinal.add_lt_of_lt hκ.le hT (Cardinal.mk_range_le.trans_lt hE)))
  letI : IsAlgClosed F := hclosed
  exact ⟨B₁, fun _ h => Substructure.subset_closure (Or.inl (hT₀ h)), hB₁, E,
    residueCoefficientField_isAlgClosed F, hres,
    fun _ h => Substructure.subset_closure (Or.inr ⟨⟨_, h⟩, rfl⟩)⟩

private theorem normalized_mem_of_scaled_pair (C : Set (Fin (n + n) → RV))
    (a b t s : Fin n → RV) (x y : Fin n → k)
    (hx : residueScale a x = t) (hy : residueScale b y = s)
    (ht : ∀ i, t i ≠ 0) (hs : ∀ i, s i ≠ 0) (hp : productTuple t s ∈ C) :
    productTuple x y ∈ normalizedCorrespondence C a b := by
  refine ⟨?_, fun i hi => ?_⟩
  · have h : residueScale (productTuple a b) (productTuple x y) = productTuple t s := by
      rw [← hx, ← hy]
      apply productTuple_ext
      · intro i; simp only [residueScale, productTuple_left]
      · intro i; simp only [residueScale, productTuple_right]
    exact h.symm ▸ hp
  · obtain ⟨j | j, rfl⟩ := finSumFinEquiv.surjective i
    · change productTuple x y (productLeft n n j) = 0 at hi
      rw [productTuple_left] at hi
      have h := congrFun hx j
      rw [show residueScale a x j = a j * residueRV (x j) from rfl, hi, residueRV_zero, mul_zero] at h
      exact ht j h.symm
    · change productTuple x y (productRight n n j) = 0 at hi
      rw [productTuple_right] at hi
      have h := congrFun hy j
      rw [show residueScale b y j = b j * residueRV (y j) from rfl, hi, residueRV_zero, mul_zero] at h
      exact hs j h.symm

theorem exists_rvJacobian_chain_on_full_label_subset
    (hc : CanonicalStructure.IsCanonical (M := M)) (B : BaseContext M) (hn : 0 < n)
    {U V W : RVObject (M := M) (B.base : Set M) n} (f : U ≅ V) (g : V ≅ W)
    (hU : U.volume.FiniteFibres)
    (hU₀ : ∀ u : U.domain, ∀ i, U.value u i ≠ 0)
    (hV₀ : ∀ w : V.domain, ∀ i, V.value w i ≠ 0)
    (hW₀ : ∀ w : W.domain, ∀ i, W.value w i ≠ 0)
    (D : DefSet (rawRVSpace (M := M) U.arity) (B.base : Set M))
    (hD : D.carrier ⊆ U.domain.carrier) (hd : rvDim D = n) :
    ∃ u : U.domain, u.val ∈ D.carrier ∧ ∃ ω η : RV,
      IsRVJacobianAt (volumeCorrespondence f.hom.map).carrier (U.value u) (V.value (f.hom.map u)) ω ∧
      IsRVJacobianAt (volumeCorrespondence g.hom.map).carrier (V.value (f.hom.map u))
        (W.value (g.hom.map (f.hom.map u))) η ∧
      IsRVJacobianAt (volumeCorrespondence (f.trans g).hom.map).carrier (U.value u)
        (W.value (g.hom.map (f.hom.map u))) (η * ω) := by
  let S := (B.base : Set M)
  let i₁ := productLeft n (n + n)
  let i₂ := productRight n (n + n) ∘ productLeft n n
  let i₃ := productRight n (n + n) ∘ productRight n n
  let T := volumeTripleMap f.hom.map g.hom.map
  let j : Map D U.domain := Map.inclusion hD
  let A := (T.comp j).image
  let hex := rvExchangeInput_of_earlier B.uncountable.le B.saturated B.model00
  have hA : rvDim A = n :=
    (rvDim_mapImage_eq_of_finiteFibres hc hex B.saturated B.small _
      ((volumeTripleMap_finite f.hom.map g.hom.map hU).restrict hD)).trans hd
  have hcoord (u : U.domain) : (∀ i, (T u).val (i₁ i) = U.value u i) ∧
      (∀ i, (T u).val (i₂ i) = V.value (f.hom.map u) i) ∧
      (∀ i, (T u).val (i₃ i) = W.value (g.hom.map (f.hom.map u)) i) := by
    exact ⟨volumeTripleMap_left _ _ u,
      fun i => (volumeTripleMap_right _ _ u _).trans (productTuple_left _ _ i),
      fun i => (volumeTripleMap_right _ _ u _).trans (productTuple_right _ _ i)⟩
  have hA₀ (p) (hp : p ∈ A.carrier) (i : Fin (n + (n + n))) : (p i).val ≠ iRVZero := by
    obtain ⟨d, rfl⟩ := hp
    let u := j d
    have h₀ (j) : (T u).val j ≠ 0 := by
      obtain ⟨l | r, rfl⟩ := finSumFinEquiv.surjective j
      · exact ((hcoord u).1 l).symm ▸ hU₀ u l
      · obtain ⟨l | r, rfl⟩ := finSumFinEquiv.surjective r
        · exact ((hcoord u).2.1 l).symm ▸ hV₀ (f.hom.map u) l
        · exact ((hcoord u).2.2 r).symm ▸ hW₀ (g.hom.map (f.hom.map u)) r
    exact fun h => h₀ i (Subtype.ext (h.trans RVOperations.zero_val.symm))
  obtain ⟨F, s, hF, hFd, hv⟩ := exists_full_nonzero_rvValueFibre hc B A hA₀ (hA.symm ▸ hn)
  let a := s.val ∘ i₁
  let b := s.val ∘ i₂
  let c := s.val ∘ i₃
  have hs₀ i : s.val i ≠ 0 := fun h => hA₀ s.val (hF s.property) i
    ((congrArg Subtype.val h).trans RVOperations.zero_val)
  let N := Set.range (rvValues s.val)
  let B₀ := Substructure.closure LRV (S ∪ N)
  have hSB₀ : S ⊆ (B₀ : Set M) := fun _ h => Substructure.subset_closure (Or.inl h)
  have hB₀ : Cardinal.mk B₀ < B.κ := small_generated_finite_extension B.uncountable B.base B.small N
    (Set.finite_range _)
  have hsB₀ (i) : (s.val i).val ∈ B₀ := Substructure.subset_closure (Or.inr (Set.mem_range_self i))
  obtain ⟨B₁, hB₀₁, hB₁, E, hcl, hE₀, hE₁⟩ := exists_residue_parameter_sandwich B.uncountable B₀ hB₀
  letI : IsAlgClosed E := hcl
  have hF' : F.carrier ⊆ T.image.carrier := by
    intro t ht
    obtain ⟨d, he⟩ := hF ht
    exact ⟨j d, he⟩
  have hπ : (rvHeadSelect i₁ F).FiniteFibres :=
    (volumeTriple_leftProjection_finite f.hom.map g.hom.map hU).restrict hF'
  obtain ⟨p, hp⟩ := exists_generic_projection_on_fixed_value_fibre hc hex B.uncountable.le B.saturated
    B.homogeneous B.small B₁ hB₁ (hSB₀.trans hB₀₁) F i₁ hπ (hFd.trans hA) s
    (fun i => hB₀₁ (hsB₀ i)) hv
  obtain ⟨d, hd'⟩ := hF p.property
  let u := j d
  have hu (i) : (T u).val i = p.val i := congrFun hd' i
  let x := residueNormalize a (U.value u)
  let y := residueNormalize b (V.value (f.hom.map u))
  let z := residueNormalize c (W.value (g.hom.map (f.hom.map u)))
  have hx : residueScale a x = U.value u := residueScale_normalize _ _ fun i =>
    (congrArg Values.vrv ((hcoord u).1 i).symm).trans ((congrArg Values.vrv (hu _)).trans (hv _ p.property _))
  have hy : residueScale b y = V.value (f.hom.map u) := residueScale_normalize _ _ fun i =>
    (congrArg Values.vrv ((hcoord u).2.1 i).symm).trans ((congrArg Values.vrv (hu _)).trans (hv _ p.property _))
  have hz : residueScale c z = W.value (g.hom.map (f.hom.map u)) := residueScale_normalize _ _ fun i =>
    (congrArg Values.vrv ((hcoord u).2.2 i).symm).trans ((congrArg Values.vrv (hu _)).trans (hv _ p.property _))
  have hx₁ : AlgebraicIndependent (residueParameterField B₁) x := by
    have he : p.val ∘ i₁ = U.value u := funext fun i => (hu _).symm.trans ((hcoord u).1 i)
    rw [he] at hp
    exact hp
  letI : Algebra E (residueParameterField B₁) := (Subfield.inclusion hE₁).toAlgebra
  letI : IsScalarTower E (residueParameterField B₁) k := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hInd : AlgebraicIndependent E x := hx₁.restrictScalars (algebraMap E (residueParameterField B₁)).injective
  let J := volumeCorrespondence f.hom.map
  let K := volumeCorrespondence g.hom.map
  let L := volumeCorrespondence (f.trans g).hom.map
  have hab := normalized_mem_of_scaled_pair J.carrier a b _ _ x y hx hy (hU₀ u)
    (hV₀ (f.hom.map u)) ⟨u, rfl⟩
  have hbc := normalized_mem_of_scaled_pair K.carrier b c _ _ y z hy hz (hV₀ (f.hom.map u))
    (hW₀ (g.hom.map (f.hom.map u))) ⟨f.hom.map u, rfl⟩
  have hac := normalized_mem_of_scaled_pair L.carrier a c _ _ x z hx hz (hU₀ u)
    (hW₀ (g.hom.map (f.hom.map u))) ⟨u, rfl⟩
  have ha (i) : a i ≠ 0 := hs₀ _
  have hb (i) : b i ≠ 0 := hs₀ _
  have hc' (i) : c i ≠ 0 := hs₀ _
  have hJ := normalizedCorrespondence_definable_of_base hc B₀ (J.extend hSB₀) a b ha hb
    (fun i => hsB₀ _) (fun i => hsB₀ _)
  have hK := normalizedCorrespondence_definable_of_base hc B₀ (K.extend hSB₀) b c hb hc'
    (fun i => hsB₀ _) (fun i => hsB₀ _)
  have hL := normalizedCorrespondence_definable_of_base hc B₀ (L.extend hSB₀) a c ha hc'
    (fun i => hsB₀ _) (fun i => hsB₀ _)
  letI : IsAlgClosed (VFType (M := M)) := VFAlgClosed.isAlgClosed_vfType
  letI : IsAlgClosed k := ValOneEC.Johnson.isAlgClosed_residueField v
  letI : CharZero k := residueField_charZero_of_model00 v Values.presentation_compatible B.model00
  refine ⟨u, d.property, ?_⟩
  rw [← hx, ← hy, ← hz]
  exact exists_rvJacobian_chain_at_generic_residue B.saturated B₀ hB₀ E hE₀ J.carrier K.carrier L.carrier
    a b c ha hb hc' x y z hInd
    (fun i => (productTuple_left x y i) ▸ hab.2 (productLeft n n i))
    (fun i => (productTuple_right x y i) ▸ hab.2 (productRight n n i))
    (fun i => (productTuple_right y z i) ▸ hbc.2 (productRight n n i))
    hJ hK hL (normalizedVolumeCorrespondence_finite f a b ha hb)
    (normalizedVolumeCorrespondence_finite g b c hb hc') (normalizedVolumeCorrespondence_finite (f.trans g) a c ha hc')
    hab hbc hac

end SpecialTransformations.Section9
