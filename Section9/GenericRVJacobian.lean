import Section9.VolumeChartOutput
import Section9.FiniteVolumeChartCover
import Section9.GenericVolumePair
import Section9.FullRVValueFibre
import Section4.FunctionalRelations
import Section4.RVLabelCompression

/-! The supported chart graphs agree wherever they overlap. Their
definable union covers the volume pairs off an RV-small locus. -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1300000

open FirstOrder FirstOrder.Language CategoryTheory MvPolynomial
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section4.ResiduePurity SpecialTransformations.Section7
open SpecialTransformations.DefinableGeometry

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}
local notation "RV" => CanonicalRV.RVSort M
local notation "k" => ModelResidue M

private theorem map_polynomialOfCoefficients {K L : Type} [Field K] [Field L] {a b : ℕ}
    (f : K →+* L) (s : Fin a → Fin b →₀ ℕ) (c : Fin a → K) :
    (polynomialOfCoefficients s c).map f = polynomialOfCoefficients s (f ∘ c) := by
  unfold polynomialOfCoefficients
  calc
    _ = ∑ i, (MvPolynomial.map f) (monomial (s i) (c i)) :=
      map_sum (MvPolynomial.map (σ := Fin b) f) _ _
    _ = _ := Finset.sum_congr rfl (fun i _ => map_monomial f (s i) (c i))

theorem exists_chartValue_of_full_volumePair_dimension
    (hc : CanonicalStructure.IsCanonical (M := M)) (B : BaseContext M) (hn : 0 < n)
    {U V : RVObject (M := M) (B.base : Set M) n} (e : U ≅ V) (hU : U.volume.FiniteFibres)
    (A : Finset (VolumeChartSupport n))
    (hA : ∀ a b : Fin n → RV, (∀ i, a i ≠ 0) → (∀ i, b i ≠ 0) →
      ∃ σ ∈ A, ∃ c : σ.Index → k, IsVolumeChart σ (volumeCorrespondence e.hom.map).carrier a b c)
    (D : DefSet (rawRVSpace (M := M) (n+n)) (B.base : Set M))
    (hD : D.carrier ⊆ (volumeCorrespondence e.hom.map).carrier)
    (hzero : ∀ t ∈ D.carrier, ∀ i, (t i).val ≠ iRVZero) (hd : rvDim D = n) :
    ∃ t ∈ D.carrier, ∃ ω, ∃ σ ∈ A, VolumeChartValue σ (volumeCorrespondence e.hom.map).carrier t ω := by
  let S := (B.base : Set M)
  let C := volumeCorrespondence e.hom.map
  obtain ⟨F, s, hF, hdF, hval⟩ := exists_full_nonzero_rvValueFibre hc B D hzero (hd.symm ▸ hn)
  let a := s.val ∘ productLeft n n
  let b := s.val ∘ productRight n n
  have hs (i : Fin (n+n)) : s.val i ≠ 0 := fun h =>
    hzero s.val (hF s.property) i ((congrArg Subtype.val h).trans RVOperations.zero_val)
  have hab : productTuple a b = s.val := by
    apply productTuple_ext
    · intro i; exact productTuple_left _ _ _
    · intro i; exact productTuple_right _ _ _
  obtain ⟨σ, hσ, c, hcert⟩ := hA a b (fun i => hs _) (fun i => hs _)
  let N := Set.range (rvValues s.val) ∪ Set.range (residueRaw ∘ c)
  let E := Substructure.closure LRV (S ∪ N)
  have hSE : S ⊆ (E : Set M) := fun _ h => Substructure.subset_closure (Or.inl h)
  have hE : Cardinal.mk E < B.κ := small_generated_finite_extension B.uncountable B.base B.small N
    ((Set.finite_range _).union (Set.finite_range _))
  have hsE (i) : (s.val i).val ∈ E := Substructure.subset_closure
    (Or.inr (Or.inl (Set.mem_range_self i)))
  have hcE (i) : residueRaw (c i) ∈ E := Substructure.subset_closure
    (Or.inr (Or.inr (Set.mem_range_self i)))
  let hex := rvExchangeInput_of_earlier B.uncountable.le B.saturated B.model00
  have hπ : (rvHeadSelect (productLeft n n) F).FiniteFibres :=
    (volumePair_leftProjection_finite e.hom.map hU).restrict (hF.trans hD)
  obtain ⟨p, hp⟩ := exists_generic_pair_on_fixed_value_fibre hc hex B.uncountable.le B.saturated B.homogeneous
    B.small E hE hSE F hπ (hdF.trans hd) s hsE hval
  let z := residueNormalize s.val p.val
  have hz : residueScale (productTuple a b) z = p.val := by
    rw [hab]
    exact residueScale_normalize s.val p.val (hval p.val p.property)
  have hz' : z ∈ normalizedCorrespondence C.carrier a b := by
    refine ⟨hz.symm ▸ hD (hF p.property), fun i hi => ?_⟩
    have he := congrFun hz i
    change productTuple a b i * residueRV (z i) = p.val i at he
    rw [hi, residueRV_zero, mul_zero] at he
    exact hzero p.val (hF p.property) i ((congrArg Subtype.val he).symm.trans RVOperations.zero_val)
  have hInd : AlgebraicIndependent (residueParameterField E) (z ∘ productLeft n n) := hp
  let c₀ (i : σ.Index) : residueParameterField E := ⟨c i, hcE i⟩
  let cut := chartInputCut σ.inputCut c₀
  have hcutMap : cut.map (residueParameterField E).subtype = chartInputCut σ.inputCut c :=
    map_polynomialOfCoefficients _ _ _
  obtain ⟨⟨x, hx⟩, _, _, _⟩ := (isVolumeChart_iff σ C.carrier a b c).mp hcert
  have hcut : cut ≠ 0 := by
    intro hz₀
    apply hx
    rw [← hcutMap, hz₀, map_zero, map_zero]
  have hcutz : (chartInputCut σ.inputCut c).eval (z ∘ productLeft n n) ≠ 0 := by
    rw [← hcutMap, MvPolynomial.eval_map]
    exact fun h => hcut (hInd.eq_zero_of_aeval_eq_zero cut h)
  let j := ((∏ i, b i) / ∏ i, a i) * residueRV (volumeChartDeterminant σ (Sum.elim c z))
  exact ⟨p.val, hF p.property, (fun _ => j), σ, hσ, a, b, c, z,
    (fun i => hs _), (fun i => hs _), hcert, hz', hcutz, hz.symm, rfl⟩

private theorem volumeChartValue_union_definable (hc : CanonicalStructure.IsCanonical (M := M))
    {S : Set M} (C : DefSet (rawRVSpace (M := M) (n+n)) S) (A : Finset (VolumeChartSupport n)) :
    (rawRVSpace (M := M) (n+n)).RelationDefinable (rawRVSpace (M := M) 1) S
      (fun t ω => ∃ σ ∈ A, VolumeChartValue σ C.carrier t ω) := by
  classical
  let P := rawRVSpace (M := M) (n+n)
  let Q := rawRVSpace (M := M) 1
  induction A using Finset.induction_on with
  | empty =>
    apply ((P.definable_empty S).left_relation P Q).congr P Q
    simp
  | insert σ A hσ ih =>
    apply ((volumeChartValue_relationDefinable hc σ C).union P Q ih).congr P Q
    simp [Finset.mem_insert, or_and_right, exists_or]

theorem exists_definable_generic_RVJacobian (hc : CanonicalStructure.IsCanonical (M := M))
    (B : BaseContext M) (hn : 0 < n)
    {U V : RVFiniteObject (M := M) (B.base : Set M) n} (e : U ≅ V)
    (hU : ∀ u : U.obj.domain, ∀ i, (U.obj.value u i).val ≠ iRVZero)
    (hV : ∀ u : V.obj.domain, ∀ i, (V.obj.value u i).val ≠ iRVZero) :
    let E := (finiteVolumeProperty (B.base : Set M) n).ι.mapIso e
    ∃ ω : Map U.obj.domain (DefSet.univ (rawRVSpace (M := M) 1) (B.base : Set M)),
      ∃ X : DefSet (rawRVSpace (M := M) U.obj.arity) (B.base : Set M),
        X.carrier ⊆ U.obj.domain.carrier ∧ rvDim X < n ∧
        ∀ u : U.obj.domain, u.val ∉ X.carrier → IsRVJacobianAt (volumeCorrespondence E.hom.map).carrier
          (U.obj.value u) (V.obj.value (E.hom.map u)) ((ω u).val 0) := by
  let S := (B.base : Set M)
  let E := (finiteVolumeProperty S n).ι.mapIso e
  let C := volumeCorrespondence E.hom.map
  let P := rawRVSpace (M := M) (n+n)
  let Q := rawRVSpace (M := M) 1
  let f := volumePairMap E.hom.map
  letI : IsAlgClosed (VFType (M := M)) := VFAlgClosed.isAlgClosed_vfType
  letI : IsAlgClosed k := ValOneEC.Johnson.isAlgClosed_residueField Values.presentationValuation
  obtain ⟨A, hA⟩ := exists_finite_volume_chart_cover hc B E
  let R (t : P.Carrier) (ω : Q.Carrier) := ∃ σ ∈ A, VolumeChartValue σ C.carrier t ω
  have hR : P.RelationDefinable Q S R := volumeChartValue_union_definable hc C A
  let D := C.sdiff ⟨{t | ∃ ω, R t ω}, hR.exists_right P Q⟩
  have hD₀ (t) (ht : t ∈ D.carrier) (i : Fin (n+n)) : (t i).val ≠ iRVZero := by
    obtain ⟨u, rfl⟩ := ht.1
    obtain ⟨j | j, rfl⟩ := finSumFinEquiv.surjective i
    · change (productTuple (U.obj.value u) (V.obj.value (E.hom.map u)) (productLeft n n j)).val ≠ iRVZero
      rw [productTuple_left]
      exact hU u j
    · change (productTuple (U.obj.value u) (V.obj.value (E.hom.map u)) (productRight n n j)).val ≠ iRVZero
      rw [productTuple_right]
      exact hV (E.hom.map u) j
  have hd : rvDim D < n := by
    by_contra h
    have hh := (volumePair_leftProjection_finite E.hom.map U.property).restrict
      (show D.carrier ⊆ C.carrier from Set.diff_subset)
    have hd' : rvDim D = n := ((rvDim_le_of_finite_map _ hh).trans (rvDim_le_arity _)).antisymm
      (Nat.le_of_not_gt h)
    obtain ⟨p, hp, ω, σ, hσ, hJ⟩ := exists_chartValue_of_full_volumePair_dimension hc B hn
      E U.property A hA D Set.diff_subset hD₀ hd'
    exact hp.2 ⟨ω, σ, hσ, hJ⟩
  have hzero : Q.Definable S {ω | ω 0 = 0} := by
    have h := (Q.definable_domain S).inter (rvZero_coordinate_definable S (0 : Fin 1))
    change S.Definable LRV _
    convert h using 1
    ext z
    constructor
    · rintro ⟨hz, he⟩
      exact ⟨hz, (congrFun (rvValues_decode ⟨z, hz⟩) 0).symm.trans
        ((congrArg Subtype.val he).trans RVOperations.zero_val)⟩
    · rintro ⟨hz, he⟩
      exact ⟨hz, Subtype.ext ((congrFun (rvValues_decode ⟨z, hz⟩) 0).trans (he.trans RVOperations.zero_val.symm))⟩
  let T (t : P.Carrier) (ω : Q.Carrier) := t ∈ C.carrier ∧ (R t ω ∨ (t ∈ D.carrier ∧ ω 0 = 0))
  have hT : P.RelationDefinable Q S T := (C.definable.left_relation P Q).inter P Q
    (hR.union P Q ((D.definable.left_relation P Q).inter P Q (hzero.right_relation P Q)))
  have hdom t ω (h : T t ω) : t ∈ C.carrier ∧ ω ∈ (DefSet.univ Q S).carrier := ⟨h.1, Set.mem_univ _⟩
  have htotal (t : C) : ∃ ω, T t.val ω := by
    by_cases ht : ∃ ω, R t.val ω
    · obtain ⟨ω, hω⟩ := ht
      exact ⟨ω, t.property, Or.inl hω⟩
    · exact ⟨fun _ => 0, t.property, Or.inr ⟨⟨t.property, ht⟩, rfl⟩⟩
  have huniq t ω η (hω : T t ω) (hη : T t η) : ω = η := by
    have he : ω 0 = η 0 := by
      rcases hω.2 with ⟨σ, hσ, hj⟩ | hω
      · rcases hη.2 with ⟨τ, hτ, hj'⟩ | hη
        · exact hj.isRVJacobianAt.unique hj'.isRVJacobianAt
        · exact (hη.1.2 ⟨ω, σ, hσ, hj⟩).elim
      · rcases hη.2 with hη | hη
        · exact (hω.1.2 ⟨η, hη⟩).elim
        · exact hω.2.trans hη.2.symm
    funext i
    fin_cases i
    exact he
  let j : Map C (DefSet.univ Q S) := Map.ofFunctionalRelation hT hdom htotal huniq
  let X := U.obj.domain.sdiff ⟨{t | ∃ u : U.obj.domain, u.val = t ∧ (f u).val ∉ D.carrier},
    f.definable_preimage (D.definable.compl P)⟩
  let f' := f.restrict (show X.carrier ⊆ U.obj.domain.carrier from Set.diff_subset)
  let g := f'.corestrict
    (fun x => by
      by_contra h
      exact x.property.2 ⟨⟨x.val, x.property.1⟩, rfl, h⟩)
  have hg : g.FiniteFibres := by
    intro z
    let q : C := ⟨z.val, z.property.1⟩
    apply (((volumePairMap_finite E.hom.map U.property).restrict
      (show X.carrier ⊆ U.obj.domain.carrier from Set.diff_subset)) q).subset
    intro x hx
    have he := congrArg Subtype.val hx
    exact Subtype.ext he
  refine ⟨j.comp f, X, Set.diff_subset, (rvDim_le_of_finite_map g hg).trans_lt hd, ?_⟩
  intro u hu
  have hnot : (f u).val ∉ D.carrier := by
    intro h
    exact hu ⟨u.property, fun h' => by
      obtain ⟨v, he, hv⟩ := h'
      exact hv (Subtype.ext he ▸ h)⟩
  have h := Map.ofFunctionalRelation_graph hT hdom htotal huniq (f u)
  rcases h.2 with ⟨σ, hσ, hJ⟩ | h
  · have he : (f u).val = productTuple (U.obj.value u) (V.obj.value (E.hom.map u)) :=
      volumePairMap_apply E.hom.map u
    have hl : (f u).val ∘ productLeft n n = U.obj.value u := by
      rw [he]
      exact funext (productTuple_left _ _)
    have hr : (f u).val ∘ productRight n n = V.obj.value (E.hom.map u) := by
      rw [he]
      exact funext (productTuple_right _ _)
    have hj := hJ.isRVJacobianAt
    rw [hl, hr] at hj
    exact hj
  · exact (hnot h.1).elim

end SpecialTransformations.Section9
