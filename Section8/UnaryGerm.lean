module

public import Section3.GammaThresholdGeometry
public import Section4.FullDimension
public import Mathlib.Topology.Algebra.Valued.ValuedField
public import Section8.IsolationFibres
public import Section8.IsolationFamilies
public import Section4.VFFiniteMaps
public import Section3.SmallFiniteParameters
public import Section4.RealPresentations
public import Section3.GammaCodeDefinability
public import Section8.UnaryPolynomial
public import Section3.RingSyntax
public import Mathlib.Algebra.Order.GroupWithZero.Basic

@[expose] public section

/-! The good locus and a uniform finite collection of positive slopes. -/

section UnaryGerms

/-! A definable unary VF set has a constant punctured germ at every
centre. This allows a finite family of candidate value laws to be
reduced to a single law near the centre. -/

set_option backward.isDefEq.respectTransparency false

open Filter Topology FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3

namespace SpecialTransformations.Section8

private theorem clopen_eventually_mem {K : Type} [TopologicalSpace K]
    {A : Set K} (hA : IsClopen A) (a : K) :
    ∀ᶠ x in 𝓝 a, x ∈ A ↔ a ∈ A := by
  by_cases ha : a ∈ A
  · filter_upwards [hA.isOpen.mem_nhds ha] with x hx
    exact iff_of_true hx ha
  · filter_upwards [hA.isClosed.isOpen_compl.mem_nhds ha] with x hx
    exact iff_of_false hx ha

private theorem kball_punctured_germ {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]
    [Valued K Γ] {A : Set K} (hA : ValOneEC.IsKBall (RingHom.id K) Valued.v A) (a : K) :
    ∃ c : Prop, ∀ᶠ x in 𝓝 a, x ≠ a → (x ∈ A ↔ c) := by
  let v : Valuation K Γ := Valued.v
  have hclose (B : Set K) (hB : IsClopen B) :
      ∃ c : Prop, ∀ᶠ x in 𝓝 a, x ≠ a → (x ∈ B ↔ c) :=
    ⟨a ∈ B, (clopen_eventually_mem hB a).mono (fun _ hx _ => hx)⟩
  cases hA with
  | univ => exact hclose _ isClopen_univ
  | openball b r =>
    apply hclose
    have he : ValOneEC.openBall v b (v r) =
        (fun x : K => x - b) ⁻¹' {x : K | v.restrict x < v.restrict r} := by
      ext x
      exact v.restrict_lt_iff.symm
    change IsClopen (ValOneEC.openBall v b (v r))
    rw [he]
    exact (Valued.isClopen_ball K (v.restrict r)).preimage (continuous_id.sub continuous_const)
  | closed b r =>
    by_cases hr : r = 0
    · subst r
      change ∃ c : Prop, ∀ᶠ x in 𝓝 a, x ≠ a → (x ∈ ValOneEC.closedBall v b (v 0) ↔ c)
      rw [map_zero, ValOneEC.closedBall_zero_radius]
      by_cases ha : a = b
      · subst b
        exact ⟨False, Filter.Eventually.of_forall (fun _ hx =>
          iff_of_false (fun h => hx (Set.mem_singleton_iff.mp h)) id)⟩
      · refine ⟨False, ?_⟩
        filter_upwards [isClosed_singleton.isOpen_compl.mem_nhds
          (show a ∈ ({b} : Set K)ᶜ from fun h => ha (Set.mem_singleton_iff.mp h))] with x hx
        exact fun _ => iff_of_false hx id
    · apply hclose
      have he : ValOneEC.closedBall v b (v r) =
          (fun x : K => x - b) ⁻¹' {x : K | v.restrict x ≤ v.restrict r} := by
        ext x
        exact v.restrict_le_iff.symm
      change IsClopen (ValOneEC.closedBall v b (v r))
      rw [he]
      exact (Valued.isClopen_closedBall K (v.restrict.ne_zero_iff.mpr hr)).preimage
        (continuous_id.sub continuous_const)

/-- Both a definable set and its complement cannot keep meeting every
punctured ball about the same centre. -/
theorem unary_definable_punctured_germ {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
    {Γ : Type} [LinearOrderedCommGroupWithZero Γ] [Valued (VFType (M := M)) Γ]
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {S A : Set M} (hA : DefinableAt S .vf A) (a : VFType (M := M)) :
    ∃ c : Prop, ∀ᶠ x in 𝓝 a, x ≠ a → (x.val ∈ A ↔ c) := by
  classical
  obtain ⟨ι, hι, B, t, hB, hmem⟩ :=
    GammaThresholdGeometry.boolean_good Valued.v hv A hA.isBoolComb_balls
  letI := hι
  choose c hc using fun i => kball_punctured_germ (hB i) a
  refine ⟨t {i | c i} = true, ?_⟩
  have hnear : ∀ᶠ x in 𝓝 a, ∀ i, x ≠ a → (x ∈ B i ↔ c i) :=
    Filter.eventually_all.mpr hc
  filter_upwards [hnear] with x hx
  intro hxa
  have he : {i | x ∈ B i} = {i | c i} := Set.ext (fun i => hx i hxa)
  exact (hmem x).trans (by rw [he])

/-- If a finite definable family covers a punctured neighbourhood, one
member contains a punctured neighbourhood. -/
theorem finite_definable_cover_has_punctured_germ
    {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
    {Γ : Type} [LinearOrderedCommGroupWithZero Γ] [Valued (VFType (M := M)) Γ]
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {ι : Type} [Finite ι] {S : Set M} (A : ι → Set M)
    (hA : ∀ i, DefinableAt S .vf (A i)) (a : VFType (M := M))
    (hcover : ∀ᶠ x in 𝓝 a, x ≠ a → ∃ i, x.val ∈ A i) :
    ∃ i, ∀ᶠ x in 𝓝 a, x ≠ a → x.val ∈ A i := by
  classical
  choose c hc using fun i => unary_definable_punctured_germ hv (hA i) a
  have hall : ∀ᶠ x in 𝓝 a, ∀ i, x ≠ a → (x.val ∈ A i ↔ c i) :=
    Filter.eventually_all.mpr hc
  let U : Set (VFType (M := M)) :=
    {x | (∀ i, x ≠ a → (x.val ∈ A i ↔ c i)) ∧ (x ≠ a → ∃ i, x.val ∈ A i)}
  have hU : U ∈ 𝓝 a := hall.and hcover
  have hinf := infinite_valued_neighbourhood (Section4.model_valuation_nontrivial hv) a hU
  have hnot : ¬ U ⊆ {a} := fun h => hinf ((Set.finite_singleton a).subset h)
  obtain ⟨x, hx, hne⟩ := Set.not_subset.mp hnot
  have hxa : x ≠ a := fun h => hne (Set.mem_singleton_iff.mpr h)
  obtain ⟨i, hi⟩ := hx.2 hxa
  have hci : c i := (hx.1 i hxa).mp hi
  exact ⟨i, (hc i).mono (fun _ h hn => (h hn).mpr hci)⟩

end SpecialTransformations.Section8
end UnaryGerms

section FamilyGraphs

/-! The actual graph of a VF family with the parameters held fixed in
each fibre. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section4

namespace SpecialTransformations.Section8

variable {M : Type} [LRV.Structure M] {k n m : ℕ}

def vfFamilyGraph
    (f : (Fin k → VFType (M := M)) → (Fin n → VFType (M := M)) → (Fin m → VFType (M := M))) :
    Set ((Fin k ⊕ (Fin n ⊕ Fin m)) → M) :=
  Set.range (fun p : (Fin k → VFType (M := M)) × (Fin n → VFType (M := M)) =>
    Sum.elim (vfValues p.1) (Sum.elim (vfValues p.2) (vfValues (f p.1 p.2))))

theorem vfFamilyGraph_fibre
    (f : (Fin k → VFType (M := M)) → (Fin n → VFType (M := M)) → (Fin m → VFType (M := M)))
    (b : Fin k → VFType (M := M)) :
    {z | Sum.elim (vfValues b) z ∈ vfFamilyGraph f} = vfGraph (f b) := by
  ext z
  constructor
  · rintro ⟨⟨b', a⟩, he⟩
    have hb : b' = b := vfValues_injective (funext (fun i => congrFun he (.inl i)))
    subst b'
    exact ⟨a, funext (fun i => congrFun he (.inr i))⟩
  · rintro ⟨a, rfl⟩
    exact ⟨(b, a), rfl⟩

theorem vfFamilyGraph_fibre_definable {S : Set M}
    {f : (Fin k → VFType (M := M)) → (Fin n → VFType (M := M)) → (Fin m → VFType (M := M))}
    (hf : S.Definable LRV (vfFamilyGraph f)) (b : Fin k → VFType (M := M)) :
    (S ∪ Set.range (vfValues b)).Definable LRV (vfGraph (f b)) := by
  rw [← vfFamilyGraph_fibre f b]
  apply (hf.mono Set.subset_union_left).preimage_map
  intro i
  cases i with
  | inl j =>
    exact LRV.definableFun_const (Fin n ⊕ Fin m) (Or.inr (Set.mem_range_self j))
  | inr j => exact Set.DefinableFun.proj LRV

end SpecialTransformations.Section8
end FamilyGraphs

section UnaryGoodLocus

/-! The locus for Lemma 8.3 where no unary input is isolated in the graph.
It is definable over the original base and has finite exceptions in each
parameter fibre. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace SpecialTransformations.Section8

variable {M : Type} [LRV.Structure M] {k m : ℕ}

abbrev unaryFamilyGraph
    (f : (Fin k → VFType (M := M)) → (Fin 1 → VFType (M := M)) → (Fin m → VFType (M := M))) :
    Set ((Fin k ⊕ (Fin 1 ⊕ Fin m)) → M) :=
  vfFamilyGraph f

theorem unaryFamilyGraph_fibre
    (f : (Fin k → VFType (M := M)) → (Fin 1 → VFType (M := M)) → (Fin m → VFType (M := M)))
    (b : Fin k → VFType (M := M)) :
    {z | Sum.elim (vfValues b) z ∈ unaryFamilyGraph f} = vfGraph (f b) :=
  vfFamilyGraph_fibre f b

theorem unaryFamilyGraph_fibre_definable {S : Set M}
    {f : (Fin k → VFType (M := M)) → (Fin 1 → VFType (M := M)) → (Fin m → VFType (M := M))}
    (hf : S.Definable LRV (unaryFamilyGraph f)) (b : Fin k → VFType (M := M)) :
    (S ∪ Set.range (vfValues b)).Definable LRV (vfGraph (f b)) :=
  vfFamilyGraph_fibre_definable hf b

/-- The good locus is restricted to the VF coordinates of the family. -/
def unaryGoodLocus
    (f : (Fin k → VFType (M := M)) → (Fin 1 → VFType (M := M)) → (Fin m → VFType (M := M))) :
    Set (Fin k ⊕ Fin 1 → M) :=
  {z | (∀ i, iVF (z i)) ∧ z ∉ isolatedInputsFamily (unaryFamilyGraph f)}

theorem unaryGoodLocus_definable {S : Set M}
    {f : (Fin k → VFType (M := M)) → (Fin 1 → VFType (M := M)) → (Fin m → VFType (M := M))}
    (hf : S.Definable LRV (unaryFamilyGraph f)) : S.Definable LRV (unaryGoodLocus f) := by
  have hVF : S.Definable LRV {z : Fin k ⊕ Fin 1 → M | ∀ i, iVF (z i)} := by
    rw [Set.ofPred_forall]
    exact Set.definable_iInter_of_finite (fun i => ((definableAt_sort S .vf).raw_definable).preimage_comp
      (fun _ : Fin 1 => i))
  exact hVF.inter (isolatedInputsFamily_definable hf).compl

variable [hM : M ⊨ Axioms.ACVF]

theorem isolatedInputs_unary_finite (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    {S : Set M} (hsmall : Cardinal.mk S < κ) (Δ : Space LRV M) (hΔ : Δ.RVCoded)
    {f : (Fin 1 → VFType (M := M)) → (Fin m → VFType (M := M))}
    (hf : S.Definable LRV (vfGraph f)) : (isolatedInputs (vfGraph f)).Finite := by
  let A := isolatedInputsObject hf
  have hd : vfDim Δ A ≤ 0 := Nat.le_of_lt_succ (lemma_8_2 hc hs hsmall Δ hΔ (by decide) f hf)
  obtain ⟨g, hg⟩ := (vf_bounded_finite_iff_finite_map hc hκ hs hsmall Δ hΔ A).mp
    ⟨hd, fun _ => Set.Subsingleton.finite (fun _ _ _ _ => funext (fun i => i.elim0))⟩
  have hgim : g.image.carrier.Finite :=
    Set.Subsingleton.finite (fun _ _ _ _ => funext (fun i => i.elim0))
  have hAfin := g.finite_source_of_finite_image hg hgim
  apply (hAfin.image (fun p => vfValues p.1)).subset
  rintro z ⟨t, ht⟩
  obtain ⟨y, hy⟩ := (mem_inputIsolation_iff z t).mp ht
  obtain ⟨a, ha⟩ := hy.1
  have he : vfValues a = z := funext (fun i => congrFun ha (.inl i))
  refine ⟨(a, Fin.elim0), ?_, he⟩
  change vfValues a ∈ isolatedInputs (vfGraph f)
  rw [he]
  exact ⟨t, ht⟩

/-- The complement of the original-base good locus is finite in each
actual unary VF fibre. This is the finiteness clause of Lemma 8.3. -/
theorem unaryGoodLocus_finite_exception (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    {S : Set M} (hsmall : Cardinal.mk S < κ) (Δ : Space LRV M) (hΔ : Δ.RVCoded)
    {f : (Fin k → VFType (M := M)) → (Fin 1 → VFType (M := M)) → (Fin m → VFType (M := M))}
    (hf : S.Definable LRV (unaryFamilyGraph f)) (b : Fin k → VFType (M := M)) :
    {a | Sum.elim (vfValues b) (vfValues a) ∉ unaryGoodLocus f}.Finite := by
  have hfin := isolatedInputs_unary_finite hc hκ hs
    (small_union_range hκ S hsmall (vfValues b)) Δ hΔ (unaryFamilyGraph_fibre_definable hf b)
  apply (hfin.preimage vfValues_injective.injOn).subset
  intro a ha
  have hsort : ∀ i, iVF (Sum.elim (vfValues b) (vfValues a) i) := by
    intro i
    cases i with
    | inl j => exact (b j).property
    | inr j => exact (a j).property
  have hi : Sum.elim (vfValues b) (vfValues a) ∈ isolatedInputsFamily (unaryFamilyGraph f) := by
    by_contra h
    exact ha ⟨hsort, h⟩
  change vfValues a ∈ isolatedInputs {z | Sum.elim (vfValues b) z ∈ unaryFamilyGraph f} at hi
  rwa [unaryFamilyGraph_fibre] at hi

end SpecialTransformations.Section8
end UnaryGoodLocus

section DominantCoordinate

/-! A finite VF tuple has a canonical coordinate of maximal value in
the multiplicative order. Its graph is definable by the finitely many
value comparisons and the coordinate order. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace SpecialTransformations.Section8

variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ] {m : ℕ}

private def IsDominant (v : Valuation K Γ) (z : Fin m → K) (j : Fin m) : Prop :=
  (∀ i, v (z i) ≤ v (z j)) ∧ (∀ i, i < j → v (z i) < v (z j))

public noncomputable def maximizers (v : Valuation K Γ) (z : Fin m → K) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter (fun j => ∀ i, v (z i) ≤ v (z j))

public theorem maximizers_nonempty (v : Valuation K Γ) (z : Fin m → K) (hm : 0 < m) :
    (maximizers v z).Nonempty := by
  classical
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image Finset.univ (fun j : Fin m => v (z j))
    ⟨⟨0, hm⟩, Finset.mem_univ _⟩
  exact ⟨j, Finset.mem_filter.mpr ⟨hj, fun i => hmax i (Finset.mem_univ _)⟩⟩

noncomputable def dominantIndex (v : Valuation K Γ) (z : Fin m → K) (hm : 0 < m) : Fin m :=
  (maximizers v z).min' (maximizers_nonempty v z hm)

private theorem dominantIndex_spec (v : Valuation K Γ) (z : Fin m → K) (hm : 0 < m) :
    IsDominant v z (dominantIndex v z hm) := by
  classical
  let s := maximizers v z
  let j := dominantIndex v z hm
  have hmem : j ∈ s := Finset.min'_mem _ _
  have hmax : ∀ i, v (z i) ≤ v (z j) := (Finset.mem_filter.mp hmem).2
  refine ⟨hmax, fun i hij => ?_⟩
  by_contra! hle
  have hi : i ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun k => (hmax k).trans hle⟩
  exact (not_le_of_gt hij) (Finset.min'_le s i hi)

private theorem IsDominant.unique {v : Valuation K Γ} {z : Fin m → K} {i j : Fin m}
    (hi : IsDominant v z i) (hj : IsDominant v z j) : i = j := by
  rcases lt_trichotomy i j with hij | hij | hji
  · exact False.elim ((not_le_of_gt (hj.2 i hij)) (hi.1 j))
  · exact hij
  · exact False.elim ((not_le_of_gt (hi.2 j hji)) (hj.1 i))

noncomputable def dominantCoordinate (v : Valuation K Γ) (z : Fin m → K) (hm : 0 < m) : K :=
  z (dominantIndex v z hm)

theorem value_le_dominantCoordinate (v : Valuation K Γ) (z : Fin m → K) (hm : 0 < m) (i : Fin m) :
    v (z i) ≤ v (dominantCoordinate v z hm) := (dominantIndex_spec v z hm).1 i

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def dominantGraph (v : Valuation (VFType (M := M)) Γ) (hm : 0 < m) : Set (Fin m ⊕ Fin 1 → M) :=
  Set.range (fun x : Fin m → VFType (M := M) =>
    Sum.elim (vfValues x) (fun _ => (dominantCoordinate v x hm).val))

private theorem raw_value_le_definable {ι : Type} (S : Set M) (i j : ι) :
    S.Definable LRV {z : ι → M | iLe (iRv (z j)) (iRv (z i))} := by
  let t (i : ι) : LRV.Term ι := .func Fn.rvMap ![.var i]
  have hmap : S.DefinableMap LRV (fun z : ι → M => ![(t j).realize z, (t i).realize z]) := by
    intro k
    fin_cases k
    · exact (t j).definableFun_realize.mono (Set.empty_subset S)
    · exact (t i).definableFun_realize.mono (Set.empty_subset S)
  convert (GammaParameters.raw_le_definable S).preimage_map hmap using 1
  ext z
  change iLe (iRv (z j)) (iRv (z i)) ↔ iLe ((t j).realize z) ((t i).realize z)
  have ht (k : ι) : (t k).realize z = iRv (z k) := by
    dsimp only [t, Term.realize, iRv]
    congr 1
    funext l
    fin_cases l
    rfl
  rw [ht, ht]

theorem dominantGraph_definable (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)
    (hm : 0 < m) (S : Set M) : S.Definable LRV (dominantGraph v hm) := by
  let I := Fin m ⊕ Fin 1
  let VF : Set (I → M) := {z | ∀ i : Fin m, iVF (z (.inl i))}
  let D (j : Fin m) : Set (I → M) := {z |
    z (.inr 0) = z (.inl j) ∧ (∀ i, iLe (iRv (z (.inl j))) (iRv (z (.inl i)))) ∧
      ∀ i, i < j → ¬ iLe (iRv (z (.inl i))) (iRv (z (.inl j)))}
  have hVF : S.Definable LRV VF := by
    change S.Definable LRV {z : I → M | ∀ i : Fin m, iVF (z (.inl i))}
    rw [Set.ofPred_forall]
    exact Set.definable_iInter_of_finite (fun i => ((definableAt_sort S .vf).raw_definable).preimage_comp
      (fun _ : Fin 1 => (Sum.inl i : I)))
  have hD (j : Fin m) : S.Definable LRV (D j) := by
    have he := (Set.DefinableFun.proj LRV (A := S) (i := (Sum.inr 0 : I))).ofPred_eq
      (Set.DefinableFun.proj LRV (i := Sum.inl j))
    have hle : S.Definable LRV {z : I → M | ∀ i : Fin m,
        iLe (iRv (z (.inl j))) (iRv (z (.inl i)))} := by
      rw [Set.ofPred_forall]
      exact Set.definable_iInter_of_finite (fun i : Fin m =>
        raw_value_le_definable S (Sum.inl i : I) (Sum.inl j))
    have hlt (i : Fin m) : S.Definable LRV {z : I → M |
        i < j → ¬ iLe (iRv (z (.inl i))) (iRv (z (.inl j)))} := by
      by_cases h : i < j
      · simp only [h, true_implies]
        exact (raw_value_le_definable S (Sum.inl j : I) (.inl i)).compl
      · simp only [h, false_implies, Set.setOf_true]
        exact Set.definable_univ
    have hall : S.Definable LRV {z : I → M | ∀ i : Fin m,
        i < j → ¬ iLe (iRv (z (.inl i))) (iRv (z (.inl j)))} := by
      rw [Set.ofPred_forall]
      exact Set.definable_iInter_of_finite hlt
    exact he.inter (hle.inter hall)
  convert hVF.inter (Set.definable_iUnion_of_finite hD) using 1
  ext z
  change (∃ x : Fin m → VFType (M := M),
    Sum.elim (vfValues x) (fun _ : Fin 1 => (dominantCoordinate v x hm).val) = z) ↔
    z ∈ VF ∧ z ∈ ⋃ j, D j
  rw [Set.mem_iUnion]
  have hvalue (x y : VFType (M := M)) :
      iLe (iRv y.val) (iRv x.val) ↔ v x ≤ v y := hv x y
  constructor
  · rintro ⟨x, rfl⟩
    let j := dominantIndex v x hm
    have hj := dominantIndex_spec v x hm
    refine ⟨fun i => (x i).property, j, rfl, ?_, ?_⟩
    · exact fun i => (hvalue (x i) (x j)).mpr (hj.1 i)
    · intro i hi hle
      exact (not_le_of_gt (hj.2 i hi)) ((hvalue (x j) (x i)).mp hle)
  · rintro ⟨hz, j, he, hle, hlt⟩
    let x : Fin m → VFType (M := M) := fun i => ⟨z (.inl i), hz i⟩
    have hj : IsDominant v x j := by
      refine ⟨fun i => (hvalue (x i) (x j)).mp (hle i), fun i hi => ?_⟩
      exact lt_of_not_ge (fun h => hlt i hi ((hvalue (x j) (x i)).mpr h))
    have hindex := (dominantIndex_spec v x hm).unique hj
    refine ⟨x, ?_⟩
    funext i
    cases i with
    | inl k => rfl
    | inr k =>
      fin_cases k
      change (x (dominantIndex v x hm)).val = z (.inr 0)
      rw [hindex]
      exact he.symm

end SpecialTransformations.Section8
end DominantCoordinate

section CenteredUnaryGraph

/-! The centre is an extra VF parameter. For tuple outputs, the scalar
graph selects the coordinate of maximal value in the centred difference. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace SpecialTransformations.Section8

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k m : ℕ}
variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ]

noncomputable def centeredUnaryFamily (v : Valuation (VFType (M := M)) Γ) (hm : 0 < m)
    (f : (Fin k → VFType (M := M)) → (Fin 1 → VFType (M := M)) → (Fin m → VFType (M := M)))
    (p : Fin (k + 1) → VFType (M := M)) (x : VFType (M := M)) : VFType (M := M) :=
  dominantCoordinate v (f (Fin.init p) ![x] - f (Fin.init p) ![p (Fin.last k)]) hm

theorem centeredUnaryFamily_definable (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y) (hm : 0 < m)
    {S : Set M}
    {f : (Fin k → VFType (M := M)) → (Fin 1 → VFType (M := M)) → (Fin m → VFType (M := M))}
    (hf : S.Definable LRV (unaryFamilyGraph f)) :
    S.Definable LRV (unaryScalarFamilyGraph (centeredUnaryFamily v hm f)) := by
  let X := Fin k ⊕ (Fin 1 ⊕ Fin m)
  let Z := Fin (k + 1) ⊕ Fin 2
  let W := Fin m ⊕ (Fin m ⊕ Fin m)
  let I := Z ⊕ W
  let param (i : Fin k) : I := .inl (.inl i.castSucc)
  let first (i : Fin m) : I := .inr (.inl i)
  let second (i : Fin m) : I := .inr (.inr (.inl i))
  let diff (i : Fin m) : I := .inr (.inr (.inr i))
  let xGraph : X → I := Sum.elim param (Sum.elim (fun _ => .inl (.inr 0)) first)
  let aGraph : X → I := Sum.elim param (Sum.elim (fun _ => .inl (.inl (Fin.last k))) second)
  let maxGraph : Fin m ⊕ Fin 1 → I := Sum.elim diff (fun _ => .inl (.inr 1))
  have hdiff : S.Definable LRV {z : I → M | ∀ i, iVFAdd (z (first i)) (iVFNeg (z (second i))) = z (diff i)} := by
    rw [Set.ofPred_forall]
    apply Set.definable_iInter_of_finite
    intro i
    have hneg : S.DefinableFun LRV (fun z : I → M => iVFNeg (z (second i))) :=
      (Set.DefinableFun.of_empty (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.vfNeg)).comp
        (show S.DefinableMap LRV (fun z : I → M => ![z (second i)]) from by
          intro j; fin_cases j; exact Set.DefinableFun.proj LRV)
    have hadd : S.DefinableFun LRV (fun z : I → M => iVFAdd (z (first i)) (iVFNeg (z (second i)))) :=
      (Set.DefinableFun.of_empty (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.vfAdd)).comp
        (show S.DefinableMap LRV (fun z : I → M => ![z (first i), iVFNeg (z (second i))]) from by
          intro j; fin_cases j
          · exact Set.DefinableFun.proj LRV
          · exact hneg)
    exact hadd.ofPred_eq (Set.DefinableFun.proj LRV (i := diff i))
  have hmax := (dominantGraph_definable v hv hm S).preimage_comp maxGraph
  have hd := ((hf.preimage_comp xGraph).inter ((hf.preimage_comp aGraph).inter (hdiff.inter hmax))).exists_of_finite
  convert hd using 1
  ext z
  change z ∈ unaryScalarFamilyGraph (centeredUnaryFamily v hm f) ↔
    ∃ w : W → M, Sum.elim z w ∘ xGraph ∈ unaryFamilyGraph f ∧
      Sum.elim z w ∘ aGraph ∈ unaryFamilyGraph f ∧
      (∀ i, iVFAdd (w (.inl i)) (iVFNeg (w (.inr (.inl i)))) = w (.inr (.inr i))) ∧
      Sum.elim z w ∘ maxGraph ∈ dominantGraph v hm
  constructor
  · rintro ⟨⟨p, x⟩, rfl⟩
    let b := Fin.init p
    let a := p (Fin.last k)
    let fx := f b ![x]
    let fa := f b ![a]
    let d := fx - fa
    let w : W → M := Sum.elim (vfValues fx) (Sum.elim (vfValues fa) (vfValues d))
    refine ⟨w, ⟨(b, ![x]), ?_⟩, ⟨(b, ![a]), ?_⟩, ?_, ⟨d, ?_⟩⟩
    · funext i
      rcases i with i | (j | j)
      · rfl
      · fin_cases j
        rfl
      · rfl
    · funext i
      rcases i with i | (j | j)
      · rfl
      · fin_cases j
        rfl
      · rfl
    · intro i
      change _ = (fx i - fa i).val
      rw [sub_eq_add_neg]
      rfl
    · funext i
      cases i <;> rfl
  · rintro ⟨w, ⟨⟨b, x⟩, hx⟩, ⟨⟨c, a⟩, ha⟩, hdiff, ⟨d, hd⟩⟩
    have hcb : c = b := vfValues_injective (funext (fun i =>
      (congrFun ha (.inl i)).trans (congrFun hx (.inl i)).symm))
    subst c
    have hde : d = f b x - f b a := by
      funext i
      have hfx : (f b x i).val = w (.inl i) := congrFun hx (.inr (.inr i))
      have hfa : (f b a i).val = w (.inr (.inl i)) := congrFun ha (.inr (.inr i))
      have hdi : (d i).val = w (.inr (.inr i)) := congrFun hd (.inl i)
      have h := hdiff i
      rw [← hfx, ← hfa, ← hdi] at h
      apply Subtype.ext
      change (d i).val = (f b x i - f b a i).val
      rw [sub_eq_add_neg]
      exact h.symm
    have hx' : ![x 0] = x := funext (fun i => by fin_cases i; rfl)
    have ha' : ![a 0] = a := funext (fun i => by fin_cases i; rfl)
    refine ⟨(Fin.snoc b (a 0), x 0), ?_⟩
    funext i
    rcases i with i | j
    · refine Fin.lastCases ?_ (fun i => ?_) i
      · simpa only [Sum.elim_inl, Sum.elim_inr, vfValues, Fin.snoc_last, Function.comp_apply, aGraph] using
          congrFun ha (.inr (.inl 0))
      · simpa only [Sum.elim_inl, Sum.elim_inr, vfValues, Fin.snoc_castSucc, Function.comp_apply, xGraph, param] using
          congrFun hx (.inl i)
    · fin_cases j
      · exact congrFun hx (.inr (.inl 0))
      · change (centeredUnaryFamily v hm f (Fin.snoc b (a 0)) (x 0)).val = z (.inr 1)
        rw [centeredUnaryFamily, Fin.init_snoc, Fin.snoc_last, hx', ha', ← hde]
        exact congrFun hd (.inr 0)

end SpecialTransformations.Section8
end CenteredUnaryGraph

section UnaryValueLaws

/-! Each proposed tie of two polynomial terms is a definable unary
condition on the graph. The proof uses equality of values. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3

namespace SpecialTransformations.Section8

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

public def rvTerm {ι : Type} (t : LRV.Term ι) : LRV.Term ι := .func Fn.rvMap ![t]

private theorem rvTerm_realize {ι : Type} (t : LRV.Term ι) (z : ι → M) :
    (rvTerm t).realize z = iRv (t.realize z) := by
  rw [rvTerm, Term.realize]
  unfold iRv
  congr 1
  funext i
  fin_cases i
  rfl

def termValueEq {ι : Type} (t u : LRV.Term ι) (z : ι → M) : Prop :=
  iLe ((rvTerm t).realize z) ((rvTerm u).realize z) ∧
    iLe ((rvTerm u).realize z) ((rvTerm t).realize z)

theorem termValueEq_realize {ι : Type} (t u : LRV.Term ι) (z : ι → M) :
    termValueEq t u z ↔ iLe (iRv (t.realize z)) (iRv (u.realize z)) ∧
      iLe (iRv (u.realize z)) (iRv (t.realize z)) := by
  simp only [termValueEq, rvTerm_realize]

private theorem rvTermPair_definable {ι : Type} (S : Set M) (p q : LRV.Term ι) :
    S.DefinableMap LRV (fun z : ι → M => ![(rvTerm p).realize z, (rvTerm q).realize z]) := by
  intro i
  fin_cases i
  · exact (rvTerm p).definableFun_realize.mono (Set.empty_subset S)
  · exact (rvTerm q).definableFun_realize.mono (Set.empty_subset S)

theorem termValueEq_definable {ι : Type} (S : Set M) (t u : LRV.Term ι) :
    S.Definable LRV {z | termValueEq t u z} := by
  have h := GammaParameters.raw_le_definable S
  exact (h.preimage_map (rvTermPair_definable S t u)).inter (h.preimage_map (rvTermPair_definable S u t))

/-- Weak comparison in Mathlib's multiplicative valuation order. -/
def termValueLe {ι : Type} (t u : LRV.Term ι) (z : ι → M) : Prop :=
  iLe ((rvTerm u).realize z) ((rvTerm t).realize z)

theorem termValueLe_definable {ι : Type} (S : Set M) (t u : LRV.Term ι) :
    S.Definable LRV {z | termValueLe t u z} :=
  (GammaParameters.raw_le_definable S).preimage_map (rvTermPair_definable S u t)

private noncomputable def powerTerm (b : Fin 5) (p i : ℕ) : LRV.Term (Fin 5) :=
  let v : Fin 5 → FreeCommRing (Fin 5) := FreeCommRing.of
  RingSyntax.ofRingTerm (FirstOrder.Ring.termOfFreeCommRing ((v 0 - v 2) ^ p * v b * v 1 ^ i))

private theorem powerTerm_realize (b : Fin 5) (p i : ℕ) (z : Fin 5 → VFType (M := M)) :
    (powerTerm b p i).realize (fun j => (z j).val) = ((z 0 - z 2) ^ p * z b * z 1 ^ i).val := by
  dsimp only [powerTerm]
  rw [RingSyntax.realizes, FirstOrder.Ring.realize_termOfFreeCommRing]
  simp only [map_sub, map_pow, map_mul, FreeCommRing.lift_of]

def unaryValueLaw (v : Valuation (VFType (M := M)) Γ)
    (f : VFType (M := M) → VFType (M := M)) (a b c : VFType (M := M)) (p q i j : ℕ) : Set M :=
  {z | ∃ x : VFType (M := M), x.val = z ∧ f x ≠ 0 ∧
    (v (x - a) ^ p * v b) * v (f x) ^ i = (v (x - a) ^ q * v c) * v (f x) ^ j}

theorem mem_unaryValueLaw_iff (v : Valuation (VFType (M := M)) Γ)
    (f : VFType (M := M) → VFType (M := M)) (a b c x : VFType (M := M)) (p q i j : ℕ) :
    x.val ∈ unaryValueLaw v f a b c p q i j ↔ f x ≠ 0 ∧
      (v (x - a) ^ p * v b) * v (f x) ^ i = (v (x - a) ^ q * v c) * v (f x) ^ j := by
  constructor
  · rintro ⟨y, hy, hne, he⟩
    have h : y = x := Subtype.ext hy
    subst y
    exact ⟨hne, he⟩
  · exact fun h => ⟨x, rfl, h.1, h.2⟩

theorem unaryValueLaw_definable (hc : CanonicalStructure.IsCanonical (M := M))
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)
    {S : Set M} {f : VFType (M := M) → VFType (M := M)}
    (hf : S.Definable LRV (unaryScalarGraph f)) (a b c : VFType (M := M)) (p q i j : ℕ) :
    DefinableAt (S ∪ Set.range (![a.val, b.val, c.val] : Fin 3 → M)) .vf
      (unaryValueLaw v f a b c p q i j) := by
  let B := S ∪ Set.range (![a.val, b.val, c.val] : Fin 3 → M)
  let F (z : Fin 2 → M) : Fin 5 → M := ![z 0, z 1, a.val, b.val, c.val]
  let t := powerTerm 3 p i
  let u := powerTerm 4 q j
  have hF : B.DefinableMap LRV F := by
    intro k
    fin_cases k
    · exact Set.DefinableFun.proj LRV
    · exact Set.DefinableFun.proj LRV
    · exact LRV.definableFun_const (Fin 2) (Or.inr (Set.mem_range_self (0 : Fin 3)))
    · exact LRV.definableFun_const (Fin 2) (Or.inr (Set.mem_range_self (1 : Fin 3)))
    · exact LRV.definableFun_const (Fin 2) (Or.inr (Set.mem_range_self (2 : Fin 3)))
  have hz : B.DefinableFun LRV (fun _ : Fin 2 → M => iVFZero) :=
    DefinableConstants.constant (DefinableConstants.function_symbol
      (L := LRV) Fn.vfZero Fin.elim0 (fun k => k.elim0))
  have hn := ((Set.DefinableFun.proj LRV (i := (1 : Fin 2))).ofPred_eq hz).compl
  have he := (termValueEq_definable B t u).preimage_map hF
  have hproj := ((hf.mono Set.subset_union_left).inter (he.inter hn)).image_comp (fun _ : Fin 1 => 0)
  have hvalue (x : VFType (M := M)) :
      let z := F ![x.val, (f x).val]
      (iLe ((rvTerm t).realize z) ((rvTerm u).realize z) ∧
        iLe ((rvTerm u).realize z) ((rvTerm t).realize z)) ↔
        (v (x - a) ^ p * v b) * v (f x) ^ i = (v (x - a) ^ q * v c) * v (f x) ^ j := by
    let z : Fin 5 → VFType (M := M) := ![x, f x, a, b, c]
    have hcode : F ![x.val, (f x).val] = fun k => (z k).val := by
      funext k
      fin_cases k <;> rfl
    dsimp only
    rw [hcode]
    simp only [rvTerm_realize]
    rw [show t.realize (fun k => (z k).val) = ((x - a) ^ p * b * f x ^ i).val from
      powerTerm_realize 3 p i z,
      show u.realize (fun k => (z k).val) = ((x - a) ^ q * c * f x ^ j).val from
        powerTerm_realize 4 q j z]
    change (VFValued.predV ((x - a) ^ q * c * f x ^ j) ((x - a) ^ p * b * f x ^ i) ∧
      VFValued.predV ((x - a) ^ p * b * f x ^ i) ((x - a) ^ q * c * f x ^ j)) ↔ _
    rw [hv, hv]
    simp only [map_mul, map_pow]
    exact ⟨fun h => le_antisymm h.2 h.1, fun h => ⟨h.ge, h.le⟩⟩
  have hsort : unaryValueLaw v f a b c p q i j ⊆ {z | iVF z} := by
    rintro _ ⟨x, rfl, _, _⟩
    exact x.property
  have hsorted (z : Fin 1 → M) (hz : z 0 ∈ unaryValueLaw v f a b c p q i j) (k : Fin 1) :
      iVF (z k) := by
    fin_cases k
    exact hsort hz
  refine ⟨raw_definableOver_sorted hc B (fun _ => .vf) _ ?_ hsorted, hsort⟩
  convert hproj using 1
  ext z
  constructor
  · rintro ⟨x, hx, hn', he'⟩
    refine ⟨![x.val, (f x).val], ⟨⟨x, rfl, rfl⟩, (hvalue x).mpr he', ?_⟩, ?_⟩
    · exact fun hz' => hn' (Subtype.ext hz')
    · funext k
      fin_cases k
      exact hx
  · rintro ⟨w, ⟨⟨x, hx, hy⟩, hw, hn'⟩, he'⟩
    have hw' : ![x.val, (f x).val] = w := by
      funext k
      fin_cases k <;> assumption
    subst w
    exact ⟨x, congrFun he' 0, fun hz' => hn' (congrArg Subtype.val hz'), (hvalue x).mp hw⟩

def unaryZeroLocus (f : VFType (M := M) → VFType (M := M)) : Set M :=
  {z | ∃ x : VFType (M := M), x.val = z ∧ f x = 0}

theorem mem_unaryZeroLocus_iff (f : VFType (M := M) → VFType (M := M)) (x : VFType (M := M)) :
    x.val ∈ unaryZeroLocus f ↔ f x = 0 := by
  constructor
  · rintro ⟨y, hy, h⟩
    have he : y = x := Subtype.ext hy
    rwa [he] at h
  · exact fun h => ⟨x, rfl, h⟩

theorem unaryZeroLocus_definable (hc : CanonicalStructure.IsCanonical (M := M))
    {S : Set M} {f : VFType (M := M) → VFType (M := M)}
    (hf : S.Definable LRV (unaryScalarGraph f)) : DefinableAt S .vf (unaryZeroLocus f) := by
  have hz : S.DefinableFun LRV (fun _ : Fin 2 → M => iVFZero) :=
    DefinableConstants.constant (DefinableConstants.function_symbol
      (L := LRV) Fn.vfZero Fin.elim0 (fun k => k.elim0))
  have h := (hf.inter ((Set.DefinableFun.proj LRV (i := (1 : Fin 2))).ofPred_eq hz)).image_comp
    (fun _ : Fin 1 => 0)
  have hs : unaryZeroLocus f ⊆ {z | iVF z} := by
    rintro _ ⟨x, rfl, _⟩
    exact x.property
  refine ⟨raw_definableOver_sorted hc S (fun _ => .vf) _ ?_ (fun z hz k => ?_), hs⟩
  · convert h using 1
    ext z
    constructor
    · rintro ⟨x, hx, hzero⟩
      refine ⟨![x.val, (f x).val], ⟨⟨x, rfl, rfl⟩, congrArg Subtype.val hzero⟩, ?_⟩
      funext k
      fin_cases k
      exact hx
    · rintro ⟨w, ⟨⟨x, hx, hy⟩, hw⟩, he⟩
      exact ⟨x, hx.trans (congrFun he 0), Subtype.ext (hy.trans hw)⟩
  · fin_cases k
    exact hs hz

end SpecialTransformations.Section8
end UnaryValueLaws

section ValuationTieAlgebra

/-! Cancellation in a tie between two nonzero valued terms. The
inequalities use the multiplicative order, where small values approach zero. -/

namespace SpecialTransformations.Section8

variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ]

/-- With two distinct output powers, a tie with both values small forces
the input order of the lower output power to be strictly larger. -/
theorem input_order_lt_of_small_tie {x y b c : Γ} (hx : x ≠ 0) (hy : y ≠ 0)
    (hx₁ : x ≤ 1) (hy₁ : y ≤ 1) (hsmall : c * y < b)
    {p q i j : ℕ} (hij : i < j)
    (h : (x ^ p * b) * y ^ i = (x ^ q * c) * y ^ j) : q < p := by
  by_contra! hpq
  have hxq : x ^ q = x ^ p * x ^ (q - p) := by
    rw [← pow_add, Nat.add_sub_of_le hpq]
  have hyj : y ^ j = y ^ i * y ^ (j - i) := by
    rw [← pow_add, Nat.add_sub_of_le hij.le]
  have he : (x ^ p * y ^ i) * b = (x ^ p * y ^ i) * (x ^ (q - p) * (c * y ^ (j - i))) := by
    calc
      _ = (x ^ p * b) * y ^ i := by ac_rfl
      _ = (x ^ q * c) * y ^ j := h
      _ = _ := by rw [hxq, hyj]; ac_rfl
  have hb := mul_left_cancel₀ (mul_ne_zero (pow_ne_zero _ hx) (pow_ne_zero _ hy)) he
  obtain ⟨d, hd⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.sub_ne_zero_of_lt hij)
  have hpow : y ^ (j - i) ≤ y := by
    rw [hd, pow_succ]
    exact mul_le_of_le_one_left zero_le (pow_le_one₀ zero_le hy₁)
  apply (not_le_of_gt hsmall)
  calc
    b = x ^ (q - p) * (c * y ^ (j - i)) := hb
    _ ≤ c * y ^ (j - i) := mul_le_of_le_one_left zero_le (pow_le_one₀ zero_le hx₁)
    _ ≤ c * y := mul_le_mul_of_nonneg_left hpow zero_le

/-- Cancelling the common factors yields the power form of the
rational slope `(p - q) / (j - i)`. -/
theorem power_law_of_tie {x y b c : Γ} (hx : x ≠ 0) (hy : y ≠ 0) (hc : c ≠ 0)
    {p q i j : ℕ} (hqp : q ≤ p) (hij : i ≤ j)
    (h : (x ^ p * b) * y ^ i = (x ^ q * c) * y ^ j) :
    y ^ (j - i) = (b / c) * x ^ (p - q) := by
  have hxp : x ^ p = x ^ q * x ^ (p - q) := by
    rw [← pow_add, Nat.add_sub_of_le hqp]
  have hyj : y ^ j = y ^ i * y ^ (j - i) := by
    rw [← pow_add, Nat.add_sub_of_le hij]
  have he : (x ^ q * y ^ i) * (b * x ^ (p - q)) = (x ^ q * y ^ i) * (y ^ (j - i) * c) := by
    calc
      _ = (x ^ p * b) * y ^ i := by rw [hxp]; ac_rfl
      _ = (x ^ q * c) * y ^ j := h
      _ = _ := by rw [hyj]; ac_rfl
  have hb := mul_left_cancel₀ (mul_ne_zero (pow_ne_zero _ hx) (pow_ne_zero _ hy)) he
  rw [div_mul_eq_mul_div₀]
  exact (eq_div_iff hc).mpr hb.symm

end SpecialTransformations.Section8
end ValuationTieAlgebra

section ScalarSlopeGerm

/-! Select a single law on a punctured ball and rule out nonpositive
slopes when arbitrarily close inputs have arbitrarily small output. -/

set_option backward.isDefEq.respectTransparency false

open Filter Topology FirstOrder FirstOrder.Language Polynomial
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace SpecialTransformations.Section8

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ] [Valued (VFType (M := M)) Γ]

private theorem exists_small_step (r : VFType (M := M)) (hr : r ≠ 0) :
    ∃ s : VFType (M := M), s ≠ 0 ∧ Valued.v s ≤ Valued.v r ∧ Valued.v s ≤ (1 : Γ) := by
  by_cases h : Valued.v r ≤ (1 : Γ)
  · exact ⟨r, hr, le_rfl, h⟩
  · exact ⟨1, one_ne_zero, by simpa only [map_one] using (le_of_not_ge h), by rw [map_one]⟩

/-- The numerator and denominator bounds depend only on the polynomial
shape. The local law is in powers of the multiplicative valuation. -/
theorem scalar_eventually_zero_or_positive_power (hc : CanonicalStructure.IsCanonical (M := M))
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {S : Set M} {f : VFType (M := M) → VFType (M := M)}
    (hf : S.Definable LRV (unaryScalarGraph f))
    (D : Finset (ℕ × ℕ)) (c : ↥D → VFType (M := M)) (hc₀ : ∃ d, c d ≠ 0)
    (hpoly : ∀ x, ((shapedPolynomial D c).map (Polynomial.evalRingHom x)).eval (f x) = 0)
    (a : VFType (M := M))
    (hclose : ∀ r s : VFType (M := M), r ≠ 0 → s ≠ 0 →
      ∃ x, x ≠ a ∧ Valued.v (x - a) < Valued.v r ∧ Valued.v (f x) < Valued.v s) :
    (∀ᶠ x in 𝓝 a, x ≠ a → f x = 0) ∨
      ∃ p q : ℕ, 0 < p ∧ p ≤ D.sup Prod.fst ∧ 0 < q ∧ q ≤ D.sup Prod.snd ∧
        ∃ s : VFType (M := M), s ≠ 0 ∧ ∀ᶠ x in 𝓝 a, x ≠ a → f x ≠ 0 ∧
          Valued.v (f x) ^ q = Valued.v s * Valued.v (x - a) ^ p := by
  let K := VFType (M := M)
  let v : Valuation K Γ := Valued.v
  let P := shapedPolynomial D c
  let e (i : ℕ) := (P.coeff i).rootMultiplicity a
  let b (i : ℕ) := ((P.coeff i).comp (X + C a)).trailingCoeff
  let I := Fin (D.sup Prod.snd + 1)
  let J := {j : I × I // j.1.val < j.2.val ∧ e j.1.val ≤ D.sup Prod.fst ∧
    e j.2.val ≤ D.sup Prod.fst ∧ b j.1.val ≠ 0 ∧ b j.2.val ≠ 0}
  let B := S ∪ insert a.val (Set.range (fun i => (b i).val))
  let A : Option J → Set M := fun j => match j with
    | none => unaryZeroLocus f
    | some j => unaryValueLaw v f a (b j.val.1.val) (b j.val.2.val)
        (e j.val.1.val) (e j.val.2.val) j.val.1.val j.val.2.val
  have hA (j : Option J) : DefinableAt B .vf (A j) := by
    cases j with
    | none => exact (unaryZeroLocus_definable hc hf).mono Set.subset_union_left
    | some j =>
      apply (unaryValueLaw_definable hc v hv hf a (b j.val.1.val) (b j.val.2.val) _ _ _ _).mono
      intro z hz
      rcases hz with hz | ⟨k, rfl⟩
      · exact Or.inl hz
      · fin_cases k
        · exact Or.inr (Set.mem_insert _ _)
        · exact Or.inr (Set.mem_insert_of_mem _ (Set.mem_range_self j.val.1.val))
        · exact Or.inr (Set.mem_insert_of_mem _ (Set.mem_range_self j.val.2.val))
  have hcover : ∀ᶠ x in 𝓝 a, x ≠ a → ∃ j, x.val ∈ A j := by
    filter_upwards [eventually_shaped_root_tie D c hc₀ a] with x hx
    intro hxa
    by_cases hfx : f x = 0
    · exact ⟨none, (mem_unaryZeroLocus_iff f x).mpr hfx⟩
    · obtain ⟨i, j, hij, hj, hi, hj', hbi, hbj, ht⟩ := hx hxa (f x) hfx (hpoly x)
      let ii : I := ⟨i, Nat.lt_succ_of_le (hij.le.trans hj)⟩
      let jj : I := ⟨j, Nat.lt_succ_of_le hj⟩
      let w : J := ⟨(ii, jj), hij, hi, hj', hbi, hbj⟩
      exact ⟨some w, (mem_unaryValueLaw_iff v f a (b i) (b j) x _ _ i j).mpr ⟨hfx, ht⟩⟩
  obtain ⟨j, hj⟩ := finite_definable_cover_has_punctured_germ hv A hA a hcover
  cases j with
  | none => exact Or.inl (hj.mono (fun x hx hxa => (mem_unaryZeroLocus_iff f x).mp (hx hxa)))
  | some w =>
    let i := w.val.1.val
    let j := w.val.2.val
    have hij : i < j := w.property.1
    have hbi : b i ≠ 0 := w.property.2.2.2.1
    have hbj : b j ≠ 0 := w.property.2.2.2.2
    have ht (x : K) (hx : x.val ∈ A (some w)) :=
      (mem_unaryValueLaw_iff v f a (b i) (b j) x (e i) (e j) i j).mp hx
    have hs₀ : b i / b j ≠ 0 := div_ne_zero hbi hbj
    have hpos : e j < e i := by
      obtain ⟨r, hr, hrsub⟩ := exists_nonzero_ball_subset a hj
      obtain ⟨r', hr', hrr', hr₁⟩ := exists_small_step (Γ := Γ) r hr
      obtain ⟨s, hs, hss, hs₁⟩ := exists_small_step (Γ := Γ) (b i / b j) hs₀
      obtain ⟨x, hxa, hxr, hxs⟩ := hclose r' s hr' hs
      have hxt := ht x (hrsub (hxr.trans_le hrr') hxa)
      have hsmall : v (b j) * v (f x) < v (b i) := by
        have h := hxs.trans_le hss
        change v (f x) < v (b i / b j) at h
        rw [map_div₀] at h
        calc
          v (b j) * v (f x) = v (f x) * v (b j) := mul_comm _ _
          _ < v (b i) := (lt_div_iff₀ (pos_iff_ne_zero.mpr (v.ne_zero_iff.mpr hbj))).mp h
      exact input_order_lt_of_small_tie (v.ne_zero_iff.mpr (sub_ne_zero.mpr hxa))
        (v.ne_zero_iff.mpr hxt.1) (hxr.le.trans hr₁) (hxs.le.trans hs₁) hsmall hij hxt.2
    refine Or.inr ⟨e i - e j, j - i, Nat.sub_pos_of_lt hpos,
      (Nat.sub_le _ _).trans w.property.2.1, Nat.sub_pos_of_lt hij,
      (Nat.sub_le _ _).trans (Nat.le_of_lt_succ w.val.2.isLt), b i / b j, hs₀, ?_⟩
    filter_upwards [hj] with x hx hxa
    have hxt := ht x (hx hxa)
    refine ⟨hxt.1, ?_⟩
    rw [map_div₀]
    exact power_law_of_tie (v.ne_zero_iff.mpr (sub_ne_zero.mpr hxa))
      (v.ne_zero_iff.mpr hxt.1) (v.ne_zero_iff.mpr hbj) hpos.le hij.le hxt.2

end SpecialTransformations.Section8
end ScalarSlopeGerm

section UniformSlopeGerm

/-! One finite bound on the numerator and denominator works for the
whole tuple-valued family on its good locus. -/

set_option backward.isDefEq.respectTransparency false

open Filter Topology FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace SpecialTransformations.Section8

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {k m : ℕ}
variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ] [Valued (VFType (M := M)) Γ]

private theorem good_point_close_values
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) (hm : 0 < m)
    (f : (Fin k → VFType (M := M)) → (Fin 1 → VFType (M := M)) → (Fin m → VFType (M := M)))
    (b : Fin k → VFType (M := M)) (a : VFType (M := M))
    (ha : Sum.elim (vfValues b) (vfValues ![a]) ∈ unaryGoodLocus f)
    (r s : VFType (M := M)) (hr : r ≠ 0) (hs : s ≠ 0) :
    ∃ x, x ≠ a ∧ Valued.v (x - a) < Valued.v r ∧
      Valued.v (centeredUnaryFamily Valued.v hm f (Fin.snoc b a) x) < Valued.v s := by
  let v : Valuation (VFType (M := M)) Γ := Valued.v
  let z : Fin 1 → VFType (M := M) := ![a]
  have hnot : vfValues z ∉ isolatedInputs (vfGraph (f b)) := by
    have h := ha.2
    change vfValues z ∉ isolatedInputs {w | Sum.elim (vfValues b) w ∈ unaryFamilyGraph f} at h
    rwa [unaryFamilyGraph_fibre] at h
  have hex : ¬ ∀ w : Fin 1 → VFType (M := M),
      vfValues w ∈ uniformBall (vfValues z) r.val →
      vfValues (f b w) ∈ uniformBall (vfValues (f b z)) s.val → w = z := by
    intro h
    exact hnot ((mem_isolatedInputs_iff (f b) z).mpr ⟨r, s, hr, hs, h⟩)
  push_neg at hex
  obtain ⟨w, hw, hfw, hne⟩ := hex
  have hx : w 0 ≠ a := by
    intro he
    apply hne
    funext i
    fin_cases i
    exact he
  have hw' : ![w 0] = w := funext (fun i => by fin_cases i; rfl)
  have hin := (mem_uniformBall_iff v hv z w r hr).mp hw 0
  have hout := (mem_uniformBall_iff v hv (f b z) (f b w) s hs).mp hfw
  refine ⟨w 0, hx, hin, ?_⟩
  rw [centeredUnaryFamily, Fin.init_snoc, Fin.snoc_last, hw']
  exact hout (dominantIndex v (f b w - f b z) hm)

theorem unary_family_uniform_positive_power_germ (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    {S : Set M} (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) (hm : 0 < m)
    (f : (Fin k → VFType (M := M)) → (Fin 1 → VFType (M := M)) → (Fin m → VFType (M := M)))
    (hf : S.Definable LRV (unaryFamilyGraph f)) :
    ∃ N D : ℕ, ∀ (b : Fin k → VFType (M := M)) (a : VFType (M := M)),
      Sum.elim (vfValues b) (vfValues ![a]) ∈ unaryGoodLocus f →
      (∀ᶠ x in 𝓝 a, f b ![x] = f b ![a]) ∨
      ∃ p q : ℕ, 0 < p ∧ p ≤ N ∧ 0 < q ∧ q ≤ D ∧
        ∃ s : VFType (M := M), s ≠ 0 ∧
          let g := centeredUnaryFamily Valued.v hm f (Fin.snoc b a)
          ∀ᶠ x in 𝓝 a, x ≠ a → g x ≠ 0 ∧
            Valued.v (g x) ^ q = Valued.v s * Valued.v (x - a) ^ p := by
  let v : Valuation (VFType (M := M)) Γ := Valued.v
  let g := centeredUnaryFamily v hm f
  have hg := centeredUnaryFamily_definable v hv hm hf
  obtain ⟨T, hT⟩ := unary_family_has_finite_polynomial_shapes hc hκ hs hsmall g hg
  refine ⟨T.sup (fun D => D.sup Prod.fst), T.sup (fun D => D.sup Prod.snd), fun b a ha => ?_⟩
  let u : Fin (k + 1) → VFType (M := M) := Fin.snoc b a
  obtain ⟨D, hD, c, hnonzero, hpoly⟩ := hT u
  have hu := unaryScalarFamilyGraph_fibre_definable hg u
  rcases scalar_eventually_zero_or_positive_power hc hv hu D c hnonzero hpoly a
    (good_point_close_values hv hm f b a ha) with hzero | hpower
  · left
    filter_upwards [hzero] with x hx
    by_cases hxa : x = a
    · rw [hxa]
    · funext i
      have hle : v (f b ![x] i - f b ![a] i) ≤ v (g u x) := by
        dsimp only [g, u, centeredUnaryFamily]
        rw [Fin.init_snoc, Fin.snoc_last]
        exact value_le_dominantCoordinate v (f b ![x] - f b ![a]) hm i
      have hzero' : g u x = 0 := hx hxa
      rw [hzero', map_zero] at hle
      by_contra hn
      exact (v.ne_zero_iff.mpr (sub_ne_zero.mpr hn)) (le_antisymm hle zero_le)
  · obtain ⟨p, q, hp, hp', hq, hq', s, hs', h⟩ := hpower
    exact Or.inr ⟨p, q, hp, hp'.trans (Finset.le_sup hD), hq, hq'.trans (Finset.le_sup hD), s, hs', h⟩

end SpecialTransformations.Section8
end UniformSlopeGerm
