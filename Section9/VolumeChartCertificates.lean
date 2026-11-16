module

public import Section9.ResidueChartInterpretation
public import Section9.ResidueChartCertificateLogic
public import Section9.UniformRVScaling

@[expose] public section

/-! A fixed polynomial support gives a definable family of valid
charts over all scales. The polynomial coefficients are quantified
residue-field variables. -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000

open FirstOrder FirstOrder.Language MvPolynomial
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section4.ResiduePurity SpecialTransformations.Section7
open SpecialTransformations.DefinableGeometry

namespace SpecialTransformations.Section9

structure VolumeChartSupport (n : ℕ) where
  equationsSize : ℕ
  openSize : ℕ
  cutSize : ℕ
  equations : Fin equationsSize → Fin (n + n) →₀ ℕ
  extraOpen : Fin openSize → Fin (n + n) →₀ ℕ
  inputCut : Fin cutSize → Fin n →₀ ℕ

abbrev VolumeChartSupport.Index {n : ℕ} (σ : VolumeChartSupport n) :=
  ChartCoefficientIndex n σ.equationsSize σ.openSize σ.cutSize

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ} {S : Set M}
local notation "RV" => CanonicalRV.RVSort M
local notation "k" => ModelResidue M
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

def rawVolumeNormalized (C : DefSet (rawRVSpace (M := M) (n + n)) S) :
    Set (Fin (n + n) ⊕ Fin (n + n) → M) :=
  (rawRVSpace (M := M) (n + n)).relation (rawRVSpace (M := M) (n + n))
    (fun a r => (fun i => a i * r i) ∈ C.carrier) ∩
    {w | w ∘ Sum.inr ∈ rawResidueImage {z : Fin (n + n) → k | ∀ i, z i ≠ 0}}

theorem rawVolumeNormalized_definable (hc : CanonicalStructure.IsCanonical (M := M))
    (C : DefSet (rawRVSpace (M := M) (n + n)) S) : S.Definable LRV (rawVolumeNormalized C) := by
  let E := residueDefinableField S
  have h : Relative.Def E {z : Fin (n + n) → k | ∀ i, z i ≠ 0} := by
    rw [Set.ofPred_forall]
    exact Set.definable_iInter_of_finite fun i =>
      ((Relative.projection (E := E) i).eq_const 0 E.zero_mem).compl
  have hrel : S.Definable LRV ((rawRVSpace (M := M) (n + n)).relation
      (rawRVSpace (M := M) (n + n)) (fun a r => (fun i => a i * r i) ∈ C.carrier)) :=
    normalizedCorrespondence_relation_definable S C
  exact hrel.inter
    ((residueFieldImage_indexed_definable hc E S le_rfl _ h).preimage_comp Sum.inr)

theorem mem_rawVolumeNormalized (C : DefSet (rawRVSpace (M := M) (n + n)) S)
    (a b : Fin n → RV) (z : Fin (n + n) → k) :
    Sum.elim (rvValues (productTuple a b)) (residueRaw ∘ z) ∈ rawVolumeNormalized C ↔
      z ∈ normalizedCorrespondence C.carrier a b := by
  let Q := rawRVSpace (M := M) (n+n)
  let a₀ : Q.domain := ⟨rvValues (productTuple a b), ⟨productTuple a b, rfl⟩⟩
  let z₀ : Q.domain := ⟨residueRaw ∘ z, ⟨residueRV ∘ z, rfl⟩⟩
  change (Sum.elim a₀.val z₀.val ∈ Q.relation Q (fun a r => (fun i => a i * r i) ∈ C.carrier) ∧
    (residueRaw ∘ z) ∈ rawResidueImage {z : Fin (n+n) → k | ∀ i, z i ≠ 0}) ↔ _
  have hrel : Sum.elim a₀.val z₀.val ∈ Q.relation Q
      (fun a r => (fun i => a i * r i) ∈ C.carrier) ↔ residueScale (productTuple a b) z ∈ C.carrier := by
    rw [Q.relation_decode Q _ a₀ z₀]
    have ha : Q.decode a₀ = productTuple a b := decode_rvValues _
    have hz : Q.decode z₀ = residueRV ∘ z := decode_rvValues _
    exact Iff.of_eq (congrArg₂ (fun (a r : Q.Carrier) => (fun i => a i * r i) ∈ C.carrier) ha hz)
  exact hrel.and (mem_rawResidueImage_iff _ z)

variable (σ : VolumeChartSupport n)

public def chartEquationsTest : Set (σ.Index ⊕ Fin (n + n) → k) :=
  {w | ∀ i, (chartEquation σ.equations (w ∘ Sum.inl) i).eval (w ∘ Sum.inr) = 0}

public def chartOpenTest : Set (σ.Index ⊕ Fin (n + n) → k) :=
  {w | (chartDerivativeBlock σ.equations (productRight n n) w).det *
    (chartExtraOpen σ.extraOpen (w ∘ Sum.inl)).eval (w ∘ Sum.inr) ≠ 0}

public def chartCutTest : Set (σ.Index ⊕ Fin (n + n) → k) :=
  {w | (chartInputCut σ.inputCut (w ∘ Sum.inl)).eval (w ∘ Sum.inr ∘ productLeft n n) ≠ 0}

public def chartInputDerivativeTest : Set (σ.Index ⊕ Fin (n + n) → k) :=
  {w | (chartDerivativeBlock σ.equations (productLeft n n) w).det ≠ 0}

def rawVolumeChart (C : DefSet (rawRVSpace (M := M) (n + n)) S) :
    Set (Fin (n + n) ⊕ σ.Index → M) :=
  rawResidueChartCertificate (rawVolumeNormalized C) (rawResidueImage Set.univ)
    (rawResidueImage (chartEquationsTest (M := M) σ)) (rawResidueImage (chartOpenTest (M := M) σ))
    (rawResidueImage (chartCutTest (M := M) σ)) (rawResidueImage (chartInputDerivativeTest (M := M) σ))

theorem rawVolumeChart_definable (hc : CanonicalStructure.IsCanonical (M := M))
    (C : DefSet (rawRVSpace (M := M) (n + n)) S) : S.Definable LRV (rawVolumeChart σ C) := by
  let E := residueDefinableField S
  obtain ⟨hP, hQ, hD, hR, _⟩ := relative_chart_arithmetic E σ.equations σ.extraOpen σ.inputCut
  apply rawResidueChartCertificate_definable (rawVolumeNormalized_definable hc C)
  · exact residueFieldImage_indexed_definable hc E S le_rfl _ Set.definable_univ
  · exact residueFieldImage_indexed_definable hc E S le_rfl _ hP
  · exact residueFieldImage_indexed_definable hc E S le_rfl _ (hQ.eq_const 0 E.zero_mem).compl
  · exact residueFieldImage_indexed_definable hc E S le_rfl _ (hD.eq_const 0 E.zero_mem).compl
  · exact residueFieldImage_indexed_definable hc E S le_rfl _ (hR.eq_const 0 E.zero_mem).compl

def rawVolumeChartScales (C : DefSet (rawRVSpace (M := M) (n + n)) S) :
    Set (Fin (n + n) → M) :=
  {a | ∃ c : σ.Index → M, Sum.elim a c ∈ rawVolumeChart σ C}

theorem rawVolumeChartScales_definable (hc : CanonicalStructure.IsCanonical (M := M))
    (C : DefSet (rawRVSpace (M := M) (n + n)) S) : S.Definable LRV (rawVolumeChartScales σ C) :=
  (rawVolumeChart_definable σ hc C).exists_of_finite

structure IsVolumeChart (C : Set (Fin (n + n) → RV)) (a b : Fin n → RV) (c : σ.Index → k) : Prop where
  cut_nonempty : ∃ z : Fin (n + n) → k, Sum.elim c z ∈ chartCutTest (M := M) σ
  equations : ∀ z ∈ normalizedCorrespondence C a b, Sum.elim c z ∈ chartEquationsTest (M := M) σ
  contains : ∀ z : Fin (n + n) → k, Sum.elim c z ∈ chartEquationsTest (M := M) σ →
    Sum.elim c z ∈ chartOpenTest (M := M) σ → z ∈ normalizedCorrespondence C a b
  covers : ∀ z ∈ normalizedCorrespondence C a b, Sum.elim c z ∈ chartCutTest (M := M) σ →
    Sum.elim c z ∈ chartOpenTest (M := M) σ ∧ Sum.elim c z ∈ chartInputDerivativeTest (M := M) σ

private theorem rawResidueImage_right_witness {β γ : Type}
    {A : Set (β ⊕ γ → k)} {c : β → M} {z : γ → M}
    (h : Sum.elim c z ∈ rawResidueImage A) : ∃ y : γ → k, residueRaw ∘ y = z := by
  obtain ⟨w, _, hw⟩ := h
  exact ⟨w ∘ Sum.inr, funext fun i => congrFun hw (.inr i)⟩

theorem mem_rawVolumeChart_iff (C : DefSet (rawRVSpace (M := M) (n + n)) S)
    (a b : Fin n → RV) (c : σ.Index → k) :
    Sum.elim (rvValues (productTuple a b)) (residueRaw ∘ c) ∈ rawVolumeChart σ C ↔
      IsVolumeChart σ C.carrier a b c := by
  let v := rvValues (productTuple a b)
  let u := residueRaw ∘ c
  have hTest (A : Set (σ.Index ⊕ Fin (n + n) → k)) (z : Fin (n + n) → k) :
      Sum.elim u (residueRaw ∘ z) ∈ rawResidueImage A ↔ Sum.elim c z ∈ A := by
    have he : Sum.elim u (residueRaw ∘ z) = residueRaw ∘ Sum.elim c z := by
      funext i
      cases i <;> rfl
    rw [he]
    exact mem_rawResidueImage_iff A _
  constructor
  · rintro ⟨_, ⟨z₀, h₀⟩, h⟩
    obtain ⟨z, rfl⟩ := rawResidueImage_right_witness h₀
    refine ⟨⟨z, (hTest _ z).mp h₀⟩, ?_, ?_, ?_⟩
    · intro z hz
      exact (hTest _ z).mp ((h (residueRaw ∘ z)).1 ((mem_rawVolumeNormalized C a b z).mpr hz)).1
    · intro z hP hQ
      exact (mem_rawVolumeNormalized C a b z).mp
        ((h (residueRaw ∘ z)).2 ⟨(hTest _ z).mpr hP, (hTest _ z).mpr hQ⟩)
    · intro z hz hD
      obtain ⟨hQ, hR⟩ := ((h (residueRaw ∘ z)).1 ((mem_rawVolumeNormalized C a b z).mpr hz)).2
        ((hTest _ z).mpr hD)
      exact ⟨(hTest _ z).mp hQ, (hTest _ z).mp hR⟩
  · intro h
    obtain ⟨z₀, h₀⟩ := h.cut_nonempty
    refine ⟨⟨c, Set.mem_univ _, rfl⟩, ⟨residueRaw ∘ z₀, (hTest _ z₀).mpr h₀⟩, fun z => ⟨?_, ?_⟩⟩
    · intro hz
      obtain ⟨r, _, hr⟩ := hz.2
      change residueRaw ∘ r = z at hr
      subst z
      have hp := (mem_rawVolumeNormalized C a b r).mp hz
      refine ⟨(hTest _ r).mpr (h.equations r hp), fun hD => ?_⟩
      obtain ⟨hQ, hR⟩ := h.covers r hp ((hTest _ r).mp hD)
      exact ⟨(hTest _ r).mpr hQ, (hTest _ r).mpr hR⟩
    · rintro ⟨hP, hQ⟩
      obtain ⟨r, rfl⟩ := rawResidueImage_right_witness hP
      exact (mem_rawVolumeNormalized C a b r).mpr (h.contains r ((hTest _ r).mp hP) ((hTest _ r).mp hQ))

theorem mem_rawVolumeChartScales_iff (C : DefSet (rawRVSpace (M := M) (n + n)) S)
    (a b : Fin n → RV) :
    rvValues (productTuple a b) ∈ rawVolumeChartScales σ C ↔
      ∃ c : σ.Index → k, IsVolumeChart σ C.carrier a b c := by
  constructor
  · rintro ⟨u, hu⟩
    obtain ⟨c, _, hcode⟩ := hu.1
    change residueRaw ∘ c = u at hcode
    rw [← hcode] at hu
    exact ⟨c, (mem_rawVolumeChart_iff σ C a b c).mp hu⟩
  · rintro ⟨c, hc⟩
    exact ⟨residueRaw ∘ c, (mem_rawVolumeChart_iff σ C a b c).mpr hc⟩

theorem chartDerivativeBlock_eq (s : Fin n → Fin (n + n)) (c : σ.Index → k) (z : Fin (n + n) → k) :
    chartDerivativeBlock σ.equations s (Sum.elim c z) =
      Matrix.of (fun i j => (pderiv (s j) (chartEquation σ.equations c i)).eval z) := by
  apply Matrix.ext
  intro i j
  rfl

theorem isVolumeChart_iff (C : Set (Fin (n + n) → RV)) (a b : Fin n → RV) (c : σ.Index → k) :
    let P := chartEquation σ.equations c
    let T := chartExtraOpen σ.extraOpen c
    let D := chartInputCut σ.inputCut c
    let A (z : Fin (n + n) → k) := (Matrix.of fun i j => (pderiv (productRight n n j) (P i)).eval z).det
    let B (z : Fin (n + n) → k) := (Matrix.of fun i j => (pderiv (productLeft n n j) (P i)).eval z).det
    let W := normalizedCorrespondence C a b
    IsVolumeChart σ C a b c ↔
      (∃ z : Fin (n + n) → k, D.eval (z ∘ productLeft n n) ≠ 0) ∧
      (∀ z ∈ W, ∀ i, (P i).eval z = 0) ∧
      (∀ z, (∀ i, (P i).eval z = 0) → A z * T.eval z ≠ 0 → z ∈ W) ∧
      (∀ z ∈ W, D.eval (z ∘ productLeft n n) ≠ 0 → A z * T.eval z ≠ 0 ∧ B z ≠ 0) := by
  dsimp only
  constructor
  · rintro ⟨h₁, h₂, h₃, h₄⟩
    exact ⟨h₁, h₂, h₃, h₄⟩
  · rintro ⟨h₁, h₂, h₃, h₄⟩
    exact ⟨h₁, h₂, h₃, h₄⟩

noncomputable def volumeChartDeterminant (w : σ.Index ⊕ Fin (n + n) → k) : k :=
  (-1 : k)^n * ((chartDerivativeBlock σ.equations (productLeft n n) w).det *
    (chartDerivativeBlock σ.equations (productRight n n) w).det⁻¹)

def rawVolumeChartEvaluation : Set ((σ.Index ⊕ Fin (n + n)) ⊕ Unit → M) :=
  rawResidueImage {w | w ∘ Sum.inl ∈ chartCutTest (M := M) σ ∧
    volumeChartDeterminant σ (w ∘ Sum.inl) = w (.inr ())}

theorem rawVolumeChartEvaluation_definable (hc : CanonicalStructure.IsCanonical (M := M)) :
    S.Definable LRV (rawVolumeChartEvaluation (M := M) σ) := by
  let E := residueDefinableField S
  obtain ⟨_, _, hD, _, hJ⟩ := relative_chart_arithmetic E σ.equations σ.extraOpen σ.inputCut
  apply residueFieldImage_indexed_definable hc E S le_rfl
  exact ((hD.eq_const 0 E.zero_mem).compl.preimage_comp Sum.inl).inter (relative_graph_on_sum E _ hJ)

theorem mem_rawVolumeChartEvaluation_iff (w : σ.Index ⊕ Fin (n + n) → k) (d : k) :
    Sum.elim (residueRaw ∘ w) (fun _ => residueRaw d) ∈ rawVolumeChartEvaluation (M := M) σ ↔
      (chartInputCut σ.inputCut (w ∘ Sum.inl)).eval (w ∘ Sum.inr ∘ productLeft n n) ≠ 0 ∧
        volumeChartDeterminant σ w = d := by
  have h : Sum.elim (residueRaw ∘ w) (fun _ : Unit => residueRaw d) =
      residueRaw ∘ Sum.elim w (fun _ : Unit => d) := by
    funext i
    cases i <;> rfl
  rw [h]
  exact mem_rawResidueImage_iff _ _

end SpecialTransformations.Section9
