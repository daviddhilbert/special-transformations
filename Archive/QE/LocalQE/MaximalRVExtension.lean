import MaximalResidueExtension
import FiniteValueRepresentative

/-! A maximal compatible field map represents the entire prescribed RV domain.
The finite and infinite value-degree cases are exhaustive. No divisibility of
the prescribed RV group and no henselization input are needed. -/

namespace MaximalRVExtension

open scoped IntermediateField
open PartialFieldMaps MaximalResidueExtension ResidueTranscendentalTransport

variable {K L Γ Δ : Type*} [Field K] [Field L]
  [LinearOrderedCommGroupWithZero Γ] [LinearOrderedCommGroupWithZero Δ]

theorem adjoin_generator_mem (P : K → L → Prop) (S : Subring (K × L))
    (hmax : Maximal (Compatible P) S) (e : K)
    (g : (domain S hmax.prop.1)⟮e⟯ →+* L)
    (hb : ∀ a : domain S hmax.prop.1,
      g (algebraMap _ _ a) = fieldMap S hmax.prop.1 a)
    (hg : ∀ x : (domain S hmax.prop.1)⟮e⟯, P (x : K) (g x)) :
    e ∈ domain S hmax.prop.1 := by
  let F := domain S hmax.prop.1
  let T := graph (F⟮e⟯).toSubfield g
  have hT : Compatible P T := compatible_adjoin_graph P F e g hg
  have hST : S ≤ T := by
    rw [← graph_domain_fieldMap S hmax.prop.1]
    exact graph_le_adjoin_graph F (fieldMap S hmax.prop.1) e g hb
  exact ⟨g (IntermediateField.AdjoinSimple.gen F e), hmax.2 hT hST
    ((mem_graph _ _).mpr ⟨IntermediateField.AdjoinSimple.gen F e, rfl, rfl⟩)⟩

variable [IsAlgClosed K] [IsAlgClosed L]

/-- Every source RV class in the prescribed graph has a representative in the
maximal field domain. The graph need only contain all residue units. -/
theorem maximal_represents (v : Valuation K Γ) (w : Valuation L Δ)
    (ρ : Residue v →+* Residue w) (R : RVCalc.RV v → RVCalc.RV w → Prop)
    (h : RVFrame v w ρ R)
    (hfun : ∀ x y z, R x y → R x z → y = z)
    (S : Subring (K × L))
    (hmax : Maximal (Compatible (fun x y => R (RVCalc.rv v x) (RVCalc.rv w y))) S)
    {c : K} {d : L} (hcd : R (RVCalc.rv v c) (RVCalc.rv w d)) :
    ∃ a : domain S hmax.prop.1, RVCalc.rv v (a : K) = RVCalc.rv v c := by
  let F := domain S hmax.prop.1
  let σ : F →+* L := fieldMap S hmax.prop.1
  have hb : ∀ a : F, R (RVCalc.rv v (a : K)) (RVCalc.rv w (σ a)) :=
    fun a => hmax.prop.2 _ _ (fieldMap_mem S hmax.prop.1 a)
  have hu : FiniteValueRepresentative.UnitClassesInBase v F := by
    intro x hx
    obtain ⟨a, _, ha⟩ := maximal_has_unit_representatives_of_frame v w ρ R h S hmax x hx
    exact ⟨a, ha⟩
  by_cases hc : c = 0
  · exact ⟨0, by simp [hc]⟩
  by_cases hfinite : ∃ n : ℕ, 0 < n ∧ ∃ a : F, (v c) ^ n = v (a : K)
  · obtain ⟨n, a, e, hn, he, hep, her, hgap⟩ :=
      FiniteValueRepresentative.exists_minimal_representative v F hu hc hfinite
    have hed : R (RVCalc.rv v e) (RVCalc.rv w d) := by rw [her]; exact hcd
    obtain ⟨_, g, _, _, _, hgb, _, hgr⟩ :=
      ValueAlgebraicTransport.exists_field_embedding_of_rv_root v w F σ R
        h.zero h.mul hfun hb he hn hed h.order hgap a hep
    exact ⟨⟨e, adjoin_generator_mem _ S hmax e g hgb hgr⟩, her⟩
  · have ht : ValueTranscendentalTransport.ValueTranscendental v F c := by
      intro n hn a ha
      exact hfinite ⟨n, hn, a, ha⟩
    have hd : d ≠ 0 := by
      intro hz
      have hh := h.order _ _ _ _ hcd h.zero
      simp only [RVCalc.vrv_rv, RVCalc.vrv_none, hz, map_zero] at hh
      exact hc ((Valuation.zero_iff v).mp (le_antisymm (hh.mpr le_rfl) zero_le))
    obtain ⟨g, _, hgb, _, hgr⟩ :=
      ValueTranscendentalTransport.exists_field_embedding v w F σ R
        h.zero h.mul h.inv hb hc hd hcd
        (ValueTranscendentalTransport.separated_of_valueTranscendental v F hc ht)
        (ValueTranscendentalTransport.monomialCutCompatible_of_rvOrder v w F σ R
          h.mul hb hcd h.order)
    exact ⟨⟨c, adjoin_generator_mem _ S hmax c g hgb hgr⟩, rfl⟩

/-- Assemble all local extensions into one actual field map. Every prescribed
RV pair is realized by an element of the enlarged field and its image. -/
theorem exists_field_representing_graph (v : Valuation K Γ) (w : Valuation L Δ)
    (ρ : Residue v →+* Residue w) (R : RVCalc.RV v → RVCalc.RV w → Prop)
    (h : RVFrame v w ρ R)
    (hfun : ∀ x y z, R x y → R x z → y = z)
    (F : Subfield K) (σ : F →+* L)
    (hbase : ∀ a : F, R (RVCalc.rv v (a : K)) (RVCalc.rv w (σ a))) :
    ∃ (E : Subfield K) (hFE : F ≤ E) (τ : E →+* L),
      (∀ a : F, τ ⟨(a : K), hFE a.2⟩ = σ a) ∧
      (∀ a : E, R (RVCalc.rv v (a : K)) (RVCalc.rv w (τ a))) ∧
      (∀ (c : K) (d : L), R (RVCalc.rv v c) (RVCalc.rv w d) →
        ∃ a : E, RVCalc.rv v (a : K) = RVCalc.rv v c ∧
          RVCalc.rv w (τ a) = RVCalc.rv w d) := by
  have hS : Compatible (fun x y => R (RVCalc.rv v x) (RVCalc.rv w y)) (graph F σ) := by
    refine ⟨isFieldGraph_graph F σ, ?_⟩
    intro x y hxy
    obtain ⟨a, rfl, rfl⟩ := (mem_graph F σ).mp hxy
    exact hbase a
  obtain ⟨T, hST, hmax⟩ := exists_maximal_extension _ (graph F σ) hS
  let E := domain T hmax.prop.1
  have hFE : F ≤ E := by
    intro x hx
    exact ⟨σ ⟨x, hx⟩, hST ((mem_graph F σ).mpr ⟨⟨x, hx⟩, rfl, rfl⟩)⟩
  refine ⟨E, hFE, fieldMap T hmax.prop.1, ?_, ?_, ?_⟩
  · intro a
    exact fieldMap_eq T hmax.prop.1 _ (hST ((mem_graph F σ).mpr ⟨a, rfl, rfl⟩))
  · intro a
    exact hmax.prop.2 _ _ (fieldMap_mem T hmax.prop.1 a)
  · intro c d hcd
    obtain ⟨a, ha⟩ := maximal_represents v w ρ R h hfun T hmax hcd
    refine ⟨a, ha, ?_⟩
    have hh := hmax.prop.2 _ _ (fieldMap_mem T hmax.prop.1 a)
    change R (RVCalc.rv v (a : K)) (RVCalc.rv w (fieldMap T hmax.prop.1 a)) at hh
    rw [ha] at hh
    exact hfun _ _ _ hh hcd

end MaximalRVExtension

#print axioms MaximalRVExtension.adjoin_generator_mem
#print axioms MaximalRVExtension.maximal_represents
#print axioms MaximalRVExtension.exists_field_representing_graph
