import Mathlib.ModelTheory.Satisfiability
import Mathlib.Tactic.Push

/-! The compactness step needed to turn local syntactic preparation
certificates into a model-uniform finite disjunction. This is an ordinary
first-order compactness lemma, with no valued-field or relative-QE input.
The actual certificate cover must still be established by the geometric
and syntactic construction. -/

noncomputable section
open Classical FirstOrder FirstOrder.Language

namespace SpecialTransformations.Section6

/-- A sentence cover of all models of T has a finite subcover. -/
theorem finite_sentence_cover {L : Language.{0, 0}} {ι : Type}
    (T : L.Theory) (θ : ι → L.Sentence)
    (hcover : ∀ M : T.ModelType.{0, 0, 0}, ∃ i, (θ i).Realize (M := M)) :
    ∃ s : Finset ι, ∀ M : T.ModelType.{0, 0, 0}, ∃ i ∈ s, (θ i).Realize (M := M) := by
  by_contra hfin
  push Not at hfin
  let U : L.Theory := T ∪ Set.range (fun i => (θ i).not)
  have hU : U.IsFinitelySatisfiable := by
    intro Δ hΔ
    let extra : Finset L.Sentence := Δ.filter (fun σ => σ ∉ T)
    have hextra : ∀ σ : extra, ∃ i, (θ i).not = σ.val := by
      intro σ
      have hs := Finset.mem_filter.mp σ.property
      obtain hT | ⟨i, hi⟩ := hΔ hs.1
      · exact (hs.2 hT).elim
      · exact ⟨i, hi⟩
    choose pick hpick using hextra
    let s : Finset ι := Finset.univ.image pick
    obtain ⟨M, hM⟩ := hfin s
    have hModel : M ⊨ (Δ : L.Theory) := by
      constructor
      intro σ hσ
      by_cases hσT : σ ∈ T
      · exact Theory.realize_sentence_of_mem T hσT
      · let σ' : extra := ⟨σ, Finset.mem_filter.mpr ⟨hσ, hσT⟩⟩
        have hi : pick σ' ∈ s := Finset.mem_image.mpr ⟨σ', Finset.mem_univ _, rfl⟩
        rw [← (show (θ (pick σ')).not = σ from hpick σ')]
        exact hM (pick σ') hi
    letI := hModel
    exact Theory.Model.isSatisfiable M
  obtain ⟨N⟩ := (Theory.isSatisfiable_iff_isFinitelySatisfiable).mpr hU
  have hNT : N ⊨ T := N.is_model.mono Set.subset_union_left
  letI := hNT
  obtain ⟨i, hi⟩ := hcover (Theory.ModelType.of T N)
  have hn : (N : Type) ⊨ (θ i).not := Theory.realize_sentence_of_mem U
    (show (θ i).not ∈ U from Set.mem_union_right _ ⟨i, rfl⟩)
  exact hn hi

/-- Parameter-uniform compactness. The finite subcover is chosen before
a model and before its free assignment, by naming those variables as
constants. No completeness of T is required. -/
theorem finite_formula_cover {L : Language.{0, 0}} {ι α : Type}
    (T : L.Theory) (θ : ι → L.Formula α)
    (hcover : ∀ M : T.ModelType.{0, 0, 0}, ∀ v : α → M, ∃ i, (θ i).Realize v) :
    ∃ s : Finset ι, ∀ M : T.ModelType.{0, 0, 0}, ∀ v : α → M,
      ∃ i ∈ s, (θ i).Realize v := by
  let T' := (L.lhomWithConstants α).onTheory T
  have h' : ∀ M : T'.ModelType.{0, 0, 0}, ∃ i, (Formula.equivSentence (θ i)).Realize (M := M) := by
    intro M
    letI := (L.lhomWithConstants α).reduct M
    haveI : M ⊨ T := (LHom.onTheory_model _ _).mp M.is_model
    obtain ⟨i, hi⟩ := hcover (Theory.ModelType.of T M) (fun a => (L.con a : M))
    exact ⟨i, (Formula.realize_equivSentence M (θ i)).mpr hi⟩
  obtain ⟨s, hs⟩ := finite_sentence_cover T' (fun i => Formula.equivSentence (θ i)) h'
  refine ⟨s, ?_⟩
  intro M v
  letI : (constantsOn α).Structure M := constantsOn.structure v
  haveI : M ⊨ T' := (LHom.onTheory_model _ _).mpr M.is_model
  obtain ⟨i, hi, hθ⟩ := hs (Theory.ModelType.of T' M)
  exact ⟨i, hi, (Formula.realize_equivSentence M (θ i)).mp hθ⟩

/-- The actual formula assembly in the compactness step. The hypotheses
are a cover by local guards and checked local equivalences; establishing
those from preparation is a separate obligation, not a QE axiom. -/
theorem uniform_of_local_certificates {L : Language.{0, 0}} {ι α : Type}
    (T : L.Theory) (φ : L.Formula α) (θ ψ : ι → L.Formula α)
    (hcover : ∀ M : T.ModelType.{0, 0, 0}, ∀ v : α → M, ∃ i, (θ i).Realize v)
    (hcorrect : ∀ i, ∀ M : T.ModelType.{0, 0, 0}, ∀ v : α → M,
      (θ i).Realize v → (φ.Realize v ↔ (ψ i).Realize v)) :
    ∃ s : Finset ι, ∀ M : T.ModelType.{0, 0, 0}, ∀ v : α → M,
      φ.Realize v ↔ (Formula.iSup (fun i : s => θ i.val ⊓ ψ i.val)).Realize v := by
  obtain ⟨s, hs⟩ := finite_formula_cover T θ hcover
  refine ⟨s, ?_⟩
  intro M v
  rw [Formula.realize_iSup]
  simp only [Formula.realize_inf]
  constructor
  · intro hφ
    obtain ⟨i, hi, hθ⟩ := hs M v
    exact ⟨⟨i, hi⟩, hθ, (hcorrect i M v hθ).mp hφ⟩
  · rintro ⟨i, hθ, hψ⟩
    exact (hcorrect i.val M v hθ).mpr hψ

end SpecialTransformations.Section6
