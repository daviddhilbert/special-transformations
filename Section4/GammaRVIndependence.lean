module

public import Section4.RVSequenceIndependence
public import Section4.RVDimensionRank
public import Section3.GammaParameters
public import Section3.SmallFiniteParameters

@[expose] public section

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- Accepted Section 3 input (the Gamma half of 3.7, with finite formula
support): Gamma names do not enlarge RV algebraic closure over a small
real base. This is an explicit theorem hypothesis, not a custom axiom. -/
def GammaRVAlgebraicityInput (κ : Cardinal) : Prop :=
  ∀ B : Base (M := M), Cardinal.mk B.real < κ → ∀ b : M,
    AlgebraicAtBase B .rv b ↔ AlgebraicAt B.real .rv b

def GammaRVSequenceIndependent (B : Base (M := M)) :
    {n : ℕ} → (Fin n → CanonicalRV.RVSort M) → Prop
  | 0, _ => True
  | n + 1, t => GammaRVSequenceIndependent B (Fin.init t) ∧
      ¬ AlgebraicAtBase ⟨B.real ∪ Set.range (rvValues (Fin.init t)), B.gamma⟩
        .rv (t (Fin.last n)).val

/-- The accepted Gamma half of 3.7 applies at every stage of an RV
independent sequence, with its finite earlier real coordinates retained. -/
theorem gammaRVSequenceIndependent_iff {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hγ : GammaRVAlgebraicityInput (M := M) κ)
    (B : Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    {n : ℕ} (t : Fin n → CanonicalRV.RVSort M) :
    GammaRVSequenceIndependent B t ↔ RVSequenceIndependent B.real t := by
  induction n with
  | zero => exact Iff.rfl
  | succ n ih =>
    change (GammaRVSequenceIndependent B (Fin.init t) ∧ ¬ AlgebraicAtBase
      ⟨B.real ∪ Set.range (rvValues (Fin.init t)), B.gamma⟩ .rv (t (Fin.last n)).val) ↔
      (RVSequenceIndependent B.real (Fin.init t) ∧ ¬ AlgebraicAt
        (B.real ∪ Set.range (rvValues (Fin.init t))) .rv (t (Fin.last n)).val)
    rw [ih]
    exact and_congr Iff.rfl (not_congr (hγ
      ⟨B.real ∪ Set.range (rvValues (Fin.init t)), B.gamma⟩
      (small_union_range hκ B.real hsmall (rvValues (Fin.init t))) _))

/-- A maximal-rank RV point supplies an independent selected subsequence
that stays independent over every collection of actual Gamma names. -/
theorem exists_maximum_rv_sequence_independent_gamma
    (hcan : CanonicalStructure.IsCanonical (M := M)) (hex : RVExchangeInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hγ : GammaRVAlgebraicityInput (M := M) κ) {S : Set M} (hsmall : Cardinal.mk S < κ)
    {n : ℕ} (A : DefinableGeometry.DefSet (rawRVSpace (M := M) n) S)
    (hne : A.carrier.Nonempty) :
    ∃ a : A, ∃ d : ℕ, d = rvDim A ∧ ∃ v : Fin d → Fin n,
      ∀ G : Set (Values.Gamma (M := M)), GammaRVSequenceIndependent ⟨S, G⟩ (a.val ∘ v) := by
  obtain ⟨a, ha⟩ := exists_point_of_maximum_rv_rank hcan hex hs hsmall A hne
  obtain ⟨v, hv, hvinj, hI, hspan⟩ := exists_rv_coordinate_basis_independent hcan hex S a.val
  have hseq := (rvSequenceIndependent_iff hcan hex S (a.val ∘ v)).mpr ⟨hvinj, hI⟩
  refine ⟨a, rvTupleRank hcan hex S a.val, ha, v, ?_⟩
  intro G
  exact (gammaRVSequenceIndependent_iff hκ hγ ⟨S, G⟩ hsmall _).mpr hseq

end SpecialTransformations.Section4

end
