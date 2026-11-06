import Section4.GammaRVLastRow
import Section3.AlgebraicFinite
import Section3.SmallFiniteParameters
import Section3.GammaSpecialization

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {g r : ℕ}

theorem rvLastValueRow_real_definable
    (Q : Relation S g (r + 1) (fun _ => .rv)) (j : Fin g)
    (γ : Fin g → Values.Gamma (M := M)) (b : Fin r → M) :
    DefinableAt ((S ∪ Set.range (rawTuple (representatives γ))) ∪ Set.range b) .rv
      {x | SameScalar x (rawTuple (representatives γ) j) ∧
        (rawTuple (representatives γ), Fin.snoc b x) ∈ Q.carrier} := by
  let X := {x | SameScalar x (rawTuple (representatives γ) j) ∧
    (rawTuple (representatives γ), Fin.snoc b x) ∈ Q.carrier}
  have hw : DefinableWith (S ∪ Set.range b) γ (fun _ : Fin 1 => .rv) {z | z 0 ∈ X} :=
    ⟨rvLastValueRow Q j b, by ext z; rfl⟩
  have hs := hw.specialize (representatives γ) (representatives_values γ)
  have he : (S ∪ Set.range b) ∪ Set.range (rawTuple (representatives γ)) =
      (S ∪ Set.range (rawTuple (representatives γ))) ∪ Set.range b := by
    ext x
    simp only [Set.mem_union]
    tauto
  rw [he] at hs
  exact ⟨hs, fun _ hx => hx.1.1.1⟩

/-- Genuine saturation ensures that an infinite row contains a point
outside algebraic closure of the same small real base. The Gamma codes
are displayed only in this auxiliary choice step. -/
theorem rvInfiniteLast_exists_nonalgebraic
    (hcan : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hsmall : Cardinal.mk S < κ)
    (Q : Relation S g (r + 1) (fun _ => .rv)) (j : Fin g)
    (γ : Fin g → Values.Gamma (M := M)) (b : Fin r → M)
    (hb : b ∈ (rvInfiniteLast hcan h00 hs hsmall Q j).fibre γ) :
    ∃ x : CanonicalRV.RVSort M,
      SameScalar x.val (rawTuple (representatives γ) j) ∧
      Fin.snoc b x.val ∈ Q.fibre γ ∧
      ¬ AlgebraicAt ((S ∪ Set.range (rawTuple (representatives γ))) ∪ Set.range b) .rv x.val := by
  let T := (S ∪ Set.range (rawTuple (representatives γ))) ∪ Set.range b
  let X := {x | SameScalar x (rawTuple (representatives γ) j) ∧
    (rawTuple (representatives γ), Fin.snoc b x) ∈ Q.carrier}
  have hT : Cardinal.mk T < κ := small_union_range hκ _
    (small_union_range hκ S hsmall (rawTuple (representatives γ))) b
  have hXd : DefinableAt T .rv X := rvLastValueRow_real_definable Q j γ b
  have hinf : X.Infinite := hb
  have hnot : ¬ ∀ x ∈ X, AlgebraicAt T .rv x := by
    intro h
    exact hinf (RawClosure.finite_of_definable_subset_algebraic hs T hT X hXd.raw_definable
      (fun x hx => (h x hx).raw_finite_witness))
  push_neg at hnot
  obtain ⟨x, hx, hx0⟩ := hnot
  exact ⟨⟨x, hx.1.1.1⟩, hx.1, hx.2, hx0⟩

end SpecialTransformations.Section4

end
