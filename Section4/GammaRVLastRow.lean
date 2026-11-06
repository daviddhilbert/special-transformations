import Section4.GammaRVInfiniteProjection
import Section4.GammaRVIndependence
import Section3.GammaSupport

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {g r : ℕ}

/-- A real-coordinate fibre with its fixed value class, retaining genuine
Gamma names and naming only the earlier real coordinates. -/
def rvLastValueRow (Q : Relation S g (r + 1) (fun _ => .rv))
    (j : Fin g) (b : Fin r → M) :
    Relation (S ∪ Set.range b) g 1 (fun _ => .rv) where
  carrier := {p | SameScalar (p.2 0) (p.1 j) ∧ (p.1, Fin.snoc b (p.2 0)) ∈ Q.carrier}
  definable := by
    have hq0 := Q.definable
    let T := S ∪ Set.range b
    let N := CanonicalStructure.normalize (M := M)
    letI := sM
    have hQ : @Set.Definable M T LRV N (Fin g ⊕ Fin (r + 1))
        {z | (z ∘ Sum.inl, z ∘ Sum.inr) ∈ Q.carrier} := by
      letI := N
      exact hq0.mono (Set.subset_union_left : S ⊆ T)
    let F (z : Fin g ⊕ Fin 1 → M) : Fin g ⊕ Fin (r + 1) → M :=
      Sum.elim (z ∘ Sum.inl) (Fin.snoc b (z (.inr 0)))
    have hF : @Set.DefinableMap M LRV N (Fin g ⊕ Fin 1) (Fin g ⊕ Fin (r + 1)) T F := by
      letI := N
      intro i
      cases i with
      | inl i => exact Set.DefinableFun.proj LRV
      | inr i =>
        refine Fin.lastCases ?_ (fun q => ?_) i
        · simpa only [F, Sum.elim_inr, Fin.snoc_last] using
            (Set.DefinableFun.proj (L := LRV) (A := T) (i := Sum.inr 0))
        · simpa only [F, Sum.elim_inr, Fin.snoc_castSucc] using
            (LRV.definableFun_const (Fin g ⊕ Fin 1) (Or.inr (Set.mem_range_self q)) :
              T.DefinableFun LRV (fun _ => b q))
    have hpre : @Set.Definable M T LRV N (Fin g ⊕ Fin 1)
        {z | (z ∘ Sum.inl, Fin.snoc b (z (.inr 0))) ∈ Q.carrier} := by
      letI := N
      exact hQ.preimage_map hF
    have hsame := @same_scalar_definable M N T
    have he : {z : Fin 2 → M | @SameScalar M N (z 0) (z 1)} =
        {z | SameScalar (z 0) (z 1)} := by
      ext z
      exact same_scalar_normalize (z 0) (z 1)
    rw [he] at hsame
    have hs := @Set.Definable.preimage_comp M T LRV N (Fin 2) (Fin g ⊕ Fin 1)
      (![Sum.inr 0, Sum.inl j]) _ hsame
    letI := N
    exact hs.inter hpre
  proper := by
    rintro p ⟨hs, hQ⟩
    exact ⟨(Q.proper _ hQ).1, fun i => by fin_cases i; exact hs.1.1⟩
  invariant := by
    intro t u htu x
    exact and_congr (same_scalar_with_codes_iff (x 0) (t j) (u j) (congrFun htu j))
      (Q.invariant t u htu (Fin.snoc b (x 0)))

theorem rvLastValueRow_algebraic
    (Q : Relation S g (r + 1) (fun _ => .rv)) (j : Fin g)
    (γ : Fin g → Values.Gamma (M := M)) (b : Fin r → M)
    (hfinite : {x | SameScalar x (rawTuple (representatives γ) j) ∧
      (rawTuple (representatives γ), Fin.snoc b x) ∈ Q.carrier}.Finite)
    (x : M) (hx : SameScalar x (rawTuple (representatives γ) j) ∧
      (rawTuple (representatives γ), Fin.snoc b x) ∈ Q.carrier) :
    AlgebraicAtBase ⟨S ∪ Set.range b, Set.range γ⟩ .rv x := by
  let X := {x | SameScalar x (rawTuple (representatives γ) j) ∧
    (rawTuple (representatives γ), Fin.snoc b x) ∈ Q.carrier}
  refine ⟨X, ⟨g, γ, fun _ => Set.mem_range_self _, rvLastValueRow Q j b, ?_⟩, hfinite, hx⟩
  ext z
  rfl

/-- An independent last coordinate cannot lie in a finite same-value row.
This is the forward induction step in the value-fibre construction. -/
theorem independent_mem_rvInfiniteLast
    (hcan : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (Q : Relation S g (r + 1) (fun _ => .rv)) (j : Fin g)
    (γ : Fin g → Values.Gamma (M := M)) (t : Fin (r + 1) → CanonicalRV.RVSort M)
    (ht : rvValues t ∈ Q.fibre γ)
    (hj : Values.vrv (t (Fin.last r)) = (γ j).val)
    (hind : GammaRVSequenceIndependent ⟨S, Set.range γ⟩ t) :
    rvValues (Fin.init t) ∈ (rvInfiniteLast hcan h00 hs hsmall Q j).fibre γ := by
  change Set.Infinite _
  intro hfinite
  have hSame : SameScalar (t (Fin.last r)).val (rawTuple (representatives γ) j) := by
    have hw := rawTuple_proper (representatives γ) j
    have he : Values.vrv (t (Fin.last r)) =
        Values.vrv (representatives γ j).val := hj.trans
      (congrArg Subtype.val (representative_value (γ j))).symm
    have hc := (Values.vrv_eq_iff _ _).mp he
    have ht0 : (t (Fin.last r)).val ≠ iRVZero := by
      intro hz
      exact (γ j).property (hj.symm.trans ((Values.vrv_eq_infinity_iff _).mpr hz))
    exact ⟨⟨(t (Fin.last r)).property, ht0⟩, hw, hc⟩
  have hmem : (rawTuple (representatives γ),
      Fin.snoc (rvValues (Fin.init t)) (t (Fin.last r)).val) ∈ Q.carrier := by
    have he : Fin.snoc (rvValues (Fin.init t)) (t (Fin.last r)).val = rvValues t := by
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [Fin.snoc_last, rvValues]
      · simp only [Fin.snoc_castSucc, rvValues, Fin.init_def]
    rwa [he]
  exact hind.2 (rvLastValueRow_algebraic Q j γ (rvValues (Fin.init t)) hfinite _ ⟨hSame, hmem⟩)

end SpecialTransformations.Section4

end
