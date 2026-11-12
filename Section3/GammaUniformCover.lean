module

public import Section3.GammaGoodRelations
public import Section3.TupleCompactness
public import Section3.NormalizationSaturation

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3.GammaParameters
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n : ℕ}

theorem good_gamma_slice_definable (S : Set M) (δ : Values.Gamma (M := M))
    (R : GoodGammaRelation S n) :
    @Set.Definable M (insert (raw (representative δ)) S) LRV
      (CanonicalStructure.normalize (M := M)) (Fin n)
      {a | (a,raw (representative δ)) ∈ R.carrier} := by
  let b := raw (representative δ)
  have hRd := R.definable
  let N := CanonicalStructure.normalize (M := M)
  letI := N
  have hR := hRd.mono (Set.subset_insert b S)
  let F (a : Fin n → M) : Fin n ⊕ Fin 1 → M := Sum.elim a (fun _ => b)
  have hF : (insert b S).DefinableMap LRV F := by
    intro i
    cases i with
    | inl i => exact Set.DefinableFun.proj LRV
    | inr i => exact LRV.definableFun_const (Fin n) (Set.mem_insert b S)
  exact hR.preimage_map hF

/-- Only the temporary domain base B and one code for delta are used by
compactness. Every relation in the finite union remains defined over S. -/
theorem uniform_good_gamma_relation_cover {κ : Cardinal} (hs : Saturated M κ)
    (S B : Set M) (hSB : S ⊆ B) (A : Set (Fin n → M)) (δ : Values.Gamma (M := M))
    (hsmall : Cardinal.mk ↥(insert (raw (representative δ)) B) < κ)
    (hA : @Set.Definable M B LRV (CanonicalStructure.normalize (M := M)) (Fin n) A)
    (hb : ∀ a ∈ A, GammaAlgebraicAtBase (⟨S ∪ Set.range a,∅⟩ : Base (M := M)) δ) :
    ∃ R : GoodGammaRelation S n, ∀ a ∈ A, (a,raw (representative δ)) ∈ R.carrier := by
  let b := raw (representative δ)
  let slice (R : GoodGammaRelation S n) : Set (Fin n → M) := {a | (a,b) ∈ R.carrier}
  let C := Set.range slice
  have hcov : ∀ a ∈ A, ∃ c ∈ C, a ∈ c := by
    intro a ha
    obtain ⟨R,hR⟩ := good_gamma_relation_of_algebraic S a δ (hb a ha)
    exact ⟨slice R,Set.mem_range_self _,hR⟩
  have hInsert : insert b S ⊆ insert b B := by
    intro x hx
    rcases hx with rfl | hx
    · exact Or.inl rfl
    · exact Or.inr (hSB hx)
  have hd (c : Set (Fin n → M)) (hc : c ∈ C) :
      @Set.Definable M (insert b B) LRV (CanonicalStructure.normalize (M := M)) (Fin n) c := by
    obtain ⟨R,rfl⟩ := hc
    have hslice := good_gamma_slice_definable S δ R
    let N := CanonicalStructure.normalize (M := M)
    letI := N
    exact hslice.mono hInsert
  have hsN : @Saturated M (CanonicalStructure.normalize (M := M)) κ := hs.normalize
  have hFiniteCover : ∃ C₀ : Set (Set (Fin n → M)), C₀.Finite ∧ C₀ ⊆ C ∧
      ∀ a ∈ A, ∃ c ∈ C₀, a ∈ c := by
    let N := CanonicalStructure.normalize (M := M)
    letI := N
    exact hsN.definable_finite_subcover_tuple
      (insert b B) hsmall A (hA.mono (Set.subset_insert b B)) C hd hcov
  obtain ⟨C₀,hC₀,hsub,hcover⟩ := hFiniteCover
  haveI : Finite C₀ := hC₀.to_subtype
  have hchoice (c : C₀) : ∃ R : GoodGammaRelation S n, slice R = c.val := hsub c.property
  let rel (c : C₀) := Classical.choose (hchoice c)
  have hrel (c : C₀) : slice (rel c) = c.val := Classical.choose_spec (hchoice c)
  let R : Set ((Fin n → M) × M) := {p | ∃ c : C₀, p ∈ (rel c).carrier}
  have hR : @RawClosure.Tuple.RelationDefinable M (CanonicalStructure.normalize (M := M)) n S R := by
    have hrel_def (c : C₀) := (rel c).definable
    let N := CanonicalStructure.normalize (M := M)
    letI := N
    have hu := Set.definable_iUnion_of_finite hrel_def
    simpa only [RawClosure.Tuple.RelationDefinable,R,Set.mem_ofPred_eq,Set.iUnion_ofPred] using hu
  refine ⟨⟨R,hR,?_,?_,?_⟩,?_⟩
  · rintro a x ⟨c,hc⟩
    exact (rel c).proper a x hc
  · intro a t u he
    change (∃ c : C₀, (a,raw t) ∈ (rel c).carrier) ↔
      (∃ c : C₀, (a,raw u) ∈ (rel c).carrier)
    exact exists_congr (fun c => (rel c).invariant a t u he)
  · intro a
    have hh := Set.finite_iUnion (fun c : C₀ => (rel c).finite a)
    simpa only [gammaRow,R,Set.mem_ofPred_eq,Set.iUnion_ofPred] using hh
  · intro a ha
    obtain ⟨c,hc,hac⟩ := hcover a ha
    refine ⟨⟨c,hc⟩,?_⟩
    change a ∈ slice (rel ⟨c,hc⟩)
    rw [hrel]
    exact hac

end SpecialTransformations.Section3.GammaParameters
