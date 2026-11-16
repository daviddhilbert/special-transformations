module

public import Section9.FiniteLimitSeparation
public import Section9.LimitBallDefinable
public import Section9.LimitFiniteCandidate
public import Section9.LimitPolynomialCover

@[expose] public section

/-! Existence of the finite minimal limit in Lemma 9.5. The definable
graph is projected one coordinate at a time, and the candidate sets
from the two polynomial charts are combined and minimized. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

local notation "VF" => VFType (M := M)

private theorem exists_finite_limitSet_of_coordinate {m : ℕ}
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal} (hs : Saturated M κ)
    {S : Set M} (hsmall : Cardinal.mk S < κ) (A : Set (Fin 1 → VF))
    (f : (Fin 1 → VF) → Set (Fin m → VF))
    (hG : S.Definable LRV (unaryLimitGraph A f)) (hfin : ∀ x ∈ A, (f x).Finite) (i : Fin m) :
    ∃ L : Set (Fin 1 → LimitPoint M), L.Finite ∧
      IsLimitSet A 0 (fun x => (fun y (_ : Fin 1) => y i) '' f x) L := by
  classical
  let index : Fin 2 → Fin 1 ⊕ Fin m := ![.inl 0, .inr i]
  let G : Set (Fin 2 → M) := (fun z => z ∘ index) '' unaryLimitGraph A f
  have hG' : S.Definable LRV G := hG.image_comp index
  have hsort : ∀ z ∈ G, ∀ j, iVF (z j) := by
    rintro z ⟨_, ⟨x, _, y, _, rfl⟩, rfl⟩ j
    fin_cases j
    · exact (x 0).property
    · exact (y i).property
  have hmem (u v : VF) : vfValues ![u, v] ∈ G ↔
      ∃ x ∈ A, x 0 = u ∧ ∃ y ∈ f x, y i = v := by
    constructor
    · rintro ⟨_, ⟨x, hx, y, hy, rfl⟩, he⟩
      exact ⟨x, hx, Subtype.ext (congrFun he 0), y, hy, Subtype.ext (congrFun he 1)⟩
    · rintro ⟨x, hx, hxu, y, hy, hyv⟩
      refine ⟨Sum.elim (vfValues x) (vfValues y), ⟨x, hx, y, hy, rfl⟩, ?_⟩
      funext j
      fin_cases j
      · exact congrArg Subtype.val hxu
      · exact congrArg Subtype.val hyv
  have hGfin (u : VF) : {v : VF | vfValues ![u, v] ∈ G}.Finite := by
    let a : Fin 1 → VF := fun _ => u
    by_cases ha : a ∈ A
    · apply ((hfin a ha).image (fun y => y i)).subset
      intro v hv
      obtain ⟨x, hx, he, y, hy, hyv⟩ := (hmem u v).mp hv
      have hx' : x = a := funext (fun j => by fin_cases j; exact he)
      exact ⟨y, hx' ▸ hy, hyv⟩
    · apply Set.finite_empty.subset
      intro v hv
      obtain ⟨x, hx, he, _⟩ := (hmem u v).mp hv
      have hx' : x = a := funext (fun j => by fin_cases j; exact he)
      exact (ha (hx' ▸ hx)).elim
  obtain ⟨P, hP, hp⟩ := exists_polynomial_of_finite_vf_fibres hc hs hsmall hG' hsort hGfin
  let E := vfParameterField S
  let p := MvPolynomial.map E.subtype P
  have hp₀ : p ≠ 0 := by
    intro h
    apply hP
    exact (MvPolynomial.map_injective E.subtype Subtype.val_injective) (h.trans (map_zero _).symm)
  apply exists_finite_limitSet_of_unary_polynomial A _ p hp₀
  rintro x hx _ ⟨y, hy, rfl⟩
  change MvPolynomial.eval ![x 0, y i] (MvPolynomial.map E.subtype P) = 0
  rw [MvPolynomial.eval_map]
  exact hp _ ((hmem _ _).mpr ⟨x, hx, rfl, y, hy, rfl⟩)

/-- The existence part of Lemma 9.5, in the actual VF and Gamma sorts.
Same-base definability is proved separately from frequent hits. -/
theorem lemma_9_5_finite_minimal {m : ℕ}
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal} (hs : Saturated M κ)
    {S : Set M} (hsmall : Cardinal.mk S < κ) (A : Set (Fin 1 → VF))
    (f : (Fin 1 → VF) → Set (Fin m → VF))
    (hG : S.Definable LRV (unaryLimitGraph A f)) (hfin : ∀ x ∈ A, (f x).Finite) :
    ∃ L : Set (Fin m → LimitPoint M), L.Finite ∧ IsMinimalLimitSet A 0 f L := by
  obtain ⟨K, hKf, hK⟩ := exists_finite_limitSet_of_coordinates A 0 f
    (exists_finite_limitSet_of_coordinate hc hs hsmall A f hG hfin)
  obtain ⟨L, _, hL, hLf⟩ := hK.exists_minimal_subset hKf
  exact ⟨L, hLf, hL⟩

end SpecialTransformations.Section9
