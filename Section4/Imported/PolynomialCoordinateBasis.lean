module

/-
Attributed excerpt from DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture.
Fixed revision: e457fde9100c9b7226bd4d81af6860f210a531ab.
Source: RB31EndToEnd/Algebra/PolynomialPrimeTrdegHeight.lean.
Source credit: the upstream formalization's contributors.
Apache-2.0; see BodyPin-LICENSE. The upstream file has no separate author header.
The coordinate definitions and two basis proofs below are retained unchanged;
only imports are narrowed. The remaining prime-height code is not needed here.
-/
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.RingTheory.Polynomial.Quotient

@[expose] public section

noncomputable section
namespace RB31E2E.PolynomialPrimeTrdegHeight
open MvPolynomial

/-- The image of a polynomial coordinate in a quotient. -/
def quotientCoordinate {k ι : Type*} [CommRing k]
    (P : Ideal (MvPolynomial ι k)) (i : ι) :
    MvPolynomial ι k ⧸ P :=
  Ideal.Quotient.mk P (MvPolynomial.X i)

/-- A polynomial quotient is generated, as an algebra, by the images of its
coordinate variables. -/
theorem adjoin_range_quotientCoordinate
    {k ι : Type*} [CommRing k]
    (P : Ideal (MvPolynomial ι k)) :
    Algebra.adjoin k (Set.range (quotientCoordinate P)) = ⊤ := by
  rw [Algebra.adjoin_range_eq_range_aeval]
  apply top_unique
  rintro b -
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective b
  refine ⟨f, ?_⟩
  change MvPolynomial.aeval
    (fun d : ι ↦ Ideal.Quotient.mk P (MvPolynomial.X d)) f =
      Ideal.Quotient.mk P f
  rw [← MvPolynomial.mkₐ_eq_aeval P]
  rfl

/-- Every prime quotient of a finite polynomial ring admits a
transcendence basis chosen from the images of the original coordinates.
This is an existence theorem, not a premise of the later height formula. -/
theorem exists_coordinate_transcendenceBasis
    {k ι : Type*} [Field k] [Finite ι]
    (P : Ideal (MvPolynomial ι k)) [P.IsPrime] :
    ∃ t : Set (MvPolynomial ι k ⧸ P),
      t ⊆ Set.range (quotientCoordinate P) ∧
      IsTranscendenceBasis k
        ((↑) : t → (MvPolynomial ι k ⧸ P)) := by
  let B := MvPolynomial ι k ⧸ P
  let x : ι → B := quotientCoordinate P
  have htop : Algebra.adjoin k (Set.range x) = ⊤ :=
    adjoin_range_quotientCoordinate P
  letI : Algebra.IsAlgebraic (Algebra.adjoin k (Set.range x)) B := by
    constructor
    intro b
    have hb : b ∈ Algebra.adjoin k (Set.range x) := by
      rw [htop]
      trivial
    exact isAlgebraic_algebraMap
      (⟨b, hb⟩ : Algebra.adjoin k (Set.range x))
  exact exists_isTranscendenceBasis_subset (R := k) (A := B)
    (Set.range x)

/-- Index-level version: one can choose a subset of the original variable
indices whose quotient-coordinate images form a transcendence basis. -/
theorem exists_coordinateIndex_transcendenceBasis
    {k ι : Type*} [Field k] [Finite ι]
    (P : Ideal (MvPolynomial ι k)) [P.IsPrime] :
    ∃ S : Set ι,
      IsTranscendenceBasis k
        (fun i : S ↦ quotientCoordinate P i) := by
  obtain ⟨t, ht, htb⟩ := exists_coordinate_transcendenceBasis P
  let g : t → ι := fun y ↦
    Classical.choose (ht y.property)
  have hg (y : t) : quotientCoordinate P (g y) = y :=
    Classical.choose_spec (ht y.property)
  have hginj : Function.Injective g := by
    intro a b hab
    apply Subtype.ext
    simpa [hg] using congrArg (quotientCoordinate P) hab
  let S : Set ι := Set.range g
  let e : t ≃ S := Equiv.ofInjective g hginj
  have heq :
      (fun i : S ↦ quotientCoordinate P i) ∘ e =
        ((↑) : t → (MvPolynomial ι k ⧸ P)) := by
    funext y
    exact hg y
  refine ⟨S, ?_⟩
  exact (isTranscendenceBasis_equiv' e heq).mp htb

end RB31E2E.PolynomialPrimeTrdegHeight
