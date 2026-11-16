module

public import Section4.AffineKrullDimension
public import Mathlib.RingTheory.Ideal.Maximal

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Classical
open scoped nonZeroDivisors

noncomputable section

namespace SpecialTransformations.Section4

/-- A finite-type algebra containing an injective copy of a polynomial
ring in k variables has actual Krull dimension at least k. A prime
disjoint from the nonzero polynomials reduces the assertion to a domain. -/
theorem polynomial_subring_le_ringKrullDim
    {K R : Type} [Field K] [CommRing R] [Algebra K R] [Algebra.FiniteType K R]
    {k : ℕ} (f : MvPolynomial (Fin k) K →ₐ[K] R) (hinj : Function.Injective f) :
    (k : WithBot ℕ∞) ≤ ringKrullDim R := by
  let T : Submonoid R := (nonZeroDivisors (MvPolynomial (Fin k) K)).map f.toRingHom
  have hbot : Disjoint ((⊥ : Ideal R) : Set R) (T : Set R) := by
    apply Set.disjoint_left.mpr
    rintro x hx ⟨p, hp, rfl⟩
    have hx0 : f p = 0 := hx
    apply nonZeroDivisors.ne_zero hp
    apply hinj
    simpa only [map_zero] using hx0
  obtain ⟨P, hP, _, hdis⟩ := Ideal.exists_le_prime_disjoint (⊥ : Ideal R) T hbot
  letI := hP
  let J : MvPolynomial (Fin k) K →ₐ[K] (R ⧸ P) := (Ideal.Quotient.mkₐ K P).comp f
  have hJ : Function.Injective J := by
    intro p q he
    apply sub_eq_zero.mp
    by_contra hz
    have hzero : J (p - q) = 0 := by rw [map_sub, he, sub_self]
    have hmem : f (p - q) ∈ P := Ideal.Quotient.eq_zero_iff_mem.mp hzero
    apply Set.disjoint_left.mp hdis hmem
    exact ⟨p - q, mem_nonZeroDivisors_iff_ne_zero.mpr hz, rfl⟩
  have heval : MvPolynomial.aeval (fun i => J (MvPolynomial.X i)) = J := by
    apply MvPolynomial.algHom_ext
    intro i
    simp
  have hind : AlgebraicIndependent K (fun i => J (MvPolynomial.X i)) := by
    apply algebraicIndependent_iff_injective_aeval.mpr
    rw [heval]
    exact hJ
  let L := FractionRing (R ⧸ P)
  let incl : (R ⧸ P) →ₐ[K] L := IsScalarTower.toAlgHom K (R ⧸ P) L
  have hindL := hind.map' (f := incl) (FaithfulSMul.algebraMap_injective (R ⧸ P) L)
  have hcard : (k : Cardinal) ≤ Algebra.trdeg K L := by
    simpa only [Cardinal.mk_fintype, Fintype.card_fin] using hindL.cardinalMk_le_trdeg
  obtain ⟨d, hd, htr⟩ := AffineKrullDimension.exists_dimension_and_trdeg K (R ⧸ P)
  rw [htr] at hcard
  have hk : k ≤ d := by exact_mod_cast hcard
  calc
    (k : WithBot ℕ∞) ≤ d := by exact_mod_cast hk
    _ = ringKrullDim (R ⧸ P) := hd.symm
    _ ≤ ringKrullDim R := ringKrullDim_quotient_le P

end SpecialTransformations.Section4

end
