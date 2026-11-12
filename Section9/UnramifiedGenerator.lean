module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Section9.ValuedPowerBasis
public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.Henselian

@[expose] public section

/-! When the residue degree equals the field degree, a primitive
residue generator lifts to a simple integral root. Its powers give
an integral coordinate expansion by residue independence. -/

set_option backward.isDefEq.respectTransparency false

open IsLocalRing Polynomial

namespace SpecialTransformations.Section9

variable {K G : Type*} [Field K] [LinearOrderedCommGroupWithZero G]

theorem exists_unramified_powerBasis_of_residue_degree
    (v : Valuation K G) (F : Subfield K) [FiniteDimensional F K]
    [HenselianLocalRing v.valuationSubring]
    [CharZero (ResidueField v.valuationSubring)]
    (hdegree : letI := (residueFieldInclusion v F).toAlgebra
      Module.finrank F K = Module.finrank (ResidueField (v.comap F.subtype).valuationSubring)
        (ResidueField v.valuationSubring)) :
    ∃ (u : v.valuationSubring) (P : Polynomial K) (d : ℕ),
      P.eval (u : K) = 0 ∧ v (P.derivative.eval (u : K)) = 1 ∧
      (∀ i ∈ P.support, P.coeff i ∈ F ∧ v (P.coeff i) ≤ 1) ∧
      (∀ c : Fin d → ResidueField (v.comap F.subtype).valuationSubring,
        (∑ j, residueFieldInclusion v F (c j) * residue v.valuationSubring u ^ (j : ℕ)) = 0 →
        c = 0) ∧
      ∀ z : K, ∃ c : Fin d → F, ∑ j, (c j : K) * (u : K) ^ (j : ℕ) = z := by
  classical
  let A := (v.comap F.subtype).valuationSubring
  let B := v.valuationSubring
  let k := ResidueField A
  let l := ResidueField B
  let j := residueFieldInclusion v F
  letI : Algebra k l := j.toAlgebra
  letI : CharZero k := ⟨by
    intro a b h
    apply (Nat.cast_injective (R := l))
    simpa only [map_natCast] using congrArg j h⟩
  letI : FiniteDimensional k l := FiniteDimensional.of_finrank_pos
    (show 0 < Module.finrank k l from hdegree ▸ Module.finrank_pos)
  letI : Algebra.IsSeparable k l := Algebra.IsAlgebraic.isSeparable_of_perfectField
  let pb : PowerBasis k l := Field.powerBasisOfFiniteOfSeparable k l
  let q := minpoly k pb.gen
  have hq : q.Monic := minpoly.monic (Algebra.IsIntegral.isIntegral pb.gen)
  have hzero : aeval pb.gen q = 0 := minpoly.aeval k pb.gen
  have hsep : q.Separable := (minpoly.irreducible (Algebra.IsIntegral.isIntegral pb.gen)).separable
  have hderiv : aeval pb.gen q.derivative ≠ 0 := hsep.aeval_derivative_ne_zero hzero
  have hqLift : q ∈ lifts (residue A) :=
    ⟨(Polynomial.map_surjective _ residue_surjective q).choose,
      (Polynomial.map_surjective _ residue_surjective q).choose_spec⟩
  obtain ⟨P, hP, _, hPm⟩ := lifts_and_natDegree_eq_and_monic hqLift hq
  let i := valuationRingInclusion v F
  let Q := P.map i
  have hred : Q.map (residue B) = q.map j := by
    change (P.map i).map (residue B) = _
    rw [Polynomial.map_map, ← ResidueField.map_comp_residue, ← Polynomial.map_map, hP]
    rfl
  have hQzero : aeval pb.gen Q = 0 := by
    rw [Polynomial.aeval_def, ResidueField.algebraMap_eq, ← Polynomial.eval_map, hred,
      Polynomial.eval_map]
    exact hzero
  have hQderiv : aeval pb.gen Q.derivative ≠ 0 := by
    rw [Polynomial.aeval_def, ResidueField.algebraMap_eq, ← Polynomial.eval_map,
      ← Polynomial.derivative_map, hred, Polynomial.derivative_map, Polynomial.eval_map]
    exact hderiv
  have hEval (p : Polynomial B) (a : B) : residue B (p.eval a) = aeval (residue B a) p := by
    rw [← Polynomial.eval_map_apply, Polynomial.aeval_def, ResidueField.algebraMap_eq,
      Polynomial.eval_map]
  obtain ⟨a, ha⟩ := residue_surjective (R := B) pb.gen
  have ha₀ : Q.eval a ∈ maximalIdeal B := by
    rw [← residue_eq_zero_iff, hEval, ha]
    exact hQzero
  have haUnit : IsUnit (Q.derivative.eval a) := by
    rw [← residue_ne_zero_iff_isUnit, hEval, ha]
    exact hQderiv
  obtain ⟨u, hu, hua⟩ := HenselianLocalRing.is_henselian Q (hPm.map i) a ha₀ haUnit
  have hres : residue B u = pb.gen := by
    rw [← residue_eq_zero_iff, map_sub, ha, sub_eq_zero] at hua
    exact hua
  have hEvalK (p : Polynomial B) (a : B) : (p.map B.subtype).eval (a : K) = B.subtype (p.eval a) :=
    Polynomial.eval_map_apply B.subtype (p := p) a
  let P₀ := Q.map B.subtype
  have hroot : P₀.eval (u : K) = 0 := by
    exact (hEvalK Q u).trans ((congrArg B.subtype (show Q.eval u = 0 from hu)).trans (map_zero _))
  have huDeriv : residue B (Q.derivative.eval u) ≠ 0 := by
    rw [hEval, hres]
    exact hQderiv
  have hunitB : v ((Q.derivative.eval u : B) : K) = 1 := by
    have hi := (Valuation.mem_valuationSubring_iff v _).mp (Q.derivative.eval u).property
    have hn : Q.derivative.eval u ∉ maximalIdeal B := by
      rwa [← residue_eq_zero_iff]
    exact hi.antisymm (le_of_not_gt (fun h => hn ((Valuation.mem_maximalIdeal_iff K v).mpr h)))
  have hunit : v (P₀.derivative.eval (u : K)) = 1 := by
    change v ((Q.map B.subtype).derivative.eval (u : K)) = 1
    rw [Polynomial.derivative_map]
    exact (congrArg v (hEvalK Q.derivative u)).trans hunitB
  have hcoeff (a : ℕ) : P₀.coeff a ∈ F ∧ v (P₀.coeff a) ≤ 1 := by
    change ((P.map i).map B.subtype).coeff a ∈ F ∧ v (((P.map i).map B.subtype).coeff a) ≤ 1
    rw [Polynomial.coeff_map, Polynomial.coeff_map]
    exact ⟨(P.coeff a).val.property, (P.coeff a).property⟩
  have hind (c : Fin pb.dim → k)
      (hc : (∑ j', j (c j') * residue B u ^ (j' : ℕ)) = 0) : c = 0 := by
    apply pb.basis.linearIndependent.fintypeLinearCombination_injective
    rw [map_zero]
    simp only [Fintype.linearCombination_apply, pb.basis_eq_pow, Algebra.smul_def]
    change (∑ i, j (c i) * pb.gen ^ (i : ℕ)) = 0
    simpa only [hres] using hc
  let L := Fintype.linearCombination F (fun i : Fin pb.dim => (u : K) ^ (i : ℕ))
  have he (c : Fin pb.dim → F) : L c = ∑ i, (c i : K) * (u : K) ^ (i : ℕ) := by
    simp only [L, Fintype.linearCombination_apply, Algebra.smul_def]
    rfl
  have hInj : Function.Injective L := by
    apply (injective_iff_map_eq_zero L).mpr
    intro c hc
    funext i
    apply Subtype.ext
    have h := value_coeff_le_powerSum v F u hind c i
    rw [← he, hc, map_zero] at h
    exact v.zero_iff.mp (le_antisymm h zero_le)
  have hdim : Module.finrank F (Fin pb.dim → F) = Module.finrank F K := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin, ← pb.finrank]
    exact hdegree.symm
  have hSurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hInj
  refine ⟨u, P₀, pb.dim, hroot, hunit, fun i _ => hcoeff i, hind, fun z => ?_⟩
  obtain ⟨c, hc⟩ := hSurj z
  exact ⟨c, (he c).symm.trans hc⟩

end SpecialTransformations.Section9
