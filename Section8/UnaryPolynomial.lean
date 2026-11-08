import Mathlib.Algebra.Polynomial.Div
import Section3.PolynomialLocal
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Section4.FullDimension
import Section4.PolynomialCover
import Section3.RingSyntax
import Section3.DefinableConstants
import Section3.TupleCompactness
import Section3.SmallFiniteParameters

/-! Polynomial relations, finite coefficient shapes, and ties of dominant terms. -/

section PolynomialGerms

/-! The polynomial step in the local value law of Lemma 8.3.
The lowest nonzero coefficient controls both value and RV near the centre. -/

set_option backward.isDefEq.respectTransparency false

open Filter Topology Polynomial FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3

namespace SpecialTransformations.Section8

private theorem eval_eq_root_power_mul_quotient {K : Type} [Field K]
    (p : Polynomial K) (a x : K) :
    p.eval x = (x - a) ^ p.rootMultiplicity a *
      (p /ₘ (X - C a) ^ p.rootMultiplicity a).eval x := by
  have h := congrArg (Polynomial.eval x) (p.pow_mul_divByMonic_rootMultiplicity_eq a)
  simpa only [eval_mul, eval_pow, eval_sub, eval_X, eval_C] using h.symm

theorem eventually_value_eval_eq_root_power {K Γ : Type} [Field K]
    [LinearOrderedCommGroupWithZero Γ] [Valued K Γ]
    (p : Polynomial K) (hp : p ≠ 0) (a : K) :
    ∀ᶠ x in 𝓝 a, Valued.v (p.eval x) =
      Valued.v (x - a) ^ p.rootMultiplicity a *
        Valued.v (p.comp (X + C a)).trailingCoeff := by
  let q := p /ₘ (X - C a) ^ p.rootMultiplicity a
  have hq : q.eval a ≠ 0 := eval_divByMonic_pow_rootMultiplicity_ne_zero a hp
  have hqa : q.eval a = (p.comp (X + C a)).trailingCoeff :=
    eval_divByMonic_eq_trailingCoeff_comp
  filter_upwards [polynomial_close_nhds q a hq] with x hx
  have he : Valued.v (q.eval x) = Valued.v (q.eval a) :=
    (Valued.v : Valuation K Γ).map_eq_of_sub_lt hx
  rw [eval_eq_root_power_mul_quotient, map_mul, map_pow]
  change _ * Valued.v (q.eval x) = _
  rw [he, hqa]

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ] [Valued (VFType (M := M)) Γ]

/-- The local monomial law holds in the released RV sort, before passing
to the value-group quotient. -/
theorem eventually_rv_eval_eq_root_power
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (p : Polynomial (VFType (M := M))) (hp : p ≠ 0) (a : VFType (M := M)) :
    ∀ᶠ x in 𝓝 a, iRv (p.eval x).val =
      iRVMul (iRv ((x - a) ^ p.rootMultiplicity a).val)
        (iRv (p.comp (X + C a)).trailingCoeff.val) := by
  let q := p /ₘ (X - C a) ^ p.rootMultiplicity a
  have hq : q.eval a ≠ 0 := eval_divByMonic_pow_rootMultiplicity_ne_zero a hp
  have hqa : q.eval a = (p.comp (X + C a)).trailingCoeff :=
    eval_divByMonic_eq_trailingCoeff_comp
  filter_upwards [polynomial_rv_locally_constant hv q a hq] with x hx
  let w := (x - a) ^ p.rootMultiplicity a
  calc
    iRv (p.eval x).val = iRv (w * q.eval x).val :=
      congrArg (fun z : VFType (M := M) => iRv z.val) (eval_eq_root_power_mul_quotient p a x)
    _ = iRVMul (iRv w.val) (iRv (q.eval x).val) :=
      rv_mul_hom_of_model hM w.property (q.eval x).property
    _ = _ := by rw [hx, hqa]

end SpecialTransformations.Section8
end PolynomialGerms

section PolynomialSlopeTies

/-! At a nonzero root, at least two terms have the maximal valuation
in Mathlib's multiplicative order. After specializing the coefficients
of a bivariate polynomial near a centre, such a tie gives a candidate
rational slope with two distinct output exponents. -/

set_option backward.isDefEq.respectTransparency false

open Filter Topology Polynomial
open scoped BigOperators

namespace SpecialTransformations.Section8

variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]

theorem nonzero_root_has_equal_maximal_terms (v : Valuation K Γ)
    (p : Polynomial K) (hp : p ≠ 0) (y : K) (hy : y ≠ 0) (hroot : p.eval y = 0) :
    ∃ i ∈ p.support, ∃ j ∈ p.support, i ≠ j ∧
      v (p.coeff i * y ^ i) = v (p.coeff j * y ^ j) ∧
      ∀ k ∈ p.support, v (p.coeff k * y ^ k) ≤ v (p.coeff i * y ^ i) := by
  classical
  let term (i : ℕ) := p.coeff i * y ^ i
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image p.support (fun j => v (term j))
    (Polynomial.support_nonempty.mpr hp)
  by_cases h : ∃ j ∈ p.support, j ≠ i ∧ v (term j) = v (term i)
  · obtain ⟨j, hj, hne, he⟩ := h
    exact ⟨i, hi, j, hj, hne.symm, he.symm, hmax⟩
  · exfalso
    have hlt (j : ℕ) (hj : j ∈ p.support \ {i}) : v (term j) < v (term i) := by
      have hmem : j ∈ p.support ∧ j ≠ i := by
        simpa only [Finset.mem_sdiff, Finset.mem_singleton] using hj
      exact lt_of_le_of_ne (hmax j hmem.1) (fun he => h ⟨j, hmem.1, hmem.2, he⟩)
    have hsum : (∑ j ∈ p.support, term j) = 0 := by
      rw [← hroot, Polynomial.eval_eq_sum]
      rfl
    have he := v.map_sum_eq_of_lt hi hlt
    rw [hsum, map_zero] at he
    have hterm : term i ≠ 0 := mul_ne_zero (Polynomial.mem_support_iff.mp hi) (pow_ne_zero _ hy)
    exact (v.ne_zero_iff.mpr hterm) he.symm

/-- For a bivariate polynomial viewed as a polynomial in the output,
the two powers of the output value come from its finite support. The
powers of the input distance come from the multiplicities of its
coefficient polynomials at the centre. -/
theorem eventually_specialized_root_tie [Valued K Γ]
    (P : Polynomial (Polynomial K)) (hP : P ≠ 0) (a : K) :
    ∀ᶠ x in 𝓝 a, x ≠ a → ∀ y : K, y ≠ 0 →
      (P.map (Polynomial.evalRingHom x)).eval y = 0 →
      ∃ i ∈ P.support, ∃ j ∈ P.support, i ≠ j ∧
        (Valued.v (x - a) ^ (P.coeff i).rootMultiplicity a *
          Valued.v ((P.coeff i).comp (X + C a)).trailingCoeff) * Valued.v y ^ i =
        (Valued.v (x - a) ^ (P.coeff j).rootMultiplicity a *
          Valued.v ((P.coeff j).comp (X + C a)).trailingCoeff) * Valued.v y ^ j := by
  let v : Valuation K Γ := Valued.v
  have hcoeff : ∀ᶠ x in 𝓝 a, ∀ i ∈ P.support, v ((P.coeff i).eval x) =
      v (x - a) ^ (P.coeff i).rootMultiplicity a *
        v ((P.coeff i).comp (X + C a)).trailingCoeff := by
    rw [Filter.eventually_all_finset]
    intro i hi
    exact eventually_value_eval_eq_root_power (P.coeff i) (Polynomial.mem_support_iff.mp hi) a
  filter_upwards [hcoeff] with x hx hxa y hy hroot
  let q := P.map (Polynomial.evalRingHom x)
  have hqcoeff (i : ℕ) : q.coeff i = (P.coeff i).eval x := Polynomial.coeff_map _ _
  obtain ⟨k, hk⟩ := Polynomial.support_nonempty.mpr hP
  have htrail : ((P.coeff k).comp (X + C a)).trailingCoeff ≠ 0 := by
    rw [← Polynomial.eval_divByMonic_eq_trailingCoeff_comp]
    exact Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero a (Polynomial.mem_support_iff.mp hk)
  have hqk : v (q.coeff k) ≠ 0 := by
    rw [hqcoeff, hx k hk]
    exact mul_ne_zero (pow_ne_zero _ (v.ne_zero_iff.mpr (sub_ne_zero.mpr hxa))) (v.ne_zero_iff.mpr htrail)
  have hq : q ≠ 0 := fun he => hqk (by rw [he, coeff_zero, map_zero])
  obtain ⟨i, hi, j, hj, hne, he, _⟩ := nonzero_root_has_equal_maximal_terms v q hq y hy hroot
  have hsub : q.support ⊆ P.support := by
    intro l hl
    apply Polynomial.mem_support_iff.mpr
    intro hz
    apply (Polynomial.mem_support_iff.mp hl)
    rw [hqcoeff, hz, eval_zero]
  refine ⟨i, hsub hi, j, hsub hj, hne, ?_⟩
  rw [map_mul, map_mul, map_pow, map_pow, hqcoeff, hqcoeff, hx i (hsub hi), hx j (hsub hj)] at he
  exact he

end SpecialTransformations.Section8
end PolynomialSlopeTies

section PolynomialShapes

/-! A finite set of exponent pairs is a polynomial shape. Its coefficient
tuple can be quantified in the valued-field language, while the shape
itself fixes the exponents used to extract slopes. -/

set_option backward.isDefEq.respectTransparency false

open Polynomial
open scoped BigOperators

namespace SpecialTransformations.Section8

variable {K : Type} [Field K]

noncomputable def shapedPolynomial (D : Finset (ℕ × ℕ)) (c : ↥D → K) :
    Polynomial (Polynomial K) :=
  ∑ d : ↥D, monomial d.val.2 (monomial d.val.1 (c d))

theorem coeff_coeff_shapedPolynomial (D : Finset (ℕ × ℕ)) (c : ↥D → K) (d : ↥D) :
    ((shapedPolynomial D c).coeff d.val.2).coeff d.val.1 = c d := by
  classical
  simp only [shapedPolynomial, Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single d]
  · simp [Polynomial.coeff_monomial]
  · intro e _ he
    by_cases h2 : e.val.2 = d.val.2
    · have h1 : e.val.1 ≠ d.val.1 := fun h => he (Subtype.ext (Prod.ext h h2))
      simp only [Polynomial.coeff_monomial, h2, if_pos, h1, if_false]
    · simp only [Polynomial.coeff_monomial, h2, if_false, Polynomial.coeff_zero]
  · intro h
    exact (h (Finset.mem_univ d)).elim

theorem shapedPolynomial_ne_zero {D : Finset (ℕ × ℕ)} {c : ↥D → K}
    (h : ∃ d, c d ≠ 0) : shapedPolynomial D c ≠ 0 := by
  obtain ⟨d, hd⟩ := h
  intro he
  have hc := coeff_coeff_shapedPolynomial D c d
  rw [he, Polynomial.coeff_zero, Polynomial.coeff_zero] at hc
  exact hd hc.symm

theorem shapedPolynomial_eval (D : Finset (ℕ × ℕ)) (c : ↥D → K) (x y : K) :
    ((shapedPolynomial D c).map (Polynomial.evalRingHom x)).eval y =
      ∑ d : ↥D, (c d * x ^ d.val.1) * y ^ d.val.2 := by
  change Polynomial.evalRingHom y (Polynomial.mapRingHom (Polynomial.evalRingHom x)
    (∑ d : ↥D, monomial d.val.2 (monomial d.val.1 (c d)))) = _
  rw [map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro d _
  change ((monomial d.val.2 (monomial d.val.1 (c d))).map (Polynomial.evalRingHom x)).eval y = _
  rw [Polynomial.map_monomial, Polynomial.eval_monomial]
  change (monomial d.val.1 (c d)).eval x * y ^ d.val.2 = _
  rw [Polynomial.eval_monomial]

private noncomputable def exponentPair : (Fin 2 →₀ ℕ) ≃ ℕ × ℕ :=
  (Finsupp.equivFunOnFinite : (Fin 2 →₀ ℕ) ≃ (Fin 2 → ℕ)).trans
    { toFun := fun d => (d 0, d 1)
      invFun := fun d => ![d.1, d.2]
      left_inv := fun d => by funext i; fin_cases i <;> rfl
      right_inv := fun d => by cases d; rfl }

/-- Every nonzero polynomial in two variables has a finite shape with a
nonzero coefficient tuple and the same evaluations. -/
theorem mvPolynomial_has_shape (P : MvPolynomial (Fin 2) K) (hP : P ≠ 0) :
    ∃ D : Finset (ℕ × ℕ), ∃ c : ↥D → K, (∃ d, c d ≠ 0) ∧
      ∀ x y : K, MvPolynomial.eval ![x, y] P =
        ((shapedPolynomial D c).map (Polynomial.evalRingHom x)).eval y := by
  classical
  let e := exponentPair
  let D := P.support.map e.toEmbedding
  let c : ↥D → K := fun d => P.coeff (e.symm d.val)
  refine ⟨D, c, ?_, ?_⟩
  · obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr hP
    refine ⟨⟨e d, Finset.mem_map.mpr ⟨d, hd, rfl⟩⟩, ?_⟩
    simpa only [c, Equiv.symm_apply_apply] using MvPolynomial.mem_support_iff.mp hd
  · intro x y
    rw [MvPolynomial.eval_eq', shapedPolynomial_eval]
    change _ = ∑ d ∈ D.attach, (P.coeff (e.symm d.val) * x ^ d.val.1) * y ^ d.val.2
    rw [Finset.sum_attach D (fun d => (P.coeff (e.symm d) * x ^ d.1) * y ^ d.2)]
    change _ = ∑ d ∈ P.support.map e.toEmbedding, (P.coeff (e.symm d) * x ^ d.1) * y ^ d.2
    rw [Finset.sum_map]
    apply Finset.sum_congr rfl
    intro d _
    simp only [Equiv.toEmbedding_apply, Equiv.symm_apply_apply, Fin.prod_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, ← mul_assoc]
    rfl

end SpecialTransformations.Section8
end PolynomialShapes

section BoundedPolynomialTies

/-! A finite polynomial shape bounds both the output powers and the
input orders appearing in the local equality between two terms. -/

set_option backward.isDefEq.respectTransparency false

open Filter Topology Polynomial

namespace SpecialTransformations.Section8

variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]

theorem shapedPolynomial_natDegree_le (D : Finset (ℕ × ℕ)) (c : ↥D → K) :
    (shapedPolynomial D c).natDegree ≤ D.sup Prod.snd := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  simp only [shapedPolynomial, Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro d _
  have hd : d.val.2 < j := lt_of_le_of_lt (Finset.le_sup d.property) hj
  simp [Polynomial.coeff_monomial, hd.ne, hd.ne.symm]

theorem shapedPolynomial_coeff_natDegree_le (D : Finset (ℕ × ℕ)) (c : ↥D → K) (j : ℕ) :
    ((shapedPolynomial D c).coeff j).natDegree ≤ D.sup Prod.fst := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro e he
  simp only [shapedPolynomial, Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro d _
  have hd : d.val.1 < e := lt_of_le_of_lt (Finset.le_sup d.property) he
  by_cases h : d.val.2 = j
  · simp [Polynomial.coeff_monomial, h, hd.ne, hd.ne.symm]
  · simp [Polynomial.coeff_monomial, h, Ne.symm h]

private theorem rootMultiplicity_le_degree (p : Polynomial K) (hp : p ≠ 0) (a : K) :
    p.rootMultiplicity a ≤ p.natDegree := by
  have h := Polynomial.natDegree_le_of_dvd (Polynomial.pow_rootMultiplicity_dvd p a) hp
  rwa [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one] at h

/-- The term powers in a local tie are bounded by the shape alone.
The two coefficients of lowest order are nonzero. -/
theorem eventually_shaped_root_tie [Valued K Γ]
    (D : Finset (ℕ × ℕ)) (c : ↥D → K) (hc : ∃ d, c d ≠ 0) (a : K) :
    let P := shapedPolynomial D c
    let e (i : ℕ) := (P.coeff i).rootMultiplicity a
    let b (i : ℕ) := ((P.coeff i).comp (X + C a)).trailingCoeff
    ∀ᶠ x in 𝓝 a, x ≠ a → ∀ y : K, y ≠ 0 → (P.map (Polynomial.evalRingHom x)).eval y = 0 →
      ∃ i j : ℕ, i < j ∧ j ≤ D.sup Prod.snd ∧
        e i ≤ D.sup Prod.fst ∧ e j ≤ D.sup Prod.fst ∧ b i ≠ 0 ∧ b j ≠ 0 ∧
        (Valued.v (x - a) ^ e i * Valued.v (b i)) * Valued.v y ^ i =
          (Valued.v (x - a) ^ e j * Valued.v (b j)) * Valued.v y ^ j := by
  dsimp only
  let P := shapedPolynomial D c
  have hin (i : ℕ) (hi : i ∈ P.support) : (P.coeff i).rootMultiplicity a ≤ D.sup Prod.fst :=
    (rootMultiplicity_le_degree _ (Polynomial.mem_support_iff.mp hi) a).trans
      (shapedPolynomial_coeff_natDegree_le D c i)
  have hout (i : ℕ) (hi : i ∈ P.support) : i ≤ D.sup Prod.snd :=
    (Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hi)).trans
      (shapedPolynomial_natDegree_le D c)
  have htrail (i : ℕ) (hi : i ∈ P.support) :
      ((P.coeff i).comp (X + C a)).trailingCoeff ≠ 0 := by
    have he : ((P.coeff i) /ₘ (X - C a) ^ (P.coeff i).rootMultiplicity a).eval a =
        ((P.coeff i).comp (X + C a)).trailingCoeff := Polynomial.eval_divByMonic_eq_trailingCoeff_comp
    rw [← he]
    exact Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero a (Polynomial.mem_support_iff.mp hi)
  filter_upwards [eventually_specialized_root_tie P (shapedPolynomial_ne_zero hc) a] with x hx
  intro hxa y hy hroot
  obtain ⟨i, hi, j, hj, hne, he⟩ := hx hxa y hy hroot
  rcases lt_or_gt_of_ne hne with hij | hji
  · exact ⟨i, j, hij, hout j hj, hin i hi, hin j hj, htrail i hi, htrail j hj, he⟩
  · exact ⟨j, i, hji, hout i hi, hin j hj, hin i hi, htrail j hj, htrail i hi, he.symm⟩

end SpecialTransformations.Section8
end BoundedPolynomialTies

section UnaryGraphPolynomial

/-! A definable unary graph satisfies a nonzero bivariate polynomial
relation. The polynomial is obtained from the existing Section 4
finite-cover theorem. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace SpecialTransformations.Section8

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def unaryScalarGraph (f : VFType (M := M) → VFType (M := M)) : Set (Fin 2 → M) :=
  {z | ∃ x : VFType (M := M), x.val = z 0 ∧ (f x).val = z 1}

private theorem mem_unaryScalarGraph (f : VFType (M := M) → VFType (M := M))
    (z : Fin 2 → VFType (M := M)) :
    vfValues z ∈ unaryScalarGraph f ↔ z 1 = f (z 0) := by
  constructor
  · rintro ⟨x, hx, hy⟩
    have he : x = z 0 := Subtype.ext hx
    exact (Subtype.ext hy).symm.trans (congrArg f he)
  · intro he
    exact ⟨z 0, rfl, congrArg Subtype.val he.symm⟩

private noncomputable def unaryGraphObject {S : Set M} {f : VFType (M := M) → VFType (M := M)}
    (hf : S.Definable LRV (unaryScalarGraph f)) : DefSet (rawMixedSpace (M := M) 2 0) S where
  carrier := {p | vfValues p.1 ∈ unaryScalarGraph f}
  definable := by
    let P := rawMixedSpace (M := M) 2 0
    have h := (P.definable_domain S).inter (hf.preimage_comp (Sum.inl : Fin 2 → Fin 2 ⊕ Fin 0))
    change S.Definable LRV (P.preimage {p | vfValues p.1 ∈ unaryScalarGraph f})
    convert h using 1
    ext z
    have he (hz : z ∈ P.domain) : vfValues (P.decode ⟨z, hz⟩).1 = z ∘ Sum.inl :=
      funext (fun i => congrFun (mixedValues_decode ⟨z, hz⟩) (.inl i))
    constructor
    · rintro ⟨hz, hmem⟩
      exact ⟨hz, Eq.mp (congrArg (fun x => x ∈ unaryScalarGraph f) (he hz)) hmem⟩
    · rintro ⟨hz, hmem⟩
      exact ⟨hz, Eq.mpr (congrArg (fun x => x ∈ unaryScalarGraph f) (he hz)) hmem⟩

theorem unary_graph_polynomial_relation (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) {S : Set M} (hsmall : Cardinal.mk S < κ)
    (f : VFType (M := M) → VFType (M := M)) (hf : S.Definable LRV (unaryScalarGraph f)) :
    ∃ P : MvPolynomial (Fin 2) (vfParameterField S), P ≠ 0 ∧
      ∀ x : VFType (M := M), P.eval₂ (vfParameterField S).subtype ![x, f x] = 0 := by
  let A := unaryGraphObject hf
  have hsort : ∀ z ∈ unaryScalarGraph f, ∀ i, iVF (z i) := by
    rintro z ⟨x, hx, hy⟩ i
    fin_cases i
    · exact hx ▸ x.property
    · exact hy ▸ (f x).property
  have hA := raw_definableOver_sorted hc S (fun _ => .vf) _ hf hsort
  obtain ⟨Γ, hΓ, v, hv⟩ := VFValued.exists_valuation_predV (M := M)
  letI := hΓ
  letI : Valued (VFType (M := M)) Γ := Valued.mk' v
  have hdep (p : A) : ¬ AlgebraicIndependent (vfParameterField S) (p.val.1 ∘ id) := by
    intro h
    let a := p.val.1
    have ha : AlgebraicIndependent (vfParameterField S) a := h
    have hag : vfValues a ∈ unaryScalarGraph f := p.property
    obtain ⟨D, hcentre, hD⟩ := independent_definable_contains_polydisc hv S _ hA a ha hag
    have hinf := D.side_infinite (model_valuation_nontrivial hv) (1 : Fin 2)
    have hsub : ¬ D.side 1 ⊆ {a 1} := fun hsub => hinf ((Set.finite_singleton _).subset hsub)
    obtain ⟨y, hy, hya⟩ := Set.not_subset.mp hsub
    let z : Fin 2 → VFType (M := M) := ![a 0, y]
    have hz : z ∈ D.carrier := by
      intro i
      fin_cases i
      · have hr : 0 < v (D.step 0) := pos_iff_ne_zero.mpr (v.ne_zero_iff.mpr (D.step_ne_zero 0))
        change v (a 0 - D.centre 0) < v (D.step 0)
        simpa only [hcentre, sub_self, map_zero] using hr
      · exact hy
    have hfa := (mem_unaryScalarGraph f a).mp hag
    have hfz := (mem_unaryScalarGraph f z).mp (hD z hz)
    apply hya
    change y = a 1
    exact hfz.trans hfa.symm
  obtain ⟨P, hP, hp⟩ :=
    exists_polynomial_vanishing_on_selection hs hsmall A id hdep
  refine ⟨P, hP, fun x => ?_⟩
  let p : A := ⟨(![x, f x], Fin.elim0), ⟨x, rfl, rfl⟩⟩
  exact hp p

end SpecialTransformations.Section8
end UnaryGraphPolynomial

section PolynomialShapeDefinability

/-! A fixed shape gives one formula for the existence of a nonzero
polynomial vanishing along a unary graph fibre. Compactness selects
finitely many shapes once these formulas cover the parameter space. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3
open scoped BigOperators

namespace SpecialTransformations.Section8

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

private def vfTupleSet (ι : Type) : Set (ι → M) := {z | ∀ i, iVF (z i)}

private theorem vfTupleSet_definable (S : Set M) (ι : Type) [Finite ι] :
    S.Definable LRV (vfTupleSet ι) := by
  change S.Definable LRV {z : ι → M | ∀ i, iVF (z i)}
  rw [Set.ofPred_forall]
  exact Set.definable_iInter_of_finite (fun i => ((definableAt_sort S .vf).raw_definable).preimage_comp
    (fun _ : Fin 1 => i))

private noncomputable def shapeValue (D : Finset (ℕ × ℕ)) (z : ↥D ⊕ Fin 2 → VFType (M := M)) : VFType (M := M) :=
  ∑ d : ↥D, (z (.inl d) * z (.inr 0) ^ d.val.1) * z (.inr 1) ^ d.val.2

def shapeZeroSet (D : Finset (ℕ × ℕ)) : Set ((↥D ⊕ Fin 2) → M) :=
  {z | ∃ hz : ∀ i, iVF (z i), shapeValue D (fun i => ⟨z i, hz i⟩) = 0}

theorem mem_shapeZeroSet_iff_eval (D : Finset (ℕ × ℕ))
    (c : ↥D → VFType (M := M)) (x y : VFType (M := M)) :
    Sum.elim (fun d => (c d).val) ![x.val, y.val] ∈ shapeZeroSet D ↔
      ((shapedPolynomial D c).map (Polynomial.evalRingHom x)).eval y = 0 := by
  let a : ↥D ⊕ Fin 2 → VFType (M := M) := Sum.elim c ![x, y]
  let z := Sum.elim (fun d => (c d).val) ![x.val, y.val]
  have hval (i : ↥D ⊕ Fin 2) : (a i).val = z i := by
    cases i with
    | inl j => rfl
    | inr j => fin_cases j <;> rfl
  have he (hz : ∀ i, iVF (z i)) : (fun i => (⟨z i, hz i⟩ : VFType (M := M))) = a :=
    funext (fun i => Subtype.ext (hval i).symm)
  have hsort (i : ↥D ⊕ Fin 2) : iVF (z i) := hval i ▸ (a i).property
  rw [shapedPolynomial_eval]
  constructor
  · rintro ⟨hz, h⟩
    rw [he hz] at h
    exact h
  · intro h
    refine ⟨hsort, ?_⟩
    rw [he hsort]
    exact h

theorem shapeZeroSet_definable (S : Set M) (D : Finset (ℕ × ℕ)) :
    S.Definable LRV (shapeZeroSet D) := by
  let I := ↥D ⊕ Fin 2
  let q : FreeCommRing I := ∑ d : ↥D,
    (FreeCommRing.of (.inl d) * FreeCommRing.of (.inr 0) ^ d.val.1) *
      FreeCommRing.of (.inr 1) ^ d.val.2
  let t : LRV.Term I := RingSyntax.ofRingTerm (FirstOrder.Ring.termOfFreeCommRing q)
  let zero : LRV.Term I := .func Fn.vfZero Fin.elim0
  have he : (∅ : Set M).Definable LRV {z : I → M | t.realize z = zero.realize z} := by
    refine Set.empty_definable_iff.mpr ⟨t.equal zero, ?_⟩
    ext z
    exact Formula.realize_equal.symm
  have eval (z : I → M) (hz : ∀ i, iVF (z i)) :
      t.realize z = (shapeValue D (fun i => ⟨z i, hz i⟩)).val := by
    let a : I → VFType (M := M) := fun i => ⟨z i, hz i⟩
    change t.realize (fun i => (a i).val) = (shapeValue D a).val
    dsimp only [t]
    rw [RingSyntax.realizes, FirstOrder.Ring.realize_termOfFreeCommRing]
    simp only [q, shapeValue, map_sum, map_mul, map_pow, FreeCommRing.lift_of]
  convert (vfTupleSet_definable S I).inter (he.mono (Set.empty_subset S)) using 1
  ext z
  have hz : zero.realize z = (0 : VFType (M := M)).val := by
    change Structure.funMap (L := LRV) Fn.vfZero _ = _
    congr 1
    funext j
    exact j.elim0
  constructor
  · rintro ⟨hs, h⟩
    exact ⟨hs, (eval z hs).trans (congrArg Subtype.val h) |>.trans hz.symm⟩
  · rintro ⟨hs, h⟩
    exact ⟨hs, Subtype.ext ((eval z hs).symm.trans (h.trans hz))⟩

/-- A coefficient tuple is quantified, with at least one nonzero entry.
The competing tuple ranges over the whole graph fibre. -/
def shapeAdmissible {k : ℕ} (D : Finset (ℕ × ℕ)) (G : Set (Fin k ⊕ Fin 2 → M)) :
    Set (Fin k → M) :=
  {b | ∃ c : ↥D → M, c ∈ vfTupleSet _ ∧ (¬ ∀ i, c i = iVFZero) ∧
    ¬ ∃ w : Fin 2 → M, Sum.elim b w ∈ G ∧ Sum.elim c w ∉ shapeZeroSet D}

theorem shapeAdmissible_definable {S : Set M} {k : ℕ} (D : Finset (ℕ × ℕ))
    {G : Set (Fin k ⊕ Fin 2 → M)} (hG : S.Definable LRV G) :
    S.Definable LRV (shapeAdmissible D G) := by
  let I := Fin k ⊕ ↥D
  let toGraph : Fin k ⊕ Fin 2 → I ⊕ Fin 2 := Sum.elim (Sum.inl ∘ Sum.inl) Sum.inr
  let toPoly : ↥D ⊕ Fin 2 → I ⊕ Fin 2 := Sum.elim (Sum.inl ∘ Sum.inr) Sum.inr
  have hBad := ((hG.preimage_comp toGraph).inter
    ((shapeZeroSet_definable S D).preimage_comp toPoly).compl).exists_of_finite
  have hCoeffs := (vfTupleSet_definable S (↥D)).preimage_comp (Sum.inr : ↥D → I)
  have hZero : S.DefinableFun LRV (fun _ : I → M => iVFZero) :=
    DefinableConstants.constant (DefinableConstants.function_symbol
      (L := LRV) Fn.vfZero Fin.elim0 (fun j => j.elim0))
  have hAllZero : S.Definable LRV {z : I → M | ∀ i : ↥D, z (.inr i) = iVFZero} := by
    rw [Set.ofPred_forall]
    exact Set.definable_iInter_of_finite (fun i =>
      (Set.DefinableFun.proj LRV (i := (Sum.inr i : I))).ofPred_eq hZero)
  convert (hCoeffs.inter (hAllZero.compl.inter hBad.compl)).exists_of_finite using 1
  ext b
  have hg (c : ↥D → M) (w : Fin 2 → M) :
      Sum.elim (Sum.elim b c) w ∘ toGraph = Sum.elim b w := by
    funext i
    cases i <;> rfl
  have hp (c : ↥D → M) (w : Fin 2 → M) :
      Sum.elim (Sum.elim b c) w ∘ toPoly = Sum.elim c w := by
    funext i
    cases i <;> rfl
  change (∃ c : ↥D → M, c ∈ vfTupleSet _ ∧ (¬ ∀ i, c i = iVFZero) ∧
      ¬ ∃ w : Fin 2 → M, Sum.elim b w ∈ G ∧ Sum.elim c w ∉ shapeZeroSet D) ↔
    ∃ c : ↥D → M, c ∈ vfTupleSet _ ∧ (¬ ∀ i, c i = iVFZero) ∧
      ¬ ∃ w : Fin 2 → M, (Sum.elim (Sum.elim b c) w ∘ toGraph) ∈ G ∧
        (Sum.elim (Sum.elim b c) w ∘ toPoly) ∉ shapeZeroSet D
  simp only [hg, hp]

theorem finite_admissible_shapes {κ : Cardinal} (hs : Saturated M κ)
    {S : Set M} (hsmall : Cardinal.mk S < κ) {k : ℕ}
    {G : Set (Fin k ⊕ Fin 2 → M)} (hG : S.Definable LRV G)
    (hcover : ∀ b ∈ vfTupleSet (M := M) (Fin k), ∃ D : Finset (ℕ × ℕ), b ∈ shapeAdmissible D G) :
    ∃ T : Finset (Finset (ℕ × ℕ)), ∀ b ∈ vfTupleSet (M := M) (Fin k),
      ∃ D ∈ T, b ∈ shapeAdmissible D G := by
  classical
  let family : Set (Set (Fin k → M)) := Set.range (fun D => shapeAdmissible D G)
  obtain ⟨C, hC, hsub, hcov⟩ := hs.definable_finite_subcover_tuple S hsmall
    (vfTupleSet (Fin k)) (vfTupleSet_definable S (Fin k)) family
    (by rintro _ ⟨D, rfl⟩; exact shapeAdmissible_definable D hG)
    (by intro b hb; obtain ⟨D, hD⟩ := hcover b hb; exact ⟨_, ⟨D, rfl⟩, hD⟩)
  letI : Fintype C := hC.fintype
  let shape (c : C) := Classical.choose (hsub c.property)
  have hshape (c : C) : shapeAdmissible (shape c) G = c.val := Classical.choose_spec (hsub c.property)
  refine ⟨Finset.univ.image shape, fun b hb => ?_⟩
  obtain ⟨c, hc, hbc⟩ := hcov b hb
  let c' : C := ⟨c, hc⟩
  exact ⟨shape c', Finset.mem_image.mpr ⟨c', Finset.mem_univ _, rfl⟩, (hshape c').symm ▸ hbc⟩

end SpecialTransformations.Section8
end PolynomialShapeDefinability

section UniformGraphShapes

/-! A definable family of unary scalar graphs admits finitely many
polynomial shapes. The coefficients can vary from fibre to fibre. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace SpecialTransformations.Section8

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {k : ℕ}

def unaryScalarFamilyGraph (f : (Fin k → VFType (M := M)) → VFType (M := M) → VFType (M := M)) :
    Set ((Fin k ⊕ Fin 2) → M) :=
  Set.range (fun p : (Fin k → VFType (M := M)) × VFType (M := M) =>
    Sum.elim (vfValues p.1) ![p.2.val, (f p.1 p.2).val])

private theorem scalarFamilyGraph_fibre
    (f : (Fin k → VFType (M := M)) → VFType (M := M) → VFType (M := M))
    (b : Fin k → VFType (M := M)) :
    {z | Sum.elim (vfValues b) z ∈ unaryScalarFamilyGraph f} = unaryScalarGraph (f b) := by
  ext z
  constructor
  · rintro ⟨⟨p, x⟩, he⟩
    have hp : p = b := vfValues_injective (funext (fun i => congrFun he (.inl i)))
    subst p
    exact ⟨x, congrFun he (.inr 0), congrFun he (.inr 1)⟩
  · rintro ⟨x, hx, hy⟩
    refine ⟨(b, x), ?_⟩
    funext i
    cases i with
    | inl j => rfl
    | inr j =>
      fin_cases j
      · exact hx
      · exact hy

theorem unaryScalarFamilyGraph_fibre_definable {S : Set M}
    {f : (Fin k → VFType (M := M)) → VFType (M := M) → VFType (M := M)}
    (hf : S.Definable LRV (unaryScalarFamilyGraph f)) (b : Fin k → VFType (M := M)) :
    (S ∪ Set.range (vfValues b)).Definable LRV (unaryScalarGraph (f b)) := by
  rw [← scalarFamilyGraph_fibre f b]
  apply (hf.mono Set.subset_union_left).preimage_map
  intro i
  cases i with
  | inl j =>
    exact LRV.definableFun_const (Fin 2) (Or.inr (Set.mem_range_self j))
  | inr j => exact Set.DefinableFun.proj LRV

theorem shapeAdmissible_scalarFamily_iff
    (f : (Fin k → VFType (M := M)) → VFType (M := M) → VFType (M := M))
    (b : Fin k → VFType (M := M)) (D : Finset (ℕ × ℕ)) :
    vfValues b ∈ shapeAdmissible D (unaryScalarFamilyGraph f) ↔
      ∃ c : ↥D → VFType (M := M), (∃ i, c i ≠ 0) ∧
        ∀ x : VFType (M := M),
          ((shapedPolynomial D c).map (Polynomial.evalRingHom x)).eval (f b x) = 0 := by
  classical
  constructor
  · rintro ⟨c, hc, hnonzero, hbad⟩
    let a : ↥D → VFType (M := M) := fun i => ⟨c i, hc i⟩
    refine ⟨a, ?_, ?_⟩
    · obtain ⟨i, hi⟩ := not_forall.mp hnonzero
      exact ⟨i, fun h => hi (congrArg Subtype.val h)⟩
    · intro x
      apply (mem_shapeZeroSet_iff_eval D a x (f b x)).mp
      by_contra h
      exact hbad ⟨![x.val, (f b x).val], ⟨(b, x), rfl⟩, h⟩
  · rintro ⟨a, ⟨i, hi⟩, ha⟩
    refine ⟨fun j => (a j).val, fun j => (a j).property, ?_, ?_⟩
    · exact fun h => hi (Subtype.ext (h i))
    · rintro ⟨w, hw, hnot⟩
      have hmem : w ∈ unaryScalarGraph (f b) :=
        (Set.ext_iff.mp (scalarFamilyGraph_fibre f b) w).mp hw
      obtain ⟨x, hx, hy⟩ := hmem
      have he : (![x.val, (f b x).val] : Fin 2 → M) = w := by
        funext j
        fin_cases j
        · exact hx
        · exact hy
      apply hnot
      rw [← he]
      exact (mem_shapeZeroSet_iff_eval D a x (f b x)).mpr (ha x)

theorem unary_family_has_finite_polynomial_shapes
    (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    {S : Set M} (hsmall : Cardinal.mk S < κ)
    (f : (Fin k → VFType (M := M)) → VFType (M := M) → VFType (M := M))
    (hf : S.Definable LRV (unaryScalarFamilyGraph f)) :
    ∃ T : Finset (Finset (ℕ × ℕ)), ∀ b : Fin k → VFType (M := M),
      ∃ D ∈ T, ∃ c : ↥D → VFType (M := M), (∃ i, c i ≠ 0) ∧
        ∀ x : VFType (M := M),
          ((shapedPolynomial D c).map (Polynomial.evalRingHom x)).eval (f b x) = 0 := by
  have hcover (z : Fin k → M) (hz : ∀ i, iVF (z i)) :
      ∃ D, z ∈ shapeAdmissible D (unaryScalarFamilyGraph f) := by
    let b : Fin k → VFType (M := M) := fun i => ⟨z i, hz i⟩
    let B := S ∪ Set.range (vfValues b)
    let E := vfParameterField B
    obtain ⟨P, hP, hPzero⟩ := unary_graph_polynomial_relation hc hs
      (small_union_range hκ S hsmall (vfValues b)) (f b) (unaryScalarFamilyGraph_fibre_definable hf b)
    let p := MvPolynomial.map E.subtype P
    have hp : p ≠ 0 := by
      intro h
      apply hP
      exact (MvPolynomial.map_injective E.subtype Subtype.val_injective) (h.trans (map_zero _).symm)
    obtain ⟨D, c, hc', he⟩ := mvPolynomial_has_shape p hp
    refine ⟨D, (shapeAdmissible_scalarFamily_iff f b D).mpr ⟨c, hc', ?_⟩⟩
    intro x
    rw [← he]
    change MvPolynomial.eval ![x, f b x] (MvPolynomial.map E.subtype P) = 0
    rw [MvPolynomial.eval_map]
    exact hPzero x
  obtain ⟨T, hT⟩ := finite_admissible_shapes hs hsmall hf hcover
  refine ⟨T, fun b => ?_⟩
  obtain ⟨D, hD, hb⟩ := hT (vfValues b) (fun i => (b i).property)
  exact ⟨D, hD, (shapeAdmissible_scalarFamily_iff f b D).mp hb⟩

end SpecialTransformations.Section8
end UniformGraphShapes
