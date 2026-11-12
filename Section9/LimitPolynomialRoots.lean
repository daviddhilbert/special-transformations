module

public import Section9.LimitPolynomialNormalization
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.List.OfFn

@[expose] public section

/-! The bounded output chart for a nonzero bivariate polynomial. The
candidate centres are the roots of the first nonzero input row. -/

open scoped BigOperators

namespace SpecialTransformations.Section9

variable {K G : Type*} [Field K] [IsAlgClosed K] [LinearOrderedCommGroupWithZero G]

theorem exists_bounded_root_candidates (v : Valuation K G)
    (D : Finset (ℕ × ℕ)) (hD : D.Nonempty) (c : ℕ × ℕ → K) (hc : ∀ d ∈ D, c d ≠ 0) :
    ∃ B : Set K, B.Finite ∧ ∀ r : K, r ≠ 0 → ∃ δ : K, δ ≠ 0 ∧
      ∀ x y : K, x ≠ 0 → v x < v δ → v y ≤ 1 →
        (∑ d ∈ D, c d * x ^ d.1 * y ^ d.2) = 0 → ∃ b ∈ B, v (y - b) < v r := by
  classical
  obtain ⟨d₀, hd₀, hmin⟩ := Finset.exists_min_image D Prod.fst hD
  let L := D.filter (fun d => d.1 = d₀.1)
  let H := D.filter (fun d => d₀.1 < d.1)
  let p : Polynomial K := ∑ d ∈ L, Polynomial.monomial d.2 (c d)
  have hdL : d₀ ∈ L := Finset.mem_filter.mpr ⟨hd₀, rfl⟩
  have hcoeff : p.coeff d₀.2 = c d₀ := by
    simp only [p, Polynomial.finsetSum_coeff]
    rw [Finset.sum_eq_single d₀]
    · simp [Polynomial.coeff_monomial]
    · intro e he hne
      have he₂ : e.2 ≠ d₀.2 := fun h => hne (Prod.ext (Finset.mem_filter.mp he).2 h)
      simp [Polynomial.coeff_monomial, he₂, Ne.symm he₂]
    · intro h
      exact (h hdL).elim
  have hp : p ≠ 0 := by
    intro he
    rw [he, Polynomial.coeff_zero] at hcoeff
    exact hc d₀ hd₀ hcoeff.symm
  have heval (y : K) : p.eval y = ∑ d ∈ L, c d * y ^ d.2 := by
    change Polynomial.evalRingHom y (∑ d ∈ L, Polynomial.monomial d.2 (c d)) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro d _
    exact Polynomial.eval_monomial
  let roots := p.roots.toList
  let b (i : Fin roots.length) : K := roots[i]
  have hfactor (y : K) : p.eval y = p.leadingCoeff * ∏ i, (y - b i) := by
    rw [(IsAlgClosed.splits p).eval_eq_prod_roots, ← Multiset.prod_map_toList]
    change p.leadingCoeff * (roots.map (y - ·)).prod = _
    rw [← List.ofFn_getElem_eq_map, List.prod_ofFn]
    rfl
  refine ⟨Set.range b, Set.finite_range b, fun r hr => ?_⟩
  obtain ⟨δ, hδ, hbound⟩ := exists_input_radius_near_factor v Finset.univ H p.leadingCoeff
    (Polynomial.leadingCoeff_ne_zero.mpr hp) b c (fun d => d.1 - d₀.1 - 1) Prod.snd r hr
  refine ⟨δ, hδ, fun x y hx hsmall hy hroot => ?_⟩
  have heq := factor_input_power D c d₀.1 hmin x y
  change (∑ d ∈ D, c d * x ^ d.1 * y ^ d.2) =
    x ^ d₀.1 * ((∑ d ∈ L, c d * y ^ d.2) +
      x * ∑ d ∈ H, c d * x ^ (d.1 - d₀.1 - 1) * y ^ d.2) at heq
  rw [← heval y, hfactor y] at heq
  have hz := (mul_eq_zero.mp (heq.symm.trans hroot)).resolve_left (pow_ne_zero _ hx)
  obtain ⟨i, _, hi⟩ := hbound x y hsmall hy hz
  exact ⟨b i, Set.mem_range_self i, hi⟩

end SpecialTransformations.Section9
