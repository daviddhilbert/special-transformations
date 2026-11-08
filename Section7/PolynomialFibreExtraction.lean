import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Data.Set.Finite.Lattice

/-!
# Extracting a genuine polynomial equation from a finite fibre

The elementary field part of Lemma 7.4. A finite list of polynomial tests
can isolate a nonzero field point only if a nonzero polynomial vanishes
there. In characteristic zero, a suitable iterated derivative of that
polynomial still vanishes and its next derivative does not. These facts do
not supply the original-base RV normal form; that bridge is separate.
-/

namespace SpecialTransformations.Section7

section Specialize

variable {R S σ : Type*} [CommRing R] [CommRing S] [DecidableEq σ]

/-- Keep variable `i`, evaluate every other variable, and map the
coefficients. The coefficient map may be the actual residue projection. -/
noncomputable def specializeVariable (f : R →+* S) (a : σ → S) (i : σ) :
    MvPolynomial σ R →+* Polynomial S :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp f)
    (fun j => if j = i then Polynomial.X else Polynomial.C (a j))

theorem eval_specializeVariable (f : R →+* S) (a : σ → S) (i : σ)
    (p : MvPolynomial σ R) (x : S) :
    (specializeVariable f a i p).eval x = MvPolynomial.eval₂ f (Function.update a i x) p := by
  have he : (Polynomial.evalRingHom x).comp (specializeVariable f a i) =
      MvPolynomial.eval₂Hom f (Function.update a i x) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [specializeVariable]
    · intro j
      by_cases hj : j = i <;> simp [specializeVariable, Function.update, hj]
  exact RingHom.congr_fun he p

theorem derivative_specializeVariable (f : R →+* S) (a : σ → S) (i : σ)
    (p : MvPolynomial σ R) :
    (specializeVariable f a i p).derivative = specializeVariable f a i (MvPolynomial.pderiv i p) := by
  induction p using MvPolynomial.induction_on with
  | C r => simp [specializeVariable]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp =>
    rw [map_mul, Polynomial.derivative_mul, MvPolynomial.pderiv_mul, map_add,
      map_mul, map_mul, hp]
    by_cases hj : j = i
    · subst j
      simp [specializeVariable]
    · simp [specializeVariable, hj, MvPolynomial.pderiv_X_of_ne hj]

theorem iterate_derivative_specializeVariable (f : R →+* S) (a : σ → S) (i : σ)
    (p : MvPolynomial σ R) (k : ℕ) :
    (Polynomial.derivative^[k]) (specializeVariable f a i p) =
      specializeVariable f a i (((MvPolynomial.pderiv i)^[k]) p) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
      derivative_specializeVariable]

end Specialize

variable {K : Type*} [Field K]

theorem exists_nonzero_root_of_finite_polynomial_pattern [Infinite K]
    {ι : Type*} [Finite ι] (P : ι → Polynomial K) (x : K)
    (hfin : {y | y ≠ 0 ∧ ∀ i, (P i).IsRoot y ↔ (P i).IsRoot x}.Finite) :
    ∃ i, P i ≠ 0 ∧ (P i).IsRoot x := by
  classical
  by_contra h
  let Z (i : ι) : Set K := {y | P i ≠ 0 ∧ (P i).IsRoot y}
  have hZ (i : ι) : (Z i).Finite := by
    by_cases hi : P i = 0
    · have he : Z i = ∅ := by ext y; simp [Z, hi]
      rw [he]
      exact Set.finite_empty
    · exact (Polynomial.finite_setOfPred_isRoot hi).subset (fun _ hy => hy.2)
  let U : Set K := {0} ∪ ⋃ i, Z i
  have hU : U.Finite := (Set.finite_singleton 0).union (Set.finite_iUnion hZ)
  have hcover : (Set.univ : Set K) ⊆ U ∪
      {y | y ≠ 0 ∧ ∀ i, (P i).IsRoot y ↔ (P i).IsRoot x} := by
    intro y _
    by_cases hy : y ∈ U
    · exact Or.inl hy
    · refine Or.inr ⟨fun hz => hy (Or.inl (Set.mem_singleton_iff.mpr hz)), ?_⟩
      intro i
      by_cases hi : P i = 0
      · simp [hi, Polynomial.IsRoot]
      · exact iff_of_false
          (fun hiy => hy (Or.inr (Set.mem_iUnion.mpr ⟨i, hi, hiy⟩)))
          (fun hix => h ⟨i, hi, hix⟩)
  exact Set.infinite_univ ((hU.union hfin).subset hcover)

theorem exists_iterate_derivative_simpleRoot [CharZero K] {p : Polynomial K}
    {x : K} (hp : p ≠ 0) (hx : p.IsRoot x) :
    ∃ k, ((Polynomial.derivative^[k]) p).IsRoot x ∧
      ¬ (Polynomial.derivative ((Polynomial.derivative^[k]) p)).IsRoot x := by
  let m := p.rootMultiplicity x
  have hm : 0 < m := (Polynomial.rootMultiplicity_pos hp).mpr hx
  have hk : m - 1 < p.rootMultiplicity x := by change m - 1 < m; omega
  have hm' : m - 1 + 1 = m := Nat.sub_add_cancel (Nat.succ_le_of_lt hm)
  refine ⟨m - 1, Polynomial.isRoot_iterate_derivative_of_lt_rootMultiplicity hk, ?_⟩
  have hiter := Function.iterate_succ_apply'
    (f := (Polynomial.derivative : Polynomial K → Polynomial K)) (m - 1) p
  change (Polynomial.derivative^[m - 1 + 1]) p = _ at hiter
  rw [hm'] at hiter
  rw [← hiter]
  intro hmroot
  have hall : ∀ j ≤ m, ((Polynomial.derivative^[j]) p).IsRoot x := by
    intro j hj
    rcases lt_or_eq_of_le hj with hlt | rfl
    · exact Polynomial.isRoot_iterate_derivative_of_lt_rootMultiplicity hlt
    · exact hmroot
  exact (lt_irrefl m) (Polynomial.lt_rootMultiplicity_of_isRoot_iterate_derivative hp hall)

end SpecialTransformations.Section7
