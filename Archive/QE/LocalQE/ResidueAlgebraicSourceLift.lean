import ResidueAlgebraicRoot

/-!
Adjoin a lift of an algebraic residue class on both sides.

A monic integral base polynomial lifting the residue minimal polynomial is
the input. Neither a source root nor a target root is assumed. Algebraic
closedness supplies both roots with their prescribed RV classes, and the
finite-degree calculation supplies the actual embedding of the new field.
-/

namespace ResidueAlgebraicTransport

open scoped BigOperators IntermediateField
open Polynomial ResidueTranscendentalTransport

variable {K L Γ Δ : Type*} [Field K] [Field L]
  [LinearOrderedCommGroupWithZero Γ] [LinearOrderedCommGroupWithZero Δ]

theorem eval_lt_one_of_lifted_minpoly (v : Valuation K Γ) (F : Subfield K)
    (κ : Subfield (Residue v)) {u : K} (hu : v u = 1)
    (p : Polynomial F) (hc : ∀ i : ℕ, v (p.coeff i : K) ≤ 1)
    (hcoeff : ∀ i : ℕ, M7.vres v (p.coeff i : K) (hc i) =
      κ.subtype ((minpoly κ (M7.vres v u hu.le)).coeff i))
    (hdegree : (minpoly κ (M7.vres v u hu.le)).natDegree = p.natDegree) :
    v (p.eval₂ F.subtype u) < 1 := by
  let z := M7.vres v u hu.le
  let q : Polynomial κ := minpoly κ z
  let c : Fin (p.natDegree + 1) → K := fun i => (p.coeff i : K)
  have hc' : ∀ i, v (c i) ≤ 1 := fun i => hc i
  have ht : ∀ i, v (c i * u ^ (i : ℕ)) ≤ 1 := fun i => by
    simpa [map_mul, map_pow, hu] using hc' i
  have hs : v (∑ i, c i * u ^ (i : ℕ)) ≤ 1 := M7.val_sum_le_one' v ht
  have hresid : M7.vres v (∑ i, c i * u ^ (i : ℕ)) hs = q.eval₂ κ.subtype z := by
    rw [M7.vres_sum v ht]
    calc
      (∑ i, M7.vres v (c i * u ^ (i : ℕ)) (ht i)) =
          ∑ i : Fin (p.natDegree + 1), κ.subtype (q.coeff i) * z ^ (i : ℕ) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [M7.vres_mul v (hc' i) (M7.val_pow_le_one v hu.le i), M7.vres_pow v hu.le]
        exact congrArg (fun a => a * z ^ (i : ℕ)) (hcoeff i)
      _ = q.eval₂ κ.subtype z := by
        rw [eval₂_eq_fin_sum, show q.natDegree = p.natDegree from hdegree]
  have hzero : q.eval₂ κ.subtype z = 0 := minpoly.aeval κ z
  rw [hzero] at hresid
  have hsmall := (M7.vres_eq_zero_iff v _ hs).mp hresid
  rw [eval₂_eq_fin_sum]
  exact hsmall

theorem exists_unit_root_of_lifted_minpoly [IsAlgClosed K]
    (v : Valuation K Γ) (F : Subfield K)
    (κ : Subfield (Residue v)) {u : K} (hu : v u = 1)
    (p : Polynomial F) (hp : p.Monic) (hc : ∀ i : ℕ, v (p.coeff i : K) ≤ 1)
    (hcoeff : ∀ i : ℕ, M7.vres v (p.coeff i : K) (hc i) =
      κ.subtype ((minpoly κ (M7.vres v u hu.le)).coeff i))
    (hdegree : (minpoly κ (M7.vres v u hu.le)).natDegree = p.natDegree) :
    ∃ e : K, ∃ he : v e = 1, p.eval₂ F.subtype e = 0 ∧
      RVCalc.rv v e = RVCalc.rv v u ∧ M7.vres v e he.le = M7.vres v u hu.le := by
  have hsmall : v ((p.map F.subtype).eval u) < 1 := by
    rw [Polynomial.eval_map]
    exact eval_lt_one_of_lifted_minpoly v F κ hu p hc hcoeff hdegree
  obtain ⟨e, hepoly, herv⟩ := RVCalc.exists_root_rv_eq v (hp.map F.subtype) hsmall hu
  have he : v e = 1 := by
    have h := congrArg (RVCalc.vrv v) herv
    simpa only [RVCalc.vrv_rv, hu] using h
  refine ⟨e, he, ?_, herv, residue_eq_of_rv_eq v he hu herv⟩
  simpa only [Polynomial.IsRoot.def, Polynomial.eval_map] using hepoly

/-- The finite residue-algebraic adjoining step, with source and target roots
constructed. The polynomial-lifting input consists only of coefficient and
degree identities for the ordinary residue minimal polynomial. -/
theorem exists_adjoin_embedding_of_lifted_minpoly [IsAlgClosed K] [IsAlgClosed L]
    (v : Valuation K Γ) (w : Valuation L Δ)
    (F : Subfield K) (σ : F →+* L) (ρ : Residue v →+* Residue w)
    (κ : Subfield (Residue v))
    (hκ : ∀ (a : F) (ha : v (a : K) ≤ 1), M7.vres v (a : K) ha ∈ κ)
    (R : RVCalc.RV v → RVCalc.RV w → Prop)
    (hzero : R none none)
    (hmul : ∀ a b a' b', R a a' → R b b' →
      R (RVCalc.rvMul v a b) (RVCalc.rvMul w a' b'))
    (hintegral : ∀ a : F, v (a : K) ≤ 1 → w (σ a) ≤ 1)
    (hres : ∀ (a : F) (ha : v (a : K) ≤ 1) (hb : w (σ a) ≤ 1),
      ρ (M7.vres v (a : K) ha) = M7.vres w (σ a) hb)
    (hbase : ∀ a : F, R (RVCalc.rv v (a : K)) (RVCalc.rv w (σ a)))
    (hunit : ∀ (x : K) (y : L) (hx : v x = 1) (hy : w y = 1),
      ρ (M7.vres v x hx.le) = M7.vres w y hy.le → R (RVCalc.rv v x) (RVCalc.rv w y))
    {u : K} {a₀ : L} (hu : v u = 1) (ha₀ : w a₀ = 1)
    (p : Polynomial F) (hp : p.Monic) (hc : ∀ i : ℕ, v (p.coeff i : K) ≤ 1)
    (hcoeff : ∀ i : ℕ, M7.vres v (p.coeff i : K) (hc i) =
      κ.subtype ((minpoly κ (M7.vres v u hu.le)).coeff i))
    (hdegree : (minpoly κ (M7.vres v u hu.le)).natDegree = p.natDegree)
    (hvar : ρ (M7.vres v u hu.le) = M7.vres w a₀ ha₀.le) :
    ∃ e : K, v e = 1 ∧ RVCalc.rv v e = RVCalc.rv v u ∧
      ∃ g : F⟮e⟯ →+* L,
        Function.Injective g ∧
        (∀ a : F, g (algebraMap F F⟮e⟯ a) = σ a) ∧
        RVCalc.rv w (g (IntermediateField.AdjoinSimple.gen F e)) = RVCalc.rv w a₀ ∧
        ∀ x : F⟮e⟯, R (RVCalc.rv v (x : K)) (RVCalc.rv w (g x)) := by
  obtain ⟨e, he, hpe, herv, heres⟩ :=
    exists_unit_root_of_lifted_minpoly v F κ hu p hp hc hcoeff hdegree
  have hdegree' : (minpoly κ (M7.vres v e he.le)).natDegree = p.natDegree := by
    rw [heres]
    exact hdegree
  have hvar' : ρ (M7.vres v e he.le) = M7.vres w a₀ ha₀.le := by
    rw [heres]
    exact hvar
  exact ⟨e, he, herv, exists_field_embedding_with_root v w F σ ρ κ hκ R hzero hmul
    hintegral hres hbase hunit he ha₀ p hp hc hpe hdegree' hvar'⟩

end ResidueAlgebraicTransport

#print axioms ResidueAlgebraicTransport.eval_lt_one_of_lifted_minpoly
#print axioms ResidueAlgebraicTransport.exists_unit_root_of_lifted_minpoly
#print axioms ResidueAlgebraicTransport.exists_adjoin_embedding_of_lifted_minpoly
