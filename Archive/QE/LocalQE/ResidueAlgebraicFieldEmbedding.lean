import ResidueAlgebraicTransport

/-!
The actual finite unit field extension for Yin's residue-algebraic step.
Given roots e,d of the same transported monic polynomial, whose degree is the
minimal degree of the residue of e, construct F(e) → L and prove compatibility
with the prescribed partial RV relation on every element. Ordinary minimality
of the polynomial over F is proved from the residue calculation.

Existence of a target root with the prescribed residue is separate (the Hensel
input). This theorem does not assume a field extension map or RV transport.
-/

namespace ResidueAlgebraicTransport

open scoped BigOperators IntermediateField
open Polynomial ResidueTranscendentalTransport

variable {K L Γ Δ : Type*} [Field K] [Field L]
  [LinearOrderedCommGroupWithZero Γ] [LinearOrderedCommGroupWithZero Δ]

theorem powers_linearIndependent (v : Valuation K Γ) (w : Valuation L Δ)
    (F : Subfield K) (σ : F →+* L) (ρ : Residue v →+* Residue w)
    (hintegral : ∀ a : F, v (a : K) ≤ 1 → w (σ a) ≤ 1)
    (hres : ∀ (a : F) (ha : v (a : K) ≤ 1) (hb : w (σ a) ≤ 1),
      ρ (M7.vres v (a : K) ha) = M7.vres w (σ a) hb)
    {N : ℕ} {e : K} {d : L}
    (he : v e = 1) (hd : w d = 1) (hI : ResidueIndependent v F he N)
    (hvar : ρ (M7.vres v e he.le) = M7.vres w d hd.le) :
    LinearIndependent F (fun i : Fin N => e ^ (i : ℕ)) := by
  refine Fintype.linearIndependent_iff.mpr ?_
  intro c hc i
  by_contra hci
  have hnz := (nonzero_sums v w F σ ρ hintegral hres he hd hI ⟨i, hci⟩ hvar).1
  have hcF : ∀ a : F, algebraMap F K a = (a : K) := fun a => rfl
  exact hnz (by simpa only [Algebra.smul_def, hcF] using hc)

theorem exists_field_embedding (v : Valuation K Γ) (w : Valuation L Δ)
    (F : Subfield K) (σ : F →+* L) (ρ : Residue v →+* Residue w)
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
    {e : K} {d : L} (he : v e = 1) (hd : w d = 1)
    (p : Polynomial F) (hp : p.Monic)
    (hpe : p.eval₂ F.subtype e = 0) (hpd : p.eval₂ σ d = 0)
    (hI : ResidueIndependent v F he p.natDegree)
    (hvar : ρ (M7.vres v e he.le) = M7.vres w d hd.le) :
    ∃ g : F⟮e⟯ →+* L,
      Function.Injective g ∧
      (∀ a : F, g (algebraMap F F⟮e⟯ a) = σ a) ∧
      g (IntermediateField.AdjoinSimple.gen F e) = d ∧
      ∀ x : F⟮e⟯, R (RVCalc.rv v (x : K)) (RVCalc.rv w (g x)) := by
  letI : Algebra F L := σ.toAlgebra
  have heI : IsIntegral F e := ⟨p, hp, hpe⟩
  have hpmin : minpoly F e = p :=
    minpoly.eq_of_linearIndependent F e hp hpe p.natDegree
      (Polynomial.degree_eq_natDegree hp.ne_zero)
      (powers_linearIndependent v w F σ ρ hintegral hres he hd hI hvar)
  let pb : PowerBasis F F⟮e⟯ := IntermediateField.adjoin.powerBasis heI
  have hgenmin : minpoly F pb.gen = p := by
    change minpoly F (IntermediateField.AdjoinSimple.gen F e) = p
    rw [IntermediateField.minpoly_gen, hpmin]
  have hdroot : Polynomial.aeval d (minpoly F pb.gen) = 0 := by
    rw [hgenmin]
    exact hpd
  let g : F⟮e⟯ →ₐ[F] L := pb.lift d hdroot
  have hggen : g pb.gen = d := pb.lift_gen d hdroot
  refine ⟨g.toRingHom, g.injective, ?_, ?_, ?_⟩
  · intro a
    exact g.commutes a
  · exact hggen
  · intro x
    let c : Fin pb.dim → F := pb.basis.repr x
    have hI' : ResidueIndependent v F he pb.dim := by
      change ResidueIndependent v F he (minpoly F e).natDegree
      rw [hpmin]
      exact hI
    have hx : (∑ i, (c i : K) * e ^ (i : ℕ)) = (x : K) := by
      have h := congrArg (F⟮e⟯).val (pb.basis.sum_repr x)
      have hcoeff : ∀ a : F, (F⟮e⟯).val (algebraMap F F⟮e⟯ a) = (a : K) := fun a => rfl
      have hvx : (F⟮e⟯).val x = (x : K) := rfl
      simpa only [map_sum, pb.basis_eq_pow, Algebra.smul_def, map_mul, map_pow, hcoeff,
        show (F⟮e⟯).val pb.gen = e from rfl, hvx, c] using h
    have hg : (∑ i, σ (c i) * d ^ (i : ℕ)) = g x := by
      have h := congrArg g (pb.basis.sum_repr x)
      have hcoeff : ∀ a : F, g (algebraMap F F⟮e⟯ a) = σ a := g.commutes
      simpa only [map_sum, pb.basis_eq_pow, Algebra.smul_def, map_mul, map_pow,
        hcoeff, hggen] using h
    change R (RVCalc.rv v (x : K)) (RVCalc.rv w (g x))
    rw [← hx, ← hg]
    exact rv_sum_relation v w F σ ρ R hzero hmul hintegral hres hbase hunit he hd hI' hvar

/-- Textbook-facing form: the only residue degree hypothesis is an equality of
ordinary minimal-polynomial degrees over the base residue subfield. -/
theorem exists_field_embedding_of_residue_minpoly
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
    {e : K} {d : L} (he : v e = 1) (hd : w d = 1)
    (p : Polynomial F) (hp : p.Monic)
    (hpe : p.eval₂ F.subtype e = 0) (hpd : p.eval₂ σ d = 0)
    (hdegree : (minpoly κ (M7.vres v e he.le)).natDegree = p.natDegree)
    (hvar : ρ (M7.vres v e he.le) = M7.vres w d hd.le) :
    ∃ g : F⟮e⟯ →+* L,
      Function.Injective g ∧
      (∀ a : F, g (algebraMap F F⟮e⟯ a) = σ a) ∧
      g (IntermediateField.AdjoinSimple.gen F e) = d ∧
      ∀ x : F⟮e⟯, R (RVCalc.rv v (x : K)) (RVCalc.rv w (g x)) :=
  exists_field_embedding v w F σ ρ R hzero hmul hintegral hres hbase hunit
    he hd p hp hpe hpd (residueIndependent_of_minpoly v F κ hκ he hdegree) hvar

end ResidueAlgebraicTransport

#print axioms ResidueAlgebraicTransport.powers_linearIndependent
#print axioms ResidueAlgebraicTransport.exists_field_embedding
#print axioms ResidueAlgebraicTransport.exists_field_embedding_of_residue_minpoly
