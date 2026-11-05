import ResidueAlgebraicSourceLift
import ResiduePolynomialLift

/-!
The local residue-algebraic adjoining step, with polynomial lifts, source
roots, target roots, and the RV-compatible field embedding all constructed.

The base residue subfield is specified by the usual inclusion and surjectivity
properties. Algebraicity of the selected residue class is the only algebraic
input. Selecting its target unit representative from the prescribed RV map is
left to the model-language bridge.
-/

namespace ResidueAlgebraicTransport

open scoped IntermediateField
open Polynomial ResidueTranscendentalTransport

variable {K L Γ Δ : Type*} [Field K] [Field L]
  [LinearOrderedCommGroupWithZero Γ] [LinearOrderedCommGroupWithZero Δ]

theorem exists_adjoin_embedding [IsAlgClosed K] [IsAlgClosed L]
    (v : Valuation K Γ) (w : Valuation L Δ)
    (F : Subfield K) (σ : F →+* L) (ρ : Residue v →+* Residue w)
    (κ : Subfield (Residue v))
    (hκ : ∀ (a : F) (ha : v (a : K) ≤ 1), M7.vres v (a : K) ha ∈ κ)
    (hsurj : ∀ z : κ, ∃ a : F, ∃ ha : v (a : K) ≤ 1,
      M7.vres v (a : K) ha = κ.subtype z)
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
    (halg : IsIntegral κ (M7.vres v u hu.le))
    (hvar : ρ (M7.vres v u hu.le) = M7.vres w a₀ ha₀.le) :
    ∃ e : K, v e = 1 ∧ RVCalc.rv v e = RVCalc.rv v u ∧
      ∃ g : F⟮e⟯ →+* L,
        Function.Injective g ∧
        (∀ a : F, g (algebraMap F F⟮e⟯ a) = σ a) ∧
        RVCalc.rv w (g (IntermediateField.AdjoinSimple.gen F e)) = RVCalc.rv w a₀ ∧
        ∀ x : F⟮e⟯, R (RVCalc.rv v (x : K)) (RVCalc.rv w (g x)) := by
  obtain ⟨p, hp, hdegree, hc, hcoeff⟩ := exists_monic_integral_lift v F κ hsurj
    (minpoly κ (M7.vres v u hu.le)) (minpoly.monic halg)
  exact exists_adjoin_embedding_of_lifted_minpoly v w F σ ρ κ hκ R hzero hmul
    hintegral hres hbase hunit hu ha₀ p hp hc hcoeff hdegree hvar

end ResidueAlgebraicTransport

#print axioms ResidueAlgebraicTransport.exists_adjoin_embedding
