import ResidueAlgebraicTransport
import Mathlib.Algebra.Polynomial.Lifts

/-!
Lift monic polynomials from the base residue field to the integral base field.
The only input is surjectivity of reduction onto that residue field. All
coefficient identities, integrality, monicity, and degree preservation are
proved, using Mathlib's general monic polynomial lifting theorem.
-/

namespace ResidueAlgebraicTransport

open Polynomial ResidueTranscendentalTransport

variable {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]

abbrev BaseIntegers (v : Valuation K Γ) (F : Subfield K) :=
  v.valuationSubring.comap F.subtype

def baseIntegerInclusion (v : Valuation K Γ) (F : Subfield K) :
    BaseIntegers v F →+* v.valuationSubring where
  toFun a := ⟨((a : F) : K), a.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

noncomputable def baseResidueHom (v : Valuation K Γ) (F : Subfield K) :
    BaseIntegers v F →+* Residue v :=
  (IsLocalRing.residue v.valuationSubring).comp (baseIntegerInclusion v F)

theorem baseResidueHom_apply (v : Valuation K Γ) (F : Subfield K)
    (a : BaseIntegers v F) (ha : v ((a : F) : K) ≤ 1) :
    baseResidueHom v F a = M7.vres v ((a : F) : K) ha := rfl

theorem exists_monic_integral_lift (v : Valuation K Γ) (F : Subfield K)
    (κ : Subfield (Residue v))
    (hsurj : ∀ z : κ, ∃ a : F, ∃ ha : v (a : K) ≤ 1,
      M7.vres v (a : K) ha = κ.subtype z)
    (q : Polynomial κ) (hq : q.Monic) :
    ∃ p : Polynomial F, p.Monic ∧ q.natDegree = p.natDegree ∧
      ∃ hc : ∀ i : ℕ, v (p.coeff i : K) ≤ 1,
        ∀ i : ℕ, M7.vres v (p.coeff i : K) (hc i) = κ.subtype (q.coeff i) := by
  let r := baseResidueHom v F
  have hlifts : q.map κ.subtype ∈ Polynomial.lifts r := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    obtain ⟨a, ha, har⟩ := hsurj (q.coeff i)
    let a' : BaseIntegers v F :=
      ⟨a, (Valuation.mem_valuationSubring_iff v (a : K)).mpr ha⟩
    refine ⟨a', ?_⟩
    rw [Polynomial.coeff_map]
    exact har
  obtain ⟨P, hPmap, hPdegree, hPmonic⟩ :=
    Polynomial.lifts_and_natDegree_eq_and_monic hlifts (hq.map κ.subtype)
  let p : Polynomial F := P.map (BaseIntegers v F).subtype
  have hp : p.Monic := hPmonic.map _
  have hdegree : q.natDegree = p.natDegree := by
    calc
      q.natDegree = (q.map κ.subtype).natDegree := (hq.natDegree_map _).symm
      _ = P.natDegree := hPdegree.symm
      _ = p.natDegree := (hPmonic.natDegree_map _).symm
  have hc : ∀ i : ℕ, v (p.coeff i : K) ≤ 1 := by
    intro i
    dsimp only [p]
    rw [Polynomial.coeff_map]
    exact (Valuation.mem_valuationSubring_iff v _).mp (P.coeff i).property
  refine ⟨p, hp, hdegree, hc, ?_⟩
  intro i
  have hi := congrArg (fun f : Polynomial (Residue v) => f.coeff i) hPmap
  simp only [Polynomial.coeff_map] at hi
  dsimp only [p]
  simp only [Polynomial.coeff_map]
  change r (P.coeff i) = κ.subtype (q.coeff i)
  exact hi

end ResidueAlgebraicTransport

#print axioms ResidueAlgebraicTransport.baseResidueHom_apply
#print axioms ResidueAlgebraicTransport.exists_monic_integral_lift
