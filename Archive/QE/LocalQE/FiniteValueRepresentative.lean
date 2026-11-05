import ValueAlgebraicTransport
import Mathlib.Data.Nat.Find

/-! Source representatives for the finite value-degree case. Once every unit
RV class has a base-field representative, a value-level power relation can be
corrected to an exact field-level power equation without changing the new RV
class. Minimal value degree is selected from an ordinary existence hypothesis. -/

namespace FiniteValueRepresentative

open ResidueTranscendentalTransport ValueAlgebraicTransport

variable {K Γ : Type*} [Field K] [IsAlgClosed K]
  [LinearOrderedCommGroupWithZero Γ]

/-- Every valuation-one leading-term class is represented in the base field. -/
def UnitClassesInBase (v : Valuation K Γ) (F : Subfield K) : Prop :=
  ∀ x : K, v x = 1 → ∃ b : F, RVCalc.rv v (b : K) = RVCalc.rv v x

/-- Correct the base power witness by a base unit, then lift its exact nth root
with the prescribed source leading term. -/
theorem root_same_rv_of_value_power (v : Valuation K Γ) (F : Subfield K)
    (hunits : UnitClassesInBase v F) {c : K} (hc : c ≠ 0)
    {n : ℕ} (hn : 0 < n) (a : F) (hvalue : (v c) ^ n = v (a : K)) :
    ∃ (a' : F) (e : K), e ≠ 0 ∧ e ^ n = (a' : K) ∧
      RVCalc.rv v e = RVCalc.rv v c := by
  have hva : v (a : K) ≠ 0 := by
    rw [← hvalue]
    exact pow_ne_zero n ((Valuation.ne_zero_iff v).mpr hc)
  have ha : (a : K) ≠ 0 := (Valuation.ne_zero_iff v).mp hva
  have hu : v (c ^ n / (a : K)) = 1 := by
    rw [Valuation.map_div, map_pow, hvalue, div_self hva]
  obtain ⟨b, hbrv⟩ := hunits (c ^ n / (a : K)) hu
  have hvb : v (b : K) = 1 := by
    have h := congrArg (RVCalc.vrv v) hbrv
    simpa only [RVCalc.vrv_rv, hu] using h
  have hb : (b : K) ≠ 0 := by
    intro hz
    simp [hz] at hvb
  have hmul : (a : K) * (c ^ n / (a : K)) = c ^ n := mul_div_cancel₀ _ ha
  have hclass : RVCalc.rv v (c ^ n) = RVCalc.rv v ((a * b : F) : K) := by
    calc
      RVCalc.rv v (c ^ n) = RVCalc.rv v ((a : K) * (c ^ n / (a : K))) :=
        congrArg (RVCalc.rv v) hmul.symm
      _ = RVCalc.rvMul v (RVCalc.rv v (a : K)) (RVCalc.rv v (c ^ n / (a : K))) :=
        rv_mul_all v _ _
      _ = RVCalc.rvMul v (RVCalc.rv v (a : K)) (RVCalc.rv v (b : K)) := by rw [hbrv]
      _ = RVCalc.rv v ((a * b : F) : K) := (rv_mul_all v _ _).symm
  obtain ⟨e, hepow, herv⟩ := RVCalc.nth_root_with_rv v hn (mul_ne_zero ha hb) hc hclass
  have he : e ≠ 0 := by
    intro hz
    have h := herv
    rw [hz, RVCalc.rv_zero] at h
    exact RVCalc.rv_ne_none hc h.symm
  exact ⟨a * b, e, he, hepow, herv⟩

theorem noSmallerValuePower_of_same_rv (v : Valuation K Γ) (F : Subfield K)
    {c e : K} {n : ℕ} (hgap : NoSmallerValuePower v F c n)
    (hrv : RVCalc.rv v e = RVCalc.rv v c) : NoSmallerValuePower v F e n := by
  have hv : v e = v c := by
    have h := congrArg (RVCalc.vrv v) hrv
    simpa only [RVCalc.vrv_rv] using h
  intro i hi hin a
  rw [hv]
  exact hgap i hi hin a

/-- Fixed-degree interface, when the least value exponent has already been
selected by the surrounding maximal-extension argument. -/
theorem root_same_rv_of_minimal_value_power (v : Valuation K Γ) (F : Subfield K)
    (hunits : UnitClassesInBase v F) {c : K} (hc : c ≠ 0)
    {n : ℕ} (hn : 0 < n) (hgap : NoSmallerValuePower v F c n)
    (a : F) (hvalue : (v c) ^ n = v (a : K)) :
    ∃ (a' : F) (e : K), e ≠ 0 ∧ e ^ n = (a' : K) ∧
      RVCalc.rv v e = RVCalc.rv v c ∧ NoSmallerValuePower v F e n := by
  obtain ⟨a', e, he, hepow, hrv⟩ := root_same_rv_of_value_power v F hunits hc hn a hvalue
  exact ⟨a', e, he, hepow, hrv, noSmallerValuePower_of_same_rv v F hgap hrv⟩

/-- No minimality is assumed: any positive power lying in the base value group
has a least such exponent, and the representative at that exponent satisfies
the exact hypotheses of the finite value-degree field-embedding theorem. -/
theorem exists_minimal_representative (v : Valuation K Γ) (F : Subfield K)
    (hunits : UnitClassesInBase v F) {c : K} (hc : c ≠ 0)
    (hfinite : ∃ n : ℕ, 0 < n ∧ ∃ a : F, (v c) ^ n = v (a : K)) :
    ∃ (n : ℕ) (a : F) (e : K), 0 < n ∧ e ≠ 0 ∧ e ^ n = (a : K) ∧
      RVCalc.rv v e = RVCalc.rv v c ∧ NoSmallerValuePower v F e n := by
  classical
  let n : ℕ := Nat.find hfinite
  have hn : 0 < n := (Nat.find_spec hfinite).1
  obtain ⟨a, ha⟩ := (Nat.find_spec hfinite).2
  have hgap : NoSmallerValuePower v F c n := by
    intro i hi hin b hb
    exact Nat.find_min hfinite hin ⟨hi, b, hb⟩
  obtain ⟨a', e, he, hepow, hrv, hegap⟩ :=
    root_same_rv_of_minimal_value_power v F hunits hc hn hgap a ha
  exact ⟨n, a', e, hn, he, hepow, hrv, hegap⟩

end FiniteValueRepresentative

#print axioms FiniteValueRepresentative.root_same_rv_of_value_power
#print axioms FiniteValueRepresentative.noSmallerValuePower_of_same_rv
#print axioms FiniteValueRepresentative.root_same_rv_of_minimal_value_power
#print axioms FiniteValueRepresentative.exists_minimal_representative
