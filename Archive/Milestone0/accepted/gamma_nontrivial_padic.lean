module

public import Mathlib

@[expose] public section

noncomputable section
open Valuation
open scoped NNReal

example (p : ℕ) [hp : Fact (Nat.Prime p)] :
    (PadicComplex.valued p).v ((p : PadicAlgCl p) : PadicComplex p) ≠ 1 := by
  rw [PadicComplex.valuation_extends, PadicAlgCl.valuation_p]
  intro h
  have h2 : (1 : ℝ≥0) / (p : ℝ≥0) * (p : ℝ≥0) = (1 : ℝ≥0) * (p : ℝ≥0) := by rw [h]
  have h3 : (1 : ℝ≥0) = (p : ℝ≥0) := by simpa [one_div] using h2
  have hp1 : (1 : ℕ) < p := hp.out.one_lt
  have hp1' : (1 : ℝ≥0) < (p : ℝ≥0) := by exact_mod_cast hp1
  rw [← h3] at hp1'
  exact lt_irrefl _ hp1'
