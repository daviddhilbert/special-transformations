import Section4.GammaMultiplicationSyntax
import Section3.GammaValueLaws

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M}

def GammaDcl (S : Set M) : Set (Values.Gamma (M := M)) :=
  {a | Values.GammaDefinable S {a}}

theorem gammaDcl_one : (1 : Values.Gamma (M := M)) ∈ GammaDcl S :=
  GammaSyntax.one_definable S

theorem gammaDcl_mul {a b : Values.Gamma (M := M)}
    (ha : a ∈ GammaDcl S) (hb : b ∈ GammaDcl S) : a * b ∈ GammaDcl S := by
  let ι := Fin 1 ⊕ Fin 2
  have h := ((GammaSyntax.unary_at ha (Sum.inr (0 : Fin 2) : ι)).and
    (GammaSyntax.unary_at hb (Sum.inr (1 : Fin 2) : ι))).and
    (GammaSyntax.mul_definable S (Sum.inr (0 : Fin 2) : ι) (Sum.inr 1) (Sum.inl 0))
  apply (GammaSyntax.scalar_definable_iff {a * b}).mp
  exact h.exists_block.congr (fun z => by
    change (∃ t : Fin 2 → Values.Gamma (M := M),
      (t 0 = a ∧ t 1 = b) ∧ t 0 * t 1 = z 0) ↔ z 0 = a * b
    constructor
    · rintro ⟨t, ⟨ha, hb⟩, ht⟩
      rw [ha, hb] at ht
      exact ht.symm
    · intro he
      exact ⟨![a,b], ⟨rfl, rfl⟩, he.symm⟩)

theorem gammaDcl_inv {a : Values.Gamma (M := M)} (ha : a ∈ GammaDcl S) :
    a⁻¹ ∈ GammaDcl S := by
  let ι := Fin 1 ⊕ Fin 2
  have h := ((GammaSyntax.unary_at ha (Sum.inr (0 : Fin 2) : ι)).and
    (GammaSyntax.unary_at (gammaDcl_one (M := M) (S := S)) (Sum.inr (1 : Fin 2) : ι))).and
    (GammaSyntax.mul_definable S (Sum.inr (0 : Fin 2) : ι) (Sum.inl 0) (Sum.inr 1))
  apply (GammaSyntax.scalar_definable_iff {a⁻¹}).mp
  exact h.exists_block.congr (fun z => by
    change (∃ t : Fin 2 → Values.Gamma (M := M),
      (t 0 = a ∧ t 1 = 1) ∧ t 0 * z 0 = t 1) ↔ z 0 = a⁻¹
    constructor
    · rintro ⟨t, ⟨ha, hb⟩, ht⟩
      rw [ha, hb] at ht
      exact mul_left_cancel (ht.trans (mul_inv_cancel a).symm)
    · intro he
      exact ⟨![a,1], ⟨rfl, rfl⟩, by change a * z 0 = 1; rw [he, mul_inv_cancel]⟩)

theorem gamma_square_injective : Function.Injective
    (fun a : Values.Gamma (M := M) => a * a) := by
  intro a b hab
  rcases lt_trichotomy a b with h | h | h
  · exact False.elim ((ne_of_lt (mul_lt_mul_of_lt_of_lt h h)) hab)
  · exact h
  · exact False.elim ((ne_of_gt (mul_lt_mul_of_lt_of_lt h h)) hab)

theorem gammaDcl_square_root {a : Values.Gamma (M := M)} (ha : a ∈ GammaDcl S) :
    ∃ r ∈ GammaDcl S, r * r = a := by
  obtain ⟨r, hr⟩ := Values.gamma_pow_surjective (M := M) 2 (by decide) a
  have hrr : r * r = a := by simpa only [pow_two] using hr
  refine ⟨r, ?_, hrr⟩
  let ι := Fin 1 ⊕ Fin 1
  have h := (GammaSyntax.unary_at ha (Sum.inr (0 : Fin 1) : ι)).and
    (GammaSyntax.mul_definable S (Sum.inl (0 : Fin 1) : ι) (Sum.inl 0) (Sum.inr 0))
  apply (GammaSyntax.scalar_definable_iff {r}).mp
  exact h.exists_block.congr (fun z => by
    change (∃ t : Fin 1 → Values.Gamma (M := M), t 0 = a ∧ z 0 * z 0 = t 0) ↔ z 0 = r
    constructor
    · rintro ⟨t, ht, hz⟩
      exact gamma_square_injective (hz.trans (ht.trans hrr.symm))
    · intro hz
      exact ⟨![a], rfl, by change z 0 * z 0 = a; rw [hz, hrr]⟩)

/-- A named nontrivial value supplies the two tail samples; unique square
roots supply samples between named endpoints even in non-Archimedean Gamma. -/
theorem gammaDcl_samples (δ : Values.Gamma (M := M)) (hδ : δ ∈ GammaDcl S) (hδ1 : 1 < δ) :
    (∀ a ∈ GammaDcl S, ∃ b ∈ GammaDcl S, b < a) ∧
    (∀ a ∈ GammaDcl S, ∃ b ∈ GammaDcl S, a < b) ∧
    (∀ a ∈ GammaDcl S, ∀ b ∈ GammaDcl S, a < b →
      ∃ c ∈ GammaDcl S, a < c ∧ c < b) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    refine ⟨a * δ⁻¹, gammaDcl_mul ha (gammaDcl_inv hδ), ?_⟩
    have hi : δ⁻¹ < 1 := Left.inv_lt_one_iff.mpr hδ1
    simpa only [mul_one] using mul_lt_mul_right hi a
  · intro a ha
    refine ⟨a * δ, gammaDcl_mul ha hδ, ?_⟩
    simpa only [mul_one] using mul_lt_mul_right hδ1 a
  · intro a ha b hb hab
    obtain ⟨r, hr, hrr⟩ := gammaDcl_square_root (gammaDcl_mul ha hb)
    refine ⟨r, hr, ?_, ?_⟩
    · apply lt_of_not_ge
      intro hra
      have hle : r * r ≤ a * a := mul_le_mul' hra hra
      have hlt : a * a < a * b := mul_lt_mul_right hab a
      rw [hrr] at hle
      exact not_le_of_gt hlt hle
    · apply lt_of_not_ge
      intro hbr
      have hle : b * b ≤ r * r := mul_le_mul' hbr hbr
      have hlt : a * b < b * b := mul_lt_mul_left hab b
      rw [hrr] at hle
      exact not_le_of_gt hlt hle

end SpecialTransformations.Section4

end
