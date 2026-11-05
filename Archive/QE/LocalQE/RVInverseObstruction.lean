import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Group.Submonoid.Basic
import Mathlib.Tactic

/-! A finite algebraic obstruction in the earlier inverse-free RV reduct.

The nonzero graded RV group is `Multiplicative ℤ × F₈ˣ`. Its submonoid contains
the identity and all strictly positive grades. Cubing the coefficient is an
injective, grade-preserving monoid map, but any extension to the group induces
the nonadditive cube map on grade-zero coefficients. This file proves that
algebraic obstruction; it does not by itself construct an ACVF countermodel.
The author has since confirmed that RV inversion belongs to the intended
language. This positive-grade monoid is not closed under that named inverse,
so this historical audit does not obstruct the corrected QE target.
-/

namespace RVInverseObstruction

noncomputable section

abbrev F8 := GaloisField 2 3

theorem card_F8 : Nat.card F8 = 8 := by
  simpa using GaloisField.card 2 3 (by decide)

theorem card_units_F8 : Nat.card F8ˣ = 7 := by
  rw [Nat.card_units, card_F8]

theorem cube_units_injective : Function.Injective (fun u : F8ˣ => u ^ 3) := by
  apply (Nat.Coprime.pow_left_bijective (G := F8ˣ) (n := 3) ?_).injective
  rw [card_units_F8]
  decide

theorem cube_add_one_ne {F : Type*} [Field F] [CharP F 2]
    (x : F) (hx0 : x ≠ 0) (hx1 : x ≠ 1) : (x + 1) ^ 3 ≠ x ^ 3 + 1 := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have h3 : (3 : F) = 1 := by linear_combination h2
  have hexpand : (x + 1) ^ 3 = x ^ 3 + x ^ 2 + x + 1 := by
    calc
      (x + 1) ^ 3 = x ^ 3 + 3 * x ^ 2 + 3 * x + 1 := by ring
      _ = x ^ 3 + x ^ 2 + x + 1 := by rw [h3]; ring
  intro h
  have hmul : x * (x + 1) = 0 := by linear_combination h - hexpand
  have hplus : x + 1 = 0 := (mul_eq_zero.mp hmul).resolve_left hx0
  apply hx1
  apply add_right_cancel (b := (1 : F))
  simpa only [one_add_one_eq_two, h2] using hplus

theorem exists_cube_add_failure : ∃ x : F8, (x + 1) ^ 3 ≠ x ^ 3 + 1 := by
  letI : Fintype F8ˣ := Fintype.ofFinite _
  have hc : 1 < Fintype.card F8ˣ := by
    rw [← Nat.card_eq_fintype_card, card_units_F8]
    decide
  obtain ⟨u, hu⟩ := Fintype.exists_ne_of_one_lt_card hc (1 : F8ˣ)
  exact ⟨u, cube_add_one_ne (u : F8) (Units.ne_zero u) (fun h => hu (Units.ext h))⟩

theorem no_cube_ringHom : ¬ ∃ ρ : F8 →+* F8, ∀ x : F8, ρ x = x ^ 3 := by
  rintro ⟨ρ, hρ⟩
  obtain ⟨x, hx⟩ := exists_cube_add_failure
  apply hx
  rw [← hρ (x + 1), map_add, hρ x, map_one]

abbrev Graded := Multiplicative ℤ × F8ˣ

def positiveMonoid : Submonoid Graded where
  carrier := {x | 0 < x.1.toAdd ∨ x = 1}
  one_mem' := Or.inr rfl
  mul_mem' := by
    intro x y hx hy
    rcases hx with hx | rfl
    · rcases hy with hy | rfl
      · left
        change 0 < x.1.toAdd + y.1.toAdd
        omega
      · simpa using Or.inl hx
    · simpa using hy

def cube : Graded →* Graded where
  toFun x := (x.1, x.2 ^ 3)
  map_one' := by simp
  map_mul' x y := by ext <;> simp [mul_pow]

def positiveCube : positiveMonoid →* Graded := cube.comp positiveMonoid.subtype

theorem cube_injective : Function.Injective cube := by
  intro x y h
  apply Prod.ext
  · simpa only [cube, MonoidHom.coe_mk, OneHom.coe_mk] using congrArg Prod.fst h
  · exact cube_units_injective (congrArg Prod.snd h)

theorem positiveCube_injective : Function.Injective positiveCube :=
  cube_injective.comp Subtype.val_injective

theorem positiveCube_grade (x : positiveMonoid) :
    (positiveCube x).1 = (x : Graded).1 := rfl

theorem positiveCube_order (x y : positiveMonoid) :
    (x : Graded).1.toAdd ≤ (y : Graded).1.toAdd ↔
      (positiveCube x).1.toAdd ≤ (positiveCube y).1.toAdd := Iff.rfl

/-- Every nonidentity element of grade zero is missing from this submonoid. -/
theorem grade_zero_mem_iff (u : F8ˣ) :
    ((1, u) : Graded) ∈ positiveMonoid ↔ u = 1 := by
  change (0 < (0 : ℤ) ∨ ((1, u) : Graded) = 1) ↔ u = 1
  simp

def ray (u : F8ˣ) : positiveMonoid :=
  ⟨(Multiplicative.ofAdd 1, u), Or.inl (by change 0 < (1 : ℤ); decide)⟩

theorem ray_ratio (u : F8ˣ) :
    ((ray u : positiveMonoid) : Graded) / (ray 1 : Graded) = (1, u) := by
  ext <;> simp [ray]

theorem group_extension_forces_cube (g : Graded →* Graded)
    (hg : ∀ x : positiveMonoid, g x = positiveCube x) (u : F8ˣ) :
    g (1, u) = (1, u ^ 3) := by
  rw [← ray_ratio u, map_div, hg, hg]
  ext <;> simp [positiveCube, cube, ray]

/-- The multiplicative map has no extension whose induced residue map is a ring hom. -/
theorem no_residue_compatible_extension :
    ¬ ∃ (g : Graded →* Graded) (ρ : F8 →+* F8),
      (∀ x : positiveMonoid, g x = positiveCube x) ∧
      (∀ u : F8ˣ, ((g (1, u)).2 : F8) = ρ (u : F8)) := by
  rintro ⟨g, ρ, hg, hρ⟩
  apply no_cube_ringHom
  refine ⟨ρ, ?_⟩
  intro x
  by_cases hx : x = 0
  · simp [hx]
  · have h := hρ (Units.mk0 x hx)
    rw [group_extension_forces_cube g hg] at h
    exact h.symm

end
end RVInverseObstruction

#print axioms RVInverseObstruction.cube_units_injective
#print axioms RVInverseObstruction.exists_cube_add_failure
#print axioms RVInverseObstruction.positiveCube_injective
#print axioms RVInverseObstruction.positiveCube_order
#print axioms RVInverseObstruction.no_residue_compatible_extension
