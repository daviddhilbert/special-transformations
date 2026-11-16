module

public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Order.Group.Unbundled.Basic
public import Mathlib.Tactic

@[expose] public section

/-! The monomial permutation underlying the arity-two obstruction to the
Gamma comparison in Lemma 9.15. The order here is the paper's additive order. -/

namespace SpecialTransformations.Section9

variable {G Γ : Type*} [CommGroup G] [AddCommGroup Γ] [LinearOrder Γ]
  [IsOrderedAddMonoid Γ]

variable (v : G →* Multiplicative Γ)

private abbrev value (x : G) : Γ := (v x).toAdd

/-- The locus of two nonzero elements in the maximal ideal, in additive order. -/
def PositivePair (p : G × G) : Prop := 0 < value v p.1 ∧ 0 < value v p.2

/-- Cycle the three open cones separated by `a = b` and `a = 2b`, and
exchange the two rays. Here `a` and `b` are the input valuations. -/
def monomialPermutation (p : G × G) : G × G :=
  let a := value v p.1
  let b := value v p.2
  if b + b < a then (p.1, p.1 / p.2)
  else if a = b + b then (p.1 / p.2, p.2)
  else if b < a then (p.2 * p.2 / p.1, p.2)
  else if a = b then (p.1 * p.2, p.2)
  else (p.1 * p.2, p.1)

private def monomialInverse (p : G × G) : G × G :=
  let a := value v p.1
  let b := value v p.2
  if b + b < a then (p.2, p.1 / p.2)
  else if a = b + b then (p.1 / p.2, p.2)
  else if b < a then (p.1, p.1 / p.2)
  else if a = b then (p.1 * p.2, p.2)
  else (p.2 * p.2 / p.1, p.2)

omit [LinearOrder Γ] [IsOrderedAddMonoid Γ] in
private theorem value_mul (x y : G) : value v (x * y) = value v x + value v y :=
  congrArg Multiplicative.toAdd (map_mul v x y)

omit [LinearOrder Γ] [IsOrderedAddMonoid Γ] in
private theorem value_div (x y : G) : value v (x / y) = value v x - value v y :=
  congrArg Multiplicative.toAdd (map_div v x y)

set_option maxHeartbeats 1500000 in
private theorem forward_spec (p : G × G) (hp : PositivePair v p) :
    PositivePair v (monomialPermutation v p) ∧
    monomialInverse v (monomialPermutation v p) = p ∧
    value v (monomialPermutation v p).1 + value v (monomialPermutation v p).2 ≠
      value v p.1 + value v p.2 := by
  obtain ⟨ha, hb⟩ := hp
  simp only [monomialPermutation]
  split_ifs
  all_goals
    simp only [PositivePair, monomialInverse, value_mul, value_div]
    split_ifs <;> try (exfalso; grind)
    refine ⟨⟨by grind, by grind⟩, ?_, by grind⟩
    apply Prod.ext <;> simp [div_div_cancel, mul_div_cancel_left]

set_option maxHeartbeats 1500000 in
private theorem inverse_spec (p : G × G) (hp : PositivePair v p) :
    PositivePair v (monomialInverse v p) ∧
    monomialPermutation v (monomialInverse v p) = p := by
  obtain ⟨ha, hb⟩ := hp
  simp only [monomialInverse]
  split_ifs
  all_goals
    simp only [PositivePair, monomialPermutation, value_mul, value_div]
    split_ifs <;> try (exfalso; grind)
    refine ⟨⟨by grind, by grind⟩, ?_⟩
    apply Prod.ext <;> simp [div_div_cancel]

/-- A bijection of the positive-valued pairs that changes the sum of the two
valuations at every point. For the monomial branches in a valued field this
change is the additive value of their Jacobian determinant. -/
theorem monomialPermutation_bijOn_and_changes_sum :
    Set.BijOn (monomialPermutation v) (PositivePair v) (PositivePair v) ∧
    ∀ p, PositivePair v p →
      (v (monomialPermutation v p).1).toAdd + (v (monomialPermutation v p).2).toAdd ≠
        (v p.1).toAdd + (v p.2).toAdd := by
  refine ⟨⟨fun p hp => (forward_spec v p hp).1, ?_, ?_⟩,
    fun p hp => (forward_spec v p hp).2.2⟩
  · intro p hp q hq hpq
    simpa only [(forward_spec v p hp).2.1, (forward_spec v q hq).2.1] using
      congrArg (monomialInverse v) hpq
  · intro p hp
    exact ⟨monomialInverse v p, (inverse_spec v p hp).1, (inverse_spec v p hp).2⟩

end SpecialTransformations.Section9
