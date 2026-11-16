module

public import Mathlib
public import Mathlib.Topology.Algebra.Valued.ValuedField

@[expose] public section
open Filter Topology MonoidWithZeroHom
namespace SpecialTransformations.Section3
theorem infinite_valued_neighbourhood {K Γ : Type} [Field K]
    [LinearOrderedCommGroupWithZero Γ] [Valued K Γ]
    (hnt : ∃ ε : K, ε ≠ 0 ∧ Valued.v ε < 1)
    (a : K) {s : Set K} (hs : s ∈ 𝓝 a) : s.Infinite := by
  classical
  intro hf
  have ho := isOpen_singleton_of_finite_mem_nhds a hs hf
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.mp (ho.mem_nhds (Set.mem_singleton a))
  let v : Valuation K Γ := Valued.v
  obtain ⟨r, hr⟩ := ValueGroup₀.restrict₀_surjective (.ofClass v) γ.val
  have hr' : v.restrict r = γ.val := hr
  have hr0 : r ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hr'
    exact γ.ne_zero hr'.symm
  obtain ⟨ε, hε0, hε⟩ := hnt
  have hsmall : v.restrict (a + r * ε - a) < γ.val := by
    rw [add_sub_cancel_left, map_mul, hr']
    simpa using mul_lt_mul_of_pos_left ((v.restrict_lt_one_iff).mpr hε) (Units.zero_lt γ)
  have heq : a + r * ε = a := hγ hsmall
  have hz : r * ε = 0 := add_left_cancel (by simpa using heq : a + r * ε = a + 0)
  exact (mul_ne_zero hr0 hε0) hz
end SpecialTransformations.Section3