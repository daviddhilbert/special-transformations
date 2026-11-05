import CanonicalTheory

/-! The RV language has finitely many symbols, hence is countable.
This lets the QE criterion use countably saturated elementary extensions. -/

open SpecialTransformations.Milestone0

namespace CanonicalCountable

private def fnCode : (Σ n, Fn n) → ℕ
  | ⟨_, .vfZero⟩ => 0
  | ⟨_, .vfOne⟩ => 1
  | ⟨_, .vfAdd⟩ => 2
  | ⟨_, .vfNeg⟩ => 3
  | ⟨_, .vfMul⟩ => 4
  | ⟨_, .rvOne⟩ => 5
  | ⟨_, .rvZero⟩ => 6
  | ⟨_, .rvMul⟩ => 7
  | ⟨_, .rvInv⟩ => 8
  | ⟨_, .kAdd⟩ => 9
  | ⟨_, .kNeg⟩ => 10
  | ⟨_, .rvMap⟩ => 11

private theorem fnCode_injective : Function.Injective fnCode := by
  rintro ⟨n, f⟩ ⟨m, g⟩ h
  cases f <;> cases g <;> simp_all [fnCode]

private def relCode : (Σ n, Rel n) → ℕ
  | ⟨_, .memVF⟩ => 0
  | ⟨_, .memRV⟩ => 1
  | ⟨_, .memUnits⟩ => 2
  | ⟨_, .rvLe⟩ => 3

private theorem relCode_injective : Function.Injective relCode := by
  rintro ⟨n, f⟩ ⟨m, g⟩ h
  cases f <;> cases g <;> simp_all [relCode]

instance : Countable LRV.Symbols := by
  letI : Countable (Σ n, Fn n) := Function.Injective.countable fnCode_injective
  letI : Countable (Σ n, Rel n) := Function.Injective.countable relCode_injective
  change Countable ((Σ n, Fn n) ⊕ (Σ n, Rel n))
  infer_instance

end CanonicalCountable
