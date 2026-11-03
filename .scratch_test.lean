import Mathlib
open FirstOrder FirstOrder.Language
open FirstOrder.Ring
open scoped FirstOrder
attribute [local instance 100] FirstOrder.Ring.compatibleRingOfRing
set_option backward.isDefEq.respectTransparency false
example {K N : Type*} [CommRing K] [CommRing N] [CompatibleRing N]
    (ts : Fin 2 → Language.ring.Term (K ⊕ Fin 1)) (v : K ⊕ Fin 1 → N) :
    Term.realize v (Term.func FirstOrder.ringFunc.add ts) =
      Term.realize v (ts 0) + Term.realize v (ts 1) := by
  rw [Term.realize_func]
  simp
