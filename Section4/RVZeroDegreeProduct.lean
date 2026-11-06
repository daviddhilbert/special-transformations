import Section4.RVProduct

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] {S : Set M} {k : ℕ}

/-- The degree-zero convention in Remark 4.21: only the nonzero-degree
factor contributes volume coordinates. -/
theorem rvProductObject_value_zero_left (U : RVObject (M := M) S 0)
    (V : RVObject (M := M) S k) (a : (rvProductObject U V).domain) :
    (rvProductObject U V).value a =
      V.value ⟨(rvUnpack U.domain V.domain a).val.2,
        (rvUnpack U.domain V.domain a).property.2⟩ ∘ Fin.cast (Nat.zero_add k) := by
  rw [rvProductObject_value]
  have hzero : U.value ⟨(rvUnpack U.domain V.domain a).val.1,
      (rvUnpack U.domain V.domain a).property.1⟩ = Fin.elim0 := funext (fun i : Fin 0 => i.elim0)
  rw [hzero]
  exact Fin.elim0_append _

theorem rvProductObject_value_zero_right (U : RVObject (M := M) S k)
    (V : RVObject (M := M) S 0) (a : (rvProductObject U V).domain) :
    (rvProductObject U V).value a =
      U.value ⟨(rvUnpack U.domain V.domain a).val.1,
        (rvUnpack U.domain V.domain a).property.1⟩ ∘ Fin.cast (Nat.add_zero k) := by
  rw [rvProductObject_value]
  have hzero : V.value ⟨(rvUnpack U.domain V.domain a).val.2,
      (rvUnpack U.domain V.domain a).property.2⟩ = Fin.elim0 := funext (fun i : Fin 0 => i.elim0)
  rw [hzero]
  exact Fin.append_elim0 _

end SpecialTransformations.Section4

end
