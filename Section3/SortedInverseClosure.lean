module

public import Section3.SortedFunctionClosure
public import VFValued

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem definableClosureAt_vf_inv (S : Set M) (x : VFType (M := M))
    (hx : DefinableClosureAt S .vf x.val) : DefinableClosureAt S .vf (x⁻¹).val := by
  by_cases hx0 : x = 0
  · have hz : DefinableClosureAt S .vf (0 : VFType (M := M)).val :=
      definableClosureAt_function_symbol S Fn.vfZero Fin.elim0
        (fun i => i.elim0) (fun i => i.elim0)
    simpa only [hx0, inv_zero] using hz
  · let p : Parameters ({x.val} : Set M) :=
      ⟨1, ![x.val], fun _ => .vf,
        by intro i; fin_cases i; exact x.property,
        by intro i; fin_cases i; exact Set.mem_singleton _⟩
    let t : LRV.Term (Fin 1 ⊕ Fin 1) :=
      .func Fn.vfMul ![.var (.inl 0), .var (.inr 0)]
    let one : LRV.Term (Fin 1 ⊕ Fin 1) := .func Fn.vfOne Fin.elim0
    let φ : LRV.BoundedFormula (Fin 1) 1 := .equal t one
    have hw : WellSorted p.sorts (fun _ => .vf) φ := by
      apply WellSorted.equal (s := .vf)
      · apply tmSort_func
        intro i; fin_cases i <;> rfl
      · apply tmSort_func
        intro i; exact i.elim0
    have heval (z : Fin 1 → M) : φ.Realize p.values z ↔ iVFMul x.val (z 0) = iVFOne := by
      have ht : t.realize (Sum.elim p.values z) = iVFMul x.val (z 0) := by
        change Structure.funMap (L := LRV) Fn.vfMul _ =
          Structure.funMap (L := LRV) Fn.vfMul ![x.val, z 0]
        congr 1
        funext i; fin_cases i <;> rfl
      have ho : one.realize (Sum.elim p.values z) = iVFOne := by
        change Structure.funMap (L := LRV) Fn.vfOne _ =
          Structure.funMap (L := LRV) Fn.vfOne Fin.elim0
        congr 1
        funext i; exact i.elim0
      change t.realize _ = one.realize _ ↔ _
      rw [ht, ho]
    have hnamed : DefinableClosureAt ({x.val} : Set M) .vf (x⁻¹).val := by
      constructor
      · refine ⟨p, φ, hw, ?_⟩
        ext z
        change z 0 = (x⁻¹).val ↔ (∀ i, sortEval .vf (z i)) ∧ φ.Realize p.values z
        rw [heval]
        constructor
        · intro hz
          refine ⟨?_, ?_⟩
          · intro i; fin_cases i; exact hz ▸ (x⁻¹).property
          · rw [hz]
            have hm : x * x⁻¹ = (1 : VFType (M := M)) := mul_inv_cancel₀ hx0
            exact congrArg Subtype.val hm
        · rintro ⟨hz, hp⟩
          let y : VFType (M := M) := ⟨z 0, hz 0⟩
          have hprod : x * y = 1 := Subtype.ext hp
          have hy : y = x⁻¹ := by
            calc
              y = x⁻¹ * (x * y) := by rw [← mul_assoc, inv_mul_cancel₀ hx0, one_mul]
              _ = x⁻¹ := by rw [hprod, mul_one]
          exact congrArg Subtype.val hy
      · rintro y rfl
        exact (x⁻¹).property
    apply hnamed.eliminate_sorted_definable_params
    intro b hb
    have hb' := Set.mem_singleton_iff.mp hb
    subst b
    exact ⟨.vf, hx⟩

end SpecialTransformations.Section3
