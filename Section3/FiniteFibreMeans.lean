import Section3.FibreEnumerations
import Section3.BarycentreSyntax
import Section3.Barycentre
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.Barycentre
open RawClosure.Tuple
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n : ℕ}

def finiteFibreRelation (F : (Fin n → M) → Finset (VFType (M := M))) :
    Set ((Fin n → M) × M) := {p | ∃ x ∈ F p.1, x.val = p.2}

omit hM in
theorem finiteFibre_enumeration_exists
    (F : (Fin n → M) → Finset (VFType (M := M))) (t : Fin n → M) :
    ∃ c : Fin (F t).card → M, Enumerates (finiteFibreRelation F) (F t).card t c := by
  let e := Finset.equivFin (F t)
  let c (i : Fin (F t).card) : M := (e.symm i).val.val
  refine ⟨c, ?_, ?_, ?_⟩
  · intro i j hij
    exact e.symm.injective (Subtype.ext (Subtype.ext hij))
  · intro i
    exact ⟨(e.symm i).val, (e.symm i).property, rfl⟩
  · rintro b ⟨x, hx, rfl⟩
    refine ⟨e ⟨x, hx⟩, ?_⟩
    simp only [c, Equiv.symm_apply_apply]

theorem enumerated_mean_equation (h00 : M ⊨ Axioms.ACVF00)
    (F : (Fin n → M) → Finset (VFType (M := M))) (t : Fin n → M)
    {k : ℕ} (hk : k ≠ 0) (c : Fin k → M)
    (hc : Enumerates (finiteFibreRelation F) k t c) (z : VFType (M := M)) :
    (linearTerm k).realize (Sum.elim (fun _ => z.val) c) = iVFZero ↔
      z = mean (F t) := by
  have hsort (i : Fin k) : iVF (c i) := by
    obtain ⟨x, _, hx⟩ := hc.2.1 i
    change x.val = c i at hx
    rw [← hx]
    exact x.property
  let C (i : Fin k) : VFType (M := M) := ⟨c i, hsort i⟩
  have hmem (i : Fin k) : C i ∈ F t := by
    obtain ⟨x, hx, he⟩ := hc.2.1 i
    have hxc : x = C i := Subtype.ext he
    exact hxc ▸ hx
  let e0 (i : Fin k) : ↥(F t) := ⟨C i, hmem i⟩
  have he0 : Function.Bijective e0 := by
    constructor
    · intro i j hij
      exact hc.1 (congrArg (fun x : ↥(F t) => x.val.val) hij)
    · intro x
      have htx : (t, x.val.val) ∈ finiteFibreRelation F := ⟨x.val, x.property, rfl⟩
      obtain ⟨i, hi⟩ := hc.2.2 x.val.val htx
      exact ⟨i, Subtype.ext (Subtype.ext hi)⟩
  let e : Fin k ≃ ↥(F t) := Equiv.ofBijective e0 he0
  have hcval : (fun i => (C i).val) = c := rfl
  rw [← hcval, linearTerm_realize]
  have heq : ((k : VFType (M := M)) * z - ∑ i, C i).val = iVFZero ↔
      (k : VFType (M := M)) * z - ∑ i, C i = 0 :=
    ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  exact heq.trans (sub_eq_zero.trans (mean_equation_of_equiv h00 (F t) hk e z))

end SpecialTransformations.Section3.Barycentre
