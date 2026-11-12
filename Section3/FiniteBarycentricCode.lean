module

public import Section3.Barycentre

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.Barycentre
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

noncomputable def fibre (A : Finset (VFType (M := M))) (x : VFType (M := M)) :=
  A.filter (fun y => iRv (y - mean A).val = iRv (x - mean A).val)

/-- An explicit finite RV code, formed by successive barycentric splittings.
Definability of the uniform finite-family construction is a separate theorem. -/
noncomputable def code : (d : ℕ) → Finset (VFType (M := M)) → VFType (M := M) → Fin d → M
  | 0, _, _ => Fin.elim0
  | d + 1, A, x => Fin.cons (iRv (x - mean A).val) (code d (fibre A x) x)

theorem code_sorted (d : ℕ) (A : Finset (VFType (M := M))) (x : VFType (M := M)) :
    ∀ i, iRV (code d A x i) := by
  induction d generalizing A x with
  | zero => intro i; exact i.elim0
  | succ d ih =>
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact rv_mem hM (x - mean A).property
    · exact ih (fibre A x) x j

theorem code_injective_of_card_le (h00 : M ⊨ Axioms.ACVF00) (d : ℕ)
    (A : Finset (VFType (M := M))) (hcard : A.card ≤ d + 1) :
    Set.InjOn (code d A) (A : Set (VFType (M := M))) := by
  induction d generalizing A with
  | zero =>
    intro x hx y hy _
    exact (Finset.card_le_one_iff.mp hcard) hx hy
  | succ d ih =>
    intro x hx y hy hxy
    by_cases hsmall : A.card ≤ 1
    · exact (Finset.card_le_one_iff.mp hsmall) hx hy
    · have htwo : 2 ≤ A.card := by omega
      have hfirst : iRv (x - mean A).val = iRv (y - mean A).val := congrFun hxy 0
      have hfib : fibre A x = fibre A y := by
        unfold fibre
        rw [hfirst]
      have htail : code d (fibre A x) x = code d (fibre A x) y := by
        have ht := congrArg (fun z : Fin (d + 1) → M => Fin.tail z) hxy
        change code d (fibre A x) x = code d (fibre A y) y at ht
        rwa [← hfib] at ht
      have hbound : (fibre A x).card ≤ d + 1 := by
        have := fibre_card_lt h00 A htwo (iRv (x - mean A).val)
        change (fibre A x).card < A.card at this
        omega
      apply ih (fibre A x) hbound
      · exact Finset.mem_filter.mpr ⟨hx, rfl⟩
      · exact Finset.mem_filter.mpr ⟨hy, hfirst.symm⟩
      · exact htail

/-- The explicit construction separates every point of the finite VF set.
This is the combinatorial part of 3.9; it does not by itself assert an
original-base definable graph. -/
theorem code_injective (h00 : M ⊨ Axioms.ACVF00) (A : Finset (VFType (M := M))) :
    Set.InjOn (code A.card A) (A : Set (VFType (M := M))) :=
  code_injective_of_card_le h00 A.card A (Nat.le_succ _)

end SpecialTransformations.Section3.Barycentre
