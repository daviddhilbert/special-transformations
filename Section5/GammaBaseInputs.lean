import Section5.GammaExistence
import Section3.GammaSpecialization

/-! Internal real presentations for genuinely Gamma-named definable sets.
All conclusions about the original set continue to use its invariant full
preimage. The chosen codes serve only to obtain a real presentation. -/

set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace SpecialTransformations.Section5

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {n m : ℕ} {S : Set M}

local notation "N" => (@CanonicalStructure.normalize M sM)

omit hM in
private theorem gammaPointCode_injective :
    Function.Injective (gammaPointCode (M := M) (n := n) (m := m)) := by
  intro p q h
  apply Prod.ext
  · funext i
    apply Subtype.ext
    simpa only [gammaPointCode, vfAt, Fin.append_left] using congrFun h (Fin.castAdd m i)
  · funext i
    apply Subtype.ext
    simpa only [gammaPointCode, Fin.append_right] using congrFun h (Fin.natAdd n i)

private theorem pointDefinable_of_flatCode (A : Set (Point (M := M) n m))
    (hA : DefinableOver S (gammaPointSort n m) (gammaPointCode '' A)) :
    SetDefinable (pointSpace n m) S A := by
  let e : Fin n ⊕ Fin m ≃ Fin (n + m) := finSumFinEquiv
  let P := pointSpace (M := M) n m
  have hraw := (definableOver_iff_normalized_raw S (gammaPointSort n m) _).mp hA
  have hp (c : pDomain P) : gammaPointCode (pDecode P c) = c.val ∘ e.symm := by
    funext i
    cases i using Fin.addCases with
    | left i => simp only [gammaPointCode, vfAt, Fin.append_left, Function.comp_apply,
        e, finSumFinEquiv_symm_apply_castAdd]; rfl
    | right i => simp only [gammaPointCode, Fin.append_right, Function.comp_apply,
        e, finSumFinEquiv_symm_apply_natAdd]; rfl
  have hdom (z : Fin n ⊕ Fin m → M) (hz : z ∘ e.symm ∈ gammaPointCode '' A) :
      z ∈ pDomain P := by
    refine ⟨fun i => ?_, fun i => ?_⟩
    · have hh := hraw.2 _ hz (Fin.castAdd m i)
      simpa only [gammaPointSort, Fin.append_left, Function.comp_apply,
        e, finSumFinEquiv_symm_apply_castAdd] using hh
    · have hh := hraw.2 _ hz (Fin.natAdd n i)
      simpa only [gammaPointSort, Fin.append_right, Function.comp_apply,
        e, finSumFinEquiv_symm_apply_natAdd] using hh
  have he : @DefinableGeometry.Space.preimage LRV M N P A =
      (fun z : Fin n ⊕ Fin m → M => z ∘ e.symm) ⁻¹' (gammaPointCode '' A) := by
    ext z
    constructor
    · rintro ⟨hz, ha⟩
      exact ⟨pDecode P ⟨z, hz⟩, ha, hp ⟨z, hz⟩⟩
    · intro hz
      have hd := hdom z hz
      obtain ⟨p, hpA, hcode⟩ := hz
      have h := gammaPointCode_injective ((hp ⟨z, hd⟩).trans hcode.symm)
      refine ⟨hd, ?_⟩
      change pDecode P ⟨z, hd⟩ ∈ A
      exact h.symm ▸ hpA
  change @Set.Definable M S LRV N (Fin n ⊕ Fin m)
    (@DefinableGeometry.Space.preimage LRV M N P A)
  rw [he]
  exact @Set.Definable.preimage_comp M S LRV N _ _ e.symm _ hraw.1

theorem gammaPresentationInput (B : GammaParameters.Base (M := M)) :
    GammaPresentationInput B := by
  intro n m A hA
  obtain ⟨d, γ, hγ, h⟩ := hA
  let t := GammaParameters.representatives γ
  have ht := GammaParameters.representatives_values γ
  have hD := pointDefinable_of_flatCode A (h.specialize t ht)
  refine ⟨d, t, ?_, PresentedSet.mk A hD, rfl⟩
  intro i
  have hi : GammaParameters.value (t i) = γ i := congrFun ht i
  rw [hi]
  exact hγ i

end SpecialTransformations.Section5
