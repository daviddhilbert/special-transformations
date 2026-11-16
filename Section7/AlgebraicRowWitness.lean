module

public import Section3.GammaBaseDescent
public import Section3.GammaParameterBridge
public import Section3.RVGammaAlgebraicity
public import Section3.SmallFiniteParameters

@[expose] public section

/-!
# A finite original-real-base witness for Lemma 7.4

Remove Gamma names from the RV algebraicity witness by the checked
Section 3 theorem, then promote the named input tuple into variables and
cut finite rows. The output uses exactly the original real base, and is
ready for the checked guarded rational normal form.
-/

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

set_option backward.isDefEq.respectTransparency false

namespace SpecialTransformations.Section7

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem originalBase_finite_RV_row {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : Base (M := M)) (hsmall : Cardinal.mk B.real < κ) {n : ℕ}
    (t : Fin (n + 1) → CanonicalRV.RVSort M)
    (hb : AlgebraicAtBase ⟨B.real ∪ Set.range (fun i : Fin n => (t i.castSucc).val), B.gamma⟩
      .rv (t (Fin.last n)).val) :
    ∃ A : Set (Fin (n + 1) → M), DefinableOver B.real (fun _ => .rv) A ∧
      (fun j => (t j).val) ∈ A ∧
      {x | Fin.snoc (fun i : Fin n => (t i.castSucc).val) x ∈ A}.Finite := by
  let a : Fin n → M := fun i => (t i.castSucc).val
  let b := (t (Fin.last n)).val
  let S := B.real ∪ Set.range a
  have hS : Cardinal.mk S < κ := small_union_range hκ B.real hsmall a
  have hbr : AlgebraicAt S .rv b :=
    (algebraic_rv_gamma_base_iff hκ hs h00 ⟨S, B.gamma⟩ hS b).mp hb
  let B₀ : Base (M := M) := ⟨B.real, ∅⟩
  have hb₀ : AlgebraicAtBase ⟨B₀.real ∪ Set.range a, B₀.gamma⟩ .rv b :=
    (algebraic_base_empty_iff S .rv b).mpr hbr
  obtain ⟨R, hR⟩ := good_base_relation_of_algebraic B₀ (fun _ : Fin n => .rv) a
    (fun i => (t i.castSucc).property) .rv b hb₀
  let A : Set (Fin (n + 1) → M) := {z | (Fin.init z, z (Fin.last n)) ∈ R.carrier}
  have hsort : Fin.lastCases .rv (fun _ : Fin n => .rv) = (fun _ => SortTag.rv) := by
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp
    · simp
  have hD : DefinableOverBase B₀ (fun _ => .rv) A := by
    simpa only [hsort] using R.definable
  refine ⟨A, (base_empty_iff B.real (fun _ => .rv) A).mp hD, hR, ?_⟩
  simpa only [A, Set.mem_ofPred_eq, Fin.init_snoc, Fin.snoc_last] using R.finite a

end SpecialTransformations.Section7
