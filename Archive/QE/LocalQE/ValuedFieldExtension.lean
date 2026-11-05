import VFGeneratedFinish
import VFAlgClosed

set_option backward.isDefEq.respectTransparency false

/-! The ordinary valued-field extension interface and its application to the
actual VF reduct. This interface was originally an authorized Marker-notes
input. `JohnsonValuedExtension.markerNotesProposition45` now proves it from
the repository's Johnson theorem, and the RV assembly uses that proof. -/

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open ValuedReduct

namespace ValuedFieldExtension

def fieldFunction {E : Type} [Field E] : {k : ℕ} → VFn k → (Fin k → E) → E
  | _, .zero, _ => 0
  | _, .one, _ => 1
  | _, .add, xs => xs 0 + xs 1
  | _, .neg, xs => -xs 0
  | _, .mul, xs => xs 0 * xs 1

/-- A language structure is the usual valued-field structure, with the binary
relation interpreted in multiplicative valuation order. -/
structure InterpretsValuation {E Γ : Type} [Field E]
    [LinearOrderedCommGroupWithZero Γ] [LVal.Structure E] (v : Valuation E Γ) : Prop where
  functions : ∀ {k : ℕ} (f : VFn k) (xs : Fin k → E),
    Structure.funMap (L := LVal) f xs = fieldFunction f xs
  comparison : ∀ xs : Fin 2 → E,
    Structure.RelMap (L := LVal) VRel.le xs ↔ v (xs 0) ≤ v (xs 1)

/-- The ordinary extension interface, proved downstream from Johnson's QE.
Its original standard-reference source was Marker,
*Model Theory of Valued Fields* (2018 lecture notes), Proposition 4.5, printed
page 37: an embedding of a subring of an algebraically closed nontrivially
valued field extends to the whole field in a sufficiently saturated target.

We use its subfield special case. The notes' additive valuation divisibility
predicate is replaced by the reversed multiplicative comparison. The notes'
valuation-ring predicate is quantifier-free definable by comparison with 1.
Thus this is the same valued-field language up to that definitional convention.
Both valuations are genuinely nontrivial. No RV map or RV theorem is quoted.

Source: https://homepages.math.uic.edu/~marker/valued_fields.pdf
-/
def MarkerNotesProposition45 : Prop :=
  ∀ (E F Γ Δ : Type) [Field E] [Field F] [IsAlgClosed E] [IsAlgClosed F]
    [LinearOrderedCommGroupWithZero Γ] [LinearOrderedCommGroupWithZero Δ]
    [LVal.Structure E] [LVal.Structure F]
    (v : Valuation E Γ) (w : Valuation F Δ),
    InterpretsValuation v → InterpretsValuation w →
    (∃ x : E, x ≠ 0 ∧ v x ≠ 1) → (∃ x : F, x ≠ 0 ∧ w x ≠ 1) →
    MarkerBridge.SatAt LVal F (Order.succ (Cardinal.mk E)) →
    ∀ (A : Subfield E) (g : A →+* F),
      (∀ a b : A, w (g a) ≤ w (g b) ↔ v a.1 ≤ v b.1) →
      ∃ G : E →+* F, (∀ a : A, G a.1 = g a) ∧
        (∀ a b : E, w (G a) ≤ w (G b) ↔ v a ≤ v b)

theorem satAt_mono {L : Language} {E : Type} [L.Structure E] {κ θ : Cardinal}
    (hκθ : κ ≤ θ) (h : MarkerBridge.SatAt L E θ) : MarkerBridge.SatAt L E κ := by
  intro A g hA p hp
  exact h A g (lt_of_lt_of_le hA hκθ) p hp

section Model

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem interprets_valuation {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ a b, VFValued.predV a b ↔ v a ≤ v b) : InterpretsValuation v where
  functions f xs := by cases f <;> rfl
  comparison xs := hv (xs 0) (xs 1)

/-- The nontriviality axiom supplies a nonzero VF element with value below 1.
The reversed predV convention is retained explicitly. -/
theorem exists_nontrivial_predV : ∃ a : VFType (M := M), a ≠ 0 ∧ ¬ VFValued.predV 1 a := by
  have h := hM.realize_of_mem Axioms.axNontrivialRV
    (mem_ACVF_repairRV (by simp [Axioms.repairRV, Axioms.ofList]))
  have hsnoc (a : M) : (Fin.snoc (default : Fin 0 → M) a : Fin 1 → M) 0 = a := by
    change (Fin.snoc (default : Fin 0 → M) a : Fin 1 → M) (Fin.last 0) = a
    exact Fin.snoc_last _ _
  have hh : ∃ a : M, iVF a ∧ (a ≠ iVFZero ∧ ¬ iLe (iRv a) (iRv iVFOne)) := by
    simpa [Axioms.axNontrivialRV, exSorted, sortPred, Sentence.Realize, Formula.Realize,
      BoundedFormula.realize_ex, BoundedFormula.realize_inf, BoundedFormula.realize_not,
      pVF_realize, pEq, BoundedFormula.realize_bdEqual, realize_tRv, realize_tVFZero,
      realize_tVFOne, realize_pLe, realize_tv, hsnoc] using h
  obtain ⟨a, ha, ha0, ha1⟩ := hh
  exact ⟨⟨a, ha⟩, fun he => ha0 (congrArg Subtype.val he), ha1⟩

theorem valuation_nontrivial {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ a b, VFValued.predV a b ↔ v a ≤ v b) :
    ∃ a : VFType (M := M), a ≠ 0 ∧ v a ≠ 1 := by
  obtain ⟨a, ha0, ha1⟩ := exists_nontrivial_predV (M := M)
  refine ⟨a, ha0, ?_⟩
  intro he
  apply ha1 ((hv 1 a).mpr ?_)
  rw [Valuation.map_one, he]

end Model

section Extension

variable {M N : Type} [LRV.Structure M] [LRV.Structure N]
variable [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]

/-- Genuine tagged saturation, the separately proved reduct interpretation,
and the ordinary extension interface produce an actual field map.
There is no uninterpreted theory T or unproved model-of-T premise. -/
theorem valuedExtension_of_notes (hNotes : MarkerNotesProposition45)
    (hSat : MarkerBridge.SatAt LRV N (Order.succ (Cardinal.mk M)))
    (K : Subfield (VFType (M := M))) (g : K →+* VFType (M := N))
    (hg : ∀ a b : K, VFValued.predV (g a) (g b) ↔ VFValued.predV a.1 b.1) :
    Nonempty (VFGeneratedFinish.ValuedExtension K g) := by
  letI : IsAlgClosed (VFType (M := M)) := VFAlgClosed.isAlgClosed_vfType
  letI : IsAlgClosed (VFType (M := N)) := VFAlgClosed.isAlgClosed_vfType
  obtain ⟨Γ, hΓ, v, hv⟩ := VFValued.exists_valuation_predV (M := M)
  obtain ⟨Δ, hΔ, w, hw⟩ := VFValued.exists_valuation_predV (M := N)
  letI := hΓ
  letI := hΔ
  have hsize : Cardinal.mk (VFType (M := M)) ≤ Cardinal.mk M :=
    Cardinal.mk_le_of_injective (f := (Subtype.val : VFType (M := M) → M)) Subtype.val_injective
  have hSat' : MarkerBridge.SatAt LVal (VFType (M := N))
      (Order.succ (Cardinal.mk (VFType (M := M)))) :=
    satAt_mono (Order.succ_le_succ hsize) (ValuedReduct.satAt_valuedReduct hSat)
  have hg' : ∀ a b : K, w (g a) ≤ w (g b) ↔ v a.1 ≤ v b.1 :=
    fun a b => (hw (g a) (g b)).symm.trans ((hg a b).trans (hv a.1 b.1))
  obtain ⟨G, hG, hcomp⟩ := hNotes (VFType (M := M)) (VFType (M := N)) Γ Δ v w
    (interprets_valuation v hv) (interprets_valuation w hw)
    (valuation_nontrivial v hv) (valuation_nontrivial w hw) hSat' K g hg'
  exact ⟨{
    hom := G
    comparison := fun a b => (hw (G a) (G b)).trans ((hcomp a b).trans (hv a b).symm)
    agrees := hG
  }⟩

end Extension
end ValuedFieldExtension

#print axioms ValuedFieldExtension.exists_nontrivial_predV
#print axioms ValuedFieldExtension.valuation_nontrivial
#print axioms ValuedFieldExtension.valuedExtension_of_notes
