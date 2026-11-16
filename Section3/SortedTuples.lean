module

public import Section3.ClosureBridge
public import Section3.CanonicalParameters
public import Section3.DefinableConstants

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- Raw-to-sorted definability for any finite mixed tuple in a canonical model. -/
theorem raw_definableOver_sorted (hc : CanonicalStructure.IsCanonical (M := M))
    (A : Set M) {n : ℕ} (sn : Fin n → SortTag) (s : Set (Fin n → M))
    (hraw : A.Definable LRV s) (hsubset : ∀ x ∈ s, ∀ i, sortEval (sn i) (x i)) :
    DefinableOver A sn s := by
  classical
  obtain ⟨B, hBA, hB⟩ := Set.definable_iff_finitely_definable.mp hraw
  let e : ↥B ≃ Fin B.card := Finset.equivFin B
  let values (i : Fin B.card) : M := (e.symm i).val
  let sorts (i : Fin B.card) : SortTag := if iVF (values i) then .vf else .rv
  have hsorts (i : Fin B.card) : sortEval (sorts i) (values i) := by
    by_cases hi : iVF (values i)
    · dsimp only [sorts]
      rw [if_pos hi]
      exact hi
    · dsimp only [sorts]
      rw [if_neg hi]
      exact (TypedModelMap.sort_cover (M := M) (values i)).resolve_left hi
  let p : Parameters A := ⟨B.card, values, sorts, hsorts,
    fun i => hBA (e.symm i).property⟩
  obtain ⟨ψ, hψ⟩ := raw_definable_formula_tuple hB
  let χ : LRV.BoundedFormula (Fin B.card) n := BoundedFormula.relabelEquiv e ψ
  have hχ (x : Fin n → M) : χ.Realize p.values x ↔ x ∈ s := by
    dsimp only [χ]
    rw [BoundedFormula.realize_relabelEquiv]
    have hv : p.values ∘ e = (Subtype.val : ↥B → M) := by
      funext b
      simp [p, values]
    rw [hv]
    exact hψ x
  obtain ⟨q, hq, heq⟩ := LocalAssembly.fullQE (Fin B.card) n χ
  let q' := CanonicalStructure.sortedQF p.sorts sn q
  refine ⟨p, q', CanonicalStructure.sortedQF_wellSorted p.sorts sn q, ?_⟩
  have hq' (x : Fin n → M) (hx : ∀ i, sortEval (sn i) (x i)) :
      q'.Realize p.values x ↔ x ∈ s :=
    (CanonicalStructure.sortedQF_realize hM hc p.sorts sn p.values x p.sorted hx q hq).trans
      ((heq M (CanonicalTheory.model_CanonicalACVF_iff.mpr ⟨hM, hc⟩) p.values x).symm.trans (hχ x))
  ext x
  exact ⟨fun hx => ⟨hsubset x hx, (hq' x (hsubset x hx)).mpr hx⟩,
    fun hx => (hq' x hx.1).mp hx.2⟩

/-- Parameter elimination for sorted definable sets in all finite arities. -/
theorem DefinableOver.eliminate_sorted_definable_params {S B : Set M} {n : ℕ}
    {sn : Fin n → SortTag} {s : Set (Fin n → M)} (hs : DefinableOver B sn s)
    (hB : ∀ b ∈ B, ∃ τ, DefinableClosureAt S τ b) : DefinableOver S sn s := by
  let N := CanonicalStructure.normalize (M := M)
  letI := sM
  have hN : @Theory.Model LRV M N Axioms.ACVF := CanonicalStructure.normalized_model hM
  have hcan : @CanonicalStructure.IsCanonical M N := CanonicalStructure.normalize_isCanonical
  have hBn (b : M) (hb : b ∈ B) : @Set.Definable₁ M S LRV N {b} := by
    obtain ⟨τ, hb'⟩ := hB b hb
    have hn := (definableClosureAt_normalize_iff S τ b).mpr hb'
    exact @DefinableAt.raw_definable M N S τ {b} hn
  have hsn := (definableOver_normalize_iff B sn s).mpr hs
  have hraw : @Set.Definable M S LRV N (Fin n) s :=
    @DefinableConstants.eliminate_parameters M LRV N S B n s hBn
      (@DefinableOver.raw_definable M N B n sn s hsn)
  have hsort : ∀ x ∈ s, ∀ i, @sortEval M N (sn i) (x i) := by
    obtain ⟨p, φ, hw, he⟩ := hsn
    intro x hx
    exact (he ▸ hx).1
  have hout := @raw_definableOver_sorted M N hN hcan S n sn s hraw hsort
  exact (definableOver_normalize_iff S sn s).mp hout

end SpecialTransformations.Section3
