import ACVFQE
import Section3.ParameterBridge
import Section3.DefinableCompactness
import Section3.AlgebraicityDescent
import Section3.TupleDescent
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem raw_definable_sorted (hc : CanonicalStructure.IsCanonical (M := M))
    (A s : Set M) (σ : SortTag) (hraw : A.Definable₁ LRV s)
    (hsubset : s ⊆ {x | sortEval σ x}) : DefinableAt A σ s := by
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
    · have hr := (TypedModelMap.sort_cover (M := M) (values i)).resolve_left hi
      dsimp only [sorts]
      rw [if_neg hi]
      exact hr
  let p : Parameters A := ⟨B.card, values, sorts, hsorts,
    fun i => hBA (e.symm i).property⟩
  obtain ⟨ψ, hψ⟩ := raw_definable_formula hB
  let χ : LRV.BoundedFormula (Fin B.card) 1 :=
    ψ.relabel (fun b => Sum.inl (e b))
  have hχ (x : M) : χ.Realize p.values ![x] ↔ x ∈ s := by
    dsimp only [χ]
    rw [BoundedFormula.realize_relabel]
    have hv : Sum.elim p.values (![x] ∘ Fin.castAdd 1) ∘ (fun b => Sum.inl (e b)) =
        (Subtype.val : ↥B → M) := by
      funext b
      simp [p, values, Function.comp_def]
    have hx : (![x] ∘ Fin.natAdd 0 : Fin 1 → M) = ![x] := by
      funext i; fin_cases i; rfl
    rw [hv, hx]
    exact hψ x
  obtain ⟨q, hq, heq⟩ := LocalAssembly.fullQE (Fin B.card) 1 χ
  let q' := CanonicalStructure.sortedQF p.sorts (fun _ : Fin 1 => σ) q
  have hw : WellSorted p.sorts (fun _ : Fin 1 => σ) q' :=
    CanonicalStructure.sortedQF_wellSorted p.sorts (fun _ => σ) q
  have hq' (x : M) (hx : sortEval σ x) : q'.Realize p.values ![x] ↔ x ∈ s := by
    have hxs : ∀ i : Fin 1, sortEval σ (![x] i) := by intro i; fin_cases i; exact hx
    exact (CanonicalStructure.sortedQF_realize hM hc p.sorts (fun _ => σ) p.values ![x]
      p.sorted hxs q hq).trans
      ((heq M (CanonicalTheory.model_CanonicalACVF_iff.mpr ⟨hM, hc⟩) p.values ![x]).symm.trans (hχ x))
  refine ⟨⟨p, q', hw, ?_⟩, hsubset⟩
  ext x
  have hvec : ![x 0] = x := by funext i; fin_cases i; rfl
  constructor
  · intro hx
    have hsx := hsubset hx
    refine ⟨fun i => by fin_cases i; exact hsx, ?_⟩
    exact hvec ▸ (hq' (x 0) hsx).mpr hx
  · rintro ⟨hx, hqx⟩
    exact (hq' (x 0) (hx 0)).mp (hvec ▸ hqx)
theorem algebraicAt_iff_raw (hc : CanonicalStructure.IsCanonical (M := M))
    (A : Set M) (σ : SortTag) (x : M) :
    AlgebraicAt A σ x ↔ RawClosure.AlgebraicOver A x ∧ sortEval σ x := by
  constructor
  · intro hx
    exact ⟨hx.raw_finite_witness, hx.sorted⟩
  · rintro ⟨⟨t, ht, hf, hxt⟩, hxσ⟩
    let u := t ∩ {y | sortEval σ y}
    have hσdef := (definableAt_sort A σ).raw_definable
    have hudef : A.Definable₁ LRV u := ht.inter hσdef
    have husub : u ⊆ {y | sortEval σ y} := Set.inter_subset_right
    exact ⟨u, raw_definable_sorted hc A u σ hudef husub,
      hf.subset Set.inter_subset_left, hxt, hxσ⟩

/-- Unary case of Lemma 3.1, in the actual sorted closure API.
The canonical assumption fixes only off-sort interpretations in the tagged
encoding. Both closure directions are proved above; there is no compactness
or algebraicity-descent conclusion assumed as an input. -/
theorem lemma_3_1_unary (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) (S A : Set M) (b : M)
    (hsmall : Cardinal.mk ↥(insert b S) < κ) (τ σ : SortTag)
    (hA : DefinableAt S τ A) (hne : A.Nonempty)
    (hb : ∀ a ∈ A, AlgebraicAt (insert a S) σ b) : AlgebraicAt S σ b := by
  obtain ⟨a₀, ha₀⟩ := hne
  have hbσ := (hb a₀ ha₀).sorted
  apply (algebraicAt_iff_raw hc S σ b).mpr
  refine ⟨?_, hbσ⟩
  apply RawClosure.algebraicity_descent_raw hs S A b hsmall hA.raw_definable ⟨a₀, ha₀⟩
  intro a ha
  exact (hb a ha).raw_finite_witness

/-- Lemma 3.1 for a nonempty definable family of any finite mixed tuple arity.
Parameters of a point are all its coordinates. The base remains the original
arbitrary small set S; the size bound after adjoining b is proved, not assumed. -/
theorem lemma_3_1 (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (S : Set M) (hsmall : Cardinal.mk S < κ) {n : ℕ} (sn : Fin n → SortTag)
    (A : Set (Fin n → M)) (b : M) (σ : SortTag)
    (hA : DefinableOver S sn A) (hne : A.Nonempty)
    (hb : ∀ a ∈ A, AlgebraicAt (S ∪ Set.range a) σ b) : AlgebraicAt S σ b := by
  obtain ⟨a₀, ha₀⟩ := hne
  apply (algebraicAt_iff_raw hc S σ b).mpr
  refine ⟨?_, (hb a₀ ha₀).sorted⟩
  apply RawClosure.Tuple.algebraicity_descent_raw hs S A b (small_insert hκ S hsmall b)
    hA.raw_definable ⟨a₀, ha₀⟩
  intro a ha
  exact (hb a ha).raw_finite_witness

end SpecialTransformations.Section3
