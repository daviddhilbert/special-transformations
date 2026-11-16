module

public import Section6.NativeResidueOperations

@[expose] public section

/-! The recovered valued field and its leading terms present the original
tagged henselian model. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer TrivCase

namespace SpecialTransformations.Section6.NativePresentation

open NativeField NativeValuation NativeRV ConcreteValued

variable {M Γ : Type} [LRV.Structure M] [LinearOrderedCommGroupWithZero Γ]
variable [hM : M ⊨ HenselianTheory.valuedField]
variable (v : Valuation (NativeField.VF M) Γ)
variable (hv : ∀ a b, NativeValuation.predV a b ↔ v a ≤ v b)
local instance : LRV.Structure (Carrier v) := nativeStructure v

private theorem cover (z : M) : iVF z ∨ iRV z := by
  have hmem : Axioms.sdCover ∈ HenselianTheory.valuedField := by
    simp [HenselianTheory.valuedField, Axioms.sortAxioms, Axioms.ofList]
  have h := sentence_realize hM hmem
  simp only [Axioms.sdCover, allOne, Sentence.Realize, BoundedFormula.realize_alls,
    BoundedFormula.realize_sup, pVF_realize, pRVsort_realize, RVCalc.realize_var_inr] at h
  exact h ![z]

private theorem disjoint {z : M} (hz : iVF z) : ¬ iRV z := by
  have hmem : Axioms.sdDisjoint ∈ HenselianTheory.valuedField := by
    simp [HenselianTheory.valuedField, Axioms.sortAxioms, Axioms.ofList]
  have h := sentence_realize hM hmem
  simp only [Axioms.sdDisjoint, allOne, Sentence.Realize, BoundedFormula.realize_alls,
    BoundedFormula.realize_not, BoundedFormula.realize_inf, pVF_realize, pRVsort_realize,
    RVCalc.realize_var_inr] at h
  exact fun hr => h ![z] ⟨hz, hr⟩

def pack : Carrier v → M := Sum.elim Subtype.val (fun q => (equiv v hv q).val)

theorem pack_sort (s : SortTag) (x : Carrier v) :
    sortEval s (pack v hv x) ↔ hasSort v s x := by
  cases s <;> cases x with
  | inl x =>
    first
    | exact ⟨fun _ => trivial, fun _ => x.property⟩
    | exact ⟨fun h => disjoint x.property h, False.elim⟩
  | inr q =>
    first
    | exact ⟨fun h => disjoint h (equiv v hv q).property, False.elim⟩
    | exact ⟨fun _ => trivial, fun _ => (equiv v hv q).property⟩

theorem pack_bijective : Function.Bijective (pack v hv) := by
  constructor
  · intro x y h
    cases x with
    | inl a =>
      cases y with
      | inl b => exact congrArg Sum.inl (Subtype.ext h)
      | inr q =>
        have he : a.val = (equiv v hv q).val := h
        exact (disjoint a.property (he.symm ▸ (equiv v hv q).property)).elim
    | inr q =>
      cases y with
      | inl a =>
        have he : (equiv v hv q).val = a.val := h
        exact (disjoint a.property (he ▸ (equiv v hv q).property)).elim
      | inr r => exact congrArg Sum.inr ((equiv v hv).injective (Subtype.ext h))
  · intro z
    rcases cover z with hz | hz
    · exact ⟨.inl ⟨z, hz⟩, rfl⟩
    · obtain ⟨q, hq⟩ := (equiv v hv).surjective ⟨z, hz⟩
      exact ⟨.inr q, congrArg Subtype.val hq⟩

private theorem model_relation_sort (hc : M ⊨ HenselianTheory.canonicalNative)
    {n : ℕ} (r : Rel n) (z : Fin n → M) (hz : Structure.RelMap (L := LRV) r z) :
    ∀ i, sortEval (Rel.argSort r i) (z i) := by
  have h := sentence_realize hc (show HenselianTheory.nativeRelationSort r ∈
    HenselianTheory.canonicalNative from Or.inr ⟨n, r, rfl⟩)
  simp only [HenselianTheory.nativeRelationSort, Sentence.Realize, BoundedFormula.realize_alls,
    BoundedFormula.realize_imp, sortedHyps_realize] at h
  intro i
  cases hs : Rel.argSort r i with
  | vf =>
    change iVF (z i)
    simpa only [hs] using h z hz i
  | rv =>
    change iRV (z i)
    simpa only [hs] using h z hz i

private theorem tuple_one {A : Type} (z : Fin 1 → A) : z = ![z 0] := by
  funext i
  fin_cases i
  rfl

private theorem tuple_two {A : Type} (z : Fin 2 → A) : z = ![z 0, z 1] := by
  funext i
  fin_cases i <;> rfl

private theorem map_function (hc : M ⊨ HenselianTheory.canonicalNative)
    {n : ℕ} (f : Fn n) (z : Fin n → Carrier v) :
    pack v hv (Structure.funMap (L := LRV) f z) =
      Structure.funMap (L := LRV) f (pack v hv ∘ z) := by
  classical
  by_cases h : ∀ i, hasSort v (Fn.argSort f i) (z i)
  · rw [function_of_sorted v f z h]
    have hf (i : Fin n) (hi : Fn.argSort f i = .vf) : ∃ x, z i = Sum.inl x := by
      apply of_vf v
      change sortEval .vf (z i)
      rw [sortEval_iff, ← hi]
      exact h i
    have hr (i : Fin n) (hi : Fn.argSort f i = .rv) : ∃ q, z i = Sum.inr q := by
      apply of_rv v
      change sortEval .rv (z i)
      rw [sortEval_iff, ← hi]
      exact h i
    cases f with
    | vfZero =>
      rw [show pack v hv ∘ z = Fin.elim0 from Subsingleton.elim _ _] <;> rfl
    | vfOne =>
      rw [show pack v hv ∘ z = Fin.elim0 from Subsingleton.elim _ _] <;> rfl
    | vfAdd =>
      rw [tuple_two (pack v hv ∘ z)]
      obtain ⟨x, hx⟩ := hf 0 rfl
      obtain ⟨y, hy⟩ := hf 1 rfl
      change pack v hv (.inl (vfValue v (z 0) + vfValue v (z 1))) =
        iVFAdd (pack v hv (z 0)) (pack v hv (z 1))
      rw [hx, hy] <;> rfl
    | vfNeg =>
      rw [tuple_one (pack v hv ∘ z)]
      obtain ⟨x, hx⟩ := hf 0 rfl
      change pack v hv (.inl (-vfValue v (z 0))) = iVFNeg (pack v hv (z 0))
      rw [hx] <;> rfl
    | vfMul =>
      rw [tuple_two (pack v hv ∘ z)]
      obtain ⟨x, hx⟩ := hf 0 rfl
      obtain ⟨y, hy⟩ := hf 1 rfl
      change pack v hv (.inl (vfValue v (z 0) * vfValue v (z 1))) =
        iVFMul (pack v hv (z 0)) (pack v hv (z 1))
      rw [hx, hy] <;> rfl
    | rvMap =>
      rw [tuple_one (pack v hv ∘ z)]
      obtain ⟨x, hx⟩ := hf 0 rfl
      change pack v hv (.inr (RVCalc.rv v (vfValue v (z 0)))) = iRv (pack v hv (z 0))
      rw [hx]
      exact congrArg Subtype.val (equiv_rv v hv x)
    | rvZero =>
      rw [show pack v hv ∘ z = Fin.elim0 from Subsingleton.elim _ _]
      exact equiv_zero v hv
    | rvOne =>
      rw [show pack v hv ∘ z = Fin.elim0 from Subsingleton.elim _ _]
      exact equiv_one v hv
    | rvMul =>
      rw [tuple_two (pack v hv ∘ z)]
      obtain ⟨x, hx⟩ := hr 0 rfl
      obtain ⟨y, hy⟩ := hr 1 rfl
      change pack v hv (.inr (RVCalc.rvMul v (ConcreteValued.rvValue v (z 0))
        (ConcreteValued.rvValue v (z 1)))) = iRVMul (pack v hv (z 0)) (pack v hv (z 1))
      rw [hx, hy]
      exact equiv_mul v hv x y
    | rvInv =>
      rw [tuple_one (pack v hv ∘ z)]
      obtain ⟨x, hx⟩ := hr 0 rfl
      change pack v hv (.inr ((ConcreteValued.rvValue v (z 0)).map Inv.inv)) =
        iRVInvFn (pack v hv (z 0))
      rw [hx]
      exact equiv_inv v hv x
    | kAdd =>
      rw [tuple_two (pack v hv ∘ z)]
      obtain ⟨x, hx⟩ := hr 0 rfl
      obtain ⟨y, hy⟩ := hr 1 rfl
      change pack v hv (.inr (addResidue v (ConcreteValued.rvValue v (z 0))
        (ConcreteValued.rvValue v (z 1)))) = iKAdd (pack v hv (z 0)) (pack v hv (z 1))
      rw [hx, hy]
      exact equiv_addResidue v hv x y
    | kNeg =>
      rw [tuple_one (pack v hv ∘ z)]
      obtain ⟨x, hx⟩ := hr 0 rfl
      change pack v hv (.inr (negResidue v (ConcreteValued.rvValue v (z 0)))) =
        iKNeg (pack v hv (z 0))
      rw [hx]
      exact equiv_negResidue v hv x
  · have hmem : CanonicalTheory.functionAxiom f ∈ HenselianTheory.canonicalNative :=
      Or.inl ⟨n, f, rfl⟩
    have he := (CanonicalTheory.functionAxiom_realize f).mp (sentence_realize hc hmem)
      (pack v hv ∘ z) (fun hz => h (fun i => (pack_sort v hv _ _).mp (hz i)))
    change pack v hv (if _ then _ else _) = _
    rw [if_neg h, he]
    cases Fn.resSort f with
    | vf => rfl
    | rv => exact equiv_zero v hv

def presentation (hc : M ⊨ HenselianTheory.canonicalNative) : Carrier v ≃[LRV] M where
  toEquiv := _root_.Equiv.ofBijective _ (pack_bijective v hv)
  map_fun' := map_function v hv hc
  map_rel' := by
    intro n r z
    change Structure.RelMap (L := LRV) r (pack v hv ∘ z) ↔ Structure.RelMap (L := LRV) r z
    cases r with
    | memVF =>
      rw [tuple_one (pack v hv ∘ z), tuple_one z]
      exact pack_sort v hv .vf (z 0)
    | memRV =>
      rw [tuple_one (pack v hv ∘ z), tuple_one z]
      exact pack_sort v hv .rv (z 0)
    | memUnits =>
      by_cases hz : hasSort v .rv (z 0)
      · obtain ⟨q, hq⟩ := of_rv v (z 0) ((sortEval_iff v _ _).mpr hz)
        rw [tuple_one (pack v hv ∘ z), tuple_one z]
        change iUnits (pack v hv (z 0)) ↔ iUnits (z 0)
        rw [hq, units_inr]
        exact equiv_units v hv q
      · exact iff_of_false (fun h => hz ((pack_sort v hv _ _).mp
          (model_relation_sort hc .memUnits (pack v hv ∘ z) h 0))) (fun h => hz h.1)
    | rvLe =>
      by_cases hz : ∀ i, hasSort v .rv (z i)
      · obtain ⟨q, hq⟩ := of_rv v (z 0) ((sortEval_iff v _ _).mpr (hz 0))
        obtain ⟨r, hr⟩ := of_rv v (z 1) ((sortEval_iff v _ _).mpr (hz 1))
        rw [tuple_two (pack v hv ∘ z), tuple_two z]
        change iLe (pack v hv (z 0)) (pack v hv (z 1)) ↔ iLe (z 0) (z 1)
        rw [hq, hr, le_inr]
        exact equiv_le v hv q r
      · exact iff_of_false (fun h => hz (fun i => (pack_sort v hv _ _).mp
          (model_relation_sort hc .rvLe (pack v hv ∘ z) h i))) (fun h => hz h.1)

end SpecialTransformations.Section6.NativePresentation
