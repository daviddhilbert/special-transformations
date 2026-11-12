module

public import Section4.ResidueScopedContext
public import ResidueReduct
public import Section3.SortedTuples

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

noncomputable section

namespace SpecialTransformations.Section4.ResiduePurity

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

def residueRaw (a : ModelResidue M) : M := (residueRV a).val

theorem residueRaw_injective : Function.Injective (residueRaw (M := M)) :=
  Subtype.val_injective.comp residueRV_injective

def residueFieldValues {n : ℕ} (a : Fin n → ModelResidue M) : Fin n → M := residueRaw ∘ a

def residueFieldImage {n : ℕ} (D : Set (Fin n → ModelResidue M)) : Set (Fin n → M) :=
  {z | ∃ a ∈ D, residueFieldValues a = z}

def residueGuardFormula (S : Set M) (n : ℕ) : LRV.Formula (S ⊕ Fin n) :=
  Formula.relabel (Sum.elim (fun e : Empty => e.elim) Sum.inr) (kHyps (k := n)).toFormula

theorem residueGuardFormula_realize (S : Set M) (n : ℕ) (z : Fin n → M) :
    (residueGuardFormula S n).Realize (Sum.elim Subtype.val z) ↔
      ∀ i, iUnits (z i) ∨ z i = iRVZero := by
  rw [residueGuardFormula, Formula.realize_relabel, BoundedFormula.realize_toFormula]
  change (kHyps (k := n)).Realize _ z ↔ _
  exact ValuedModelMap.kHyps_realize _ z

/-- Pure field definability translates back to a complete guarded LRV
image using the published residue interpretation, with actual parameter
names and all residue elements, including zero. -/
theorem residueFieldImage_raw_definable {n : ℕ} (E : Subfield (ModelResidue M))
    (S : Set M) (hparam : ∀ c : E, residueRaw c.val ∈ S)
    (D : Set (Fin n → ModelResidue M)) (hD : Relative.Def E D) :
    S.Definable LRV (residueFieldImage D) := by
  obtain ⟨φ, hφ⟩ := Set.definable_iff_exists_formula_sum.mp hD
  let param (c : E) : S := ⟨residueRaw c.val, hparam c⟩
  let ψ : LRV.Formula (S ⊕ Fin n) :=
    Formula.relabel (Sum.map param id) (ResidueReduct.translateFormula φ)
  have hψ (a : Fin n → ModelResidue M) :
      ψ.Realize (Sum.elim Subtype.val (residueFieldValues a)) ↔
        φ.Realize (Sum.elim (fun c : E => c.val) a) := by
    dsimp only [ψ]
    rw [Formula.realize_relabel]
    have he : Sum.elim (Subtype.val : S → M) (residueFieldValues a) ∘ Sum.map param id =
        fun j => CanonicalResidue.encodeResidue Values.presentationValuation
          Values.presentation_compatible (Sum.elim (fun c : E => c.val) a j) := by
      funext j
      cases j <;> rfl
    exact he.symm ▸ (ResidueReduct.realize_translate Values.presentationValuation
      Values.presentation_compatible φ (Sum.elim (fun c : E => c.val) a))
  apply Set.definable_iff_exists_formula_sum.mpr
  refine ⟨residueGuardFormula S n ⊓ ψ, ?_⟩
  ext z
  change (∃ a ∈ D, residueFieldValues a = z) ↔
    (residueGuardFormula S n ⊓ ψ).Realize (Sum.elim Subtype.val z)
  rw [Formula.realize_inf]
  rw [residueGuardFormula_realize]
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨fun i => CanonicalResidue.encodeResidue_inK _ _ (a i), ?_⟩
    apply (hψ a).mpr
    exact (Set.ext_iff.mp hφ a).mp ha
  · rintro ⟨hz, hzψ⟩
    have ha (i : Fin n) : ∃ a : ModelResidue M, residueRaw a = z i :=
      CanonicalResidue.encodeResidue_surjective_inK _ _ (z i) (hz i)
    choose a ha using ha
    have he : residueFieldValues a = z := funext ha
    have hψa : ψ.Realize (Sum.elim Subtype.val (residueFieldValues a)) := he.symm ▸ hzψ
    exact ⟨a, (Set.ext_iff.mp hφ a).mpr ((hψ a).mp hψa), he⟩

theorem residueFieldImage_definable (hcan : CanonicalStructure.IsCanonical (M := M))
    {n : ℕ} (E : Subfield (ModelResidue M)) (S : Set M)
    (hparam : ∀ c : E, residueRaw c.val ∈ S)
    (D : Set (Fin n → ModelResidue M)) (hD : Relative.Def E D) :
    DefinableOver S (fun _ => .rv) (residueFieldImage D) := by
  apply raw_definableOver_sorted hcan S (fun _ => .rv) _
    (residueFieldImage_raw_definable E S hparam D hD)
  rintro z ⟨a, ha, rfl⟩ i
  exact (residueRV (a i)).property

theorem residueFieldImage_definable_of_definable_names
    (hcan : CanonicalStructure.IsCanonical (M := M)) {n : ℕ}
    (E : Subfield (ModelResidue M)) (S : Set M)
    (hparam : ∀ c : E, DefinableClosureAt S .rv (residueRaw c.val))
    (D : Set (Fin n → ModelResidue M)) (hD : Relative.Def E D) :
    DefinableOver S (fun _ => .rv) (residueFieldImage D) := by
  let T := S ∪ residueFieldNames E
  have h := residueFieldImage_definable hcan E T
    (fun c => Or.inr ⟨c, rfl⟩) D hD
  apply h.eliminate_sorted_definable_params
  rintro b (hb | ⟨c, rfl⟩)
  · rcases TypedModelMap.sort_cover b with hVF | hRV
    · exact ⟨.vf, definableClosureAt_of_mem hb hVF⟩
    · exact ⟨.rv, definableClosureAt_of_mem hb hRV⟩
  · exact ⟨.rv, hparam c⟩

end SpecialTransformations.Section4.ResiduePurity

end
