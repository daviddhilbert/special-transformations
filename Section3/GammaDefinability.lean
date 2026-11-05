import Section3.ValueQuotient
import Section3.SortedBoolean
import Section3.DefinableConstants
import Section3.EncodedBallGeometry
import Section3.TupleRelations
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3.Values
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def gammaOf (t : CanonicalRV.RVSort M) (ht : t.val ≠ iRVZero) : Gamma (M := M) :=
  ⟨vrv t, fun h => ht ((vrv_eq_infinity_iff t).mp h)⟩

def gammaPullback (V : Set (Gamma (M := M))) : Set M :=
  {t | ∃ hRV : iRV t, ∃ h0 : t ≠ iRVZero, gammaOf ⟨t, hRV⟩ h0 ∈ V}

/-- Definability on the actual Gamma imaginary is definability of its full
RV preimage, over the same real base. No representative is named. This
interface alone makes no assertion about Gamma-generated substructures. -/
def GammaDefinable (S : Set M) (V : Set (Gamma (M := M))) : Prop :=
  DefinableAt S .rv (gammaPullback V)

end SpecialTransformations.Section3.Values

namespace SpecialTransformations.Section3.RawValueFibres
open RawClosure.Tuple
variable {M : Type} [sM : LRV.Structure M]

def relation (A : Set M) : Set ((Fin 1 → M) × M) :=
  {p | iRV (p.1 0) ∧ p.1 0 ≠ iRVZero ∧ p.2 ∈ A ∧ iLe (p.1 0) p.2 ∧ iLe p.2 (p.1 0)}

private theorem rel_definable (S : Set M) : S.Definable LRV
    {x : Fin 2 → M | Structure.RelMap (L := LRV) Rel.rvLe x} := by
  have h : (∅ : Set M).Definable LRV {x : Fin 2 → M | Structure.RelMap (L := LRV) Rel.rvLe x} :=
    Set.empty_definable_iff.mpr ⟨.rel Rel.rvLe (fun i => .var (.inl i)), rfl⟩
  exact h.mono (Set.empty_subset S)

/-- A complete real graph for the value fibre in A, including its sort and
non-infinity guards, is definable over exactly A's original parameter base. -/
theorem relation_definable (S A : Set M) (hA : S.Definable₁ LRV A) :
    RelationDefinable S (relation A) := by
  let ι := Fin 1 ⊕ Fin 1
  let idx : Fin 2 → ι := ![.inl 0, .inr 0]
  have hle : S.Definable LRV {z : ι → M | iLe (z (.inl 0)) (z (.inr 0))} := by
    have h := (rel_definable S).preimage_comp idx
    convert h using 1
    ext z
    have he : z ∘ idx = ![z (.inl 0), z (.inr 0)] := by funext i; fin_cases i <;> rfl
    change Structure.RelMap (L := LRV) Rel.rvLe ![z (.inl 0), z (.inr 0)] ↔
      Structure.RelMap (L := LRV) Rel.rvLe (z ∘ idx)
    rw [he]
  have hge := hle.preimage_comp (Sum.swap : ι → ι)
  have hr := (definableAt_sort S .rv).raw_definable.preimage_comp (Sum.inl : Fin 1 → ι)
  have ha := hA.preimage_comp (Sum.inr : Fin 1 → ι)
  have hzero : S.DefinableFun LRV (fun _ : ι → M => iRVZero) :=
    DefinableConstants.constant (DefinableConstants.function_symbol (L := LRV) Fn.rvZero Fin.elim0
      (fun i => i.elim0))
  have hn := ((Set.DefinableFun.proj (L := LRV) (A := S) (i := Sum.inl 0)).ofPred_eq hzero).compl
  change S.Definable LRV _
  convert (((hr.inter hn).inter ha).inter hle).inter hge using 1
  ext z
  simp only [relation, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_inter_iff,
    Set.mem_compl_iff, Function.comp_def, Sum.swap_inl, Sum.swap_inr]
  tauto

variable [hM : M ⊨ Axioms.ACVF]

/-- Normalization preserves this actual guarded fibre relation. -/
theorem relation_normalize (A : Set M) (hA : A ⊆ {x | iRV x}) :
    @relation M (CanonicalStructure.normalize (M := M)) A = relation A := by
  have hz : @iRVZero M (CanonicalStructure.normalize (M := M)) = iRVZero :=
    CanonicalStructure.sortZero_normalize .rv
  ext p
  by_cases ht : iRV (p.1 0)
  · by_cases ha : p.2 ∈ A
    · change (iRV (p.1 0) ∧ _ ∧ _ ∧ _ ∧ _) ↔ (iRV (p.1 0) ∧ _ ∧ _ ∧ _ ∧ _)
      simp only [ht, ha, true_and, hz]
      exact and_congr Iff.rfl (and_congr
        (rv_le_normalize (p.1 0) p.2 ht (hA ha)) (rv_le_normalize p.2 (p.1 0) (hA ha) ht))
    · change (iRV (p.1 0) ∧ _ ∧ _ ∧ _ ∧ _) ↔ (iRV (p.1 0) ∧ _ ∧ _ ∧ _ ∧ _)
      simp only [ha, and_false, false_and]
  · change (iRV (p.1 0) ∧ _ ∧ _ ∧ _ ∧ _) ↔ (iRV (p.1 0) ∧ _ ∧ _ ∧ _ ∧ _)
    simp only [ht, false_and]

end SpecialTransformations.Section3.RawValueFibres
