import Section3.Counting
import Section3.ParameterBridge
import Section3.SortedBoolean

/-!
# Real tuple quantifiers used for local lifts

The set of RV pairs on which an equation system has a bijective graph
is first-order definable by quantifying over both field fibres. These
helpers express the exact tuple quantifiers, including uniqueness, in
the existing definable-set API.
-/

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace SpecialTransformations.Section7

variable {M : Type} [LRV.Structure M] {S : Set M}

theorem definable_existsUnique_tuple {ι ι' : Type} [Finite ι']
    (P : (ι → M) → (ι' → M) → Prop)
    (hP : S.Definable LRV {z : ι ⊕ ι' → M | P (z ∘ Sum.inl) (z ∘ Sum.inr)}) :
    S.Definable LRV {z : ι → M | ∃! y, P z y} := by
  let π : ι ⊕ ι' → (ι ⊕ ι') ⊕ ι' := Sum.elim (Sum.inl ∘ Sum.inl) Sum.inr
  have heq : S.Definable LRV {z : (ι ⊕ ι') ⊕ ι' → M |
      (fun i => z (.inr i)) = (fun i => z (.inl (.inr i)))} := by
    have hd (i : ι') := RawClosure.definable_equal_coordinates S
      (.inr i : (ι ⊕ ι') ⊕ ι') (.inl (.inr i))
    convert Set.definable_iInter_of_finite hd using 1
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, funext_iff]
  have hunique : S.Definable LRV {z : ι ⊕ ι' → M |
      ∀ y, P (z ∘ Sum.inl) y → y = z ∘ Sum.inr} := by
    classical
    have h := ((hP.preimage_comp π).compl.union heq).forall_of_finite
    convert h using 1
    ext z
    simp only [π, Set.mem_ofPred_eq, Set.mem_union, Set.mem_compl_iff, Set.mem_preimage, Function.comp_def,
      Sum.elim_inl, Sum.elim_inr]
    constructor
    · intro h y
      by_cases hy : P (z ∘ Sum.inl) y
      · exact Or.inr (h y hy)
      · exact Or.inl hy
    · intro h y hy
      exact (h y).resolve_left (fun hn => hn hy)
  have h := (hP.inter hunique).exists_of_finite
  convert h using 1
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Sum.elim_comp_inl, Sum.elim_comp_inr,
    ExistsUnique]

theorem rawTupleFibreGuard_definable (S : Set M) {ι : Type} {n : ℕ}
    (f g : Fin n → ι) :
    S.Definable LRV {z : ι → M | ∀ i, iVF (z (f i)) ∧ iRv (z (f i)) = z (g i)} := by
  have h (i : Fin n) : S.Definable LRV
      {z : ι → M | iVF (z (f i)) ∧ iRv (z (f i)) = z (g i)} := by
    have hv := (definableAt_sort S .vf).raw_definable.preimage_comp (fun _ : Fin 1 => f i)
    have hr : S.DefinableFun LRV (fun z : ι → M => iRv (z (f i))) :=
      (Set.DefinableFun.of_empty
        (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.rvMap)).comp
        (show S.DefinableMap LRV (fun z : ι → M => ![z (f i)]) from
          by intro j; fin_cases j; exact Set.DefinableFun.proj LRV)
    exact hv.inter (hr.ofPred_eq (Set.DefinableFun.proj LRV))
  convert Set.definable_iInter_of_finite h using 1
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_iInter]

theorem definable_rvTuple (S : Set M) {ι : Type} :
    S.DefinableMap LRV (fun z : ι → M => iRv ∘ z) := by
  intro i
  exact (Set.DefinableFun.of_empty
    (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.rvMap)).comp
    (show S.DefinableMap LRV (fun z : ι → M => ![z i]) from
      by intro j; fin_cases j; exact Set.DefinableFun.proj LRV)

end SpecialTransformations.Section7
