import Section4.RVRank
import Section3.TupleRelations

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M]

theorem definable_mem_automorphism_iff (e : M ≃[LRV] M) {S : Set M}
    (hfix : ∀ s ∈ S, e s = s) {ι : Type} {D : Set (ι → M)}
    (hD : S.Definable LRV D) (a : ι → M) : (e ∘ a ∈ D ↔ a ∈ D) := by
  obtain ⟨φ, hφ⟩ := Set.definable_iff_exists_formula_sum.mp hD
  have hp : e ∘ Sum.elim (Subtype.val : S → M) a =
      Sum.elim (Subtype.val : S → M) (e ∘ a) := by
    funext i
    cases i with
    | inl s => exact hfix s.val s.property
    | inr i => rfl
  have h := StrongHomClass.realize_formula e φ (v := Sum.elim (Subtype.val : S → M) a)
  rw [hp] at h
  simpa only [hφ, Set.mem_setOf_eq] using h

theorem automorphism_symm_fixes (e : M ≃[LRV] M) {S : Set M}
    (hfix : ∀ s ∈ S, e s = s) : ∀ s ∈ S, e.symm s = s := by
  intro s hs
  have h := congrArg e.symm (hfix s hs)
  simpa only [FirstOrder.Language.Equiv.symm_apply_apply] using h.symm

/-- Finite parameter tuples are transported using an original-base good
relation. Definability and finiteness of the entire fibre are retained. -/
theorem raw_algebraic_tuple_automorphism (e : M ≃[LRV] M) {S : Set M}
    (hfix : ∀ s ∈ S, e s = s) {n : ℕ} (a : Fin n → M) (b : M)
    (hb : RawClosure.AlgebraicOver (S ∪ Set.range a) b) :
    RawClosure.AlgebraicOver (S ∪ Set.range (e ∘ a)) (e b) := by
  obtain ⟨R, hR⟩ := RawClosure.Tuple.good_relation_of_algebraic S a b hb
  let z : Fin n ⊕ Fin 1 → M := Sum.elim a ![b]
  have hz : (z ∘ Sum.inl, z (.inr 0)) ∈ R.val := hR
  have he := (definable_mem_automorphism_iff e hfix R.property.1 z).mpr hz
  change (((e ∘ z) ∘ Sum.inl), (e ∘ z) (.inr 0)) ∈ R.val at he
  have hemem : (e ∘ a, e b) ∈ R.val := by
    simpa only [z, Function.comp_def, Sum.elim_inl, Sum.elim_inr,
      Matrix.cons_val_zero] using he
  let T := S ∪ Set.range (e ∘ a)
  let F (x : Fin 1 → M) : Fin n ⊕ Fin 1 → M := Sum.elim (e ∘ a) x
  have hF : T.DefinableMap LRV F := by
    intro i
    cases i with
    | inl i => exact LRV.definableFun_const (Fin 1) (Or.inr (Set.mem_range_self i))
    | inr i => exact Set.DefinableFun.proj LRV
  have hslice : T.Definable₁ LRV {x | (e ∘ a, x) ∈ R.val} := by
    have h := (R.property.1.mono (Set.subset_union_left : S ⊆ T)).preimage_map hF
    exact h
  exact ⟨_, hslice, R.property.2 (e ∘ a), hemem⟩

theorem raw_algebraic_tuple_automorphism_iff (e : M ≃[LRV] M) {S : Set M}
    (hfix : ∀ s ∈ S, e s = s) {n : ℕ} (a : Fin n → M) (b : M) :
    RawClosure.AlgebraicOver (S ∪ Set.range (e ∘ a)) (e b) ↔
      RawClosure.AlgebraicOver (S ∪ Set.range a) b := by
  refine ⟨?_, raw_algebraic_tuple_automorphism e hfix a b⟩
  intro h
  have h' := raw_algebraic_tuple_automorphism e.symm (automorphism_symm_fixes e hfix)
    (e ∘ a) (e b) h
  simpa [Function.comp_def] using h'

variable [hM : M ⊨ Axioms.ACVF]

def rvAutomorphismMap (e : M ≃[LRV] M) (t : CanonicalRV.RVSort M) :
    CanonicalRV.RVSort M := by
  refine ⟨e t.val, ?_⟩
  have h := e.map_rel Rel.memRV ![t.val]
  have he : e ∘ ![t.val] = ![e t.val] := by funext i; fin_cases i; rfl
  rw [he] at h
  exact h.mpr t.property

@[simp] theorem rvAutomorphismMap_val (e : M ≃[LRV] M) (t : CanonicalRV.RVSort M) :
    (rvAutomorphismMap e t).val = e t.val := rfl

def rvAutomorphism (e : M ≃[LRV] M) : CanonicalRV.RVSort M ≃ CanonicalRV.RVSort M where
  toFun := rvAutomorphismMap e
  invFun := rvAutomorphismMap e.symm
  left_inv t := Subtype.ext (e.symm_apply_apply t.val)
  right_inv t := Subtype.ext (e.apply_symm_apply t.val)

theorem rvAutomorphism_algebraic_tuple_iff
    (hcan : CanonicalStructure.IsCanonical (M := M)) (e : M ≃[LRV] M) {S : Set M}
    (hfix : ∀ s ∈ S, e s = s) {n : ℕ} (t : Fin n → CanonicalRV.RVSort M)
    (u : CanonicalRV.RVSort M) :
    AlgebraicAt (S ∪ Set.range (rvValues (rvAutomorphism e ∘ t))) .rv
      (rvAutomorphism e u).val ↔
      AlgebraicAt (S ∪ Set.range (rvValues t)) .rv u.val := by
  rw [algebraicAt_iff_raw hcan, algebraicAt_iff_raw hcan]
  have he : rvValues (rvAutomorphism e ∘ t) = e ∘ rvValues t := rfl
  rw [he]
  exact and_congr (raw_algebraic_tuple_automorphism_iff e hfix (rvValues t) u.val)
    (iff_of_true (rvAutomorphism e u).property u.property)

end SpecialTransformations.Section4

end
