import Section4.DefinableGeometry
import Section3.SortedBoolean
import Section3.Coordinates
import Section3.GammaDefinability
import Section3.SortedFunctionClosure
import Mathlib.Data.Finite.Prod

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

/-!
# The VF, RV and Gamma spaces in the released language

All presentations use the canonical normalization of the released LRV
structure. The Section 3 bridge identifies their real-sort definable sets
with sorted definability over the same arbitrary base. Gamma is the actual
value quotient; its presentation uses all nonzero RV representatives.
-/

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace SpecialTransformations.Section4

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

abbrev Space := @DefinableGeometry.Space LRV M (CanonicalStructure.normalize (M := M))

abbrev RawDefinable (S : Set M) {ι : Type} (A : Set (ι → M)) :=
  @Set.Definable M S LRV (CanonicalStructure.normalize (M := M)) ι A

theorem sort_coordinate_definable (S : Set M) {ι : Type} (σ : SortTag) (i : ι) :
    RawDefinable S {z : ι → M | sortEval σ (z i)} := by
  have h := (definableAt_iff_normalized_raw S σ {x | sortEval σ x}).mp
    (definableAt_sort S σ)
  exact @Set.Definable.preimage_comp M S LRV (CanonicalStructure.normalize (M := M))
    (Fin 1) ι (fun _ => i) _ h.1

theorem coordinate_equality_definable (S : Set M) {ι : Type} (i j : ι) :
    RawDefinable S {z : ι → M | z i = z j} := by
  letI := CanonicalStructure.normalize (M := M)
  exact RawClosure.definable_equal_coordinates S i j

theorem tuple_domain_definable (S : Set M) {ι : Type} [Finite ι] (σ : ι → SortTag) :
    RawDefinable S {z : ι → M | ∀ i, sortEval (σ i) (z i)} := by
  have h := fun i => sort_coordinate_definable (M := M) S (σ i) i
  letI := CanonicalStructure.normalize (M := M)
  convert Set.definable_iInter_of_finite h using 1
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_iInter]

/-- The full finite product of any specified real sorts. -/
def realSpace {ι : Type} [Finite ι] (σ : ι → SortTag) : Space (M := M) := by
  let X := Coordinates.Tuple (M := M) σ
  let D : Set (ι → M) := {z | ∀ i, sortEval (σ i) (z i)}
  have hD := tuple_domain_definable (M := M) ∅ σ
  have hx := @Set.Definable.preimage_comp M ∅ LRV (CanonicalStructure.normalize (M := M))
    ι (ι ⊕ ι) Sum.inl D hD
  have hy := @Set.Definable.preimage_comp M ∅ LRV (CanonicalStructure.normalize (M := M))
    ι (ι ⊕ ι) Sum.inr D hD
  have he (i : ι) := coordinate_equality_definable (M := M) ∅
    (Sum.inl i : ι ⊕ ι) (Sum.inr i)
  letI := CanonicalStructure.normalize (M := M)
  exact {
  Carrier := X
  Index := ι
  finiteIndex := inferInstance
  domain := D
  domain_definable := hD
  decode z i := ⟨z.val i, z.property i⟩
  onto x := ⟨⟨fun i => (x i).val, fun i => (x i).property⟩, rfl⟩
  diagonal_definable := by
    have hall := Set.definable_iInter_of_finite he
    convert hx.inter (hy.inter hall) using 1
    ext z
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage]
    constructor
    · rintro ⟨hx, hy, he⟩
      exact ⟨hx, hy, fun i => congrArg Subtype.val (congrFun he i)⟩
    · rintro ⟨hx, hy, he⟩
      exact ⟨hx, hy, funext (fun i => Subtype.ext (he i))⟩ }

abbrev vfSpace (n : ℕ) : Space (M := M) := realSpace (fun _ : Fin n => .vf)

abbrev rvSpace (n : ℕ) : Space (M := M) := realSpace (fun _ : Fin n => .rv)

abbrev mixedSpace (n m : ℕ) : Space (M := M) :=
  realSpace (Coordinates.mixedSort (n := n) (m := m))

theorem realSpace_preimage {n : ℕ} (σ : Fin n → SortTag)
    (A : Set (Coordinates.Tuple (M := M) σ)) :
    @DefinableGeometry.Space.preimage LRV M (CanonicalStructure.normalize (M := M))
      (realSpace σ) A = (fun x i => (x i).val) '' A := by
  ext z
  constructor
  · rintro ⟨hz, ha⟩
    exact ⟨fun i => ⟨z i, hz i⟩, ha, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨fun i => (x i).property, hx⟩

/-- The presentation agrees with the existing sorted definition, including
the original parameter base. -/
theorem realSpace_definable_iff (S : Set M) {n : ℕ} (σ : Fin n → SortTag)
    (A : Set (Coordinates.Tuple (M := M) σ)) :
    @DefinableGeometry.Space.Definable LRV M (CanonicalStructure.normalize (M := M))
      (realSpace σ) S A ↔ DefinableOver S σ ((fun x i => (x i).val) '' A) := by
  have hsort : ∀ z ∈ ((fun x i => (x i).val) '' A), ∀ i, sortEval (σ i) (z i) := by
    rintro z ⟨x, hx, rfl⟩ i
    exact (x i).property
  rw [definableOver_iff_normalized_raw]
  change RawDefinable S
    (@DefinableGeometry.Space.preimage LRV M (CanonicalStructure.normalize (M := M))
      (realSpace σ) A) ↔ _
  rw [realSpace_preimage]
  exact ⟨fun h => ⟨h, hsort⟩, And.left⟩

private theorem nonzero_rv_domain_definable (S : Set M) :
    RawDefinable S {z : Fin 1 → M | iRV (z 0) ∧ z 0 ≠ iRVZero} := by
  have hr := sort_coordinate_definable (M := M) S .rv (0 : Fin 1)
  have hz : DefinableClosureAt S .rv (iRVZero : M) :=
    definableClosureAt_function_symbol S Fn.rvZero Fin.elim0
      (fun i => i.elim0) (fun i => i.elim0)
  have hzraw := (definableAt_iff_normalized_raw S .rv {iRVZero}).mp hz
  letI := CanonicalStructure.normalize (M := M)
  exact hr.inter hzraw.1.compl

private theorem rv_comparison_definable (S : Set M) :
    RawDefinable S {z : Fin 2 → M | iRV (z 0) ∧ iRV (z 1) ∧ iLe (z 0) (z 1)} := by
  have h0 := sort_coordinate_definable (M := M) S .rv (0 : Fin 2)
  have h1 := sort_coordinate_definable (M := M) S .rv (1 : Fin 2)
  have hn : RawDefinable S {z : Fin 2 → M |
      @Structure.RelMap LRV M (CanonicalStructure.normalize (M := M)) 2 Rel.rvLe z} := by
    letI := CanonicalStructure.normalize (M := M)
    have hf : (∅ : Set M).Definable LRV
        {z : Fin 2 → M | Structure.RelMap (L := LRV) Rel.rvLe z} :=
      Set.empty_definable_iff.mpr ⟨.rel Rel.rvLe (fun i => .var (.inl i)), rfl⟩
    exact hf.mono (Set.empty_subset S)
  let N := CanonicalStructure.normalize (M := M)
  have h : @Set.Definable M S LRV N (Fin 2)
      ({z | iRV (z 0)} ∩ ({z | iRV (z 1)} ∩
        {z | @Structure.RelMap LRV M N 2 Rel.rvLe z})) := by
    letI := N
    exact h0.inter (h1.inter hn)
  convert h using 1
  ext z
  have he : z = ![z 0, z 1] := by funext i; fin_cases i <;> rfl
  have hnle : @Structure.RelMap LRV M N 2 Rel.rvLe z ↔ @iLe M N (z 0) (z 1) := by
    exact Iff.of_eq (congrArg (@Structure.RelMap LRV M N 2 Rel.rvLe) he)
  constructor
  · rintro ⟨h0, h1, hle⟩
    exact ⟨h0, h1, hnle.mpr ((@rv_le_normalize M sM _ _ h0 h1).mpr hle)⟩
  · rintro ⟨h0, h1, hle⟩
    exact ⟨h0, h1, (@rv_le_normalize M sM _ _ h0 h1).mp (hnle.mp hle)⟩

/-- The genuine imaginary Gamma carrier, presented by all nonzero RV codes. -/
def gammaSpace : Space (M := M) := by
  let X := Values.Gamma (M := M)
  let D : Set (Fin 1 → M) := {z | iRV (z 0) ∧ z 0 ≠ iRVZero}
  let dec (z : D) : X := Values.gammaOf ⟨z.val 0, z.property.1⟩ z.property.2
  have hEq (x y : D) : dec x = dec y ↔
      iLe (x.val 0) (y.val 0) ∧ iLe (y.val 0) (x.val 0) := by
    constructor
    · intro h
      exact (Values.vrv_eq_iff _ _).mp (congrArg Subtype.val h)
    · intro h
      exact Subtype.ext ((Values.vrv_eq_iff _ _).mpr h)
  have hon : Function.Surjective dec := by
    intro γ
    obtain ⟨t, ht, htγ⟩ := Values.gamma_has_nonzero_representative γ
    exact ⟨⟨![t.val], t.property, ht⟩, Subtype.ext htγ⟩
  have hD := nonzero_rv_domain_definable (M := M) ∅
  let ι := Fin 1 ⊕ Fin 1
  have hx := @Set.Definable.preimage_comp M ∅ LRV (CanonicalStructure.normalize (M := M))
    (Fin 1) ι Sum.inl D hD
  have hy := @Set.Definable.preimage_comp M ∅ LRV (CanonicalStructure.normalize (M := M))
    (Fin 1) ι Sum.inr D hD
  have hl := @Set.Definable.preimage_comp M ∅ LRV (CanonicalStructure.normalize (M := M))
    (Fin 2) ι (![Sum.inl 0, Sum.inr 0]) _ (rv_comparison_definable (M := M) ∅)
  have hr := @Set.Definable.preimage_comp M ∅ LRV (CanonicalStructure.normalize (M := M))
    (Fin 2) ι (![Sum.inr 0, Sum.inl 0]) _ (rv_comparison_definable (M := M) ∅)
  letI := CanonicalStructure.normalize (M := M)
  exact {
  Carrier := X
  Index := Fin 1
  finiteIndex := inferInstance
  domain := D
  domain_definable := hD
  decode := dec
  onto := hon
  diagonal_definable := by
    convert hx.inter (hy.inter (hl.inter hr)) using 1
    ext z
    constructor
    · rintro ⟨hx, hy, he⟩
      have hv := (hEq ⟨z ∘ Sum.inl, hx⟩ ⟨z ∘ Sum.inr, hy⟩).mp he
      exact ⟨hx, hy, ⟨hx.1, hy.1, hv.1⟩, ⟨hy.1, hx.1, hv.2⟩⟩
    · rintro ⟨hx, hy, ⟨_, _, hl⟩, ⟨_, _, hr⟩⟩
      exact ⟨hx, hy, (hEq _ _).mpr ⟨hl, hr⟩⟩ }

end SpecialTransformations.Section4
