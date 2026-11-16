module

public import Section4.RVRestrictions

@[expose] public section

/-! Turn a finite definable cover into a same-base disjoint cover,
retaining the original piece that contains each new piece. -/

open FirstOrder FirstOrder.Language
open SpecialTransformations.DefinableGeometry

namespace SpecialTransformations.Section9

variable {L : Language} {M : Type} [L.Structure M] {P : Space L M} {S : Set M}

theorem exists_disjoint_definable_refinement {ι : Type} [Finite ι] (D : ι → DefSet P S) :
    ∃ E : ι → DefSet P S, (∀ i, (E i).carrier ⊆ (D i).carrier) ∧
      (∀ x, (∃ i, x ∈ (D i).carrier) → ∃ i, x ∈ (E i).carrier) ∧
      ∀ i j x, x ∈ (E i).carrier → x ∈ (E j).carrier → i = j := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  let e := Fintype.equivFin ι
  let earlier (i : ι) : DefSet P S :=
    ⟨⋃ j : {j : ι // e j < e i}, (D j.val).carrier, by
      change S.Definable L (P.preimage (⋃ j : {j : ι // e j < e i}, (D j.val).carrier))
      have he : P.preimage (⋃ j : {j : ι // e j < e i}, (D j.val).carrier) =
          ⋃ j : {j : ι // e j < e i}, P.preimage (D j.val).carrier := by
        ext z
        simp only [Set.mem_iUnion, Space.preimage, Set.mem_setOf_eq]
        aesop
      rw [he]
      exact Set.definable_iUnion_of_finite (fun j => (D j.val).definable)⟩
  let E i := (D i).sdiff (earlier i)
  have memEarlier (i : ι) (x : P.Carrier) : x ∈ (earlier i).carrier ↔
      ∃ j, e j < e i ∧ x ∈ (D j).carrier := by
    change x ∈ ⋃ j : {j : ι // e j < e i}, (D j.val).carrier ↔ _
    simp only [Set.mem_iUnion, Subtype.exists, exists_prop]
  refine ⟨E, fun i => Set.sdiff_subset, ?_, ?_⟩
  · rintro x ⟨j, hj⟩
    let A := Finset.univ.filter (fun r => x ∈ (D (e.symm r)).carrier)
    have hA : A.Nonempty := ⟨e j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      simpa only [e.symm_apply_apply] using hj⟩⟩
    let i := e.symm (A.min' hA)
    refine ⟨i, (Finset.mem_filter.mp (A.min'_mem hA)).2, ?_⟩
    rintro h
    obtain ⟨k, hki, hk⟩ := (memEarlier i x).mp h
    have hkA : e k ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      simpa only [e.symm_apply_apply] using hk⟩
    have hle : e i ≤ e k := by
      simpa only [i, e.apply_symm_apply] using A.min'_le (e k) hkA
    exact (not_lt_of_ge hle) hki
  · intro i j x hi hj
    apply e.injective
    rcases lt_trichotomy (e i) (e j) with h | h | h
    · exact (hj.2 ((memEarlier j x).mpr ⟨i, h, hi.1⟩)).elim
    · exact h
    · exact (hi.2 ((memEarlier i x).mpr ⟨j, h, hj.1⟩)).elim

end SpecialTransformations.Section9
