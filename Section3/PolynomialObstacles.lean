module

public import Section3.SortedBoolean
public import Section3.VFDefinableClosure

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.PolynomialObstacles
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

noncomputable def roots (E : Subfield (VFType (M := M))) (q : Polynomial E) :
    Finset (VFType (M := M)) := (q.map E.subtype).roots.toFinset

def rawRoots (E : Subfield (VFType (M := M))) (q : Polynomial E) : Set M :=
  Subtype.val '' (roots E q : Set (VFType (M := M)))

theorem rawRoots_eq_rootSet (E : Subfield (VFType (M := M))) (q : Polynomial E)
    (hq : q ≠ 0) : rawRoots E q = PolynomialRoots.rootSet E q := by
  classical
  ext z
  change (∃ x : VFType (M := M), x ∈ roots E q ∧ x.val = z) ↔ _
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x.property, ?_⟩
    change q.eval₂ E.subtype x = 0
    have hroot := (Polynomial.mem_roots (p := q.map E.subtype) (Polynomial.map_ne_zero hq)).mp
      (Multiset.mem_toFinset.mp hx)
    simpa only [Polynomial.IsRoot, Polynomial.eval_map] using hroot
  · rintro ⟨hz, hx⟩
    refine ⟨⟨z, hz⟩, ?_, rfl⟩
    apply Multiset.mem_toFinset.mpr
    apply (Polynomial.mem_roots (p := q.map E.subtype) (Polynomial.map_ne_zero hq)).mpr
    simpa only [Polynomial.IsRoot, Polynomial.eval_map] using hx

theorem rawRoots_definable (S : Set M) (E : Subfield (VFType (M := M)))
    (hE : E ≤ vfDefinableClosureField S) (q : Polynomial E) :
    DefinableAt S .vf (rawRoots E q) := by
  classical
  by_cases hq : q = 0
  · subst q
    have he : rawRoots E (0 : Polynomial E) = ∅ := by simp [rawRoots, roots]
    rw [he]
    exact DefinableAt.empty S .vf
  · rw [rawRoots_eq_rootSet E q hq]
    let D : Set M := {z | DefinableClosureAt S .vf z}
    have hnamed (x : E) : x.val.val ∈ D := hE x.property
    exact (PolynomialRoots.rootSet_definable D E hnamed q).eliminate_sorted_definable_params
      (fun z hz => ⟨.vf, hz⟩)

noncomputable def obstacles (E : Subfield (VFType (M := M))) (l : List (Polynomial E)) :
    Finset (VFType (M := M)) := insert 0 (l.toFinset.biUnion (roots E))

theorem zero_mem (E : Subfield (VFType (M := M))) (l : List (Polynomial E)) :
    0 ∈ obstacles E l := Finset.mem_insert_self _ _

theorem root_mem (E : Subfield (VFType (M := M))) (l : List (Polynomial E))
    (q : Polynomial E) (hq : q ∈ l) (c : VFType (M := M))
    (hc : c ∈ (q.map E.subtype).roots) : c ∈ obstacles E l := by
  classical
  apply Finset.mem_insert_of_mem
  exact Finset.mem_biUnion.mpr ⟨q, List.mem_toFinset.mpr hq, Multiset.mem_toFinset.mpr hc⟩

theorem raw_obstacles_eq (E : Subfield (VFType (M := M))) (l : List (Polynomial E)) :
    Subtype.val '' (obstacles E l : Set (VFType (M := M))) =
      {(0 : VFType (M := M)).val} ∪ ⋃ q ∈ l.toFinset, rawRoots E q := by
  classical
  ext z
  change (∃ x : VFType (M := M), x ∈ obstacles E l ∧ x.val = z) ↔ _
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases Finset.mem_insert.mp hx with hx | hx
    · exact Or.inl (congrArg Subtype.val hx)
    · obtain ⟨q, hq, hxq⟩ := Finset.mem_biUnion.mp hx
      exact Or.inr (Set.mem_iUnion.mpr ⟨q, Set.mem_iUnion.mpr ⟨hq, x, hxq, rfl⟩⟩)
  · rintro (hz | hz)
    · exact ⟨(0 : VFType (M := M)), zero_mem E l, hz.symm⟩
    · obtain ⟨q, hz⟩ := Set.mem_iUnion.mp hz
      obtain ⟨hq, hz⟩ := Set.mem_iUnion.mp hz
      obtain ⟨x, hxq, hxz⟩ := hz
      exact ⟨x, Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨q, hq, hxq⟩), hxz⟩

theorem obstacles_definable (S : Set M) (E : Subfield (VFType (M := M)))
    (hE : E ≤ vfDefinableClosureField S) (l : List (Polynomial E)) :
    DefinableAt S .vf (Subtype.val '' (obstacles E l : Set (VFType (M := M)))) := by
  classical
  rw [raw_obstacles_eq]
  have hz : DefinableAt S .vf {(0 : VFType (M := M)).val} :=
    definableClosureAt_function_symbol S Fn.vfZero Fin.elim0
      (fun i => i.elim0) (fun i => i.elim0)
  exact hz.union (DefinableAt.finite_iUnion l.toFinset (rawRoots E)
    (fun q _ => rawRoots_definable S E hE q))

end SpecialTransformations.Section3.PolynomialObstacles
