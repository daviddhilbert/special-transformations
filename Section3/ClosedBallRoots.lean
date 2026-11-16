module

public import Section3.BallGeometry
public import JohnsonGeometry

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Classical
namespace SpecialTransformations.Section3
namespace ClosedBallRoots
open ValOneEC
variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]
    [IsAlgClosed K] (v : Valuation K Γ)

/-- A finite root-free closed ball sits properly inside a root-free open ball.
The radius is the distance to the nearest member of the finite obstacle set. -/
theorem enlarge (hnt : ∃ x : K, x ≠ 0 ∧ v x < 1)
    (R : Finset K) (hR : R.Nonempty) (a b : K)
    (hmiss : ∀ c ∈ R, c ∉ closedBall v a (v b)) :
    ∃ d : K, closedBall v a (v b) ⊂ openBall v a (v d) ∧
      (∀ c ∈ R, c ∉ openBall v a (v d)) := by
  obtain ⟨c, hc, hmin⟩ := R.exists_min_image (fun c => v (c - a)) hR
  have hbc : v b < v (c - a) := lt_of_not_ge (hmiss c hc)
  refine ⟨c - a, ?_, ?_⟩
  · refine ⟨fun x hx => lt_of_le_of_lt hx hbc, ?_⟩
    obtain ⟨z, hz1, hz2⟩ := Johnson.exists_val_between' v hnt hbc
    intro hsub
    have hzmem : a + z ∈ openBall v a (v (c - a)) := by
      change v (a + z - a) < _
      simpa only [add_sub_cancel_left] using hz2
    have hzle := hsub hzmem
    change v (a + z - a) ≤ v b at hzle
    rw [add_sub_cancel_left] at hzle
    exact (not_le_of_gt hz1) hzle
  · intro e he heC
    exact (not_lt_of_ge (hmin e he)) heC

/-- Closed balls of the paper, including the whole field and singletons.
Finite radii are realized by actual field elements. -/
def IsClosedBall (D : Set K) : Prop :=
  D = Set.univ ∨ ∃ a b : K, D = closedBall v a (v b)

omit [IsAlgClosed K] in
theorem IsClosedBall.isValBall {D : Set K} (hD : IsClosedBall v D) :
    Johnson.IsValBall v D := by
  rcases hD with rfl | ⟨a, b, rfl⟩
  · exact .univ
  · exact .closed a b

omit [IsAlgClosed K] in
theorem IsClosedBall.nonempty {D : Set K} (hD : IsClosedBall v D) : D.Nonempty := by
  rcases hD with rfl | ⟨a, b, rfl⟩
  · exact Set.univ_nonempty
  · exact ⟨a, Johnson.closedBall_self_mem v a (v b)⟩

/-- Root-free local constancy forces a finite obstacle set to meet every
member of a finite disjoint family of closed balls. This is the geometric
step for the center construction; no centers or named roots are assumed. -/
theorem meets_each (hnt : ∃ x : K, x ≠ 0 ∧ v x < 1)
    {ι : Type} (s : Finset ι) (D : ι → Set K)
    (hD : ∀ i ∈ s, IsClosedBall v (D i))
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (D i) (D j))
    (R : Finset K) (hR : R.Nonempty)
    (hconstant : ∀ a b : K, (∀ c ∈ R, c ∉ openBall v a (v b)) →
      ∀ x ∈ openBall v a (v b), ∀ y ∈ openBall v a (v b),
        (x ∈ ⋃ i ∈ s, D i ↔ y ∈ ⋃ i ∈ s, D i)) :
    ∀ i ∈ s, ∃ c ∈ R, c ∈ D i := by
  intro i hi
  by_contra hnot
  have hmiss : ∀ c ∈ R, c ∉ D i := by simpa only [not_exists, not_and] using hnot
  rcases hD i hi with hwhole | ⟨a, b, hDi⟩
  · obtain ⟨c, hc⟩ := hR
    exact hmiss c hc (hwhole.symm ▸ Set.mem_univ c)
  obtain ⟨d, hproper, havoid⟩ := enlarge v hnt R hR a b (hDi ▸ hmiss)
  let C := openBall v a (v d)
  have hBC : D i ⊆ C := by simpa only [hDi] using hproper.1
  have hCB : ¬ C ⊆ D i := by simpa only [hDi] using hproper.2
  have ha : a ∈ D i := hDi.symm ▸ Johnson.closedBall_self_mem v a (v b)
  have haC : a ∈ C := hBC ha
  have hCU : C ⊆ ⋃ j ∈ s, D j := by
    intro x hx
    exact (hconstant a d havoid x hx a haC).mpr
      (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hi, ha⟩⟩)
  let t := s.filter (fun j => (D j ∩ C).Nonempty)
  have ht (j : ι) (hj : j ∈ t) : j ∈ s ∧ (D j ∩ C).Nonempty := Finset.mem_filter.mp hj
  have hnotSub (j : ι) (hj : j ∈ t) : ¬ C ⊆ D j := by
    intro hsub
    by_cases hji : j = i
    · subst j; exact hCB hsub
    · have hh := hdisj i hi j (ht j hj).1 (Ne.symm hji)
      exact Set.disjoint_left.mp hh ha (hsub haC)
  have hsub (j : ι) (hj : j ∈ t) : D j ⊆ C := by
    rcases Johnson.isValBall_subset_or_subset v
      (IsClosedBall.isValBall v (hD j (ht j hj).1)) (.openball a d) (ht j hj).2 with h | h
    · exact h
    · exact False.elim (hnotSub j hj h)
  have hcover : C = ⋃ j ∈ t, D j := by
    apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨j, hj, hxj⟩ : ∃ j ∈ s, x ∈ D j := by
        simpa only [Set.mem_iUnion, exists_prop] using hCU hx
      exact Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr
        ⟨Finset.mem_filter.mpr ⟨hj, x, hxj, hx⟩, hxj⟩⟩
    · intro x hx
      obtain ⟨j, hj, hxj⟩ : ∃ j ∈ t, x ∈ D j := by simpa only [Set.mem_iUnion, exists_prop] using hx
      exact hsub j hj hxj
  exact Johnson.ne_finite_union_of_proper_subballs v
    ((Johnson.exists_ne_zero_val_lt_one_iff v).mp hnt) (.openball a d) ⟨a, haC⟩ t D
    (fun j hj => IsClosedBall.isValBall v (hD j (ht j hj).1)) hsub
    (fun j hj he => hnotSub j hj (he ▸ Set.Subset.rfl)) hcover

end ClosedBallRoots
end SpecialTransformations.Section3
