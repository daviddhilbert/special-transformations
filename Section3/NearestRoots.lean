module

public import Section3.BallGeometry

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Classical
namespace SpecialTransformations.Section3.Balls
variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ)

/-- Roots nearest to some member of A; only A, R and the valuation occur. -/
noncomputable def nearestRoots (R : Finset K) (A : Set K) : Finset K :=
  R.filter (fun r => ∃ a ∈ A, ∀ s ∈ R, v (r - a) ≤ v (s - a))

theorem nearestRoots_nonempty (R : Finset K) (hR : R.Nonempty)
    (A : Set K) (hA : A.Nonempty) : (nearestRoots v R A).Nonempty := by
  obtain ⟨a, ha⟩ := hA
  obtain ⟨r, hr, hmin⟩ := R.exists_min_image (fun r => v (r - a)) hR
  exact ⟨r, Finset.mem_filter.mpr ⟨hr, a, ha, hmin⟩⟩

theorem nearestRoots_mem_closedDisc (R : Finset K) (A : Set K) (a : K) (ρ : Radius Γ)
    (hA : A ⊆ closedDisc v a ρ) (hR : ∃ r ∈ R, r ∈ closedDisc v a ρ) :
    ∀ r ∈ nearestRoots v R A, r ∈ closedDisc v a ρ := by
  intro r hr
  cases ρ with
  | none => trivial
  | some γ =>
    obtain ⟨hrR, x, hxA, hnear⟩ := Finset.mem_filter.mp hr
    obtain ⟨s, hsR, hsB⟩ := hR
    have hxB : v (x - a) ≤ OrderDual.ofDual γ := hA hxA
    have hsB' : v (s - a) ≤ OrderDual.ofDual γ := hsB
    have hsx : v (s - x) ≤ OrderDual.ofDual γ := by
      have he : s - x = (s - a) - (x - a) := by ring
      rw [he]
      exact v.map_sub_le hsB' hxB
    have hrx := (hnear s hsR).trans hsx
    change v (r - a) ≤ OrderDual.ofDual γ
    have he : r - a = (r - x) + (x - a) := by ring
    rw [he]
    exact v.map_add_le hrx hxB

theorem nearestRoots_mem_openDisc (R : Finset K) (A : Set K) (a : K) (ρ : OpenRadius Γ)
    (hA : A ⊆ openDisc v a ρ) (hR : ∃ r ∈ R, r ∈ openDisc v a ρ) :
    ∀ r ∈ nearestRoots v R A, r ∈ openDisc v a ρ := by
  intro r hr
  obtain ⟨hrR, x, hxA, hnear⟩ := Finset.mem_filter.mp hr
  obtain ⟨s, hsR, hsB⟩ := hR
  have hxB : v (x - a) < (OrderDual.ofDual ρ : Γˣ).val := hA hxA
  have hsB' : v (s - a) < (OrderDual.ofDual ρ : Γˣ).val := hsB
  have hsx : v (s - x) < (OrderDual.ofDual ρ : Γˣ).val := by
    have he : s - x = (s - a) - (x - a) := by ring
    rw [he]
    exact v.map_sub_lt hsB' hxB
  have hrx := lt_of_le_of_lt (hnear s hsR) hsx
  change v (r - a) < (OrderDual.ofDual ρ : Γˣ).val
  have he : r - a = (r - x) + (x - a) := by ring
  rw [he]
  exact v.map_add_lt hrx hxB

end SpecialTransformations.Section3.Balls
