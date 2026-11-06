import Section3.BallTranslation

/- Component: OpenBallHullGeometry -/
set_option backward.isDefEq.respectTransparency false
open Classical
namespace SpecialTransformations.Section3.Balls
variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]

/-- An actual VF radius supplies a boundary point, so comparing strict
discs requires neither density nor completeness of the value group. -/
theorem strictDisc_radius_le_of_subset (v : Valuation K Γ) (a b r s : K) (hr : r ≠ 0)
    (hsub : {x | v (x-a) < v r} ⊆ {x | v (x-b) < v s}) : v r ≤ v s := by
  by_contra hle
  have hsr : v s < v r := lt_of_not_ge hle
  have ha : v (a-a) < v r := by
    simpa only [sub_self,map_zero] using (zero_lt_iff.mpr ((v.ne_zero_iff).mpr hr))
  have hab : v (a-b) < v s := hsub ha
  have hba : v (b-a) < v s := by rwa [v.map_sub_swap]
  have hx : v ((b+s)-a) < v r := by
    have he : (b+s)-a = (b-a)+s := by ring
    rw [he]
    exact v.map_add_lt (hba.trans hsr) hsr
  have hbad : v ((b+s)-b) < v s := hsub hx
  have he : (b+s)-b = s := by ring
  rw [he] at hbad
  exact (lt_irrefl (v s)) hbad

theorem strictDisc_radius_eq_of_eq (v : Valuation K Γ) (a b r s : K)
    (hr : r ≠ 0) (hs : s ≠ 0)
    (he : {x | v (x-a) < v r} = {x | v (x-b) < v s}) : v r = v s :=
  le_antisymm (strictDisc_radius_le_of_subset v a b r s hr he.subset)
    (strictDisc_radius_le_of_subset v b a s r hs he.symm.subset)

/-- The same-radius closed hull is intrinsic to a proper open disc.
This is an order-theoretic ball hull, not topological closure. -/
theorem closedHull_eq_of_strictDisc_eq (v : Valuation K Γ) (a b r s : K)
    (hr : r ≠ 0) (hs : s ≠ 0)
    (he : {x | v (x-a) < v r} = {x | v (x-b) < v s}) :
    {x | v (x-a) ≤ v r} = {x | v (x-b) ≤ v s} := by
  have hrs := strictDisc_radius_eq_of_eq v a b r s hr hs he
  have ha : v (a-a) < v r := by
    simpa only [sub_self,map_zero] using (zero_lt_iff.mpr ((v.ne_zero_iff).mpr hr))
  have hab : v (a-b) < v s := he.subset ha
  have hba : v (b-a) < v r := by rw [v.map_sub_swap,hrs]; exact hab
  ext x
  constructor
  · intro hx
    change v (x-a) ≤ v r at hx
    change v (x-b) ≤ v s
    have heq : x-b = (x-a)+(a-b) := by ring
    rw [heq]
    exact le_trans (v.map_add _ _) (max_le (hrs ▸ hx) hab.le)
  · intro hx
    change v (x-b) ≤ v s at hx
    change v (x-a) ≤ v r
    have heq : x-a = (x-b)+(b-a) := by ring
    rw [heq]
    exact le_trans (v.map_add _ _) (max_le (hrs.symm ▸ hx) hba.le)

end SpecialTransformations.Section3.Balls
