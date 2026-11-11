import Section3.MeanInBalls
import Section3.EncodedBallGeometry
import Section3.SortedBoolean
import Section3.SortedFunctionClosure
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.Remark319Audit

/-- The definable multiplicative subgroup of signs, already in characteristic zero. -/
def signs {K : Type} [Field K] : Subgroup Kˣ where
  carrier := {u | u = 1 ∨ u = -1}
  one_mem' := Or.inl rfl
  mul_mem' := by
    rintro u w (rfl | rfl) (rfl | rfl) <;> simp
  inv_mem' := by
    rintro u (rfl | rfl) <;> simp

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

noncomputable def points : Finset (VFType (M := M)) := {1, -1}

def rawSigns : Set M := Subtype.val '' (points (M := M) : Set (VFType (M := M)))

theorem mem_points (x : VFType (M := M)) : x ∈ points (M := M) ↔ x = 1 ∨ x = -1 := by
  change x ∈ insert (1 : VFType (M := M)) {-1} ↔ _
  rw [Finset.mem_insert, Finset.mem_singleton]

theorem signs_image : (fun u : (VFType (M := M))ˣ => u.val.val) ''
    ((signs (K := VFType (M := M))) : Set (VFType (M := M))ˣ) = rawSigns (M := M) := by
  classical
  ext z
  change (∃ u : (VFType (M := M))ˣ, (u = 1 ∨ u = -1) ∧ u.val.val = z) ↔
    (∃ x : VFType (M := M), x ∈ points (M := M) ∧ x.val = z)
  constructor
  · rintro ⟨u, hu, rfl⟩
    rcases hu with rfl | rfl
    · exact ⟨(1 : VFType (M := M)), Finset.mem_insert_self _ _, rfl⟩
    · exact ⟨(-1 : VFType (M := M)), Finset.mem_insert_of_mem (Finset.mem_singleton_self _), rfl⟩
  · rintro ⟨x, hx, rfl⟩
    rcases (mem_points x).mp hx with hx | hx
    · subst x
      exact ⟨1, Or.inl rfl, rfl⟩
    · subst x
      exact ⟨-1, Or.inr rfl, rfl⟩

theorem rawSigns_definable (S : Set M) : DefinableAt S .vf (rawSigns (M := M)) := by
  have h1 : DefinableClosureAt S .vf (1 : VFType (M := M)).val :=
    definableClosureAt_function_symbol S Fn.vfOne Fin.elim0 (fun i => i.elim0) (fun i => i.elim0)
  have hm : DefinableClosureAt S .vf (-1 : VFType (M := M)).val :=
    definableClosureAt_function_symbol S Fn.vfNeg ![(1 : VFType (M := M)).val]
      (by intro i; fin_cases i; exact (1 : VFType (M := M)).property)
      (by intro i; fin_cases i; exact h1)
  have he : rawSigns (M := M) = {(1 : VFType (M := M)).val} ∪ {(-1 : VFType (M := M)).val} := by
    ext z
    simp only [rawSigns, points, Finset.coe_insert, Finset.coe_singleton,
      Set.image_insert_eq, Set.image_singleton, Set.singleton_union]
  rw [he]
  exact h1.union hm

theorem zero_not_mem : (0 : VFType (M := M)).val ∉ rawSigns (M := M) := by
  change ¬ ∃ x : VFType (M := M), x ∈ points (M := M) ∧ x.val = (0 : VFType (M := M)).val
  rintro ⟨x, hx, he⟩
  have hx0 : x = (0 : VFType (M := M)) := Subtype.ext he
  rcases (mem_points x).mp hx with h | h
  · exact zero_ne_one (hx0.symm.trans h)
  · exact neg_ne_zero.mpr (one_ne_zero : (1 : VFType (M := M)) ≠ 0) (hx0.symm.trans h).symm

/-- Concrete obstruction to the unrestricted classification in Remark3.19:
the signs form a parameter-free definable subgroup, but its VF point set is
not a ball. Any such ball would contain the mean zero of 1 and -1. -/
theorem rawSigns_not_ball (h00 : M ⊨ Axioms.ACVF00) : ¬ IsBall (rawSigns (M := M)) := by
  intro hB
  obtain ⟨Γ, hΓ, v, hv⟩ := VFValued.exists_valuation_predV (M := M)
  letI := hΓ
  have hdiff : (1 : VFType (M := M)) ≠ -1 := by
    intro h
    have h2 : (2 : VFType (M := M)) = 0 := by
      calc
        (2 : VFType (M := M)) = 1 + 1 := by ring
        _ = 1 + -1 := congrArg (fun x : VFType (M := M) => 1 + x) h
        _ = 0 := add_neg_cancel _
    exact Barycentre.natCast_ne_zero h00 2 (by decide) h2
  have hmean : Barycentre.mean (points (M := M)) = 0 := by
    simp [Barycentre.mean, points, Finset.sum_pair hdiff]
  have hne : (points (M := M)).Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  obtain ⟨a, ⟨ρ, he⟩ | ⟨ρ, he⟩⟩ := encodedBall_disc v hv (rawSigns (M := M)) hB
  · have hmem : ∀ x ∈ points (M := M), x ∈ Balls.openDisc v a ρ := by
      intro x hx
      exact (Set.ext_iff.mp he x).mp ⟨x, hx, rfl⟩
    have hm := Barycentre.mean_mem_openDisc v hv h00 (points (M := M)) hne a ρ hmem
    rw [hmean] at hm
    exact zero_not_mem ((Set.ext_iff.mp he 0).mpr hm)
  · have hmem : ∀ x ∈ points (M := M), x ∈ Balls.closedDisc v a ρ := by
      intro x hx
      exact (Set.ext_iff.mp he x).mp ⟨x, hx, rfl⟩
    have hm := Barycentre.mean_mem_closedDisc v hv h00 (points (M := M)) hne a ρ hmem
    rw [hmean] at hm
    exact zero_not_mem ((Set.ext_iff.mp he 0).mpr hm)

theorem rawSigns_not_valuation_units (h00 : M ⊨ Axioms.ACVF00)
    {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y) :
    rawSigns (M := M) ≠ Subtype.val '' {x : VFType (M := M) | v x = 1} := by
  intro he
  have h3val : v (3 : VFType (M := M)) = 1 := Barycentre.natCast_value_one v hv h00 3 (by decide)
  have h3 : (3 : VFType (M := M)).val ∈ rawSigns (M := M) :=
    he.symm ▸ ⟨(3 : VFType (M := M)), h3val, rfl⟩
  obtain ⟨x, hx, hex⟩ := h3
  have hex' : x = (3 : VFType (M := M)) := Subtype.ext hex
  have hp := (mem_points x).mp hx
  have hp' : (3 : VFType (M := M)) = 1 ∨ (3 : VFType (M := M)) = -1 :=
    hp.imp (fun h => hex'.symm.trans h) (fun h => hex'.symm.trans h)
  rcases hp' with h | h
  · have hz : (2 : VFType (M := M)) = 0 := by linear_combination h
    exact Barycentre.natCast_ne_zero h00 2 (by decide) hz
  · have hz : (4 : VFType (M := M)) = 0 := by linear_combination h
    exact Barycentre.natCast_ne_zero h00 4 (by decide) hz

end SpecialTransformations.Section3.Remark319Audit
