module

public import Section3.Average

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.Barycentre
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem natCast_ne_zero (h00 : M ⊨ Axioms.ACVF00) (k : ℕ) (hk : k ≠ 0) :
    (k : VFType (M := M)) ≠ 0 := by
  intro hz
  have h := Average.nat_unit h00 k hk
  rw [hz, Average.val_zero] at h
  exact RVCalc.rv_one_ne_zero hM
    (RVCalc.le_infty_eq hM (rv_one_mem hM) h)

noncomputable def mean (A : Finset (VFType (M := M))) : VFType (M := M) :=
  (∑ x ∈ A, x) / (A.card : VFType (M := M))

theorem sum_sub_mean (h00 : M ⊨ Axioms.ACVF00) (A : Finset (VFType (M := M))) :
    (∑ x ∈ A, (x - mean A)) = 0 := by
  classical
  by_cases hA : A.card = 0
  · have he : A = ∅ := Finset.card_eq_zero.mp hA
    simp [he]
  · have hn := natCast_ne_zero h00 A.card hA
    simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mean]
    field_simp [hn]; ring

theorem mean_equation_of_equiv (h00 : M ⊨ Axioms.ACVF00)
    (A : Finset (VFType (M := M))) {k : ℕ} (hk : k ≠ 0) (e : Fin k ≃ ↥A)
    (z : VFType (M := M)) :
    (k : VFType (M := M)) * z = ∑ i, (e i).val ↔ z = mean A := by
  have hcard : k = A.card := by
    have h := Fintype.card_congr e
    simpa only [Fintype.card_fin, Fintype.card_coe] using h
  have hsum : (∑ i, (e i).val) = ∑ x ∈ A, x := by
    rw [e.sum_comp (fun x : A => x.val)]
    exact Finset.sum_coe_sort A (fun x => x)
  rw [hsum, mean, ← hcard, eq_div_iff (natCast_ne_zero h00 k hk),
    mul_comm (k : VFType (M := M)) z]

/-- Centering a finite set of at least two distinct points at its mean
separates at least two RV classes, in residue characteristic zero. -/
theorem rv_nonconstant (h00 : M ⊨ Axioms.ACVF00) (A : Finset (VFType (M := M)))
    (hA : 2 ≤ A.card) :
    ∃ x ∈ A, ∃ y ∈ A, iRv (x - mean A).val ≠ iRv (y - mean A).val := by
  classical
  by_contra! h
  let e : ↥A ≃ Fin A.card := Finset.equivFin A
  let c (i : Fin A.card) : VFType (M := M) := (e.symm i).val
  let g (i : Fin A.card) : VFType (M := M) := c i - mean A
  let i₀ : Fin A.card := ⟨0, by omega⟩
  have hinj : Function.Injective g := by
    intro i j hij
    apply e.symm.injective
    apply Subtype.ext
    exact sub_left_inj.mp hij
  have hsum : (∑ i, g i) = 0 := by
    have he := e.symm.sum_comp (fun x : A => x.val - mean A)
    exact he.trans ((Finset.sum_coe_sort A (fun x => x - mean A)).trans
      (sum_sub_mean h00 A))
  have hs (i : Fin A.card) : Average.val (g i) = Average.val (g i₀) :=
    h (c i) (e.symm i).property (c i₀) (e.symm i₀).property
  have hsame (i : Fin A.card) :
      iLe (Average.val (g i)) (Average.val (g i₀)) ∧
      iLe (Average.val (g i₀)) (Average.val (g i)) := by
    rw [hs i]
    exact ⟨RVCalc.le_refl_rv hM (Average.val_mem _),
      RVCalc.le_refl_rv hM (Average.val_mem _)⟩
  obtain ⟨i, j, _, _, _, hij⟩ := Average.lemma_3_8 h00 hA i₀ g hinj hsame hsum
  exact hij (h (c i) (e.symm i).property (c j) (e.symm j).property)

theorem fibre_card_lt (h00 : M ⊨ Axioms.ACVF00) (A : Finset (VFType (M := M)))
    (hA : 2 ≤ A.card) (t : M) :
    (A.filter (fun x => iRv (x - mean A).val = t)).card < A.card := by
  classical
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, ?_⟩
  intro he
  obtain ⟨x, hx, y, hy, hxy⟩ := rv_nonconstant h00 A hA
  rw [← he] at hx hy
  exact hxy ((Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm)

end SpecialTransformations.Section3.Barycentre
