import SubstructureField

/-! Preservation of the valuation predicate passes from a substructure's VF
ring to its generated field. No shared value group is required. -/

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
open SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Milestone0.VFValued
open scoped FirstOrder

namespace SubfieldExtension

theorem pred_div_iff_cross_mul {K : Type*} [Field K] {p : K → K → Prop}
    (hp : IsValPred p) (a b c d : K) (hb : b ≠ 0) (hd : d ≠ 0) :
    p (a / b) (c / d) ↔ p (a * d) (c * b) := by
  have h₁ : (a / b) * (b * d) = a * d := by
    rw [← mul_assoc, div_mul_cancel₀ _ hb]
  have h₂ : (c / d) * (b * d) = c * b := by
    rw [mul_comm b d, ← mul_assoc, div_mul_cancel₀ _ hd]
  simpa only [h₁, h₂] using hp.scale (a / b) (c / d) (b * d) (mul_ne_zero hb hd)

/-- A ring embedding preserving valuation comparison extends to a field
embedding preserving the same comparison on all generated fractions. -/
theorem extend_pred_iff {R K L : Type*} [CommRing R] [IsDomain R] [Field K] [Field L]
    (r : R →+* K) (hr : Function.Injective r)
    (σ : R →+* L) (hσ : Function.Injective σ)
    (p : K → K → Prop) (q : L → L → Prop) (hp : IsValPred p) (hq : IsValPred q)
    (hbase : ∀ x y : R, q (σ x) (σ y) ↔ p (r x) (r y))
    (z w : Subfield.closure (Set.range r)) :
    q (extend r hr σ hσ z) (extend r hr σ hσ w) ↔ p (z : K) (w : K) := by
  obtain ⟨a, b, hb, rfl⟩ := generator_div_surjective r hr z
  obtain ⟨c, d, hd, rfl⟩ := generator_div_surjective r hr w
  have hrb : r b ≠ 0 := fun h => hb (hr (h.trans r.map_zero.symm))
  have hrd : r d ≠ 0 := fun h => hd (hr (h.trans r.map_zero.symm))
  have hσb : σ b ≠ 0 := fun h => hb (hσ (h.trans σ.map_zero.symm))
  have hσd : σ d ≠ 0 := fun h => hd (hσ (h.trans σ.map_zero.symm))
  simp only [extend_generator_div]
  change q (σ a / σ b) (σ c / σ d) ↔ p (r a / r b) (r c / r d)
  rw [pred_div_iff_cross_mul hq _ _ _ _ hσb hσd,
    pred_div_iff_cross_mul hp _ _ _ _ hrb hrd]
  simpa only [map_mul] using hbase (a * d) (c * b)

end SubfieldExtension

namespace SubstructureField

variable {M N : Type} [LRV.Structure M] [LRV.Structure N]
  [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]

def rvElement (S : LRV.Substructure M) (x : S) : S :=
  ⟨iRv (x : M), S.fun_mem Fn.rvMap ![(x : M)] (by
    intro i; fin_cases i; exact x.2)⟩

theorem map_rvElement (S : LRV.Substructure M) (f : S ↪[LRV] N) (x : S) :
    f (rvElement S x) = iRv (f x) := by
  have h := map_function S f Fn.rvMap ![(x : M)] (by
    intro i; fin_cases i; exact x.2)
  apply h.trans
  change Structure.funMap (L := LRV) Fn.rvMap _ =
    Structure.funMap (L := LRV) Fn.rvMap ![f x]
  congr 1
  funext i
  fin_cases i
  rfl

theorem iLe_map (S : LRV.Substructure M) (f : S ↪[LRV] N) (x y : S) :
    iLe (f x) (f y) ↔ iLe (x : M) (y : M) := by
  have h := f.map_rel Rel.rvLe ![x, y]
  have ht : (f ∘ ![x, y]) = ![f x, f y] := by
    funext i; fin_cases i <;> rfl
  have hs : (fun i : Fin 2 => ((![x, y] : Fin 2 → S) i : M)) = ![(x : M), (y : M)] := by
    funext i; fin_cases i <;> rfl
  change Structure.RelMap (L := LRV) Rel.rvLe (f ∘ ![x, y]) ↔
    Structure.RelMap (L := LRV) Rel.rvLe (fun i : Fin 2 => ((![x, y] : Fin 2 → S) i : M)) at h
  rw [ht, hs] at h
  exact h

theorem ringMap_pred_iff (S : LRV.Substructure M) (f : S ↪[LRV] N)
    (x y : vfRing S) :
    predV (ringMap S f x) (ringMap S f y) ↔ predV (x : VFType (M := M)) (y : VFType (M := M)) := by
  have h := iLe_map S f (rvElement S ⟨y.1.1, y.2⟩) (rvElement S ⟨x.1.1, x.2⟩)
  rw [map_rvElement, map_rvElement] at h
  exact h

/-- The field frame extracted from an arbitrary language-substructure embedding
is a valued-field embedding in the exact predicate supplied by the frozen theory. -/
theorem fieldMap_pred_iff (S : LRV.Substructure M) (f : S ↪[LRV] N)
    (z w : generatedField S) :
    predV (fieldMap S f z) (fieldMap S f w) ↔
      predV (z : VFType (M := M)) (w : VFType (M := M)) := by
  exact SubfieldExtension.extend_pred_iff (vfRing S).subtype Subtype.coe_injective
    (ringMap S f) (ringMap_injective S f) (predV (M := M)) (predV (M := N))
    (isValPred_predV (M := M)) (isValPred_predV (M := N)) (ringMap_pred_iff S f) z w

/-- The same preservation statement for any two valuations representing the
model predicates, even when their value groups differ. -/
theorem fieldMap_valuation_iff {Γ Δ : Type*}
    [LinearOrderedCommGroupWithZero Γ] [LinearOrderedCommGroupWithZero Δ]
    (v : Valuation (VFType (M := M)) Γ) (w : Valuation (VFType (M := N)) Δ)
    (hv : ∀ x y, predV x y ↔ v x ≤ v y) (hw : ∀ x y, predV x y ↔ w x ≤ w y)
    (S : LRV.Substructure M) (f : S ↪[LRV] N) (x y : generatedField S) :
    w (fieldMap S f x) ≤ w (fieldMap S f y) ↔ v (x : VFType (M := M)) ≤ v (y : VFType (M := M)) :=
  (hw _ _).symm.trans ((fieldMap_pred_iff S f x y).trans (hv _ _))

end SubstructureField

#print axioms SubfieldExtension.extend_pred_iff
#print axioms SubstructureField.ringMap_pred_iff
#print axioms SubstructureField.fieldMap_pred_iff
#print axioms SubstructureField.fieldMap_valuation_iff
