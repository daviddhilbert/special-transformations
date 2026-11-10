import Section3.GuardedRationalNormalForm
import Section8.GammaRadiusBase

/-! Finite RV data for a relation with a block of RV variables. The
published QE and the sorted Boolean syntax isolate VF dependence in
finitely many RV values, uniformly in the final RV block. -/

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section8
open SpecialTransformations.Section3.GuardedRVNormalForm

noncomputable section

namespace SpecialTransformations.Section10

attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

variable {M I R V : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
local notation "VF" => VFType (M := M)
local notation "RV" => CanonicalRV.RVSort M

private def exprSupport : RVExpr I R V → List (VFPolynomial I)
  | .vf P => [P]
  | .mul P Q | .addK P Q => exprSupport P ++ exprSupport Q
  | .inv P | .negK P => exprSupport P
  | _ => []

private theorem expr_eval_eq (a b : I → VF) (r : R → RV) (t : V → RV)
    (P : RVExpr I R V) (h : ∀ Q ∈ exprSupport P,
      RVOperations.rvHom (Q.realize a) = RVOperations.rvHom (Q.realize b)) :
    P.eval a r t = P.eval b r t := by
  induction P with
  | zero | one | parameter | ofVariable => rfl
  | vf Q => exact h Q List.mem_cons_self
  | mul P Q hp hq | addK P Q hp hq =>
    have hp' := hp (fun f hf => h f (List.mem_append_left _ hf))
    have hq' := hq (fun f hf => h f (List.mem_append_right _ hf))
    simp only [RVExpr.eval, hp', hq']
  | inv P hp | negK P hp => simp only [RVExpr.eval, hp h]

private def booleanSupport : PolarityDNF.Expr (RVAtom I R V) → List (VFPolynomial I)
  | .falsum => []
  | .atom (.equality P Q) | .atom (.order P Q) => exprSupport P ++ exprSupport Q
  | .imp P Q => booleanSupport P ++ booleanSupport Q

private theorem boolean_eval_iff (a b : I → VF) (r : R → RV) (t : V → RV)
    (E : PolarityDNF.Expr (RVAtom I R V)) (h : ∀ P ∈ booleanSupport E,
      RVOperations.rvHom (P.realize a) = RVOperations.rvHom (P.realize b)) :
    E.eval (RVAtom.eval a r t) ↔ E.eval (RVAtom.eval b r t) := by
  induction E with
  | falsum => rfl
  | imp P Q hp hq =>
    exact imp_congr (hp (fun f hf => h f (List.mem_append_left _ hf)))
      (hq (fun f hf => h f (List.mem_append_right _ hf)))
  | atom A =>
    cases A with
    | equality P Q | order P Q =>
      have hp := expr_eval_eq a b r t P (fun f hf => h f (List.mem_append_left _ hf))
      have hq := expr_eval_eq a b r t Q (fun f hf => h f (List.mem_append_right _ hf))
      simp only [PolarityDNF.Expr.eval, RVAtom.eval, hp, hq]

/-- Over a canonical model, the truth of a sorted definable relation with
RV outputs is determined by the input RV slots and a finite tuple of
same-base definable RV values of the input. -/
theorem exists_rv_preparation_data (hc : CanonicalStructure.IsCanonical (M := M))
    {ι ρ : Type} [Finite ι] [Finite ρ] {S : Set M} (σ : ι → SortTag)
    (H : Set ((ι ⊕ ρ) → M)) (hH : S.Definable LRV H)
    (hHsort : ∀ z ∈ H, ∀ j, sortEval (Sum.elim σ (fun _ => .rv) j) (z j)) :
    ∃ (d : ℕ) (f : (ι → M) → Fin d → M), S.DefinableMap LRV f ∧
      (∀ x, (∀ i, sortEval (σ i) (x i)) → ∀ i, iRV (f x i)) ∧
      ∀ (x y : ι → M) (t : ρ → M), (∀ i, sortEval (σ i) (x i)) →
        (∀ i, sortEval (σ i) (y i)) → (∀ i, iRV (t i)) →
        (∀ i, σ i = .rv → x i = y i) → f x = f y →
        (Sum.elim x t ∈ H ↔ Sum.elim y t ∈ H) := by
  let _ := Fintype.ofFinite (ι ⊕ ρ)
  let e := (Fintype.equivFin (ι ⊕ ρ)).symm
  let sn := Sum.elim σ (fun _ : ρ => SortTag.rv) ∘ e
  let D := {z | z ∘ e.symm ∈ H}
  have hD : S.Definable LRV D := hH.preimage_comp e.symm
  have hDN : @Set.Definable M S LRV (@CanonicalStructure.normalize M sM) _ D :=
    (normalize_eq_of_isCanonical hc).symm ▸ hD
  have hsort (z) (hz : z ∈ D) (i) : sortEval (sn i) (z i) := by
    simpa only [sn, Function.comp_apply, Equiv.symm_apply_apply] using
      hHsort (z ∘ e.symm) hz (e i)
  obtain ⟨p, φ, hqf, hws, hφ⟩ := DefinableOver.quantifier_free hM
    ((definableOver_iff_normalized_raw S sn D).mpr ⟨hDN, hsort⟩)
  obtain ⟨E, hE⟩ := qf_source_boolean p.sorts sn φ hqf hws
  let Q := booleanSupport E
  let pack (x : ι → M) (t : ρ → M) := Sum.elim x t ∘ e
  have hp (x : ι → M) (t : ρ → M) (hx : ∀ i, sortEval (σ i) (x i)) (ht : ∀ i, iRV (t i)) :
      ∀ i, sortEval (sn i) (pack x t i) := by
    intro i
    cases hi : e i with
    | inl j => simpa only [sn, pack, Function.comp_apply, hi, Sum.elim_inl] using hx j
    | inr j => simpa only [sn, pack, Function.comp_apply, hi, Sum.elim_inr, sortEval, iRV] using ht j
  let dummy : ρ → M := fun _ => iRVZero
  have hdummy : ∀ i, iRV (dummy i) := fun _ => rv_zero_mem hM
  have hzero : S.DefinableFun LRV (fun _ : ι → M => iRVZero) :=
    (Set.DefinableFun.of_empty (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.rvZero)).comp
      (show S.DefinableMap LRV (fun _ : ι → M => Fin.elim0) from fun i => i.elim0)
  let term (P : VFPolynomial (VFSlot p.sorts sn)) : LRV.Term (Fin p.length ⊕ Fin (Fintype.card (ι ⊕ ρ))) :=
    (RVExpr.vf P).toTerm (vfSlotMap p.sorts sn) (rvParameterMap p.sorts) (rvVariableMap sn)
  let f (x : ι → M) (i : Fin Q.length) := (term (Q.get i)).realize (Sum.elim p.values (pack x dummy))
  have hf : S.DefinableMap LRV f := by
    intro i
    apply ((term (Q.get i)).definableFun_realize.of_empty).comp
    intro j
    cases j with
    | inl j => exact LRV.definableFun_const _ (p.mem_base j)
    | inr j =>
      cases hj : e j with
      | inl l => simpa only [pack, Function.comp_apply, hj, Sum.elim_inl, Sum.elim_inr] using
          (Set.DefinableFun.proj (A := S) (i := l) LRV)
      | inr l => simpa only [pack, Function.comp_apply, hj, Sum.elim_inr, dummy] using hzero
  let a (x : ι → M) (t : ρ → M) (hx : ∀ i, sortEval (σ i) (x i)) (ht : ∀ i, iRV (t i)) :=
    SourceAssignment.vfValues p.sorts sn p.values (pack x t) p.sorted (hp x t hx ht)
  have ha (x : ι → M) (t : ρ → M) (hx : ∀ i, sortEval (σ i) (x i)) (ht : ∀ i, iRV (t i)) :
      a x dummy hx hdummy = a x t hx ht := by
    funext j
    apply Subtype.ext
    obtain ⟨j, hj⟩ := j
    cases j with
    | inl j => rfl
    | inr j =>
      change sn j = .vf at hj
      change pack x dummy j = pack x t j
      cases he : e j with
      | inl l => simp only [pack, Function.comp_apply, he, Sum.elim_inl]
      | inr l => simp only [sn, Function.comp_apply, he, Sum.elim_inr, reduceCtorEq] at hj
  have hreal (x : ι → M) (hx : ∀ i, sortEval (σ i) (x i)) (i : Fin Q.length) :
      f x i = (RVOperations.rvHom ((Q.get i).realize (a x dummy hx hdummy))).val :=
    SourceAssignment.expression_realize p.sorts sn p.values (pack x dummy) p.sorted
      (hp x dummy hx hdummy) (RVExpr.vf (Q.get i))
  have hrv (x) (hx : ∀ i, sortEval (σ i) (x i)) (i) : iRV (f x i) := by
    rw [hreal x hx i]
    exact (RVOperations.rvHom ((Q.get i).realize (a x dummy hx hdummy))).property
  refine ⟨Q.length, f, hf, hrv, ?_⟩
  intro x y t hx hy ht hxy hfxy
  have hr : SourceAssignment.rvVariables sn (pack x t) (hp x t hx ht) =
      SourceAssignment.rvVariables sn (pack y t) (hp y t hy ht) := by
    funext i
    apply Subtype.ext
    change pack x t i.val = pack y t i.val
    have hi := i.property
    cases he : e i.val with
    | inl j =>
      simp only [pack, Function.comp_apply, he, Sum.elim_inl]
      apply hxy j
      simpa only [sn, Function.comp_apply, he, Sum.elim_inl] using hi
    | inr j => simp only [pack, Function.comp_apply, he, Sum.elim_inr]
  have hdata (P : VFPolynomial (VFSlot p.sorts sn)) (hP : P ∈ Q) :
      RVOperations.rvHom (P.realize (a x t hx ht)) = RVOperations.rvHom (P.realize (a y t hy ht)) := by
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hP
    rw [← ha x t hx ht, ← ha y t hy ht]
    apply Subtype.ext
    exact (hreal x hx i).symm.trans ((congrFun hfxy i).trans (hreal y hy i))
  have hmem (z : ι → M) : Sum.elim z t ∈ H ↔ pack z t ∈ D := by
    change Sum.elim z t ∈ H ↔ pack z t ∘ e.symm ∈ H
    simp only [pack, Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id]
  have hformula (z : ι → M) (hz : ∀ i, sortEval (σ i) (z i)) :
      Sum.elim z t ∈ H ↔ φ.Realize p.values (pack z t) := by
    rw [hmem, hφ]
    exact and_iff_right (hp z t hz ht)
  rw [hformula x hx, hformula y hy, hE M p.values (pack x t) p.sorted (hp x t hx ht),
    hE M p.values (pack y t) p.sorted (hp y t hy ht), hr]
  exact boolean_eval_iff _ _ _ _ E hdata

end SpecialTransformations.Section10
