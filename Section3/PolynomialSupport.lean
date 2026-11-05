import Section3.PolynomialSyntax
import CanonicalRV
import CanonicalStructure
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.PolynomialSupport
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M}

/-- The finite list of unary VF polynomials below rv nodes. Zero polynomials
are harmless: their root multiset is empty and their RV value is constant. -/
noncomputable def term (p : Parameters S) (E : Subfield (VFType (M := M)))
    (hp : ∀ i (h : iVF (p.values i)), (⟨p.values i, h⟩ : VFType (M := M)) ∈ E) :
    LRV.Term (Fin p.length ⊕ Fin 1) → List (Polynomial E)
  | .var _ => []
  | .func .rvMap ts => [PolynomialSyntax.toPolynomial p E hp (ts 0)]
  | .func _ ts => (List.finRange _).flatMap (fun i => term p E hp (ts i))

omit hM in
private theorem eval_rvMap {α : Type} (ts : Fin 1 → LRV.Term α) (v : α → M) :
    (Term.func Fn.rvMap ts).realize v = iRv ((ts 0).realize v) := by
  change Structure.funMap (L := LRV) Fn.rvMap (fun i => (ts i).realize v) = _
  have he : (fun i => (ts i).realize v) = ![(ts 0).realize v] := by
    funext i
    fin_cases i
    rfl
  rw [he]
  rfl

theorem rv_term_eq_of_support (p : Parameters S) (E : Subfield (VFType (M := M)))
    (hp : ∀ i (h : iVF (p.values i)), (⟨p.values i, h⟩ : VFType (M := M)) ∈ E)
    (t : LRV.Term (Fin p.length ⊕ Fin 1))
    (ht : TmSort p.sorts (fun _ => .vf) t = some .rv)
    (x y : VFType (M := M))
    (hP : ∀ q ∈ term p E hp t,
      iRv ((q.eval₂ E.subtype x).val) = iRv ((q.eval₂ E.subtype y).val)) :
    t.realize (Sum.elim p.values ![x.val]) = t.realize (Sum.elim p.values ![y.val]) := by
  induction t with
  | var i =>
    cases i with
    | inl i => rfl
    | inr i => cases ht
  | func f ts ih =>
    obtain ⟨harg, hres⟩ := (tmSort_func_iff p.sorts (fun _ => .vf) f ts).mp ht
    have hfunc {k : ℕ} (f : Fn k) (ts : Fin k → LRV.Term (Fin p.length ⊕ Fin 1))
        (h : ∀ i, (ts i).realize (Sum.elim p.values ![x.val]) =
          (ts i).realize (Sum.elim p.values ![y.val])) :
        (Term.func f ts).realize (Sum.elim p.values ![x.val]) =
          (Term.func f ts).realize (Sum.elim p.values ![y.val]) := by
      change Structure.funMap (L := LRV) f _ = Structure.funMap (L := LRV) f _
      congr 1
      funext i
      exact h i
    cases f with
    | vfZero => cases hres
    | vfOne => cases hres
    | vfAdd => cases hres
    | vfMul => cases hres
    | vfNeg => cases hres
    | rvZero => exact hfunc _ _ (fun i => i.elim0)
    | rvOne => exact hfunc _ _ (fun i => i.elim0)
    | rvMul =>
      apply hfunc
      intro i
      apply ih i (harg i)
      intro q hq
      exact hP q (List.mem_flatMap.mpr ⟨i, List.mem_finRange i, hq⟩)
    | rvInv =>
      apply hfunc
      intro i
      apply ih i (harg i)
      intro q hq
      exact hP q (List.mem_flatMap.mpr ⟨i, List.mem_finRange i, hq⟩)
    | kAdd =>
      apply hfunc
      intro i
      apply ih i (harg i)
      intro q hq
      exact hP q (List.mem_flatMap.mpr ⟨i, List.mem_finRange i, hq⟩)
    | kNeg =>
      apply hfunc
      intro i
      apply ih i (harg i)
      intro q hq
      exact hP q (List.mem_flatMap.mpr ⟨i, List.mem_finRange i, hq⟩)
    | rvMap =>
      rw [eval_rvMap, eval_rvMap,
        PolynomialSyntax.realizes p E hp (ts 0) (harg 0) x,
        PolynomialSyntax.realizes p E hp (ts 0) (harg 0) y]
      exact hP _ (List.mem_cons_self)


/-- A finite support for all VF dependence of a unary quantifier-free formula. -/
noncomputable def formula (p : Parameters S) (E : Subfield (VFType (M := M)))
    (hp : ∀ i (h : iVF (p.values i)), (⟨p.values i, h⟩ : VFType (M := M)) ∈ E) :
    LRV.BoundedFormula (Fin p.length) 1 → List (Polynomial E)
  | .falsum => []
  | .equal t u => if TmSort p.sorts (fun _ => .vf) t = some .vf then
      [PolynomialSyntax.toPolynomial p E hp t - PolynomialSyntax.toPolynomial p E hp u]
    else term p E hp t ++ term p E hp u
  | .rel _ ts => (List.finRange _).flatMap (fun i => term p E hp (ts i))
  | .imp φ ψ => formula p E hp φ ++ formula p E hp ψ
  | .all _ => []

theorem formula_iff_of_support (p : Parameters S) (E : Subfield (VFType (M := M)))
    (hp : ∀ i (h : iVF (p.values i)), (⟨p.values i, h⟩ : VFType (M := M)) ∈ E)
    (φ : LRV.BoundedFormula (Fin p.length) 1) (hqf : φ.IsQF)
    (hws : WellSorted p.sorts (fun _ => .vf) φ)
    (x y : VFType (M := M))
    (hP : ∀ q ∈ formula p E hp φ,
      iRv ((q.eval₂ E.subtype x).val) = iRv ((q.eval₂ E.subtype y).val)) :
    φ.Realize p.values ![x.val] ↔ φ.Realize p.values ![y.val] := by
  induction hqf with
  | falsum => exact Iff.rfl
  | of_isAtomic hatom =>
    cases hatom with
    | equal t u =>
      simp only [Term.bdEqual, formula] at hP
      cases hws with
      | @equal _ _ _ _ σ ht hu =>
        cases σ with
        | rv =>
          have hnot : TmSort p.sorts (fun _ => .vf) t ≠ some .vf := by rw [ht]; decide
          have hsupport (q) (hq : q ∈ term p E hp t ++ term p E hp u) :
              iRv ((q.eval₂ E.subtype x).val) = iRv ((q.eval₂ E.subtype y).val) := by
            apply hP q
            change q ∈ (if TmSort p.sorts (fun _ => .vf) t = some .vf then
              [PolynomialSyntax.toPolynomial p E hp t - PolynomialSyntax.toPolynomial p E hp u]
              else term p E hp t ++ term p E hp u)
            rw [if_neg hnot]
            exact hq
          change t.realize _ = u.realize _ ↔ t.realize _ = u.realize _
          rw [rv_term_eq_of_support p E hp t ht x y (fun q hq => hsupport q (List.mem_append_left _ hq)),
            rv_term_eq_of_support p E hp u hu x y (fun q hq => hsupport q (List.mem_append_right _ hq))]
        | vf =>
          let D := PolynomialSyntax.toPolynomial p E hp t - PolynomialSyntax.toPolynomial p E hp u
          have hD (z : VFType (M := M)) : (t.bdEqual u).Realize p.values ![z.val] ↔
              D.eval₂ E.subtype z = 0 := by
            change t.realize _ = u.realize _ ↔ _
            rw [PolynomialSyntax.realizes p E hp t ht z, PolynomialSyntax.realizes p E hp u hu z]
            exact Subtype.val_inj.trans (by simp only [D, Polynomial.eval₂_sub, sub_eq_zero])
          have hrv := hP D (by
            change D ∈ (if TmSort p.sorts (fun _ => .vf) t = some .vf then
              [PolynomialSyntax.toPolynomial p E hp t - PolynomialSyntax.toPolynomial p E hp u]
              else term p E hp t ++ term p E hp u)
            rw [if_pos ht]
            exact List.mem_cons_self)
          exact (hD x).trans (((CanonicalRV.encodedRv_zero_iff _).symm.trans
            ((congrArg (fun z : M => z = iRVZero) hrv).to_iff.trans
              (CanonicalRV.encodedRv_zero_iff _))).trans (hD y).symm)
    | rel R ts =>
      simp only [Relations.boundedFormula, formula] at hP
      cases hws with
      | rel _ _ _ hts =>
        have hrel {k : ℕ} (R : Rel k) (ts : Fin k → LRV.Term (Fin p.length ⊕ Fin 1))
            (h : ∀ i, (ts i).realize (Sum.elim p.values ![x.val]) =
              (ts i).realize (Sum.elim p.values ![y.val])) :
            (BoundedFormula.rel R ts).Realize p.values ![x.val] ↔
              (BoundedFormula.rel R ts).Realize p.values ![y.val] := by
          change Structure.RelMap (L := LRV) R _ ↔ Structure.RelMap (L := LRV) R _
          have he : (fun i => (ts i).realize (Sum.elim p.values ![x.val])) =
              (fun i => (ts i).realize (Sum.elim p.values ![y.val])) := funext h
          rw [he]
        have hsupport (i) (q) (hq : q ∈ term p E hp (ts i)) :=
          hP q (by
            change q ∈ (List.finRange _).flatMap (fun j => term p E hp (ts j))
            exact List.mem_flatMap.mpr ⟨i, List.mem_finRange i, hq⟩)
        cases R with
        | memUnits => exact hrel _ _ (fun i => rv_term_eq_of_support p E hp (ts i) (hts i) x y (hsupport i))
        | rvLe => exact hrel _ _ (fun i => rv_term_eq_of_support p E hp (ts i) (hts i) x y (hsupport i))
        | memVF =>
          have htrue (z : VFType (M := M)) :
              (BoundedFormula.rel Rel.memVF ts).Realize p.values ![z.val] := by
            have hz : ∀ i : Fin 1, sortEval SortTag.vf (![z.val] i) := by
              intro i; fin_cases i; exact z.property
            have hs := CanonicalStructure.term_sort hM p.sorts (fun _ => .vf) p.values ![z.val]
              p.sorted hz (ts 0) (hts 0)
            change Structure.RelMap (L := LRV) Rel.memVF (fun i => (ts i).realize _)
            have he : (fun i => (ts i).realize (Sum.elim p.values ![z.val])) =
                (![(ts 0).realize (Sum.elim p.values ![z.val])] : Fin 1 → M) := by
              funext i; fin_cases i; rfl
            rw [he]; exact hs
          exact iff_of_true (htrue x) (htrue y)
        | memRV =>
          have htrue (z : VFType (M := M)) :
              (BoundedFormula.rel Rel.memRV ts).Realize p.values ![z.val] := by
            have hz : ∀ i : Fin 1, sortEval SortTag.vf (![z.val] i) := by
              intro i; fin_cases i; exact z.property
            have hs := CanonicalStructure.term_sort hM p.sorts (fun _ => .vf) p.values ![z.val]
              p.sorted hz (ts 0) (hts 0)
            change Structure.RelMap (L := LRV) Rel.memRV (fun i => (ts i).realize _)
            have he : (fun i => (ts i).realize (Sum.elim p.values ![z.val])) =
                (![(ts 0).realize (Sum.elim p.values ![z.val])] : Fin 1 → M) := by
              funext i; fin_cases i; rfl
            rw [he]; exact hs
          exact iff_of_true (htrue x) (htrue y)
  | @imp φ ψ hφ hψ ihφ ihψ =>
    simp only [formula] at hP
    cases hws with
    | imp _ hwφ hwψ =>
      exact imp_congr (ihφ hwφ (fun q hq => hP q (by
        exact List.mem_append_left _ hq)))
        (ihψ hwψ (fun q hq => hP q (by
            exact List.mem_append_right _ hq)))

end SpecialTransformations.Section3.PolynomialSupport

