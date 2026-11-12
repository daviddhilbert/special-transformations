module

public import Section4.MultivariateSyntax
public import Section3.PolynomialLocal
public import CanonicalStructure
public import Mathlib.Topology.Algebra.MvPolynomial

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! Finite-tuple extension of the accepted Section 3 local-polynomial
argument. All language terms remain in the released LRV syntax. -/

open FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ] [Valued (VFType (M := M)) Γ]

theorem multivariate_rv_locally_constant
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {ι : Type} (p : MvPolynomial ι (VFType (M := M))) (a : ι → VFType (M := M))
    (ha : p.eval a ≠ 0) :
    {x | iRv (p.eval x).val = iRv (p.eval a).val} ∈ 𝓝 a := by
  have h : {y : VFType (M := M) | iRv y.val = iRv (p.eval a).val} ∈ 𝓝 (p.eval a) := by
    simpa only [Polynomial.eval_X] using polynomial_rv_locally_constant hv Polynomial.X (p.eval a)
      (by simpa only [Polynomial.eval_X] using ha)
  exact p.continuous_eval.continuousAt.preimage_mem_nhds h

namespace MultivariateLocal

private theorem eval_rvMap {α : Type} (ts : Fin 1 → LRV.Term α) (v : α → M) :
    (Term.func Fn.rvMap ts).realize v = iRv ((ts 0).realize v) := by
  change Structure.funMap (L := LRV) Fn.rvMap (fun i => (ts i).realize v) = _
  have he : (fun i => (ts i).realize v) = ![(ts 0).realize v] := by
    funext i
    fin_cases i
    rfl
  rw [he]
  rfl

variable {S : Set M} {n : ℕ}

theorem rvTerm_local (p : Parameters S) (E : Subfield (VFType (M := M)))
    (hp : ∀ i (h : iVF (p.values i)), (⟨p.values i, h⟩ : VFType (M := M)) ∈ E)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (a : Fin n → VFType (M := M)) (ha : AlgebraicIndependent E a)
    (t : LRV.Term (Fin p.length ⊕ Fin n))
    (ht : TmSort p.sorts (fun _ => .vf) t = some .rv) :
    {x | t.realize (Sum.elim p.values (vfValues x)) =
      t.realize (Sum.elim p.values (vfValues a))} ∈ 𝓝 a := by
  induction t with
  | var i =>
    cases i with
    | inl i => exact Filter.Eventually.of_forall (fun _ => rfl)
    | inr i => cases ht
  | func f ts ih =>
    obtain ⟨harg, hres⟩ := (tmSort_func_iff p.sorts (fun _ => .vf) f ts).mp ht
    have hfunc {k : ℕ} (f : Fn k) (ts : Fin k → LRV.Term (Fin p.length ⊕ Fin n))
        (h : ∀ i, {x | (ts i).realize (Sum.elim p.values (vfValues x)) =
          (ts i).realize (Sum.elim p.values (vfValues a))} ∈ 𝓝 a) :
        {x | (Term.func f ts).realize (Sum.elim p.values (vfValues x)) =
          (Term.func f ts).realize (Sum.elim p.values (vfValues a))} ∈ 𝓝 a := by
      filter_upwards [(Filter.eventually_all).mpr h] with x hx
      change Structure.funMap (L := LRV) f _ = Structure.funMap (L := LRV) f _
      congr 1
      funext i
      exact hx i
    cases f with
    | vfZero => cases hres
    | vfOne => cases hres
    | vfAdd => cases hres
    | vfMul => cases hres
    | vfNeg => cases hres
    | rvZero => exact hfunc _ _ (fun i => i.elim0)
    | rvOne => exact hfunc _ _ (fun i => i.elim0)
    | rvMul => exact hfunc _ _ (fun i => ih i (harg i))
    | rvInv => exact hfunc _ _ (fun i => ih i (harg i))
    | kAdd => exact hfunc _ _ (fun i => ih i (harg i))
    | kNeg => exact hfunc _ _ (fun i => ih i (harg i))
    | rvMap =>
      let q := MultivariateSyntax.toPolynomial p E hp (ts 0)
      have hterm (x : Fin n → VFType (M := M)) :
          (Term.func Fn.rvMap ts).realize (Sum.elim p.values (vfValues x)) =
            iRv ((q.eval₂ E.subtype x).val) := by
        rw [eval_rvMap, MultivariateSyntax.realizes p E hp (ts 0) (harg 0) x]
      by_cases hq : q = 0
      · filter_upwards [] with x
        rw [hterm x, hterm a, hq]
        simp
      · have hqa : q.eval₂ E.subtype a ≠ 0 := by
          intro hz
          exact hq (ha.eq_zero_of_aeval_eq_zero q hz)
        have hnear := multivariate_rv_locally_constant hv (q.map E.subtype) a
          (by simpa only [MvPolynomial.eval_map] using hqa)
        filter_upwards [hnear] with x hx
        rw [hterm x, hterm a]
        simpa only [MvPolynomial.eval_map] using hx

theorem qf_local (p : Parameters S) (E : Subfield (VFType (M := M)))
    (hp : ∀ i (h : iVF (p.values i)), (⟨p.values i, h⟩ : VFType (M := M)) ∈ E)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (a : Fin n → VFType (M := M)) (ha : AlgebraicIndependent E a)
    (φ : LRV.BoundedFormula (Fin p.length) n) (hqf : φ.IsQF)
    (hws : WellSorted p.sorts (fun _ => .vf) φ) :
    {x | φ.Realize p.values (vfValues x) ↔ φ.Realize p.values (vfValues a)} ∈ 𝓝 a := by
  induction hqf with
  | falsum => exact Filter.Eventually.of_forall (fun _ => Iff.rfl)
  | of_isAtomic hatom =>
    cases hatom with
    | equal t u =>
      cases hws with
      | @equal _ _ _ _ σ ht hu =>
        cases σ with
        | rv =>
          filter_upwards [rvTerm_local p E hp hv a ha t ht,
            rvTerm_local p E hp hv a ha u hu] with x hx hy
          change t.realize _ = u.realize _ ↔ t.realize _ = u.realize _
          rw [hx, hy]
        | vf =>
          let D := MultivariateSyntax.toPolynomial p E hp t - MultivariateSyntax.toPolynomial p E hp u
          have hD (x : Fin n → VFType (M := M)) :
              (t.bdEqual u).Realize p.values (vfValues x) ↔ D.eval₂ E.subtype x = 0 := by
            change t.realize _ = u.realize _ ↔ _
            rw [MultivariateSyntax.realizes p E hp t ht x, MultivariateSyntax.realizes p E hp u hu x]
            exact Subtype.val_inj.trans (by simp only [D, MvPolynomial.eval₂_sub, sub_eq_zero])
          by_cases hD0 : D = 0
          · filter_upwards [] with x
            rw [hD x, hD a, hD0]
            simp
          · have hDa : D.eval₂ E.subtype a ≠ 0 :=
              fun h => hD0 (ha.eq_zero_of_aeval_eq_zero D h)
            have hval : Valued.v (D.eval₂ E.subtype a) ≠ 0 := Valued.v.ne_zero_iff.mpr hDa
            have hnear : {x : Fin n → VFType (M := M) |
                Valued.v (D.eval₂ E.subtype x) = Valued.v (D.eval₂ E.subtype a)} ∈ 𝓝 a := by
              have hval' : Valued.v ((D.map E.subtype).eval a) ≠ 0 := by
                simpa only [MvPolynomial.eval_map] using hval
              have h := (D.map E.subtype).continuous_eval.continuousAt.preimage_mem_nhds
                (Valued.locally_const hval')
              change {x : Fin n → VFType (M := M) |
                Valued.v ((D.map E.subtype).eval x) =
                  Valued.v ((D.map E.subtype).eval a)} ∈ 𝓝 a at h
              simpa only [MvPolynomial.eval_map] using h
            filter_upwards [hnear] with x hx
            have hDx : D.eval₂ E.subtype x ≠ 0 := by
              intro hz
              rw [hz, map_zero] at hx
              exact hval hx.symm
            exact (hD x).trans ((iff_of_false hDx hDa).trans (hD a).symm)
    | rel R ts =>
      cases hws with
      | rel _ _ _ hts =>
        have hrel {k : ℕ} (R : Rel k) (ts : Fin k → LRV.Term (Fin p.length ⊕ Fin n))
            (h : ∀ i, {x | (ts i).realize (Sum.elim p.values (vfValues x)) =
              (ts i).realize (Sum.elim p.values (vfValues a))} ∈ 𝓝 a) :
            {x | (BoundedFormula.rel R ts).Realize p.values (vfValues x) ↔
              (BoundedFormula.rel R ts).Realize p.values (vfValues a)} ∈ 𝓝 a := by
          filter_upwards [(Filter.eventually_all).mpr h] with x hx
          change Structure.RelMap (L := LRV) R _ ↔ Structure.RelMap (L := LRV) R _
          have he : (fun i => (ts i).realize (Sum.elim p.values (vfValues x))) =
              (fun i => (ts i).realize (Sum.elim p.values (vfValues a))) := funext hx
          rw [he]
        cases R with
        | memUnits => exact hrel _ _ (fun i => rvTerm_local p E hp hv a ha (ts i) (hts i))
        | rvLe => exact hrel _ _ (fun i => rvTerm_local p E hp hv a ha (ts i) (hts i))
        | memVF =>
          have htrue (x : Fin n → VFType (M := M)) :
              (BoundedFormula.rel Rel.memVF ts).Realize p.values (vfValues x) := by
            have hs := CanonicalStructure.term_sort hM p.sorts (fun _ => .vf)
              p.values (vfValues x) p.sorted (fun i => (x i).property) (ts 0) (hts 0)
            change Structure.RelMap (L := LRV) Rel.memVF (fun i => (ts i).realize _)
            have he : (fun i => (ts i).realize (Sum.elim p.values (vfValues x))) =
                (![(ts 0).realize (Sum.elim p.values (vfValues x))] : Fin 1 → M) := by
              funext i
              fin_cases i
              rfl
            rw [he]
            exact hs
          exact Filter.Eventually.of_forall (fun x => iff_of_true (htrue x) (htrue a))
        | memRV =>
          have htrue (x : Fin n → VFType (M := M)) :
              (BoundedFormula.rel Rel.memRV ts).Realize p.values (vfValues x) := by
            have hs := CanonicalStructure.term_sort hM p.sorts (fun _ => .vf)
              p.values (vfValues x) p.sorted (fun i => (x i).property) (ts 0) (hts 0)
            change Structure.RelMap (L := LRV) Rel.memRV (fun i => (ts i).realize _)
            have he : (fun i => (ts i).realize (Sum.elim p.values (vfValues x))) =
                (![(ts 0).realize (Sum.elim p.values (vfValues x))] : Fin 1 → M) := by
              funext i
              fin_cases i
              rfl
            rw [he]
            exact hs
          exact Filter.Eventually.of_forall (fun x => iff_of_true (htrue x) (htrue a))
  | @imp φ ψ hφ hψ ihφ ihψ =>
    cases hws with
    | imp _ hwφ hwψ =>
      filter_upwards [ihφ hwφ, ihψ hwψ] with x hx hy
      exact imp_congr hx hy

end MultivariateLocal

end SpecialTransformations.Section4
