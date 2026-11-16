module

public import Section3.RVTermLocal
public import CanonicalStructure

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {A : Set M}
variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ] [Valued (VFType (M := M)) Γ]

theorem qf_local (p : Parameters A) (E : Subfield (VFType (M := M)))
    (hp : ∀ i (h : iVF (p.values i)), (⟨p.values i, h⟩ : VFType (M := M)) ∈ E)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (a : VFType (M := M)) (ha : Transcendental E a)
    (φ : LRV.BoundedFormula (Fin p.length) 1) (hqf : φ.IsQF)
    (hws : WellSorted p.sorts (fun _ => .vf) φ) :
    {x : VFType (M := M) | φ.Realize p.values ![x.val] ↔ φ.Realize p.values ![a.val]} ∈ 𝓝 a := by
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
          let D := PolynomialSyntax.toPolynomial p E hp t - PolynomialSyntax.toPolynomial p E hp u
          have hD (x : VFType (M := M)) : (t.bdEqual u).Realize p.values ![x.val] ↔
              D.eval₂ E.subtype x = 0 := by
            change t.realize _ = u.realize _ ↔ _
            rw [PolynomialSyntax.realizes p E hp t ht x, PolynomialSyntax.realizes p E hp u hu x]
            exact Subtype.val_inj.trans (by simp only [D, Polynomial.eval₂_sub, sub_eq_zero])
          by_cases hD0 : D = 0
          · filter_upwards [] with x
            rw [hD x, hD a, hD0]
            simp
          · have hDa : D.eval₂ E.subtype a ≠ 0 := fun h => ha ⟨D, hD0, h⟩
            have hval : Valued.v (D.eval₂ E.subtype a) ≠ 0 := (Valued.v.ne_zero_iff).mpr hDa
            have hnear := (D.continuous_eval₂ E.subtype).continuousAt.preimage_mem_nhds
              (Valued.locally_const hval)
            filter_upwards [hnear] with x hx
            have hDx : D.eval₂ E.subtype x ≠ 0 := by
              intro hzero
              have hvx : Valued.v (D.eval₂ E.subtype x) = Valued.v (D.eval₂ E.subtype a) := hx
              rw [hzero, map_zero] at hvx
              exact hval hvx.symm
            exact (hD x).trans ((iff_of_false hDx hDa).trans (hD a).symm)
    | rel R ts =>
      cases hws with
      | rel _ _ _ hts =>
        have hrel {k : ℕ} (R : Rel k) (ts : Fin k → LRV.Term (Fin p.length ⊕ Fin 1))
            (h : ∀ i, {x : VFType (M := M) | (ts i).realize (Sum.elim p.values ![x.val]) =
              (ts i).realize (Sum.elim p.values ![a.val])} ∈ 𝓝 a) :
            {x : VFType (M := M) | (BoundedFormula.rel R ts).Realize p.values ![x.val] ↔
              (BoundedFormula.rel R ts).Realize p.values ![a.val]} ∈ 𝓝 a := by
          filter_upwards [(Filter.eventually_all).mpr h] with x hx
          change Structure.RelMap (L := LRV) R _ ↔ Structure.RelMap (L := LRV) R _
          have he : (fun i => (ts i).realize (Sum.elim p.values ![x.val])) =
              (fun i => (ts i).realize (Sum.elim p.values ![a.val])) := funext hx
          rw [he]
        cases R with
        | memUnits => exact hrel _ _ (fun i => rvTerm_local p E hp hv a ha (ts i) (hts i))
        | rvLe => exact hrel _ _ (fun i => rvTerm_local p E hp hv a ha (ts i) (hts i))
        | memVF =>
          have htrue (x : VFType (M := M)) :
              (BoundedFormula.rel Rel.memVF ts).Realize p.values ![x.val] := by
            have hx : ∀ i : Fin 1, sortEval SortTag.vf (![x.val] i) := by
              intro i; fin_cases i; exact x.property
            have hs := CanonicalStructure.term_sort hM p.sorts (fun _ => .vf) p.values ![x.val]
              p.sorted hx (ts 0) (hts 0)
            change Structure.RelMap (L := LRV) Rel.memVF (fun i => (ts i).realize _)
            have he : (fun i => (ts i).realize (Sum.elim p.values ![x.val])) =
                (![(ts 0).realize (Sum.elim p.values ![x.val])] : Fin 1 → M) := by
              funext i; fin_cases i; rfl
            rw [he]; exact hs
          exact Filter.Eventually.of_forall (fun x => iff_of_true (htrue x) (htrue a))
        | memRV =>
          have htrue (x : VFType (M := M)) :
              (BoundedFormula.rel Rel.memRV ts).Realize p.values ![x.val] := by
            have hx : ∀ i : Fin 1, sortEval SortTag.vf (![x.val] i) := by
              intro i; fin_cases i; exact x.property
            have hs := CanonicalStructure.term_sort hM p.sorts (fun _ => .vf) p.values ![x.val]
              p.sorted hx (ts 0) (hts 0)
            change Structure.RelMap (L := LRV) Rel.memRV (fun i => (ts i).realize _)
            have he : (fun i => (ts i).realize (Sum.elim p.values ![x.val])) =
                (![(ts 0).realize (Sum.elim p.values ![x.val])] : Fin 1 → M) := by
              funext i; fin_cases i; rfl
            rw [he]; exact hs
          exact Filter.Eventually.of_forall (fun x => iff_of_true (htrue x) (htrue a))
  | @imp φ ψ hφ hψ ihφ ihψ =>
    cases hws with
    | imp _ hwφ hwψ =>
      filter_upwards [ihφ hwφ, ihψ hwψ] with x hx hy
      exact imp_congr hx hy

end SpecialTransformations.Section3
