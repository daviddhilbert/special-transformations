module

public import Section8.MixedLocalTerms
public import Section8.RVFibreLocus

@[expose] public section

/-! Released QE gives local constancy of the entire RV fibre near an
algebraically independent VF tuple. The neighbourhood is uniform in
the RV coordinates because VF subterms omit them. -/

set_option backward.isDefEq.respectTransparency false

open Filter Topology FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace SpecialTransformations.Section8.MixedLocal

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n m : ℕ}
variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ] [Valued (VFType (M := M)) Γ]

theorem qf_uniform_local {S : Set M} (p : Parameters S) (E : Subfield (VFType (M := M)))
    (hp : ∀ i (h : iVF (p.values i)), (⟨p.values i, h⟩ : VFType (M := M)) ∈ E)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (a : Fin n → VFType (M := M)) (ha : AlgebraicIndependent E a)
    (φ : LRV.BoundedFormula (Fin p.length) (n + m)) (hqf : φ.IsQF)
    (hws : WellSorted p.sorts (tupleSort n m) φ) :
    ∀ᶠ x in 𝓝 a, ∀ b : Fin m → CanonicalRV.RVSort M,
      φ.Realize p.values (tupleCode x b) ↔ φ.Realize p.values (tupleCode a b) := by
  induction hqf with
  | falsum => exact Filter.Eventually.of_forall (fun _ _ => Iff.rfl)
  | of_isAtomic hatom =>
    cases hatom with
    | equal t u =>
      cases hws with
      | @equal _ _ _ _ σ ht hu =>
        cases σ with
        | rv =>
          filter_upwards [rvTerm_uniform_local p E hp hv a ha t ht,
            rvTerm_uniform_local p E hp hv a ha u hu] with x hx hy b
          change t.realize _ = u.realize _ ↔ t.realize _ = u.realize _
          rw [hx b, hy b]
        | vf =>
          let φ' : LRV.BoundedFormula (Fin p.length) n := (restrictVF t).bdEqual (restrictVF u)
          have ht' := restrictVF_spec p.sorts p.values t ht
          have hu' := restrictVF_spec p.sorts p.values u hu
          have hq' : φ'.IsQF := .of_isAtomic (.equal _ _)
          have hs' : WellSorted p.sorts (fun _ => .vf) φ' := .equal _ ht'.1 hu'.1
          have he (x : Fin n → VFType (M := M)) (b : Fin m → CanonicalRV.RVSort M) :
              (t.bdEqual u).Realize p.values (tupleCode x b) ↔ φ'.Realize p.values (vfValues x) := by
            change t.realize _ = u.realize _ ↔ (restrictVF t).realize _ = (restrictVF u).realize _
            rw [ht'.2 x b, hu'.2 x b]
          filter_upwards [MultivariateLocal.qf_local p E hp hv a ha φ' hq' hs'] with x hx b
          exact (he x b).trans (hx.trans (he a b).symm)
    | rel R ts =>
      cases hws with
      | rel _ _ _ hts =>
        have hrel {l : ℕ} (r : Rel l) (us : Fin l → LRV.Term (Fin p.length ⊕ Fin (n + m)))
            (hs : ∀ i, TmSort p.sorts (tupleSort n m) (us i) = some .rv) :
            ∀ᶠ x in 𝓝 a, ∀ b : Fin m → CanonicalRV.RVSort M,
              (BoundedFormula.rel r us).Realize p.values (tupleCode x b) ↔
                (BoundedFormula.rel r us).Realize p.values (tupleCode a b) := by
          filter_upwards [Filter.eventually_all.mpr (fun i =>
            rvTerm_uniform_local p E hp hv a ha (us i) (hs i))] with x hx b
          change Structure.RelMap (L := LRV) r _ ↔ Structure.RelMap (L := LRV) r _
          have he : (fun i => (us i).realize (Sum.elim p.values (tupleCode x b))) =
              (fun i => (us i).realize (Sum.elim p.values (tupleCode a b))) := funext (fun i => hx i b)
          rw [he]
        cases R with
        | memUnits => exact hrel _ _ hts
        | rvLe => exact hrel _ _ hts
        | memVF =>
          have ht (x : Fin n → VFType (M := M)) (b : Fin m → CanonicalRV.RVSort M) :
              (BoundedFormula.rel Rel.memVF ts).Realize p.values (tupleCode x b) := by
            have hs := CanonicalStructure.term_sort hM p.sorts (tupleSort n m)
              p.values (tupleCode x b) p.sorted (tupleCode_sorted x b) (ts 0) (hts 0)
            change Structure.RelMap (L := LRV) Rel.memVF (fun i => (ts i).realize _)
            have he : (fun i => (ts i).realize (Sum.elim p.values (tupleCode x b))) =
                (![(ts 0).realize (Sum.elim p.values (tupleCode x b))] : Fin 1 → M) := by
              funext i
              fin_cases i
              rfl
            rw [he]
            exact hs
          exact Filter.Eventually.of_forall (fun x b => iff_of_true (ht x b) (ht a b))
        | memRV =>
          have ht (x : Fin n → VFType (M := M)) (b : Fin m → CanonicalRV.RVSort M) :
              (BoundedFormula.rel Rel.memRV ts).Realize p.values (tupleCode x b) := by
            have hs := CanonicalStructure.term_sort hM p.sorts (tupleSort n m)
              p.values (tupleCode x b) p.sorted (tupleCode_sorted x b) (ts 0) (hts 0)
            change Structure.RelMap (L := LRV) Rel.memRV (fun i => (ts i).realize _)
            have he : (fun i => (ts i).realize (Sum.elim p.values (tupleCode x b))) =
                (![(ts 0).realize (Sum.elim p.values (tupleCode x b))] : Fin 1 → M) := by
              funext i
              fin_cases i
              rfl
            rw [he]
            exact hs
          exact Filter.Eventually.of_forall (fun x b => iff_of_true (ht x b) (ht a b))
  | @imp φ ψ hφ hψ ihφ ihψ =>
    cases hws with
    | imp _ hwφ hwψ =>
      filter_upwards [ihφ hwφ, ihψ hwψ] with x hx hy b
      exact imp_congr (hx b) (hy b)

end SpecialTransformations.Section8.MixedLocal

namespace SpecialTransformations.Section8

open MixedLocal

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n m : ℕ}
variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ] [Valued (VFType (M := M)) Γ]

theorem rvFibre_locallyConstant_of_independent (hc : CanonicalStructure.IsCanonical (M := M))
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {S : Set M} {G : Set (Fin n ⊕ Fin m → M)} (hG : S.Definable LRV G)
    (a : Fin n → VFType (M := M)) (ha : AlgebraicIndependent (vfParameterField S) a) :
    rvLocallyConstantAt (rvFibre G) a := by
  let e : Fin n ⊕ Fin m ≃ Fin (n + m) := finSumFinEquiv
  let X := {z : Fin (n + m) → M | (∀ i, sortEval (tupleSort n m i) (z i)) ∧ z ∘ e ∈ G}
  have hsort : S.Definable LRV {z : Fin (n + m) → M | ∀ i, sortEval (tupleSort n m i) (z i)} := by
    rw [Set.ofPred_forall]
    exact Set.definable_iInter_of_finite (fun i => ((definableAt_sort S (tupleSort n m i)).raw_definable).preimage_comp
      (fun _ : Fin 1 => i))
  have hX := raw_definableOver_sorted hc S (tupleSort n m) X
    (hsort.inter (hG.preimage_comp e)) (fun _ hx => hx.1)
  obtain ⟨p, φ, hqf, hws, he⟩ := hX.quantifier_free hM
  let E := vfParameterField S
  have hp : ∀ i (h : iVF (p.values i)), (⟨p.values i, h⟩ : VFType (M := M)) ∈ E :=
    fun i h => Subfield.subset_closure (p.mem_base i)
  have hf (x : Fin n → VFType (M := M)) (b : Fin m → CanonicalRV.RVSort M) :
      b ∈ rvFibre G x ↔ φ.Realize p.values (tupleCode x b) := by
    have hcode : tupleCode x b ∘ e = Sum.elim (vfValues x) (rvValues b) := by
      funext i
      change Sum.elim (vfValues x) (rvValues b) (e.symm (e i)) = _
      rw [e.symm_apply_apply]
    have h : b ∈ rvFibre G x ↔ tupleCode x b ∈ X := by
      change _ ↔ (∀ i, sortEval (tupleSort n m i) (tupleCode x b i)) ∧ tupleCode x b ∘ e ∈ G
      rw [hcode]
      exact (and_iff_right (tupleCode_sorted x b)).symm
    exact h.trans ((Set.ext_iff.mp he (tupleCode x b)).trans (and_iff_right (tupleCode_sorted x b)))
  rw [rvLocallyConstantAt_iff_nhds]
  filter_upwards [qf_uniform_local p E hp hv a ha φ hqf hws] with x hx
  exact Set.ext (fun b => (hf x b).trans ((hx b).trans (hf a b).symm))

end SpecialTransformations.Section8
