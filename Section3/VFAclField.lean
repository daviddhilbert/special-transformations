module

public import ACVFQE
public import Section3.QFLocal
public import Section3.ValuedNeighbourhood
public import ValuedFieldExtension

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem algebraicAt_vf_isAlgebraic (A : Set M) (E : Subfield (VFType (M := M)))
    (hE : ∀ x : VFType (M := M), x.val ∈ A → x ∈ E)
    (b : VFType (M := M)) (hb : AlgebraicAt A .vf b.val) : IsAlgebraic E b := by
  classical
  by_contra htrans
  obtain ⟨s, ⟨⟨p, φ, hφ, hs⟩, hsub⟩, hf, hb⟩ := hb
  have hφb : φ.Realize p.values ![b.val] := by
    have hmem : ![b.val] ∈ {x : Fin 1 → M | x 0 ∈ s} := hb
    rw [hs] at hmem
    exact hmem.2
  have hp (i : Fin p.length) (h : iVF (p.values i)) :
      (⟨p.values i, h⟩ : VFType (M := M)) ∈ E := hE _ (p.mem_base i)
  obtain ⟨ψ, hq, hw, heq⟩ := theorem_2_3_quantifier_elimination
    (Fin p.length) p.sorts 1 (fun _ => .vf) φ hφ
  have hsort (x : VFType (M := M)) : ∀ i : Fin 1, sortEval SortTag.vf (![x.val] i) := by
    intro i; fin_cases i; exact x.property
  have hψb := (heq M hM p.values ![b.val] p.sorted (hsort b)).mp hφb
  let T : Set (VFType (M := M)) := {x | ψ.Realize p.values ![x.val]}
  have hT : T.Finite := by
    have hpre := hf.preimage (Subtype.val_injective.injOn : Set.InjOn
      (Subtype.val : VFType (M := M) → M) (Subtype.val ⁻¹' s))
    apply hpre.subset
    intro x hx
    have hφx := (heq M hM p.values ![x.val] p.sorted (hsort x)).mpr hx
    have hmem : ![x.val] ∈ {y | (∀ i, sortEval SortTag.vf (y i)) ∧ φ.Realize p.values y} :=
      ⟨hsort x, hφx⟩
    rw [← hs] at hmem
    exact hmem
  obtain ⟨Γ, hΓ, v, hv⟩ := VFValued.exists_valuation_predV (M := M)
  letI := hΓ
  letI : Valued (VFType (M := M)) Γ := Valued.mk' v
  have hlocal := qf_local p E hp hv b htrans ψ hq hw
  have hTnhds : T ∈ 𝓝 b :=
    Filter.mem_of_superset hlocal (fun x hx => hx.mpr hψb)
  obtain ⟨ε, hε0, hε⟩ := ValuedFieldExtension.exists_nontrivial_predV (M := M)
  have hnt : ∃ ε : VFType (M := M), ε ≠ 0 ∧ Valued.v ε < 1 := by
    refine ⟨ε, hε0, ?_⟩
    change v ε < 1
    rw [← v.map_one]
    exact lt_of_not_ge (fun hge => hε ((hv 1 ε).mpr hge))
  exact infinite_valued_neighbourhood hnt b hTnhds hT

noncomputable def vfParameterField (A : Set M) : Subfield (VFType (M := M)) :=
  Subfield.closure {x : VFType (M := M) | x.val ∈ A}

theorem algebraicAt_vf_parameterField (A : Set M) (b : VFType (M := M))
    (hb : AlgebraicAt A .vf b.val) : IsAlgebraic (vfParameterField A) b :=
  algebraicAt_vf_isAlgebraic A (vfParameterField A)
    (fun x hx => Subfield.subset_closure hx) b hb

end SpecialTransformations.Section3