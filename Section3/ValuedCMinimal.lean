module

public import ACVFQE
public import JohnsonValuedBridge

@[expose] public section

set_option linter.style.haveILetI false

open FirstOrder FirstOrder.Language
namespace SpecialTransformations.Section3

theorem c_minimal_valued_language {K : Type} [Field K] [IsAlgClosed K]
    {Γ : Type} [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ)
    (hnt : ∃ x : K, x ≠ 0 ∧ v x ≠ 1)
    (φ : Language.val.BoundedFormula K 1) :
    ValOneEC.Good (RingHom.id K) v {x : K | ValOneEC.Holds v (RingHom.id K) φ x} := by
  classical
  letI := FirstOrder.valStructure v
  haveI : K ⊨ ValPM.ACVF_val := JohnsonValuedBridge.model_ACVF_val v hnt
  obtain ⟨ψ, hqf, heq⟩ := hasQEb_ACVF_val K 1 φ
  have hgood := ValOneEC.good_solSet
    (f := RingHom.id K) (w := v) ValOneEC.atomGood_of_isAlgClosed ψ hqf
  have hset : {x : K | ValOneEC.Holds v (RingHom.id K) φ x} =
      {x : K | ValOneEC.Holds v (RingHom.id K) ψ x} := by
    ext x
    exact Theory.Iff.realize_bd_iff heq
  rw [hset]
  exact hgood

theorem c_minimal_valued_definable {K : Type} [Field K] [IsAlgClosed K]
    {Γ : Type} [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ)
    (hnt : ∃ x : K, x ≠ 0 ∧ v x ≠ 1) (A : Set K) (s : Set K)
    (hdef : @Set.Definable₁ K A Language.val (FirstOrder.valStructure v) s) :
    ValOneEC.Good (RingHom.id K) v s := by
  classical
  letI := FirstOrder.valStructure v
  obtain ⟨φ, hφ⟩ := Set.definable_iff_exists_formula_sum.mp hdef
  let ψ : Language.val.BoundedFormula K 1 :=
    BoundedFormula.relabel (Sum.elim (fun a : A => Sum.inl (a : K)) Sum.inr) φ
  have heval (x : K) : ValOneEC.Holds v (RingHom.id K) ψ x ↔ x ∈ s := by
    change ψ.Realize id (fun _ => x) ↔ x ∈ s
    dsimp only [ψ]
    rw [BoundedFormula.realize_relabel]
    have hxs : ((fun _ : Fin 1 => x) ∘ Fin.natAdd 1 : Fin 0 → K) = Fin.elim0 := by
      funext i; exact i.elim0
    rw [hxs]
    have hv : (Sum.elim id ((fun _ : Fin 1 => x) ∘ Fin.castAdd 0) ∘
        Sum.elim (fun a : A => Sum.inl (a : K)) Sum.inr) =
        Sum.elim (fun a : A => (a : K)) (fun _ => x) := by
      funext a; cases a <;> rfl
    rw [hv]
    change φ.Realize (Sum.elim (fun a : A => (a : K)) (fun _ => x)) ↔ x ∈ s
    have hmem := congrArg (fun t : Set (Fin 1 → K) => (fun _ => x) ∈ t) hφ
    exact (Iff.of_eq hmem).symm
  have hgood := c_minimal_valued_language v hnt ψ
  have hset : {x | ValOneEC.Holds v (RingHom.id K) ψ x} = s := by
    ext x; exact heval x
  rwa [hset] at hgood


end SpecialTransformations.Section3