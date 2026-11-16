module

public import Section3.QFInterpretation
public import Section3.GeometryBridge
public import VFAlgClosed
public import ValuedFieldExtension

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem theorem_2_8_c_minimal : IsCMinimalWS M := by
  intro α sα φ hφ p hp
  obtain ⟨Γ, hΓ, v, hv⟩ := VFValued.exists_valuation_predV (M := M)
  letI := hΓ
  letI := FirstOrder.valStructure v
  letI : IsAlgClosed (VFType (M := M)) := VFAlgClosed.isAlgClosed_vfType
  obtain ⟨ψ, hq, hw, heq⟩ := theorem_2_3_quantifier_elimination α sα 1
    (fun _ => .vf) φ hφ
  have hlift (i : α) : ∃ a : VFType (M := M), RVRepresentatives.decode (sα i) a = p i := by
    cases hi : sα i with
    | vf =>
      have hpi : iVF (p i) := by simpa only [hi, sortEval, iVF] using hp i
      exact ⟨⟨p i, hpi⟩, rfl⟩
    | rv =>
      have hpi : iRV (p i) := by simpa only [hi, sortEval, iRV] using hp i
      obtain ⟨a, ha⟩ := CanonicalRV.encodedRv_surjective (⟨p i, hpi⟩ : CanonicalRV.RVSort M)
      exact ⟨a, congrArg Subtype.val ha⟩
  choose q hqrep using hlift
  have hpq : (fun i => RVRepresentatives.decode (sα i) (q i)) = p := funext hqrep
  have hd := RVRepresentatives.qf_definable v hv sα (fun _ : Fin 1 => .vf)
    (fun _ : Fin 1 → VFType (M := M) => q) (fun z => z)
    (fun i => ValuedDefinability.constant v (q i))
    (fun i => Set.DefinableFun.proj Language.val) ψ hq hw
  rw [hpq] at hd
  let D : Set (VFType (M := M)) := {a | ψ.Realize p ![a.val]}
  have hD : (Set.univ : Set (VFType (M := M))).Definable₁ Language.val D := by
    change (Set.univ : Set (VFType (M := M))).Definable Language.val _
    convert hd using 1
    ext z
    change ψ.Realize p ![(z 0).val] ↔ ψ.Realize p (fun i => (z i).val)
    have hz : (![(z 0).val] : Fin 1 → M) = fun i => (z i).val := by
      funext i; fin_cases i; rfl
    rw [hz]
  obtain ⟨ε, hε0, hε⟩ := ValuedFieldExtension.exists_nontrivial_predV (M := M)
  have hnt : ∃ a : VFType (M := M), a ≠ 0 ∧ v a ≠ 1 := by
    refine ⟨ε, hε0, ?_⟩
    intro he
    apply hε
    exact (hv 1 ε).mpr (by rw [map_one, he])
  have hg := c_minimal_valued_definable v hnt Set.univ D hD
  have hb := good_vfImage v hv D hg
  have hset : vfImage D = {x : M | iVF x ∧ φ.Realize p ![x]} := by
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine ⟨a.property, ?_⟩
      exact (heq M hM p ![a.val] hp (by intro i; fin_cases i; exact a.property)).mpr ha
    · rintro ⟨hx, hφx⟩
      refine ⟨⟨x, hx⟩, ?_, rfl⟩
      exact (heq M hM p ![x] hp (by intro i; fin_cases i; exact hx)).mp hφx
  rw [hset] at hb
  exact hb

end SpecialTransformations.Section3