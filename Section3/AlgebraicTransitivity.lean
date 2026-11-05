import Section3.FiniteImage
import Section3.TupleRelations
import Section3.CanonicalParameters
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3
variable {M : Type} [sM : LRV.Structure M]

theorem RawClosure.eliminate_algebraic_parameters (S B : Set M)
    (hB : ∀ b ∈ B, RawClosure.AlgebraicOver S b) (x : M)
    (hx : RawClosure.AlgebraicOver B x) : RawClosure.AlgebraicOver S x := by
  classical
  obtain ⟨T, hT, hTf, hxT⟩ := hx
  obtain ⟨C, hCB, hC⟩ := Set.definable_iff_finitely_definable.mp hT
  let e : ↥C ≃ Fin C.card := Finset.equivFin C
  let a (i : Fin C.card) : M := (e.symm i).val
  have hCa : (C : Set M) ⊆ S ∪ Set.range a := by
    intro c hc
    exact Or.inr ⟨e ⟨c, hc⟩, by simp [a]⟩
  have hx' : RawClosure.AlgebraicOver (S ∪ Set.range a) x :=
    ⟨T, hC.mono hCa, hTf, hxT⟩
  obtain ⟨R, haR⟩ := RawClosure.Tuple.good_relation_of_algebraic S a x hx'
  have hAi (i : Fin C.card) : RawClosure.AlgebraicOver S (a i) :=
    hB (a i) (hCB (e.symm i).property)
  choose E hEd hEf hEa using hAi
  let Y : Set (Fin C.card → M) := {z | ∀ i, z i ∈ E i}
  have hYd : S.Definable LRV Y := by
    have h := Set.definable_iInter_of_finite
      (fun i => (hEd i).preimage_comp (fun _ : Fin 1 => i))
    convert h using 1
    ext z
    simp only [Y, Set.mem_iInter, Set.mem_preimage, Set.mem_ofPred_eq, Function.comp_apply]
  have hYf : Y.Finite := Set.Finite.pi' hEf
  have haY : a ∈ Y := hEa
  let Q : Set ((Fin C.card → M) × M) := {p | p.1 ∈ Y ∧ p ∈ R.val}
  have hQ : RawClosure.Tuple.RelationDefinable S Q :=
    (hYd.preimage_comp (Sum.inl : Fin C.card → Fin C.card ⊕ Fin 1)).inter R.property.1
  let U : Set M := {b | ∃ z, (z, b) ∈ Q}
  refine ⟨U, relation_image_definable S Q hQ, ?_, a, haY, haR⟩
  haveI : Finite Y := hYf.to_subtype
  have hf : (⋃ z : Y, {b | (z.val, b) ∈ R.val}).Finite :=
    Set.finite_iUnion (fun z : Y => R.property.2 z.val)
  apply hf.subset
  rintro b ⟨z, hzY, hzR⟩
  exact Set.mem_iUnion.mpr ⟨⟨z, hzY⟩, hzR⟩

variable [hM : M ⊨ Axioms.ACVF]

/-- Transitivity of the actual sorted algebraic closure, without saturation
or restrictions on the original totalization or base. -/
theorem AlgebraicAt.eliminate_algebraic_params {S B : Set M} {σ : SortTag} {x : M}
    (hx : AlgebraicAt B σ x) (hB : ∀ b ∈ B, ∃ τ, AlgebraicAt S τ b) :
    AlgebraicAt S σ x := by
  let N := CanonicalStructure.normalize (M := M)
  letI := sM
  have hN : @Theory.Model LRV M N Axioms.ACVF := CanonicalStructure.normalized_model hM
  have hcan : @CanonicalStructure.IsCanonical M N := CanonicalStructure.normalize_isCanonical
  have hBn (b : M) (hb : b ∈ B) : @RawClosure.AlgebraicOver M N S b := by
    obtain ⟨τ, hb'⟩ := hB b hb
    have hn := (algebraicAt_normalize_iff S τ b).mpr hb'
    exact @AlgebraicAt.raw_finite_witness M N S τ b hn
  have hxn := (algebraicAt_normalize_iff B σ x).mpr hx
  have hraw : @RawClosure.AlgebraicOver M N S x :=
    @RawClosure.eliminate_algebraic_parameters M N S B hBn x
      (@AlgebraicAt.raw_finite_witness M N B σ x hxn)
  have hout : @AlgebraicAt M N S σ x :=
    (@algebraicAt_iff_raw M N hN hcan S σ x).mpr
      ⟨hraw, @AlgebraicAt.sorted M N B σ x hxn⟩
  exact (algebraicAt_normalize_iff S σ x).mp hout

end SpecialTransformations.Section3
