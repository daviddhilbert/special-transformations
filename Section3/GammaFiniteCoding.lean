module

public import Section3.FiniteVFRealCover
public import Section3.GammaRealRestriction

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.GammaParameters
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- Lemma3.9 for genuine Gamma-named bases. A finite cover over the real
base permits reuse of the checked coding theorem, and restriction preserves
the complete graph over the original imaginary-parameter base. -/
theorem lemma_3_9_gamma_base (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M)) {n : ℕ}
    (A : Set (Fin n → VFType (M := M))) (hfin : A.Finite)
    (hA : DefinableOverBase B (fun _ => .vf) (FiniteCoding.values '' A)) :
    ∃ m : ℕ, ∃ f : A → Fin m → M, Function.Injective f ∧
      (∀ a j, iRV (f a j)) ∧
      DefinableOverBase B FiniteCoding.graphSort (FiniteCoding.graph A f) := by
  obtain ⟨C,hCf,hAC,hCd⟩ := finite_vf_tuple_cover_gamma_base B A hfin hA
  obtain ⟨m,g,hg,hs,hG⟩ := SpecialTransformations.Section3.lemma_3_9 h00 B.real C hCf hCd
  let f (a : A) := g ⟨a.val,hAC a.property⟩
  have hf : Function.Injective f := by
    intro a b he
    apply Subtype.ext
    exact congrArg (fun c : C => c.val) (hg he)
  have hsort : ∀ a j, iRV (f a j) := fun a j => hs ⟨a.val,hAC a.property⟩ j
  have he : FiniteCoding.graph A f =
      {z | z ∘ finSumFinEquiv ∘ Sum.inl ∈ FiniteCoding.values '' A ∧ z ∈ FiniteCoding.graph C g} := by
    ext z
    constructor
    · rintro ⟨a,hx,hy⟩
      exact ⟨⟨a.val,a.property,hx⟩,⟨⟨a.val,hAC a.property⟩,hx,hy⟩⟩
    · rintro ⟨⟨a,ha,hax⟩,c,hcx,hcy⟩
      have hca : c.val = a := FiniteCoding.values_injective (hcx.trans hax.symm)
      have hcs : c = (⟨a,hAC ha⟩ : C) := Subtype.ext hca
      refine ⟨⟨a,ha⟩,hax,?_⟩
      change g ⟨a,hAC ha⟩ = _
      rw [← hcs]
      exact hcy
  refine ⟨m,f,hf,hsort,?_⟩
  rw [he]
  exact hA.inter_real_preimage FiniteCoding.graphSort (FiniteCoding.graph C g) hG
    (fun i => finSumFinEquiv (Sum.inl i))

end SpecialTransformations.Section3.GammaParameters
