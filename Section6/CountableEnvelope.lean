import Section6.ElementaryAmalgam
import ACVFQE
import CountableSaturatedExtension
import CanonicalCountable

/-! Amalgamate the ordinary envelopes first, then use the checked
countable saturation theorem. The earlier preparation is over a finitely
generated base, so its small-parameter bound suffices. -/

noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Section6.NativeAmalgamation

theorem common_countable_envelope
    {M N I : Type} [sM : LRV.Structure M] [sN : LRV.Structure N]
    (hM : M ⊨ Axioms.ACVF00) (hN : N ⊨ Axioms.ACVF00)
    (hcM : CanonicalStructure.IsCanonical (M := M))
    (hcN : CanonicalStructure.IsCanonical (M := N))
    (a : I → M) (b : I → N)
    (hQF : ∀ φ : LRV.Formula I, φ.IsQF → (φ.Realize a ↔ φ.Realize b)) :
    ∃ (C : Type) (sC : LRV.Structure C),
      @Theory.Model LRV C sC Axioms.ACVF00 ∧
      @CanonicalStructure.IsCanonical C sC ∧
      @MarkerBridge.SatAt LRV C sC (Order.succ Cardinal.aleph0) ∧
      ∃ (j : @ElementaryEmbedding LRV M C sM sC)
        (k : @ElementaryEmbedding LRV N C sN sC), j ∘ a = k ∘ b := by
  letI : Nonempty N := ⟨iRVZero⟩
  have hMA : M ⊨ Axioms.ACVF := hM.mono (by intro σ hσ; exact Or.inl (Or.inl hσ))
  have hNA : N ⊨ Axioms.ACVF := hN.mono (by intro σ hσ; exact Or.inl (Or.inl hσ))
  have hMC : M ⊨ CanonicalTheory.CanonicalACVF :=
    CanonicalTheory.model_CanonicalACVF_iff.mpr ⟨hMA, hcM⟩
  have hNC : N ⊨ CanonicalTheory.CanonicalACVF :=
    CanonicalTheory.model_CanonicalACVF_iff.mpr ⟨hNA, hcN⟩
  have ht (φ : LRV.Formula I) : φ.Realize a ↔ φ.Realize b := by
    obtain ⟨ψ, hψ, he⟩ := LocalAssembly.fullQE I 0 φ
    exact (he M hMC a default).trans ((hQF ψ hψ).trans (he N hNC b default).symm)
  obtain ⟨P, sP, f, g, hfg⟩ := elementary_amalgam a b ht
  letI := sP
  letI : Nonempty P := ⟨g iRVZero⟩
  obtain ⟨C, sC, hsat, ⟨i⟩⟩ := CountableSaturatedExtension.exists_saturated_elementary_extension LRV P
  letI := sC
  let k := i.comp g
  have h00 := (k.theory_model_iff Axioms.ACVF00).mp hN
  have hC := (k.theory_model_iff CanonicalTheory.CanonicalACVF).mp hNC
  refine ⟨C, sC, h00, CanonicalTheory.canonical_of_model hC, hsat, i.comp f, k, ?_⟩
  exact congrArg (fun u => i ∘ u) hfg

end SpecialTransformations.Section6.NativeAmalgamation
