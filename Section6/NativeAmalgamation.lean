import ACVFQE
import Mathlib.ModelTheory.ElementaryMaps

/-! A common native ACVF envelope from the completed QE dependency.
The standard-reference input is generic saturated elementary-extension
existence (Marker, Model Theory: An Introduction, Chapter 4, saturated
models). It uses the released genuine SatAt, not an extension or Yin
lemma as a definition of saturation. The extension and QE steps themselves
are imported checked proofs, not rebuilt. The term-substructure adapter
follows the released CountableQECriterion argument.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Section6.NativeAmalgamation

/-- Authorized generic model-theory quotation. No theory-specific
embedding-extension or quantifier-elimination conclusion occurs here. -/
def SaturatedElementaryExtensionAt : Prop :=
  ∀ (L : _root_.FirstOrder.Language.{0, 0}) (M : Type) [sM : L.Structure M] [Nonempty M] (κ : Cardinal),
    ∃ (N : Type) (sN : L.Structure N),
      @MarkerBridge.SatAt L N sN κ ∧ Nonempty (@ElementaryEmbedding L M N sM sN)

def elementaryEmbedding_of_fullQE {L : _root_.FirstOrder.Language.{0, 0}} {T : L.Theory}
    (hQE : MarkerBridge.FullQE T) {M N : Type} [L.Structure M] [L.Structure N]
    (hM : M ⊨ T) (hN : N ⊨ T) (g : M ↪[L] N) : M ↪ₑ[L] N where
  toFun := g
  map_formula' := by
    intro n φ x
    obtain ⟨ψ, hψ, he⟩ := hQE (Fin n) 0 φ
    exact (he N hN (g ∘ x) default).trans
      ((QESaturatedExtension.embedding_realize_formula_isQF g hψ x).trans
        (he M hM x default).symm)

theorem common_envelope (hMarker : SaturatedElementaryExtensionAt)
    {M N I : Type} [sM : LRV.Structure M] [sN : LRV.Structure N]
    (κ : Cardinal) (hκ : Order.succ (Cardinal.mk M) ≤ κ)
    (hM : M ⊨ Axioms.ACVF00) (hN : N ⊨ Axioms.ACVF00)
    (hcM : CanonicalStructure.IsCanonical (M := M))
    (hcN : CanonicalStructure.IsCanonical (M := N))
    (a : I → M) (b : I → N)
    (hQF : ∀ φ : LRV.Formula I, φ.IsQF → (φ.Realize a ↔ φ.Realize b)) :
    ∃ (C : Type) (sC : LRV.Structure C),
      @Theory.Model LRV C sC Axioms.ACVF00 ∧
      @CanonicalStructure.IsCanonical C sC ∧
      @MarkerBridge.SatAt LRV C sC κ ∧
      ∃ (j : @ElementaryEmbedding LRV M C sM sC)
        (k : @ElementaryEmbedding LRV N C sN sC), j ∘ a = k ∘ b := by
  letI : Nonempty N := ⟨iRVZero⟩
  have hMA : M ⊨ Axioms.ACVF := hM.mono (by intro σ hσ; exact Or.inl (Or.inl hσ))
  have hNA : N ⊨ Axioms.ACVF := hN.mono (by intro σ hσ; exact Or.inl (Or.inl hσ))
  have hMC : M ⊨ CanonicalTheory.CanonicalACVF :=
    CanonicalTheory.model_CanonicalACVF_iff.mpr ⟨hMA, hcM⟩
  have hNC : N ⊨ CanonicalTheory.CanonicalACVF :=
    CanonicalTheory.model_CanonicalACVF_iff.mpr ⟨hNA, hcN⟩
  obtain ⟨C, sC, hsat, ⟨k⟩⟩ := hMarker LRV N κ
  letI := sC
  have hC : C ⊨ Axioms.ACVF00 := (k.theory_model_iff _).mp hN
  have hCC : C ⊨ CanonicalTheory.CanonicalACVF := (k.theory_model_iff _).mp hNC
  have hker : ∀ t u : LRV.Term I, t.realize a = u.realize a ↔ t.realize b = u.realize b := by
    intro t u
    simpa only [Formula.realize_equal] using
      hQF (t.equal u) (BoundedFormula.IsAtomic.equal _ _ |>.isQF)
  have hrel : ∀ {k : ℕ} (r : LRV.Relations k) (ts : Fin k → LRV.Term I),
      Structure.RelMap r (fun i => (ts i).realize a) ↔
        Structure.RelMap r (fun i => (ts i).realize b) := by
    intro k r ts
    simpa only [Relations.formula, Relations.boundedFormula, Formula.Realize,
      BoundedFormula.Realize, Term.realize_relabel, Sum.elim_comp_inl] using
      hQF (r.formula ts) (BoundedFormula.IsAtomic.rel _ _ |>.isQF)
  let S := HQEDerive.termSub (L := LRV) a
  let e : S ↪[LRV] N := HQEDerive.termSubEmb a b hker hrel
  let f : S ↪[LRV] C := k.toEmbedding.comp e
  have hsatM : MarkerBridge.SatAt LRV C (Order.succ (Cardinal.mk M)) := by
    intro A u hA p hp
    exact hsat A u (hA.trans_le hκ) p hp
  obtain ⟨g, hg⟩ := QESaturatedExtension.extension_of_fullQE LocalAssembly.fullQE
    M C hMC hCC hsatM S f
  let j := elementaryEmbedding_of_fullQE LocalAssembly.fullQE hMC hCC g
  refine ⟨C, sC, hC, CanonicalTheory.canonical_of_model hCC, hsat, j, k, ?_⟩
  funext i
  calc
    j (a i) = f (HQEDerive.termSubMk a i) := by
      change g (a i) = f (HQEDerive.termSubMk a i)
      simpa only [HQEDerive.termSubMk_val] using hg (HQEDerive.termSubMk (L := LRV) a i)
    _ = k (b i) := by
      change k (HQEDerive.termSubEmb a b hker hrel (HQEDerive.termSubMk a i)) = _
      rw [HQEDerive.termSubEmb_apply_var]

end SpecialTransformations.Section6.NativeAmalgamation
