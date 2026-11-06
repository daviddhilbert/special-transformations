import Section4.FiniteRefinement
import Section4.RealPresentations
import Section4.FiniteMaps

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

/-!
# Definable injection refining a finite-to-one map

This is the finite-fibre argument of Lemma 4.2 for genuine definable maps.
The target is an arbitrary presented sort, including products with Gamma.
The map is refined by finitely many RV coordinates over the same base.
-/

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3
open SpecialTransformations.DefinableGeometry

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n r : ℕ}

noncomputable def mapToRV (A : DefSet (rawMixedSpace (M := M) n r) S)
    {j : ℕ} (h : A → Fin j → M) (hsort : ∀ a k, iRV (h a k))
    (hdef : S.Definable LRV {w : (Fin n ⊕ Fin r) ⊕ Fin j → M |
      ∃ a : A, mixedValues a.val = w ∘ Sum.inl ∧ h a = w ∘ Sum.inr}) :
    Map A (DefSet.univ (rawRVSpace j) S) where
  toFun a := ⟨fun k => ⟨h a k, hsort a k⟩, Set.mem_univ _⟩
  graph_definable := by
    change S.Definable LRV {w : (Fin n ⊕ Fin r) ⊕ Fin j → M |
      ∃ hx : w ∘ Sum.inl ∈ (rawMixedSpace (M := M) n r).domain,
      ∃ hy : w ∘ Sum.inr ∈ (rawRVSpace (M := M) j).domain,
      ∃ a : A, a.val = (rawMixedSpace (M := M) n r).decode ⟨w ∘ Sum.inl, hx⟩ ∧
        (fun k => (⟨h a k, hsort a k⟩ : CanonicalRV.RVSort M)) =
          (rawRVSpace (M := M) j).decode ⟨w ∘ Sum.inr, hy⟩}
    convert hdef using 1
    ext w
    constructor
    · rintro ⟨hx, hy, a, ha, he⟩
      refine ⟨a, ?_, ?_⟩
      · rw [ha, mixedValues_decode]
      · exact (congrArg rvValues he).trans (Space.ofEmbedding_decode _ _ _ _)
    · rintro ⟨a, ha, he⟩
      have hsource : w ∘ Sum.inl ∈ (rawMixedSpace (M := M) n r).domain :=
        ha ▸ mixedValues_mem_domain a.val
      have htarget : w ∘ Sum.inr ∈ (rawRVSpace (M := M) j).domain := by
        refine ⟨fun k => ⟨h a k, hsort a k⟩, ?_⟩
        exact he
      refine ⟨hsource, htarget, a, ?_, ?_⟩
      · apply mixedValues_injective
        rw [mixedValues_decode]
        exact ha
      · apply rvValues_injective
        have hcode := Space.ofEmbedding_decode (rvValues (M := M) (n := j))
          rvValues_injective (rawRVSpace (M := M) j).domain_definable
          ⟨w ∘ Sum.inr, htarget⟩
        exact he.trans hcode.symm

@[simp] theorem mapToRV_values (A : DefSet (rawMixedSpace (M := M) n r) S)
    {j : ℕ} (h : A → Fin j → M) (hsort : ∀ a k, iRV (h a k))
    (hdef : S.Definable LRV {w : (Fin n ⊕ Fin r) ⊕ Fin j → M |
      ∃ a : A, mixedValues a.val = w ∘ Sum.inl ∧ h a = w ∘ Sum.inr}) (a : A) :
    rvValues ((mapToRV A h hsort hdef a).val) = h a := rfl

theorem injection_refinement (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    {Q : DefinableGeometry.Space LRV M}
    {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet Q S}
    (f : Map A B) (hf : f.FiniteFibres) :
    ∃ j : ℕ, ∃ h : Map A (DefSet.univ (rawRVSpace j) S),
      Function.Injective (f.pair h) := by
  letI : Fintype Q.Index := Fintype.ofFinite Q.Index
  let e : Q.Index ≃ Fin (Fintype.card Q.Index) := Fintype.equivFin Q.Index
  let E (t : Fin (Fintype.card Q.Index) → M) (y : Q.Carrier) : Prop :=
    ∃ ht : t ∘ e ∈ Q.domain, Q.decode ⟨t ∘ e, ht⟩ = y
  have hcover (y : Q.Carrier) : ∃ t, E t y := by
    obtain ⟨c, hc⟩ := Q.onto y
    let t := c.val ∘ e.symm
    have he : t ∘ e = c.val := by funext i; exact congrArg c.val (e.symm_apply_apply i)
    refine ⟨t, he.symm ▸ c.property, ?_⟩
    convert hc using 1
    congr 1
    exact Subtype.ext he
  have hsingle (t : Fin (Fintype.card Q.Index) → M) (y y' : Q.Carrier)
      (hy : E t y) (hy' : E t y') : y = y' := by
    obtain ⟨ht, hy⟩ := hy
    obtain ⟨ht', hy'⟩ := hy'
    exact hy.symm.trans hy'
  have hgraph : FiniteRefinement.RelationDefinable S
      {p | ∃ a : A, a.val = p.2 ∧ E p.1 (f a).val} := by
    have hg := f.graph_definable.preimage_comp
      (Sum.elim Sum.inr (fun i => Sum.inl (e i)) :
        (Fin n ⊕ Fin r) ⊕ Q.Index → Fin (Fintype.card Q.Index) ⊕ (Fin n ⊕ Fin r))
    change S.Definable LRV _
    convert hg using 1
    ext z
    constructor
    · rintro ⟨x, ⟨a, rfl, ht, he⟩, hx⟩
      have hsource : z ∘ Sum.inr ∈ (rawMixedSpace (M := M) n r).domain :=
        hx ▸ mixedValues_mem_domain a.val
      refine ⟨hsource, ht, a, ?_, he.symm⟩
      apply mixedValues_injective
      rw [mixedValues_decode]
      exact hx
    · rintro ⟨hx, ht, a, ha, he⟩
      refine ⟨a.val, ⟨a, rfl, ht, he.symm⟩, ?_⟩
      change mixedValues a.val = z ∘ Sum.inr
      rw [ha]
      exact mixedValues_decode _
  have hfinite (y : Q.Carrier) : {a : A | (f a).val = y}.Finite := by
    by_cases hy : y ∈ B.carrier
    · convert hf ⟨y, hy⟩ using 1
      ext a
      change (f a).val = y ↔ f a = ⟨y, hy⟩
      exact ⟨fun he => Subtype.ext he, fun he => congrArg Subtype.val he⟩
    · have he : {a : A | (f a).val = y} = ∅ := by
        ext a
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        intro ha
        exact hy (ha ▸ (f a).property)
      rw [he]
      exact Set.finite_empty
  obtain ⟨j, h, hinj, hsort, hdef⟩ := FiniteRefinement.finite_map_refinement h00 hs S hsmall
    A.carrier (fun a => (f a).val) E hcover hsingle hgraph hfinite
  let hmap := mapToRV A h hsort hdef
  refine ⟨j, hmap, ?_⟩
  intro a b hab
  apply hinj
  exact congrArg (fun z : B.prod (DefSet.univ (rawRVSpace j) S) =>
    (z.val.1, rvValues z.val.2)) hab

end SpecialTransformations.Section4
