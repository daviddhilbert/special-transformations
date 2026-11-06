import Section4.Fibres
import Section4.VFDimension
import Section4.Spaces
import Section3.VFAlgebraicity

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.DefinableGeometry.Space

variable {M : Type} [LRV.Structure M]

/-- An auxiliary presentation whose real coordinates all lie in RV. -/
def RVCoded (P : Space LRV M) : Prop := ∀ c : P.domain, ∀ i, iRV (c.val i)

theorem RVCoded.prod (P Q : Space LRV M) (hP : P.RVCoded) (hQ : Q.RVCoded) :
    (P.prod Q).RVCoded := by
  intro c i
  cases i with
  | inl i => exact hP ⟨c.val ∘ Sum.inl, c.property.1⟩ i
  | inr i => exact hQ ⟨c.val ∘ Sum.inr, c.property.2⟩ i

theorem RVCoded.power (P : Space LRV M) (hP : P.RVCoded) (ι : Type) [Finite ι] :
    (P.power ι).RVCoded := by
  intro c i
  exact hP ⟨fun j => c.val (i.1, j), c.property i.1⟩ i.2

end SpecialTransformations.DefinableGeometry.Space

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M]

theorem rawRVSpace_rvCoded (n : ℕ) : (rawRVSpace (M := M) n).RVCoded := by
  intro c i
  obtain ⟨t, ht⟩ := c.property
  have he : (t i).val = c.val i := congrFun ht i
  exact he ▸ (t i).property

theorem AuxiliaryCoordinates.rvCoded (Γ : DefinableGeometry.Space LRV M)
    (hΓ : Γ.RVCoded) (i : AuxiliaryCoordinates) : (i.space Γ).RVCoded := by
  induction i with
  | rv n => exact rawRVSpace_rvCoded n
  | gamma n => exact Space.RVCoded.power Γ hΓ (Fin n)
  | prod a b ha hb => exact Space.RVCoded.prod _ _ ha hb

variable [hM : M ⊨ Axioms.ACVF]

theorem gammaSpace_rvCoded :
    @Space.RVCoded M (CanonicalStructure.normalize (M := M)) (gammaSpace (M := M)) := by
  intro c i
  change Fin 1 at i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  exact c.property.1

/-- The algebraicity half of the dimension/transcendence-degree argument.
Finite-to-one witnesses make source VF coordinates algebraic over the VF
coordinates of their image; the RV/Gamma code parameters disappear by 3.3. -/
theorem finite_map_vf_coordinate_isAlgebraic
    (hcan : CanonicalStructure.IsCanonical (M := M))
    (Γ : DefinableGeometry.Space LRV M) (hΓ : Γ.RVCoded)
    {S : Set M} {n r k : ℕ} (i : AuxiliaryCoordinates)
    {A : DefSet (rawMixedSpace (M := M) n r) S}
    (f : Map A (DefSet.univ ((rawVFSpace k).prod (i.space Γ)) S))
    (hf : f.FiniteFibres) (a : A) (j : Fin n) :
    IsAlgebraic (vfParameterField (S ∪ Set.range (vfValues (f a).val.1))) (a.val.1 j) := by
  let Q := (rawVFSpace (M := M) k).prod (i.space Γ)
  obtain ⟨c, hc⟩ := Q.onto (f a).val
  let b := (f a).val.1
  let V := Set.range (vfValues b)
  let W := Set.range (c.val ∘ Sum.inr)
  have hD : vfValues (Q.decode c).1 = c.val ∘ Sum.inl :=
    Space.ofEmbedding_decode (vfValues (M := M) (n := k)) vfValues_injective
      (rawVFSpace (M := M) k).domain_definable ⟨c.val ∘ Sum.inl, c.property.1⟩
  have hleft : c.val ∘ Sum.inl = vfValues b :=
    hD.symm.trans (congrArg (fun q : Q.Carrier => vfValues q.1) hc)
  have hW : ∀ x ∈ W, iRV x := by
    rintro x ⟨q, rfl⟩
    exact AuxiliaryCoordinates.rvCoded Γ hΓ i ⟨c.val ∘ Sum.inr, c.property.2⟩ q
  have hrange : Set.range c.val = V ∪ W := by
    ext x
    constructor
    · rintro ⟨q, rfl⟩
      cases q with
      | inl q => exact Or.inl ⟨q, (congrFun hleft q).symm⟩
      | inr q => exact Or.inr ⟨q, rfl⟩
    · rintro (⟨q, hq⟩ | ⟨q, hq⟩)
      · exact ⟨.inl q, (congrFun hleft q).trans hq⟩
      · exact ⟨.inr q, hq⟩
  have hraw := fibre_vf_coordinate_algebraic f hf a c hc j
  have hs : AlgebraicAt (S ∪ Set.range c.val) .vf (a.val.1 j).val :=
    (algebraicAt_iff_raw hcan _ .vf _).mpr ⟨hraw, (a.val.1 j).property⟩
  have halg := algebraicAt_vf_parameterField _ (a.val.1 j) hs
  rw [hrange, ← Set.union_assoc, vfParameterField_union_rv _ _ hW] at halg
  exact halg

end SpecialTransformations.Section4

end
