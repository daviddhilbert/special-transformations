import Section9.FiniteHeadCover
import Section7.LiftedIsomorphism

/-! Refine the source labels by a finite head cover on each volume
image. The heads on the two sides may select different coordinates. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7
open SpecialTransformations.DefinableGeometry

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k n r : ℕ}
local notation "RV" => CanonicalRV.RVSort M

private def volumePreimage {A : DefSet (rawRVSpace (M := M) r) S}
    (f : Map A (DefSet.univ (rawRVSpace (M := M) n) S)) (T : DefSet (rawRVSpace (M := M) n) S) :
    DefSet (rawRVSpace (M := M) r) S :=
  ⟨{z | ∃ a : A, a.val = z ∧ (f a).val ∈ T.carrier}, f.definable_preimage T.definable⟩

private theorem finite_restricted_head_row {A : DefSet (rawRVSpace (M := M) r) S}
    (f : Map A (DefSet.univ (rawRVSpace (M := M) n) S)) (hf : f.FiniteFibres)
    (T : DefSet (rawRVSpace (M := M) n) S) (v : Fin k → Fin n) (hv : (rvHeadSelect v T).FiniteFibres)
    (x : Fin k → RV) : {u : A | (f u).val ∈ T.carrier ∧ (f u).val ∘ v = x}.Finite := by
  let D := {a : T | rvHeadSelect v T a = ⟨x, Set.mem_univ _⟩}
  have hD : D.Finite := hv ⟨x, Set.mem_univ _⟩
  let Q (a : T) : Set A := {u | f u = ⟨a.val, Set.mem_univ _⟩}
  have hQ (a : T) : (Q a).Finite := hf ⟨a.val, Set.mem_univ _⟩
  apply (hD.biUnion (fun a _ => hQ a)).subset
  rintro u ⟨hu, hx⟩
  let a : T := ⟨(f u).val, hu⟩
  refine Set.mem_iUnion₂.mpr ⟨a, ?_, ?_⟩
  · exact Subtype.ext hx
  · exact Subtype.ext rfl

theorem exists_simultaneous_finite_head_cover
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk S < κ) (hkn : k ≤ n)
    {U V : RVFiniteObject (M := M) S n} (F : U ≅ V)
    (hU : rvDim U.obj.volume.image ≤ k) (hV : rvDim V.obj.volume.image ≤ k) :
    let f := ((finiteVolumeProperty S n).ι.mapIso F).hom.map
    ∃ a b : ℕ, ∃ P : Fin a × Fin b → DefSet (rawRVSpace (M := M) U.obj.arity) S,
      ∃ v w : Fin a × Fin b → Fin k ↪ Fin n,
        (∀ i, (P i).carrier ⊆ U.obj.domain.carrier) ∧
        (∀ u : U.obj.domain, ∃ i, u.val ∈ (P i).carrier) ∧
        ∀ i x,
          {u : U.obj.domain | u.val ∈ (P i).carrier ∧ U.obj.value u ∘ v i = x}.Finite ∧
          {u : U.obj.domain | u.val ∈ (P i).carrier ∧ V.obj.value (f u) ∘ w i = x}.Finite := by
  let E := (finiteVolumeProperty S n).ι.mapIso F
  let f := U.obj.volume
  let g := V.obj.volume.comp E.hom.map
  obtain ⟨a, A, v, hv, hA⟩ := exists_finite_head_cover hc hκ hs h00 hsmall hkn U.obj.volume.image hU
  obtain ⟨b, B, w, hw, hB⟩ := exists_finite_head_cover hc hκ hs h00 hsmall hkn V.obj.volume.image hV
  let P (i : Fin a × Fin b) := (volumePreimage f (A i.1)).inter (volumePreimage g (B i.2))
  have hp (u : U.obj.domain) (i : Fin a × Fin b) : u.val ∈ (P i).carrier ↔
      (f u).val ∈ (A i.1).carrier ∧ (g u).val ∈ (B i.2).carrier := by
    constructor
    · rintro ⟨⟨u₁, h₁, hu₁⟩, ⟨u₂, h₂, hu₂⟩⟩
      exact ⟨(show u₁ = u from Subtype.ext h₁) ▸ hu₁, (show u₂ = u from Subtype.ext h₂) ▸ hu₂⟩
    · rintro ⟨hu, hu'⟩
      exact ⟨⟨u, rfl, hu⟩, ⟨u, rfl, hu'⟩⟩
  have hg : g.FiniteFibres := V.property.comp (Map.finiteFibres_of_injective (fun u u' h => by
    have he := congrArg E.inv.map h
    rwa [Section7.rvIso_inv_apply, Section7.rvIso_inv_apply] at he))
  refine ⟨a, b, P, v ∘ Prod.fst, w ∘ Prod.snd, ?_, ?_, ?_⟩
  · rintro i _ ⟨⟨u, rfl, _⟩, _⟩
    exact u.property
  · intro u
    obtain ⟨i, hi⟩ := hA ⟨(f u).val, Set.mem_range_self u⟩
    obtain ⟨j, hj⟩ := hB ⟨(g u).val, Set.mem_range_self (E.hom.map u)⟩
    exact ⟨(i,j), (hp u (i,j)).mpr ⟨hi,hj⟩⟩
  · intro i x
    exact ⟨(finite_restricted_head_row f U.property _ _ (hv i.1).2 x).subset
      (fun u hu => ⟨((hp u i).mp hu.1).1, hu.2⟩),
      (finite_restricted_head_row g hg _ _ (hw i.2).2 x).subset
      (fun u hu => ⟨((hp u i).mp hu.1).2, hu.2⟩)⟩

end SpecialTransformations.Section9
