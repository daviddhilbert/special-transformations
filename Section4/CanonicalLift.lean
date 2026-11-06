import Section4.RVCategories
import Section4.VFCategories

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

def tupleRV {n : ℕ} (a : Fin n → VFType (M := M)) : Fin n → CanonicalRV.RVSort M :=
  fun i => CanonicalRV.encodedRv (a i)

theorem tupleRV_surjective {n : ℕ} : Function.Surjective (tupleRV (M := M) (n := n)) := by
  intro t
  choose a ha using fun i => CanonicalRV.encodedRv_surjective (t i)
  exact ⟨a, funext ha⟩

/-- Definition 4.18, retaining all the RV coordinates of the original U. -/
def rvLift (U : RVObject (M := M) S k) : DefSet (rawMixedSpace (M := M) k U.arity) S where
  carrier := {p | ∃ u : U.domain, u.val = p.2 ∧ U.value u = tupleRV p.1}
  definable := by
    let P := rawMixedSpace (M := M) k U.arity
    let F (z : Fin k ⊕ Fin U.arity → M) : Fin U.arity ⊕ Fin k → M :=
      Sum.elim (z ∘ Sum.inr) (fun i => iRv (z (.inl i)))
    have hF : S.DefinableMap LRV F := by
      intro j
      cases j with
      | inl j => exact Set.DefinableFun.proj LRV
      | inr i =>
        exact (Set.DefinableFun.of_empty
          (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.rvMap)).comp
          (show S.DefinableMap LRV (fun z : Fin k ⊕ Fin U.arity → M => ![z (.inl i)]) from
            by intro j; fin_cases j; exact Set.DefinableFun.proj LRV)
    have hD : S.Definable LRV {z : Fin k ⊕ Fin U.arity → M | z ∈ P.domain} :=
      P.definable_domain S
    have h := hD.inter (U.volume.graph_definable.preimage_map hF)
    have hcode (z : Fin k ⊕ Fin U.arity → M) (hz : z ∈ P.domain) :
        rvValues (tupleRV (P.decode ⟨z, hz⟩).1) = fun i => iRv (z (.inl i)) := by
      have hc : vfValues ((rawVFSpace (M := M) k).decode ⟨z ∘ Sum.inl, hz.1⟩) =
          z ∘ Sum.inl := Space.ofEmbedding_decode vfValues vfValues_injective
            (rawVFSpace (M := M) k).domain_definable _
      funext i
      exact congrArg iRv (congrFun hc i)
    change S.Definable LRV {z : Fin k ⊕ Fin U.arity → M |
      ∃ hz : z ∈ P.domain, ∃ u : U.domain,
        u.val = (P.decode ⟨z, hz⟩).2 ∧ U.value u = tupleRV (P.decode ⟨z, hz⟩).1}
    convert h using 1
    ext z
    constructor
    · rintro ⟨hz, u, hu, hv⟩
      have ht : (fun i => iRv (z (.inl i))) ∈ (rawRVSpace (M := M) k).domain :=
        ⟨tupleRV (P.decode ⟨z, hz⟩).1, hcode z hz⟩
      refine ⟨hz, hz.2, ht, u, hu, ?_⟩
      apply rvValues_injective
      have hc : rvValues ((rawRVSpace (M := M) k).decode
          ⟨fun i => iRv (z (.inl i)), ht⟩) = fun i => iRv (z (.inl i)) :=
        Space.ofEmbedding_decode rvValues rvValues_injective
          (rawRVSpace (M := M) k).domain_definable _
      exact (congrArg rvValues hv).trans ((hcode z hz).trans hc.symm)
    · rintro ⟨hz, hs, ht, u, hu, hv⟩
      refine ⟨hz, u, hu, ?_⟩
      apply rvValues_injective
      have hc : rvValues ((rawRVSpace (M := M) k).decode
          ⟨fun i => iRv (z (.inl i)), ht⟩) = fun i => iRv (z (.inl i)) :=
        Space.ofEmbedding_decode rvValues rvValues_injective
          (rawRVSpace (M := M) k).domain_definable _
      exact (congrArg rvValues hv).trans (hc.trans (hcode z hz).symm)

def rvLiftObject (Γ : DefinableGeometry.Space LRV M) (U : RVObject (M := M) S k) :
    VFObject Γ S k :=
  ⟨⟨(k, U.arity), rvLift U⟩, vfDim_le_arity Γ (rvLift U)⟩

theorem rvLift_finite_rv_fibres (U : RVObject (M := M) S k) (hf : U.volume.FiniteFibres)
    (a : Fin k → VFType (M := M)) :
    {t : Fin U.arity → CanonicalRV.RVSort M | (a, t) ∈ (rvLift U).carrier}.Finite := by
  let T : Set (Fin U.arity → CanonicalRV.RVSort M) :=
    {t | (a, t) ∈ (rvLift U).carrier}
  by_cases hT : T.Nonempty
  · obtain ⟨t₀, u₀, hu₀, hv₀⟩ := hT
    apply ((hf (U.volume u₀)).image Subtype.val).subset
    rintro t ⟨u, hu, hv⟩
    refine ⟨u, ?_, hu⟩
    apply Subtype.ext
    exact hv.trans hv₀.symm
  · have he : T = ∅ := Set.not_nonempty_iff_eq_empty.mp hT
    change T.Finite
    rw [he]
    exact Set.finite_empty

def rvLiftFiniteObject (Γ : DefinableGeometry.Space LRV M)
    (U : RVFiniteObject (M := M) S k) : VFFiniteObject Γ S k :=
  ⟨rvLiftObject Γ U.obj, rvLift_finite_rv_fibres U.obj U.property⟩

/-- The RV image of a lift is the companion from Definition 4.16. -/
theorem rvLift_companion (U : RVObject (M := M) S k) :
    (fun p => (tupleRV p.1, p.2)) '' (rvLift U).carrier = U.companion.carrier := by
  ext q
  constructor
  · rintro ⟨p, ⟨u, hu, hv⟩, he⟩
    refine ⟨u, ?_⟩
    change (U.value u, u.val) = q
    rw [hu, hv]
    exact he
  · rintro ⟨u, rfl⟩
    obtain ⟨a, ha⟩ := tupleRV_surjective (U.value u)
    exact ⟨(a, u.val), ⟨u, rfl, ha.symm⟩, congrArg (fun t => (t, u.val)) ha⟩

end SpecialTransformations.Section4

end
