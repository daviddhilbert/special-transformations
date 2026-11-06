import Section4.VFPadding
import Section4.FiniteMaps
import Section3.TupleRelations

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- Original-coordinate projections and finite relations over the original
base. A finite cover by these pieces will give the upper dimension bound. -/
structure CoordinatePiece (S : Set M) (n k : ℕ) where
  arity : ℕ
  bound : arity ≤ k
  select : Fin arity → Fin n
  relation : Fin n → RawClosure.Tuple.GoodRelation (n := arity) S

namespace CoordinatePiece

variable {S : Set M} {n k : ℕ} (D : CoordinatePiece (M := M) S n k) (r : ℕ)

def codeSet : Set (Fin n ⊕ Fin r → M) :=
  {z | ∀ j, ((fun q => z (.inl (D.select q))), z (.inl j)) ∈ (D.relation j).val}

theorem codeSet_definable : S.Definable LRV (D.codeSet r) := by
  have h (j : Fin n) : S.Definable LRV
      {z : Fin n ⊕ Fin r → M |
        ((fun q => z (.inl (D.select q))), z (.inl j)) ∈ (D.relation j).val} :=
    (D.relation j).property.1.preimage_comp
      (show Fin D.arity ⊕ Fin 1 → Fin n ⊕ Fin r from
        Sum.elim (fun q => Sum.inl (D.select q)) (fun _ => Sum.inl j))
  convert Set.definable_iInter_of_finite h using 1
  ext z
  simp only [codeSet, Set.mem_ofPred_eq, Set.mem_iInter]

def source : DefSet (rawMixedSpace (M := M) n r) S where
  carrier := {a | mixedValues a ∈ D.codeSet r}
  definable := by
    change S.Definable LRV _
    convert ((rawMixedSpace (M := M) n r).domain_definable.mono
      (Set.empty_subset S)).inter (D.codeSet_definable r) using 1
    ext z
    constructor
    · rintro ⟨hz, hD⟩
      refine ⟨hz, ?_⟩
      change mixedValues ((rawMixedSpace (M := M) n r).decode ⟨z, hz⟩) ∈ D.codeSet r at hD
      rwa [mixedValues_decode] at hD
    · rintro ⟨hz, hD⟩
      refine ⟨hz, ?_⟩
      change mixedValues ((rawMixedSpace (M := M) n r).decode ⟨z, hz⟩) ∈ D.codeSet r
      rwa [mixedValues_decode]

def projection : Map (D.source r) (DefSet.univ (rawMixedSpace D.arity r) S) := by
  let P := rawMixedSpace (M := M) n r
  let Q := rawMixedSpace (M := M) D.arity r
  let F (z : P.Index → M) : Q.Index → M :=
    Sum.elim (fun q => z (.inl (D.select q))) (z ∘ Sum.inr)
  have hcode (c : P.domain) :
      mixedValues ((P.decode c).1 ∘ D.select, (P.decode c).2) = F c.val := by
    have hc := mixedValues_decode c
    funext i
    cases i with
    | inl q => exact congrFun hc (.inl (D.select q))
    | inr q => exact congrFun hc (.inr q)
  have hdom (c : P.domain) : F c.val ∈ Q.domain := by
    rw [← hcode c]
    exact mixedValues_mem_domain _
  refine Map.ofCodes _ (fun a => (a.1 ∘ D.select, a.2)) F
    (fun i => by cases i <;> exact Set.DefinableFun.proj LRV) hdom ?_
  intro c
  apply mixedValues_injective
  exact (mixedValues_decode ⟨F c.val, hdom c⟩).trans (hcode c).symm

theorem projection_finite : (D.projection r).FiniteFibres := by
  intro b
  let H : Set (Fin n → M) :=
    {x | ∀ j, (vfValues b.val.1, x j) ∈ (D.relation j).val}
  have hH : H.Finite := Set.Finite.pi' (fun j => (D.relation j).property.2 (vfValues b.val.1))
  let code (a : D.source r) := (vfValues a.val.1, a.val.2)
  have hinj : Function.Injective code := by
    intro a a' he
    apply Subtype.ext
    have hl : vfValues a.val.1 = vfValues a'.val.1 :=
      congrArg (fun z : (Fin n → M) × (Fin r → CanonicalRV.RVSort M) => z.1) he
    have hr : a.val.2 = a'.val.2 :=
      congrArg (fun z : (Fin n → M) × (Fin r → CanonicalRV.RVSort M) => z.2) he
    exact Prod.ext (vfValues_injective hl) hr
  apply ((hH.prod (Set.finite_singleton b.val.2)).preimage hinj.injOn).subset
  intro a ha
  have hv : a.val.1 ∘ D.select = b.val.1 :=
    congrArg (fun z : DefSet.univ (rawMixedSpace (M := M) D.arity r) S => z.val.1) ha
  have ht : a.val.2 = b.val.2 :=
    congrArg (fun z : DefSet.univ (rawMixedSpace (M := M) D.arity r) S => z.val.2) ha
  refine ⟨?_, ht⟩
  intro j
  have hj := a.property j
  change (vfValues (a.val.1 ∘ D.select), (a.val.1 j).val) ∈ (D.relation j).val at hj
  rwa [hv] at hj

def paddedProjection : Map (D.source r)
    (DefSet.univ (rawMixedSpace (M := M) k r) S) :=
  (vfPadding D.bound (rawRVSpace r) S).comp (D.projection r)

theorem paddedProjection_finite : (D.paddedProjection r).FiniteFibres :=
  (Map.finiteFibres_of_injective (vfPadding_injective D.bound (rawRVSpace r) S)).comp
    (D.projection_finite r)

end CoordinatePiece

end SpecialTransformations.Section4

end
