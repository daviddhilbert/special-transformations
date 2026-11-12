module

public import Section3.GammaParameters
public import Section3.GammaCodeDefinability
public import Section3.TupleRelations

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3.GammaParameters
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- An intersection indexed by a Gamma-definable family. Full preimages
and invariance, rather than named representative sections, define the result. -/
def familyIntersection {S : Set M} {k n : ℕ} {sn : Fin n → SortTag}
    (Q : Relation S k n sn) (σ : SortTag) (R : Set ((Fin n → M) × M)) :
    Set ((Fin k → M) × (Fin 1 → M)) :=
  {p | Proper p.1 ∧ sortEval σ (p.2 0) ∧ ∀ a, (p.1,a) ∈ Q.carrier → (a,p.2 0) ∈ R}

theorem familyIntersection_definable {S : Set M} {k n : ℕ} {sn : Fin n → SortTag}
    (Q : Relation S k n sn) (σ : SortTag) (R : Set ((Fin n → M) × M))
    (hR : @RawClosure.Tuple.RelationDefinable M (CanonicalStructure.normalize (M := M)) n S R) :
    @Set.Definable M S LRV (CanonicalStructure.normalize (M := M)) (Fin k ⊕ Fin 1)
      {z | (z ∘ Sum.inl,z ∘ Sum.inr) ∈ familyIntersection Q σ R} := by
  let U := Q.carrier
  let P : (Fin k → M) → Prop := Proper
  let E : M → Prop := sortEval σ
  have hQ := Q.definable
  have hProper := proper_normalized_definable (M := M) S (n := k)
  have hSort := ((definableAt_iff_normalized_raw S σ {x | sortEval σ x}).mp
    (definableAt_sort S σ)).1
  let N := CanonicalStructure.normalize (M := M)
  letI := N
  let α := Fin k ⊕ Fin 1
  let domainIdx : Fin k ⊕ Fin n → α ⊕ Fin n :=
    Sum.elim (fun i => Sum.inl (Sum.inl i)) Sum.inr
  let relIdx : Fin n ⊕ Fin 1 → α ⊕ Fin n :=
    Sum.elim Sum.inr (fun i => Sum.inl (Sum.inr i))
  have hp := hQ.preimage_comp domainIdx
  have hr := hR.preimage_comp relIdx
  have hu := (hp.compl.union hr).forall_of_finite
  have hg := hProper.preimage_comp (Sum.inl : Fin k → α)
  have hs := hSort.preimage_comp (Sum.inr : Fin 1 → α)
  convert (hg.inter hs).inter hu using 1
  ext z
  change (P (z ∘ Sum.inl) ∧ E (z (.inr 0)) ∧
      ∀ a, (z ∘ Sum.inl,a) ∈ U → (a,z (.inr 0)) ∈ R) ↔ _
  simp only [Set.mem_inter_iff,Set.mem_preimage,Set.mem_ofPred_eq,Set.mem_union,
    Set.mem_compl_iff,Function.comp_apply,domainIdx,relIdx,Sum.elim_inl,Sum.elim_inr,
    Sum.elim_comp_inl,Sum.elim_comp_inr]
  constructor
  · rintro ⟨hp,hs,hh⟩
    refine ⟨⟨hp,hs⟩,?_⟩
    intro a
    by_cases ha : (z ∘ Sum.inl,a) ∈ U
    · exact Or.inr (hh a ha)
    · exact Or.inl ha
  · rintro ⟨⟨hp,hs⟩,hh⟩
    exact ⟨hp,hs,fun a ha => (hh a).resolve_left (not_not.mpr ha)⟩

def intersectionRelation {S : Set M} {k n : ℕ} {sn : Fin n → SortTag}
    (Q : Relation S k n sn) (σ : SortTag) (R : Set ((Fin n → M) × M))
    (hR : @RawClosure.Tuple.RelationDefinable M (CanonicalStructure.normalize (M := M)) n S R) :
    Relation S k 1 (fun _ => σ) where
  carrier := familyIntersection Q σ R
  definable := familyIntersection_definable Q σ R hR
  proper := by
    intro p hp
    refine ⟨hp.1,?_⟩
    intro i
    fin_cases i
    exact hp.2.1
  invariant := by
    intro t u htu b
    change (Proper (rawTuple t) ∧ sortEval σ (b 0) ∧
      ∀ a, (rawTuple t,a) ∈ Q.carrier → (a,b 0) ∈ R) ↔
      (Proper (rawTuple u) ∧ sortEval σ (b 0) ∧
      ∀ a, (rawTuple u,a) ∈ Q.carrier → (a,b 0) ∈ R)
    simp only [rawTuple_proper,true_and]
    exact and_congr_right (fun _ => forall_congr' (fun a => imp_congr_left (Q.invariant t u htu a)))

theorem intersection_finite {S : Set M} {k n : ℕ} {sn : Fin n → SortTag}
    (Q : Relation S k n sn) (σ : SortTag) (R : Set ((Fin n → M) × M))
    (hf : ∀ a, {x | (a,x) ∈ R}.Finite) (γ : Fin k → Values.Gamma (M := M))
    (hne : (Q.fibre γ).Nonempty) :
    {x | (rawTuple (representatives γ),fun _ : Fin 1 => x) ∈ familyIntersection Q σ R}.Finite := by
  obtain ⟨a,ha⟩ := hne
  exact (hf a).subset (fun x hx => hx.2.2 a ha)

end SpecialTransformations.Section3.GammaParameters
