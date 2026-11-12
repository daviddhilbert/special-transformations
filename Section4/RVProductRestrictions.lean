module

public import Section4.RVProductAssociativity
public import Section4.RVRestrictions
public import Section4.FiniteGluing

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] {S : Set M} {n m k l : ℕ}

theorem mem_rvProductDomain (A : DefSet (rawRVSpace (M := M) n) S)
    (B : DefSet (rawRVSpace (M := M) m) S) (t : Fin (n + m) → CanonicalRV.RVSort M) :
    t ∈ (rvProductDomain A B).carrier ↔
      ∃ a ∈ A.carrier, ∃ b ∈ B.carrier, rvAppend a b = t := by
  constructor
  · rintro ⟨p, he⟩
    exact ⟨p.val.1, p.property.1, p.val.2, p.property.2, he⟩
  · rintro ⟨a, ha, b, hb, he⟩
    exact ⟨⟨(a, b), ha, hb⟩, he⟩

theorem rvProductDomain_union (A : DefSet (rawRVSpace (M := M) n) S)
    (B C : DefSet (rawRVSpace (M := M) m) S) :
    rvProductDomain A (B.union C) = (rvProductDomain A B).union (rvProductDomain A C) := by
  apply DefSet.eq_of_carrier_eq
  ext t
  constructor
  · intro ht
    obtain ⟨a, ha, b, hb | hb, he⟩ := (mem_rvProductDomain A (B.union C) t).mp ht
    · exact Or.inl ((mem_rvProductDomain A B t).mpr ⟨a, ha, b, hb, he⟩)
    · exact Or.inr ((mem_rvProductDomain A C t).mpr ⟨a, ha, b, hb, he⟩)
  · rintro (ht | ht)
    · obtain ⟨a, ha, b, hb, he⟩ := (mem_rvProductDomain A B t).mp ht
      exact (mem_rvProductDomain A (B.union C) t).mpr ⟨a, ha, b, Or.inl hb, he⟩
    · obtain ⟨a, ha, b, hb, he⟩ := (mem_rvProductDomain A C t).mp ht
      exact (mem_rvProductDomain A (B.union C) t).mpr ⟨a, ha, b, Or.inr hb, he⟩

theorem rvProductDomain_disjoint (A : DefSet (rawRVSpace (M := M) n) S)
    (B C : DefSet (rawRVSpace (M := M) m) S) (hd : Disjoint B.carrier C.carrier) :
    Disjoint (rvProductDomain A B).carrier (rvProductDomain A C).carrier := by
  apply Set.disjoint_left.mpr
  intro t hB hC
  obtain ⟨a, ha, b, hb, heb⟩ := (mem_rvProductDomain A B t).mp hB
  obtain ⟨a', ha', c, hc, hec⟩ := (mem_rvProductDomain A C t).mp hC
  have he : (a, b) = (a', c) := by
    apply rvAppend_injective
    exact heb.trans hec.symm
  have hbc : b = c := congrArg Prod.snd he
  exact Set.disjoint_left.mp hd hb (hbc.symm ▸ hc)

def rvProductRestrictionSubset (U : RVObject (M := M) S k) (V : RVObject (M := M) S l)
    (B : DefSet (rawRVSpace (M := M) V.arity) S) (hB : B.carrier ⊆ V.domain.carrier) :
    (rvProductDomain U.domain B).carrier ⊆ (rvProductObject U V).domain.carrier := by
  intro t ht
  obtain ⟨a, ha, b, hb, he⟩ := (mem_rvProductDomain U.domain B t).mp ht
  exact (mem_rvProductDomain U.domain V.domain t).mpr ⟨a, ha, b, hB hb, he⟩

def rvProductRestrictionIso (U : RVObject (M := M) S k) (V : RVObject (M := M) S l)
    (B : DefSet (rawRVSpace (M := M) V.arity) S) (hB : B.carrier ⊆ V.domain.carrier) :
    rvProductObject U (V.restrict B hB) ≅
      (rvProductObject U V).restrict (rvProductDomain U.domain B)
        (rvProductRestrictionSubset U V B hB) := by
  apply rvIsoOfVolumePreservingBijection (Map.id (rvProductDomain U.domain B)) Function.bijective_id
  intro p
  obtain ⟨a, b, rfl⟩ := exists_rvPackPair U.domain B p
  exact (rvProductObject_value_pair U V a ⟨b.val, hB b.property⟩).trans
    (rvProductObject_value_pair U (V.restrict B hB) a b).symm

end SpecialTransformations.Section4

end
