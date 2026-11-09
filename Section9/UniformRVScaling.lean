import Section9.VolumeResidueCorrespondence
import Section4.CodeMaps
import Section4.ResidueRVSet

/-! Normalizing an RV set is definable jointly in its scale and residue
coordinates. The scale parameters can therefore be quantified in a
chart certificate over the original base. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section4.ResiduePurity SpecialTransformations.Section7
open SpecialTransformations.DefinableGeometry

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}
local notation "RV" => CanonicalRV.RVSort M

noncomputable def rvCoordinateProductMap (S : Set M) :
    Map (DefSet.univ ((rawRVSpace (M := M) n).prod (rawRVSpace (M := M) n)) S)
      (DefSet.univ (rawRVSpace (M := M) n) S) := by
  let Q := rawRVSpace (M := M) n
  let F (x : (Q.prod Q).Carrier) : Q.Carrier := fun i => x.1 i * x.2 i
  let C (z : (Q.prod Q).Index → M) : Q.Index → M :=
    fun i => iRVMul (z (.inl i)) (z (.inr i))
  have hC : S.DefinableMap LRV C := by
    intro i
    exact (Set.DefinableFun.of_empty
      (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.rvMul)).comp
      (show S.DefinableMap LRV (fun z : Q.Index ⊕ Q.Index → M => ![z (.inl i), z (.inr i)]) from
        fun j => by fin_cases j <;> exact Set.DefinableFun.proj LRV)
  have hcode (z : (Q.prod Q).domain) : rvValues (F ((Q.prod Q).decode z)) = C z.val := by
    funext i
    change ((Q.decode ⟨z.val ∘ Sum.inl, z.property.1⟩ i) *
      (Q.decode ⟨z.val ∘ Sum.inr, z.property.2⟩ i)).val = _
    rw [RVOperations.mul_val]
    exact congrArg₂ iRVMul (congrFun (rvValues_decode ⟨_, z.property.1⟩) i)
      (congrFun (rvValues_decode ⟨_, z.property.2⟩) i)
  exact Map.ofCodes _ F C hC (fun z => ⟨F ((Q.prod Q).decode z), hcode z⟩)
    (fun z => rvValues_injective
      ((rvValues_decode ⟨C z.val, ⟨F ((Q.prod Q).decode z), hcode z⟩⟩).trans (hcode z).symm))

@[simp] theorem rvCoordinateProductMap_apply (S : Set M)
    (p : DefSet.univ ((rawRVSpace (M := M) n).prod (rawRVSpace (M := M) n)) S) :
    (rvCoordinateProductMap S p).val = fun i => p.val.1 i * p.val.2 i := rfl

theorem normalizedCorrespondence_relation_definable
    (S : Set M) (C : DefSet (rawRVSpace (M := M) n) S) :
    (rawRVSpace (M := M) n).RelationDefinable (rawRVSpace (M := M) n) S
      (fun a r => (fun i => a i * r i) ∈ C.carrier) := by
  let Q := rawRVSpace (M := M) n
  have h := (rvCoordinateProductMap S).definable_preimage C.definable
  let X := {x | ∃ p : DefSet.univ (Q.prod Q) S, p.val = x ∧
    (rvCoordinateProductMap S p).val ∈ C.carrier}
  have he : Q.relation Q (fun a r => (fun i => a i * r i) ∈ C.carrier) =
      (Q.prod Q).preimage X := by
    ext z
    constructor
    · rintro ⟨ha, hr, hz⟩
      let p : DefSet.univ (Q.prod Q) S :=
        ⟨(Q.decode ⟨z ∘ Sum.inl, ha⟩, Q.decode ⟨z ∘ Sum.inr, hr⟩), Set.mem_univ _⟩
      exact ⟨⟨ha, hr⟩, p, rfl, hz⟩
    · rintro ⟨⟨ha, hr⟩, p, hp, hz⟩
      refine ⟨ha, hr, ?_⟩
      change (fun i => (p.val.1 i) * (p.val.2 i)) ∈ C.carrier at hz
      change (fun i => ((Q.prod Q).decode ⟨z, ⟨ha, hr⟩⟩).1 i *
        ((Q.prod Q).decode ⟨z, ⟨ha, hr⟩⟩).2 i) ∈ C.carrier
      rwa [← hp]
  change S.Definable LRV (Q.relation Q _)
  rw [he]
  exact h

end SpecialTransformations.Section9
