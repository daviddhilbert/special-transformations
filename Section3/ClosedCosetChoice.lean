module

public import Section3.ClosedQuotientChoice
public import Section3.DefinableCosets
public import Section3.ClosedBallQuotient

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.ClosedCosetChoice
open ClosedBallCodes
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)
include hv

theorem closed_cosets_of_code (H : AddSubgroup (VFType (M := M))) (t : Code M)
    (ht : rawBall t.val = Subtype.val '' (H : Set (VFType (M := M))))
    (d : VFType (M := M) ⧸ H) : ClosedBallRoots.IsClosedBall v {x | QuotientAddGroup.mk' H x = d} := by
  obtain ⟨c,hc⟩ := QuotientAddGroup.mk'_surjective H d
  have heH : (H : Set (VFType (M := M))) = ball t.val := by
    ext x
    change x ∈ H ↔ x.val ∈ rawBall t.val
    rw [ht]
    exact ⟨fun hx => ⟨x,hx,rfl⟩,fun ⟨z,hz,he⟩ => (Subtype.ext he : z=x) ▸ hz⟩
  have hclass (x : VFType (M := M)) : QuotientAddGroup.mk' H x = d ↔ x-c ∈ H := by
    rw [← hc]
    exact QuotientAddGroup.eq_iff_sub_mem
  by_cases hz : t.val 2 = iVFZero
  · have heU : (H : Set (VFType (M := M))) = Set.univ :=
      heH.trans (ball_eq_univ t.val t.property hz)
    left
    ext x
    change QuotientAddGroup.mk' H x = d ↔ True
    rw [hclass]
    have hm : x-c ∈ (H : Set (VFType (M := M))) := by
      rw [heU]
      exact Set.mem_univ _
    exact iff_true_intro hm
  · let a : VFType (M := M) := ⟨t.val 0,t.property 0⟩
    let b : VFType (M := M) := ⟨t.val 1,t.property 1⟩
    have heC : (H : Set (VFType (M := M))) = ValOneEC.closedBall v a (v b) :=
      heH.trans (ball_eq_closed v hv t.val t.property hz)
    right
    refine ⟨a+c,b,?_⟩
    ext x
    change QuotientAddGroup.mk' H x = d ↔ v (x-(a+c)) ≤ v b
    rw [hclass]
    have hm : x-c ∈ H ↔ v ((x-c)-a) ≤ v b := Set.ext_iff.mp heC (x-c)
    rw [hm]
    have hd : (x-c)-a = x-(a+c) := by ring
    rw [hd]

end SpecialTransformations.Section3.ClosedCosetChoice
namespace SpecialTransformations.Section3.ClosedCosetChoice
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- Lemma 3.18(2), closed-ball alternative, on the actual additive quotient.
The complete quotient profile graph is definable over exactly S, and each
class has a representative whose f-value is the chosen quotient value.
Closedness is expressed by an actual closed-ball imaginary, including the
whole field and singleton cases. No center or representative is named in S. -/
theorem lemma_3_18_2_closed (h00 : M ⊨ Axioms.ACVF00) (S : Set M)
    (H : AddSubgroup (VFType (M := M)))
    (hH : DefinableAt S .vf (Subtype.val '' (H : Set (VFType (M := M)))))
    (hclosed : ∃ B : ClosedBallCodes.ClosedBall M,
      ClosedBallCodes.underlying B = Subtype.val '' (H : Set (VFType (M := M))))
    {m : ℕ} (f : VFType (M := M) → Set (Fin m → M))
    (hf : ∀ x ys, ys ∈ f x → ∀ i, iRV (ys i))
    (hgraph : DefinableOver S MixedPolynomialSyntax.contextSort (BallFibreConstancy.graph f)) :
    ∃ G : (VFType (M := M) ⧸ H) → Set (Fin m → M),
      (∀ d ys, ys ∈ G d → ∀ i, iRV (ys i)) ∧
      DefinableOver S MixedPolynomialSyntax.contextSort
        (BallFibreConstancy.graph (fun x => G (QuotientAddGroup.mk' H x))) ∧
      ∀ d, ∃ x : VFType (M := M), QuotientAddGroup.mk' H x = d ∧ f x = G d := by
  obtain ⟨Γ,hΓ,v,hv⟩ := VFValued.exists_valuation_predV (M := M)
  letI := hΓ
  obtain ⟨B,hB⟩ := hclosed
  obtain ⟨t,ht⟩ := Quotient.exists_rep B
  have htH : ClosedBallCodes.rawBall t.val = Subtype.val '' (H : Set (VFType (M := M))) :=
    (congrArg ClosedBallCodes.underlying ht).trans hB
  exact ClosedQuotientChoice.choose_profile v hv h00 S (QuotientAddGroup.mk' H)
    (QuotientAddGroup.mk'_surjective H) (DefinableCosets.relation _) (DefinableCosets.relation_definable S _ hH)
    (DefinableCosets.mem_relation H) (closed_cosets_of_code v hv H t htH) f hf hgraph

end SpecialTransformations.Section3.ClosedCosetChoice
namespace SpecialTransformations.Section3
export ClosedCosetChoice (lemma_3_18_2_closed)
end SpecialTransformations.Section3
