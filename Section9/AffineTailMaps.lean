import Section9.AffineTailHeadFormula
import Section4.CodeMaps
import Section4.FunctionalRelations
import Section4.VFRealFibres

/-! Apply the guarded affine tail to the outputs of existing definable
maps. The scalar used to correct the determinant stays internal. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace SpecialTransformations.Section9

variable {M Γ : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable [LinearOrderedCommGroupWithZero Γ] {m : ℕ}
local notation "VF" => VFType (M := M)

theorem exists_affineTailMap (v : Valuation VF Γ)
    (hv : ∀ a b : VF, VFValued.predV a b ↔ v a ≤ v b)
    {S : Set M} {P : Space LRV M} {A : DefSet P S}
    (a b x : Map A (DefSet.univ (rawVFSpace (M := M) m) S))
    (D c : Map A (DefSet.univ (rawVFSpace (M := M) 1) S)) (j : Fin m)
    (ha : ∀ p i, (a p).val i ≠ 0) (hb : ∀ p i, (b p).val i ≠ 0) :
    ∃ T : Map A (DefSet.univ (rawVFSpace (M := M) m) S), ∀ p,
      (T p).val = affineTail (a p).val (b p).val
        (affineTailSlopesForHead v (a p).val (b p).val j ((D p).val 0) ((c p).val 0)) (x p).val := by
  let Q := rawVFSpace (M := M) m
  let W := rawVFSpace (M := M) 1
  let I := Q.prod (Q.prod (Q.prod (W.prod W)))
  let g := a.pair (b.pair (x.pair (D.pair c)))
  let σ : AffineHeadCode m → I.Index ⊕ Q.Index := fun i =>
    match i with
    | .inl (k,i) => (![Sum.inl (.inl i), .inl (.inr (.inl i)),
      .inl (.inr (.inr (.inl i))), .inr i] : Fin 4 → I.Index ⊕ Q.Index) k
    | .inr k => (![Sum.inl (.inr (.inr (.inr (.inl (0 : Fin 1))))),
      .inl (.inr (.inr (.inr (.inr (0 : Fin 1)))))] : Fin 2 → I.Index ⊕ Q.Index) k
  let T (p : I.Carrier) (y : Q.Carrier) : Prop :=
    (fun i => (affineHeadInputs p.1 p.2.1 p.2.2.1 y (p.2.2.2.1 0) (p.2.2.2.2 0) i).val) ∈
      affineTailHeadCodes j
  have hT : I.RelationDefinable Q S T := by
    have hdef := (affineTailHeadCodes_definable S j).preimage_comp σ
    have hI := (I.domain_definable.mono (Set.empty_subset S)).preimage_comp (Sum.inl : I.Index → I.Index ⊕ Q.Index)
    have hQ := (Q.domain_definable.mono (Set.empty_subset S)).preimage_comp (Sum.inr : Q.Index → I.Index ⊕ Q.Index)
    change S.Definable LRV (I.relation Q T)
    convert hI.inter (hQ.inter hdef) using 1
    ext z
    have he (h₁ : z ∘ Sum.inl ∈ I.domain) (h₂ : z ∘ Sum.inr ∈ Q.domain) :
        T (I.decode ⟨z ∘ Sum.inl, h₁⟩) (Q.decode ⟨z ∘ Sum.inr, h₂⟩) ↔ z ∘ σ ∈ affineTailHeadCodes j := by
      have ha₀ := vfValues_decode ⟨fun i => z (.inl (.inl i)), h₁.1⟩
      have hb₀ := vfValues_decode ⟨fun i => z (.inl (.inr (.inl i))), h₁.2.1⟩
      have hx₀ := vfValues_decode ⟨fun i => z (.inl (.inr (.inr (.inl i)))), h₁.2.2.1⟩
      have hD₀ := vfValues_decode ⟨fun i => z (.inl (.inr (.inr (.inr (.inl i))))), h₁.2.2.2.1⟩
      have hc₀ := vfValues_decode ⟨fun i => z (.inl (.inr (.inr (.inr (.inr i))))), h₁.2.2.2.2⟩
      have hy₀ := vfValues_decode ⟨z ∘ Sum.inr, h₂⟩
      let p := I.decode ⟨z ∘ Sum.inl, h₁⟩
      let y := Q.decode ⟨z ∘ Sum.inr, h₂⟩
      change (fun i => (affineHeadInputs p.1 p.2.1 p.2.2.1 y (p.2.2.2.1 0) (p.2.2.2.2 0) i).val) ∈
        affineTailHeadCodes j ↔ _
      have hcode : (fun i => (affineHeadInputs p.1 p.2.1 p.2.2.1 y (p.2.2.2.1 0) (p.2.2.2.2 0) i).val) = z ∘ σ := by
        funext i
        rcases i with ⟨k,i⟩ | k
        · fin_cases k
          · exact congrFun ha₀ i
          · exact congrFun hb₀ i
          · exact congrFun hx₀ i
          · exact congrFun hy₀ i
        · fin_cases k
          · change (p.2.2.2.1 0).val = z (.inl (.inr (.inr (.inr (.inl (0 : Fin 1))))))
            exact congrFun hD₀ 0
          · change (p.2.2.2.2 0).val = z (.inl (.inr (.inr (.inr (.inr (0 : Fin 1))))))
            exact congrFun hc₀ 0
      rw [hcode]
    exact ⟨by rintro ⟨h₁, h₂, h⟩; exact ⟨h₁, h₂, (he h₁ h₂).mp h⟩,
      by rintro ⟨h₁, h₂, h⟩; exact ⟨h₁, h₂, (he h₁ h₂).mpr h⟩⟩
  let R (p : P.Carrier) (y : Q.Carrier) := ∃ p' : A, p'.val = p ∧ T (g p').val y
  have hR : P.RelationDefinable Q S R := (g.graph_definable.comp P I Q hT).congr P Q (by
    intro p y
    constructor
    · rintro ⟨_, ⟨p', hp', rfl⟩, h⟩
      exact ⟨p', hp', h⟩
    · rintro ⟨p', hp', h⟩
      exact ⟨(g p').val, ⟨p', hp', rfl⟩, h⟩)
  let G (p : A) := affineTail (a p).val (b p).val
    (affineTailSlopesForHead v (a p).val (b p).val j ((D p).val 0) ((c p).val 0)) (x p).val
  have hmem (p : A) (y : Q.Carrier) : T (g p).val y ↔ G p = y :=
    mem_affineTailHeadCodes_iff v hv j _ _ _ _ _ _ (ha p) (hb p)
  have hdom (p y) (h : R p y) : p ∈ A.carrier ∧ y ∈ (DefSet.univ Q S).carrier := by
    obtain ⟨p', rfl, _⟩ := h
    exact ⟨p'.property, Set.mem_univ _⟩
  have htotal (p : A) : ∃ y, R p.val y := ⟨G p, p, rfl, (hmem p _).mpr rfl⟩
  have huniq (p y z) (hy : R p y) (hz : R p z) : y = z := by
    obtain ⟨p₁, h₁, hy⟩ := hy
    obtain ⟨p₂, h₂, hz⟩ := hz
    have hp : p₂ = p₁ := Subtype.ext (h₂.trans h₁.symm)
    subst p₂
    exact ((hmem p₁ y).mp hy).symm.trans ((hmem p₁ z).mp hz)
  let F := Map.ofFunctionalRelation hR hdom htotal huniq
  refine ⟨F, fun p => ?_⟩
  obtain ⟨p', hp, h⟩ := Map.ofFunctionalRelation_graph hR hdom htotal huniq p
  have he : p' = p := Subtype.ext hp
  exact ((hmem p _).mp (he ▸ h)).symm

end SpecialTransformations.Section9
