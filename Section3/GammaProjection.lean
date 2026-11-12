module

public import Section3.GammaParameters

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3.GammaParameters
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- Existential real-coordinate projection retains the full proper Gamma
preimage and its global invariance. Coordinates may repeat or be omitted. -/
def Relation.imageReal {S : Set M} {k n m : ℕ} {sn : Fin n → SortTag}
    (Q : Relation S k n sn) (π : Fin m → Fin n) : Relation S k m (sn ∘ π) where
  carrier := {p | ∃ x, (p.1,x) ∈ Q.carrier ∧ x ∘ π = p.2}
  definable := by
    let U := Q.carrier
    have hQ := Q.definable
    let N := CanonicalStructure.normalize (M := M)
    letI := N
    have hq := hQ.image_comp (Sum.map id π)
    convert hq using 1
    ext z
    change (∃ x, (z ∘ Sum.inl,x) ∈ U ∧ x ∘ π = z ∘ Sum.inr) ↔
      ∃ w, (w ∘ Sum.inl,w ∘ Sum.inr) ∈ U ∧ w ∘ Sum.map id π = z
    constructor
    · rintro ⟨x,hx,hy⟩
      refine ⟨Sum.elim (z ∘ Sum.inl) x,hx,?_⟩
      funext i
      cases i with
      | inl i => rfl
      | inr i => exact congrFun hy i
    · rintro ⟨w,hw,he⟩
      have hl : w ∘ Sum.inl = z ∘ Sum.inl := funext (fun i => congrFun he (.inl i))
      refine ⟨w ∘ Sum.inr,?_,funext (fun i => congrFun he (.inr i))⟩
      rw [← hl]
      exact hw
  proper := by
    rintro p ⟨x,hx,he⟩
    obtain ⟨hp,hs⟩ := Q.proper _ hx
    refine ⟨hp,?_⟩
    intro i
    rw [← congrFun he i]
    exact hs (π i)
  invariant := by
    intro t u htu b
    exact exists_congr (fun x => and_congr (Q.invariant t u htu x) Iff.rfl)

theorem Relation.imageReal_fibre {S : Set M} {k n m : ℕ} {sn : Fin n → SortTag}
    (Q : Relation S k n sn) (π : Fin m → Fin n) (γ : Fin k → Values.Gamma (M := M)) :
    (Q.imageReal π).fibre γ = (fun x => x ∘ π) '' Q.fibre γ := rfl

theorem DefinableWith.image_real {S : Set M} {k n m : ℕ}
    {γ : Fin k → Values.Gamma (M := M)} {sn : Fin n → SortTag} {A : Set (Fin n → M)}
    (hA : DefinableWith S γ sn A) (π : Fin m → Fin n) :
    DefinableWith S γ (sn ∘ π) ((fun x => x ∘ π) '' A) := by
  obtain ⟨Q,hQA⟩ := hA
  refine ⟨Q.imageReal π,?_⟩
  rw [Relation.imageReal_fibre,hQA]

theorem DefinableOverBase.image_real {B : Base (M := M)} {n m : ℕ}
    {sn : Fin n → SortTag} {A : Set (Fin n → M)} (hA : DefinableOverBase B sn A)
    (π : Fin m → Fin n) : DefinableOverBase B (sn ∘ π) ((fun x => x ∘ π) '' A) := by
  obtain ⟨k,γ,hγ,hA⟩ := hA
  exact ⟨k,γ,hγ,hA.image_real π⟩

end SpecialTransformations.Section3.GammaParameters
