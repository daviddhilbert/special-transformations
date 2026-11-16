module

public import Section3.ClosedBallChoice

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.ClosedBallCodes
variable {M : Type} [LRV.Structure M]

/-- Real codes are identified precisely when their underlying balls agree. -/
def Code (M : Type) [LRV.Structure M] := {t : Fin 3 → M // ∀ i, iVF (t i)}

def codeSetoid : Setoid (Code M) where
  r t u := rawBall t.val = rawBall u.val
  iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

abbrev ClosedBall (M : Type) [LRV.Structure M] := Quotient (codeSetoid (M := M))

def underlying : ClosedBall M → Set M :=
  Quotient.lift (fun t : Code M => rawBall t.val) (fun _ _ h => h)

theorem underlying_injective : Function.Injective (underlying (M := M)) := by
  intro B B'
  induction B using Quotient.inductionOn with
  | h t =>
    induction B' using Quotient.inductionOn with
    | h u => exact fun h => Quotient.sound h

def pullback (A : Set (ClosedBall M)) : Set (Fin 3 → M) :=
  {t | ∃ ht : ∀ i, iVF (t i), (Quotient.mk _ (⟨t, ht⟩ : Code M)) ∈ A}

/-- Definability on the ball imaginary means definability of its full
preimage on real codes. It does not name a representative of any ball. -/
def FamilyDefinable (S : Set M) (A : Set (ClosedBall M)) : Prop :=
  DefinableOver S (fun _ => .vf) (pullback A)

theorem pullback_image (A : Set (ClosedBall M)) :
    rawBall '' pullback A = underlying '' A := by
  ext B
  constructor
  · rintro ⟨t, ⟨ht, htA⟩, rfl⟩
    exact ⟨Quotient.mk _ (⟨t, ht⟩ : Code M), htA, rfl⟩
  · rintro ⟨b, hbA, rfl⟩
    obtain ⟨t, ht⟩ := Quotient.exists_rep b
    refine ⟨t.val, ⟨t.property, ht.symm ▸ hbA⟩, ?_⟩
    exact congrArg underlying ht

def quotientCenterGraph (A : Set (ClosedBall M)) (f : A → M) : Set (Fin 4 → M) :=
  {z | ∃ t : Code M, t.val = Fin.init z ∧
    ∃ B : A, Quotient.mk _ t = B.val ∧ f B = z (Fin.last 3)}

variable [hM : M ⊨ Axioms.ACVF]

/-- Lemma 3.10: every finite definable set of actual closed-ball imaginaries
has a center function with its complete graph definable over the original S.
The finite family may contain nested balls, singletons or the whole field. -/
theorem lemma_3_10 (h00 : M ⊨ Axioms.ACVF00) (S : Set M)
    (A : Set (ClosedBall M)) (hA : A.Finite) (hdef : FamilyDefinable S A) :
    ∃ f : A → M, (∀ B, f B ∈ underlying B.val) ∧
      DefinableOver S (fun _ => .vf) (quotientCenterGraph A f) := by
  have hfin : (rawBall '' pullback A).Finite := by
    rw [pullback_image]
    exact hA.image underlying
  obtain ⟨f, hfmem, hfgraph, hfinv⟩ := coded_centers h00 S (pullback A) hdef hfin
  let rep (B : A) : Code M := Classical.choose (Quotient.exists_rep B.val)
  have hrep (B : A) : Quotient.mk _ (rep B) = B.val :=
    Classical.choose_spec (Quotient.exists_rep B.val)
  let repC (B : A) : pullback A := ⟨(rep B).val, (rep B).property, (hrep B).symm ▸ B.property⟩
  let F (B : A) : M := f (repC B)
  have hFc (t : Code M) (ht : Quotient.mk _ t ∈ A) (B : A)
      (he : Quotient.mk _ t = B.val) : F B = f ⟨t.val, t.property, ht⟩ := by
    apply hfinv
    exact congrArg underlying ((hrep B).trans he.symm)
  refine ⟨F, ?_, ?_⟩
  · intro B
    have hh := hfmem (repC B)
    have he : rawBall (rep B).val = underlying B.val := congrArg underlying (hrep B)
    exact he ▸ hh
  · have hgraph : quotientCenterGraph A F = centerGraph (pullback A) f := by
      ext z
      constructor
      · rintro ⟨t, ht, B, he, hF⟩
        have htA : Quotient.mk _ t ∈ A := he.symm ▸ B.property
        exact ⟨⟨t.val, t.property, htA⟩, ht, (hFc t htA B he).symm.trans hF⟩
      · rintro ⟨t, ht, hf⟩
        obtain ⟨hcode, htA⟩ := t.property
        let c : Code M := ⟨t.val, hcode⟩
        let B : A := ⟨Quotient.mk _ c, htA⟩
        exact ⟨c, ht, B, rfl, (hFc c htA B rfl).trans hf⟩
    rw [hgraph]
    exact hfgraph

end SpecialTransformations.Section3.ClosedBallCodes

namespace SpecialTransformations.Section3
export ClosedBallCodes (lemma_3_10)
end SpecialTransformations.Section3
