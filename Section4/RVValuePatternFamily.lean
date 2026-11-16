module

public import Section4.RVCoordinates
public import Section4.CanonicalNormalization
public import Section3.GammaProjection
public import Section3.GammaGoodRelations
public import Section3.GammaRVSeparation

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n : ℕ}

theorem sameScalar_code_iff_value (t : CanonicalRV.RVSort M) (u : Code (M := M)) :
    SameScalar t.val (raw u) ↔ Values.vrv t = (value u).val := by
  constructor
  · intro h
    exact (Values.vrv_eq_iff t u.val).mpr h.2.2
  · intro h
    have ht0 : t.val ≠ iRVZero := by
      intro hz
      exact (value u).property (h.symm.trans ((Values.vrv_eq_infinity_iff t).mpr hz))
    exact ⟨⟨t.property, ht0⟩, ⟨raw_rv u, raw_ne_zero u⟩, (Values.vrv_eq_iff t u.val).mp h⟩

def RVValuePattern (ε : Fin n → Bool) (γ : Fin n → Values.Gamma (M := M))
    (t : Fin n → CanonicalRV.RVSort M) : Prop :=
  ∀ i, if ε i then (t i).val = iRVZero else Values.vrv (t i) = (γ i).val

def rvPatternCarrier (A : DefSet (rawRVSpace (M := M) n) S) (ε : Fin n → Bool) :
    Set ((Fin n → M) × (Fin n → M)) :=
  {p | Proper p.1 ∧ p.2 ∈ (rawRVSpace n).preimage A.carrier ∧
    ∀ i, if ε i then ¬ NonzeroRV (p.2 i) else SameScalar (p.2 i) (p.1 i)}

/-- A fixed absorbing-coordinate pattern avoids introducing a second
absorbing point or dividing by zero. Unused Gamma coordinates remain free. -/
def rvPatternRelation (hcan : CanonicalStructure.IsCanonical (M := M))
    (A : DefSet (rawRVSpace (M := M) n) S) (ε : Fin n → Bool) :
    Relation S n n (fun _ => .rv) where
  carrier := rvPatternCarrier A ε
  definable := by
    let X : Set (Fin n → M) := (rawRVSpace n).preimage A.carrier
    have hdA : S.Definable LRV X := A.definable
    let N := CanonicalStructure.normalize (M := M)
    letI := sM
    have hA : @Set.Definable M S LRV N (Fin n) X := by
      change @Set.Definable M S LRV (@CanonicalStructure.normalize M sM) (Fin n) X
      rw [canonical_normalize_eq hcan]
      exact hdA
    have hproper := proper_normalized_definable (M := M) S (n := n)
    have hleft := @Set.Definable.preimage_comp M S LRV N (Fin n) (Fin n ⊕ Fin n)
      Sum.inl _ hproper
    have hright := @Set.Definable.preimage_comp M S LRV N (Fin n) (Fin n ⊕ Fin n)
      Sum.inr _ hA
    have hnz := nonzero_codes_normalized_definable (M := M) S
    have hsame := @same_scalar_definable M N S
    have he : {z : Fin 2 → M | @SameScalar M N (z 0) (z 1)} =
        {z | SameScalar (z 0) (z 1)} := by
      ext z
      exact same_scalar_normalize (z 0) (z 1)
    rw [he] at hsame
    have hpart (i : Fin n) : @Set.Definable M S LRV N (Fin n ⊕ Fin n)
        {z | if ε i then ¬ NonzeroRV (z (.inr i)) else SameScalar (z (.inr i)) (z (.inl i))} := by
      cases hε : ε i
      · exact @Set.Definable.preimage_comp M S LRV N (Fin 2) (Fin n ⊕ Fin n)
          (![Sum.inr i, Sum.inl i]) _ hsame
      · letI := N
        exact (hnz.preimage_comp (fun _ : Fin 1 => (Sum.inr i : Fin n ⊕ Fin n))).compl
    have hall : @Set.Definable M S LRV N (Fin n ⊕ Fin n)
        {z | ∀ i, if ε i then ¬ NonzeroRV (z (.inr i)) else SameScalar (z (.inr i)) (z (.inl i))} := by
      rw [Set.ofPred_forall]
      letI := N
      exact Set.definable_iInter_of_finite hpart
    letI := N
    exact hleft.inter (hright.inter hall)
  proper := by
    rintro p ⟨hp, ⟨hb, _⟩, _⟩
    obtain ⟨b, hb⟩ := hb
    exact ⟨hp, fun i => by rw [← hb]; exact (b i).property⟩
  invariant := by
    intro t u htu b
    change (Proper (rawTuple t) ∧ b ∈ (rawRVSpace n).preimage A.carrier ∧ _) ↔
      (Proper (rawTuple u) ∧ b ∈ (rawRVSpace n).preimage A.carrier ∧ _)
    simp only [rawTuple_proper, true_and]
    apply and_congr Iff.rfl
    apply forall_congr'
    intro i
    cases ε i
    · exact same_scalar_with_codes_iff (b i) (t i) (u i) (congrFun htu i)
    · exact Iff.rfl

theorem mem_rvPatternRelation_fibre
    (hcan : CanonicalStructure.IsCanonical (M := M))
    (A : DefSet (rawRVSpace (M := M) n) S) (ε : Fin n → Bool)
    (γ : Fin n → Values.Gamma (M := M)) (t : Fin n → CanonicalRV.RVSort M) :
    rvValues t ∈ (rvPatternRelation hcan A ε).fibre γ ↔ t ∈ A.carrier ∧ RVValuePattern ε γ t := by
  have hA : rvValues t ∈ (rawRVSpace n).preimage A.carrier ↔ t ∈ A.carrier := by
    change (∃ h : rvValues t ∈ (rawRVSpace n).domain,
      (rawRVSpace n).decode ⟨rvValues t, h⟩ ∈ A.carrier) ↔ _
    constructor
    · rintro ⟨h, ht⟩
      simpa only [decode_rvValues] using ht
    · intro ht
      exact ⟨⟨t, rfl⟩, by simpa only [decode_rvValues] using ht⟩
  change (Proper (rawTuple (representatives γ)) ∧
    rvValues t ∈ (rawRVSpace n).preimage A.carrier ∧ _) ↔ _
  simp only [rawTuple_proper, true_and, hA]
  apply and_congr Iff.rfl
  apply forall_congr'
  intro i
  cases hε : ε i
  · simp only [RVValuePattern, hε, Bool.false_eq_true, ite_false]
    exact (sameScalar_code_iff_value (t i) (representative (γ i))).trans
      (by rw [representative_value])
  · change (¬ NonzeroRV (t i).val) ↔ (t i).val = iRVZero
    exact ⟨fun h => Classical.byContradiction (fun hn => h ⟨(t i).property, hn⟩),
      fun h hn => hn.2 h⟩

end SpecialTransformations.Section4

end
