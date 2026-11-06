import Section4.GammaPredicates
import Section4.RVCoordinates
import Section4.CanonicalNormalization

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {g n : ℕ} {sn : Fin n → SortTag}

/-- Definable Gamma names can be eliminated using their full preimages,
without a definable choice of RV representatives. -/
theorem gamma_relation_fibre_definable (Q : Relation S g n sn)
    (γ : Fin g → Values.Gamma (M := M)) (hγ : ∀ i, Values.GammaDefinable S {γ i}) :
    SpecialTransformations.Section3.DefinableOver S sn (Q.fibre γ) := by
  let N := CanonicalStructure.normalize (M := M)
  letI := sM
  have hcode (i : Fin g) : @Set.Definable M S LRV N (Fin 1)
      {a | a 0 ∈ Values.gammaPullback {γ i}} :=
    ((definableAt_iff_normalized_raw S .rv _).mp (hγ i)).1
  have hc : @Set.Definable M S LRV N (Fin n ⊕ Fin g)
      {z | ∀ i, z (.inr i) ∈ Values.gammaPullback {γ i}} := by
    rw [Set.ofPred_forall]
    letI := N
    exact Set.definable_iInter_of_finite (fun i =>
      (hcode i).preimage_comp (fun _ : Fin 1 => (Sum.inr i : Fin n ⊕ Fin g)))
  have hq := @Set.Definable.preimage_comp M S LRV N (Fin g ⊕ Fin n) (Fin n ⊕ Fin g)
    Sum.swap _ Q.definable
  have hraw : @Set.Definable M S LRV N (Fin n) (Q.fibre γ) := by
    have h : @Set.Definable M S LRV N (Fin n)
        {b | ∃ a : Fin g → M, (a, b) ∈ Q.carrier ∧
          ∀ i, a i ∈ Values.gammaPullback {γ i}} := by
      letI := N
      exact (hq.inter hc).exists_of_finite
    convert h using 1
    ext b
    constructor
    · intro hb
      refine ⟨rawTuple (representatives γ), hb, ?_⟩
      intro i
      exact ⟨raw_rv _, raw_ne_zero _, by
        change value (representative (γ i)) = γ i
        exact representative_value _⟩
    · rintro ⟨a, ha, hcodes⟩
      have hp := (Q.proper _ ha).1
      have he : values (ofRaw a hp) = γ := by
        funext i
        obtain ⟨hr, h0, hi⟩ := hcodes i
        exact hi
      exact (Q.mem_fibre_iff (ofRaw a hp) γ he b).mpr ha
  exact (definableOver_iff_normalized_raw S sn (Q.fibre γ)).mpr ⟨hraw, Q.fibre_proper γ⟩

def rvGammaFibre (hcan : CanonicalStructure.IsCanonical (M := M))
    (Q : Relation S g n (fun _ => .rv)) (γ : Fin g → Values.Gamma (M := M))
    (hγ : ∀ i, Values.GammaDefinable S {γ i}) : DefSet (rawRVSpace (M := M) n) S where
  carrier := {t | rvValues t ∈ Q.fibre γ}
  definable := by
    have hd := (definableOver_iff_normalized_raw S (fun _ : Fin n => .rv) _).mp
      (gamma_relation_fibre_definable Q γ hγ) |>.1
    rw [canonical_normalize_eq hcan] at hd
    change @Set.Definable M S LRV sM (Fin n) _
    convert hd using 1
    ext a
    constructor
    · rintro ⟨ha, ht⟩
      have he := rvValues_decode (M := M) ⟨a, ha⟩
      change rvValues ((rawRVSpace n).decode ⟨a, ha⟩) ∈ Q.fibre γ at ht
      rwa [he] at ht
    · intro ha
      let t (i : Fin n) : CanonicalRV.RVSort M := ⟨a i, Q.fibre_proper γ a ha i⟩
      refine ⟨⟨t, rfl⟩, ?_⟩
      change rvValues ((rawRVSpace n).decode ⟨rvValues t, ⟨t, rfl⟩⟩) ∈ Q.fibre γ
      rw [decode_rvValues]
      exact ha

end SpecialTransformations.Section4

end
