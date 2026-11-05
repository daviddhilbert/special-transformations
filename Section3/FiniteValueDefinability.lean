import Section3.FiniteValueFibres
import Section3.GammaDefinability
import Section3.FiniteGluing
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3.RawValueFibres
open Values RawClosure RawClosure.Tuple
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def smallNonempty (A : Set M) (N : ℕ) : Set M :=
  {t | (∃ b, (![t], b) ∈ relation A) ∧ ![t] ∉ RawClosure.Tuple.HasMore (relation A) N}

theorem relation_normalized_definable (S A : Set M) (hA : DefinableAt S .rv A) :
    @RelationDefinable M (CanonicalStructure.normalize (M := M)) 1 S (relation A) := by
  let N := CanonicalStructure.normalize (M := M)
  letI := sM
  have hAN := (definableAt_normalize_iff S .rv A).mpr hA
  have hR := @relation_definable M N S A (@DefinableAt.raw_definable M N S .rv A hAN)
  exact relation_normalize A hA.2 ▸ hR

/-- First-order counting defines the nonempty fibres of size at most N,
with all normalization and non-infinity guards discharged. -/
theorem smallNonempty_definable (S A : Set M) (hA : DefinableAt S .rv A) (N : ℕ) :
    DefinableAt S .rv (smallNonempty A N) := by
  let K := CanonicalStructure.normalize (M := M)
  letI := sM
  have hR := relation_normalized_definable S A hA
  apply (definableAt_iff_normalized_raw S .rv _).mpr
  constructor
  · letI := K
    have hd := RawClosure.Tuple.domain_definable S (relation (M := M) (sM := sM) A) hR
    have hm := RawClosure.Tuple.hasMore_definable S (relation (M := M) (sM := sM) A) hR N
    change S.Definable LRV _
    convert hd.inter hm.compl using 1
    ext z
    have he : ![z 0] = z := by funext i; fin_cases i; rfl
    change ((∃ b, (![z 0], b) ∈ @relation M sM A) ∧
      ![z 0] ∉ RawClosure.Tuple.HasMore (@relation M sM A) N) ↔ _
    rw [he]
    rfl
  · rintro t ⟨⟨b, hb⟩, _⟩
    exact hb.1

theorem fibre_image_eq (A : Set M) (hA : A ⊆ {x | iRV x})
    (t : CanonicalRV.RVSort M) (ht : t.val ≠ iRVZero) :
    {b : M | (![t.val], b) ∈ relation A} =
      Subtype.val '' Values.fibre A (gammaOf t ht) := by
  ext b
  constructor
  · rintro ⟨hRV, h0, hb, htb, hbt⟩
    let u : CanonicalRV.RVSort M := ⟨b, hA hb⟩
    have he : vrv u = vrv t := (vrv_eq_iff u t).mpr ⟨hbt, htb⟩
    exact ⟨u, ⟨he, hb⟩, rfl⟩
  · rintro ⟨u, ⟨hγ, huA⟩, rfl⟩
    have hv := (vrv_eq_iff u t).mp hγ
    exact ⟨t.property, ht, huA, hv.2, hv.1⟩

theorem smallNonempty_iff (A : Set M) (hA : A ⊆ {x | iRV x}) (N : ℕ)
    (hbound : ∀ γ : Gamma (M := M), (Values.fibre A γ).Finite → (Values.fibre A γ).ncard ≤ N)
    (t : CanonicalRV.RVSort M) (ht : t.val ≠ iRVZero) :
    t.val ∈ smallNonempty A N ↔ gammaOf t ht ∈ finiteNonemptyValues A := by
  let F : Set M := {b | (![t.val], b) ∈ relation A}
  have hF : F = Subtype.val '' Values.fibre A (gammaOf t ht) := fibre_image_eq A hA t ht
  have hcount : ![t.val] ∉ RawClosure.Tuple.HasMore (relation A) N ↔ F.Finite ∧ F.ncard ≤ N := by
    change (¬ ∃ u : Fin (N + 1) → M, Function.Injective u ∧ ∀ i, u i ∈ F) ↔
      F.Finite ∧ F.ncard ≤ N
    exact no_inj_iff_finite_ncard_le (s := F) (k := N)
  change ((∃ b, (![t.val], b) ∈ relation A) ∧ ![t.val] ∉ RawClosure.Tuple.HasMore (relation A) N) ↔ _
  rw [hcount]
  change (F.Nonempty ∧ F.Finite ∧ F.ncard ≤ N) ↔
    (Values.fibre A (gammaOf t ht)).Nonempty ∧ (Values.fibre A (gammaOf t ht)).Finite
  rw [hF]
  constructor
  · rintro ⟨hne, hfin, hcard⟩
    exact ⟨Set.image_nonempty.mp hne, hfin.of_finite_image Subtype.val_injective.injOn⟩
  · rintro ⟨hne, hfin⟩
    refine ⟨hne.image _, hfin.image _, ?_⟩
    exact (Set.ncard_image_le hfin).trans (hbound (gammaOf t ht) hfin)

end SpecialTransformations.Section3.RawValueFibres

namespace SpecialTransformations.Section3.Values
open RawValueFibres
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem finite_nonempty_values_definable (h00 : M ⊨ Axioms.ACVF00)
    (S A : Set M) (hA : DefinableAt S .rv A) : GammaDefinable S (finiteNonemptyValues A) := by
  obtain ⟨N, hN⟩ := finite_value_fibres_uniform_bound h00 S A hA
  have he : gammaPullback (finiteNonemptyValues A) = smallNonempty A N := by
    ext t
    constructor
    · rintro ⟨hRV, h0, hfin⟩
      exact (smallNonempty_iff A hA.2 N hN ⟨t, hRV⟩ h0).mpr hfin
    · intro ht
      obtain ⟨b, hb⟩ := ht.1
      have hRV : iRV t := hb.1
      have h0 : t ≠ iRVZero := hb.2.1
      exact ⟨hRV, h0, (smallNonempty_iff A hA.2 N hN ⟨t, hRV⟩ h0).mp ht⟩
  unfold GammaDefinable
  rw [he]
  exact smallNonempty_definable S A hA N

/-- Lemma 3.15 on the actual non-infinity value quotient, over the original
S. Both finiteness and imaginary-sort definability are proved. There is no
uniform-bound, C-minimality-consequence, section or saturation input. -/
theorem lemma_3_15 (h00 : M ⊨ Axioms.ACVF00) (S A : Set M) (hA : DefinableAt S .rv A) :
    (finiteNonemptyValues A).Finite ∧ GammaDefinable S (finiteNonemptyValues A) :=
  ⟨finite_nonempty_values_finite h00 S A hA, finite_nonempty_values_definable h00 S A hA⟩

end SpecialTransformations.Section3.Values

namespace SpecialTransformations.Section3
export Values (lemma_3_15)
end SpecialTransformations.Section3
