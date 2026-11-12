module

public import Section3.GammaRVSeparation

@[expose] public section

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section3.GammaParameters.EndpointLogic

noncomputable section

namespace SpecialTransformations.Section4.GammaSyntax

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {ι υ : Type} [Finite ι] [Finite υ] {S : Set M}

def Proper (a : ι → M) : Prop := ∀ i, NonzeroRV (a i)

def decode (a : ι → M) : ι → Values.Gamma (M := M) := fun i => codeValue (a i)

/-- A predicate on the actual Gamma imaginary is definable precisely when
its full guarded real-code preimage is definable. All representatives remain. -/
def Definable (S : Set M) (P : (ι → Values.Gamma (M := M)) → Prop) : Prop :=
  @Set.Definable M S LRV (CanonicalStructure.normalize (M := M)) ι
    {a | Proper a ∧ P (decode a)}

theorem proper_definable (S : Set M) :
    @Set.Definable M S LRV (CanonicalStructure.normalize (M := M)) ι
      {a | Proper a} := by
  have hp := nonzero_codes_normalized_definable (M := M) S
  change @Set.Definable M S LRV (CanonicalStructure.normalize (M := M)) ι
    {a | ∀ i, NonzeroRV (a i)}
  rw [Set.ofPred_forall]
  letI := CanonicalStructure.normalize (M := M)
  exact Set.definable_iInter_of_finite (fun i => hp.preimage_comp (fun _ : Fin 1 => i))

theorem Definable.true_ (S : Set M) : Definable (ι := ι) S (fun _ => True) := by
  simpa only [Definable, and_true] using proper_definable (M := M) (ι := ι) S

theorem Definable.congr {P Q : (ι → Values.Gamma (M := M)) → Prop}
    (hp : Definable S P) (h : ∀ a, P a ↔ Q a) : Definable S Q := by
  have he : P = Q := funext (fun a => propext (h a))
  rwa [← he]

theorem Definable.forall_finite {β : Type} [Finite β]
    {P : β → (ι → Values.Gamma (M := M)) → Prop}
    (hp : ∀ b, Definable S (P b)) : Definable S (fun a => ∀ b, P b a) := by
  have hg := proper_definable (M := M) (ι := ι) S
  have hall : @Set.Definable M S LRV (CanonicalStructure.normalize (M := M)) ι
      {a | ∀ b, Proper a ∧ P b (decode a)} := by
    rw [Set.ofPred_forall]
    letI := CanonicalStructure.normalize (M := M)
    exact Set.definable_iInter_of_finite hp
  have h := @Set.Definable.inter M S LRV (CanonicalStructure.normalize (M := M)) ι _ _ hg hall
  change @Set.Definable M S LRV (CanonicalStructure.normalize (M := M)) ι _
  convert h using 1
  ext a
  change (Proper a ∧ ∀ b, P b (decode a)) ↔ (Proper a ∧ ∀ b, Proper a ∧ P b (decode a))
  exact ⟨fun h => ⟨h.1, fun b => ⟨h.1, h.2 b⟩⟩,
    fun h => ⟨h.1, fun b => (h.2 b).2⟩⟩

theorem Definable.and {P Q : (ι → Values.Gamma (M := M)) → Prop}
    (hp : Definable S P) (hq : Definable S Q) : Definable S (fun a => P a ∧ Q a) := by
  have h := @Set.Definable.inter M S LRV (CanonicalStructure.normalize (M := M)) ι _ _ hp hq
  change @Set.Definable M S LRV (CanonicalStructure.normalize (M := M)) ι _
  convert h using 1
  ext a
  change (Proper a ∧ P (decode a) ∧ Q (decode a)) ↔
    ((Proper a ∧ P (decode a)) ∧ Proper a ∧ Q (decode a))
  tauto

theorem Definable.not {P : (ι → Values.Gamma (M := M)) → Prop}
    (hp : Definable S P) : Definable S (fun a => ¬ P a) := by
  have hg := proper_definable (M := M) (ι := ι) S
  have h := @Set.Definable.inter M S LRV (CanonicalStructure.normalize (M := M)) ι _ _ hg
    (@Set.Definable.compl M S LRV (CanonicalStructure.normalize (M := M)) ι _ hp)
  change @Set.Definable M S LRV (CanonicalStructure.normalize (M := M)) ι _
  convert h using 1
  ext a
  change (Proper a ∧ ¬ P (decode a)) ↔ (Proper a ∧ ¬ (Proper a ∧ P (decode a)))
  tauto

theorem Definable.or {P Q : (ι → Values.Gamma (M := M)) → Prop}
    (hp : Definable S P) (hq : Definable S Q) : Definable S (fun a => P a ∨ Q a) := by
  have h := @Set.Definable.union M S LRV (CanonicalStructure.normalize (M := M)) ι _ _ hp hq
  change @Set.Definable M S LRV (CanonicalStructure.normalize (M := M)) ι _
  convert h using 1
  ext a
  change (Proper a ∧ (P (decode a) ∨ Q (decode a))) ↔
    ((Proper a ∧ P (decode a)) ∨ (Proper a ∧ Q (decode a)))
  tauto

theorem Definable.imp {P Q : (ι → Values.Gamma (M := M)) → Prop}
    (hp : Definable S P) (hq : Definable S Q) : Definable S (fun a => P a → Q a) := by
  simpa only [imp_iff_not_or] using hp.not.or hq

theorem Definable.iff {P Q : (ι → Values.Gamma (M := M)) → Prop}
    (hp : Definable S P) (hq : Definable S Q) : Definable S (fun a => P a ↔ Q a) := by
  simpa only [iff_def] using (hp.imp hq).and (hq.imp hp)

theorem Definable.reindex {P : (ι → Values.Gamma (M := M)) → Prop}
    (hp : Definable S P) (f : ι → υ) : Definable S (fun a => P (a ∘ f)) := by
  have hg := proper_definable (M := M) (ι := υ) S
  have h := @Set.Definable.inter M S LRV (CanonicalStructure.normalize (M := M)) υ _ _ hg
    (@Set.Definable.preimage_comp M S LRV (CanonicalStructure.normalize (M := M)) ι υ f _ hp)
  change @Set.Definable M S LRV (CanonicalStructure.normalize (M := M)) υ _
  convert h using 1
  ext a
  change (Proper a ∧ P (decode a ∘ f)) ↔
    (Proper a ∧ Proper (a ∘ f) ∧ P (decode (a ∘ f)))
  have he : decode (a ∘ f) = decode a ∘ f := rfl
  rw [he]
  exact ⟨fun h => ⟨h.1, fun i => h.1 (f i), h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩

theorem Definable.exists_block {P : (ι ⊕ υ → Values.Gamma (M := M)) → Prop}
    (hp : Definable S P) :
    Definable S (fun a => ∃ b : υ → Values.Gamma (M := M), P (Sum.elim a b)) := by
  have h := @Set.Definable.exists_of_finite M S LRV
    (CanonicalStructure.normalize (M := M)) ι υ inferInstance _ hp
  change @Set.Definable M S LRV (CanonicalStructure.normalize (M := M)) ι _
  convert h using 1
  ext a
  change (Proper a ∧ ∃ b, P (Sum.elim (decode a) b)) ↔
    ∃ b : υ → M, Proper (Sum.elim a b) ∧ P (decode (Sum.elim a b))
  constructor
  · rintro ⟨ha, b, hb⟩
    choose c hc hcv using fun i => codeValue_surjective (b i)
    refine ⟨c, ?_, ?_⟩
    · intro i
      cases i with
      | inl i => exact ha i
      | inr i => exact hc i
    · have he : decode (Sum.elim a c) = Sum.elim (decode a) b := by
        funext i
        cases i with
        | inl i => rfl
        | inr i => exact hcv i
      rwa [he]
  · rintro ⟨b, hab, hp⟩
    have he : decode (Sum.elim a b) = Sum.elim (decode a) (decode b) := by
      funext i
      cases i <;> rfl
    exact ⟨fun i => hab (.inl i), decode b, he ▸ hp⟩

theorem Definable.forall_block {P : (ι ⊕ υ → Values.Gamma (M := M)) → Prop}
    (hp : Definable S P) :
    Definable S (fun a => ∀ b : υ → Values.Gamma (M := M), P (Sum.elim a b)) := by
  simpa only [not_exists, not_not] using hp.not.exists_block.not

theorem lt_definable (S : Set M) (i j : ι) :
    Definable S (fun a : ι → Values.Gamma (M := M) => a i < a j) := by
  have hl := codeLt_definable (M := M) S
  have hg := proper_definable (M := M) (ι := ι) S
  have h := @Set.Definable.inter M S LRV (CanonicalStructure.normalize (M := M)) ι _ _ hg
    (@Set.Definable.preimage_comp M S LRV (CanonicalStructure.normalize (M := M))
      (Fin 2) ι (![i,j] : Fin 2 → ι) _ hl)
  change @Set.Definable M S LRV (CanonicalStructure.normalize (M := M)) ι _
  convert h using 1
  ext a
  change (Proper a ∧ codeValue (a i) < codeValue (a j)) ↔
    (Proper a ∧ codeLt (a i) (a j))
  exact and_congr_right (fun ha => (codeLt_iff _ _ (ha i) (ha j)).symm)

theorem eq_definable (S : Set M) (i j : ι) :
    Definable S (fun a : ι → Values.Gamma (M := M) => a i = a j) := by
  exact ((lt_definable S i j).not.and (lt_definable S j i).not).congr
    (fun a => ⟨fun h => le_antisymm (le_of_not_gt h.2) (le_of_not_gt h.1),
      fun h => by rw [h]; exact ⟨lt_irrefl _, lt_irrefl _⟩⟩)

theorem mem_gammaPullback_iff (A : Set (Values.Gamma (M := M))) (a : M) :
    a ∈ Values.gammaPullback A ↔ NonzeroRV a ∧ codeValue a ∈ A := by
  constructor
  · rintro ⟨ha, h0, hA⟩
    refine ⟨⟨ha, h0⟩, ?_⟩
    simpa only [codeValue, dif_pos (show NonzeroRV a from ⟨ha, h0⟩), value] using hA
  · rintro ⟨ha, hA⟩
    refine ⟨ha.1, ha.2, ?_⟩
    simpa only [codeValue, dif_pos ha, value] using hA

theorem scalar_definable_iff (A : Set (Values.Gamma (M := M))) :
    Definable S (fun a : Fin 1 → Values.Gamma (M := M) => a 0 ∈ A) ↔
      Values.GammaDefinable S A := by
  have he : {a : Fin 1 → M | Proper a ∧ decode a 0 ∈ A} =
      {a | a 0 ∈ Values.gammaPullback A} := by
    ext a
    change (Proper a ∧ decode a 0 ∈ A) ↔ a 0 ∈ Values.gammaPullback A
    rw [mem_gammaPullback_iff]
    change ((∀ i, NonzeroRV (a i)) ∧ codeValue (a 0) ∈ A) ↔ _
    have hi : (∀ i : Fin 1, NonzeroRV (a i)) ↔ NonzeroRV (a 0) := by
      exact ⟨fun h => h 0, fun h i => by fin_cases i; exact h⟩
    rw [hi]
  change @Set.Definable M S LRV (CanonicalStructure.normalize (M := M)) (Fin 1) _ ↔ _
  rw [he]
  exact ⟨fun h => (definableAt_iff_normalized_raw S .rv _).mpr
    ⟨h, fun _ h => h.choose⟩,
    fun h => ((definableAt_iff_normalized_raw S .rv _).mp h).1⟩

theorem unary_at {A : Set (Values.Gamma (M := M))}
    (hA : Values.GammaDefinable S A) (i : ι) :
    Definable S (fun a : ι → Values.Gamma (M := M) => a i ∈ A) :=
  ((scalar_definable_iff A).mpr hA).reindex (fun _ : Fin 1 => i)

end SpecialTransformations.Section4.GammaSyntax

end
