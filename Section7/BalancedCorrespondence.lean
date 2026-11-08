import Section7.LiftingDefinability
import Section4.RVZeroDeletion
import Section7.CorrespondenceLifting
import Section4.RVLabelCompression

section ZeroFibreDeletionProof

/-!
# Delete an absorbing RV coordinate and reinsert VF zero

The fibre of the absorbing element is exactly the singleton VF zero.
Deleting it preserves both existence and uniqueness in a lifted pair.
This is a fibrewise statement about the actual released sorts.
-/

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer

namespace SpecialTransformations.Section7

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem rawTupleFibre_deleteZero_iff {n : ℕ}
    (i : Fin (n + 1)) {t : Fin (n + 1) → M} (ht : t i = iRVZero)
    (a : Fin (n + 1) → M) :
    a ∈ rawTupleFibre t ↔
      a i = iVFZero ∧ a ∘ i.succAbove ∈ rawTupleFibre (t ∘ i.succAbove) := by
  constructor
  · intro ha
    exact ⟨RVCalc.vf_eq_zero_of_rv_eq_zero hM (ha i).1 ((ha i).2.trans ht),
      fun j => ha (i.succAbove j)⟩
  · rintro ⟨hzero, hrest⟩ j
    refine i.succAboveCases ?_ (fun k => ?_) j
    · rw [hzero, ht]
      exact ⟨Transfer.vf_zero_mem hM, RVCalc.rv_zero_eq hM⟩
    · exact hrest k

theorem existsUnique_deleteZero_iff {n : ℕ}
    (i : Fin (n + 1)) {t : Fin (n + 1) → M} (ht : t i = iRVZero)
    (P : (Fin n → M) → Prop) :
    (∃! a : Fin n → M, a ∈ rawTupleFibre (t ∘ i.succAbove) ∧ P a) ↔
      ∃! a : Fin (n + 1) → M, a ∈ rawTupleFibre t ∧ P (a ∘ i.succAbove) := by
  constructor
  · rintro ⟨a, ha, huniq⟩
    let a' : Fin (n + 1) → M := Fin.insertNth i iVFZero a
    have he : a' ∘ i.succAbove = a := funext (Fin.insertNth_apply_succAbove i _ _)
    have ha' : a' ∈ rawTupleFibre t := by
      apply (rawTupleFibre_deleteZero_iff i ht a').mpr
      rw [he]
      exact ⟨Fin.insertNth_apply_same i _ _, ha.1⟩
    refine ⟨a', ⟨ha', by rw [he]; exact ha.2⟩, ?_⟩
    rintro b ⟨hb, hPb⟩
    obtain ⟨hb0, hb'⟩ := (rawTupleFibre_deleteZero_iff i ht b).mp hb
    have h := huniq (b ∘ i.succAbove) ⟨hb', hPb⟩
    exact (Fin.insertNth_eq_iff.mpr ⟨hb0.symm, h.symm⟩).symm
  · rintro ⟨a, ha, huniq⟩
    obtain ⟨_, ha'⟩ := (rawTupleFibre_deleteZero_iff i ht a).mp ha.1
    refine ⟨a ∘ i.succAbove, ⟨ha', ha.2⟩, ?_⟩
    rintro b ⟨hb, hPb⟩
    let b' : Fin (n + 1) → M := Fin.insertNth i iVFZero b
    have he : b' ∘ i.succAbove = b := funext (Fin.insertNth_apply_succAbove i _ _)
    have hb' : b' ∈ rawTupleFibre t := by
      apply (rawTupleFibre_deleteZero_iff i ht b').mpr
      rw [he]
      exact ⟨Fin.insertNth_apply_same i _ _, hb⟩
    have h := huniq b' ⟨hb', by rwa [he]⟩
    rw [← he, h]

def deletePairCoordinates {n : ℕ} (i j : Fin (n + 1)) :
    Fin (n + n) → Fin ((n + 1) + (n + 1)) :=
  productTuple (productLeft (n + 1) (n + 1) ∘ i.succAbove)
    (productRight (n + 1) (n + 1) ∘ j.succAbove)

theorem productTuple_deletePairCoordinates {X : Type*} {n : ℕ}
    (i j : Fin (n + 1)) (a b : Fin (n + 1) → X) :
    productTuple a b ∘ deletePairCoordinates i j =
      productTuple (a ∘ i.succAbove) (b ∘ j.succAbove) := by
  apply productTuple_ext
  · intro k; simp [deletePairCoordinates, Function.comp_def]
  · intro k; simp [deletePairCoordinates, Function.comp_def]

theorem rawLiftDomain_deleteZero_pair {n : ℕ}
    (i j : Fin (n + 1)) (t s : Fin (n + 1) → M)
    (ht : t i = iRVZero) (hs : s j = iRVZero)
    (A : Set (Fin (n + n) → M))
    (h : productTuple (t ∘ i.succAbove) (s ∘ j.succAbove) ∈ rawLiftDomain A) :
    productTuple t s ∈ rawLiftDomain {x | x ∘ deletePairCoordinates i j ∈ A} := by
  have hproj {k : ℕ} (u w : Fin k → M) :
      productTuple u w ∘ productLeft k k = u ∧ productTuple u w ∘ productRight k k = w :=
    ⟨funext (productTuple_left u w), funext (productTuple_right u w)⟩
  have hshort := hproj (t ∘ i.succAbove) (s ∘ j.succAbove)
  have hlong := hproj t s
  simp only [rawLiftDomain, Set.mem_ofPred_eq, hshort.1, hshort.2] at h
  simp only [rawLiftDomain, Set.mem_ofPred_eq, hlong.1, hlong.2, productTuple_deletePairCoordinates]
  constructor
  · intro a ha
    exact (existsUnique_deleteZero_iff j hs
      (fun b => productTuple (a ∘ i.succAbove) b ∈ A)).mp
      (h.1 _ ((rawTupleFibre_deleteZero_iff i ht a).mp ha).2)
  · intro b hb
    exact (existsUnique_deleteZero_iff i ht
      (fun a => productTuple a (b ∘ j.succAbove) ∈ A)).mp
      (h.2 _ ((rawTupleFibre_deleteZero_iff j hs b).mp hb).2)

end SpecialTransformations.Section7

end ZeroFibreDeletionProof

section BalancedCorrespondenceProof

/-!
# Equal-weight correspondences, including the absorbing coordinates

The volume correspondence of an RV isomorphism can contain zero
coordinates. At equal weight the two sides have the same number of
zeros. The nonzero piece uses Theorem 7.6 directly. On the other
pieces delete one zero on each side and apply induction. The
deleted VF coordinates are forced to be zero.
-/

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section4

set_option backward.isDefEq.respectTransparency false

namespace SpecialTransformations.Section7

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

noncomputable def rawWeight {n : ℕ} (t : Fin n → M) : ℕ := by
  classical
  exact ∑ i, if t i ≠ iRVZero then 1 else 0

theorem rawWeight_insertZero {n : ℕ} (i : Fin (n + 1)) (t : Fin n → M) :
    rawWeight (Fin.insertNth i iRVZero t) = rawWeight t := by
  classical
  unfold rawWeight
  rw [Fin.sum_univ_succAbove _ i]
  simp

theorem rawWeight_le_arity {n : ℕ} (t : Fin n → M) : rawWeight t ≤ n := by
  classical
  unfold rawWeight
  calc
    _ ≤ ∑ _ : Fin n, 1 := Finset.sum_le_sum (fun i _ => by split_ifs <;> simp)
    _ = n := by simp

theorem rawWeight_le_pred_iff_zero {n : ℕ} (t : Fin (n + 1) → M) :
    rawWeight t ≤ n ↔ ∃ i, t i = iRVZero := by
  classical
  constructor
  · intro h
    by_contra hnone
    have hn (i : Fin (n + 1)) : t i ≠ iRVZero := fun hi => hnone ⟨i, hi⟩
    have he : rawWeight t = n + 1 := by simp [rawWeight, hn]
    rw [he] at h
    exact Nat.not_succ_le_self n h
  · rintro ⟨i, hi⟩
    have ht : Fin.insertNth i iRVZero (t ∘ i.succAbove) = t :=
      Fin.insertNth_eq_iff.mpr ⟨hi.symm, rfl⟩
    rw [← ht, rawWeight_insertZero]
    exact rawWeight_le_arity _

def padZeroPair {n : ℕ} (i j : Fin (n + 1)) (z : Fin (n + n) → M) :
    Fin ((n + 1) + (n + 1)) → M :=
  productTuple (Fin.insertNth i iRVZero (z ∘ productLeft n n))
    (Fin.insertNth j iRVZero (z ∘ productRight n n))

theorem padZeroPair_productTuple {n : ℕ} (i j : Fin (n + 1)) (a b : Fin n → M) :
    padZeroPair i j (productTuple a b) =
      productTuple (Fin.insertNth i iRVZero a) (Fin.insertNth j iRVZero b) := by
  rw [padZeroPair, show productTuple a b ∘ productLeft n n = a from funext (productTuple_left a b),
    show productTuple a b ∘ productRight n n = b from funext (productTuple_right a b)]

theorem padZeroPair_definable (S : Set M) {n : ℕ} (i j : Fin (n + 1)) :
    @Set.DefinableMap M LRV (CanonicalStructure.normalize (M := M))
      (Fin (n + n)) (Fin ((n + 1) + (n + 1))) S (padZeroPair i j) := by
  let N := CanonicalStructure.normalize (M := M)
  have hzero : @iRVZero M N = @iRVZero M sM :=
    @CanonicalStructure.normalize_fun M sM 0 Fn.rvZero Fin.elim0 (fun k => k.elim0)
  letI := N
  have hz : S.DefinableFun LRV (fun _ : Fin (n + n) → M => @iRVZero M sM) := by
    rw [← hzero]
    exact (Set.DefinableFun.of_empty (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.rvZero)).comp
      (show S.DefinableMap LRV (fun _ : Fin (n + n) → M => Fin.elim0) from fun k => k.elim0)
  intro k
  obtain ⟨l, rfl⟩ := finSumFinEquiv.surjective k
  cases l with
  | inl l =>
    change @Set.DefinableFun M LRV N (Fin (n + n)) S (fun z =>
      @padZeroPair M sM n i j z (productLeft (n + 1) (n + 1) l))
    refine i.succAboveCases ?_ (fun k => ?_) l
    · simpa only [padZeroPair, productTuple_left, Fin.insertNth_apply_same] using hz
    · simpa only [padZeroPair, productTuple_left, Fin.insertNth_apply_succAbove, Function.comp_apply] using
        (Set.DefinableFun.proj (A := S) LRV (i := productLeft n n k))
  | inr l =>
    change @Set.DefinableFun M LRV N (Fin (n + n)) S (fun z =>
      @padZeroPair M sM n i j z (productRight (n + 1) (n + 1) l))
    refine j.succAboveCases ?_ (fun k => ?_) l
    · simpa only [padZeroPair, productTuple_right, Fin.insertNth_apply_same] using hz
    · simpa only [padZeroPair, productTuple_right, Fin.insertNth_apply_succAbove, Function.comp_apply] using
        (Set.DefinableFun.proj (A := S) LRV (i := productRight n n k))

theorem zeroPadded_correspondence_definable (B : Base (M := M)) {n : ℕ}
    (i j : Fin (n + 1)) (C : Set (Fin ((n + 1) + (n + 1)) → M))
    (hC : DefinableOverBase B (fun _ => .rv) C) :
    DefinableOverBase B (fun _ => .rv) {z | padZeroPair i j z ∈ C} := by
  have h := hC.preimage_real_map (fun _ : Fin (n + n) => .rv) (padZeroPair i j)
    (padZeroPair_definable B.real i j)
  convert h using 1
  ext z
  refine ⟨fun hz => ⟨hz, ?_⟩, And.left⟩
  intro k
  obtain ⟨l, rfl⟩ := finSumFinEquiv.surjective k
  cases l with
  | inl l =>
    change sortEval .rv (z (productLeft n n l))
    have hp := hC.proper _ hz (productLeft (n + 1) (n + 1) (i.succAbove l))
    simpa only [padZeroPair, productTuple_left, Fin.insertNth_apply_succAbove, Function.comp_apply] using hp
  | inr l =>
    change sortEval .rv (z (productRight n n l))
    have hp := hC.proper _ hz (productRight (n + 1) (n + 1) (j.succAbove l))
    simpa only [padZeroPair, productTuple_right, Fin.insertNth_apply_succAbove, Function.comp_apply] using hp

theorem nonzeroRVTuple_definable (S : Set M) (n : ℕ) :
    DefinableOver S (fun _ : Fin n => .rv) {z | ∀ i, NonzeroRV (z i)} := by
  apply (definableOver_iff_normalized_raw S (fun _ : Fin n => .rv) _).mpr
  refine ⟨?_, fun _ hz i => (hz i).1⟩
  have h := nonzero_codes_normalized_definable (M := M) S
  letI := CanonicalStructure.normalize (M := M)
  rw [Set.ofPred_forall]
  exact Set.definable_iInter_of_finite fun i : Fin n =>
    h.preimage_comp (fun _ : Fin 1 => i)

theorem exists_balancedCorrespondence_lift {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hsat : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : Base (M := M)) (hsmall : Cardinal.mk B.real < κ) (hB : VFGammaGeneratedBase B)
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)
    (n : ℕ) (C : Set (Fin (n + n) → M)) (hC : DefinableOverBase B (fun _ => .rv) C)
    (hbal : ∀ t s, productTuple t s ∈ C → rawWeight t = rawWeight s)
    (hleft : ∀ b : Fin n → M, {a : Fin n → M | productTuple a b ∈ C}.Finite)
    (hright : ∀ a : Fin n → M, {b : Fin n → M | productTuple a b ∈ C}.Finite) :
    ∃ A : Set (Fin (n + n) → M), B.real.Definable LRV A ∧ C ⊆ rawLiftDomain A := by
  classical
  induction n with
  | zero =>
    obtain ⟨A, hA, _, hgood, _⟩ := theorem_7_6 hκ hsat h00 B hsmall hB v hv C hC
      (fun _ _ i => i.elim0) hleft hright
    exact ⟨A, hA, hgood⟩
  | succ n ih =>
    let N : Set (Fin ((n + 1) + (n + 1)) → M) := {z | ∀ i, NonzeroRV (z i)}
    let D := C ∩ N
    have hD : DefinableOverBase B (fun _ => .rv) D :=
      hC.inter (real_definableOverBase B _ N (nonzeroRVTuple_definable B.real _))
    obtain ⟨A₀, hA₀, _, hgood₀, _⟩ := theorem_7_6 hκ hsat h00 B hsmall hB v hv D hD
      (fun z hz i => (hz.2 i).2)
      (fun b => (hleft b).subset (fun _ hz => hz.1))
      (fun a => (hright a).subset (fun _ hz => hz.1))
    apply exists_gluedLift_of_gamma_definable hκ hsat B hsmall C hC
    intro z hz
    by_cases hz0 : ∀ i, z i ≠ iRVZero
    · exact ⟨A₀, hA₀, hgood₀ ⟨hz, fun i => ⟨by
        simpa only [sortEval, iRV] using hC.proper _ hz i, hz0 i⟩⟩⟩
    · let t := z ∘ productLeft (n + 1) (n + 1)
      let s := z ∘ productRight (n + 1) (n + 1)
      have hzip : productTuple t s = z := by
        apply productTuple_ext
        · intro i; exact productTuple_left t s i
        · intro j; exact productTuple_right t s j
      have hts : productTuple t s ∈ C := by rwa [hzip]
      have hw := hbal t s hts
      have hzero : (∃ i, t i = iRVZero) ∨ ∃ j, s j = iRVZero := by
        push Not at hz0
        obtain ⟨l, hl⟩ := hz0
        obtain ⟨k, rfl⟩ := finSumFinEquiv.surjective l
        cases k with
        | inl i => exact Or.inl ⟨i, hl⟩
        | inr j => exact Or.inr ⟨j, hl⟩
      have ht : ∃ i, t i = iRVZero := hzero.elim id (fun h =>
        (rawWeight_le_pred_iff_zero t).mp (hw.trans_le ((rawWeight_le_pred_iff_zero s).mpr h)))
      have hs : ∃ j, s j = iRVZero :=
        (rawWeight_le_pred_iff_zero s).mp (hw.symm.trans_le ((rawWeight_le_pred_iff_zero t).mpr ht))
      obtain ⟨i, hi⟩ := ht
      obtain ⟨j, hj⟩ := hs
      let C' : Set (Fin (n + n) → M) := {w | padZeroPair i j w ∈ C}
      have hC' : DefinableOverBase B (fun _ => .rv) C' :=
        zeroPadded_correspondence_definable B i j C hC
      have hbal' (a b : Fin n → M) (hab : productTuple a b ∈ C') :
          rawWeight a = rawWeight b := by
        change padZeroPair i j (productTuple a b) ∈ C at hab
        rw [padZeroPair_productTuple] at hab
        simpa only [rawWeight_insertZero] using hbal _ _ hab
      have hinsert (k : Fin (n + 1)) :
          Function.Injective (Fin.insertNth (α := fun _ : Fin (n + 1) => M) k iRVZero) := by
        intro a b he
        simpa only [Fin.removeNth_insertNth] using congrArg k.removeNth he
      have hleft' (b : Fin n → M) : {a : Fin n → M | productTuple a b ∈ C'}.Finite := by
        apply Set.Finite.of_injOn (f := Fin.insertNth i iRVZero) ?_ (hinsert i).injOn
          (hleft (Fin.insertNth j iRVZero b))
        intro a ha
        change padZeroPair i j (productTuple a b) ∈ C at ha
        rwa [padZeroPair_productTuple] at ha
      have hright' (a : Fin n → M) : {b : Fin n → M | productTuple a b ∈ C'}.Finite := by
        apply Set.Finite.of_injOn (f := Fin.insertNth j iRVZero) ?_ (hinsert j).injOn
          (hright (Fin.insertNth i iRVZero a))
        intro b hb
        change padZeroPair i j (productTuple a b) ∈ C at hb
        rwa [padZeroPair_productTuple] at hb
      obtain ⟨A, hA, hgood⟩ := ih C' hC' hbal' hleft' hright'
      have hshort : productTuple (t ∘ i.succAbove) (s ∘ j.succAbove) ∈ C' := by
        have he : Fin.insertNth i iRVZero (t ∘ i.succAbove) = t :=
          Fin.insertNth_eq_iff.mpr ⟨hi.symm, rfl⟩
        have hf : Fin.insertNth j iRVZero (s ∘ j.succAbove) = s :=
          Fin.insertNth_eq_iff.mpr ⟨hj.symm, rfl⟩
        change padZeroPair i j _ ∈ C
        rwa [padZeroPair_productTuple, he, hf]
      refine ⟨{x | x ∘ deletePairCoordinates i j ∈ A},
        hA.preimage_comp (deletePairCoordinates i j), ?_⟩
      rw [← hzip]
      exact rawLiftDomain_deleteZero_pair i j t s hi hj A (hgood hshort)

end SpecialTransformations.Section7

end BalancedCorrespondenceProof
