import Section9.AffineTailDefinability
import Section9.AffineTailCorrection
import Section8.UnaryGerm

/-! The guarded affine map is definable over the parameters of the
head map and of the representatives. Its extra scalar is eliminated. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section8

namespace SpecialTransformations.Section9

variable {M Γ : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable [LinearOrderedCommGroupWithZero Γ] {m : ℕ}
local notation "VF" => VFType (M := M)
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

abbrev AffineHeadCode (m : ℕ) := (Fin 4 × Fin m) ⊕ Fin 2
private abbrev InputCode (m : ℕ) := AffineHeadCode m ⊕ Fin 1

private def tailIndex : AffineTailCode m → InputCode m :=
  Sum.elim (Sum.inl ∘ Sum.inl) Sum.inr

private noncomputable def aProduct : FreeCommRing (InputCode m) := ∏ i : Fin m, FreeCommRing.of (.inl (.inl (0,i)))
private noncomputable def bProduct : FreeCommRing (InputCode m) := ∏ i : Fin m, FreeCommRing.of (.inl (.inl (1,i)))
private def headDet : FreeCommRing (InputCode m) := FreeCommRing.of (.inl (.inr 0))
private def desiredDet : FreeCommRing (InputCode m) := FreeCommRing.of (.inl (.inr 1))
private def slopeProduct : FreeCommRing (InputCode m) := FreeCommRing.of (.inr 0)

private noncomputable def term (p : FreeCommRing (InputCode m)) : LRV.Term (InputCode m) :=
  RingSyntax.ofRingTerm (FirstOrder.Ring.termOfFreeCommRing p)

private def guard : Set (InputCode m → M) := {z |
  (term headDet).realize z ≠ iVFZero ∧ termValueEq (term (headDet * bProduct)) (term (desiredDet * aProduct)) z}

private def inputs (j : Fin m) : Set (InputCode m → M) :=
  {z | iVF (z (.inr 0))} ∩ (fun z => z ∘ tailIndex) ⁻¹' affineTailCorrectionCodes j ∩
  ((guard ∩ {z | (term (headDet * slopeProduct)).realize z = (term desiredDet).realize z}) ∪
    (guardᶜ ∩ {z | (term (aProduct * slopeProduct)).realize z = (term bProduct).realize z}))

def affineTailHeadCodes (j : Fin m) : Set (AffineHeadCode m → M) :=
  (fun z => z ∘ Sum.inl) '' inputs j

theorem affineTailHeadCodes_definable (S : Set M) (j : Fin m) :
    S.Definable LRV (affineTailHeadCodes j) := by
  have ht (p : FreeCommRing (InputCode m)) : S.DefinableFun LRV ((term p).realize : (InputCode m → M) → M) :=
    (term p).definableFun_realize.mono (Set.empty_subset S)
  have hzero : S.DefinableFun LRV (fun _ : InputCode m → M => iVFZero) :=
    DefinableConstants.constant (DefinableConstants.function_symbol
      (L := LRV) Fn.vfZero Fin.elim0 (fun i => i.elim0))
  have hguard : S.Definable LRV (guard (m := m)) :=
    ((ht headDet).ofPred_eq hzero).compl.inter (termValueEq_definable S _ _)
  have hVF := ((definableAt_sort S .vf).raw_definable).preimage_comp (fun _ : Fin 1 => (Sum.inr 0 : InputCode m))
  have hTail := (affineTailCorrectionCodes_definable S j).preimage_comp tailIndex
  exact ((hVF.inter hTail).inter ((hguard.inter ((ht _).ofPred_eq (ht _))).union
    (hguard.compl.inter ((ht _).ofPred_eq (ht _))))).image_comp Sum.inl

def affineHeadInputs (a b x y : Fin m → VF) (D c : VF) : AffineHeadCode m → VF :=
  Sum.elim (fun i => (![a,b,x,y] : Fin 4 → Fin m → VF) i.1 i.2) ![D,c]

theorem mem_affineTailHeadCodes_iff
    (v : Valuation VF Γ) (hv : ∀ a b : VF, VFValued.predV a b ↔ v a ≤ v b)
    (j : Fin m) (a b x y : Fin m → VF) (D c : VF)
    (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0) :
    (fun i => (affineHeadInputs a b x y D c i).val) ∈ affineTailHeadCodes j ↔
      affineTail a b (affineTailSlopesForHead v a b j D c) x = y := by
  classical
  let z := affineHeadInputs a b x y D c
  let A := ∏ i, a i
  let B := ∏ i, b i
  have hA : A ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => ha i
  have hvA : v A ≠ 0 := v.ne_zero_iff.mpr hA
  let w (d : VF) (i : InputCode m) : M := ((Sum.elim z (fun _ => d)) i).val
  have he (d : VF) (p : FreeCommRing (InputCode m)) :
      (term p).realize (w d) = (FreeCommRing.lift (Sum.elim z (fun _ : Fin 1 => d)) p : VF).val := by
    change (term p).realize (fun i => ((Sum.elim z (fun _ : Fin 1 => d)) i).val) = _
    rw [term, RingSyntax.realizes, FirstOrder.Ring.realize_termOfFreeCommRing]
  have hg (d : VF) : w d ∈ guard ↔ affineTailCorrectionGood v a b D c := by
    change _ ∧ termValueEq _ _ _ ↔ _
    rw [termValueEq_realize, he, he, he]
    simp only [headDet, desiredDet, aProduct, bProduct, map_mul, map_prod, FreeCommRing.lift_of]
    have hL : FreeCommRing.lift (Sum.elim z (fun _ : Fin 1 => d)) (headDet * bProduct) = D * B := by
      simp only [headDet, bProduct, map_mul, map_prod, FreeCommRing.lift_of]
      rfl
    have hR : FreeCommRing.lift (Sum.elim z (fun _ : Fin 1 => d)) (desiredDet * aProduct) = c * A := by
      simp only [desiredDet, aProduct, map_mul, map_prod, FreeCommRing.lift_of]
      rfl
    simp only [headDet, desiredDet, aProduct, bProduct, map_mul, map_prod, FreeCommRing.lift_of] at hL hR
    rw [hL, hR]
    have h₀ : D.val ≠ iVFZero ↔ v D ≠ 0 := by
      change D.val ≠ (0 : VF).val ↔ _
      exact (not_congr Subtype.val_inj).trans v.ne_zero_iff.symm
    have hvalue : (iLe (iRv (D * B).val) (iRv (c * A).val) ∧
        iLe (iRv (c * A).val) (iRv (D * B).val)) ↔ v (D * B) = v (c * A) := by
      change (VFValued.predV (c * A) (D * B) ∧ VFValued.predV (D * B) (c * A)) ↔ _
      rw [hv, hv]
      exact ⟨fun h => le_antisymm h.2 h.1, fun h => ⟨h.ge, h.le⟩⟩
    have hD : (Sum.elim z (fun _ : Fin 1 => d) (.inl (.inr 0))) = D := rfl
    rw [hD, h₀, hvalue]
    unfold affineTailCorrectionGood
    apply and_congr_right
    intro _
    have hratio : (∏ i, v (b i) / v (a i)) = v B / v A := by
      simp only [A, B, map_prod, Finset.prod_div_distrib]
    rw [hratio, ← mul_div_assoc, div_eq_iff hvA]
    rw [map_mul, map_mul]
  have htail (d : VF) : w d ∘ tailIndex ∈ affineTailCorrectionCodes j ↔
      ∃ s : Fin m → VF, (∀ i ≠ j, a i * s i = b i) ∧ (∏ i, s i) = d ∧ affineTail a b s x = y := by
    have hcode : w d ∘ tailIndex = fun i => (affineTailInputs a b x y d i).val := by
      funext i
      rcases i with i | i <;> rfl
    rw [hcode]
    exact mem_affineTailCorrectionCodes_iff j a b x y d
  have hprod (d : VF) :
      ((term (headDet * slopeProduct)).realize (w d) = (term desiredDet).realize (w d) ↔ D * d = c) ∧
      ((term (aProduct * slopeProduct)).realize (w d) = (term bProduct).realize (w d) ↔ A * d = B) := by
    simp only [he, headDet, desiredDet, slopeProduct, aProduct, bProduct, map_mul, map_prod, FreeCommRing.lift_of]
    exact ⟨Subtype.val_inj, Subtype.val_inj⟩
  have hmem : (fun i => (z i).val) ∈ affineTailHeadCodes j ↔ ∃ d : VF, w d ∈ inputs j := by
    constructor
    · rintro ⟨q, hq, hq'⟩
      let d : VF := ⟨q (.inr 0), hq.1.1⟩
      have h : q = w d := by
        funext i
        rcases i with i | i
        · exact congrFun hq' i
        · fin_cases i
          rfl
      exact ⟨d, h ▸ hq⟩
    · rintro ⟨d, hd⟩
      exact ⟨w d, hd, rfl⟩
  rw [hmem]
  have hd (d : VF) : w d ∈ inputs j ↔
      (∃ s : Fin m → VF, (∀ i ≠ j, a i * s i = b i) ∧ (∏ i, s i) = d ∧ affineTail a b s x = y) ∧
      ((affineTailCorrectionGood v a b D c ∧ D * d = c) ∨
        (¬ affineTailCorrectionGood v a b D c ∧ A * d = B)) := by
    change (iVF (w d (.inr 0)) ∧ w d ∘ tailIndex ∈ affineTailCorrectionCodes j) ∧ _ ↔ _
    simp only [inputs, Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_setOf_eq,
      hg, htail, (hprod d).1, (hprod d).2, w, Sum.elim_inr, d.property, true_and]
  simp only [hd]
  by_cases h : affineTailCorrectionGood v a b D c
  · have hD : D ≠ 0 := v.ne_zero_iff.mp h.1
    have hdval : v (c / D) = ∏ i, v (b i) / v (a i) := by
      rw [map_div₀]
      exact (div_eq_iff h.1).mpr (h.2.symm.trans (mul_comm _ _))
    simp only [affineTailSlopesForHead, if_pos h, h, true_and, not_true_eq_false, false_and, or_false]
    constructor
    · rintro ⟨d, ⟨s, hs, hp, heq⟩, hDprod⟩
      have hval : d = c / D := (eq_div_iff hD).mpr ((mul_comm _ _).trans hDprod)
      rw [← eq_affineTailSlopes_of_equations a b s j _ ha hb hs (hp.trans hval)]
      exact heq
    · intro hy
      exact ⟨c / D, ⟨affineTailSlopes a b j (c / D), fun i hi => by
        rw [affineTailSlopes_eq_of_ne _ _ _ _ hi, mul_comm, div_mul_cancel₀ _ (ha i)],
        (affineTailSlopes_spec v a b j _ ha hb hdval).1, hy⟩, by rw [mul_comm, div_mul_cancel₀ _ hD]⟩
  · let s (i : Fin m) := b i / a i
    have hS (i : Fin m) : a i * s i = b i := by
      rw [show s i = b i / a i from rfl, mul_comm, div_mul_cancel₀ _ (ha i)]
    have hprodS : A * (∏ i, s i) = B := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun i _ => hS i
    simp only [affineTailSlopesForHead, if_neg h, h, false_and, not_false_eq_true, true_and, false_or]
    constructor
    · rintro ⟨d, ⟨s', hs, hp, heq⟩, hd'⟩
      have he : d = ∏ i, s i := mul_left_cancel₀ hA (hd'.trans hprodS.symm)
      have h1 := eq_affineTailSlopes_of_equations a b s' j _ ha hb hs (hp.trans he)
      have h2 := eq_affineTailSlopes_of_equations a b s j _ ha hb (fun i _ => hS i) rfl
      rw [h1.trans h2.symm] at heq
      exact heq
    · intro hy
      exact ⟨_, ⟨s, fun i _ => hS i, rfl, hy⟩, hprodS⟩

end SpecialTransformations.Section9
