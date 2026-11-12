module

public import Section9.AffineTail
public import Section3.RingSyntax
public import Section3.DefinableConstants
public import Section3.SortedTuples

@[expose] public section

/-! The affine correction is definable by polynomial equations for
its slopes, including the required product. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {m : ℕ}
local notation "VF" => VFType (M := M)
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

abbrev AffineTailCode (m : ℕ) := (Fin 4 × Fin m) ⊕ Fin 1
public abbrev SlopeCode (m : ℕ) := AffineTailCode m ⊕ Fin m

public noncomputable def tailVar (k : Fin 4) (i : Fin m) : FreeCommRing (SlopeCode m) :=
  FreeCommRing.of (.inl (.inl (k,i)))

public noncomputable def slopeVar (i : Fin m) : FreeCommRing (SlopeCode m) := FreeCommRing.of (.inr i)

public noncomputable def zeroTerm (p : FreeCommRing (SlopeCode m)) : LRV.Term (SlopeCode m) :=
  RingSyntax.ofRingTerm (FirstOrder.Ring.termOfFreeCommRing p)

public noncomputable def slopeEquation (i : Fin m) : FreeCommRing (SlopeCode m) :=
  tailVar 0 i * slopeVar i - tailVar 1 i

public noncomputable def outputEquation (i : Fin m) : FreeCommRing (SlopeCode m) :=
  tailVar 3 i - (tailVar 1 i + slopeVar i * (tailVar 2 i - tailVar 0 i))

public noncomputable def productEquation : FreeCommRing (SlopeCode m) :=
  (∏ i, slopeVar i) - FreeCommRing.of (.inl (.inr 0))

public def affineTailArithmetic (j : Fin m) : Set (SlopeCode m → M) := {z |
  (∀ i, iVF (z i)) ∧ (∀ i ≠ j, (zeroTerm (slopeEquation i)).realize z = iVFZero) ∧
  (∀ i, (zeroTerm (outputEquation i)).realize z = iVFZero) ∧
  (zeroTerm productEquation).realize z = iVFZero}

def affineTailCorrectionCodes (j : Fin m) : Set (AffineTailCode m → M) :=
  (fun z => z ∘ Sum.inl) '' affineTailArithmetic j

theorem affineTailCorrectionCodes_definable (S : Set M) (j : Fin m) :
    S.Definable LRV (affineTailCorrectionCodes j) := by
  have hzero : S.DefinableFun LRV (fun _ : SlopeCode m → M => iVFZero) :=
    DefinableConstants.constant (DefinableConstants.function_symbol
      (L := LRV) Fn.vfZero Fin.elim0 (fun i => i.elim0))
  have he (p : FreeCommRing (SlopeCode m)) : S.Definable LRV
      {z | (zeroTerm p).realize z = iVFZero} :=
    ((zeroTerm p).definableFun_realize.mono (Set.empty_subset S)).ofPred_eq hzero
  have hs : S.Definable LRV {z : SlopeCode m → M | ∀ i, iVF (z i)} := by
    simp only [Set.ofPred_forall]
    exact Set.definable_iInter_of_finite (fun i =>
      ((definableAt_sort S .vf).raw_definable).preimage_comp (fun _ : Fin 1 => i))
  have hslopes : S.Definable LRV {z : SlopeCode m → M |
      ∀ i ≠ j, (zeroTerm (slopeEquation i)).realize z = iVFZero} := by
    have heq : {z : SlopeCode m → M | ∀ i ≠ j, (zeroTerm (slopeEquation i)).realize z = iVFZero} =
        ⋂ i : {i : Fin m // i ≠ j}, {z | (zeroTerm (slopeEquation i.val)).realize z = iVFZero} := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Subtype.forall]
    rw [heq]
    exact Set.definable_iInter_of_finite (fun i => he (slopeEquation i.val))
  have hout : S.Definable LRV {z : SlopeCode m → M |
      ∀ i, (zeroTerm (outputEquation i)).realize z = iVFZero} := by
    simp only [Set.ofPred_forall]
    exact Set.definable_iInter_of_finite (fun i => he (outputEquation i))
  exact (hs.inter (hslopes.inter (hout.inter (he productEquation)))).image_comp Sum.inl

def affineTailInputs (a b x y : Fin m → VF) (d : VF) : AffineTailCode m → VF :=
  Sum.elim (fun i => (![a,b,x,y] : Fin 4 → Fin m → VF) i.1 i.2) (fun _ => d)

theorem mem_affineTailCorrectionCodes_iff (j : Fin m) (a b x y : Fin m → VF) (d : VF) :
    (fun i => (affineTailInputs a b x y d i).val) ∈ affineTailCorrectionCodes j ↔
      ∃ c : Fin m → VF, (∀ i ≠ j, a i * c i = b i) ∧ (∏ i, c i) = d ∧
        affineTail a b c x = y := by
  let z := affineTailInputs a b x y d
  have he (c : Fin m → VF) (p : FreeCommRing (SlopeCode m)) :
      (zeroTerm p).realize (fun i => ((Sum.elim z c) i).val) = iVFZero ↔
        FreeCommRing.lift (Sum.elim z c) p = 0 := by
    rw [zeroTerm, RingSyntax.realizes, FirstOrder.Ring.realize_termOfFreeCommRing]
    change ((FreeCommRing.lift (Sum.elim z c) p : VF)).val = (0 : VF).val ↔ _
    exact Subtype.val_inj
  have ht (c : Fin m → VF) : (fun i => ((Sum.elim z c) i).val) ∈ affineTailArithmetic j ↔
      (∀ i ≠ j, a i * c i = b i) ∧ (∏ i, c i) = d ∧ affineTail a b c x = y := by
    let w (i : SlopeCode m) := ((Sum.elim z c) i).val
    have hS (i : Fin m) : (zeroTerm (slopeEquation i)).realize w = iVFZero ↔ a i * c i = b i := by
      rw [he]
      simp only [slopeEquation, tailVar, slopeVar, map_sub, map_mul, FreeCommRing.lift_of]
      change a i * c i - b i = 0 ↔ _
      exact sub_eq_zero
    have hO (i : Fin m) : (zeroTerm (outputEquation i)).realize w = iVFZero ↔ affineTail a b c x i = y i := by
      rw [he]
      simp only [outputEquation, tailVar, slopeVar, map_sub, map_add, map_mul, FreeCommRing.lift_of]
      change y i - (b i + c i * (x i - a i)) = 0 ↔ _
      exact sub_eq_zero.trans eq_comm
    have hP : (zeroTerm productEquation).realize w = iVFZero ↔ (∏ i, c i) = d := by
      rw [he]
      simp only [productEquation, slopeVar, map_sub, map_prod, FreeCommRing.lift_of]
      change (∏ i, c i) - d = 0 ↔ _
      exact sub_eq_zero
    change w ∈ affineTailArithmetic j ↔ _
    constructor
    · rintro ⟨_, hs, ho, hp⟩
      exact ⟨fun i hi => (hS i).mp (hs i hi), hP.mp hp, funext fun i => (hO i).mp (ho i)⟩
    · rintro ⟨hs, hp, ho⟩
      exact ⟨fun i => ((Sum.elim z c) i).property, fun i hi => (hS i).mpr (hs i hi),
        fun i => (hO i).mpr (congrFun ho i), hP.mpr hp⟩
  constructor
  · rintro ⟨w, hw, hEq⟩
    let c (i : Fin m) : VF := ⟨w (.inr i), hw.1 (.inr i)⟩
    have h : w = fun i => ((Sum.elim z c) i).val := by
      funext i
      cases i with
      | inl i => exact congrFun hEq i
      | inr i => rfl
    exact ⟨c, (ht c).mp (h ▸ hw)⟩
  · rintro ⟨c, hc⟩
    exact ⟨fun i => ((Sum.elim z c) i).val, (ht c).mpr hc, rfl⟩

end SpecialTransformations.Section9
