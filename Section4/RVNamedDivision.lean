module

public import Section4.ResidueNormalization
public import Section4.RVCoordinates

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4.ResiduePurity

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n : ℕ}

def rvCoordinateDivide (s t : Fin n → CanonicalRV.RVSort M) :
    Fin n → CanonicalRV.RVSort M := fun i => t i / s i

/-- Coordinate division by named RV constants is a definable map on the
full RV sort, with its existing absorbing zero. -/
def rvNamedDivision (A : DefSet (rawRVSpace (M := M) n) S)
    (s : Fin n → CanonicalRV.RVSort M) (hs : ∀ i, (s i).val ∈ S) :
    Map A (DefSet.univ (rawRVSpace (M := M) n) S) := by
  let F (z : Fin n → M) : Fin n → M := fun i => iRVMul (z i) (iRVInvFn (s i).val)
  have hF : S.DefinableMap LRV F := by
    intro i
    have hc : S.DefinableFun LRV (fun _ : Fin n → M => (s i).val) :=
      Language.definableFun_const LRV (Fin n) (hs i)
    have hi := (Set.DefinableFun.of_empty
      (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.rvInv)).comp
        (show S.DefinableMap LRV (fun z : Fin n → M => ![(s i).val]) from
          fun j => by fin_cases j; exact hc)
    have hm := (Set.DefinableFun.of_empty
      (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.rvMul)).comp
        (show S.DefinableMap LRV
          (fun z : Fin n → M => ![z i, iRVInvFn (s i).val]) from
            fun j => by fin_cases j; exact Set.DefinableFun.proj LRV; exact hi)
    exact hm
  have hcode (c : (rawRVSpace (M := M) n).domain) :
      rvValues (rvCoordinateDivide s ((rawRVSpace n).decode c)) = F c.val := by
    funext i
    change (((rawRVSpace n).decode c i) / (s i)).val =
      iRVMul (c.val i) (iRVInvFn (s i).val)
    rw [div_eq_mul_inv, RVOperations.mul_val, RVOperations.inv_val]
    exact congrArg (fun x => iRVMul x (iRVInvFn (s i).val)) (congrFun (rvValues_decode c) i)
  refine Map.ofCodes A (rvCoordinateDivide s) F hF
    (fun c => ⟨rvCoordinateDivide s ((rawRVSpace n).decode c), hcode c⟩) ?_
  intro c
  apply rvValues_injective
  exact (rvValues_decode _).trans (hcode c).symm

theorem rvNamedDivision_injective (A : DefSet (rawRVSpace (M := M) n) S)
    (s : Fin n → CanonicalRV.RVSort M) (hs : ∀ i, (s i).val ∈ S)
    (hval : ∀ t ∈ A.carrier, ∀ i, Values.vrv (t i) = Values.vrv (s i)) :
    Function.Injective (rvNamedDivision A s hs) := by
  intro a b he
  apply Subtype.ext
  funext i
  by_cases hsi : s i = 0
  · exact (eq_zero_of_sameValue_zero (hval _ a.property i) hsi).trans
      (eq_zero_of_sameValue_zero (hval _ b.property i) hsi).symm
  · apply (div_left_inj' hsi).mp
    exact congrFun (congrArg Subtype.val he) i

theorem rvNamedDivision_toImage_bijective (A : DefSet (rawRVSpace (M := M) n) S)
    (s : Fin n → CanonicalRV.RVSort M) (hs : ∀ i, (s i).val ∈ S)
    (hval : ∀ t ∈ A.carrier, ∀ i, Values.vrv (t i) = Values.vrv (s i)) :
    Function.Bijective (rvNamedDivision A s hs).toImage := by
  constructor
  · intro a b he
    apply rvNamedDivision_injective A s hs hval
    exact Subtype.ext (congrArg (fun x : (rvNamedDivision A s hs).image => x.val) he)
  · rintro ⟨_, a, rfl⟩
    exact ⟨a, rfl⟩

theorem rvNamedDivision_dimension (A : DefSet (rawRVSpace (M := M) n) S)
    (s : Fin n → CanonicalRV.RVSort M) (hs : ∀ i, (s i).val ∈ S)
    (hval : ∀ t ∈ A.carrier, ∀ i, Values.vrv (t i) = Values.vrv (s i)) :
    rvDim (rvNamedDivision A s hs).image = rvDim A :=
  (rvDim_eq_of_bijective _ (rvNamedDivision_toImage_bijective A s hs hval)).symm

theorem rvNamedDivision_image_eq (A : DefSet (rawRVSpace (M := M) n) S)
    (s : Fin n → CanonicalRV.RVSort M) (hs : ∀ i, (s i).val ∈ S)
    (hval : ∀ t ∈ A.carrier, ∀ i, Values.vrv (t i) = Values.vrv (s i)) :
    (rvNamedDivision A s hs).image.carrier =
      (fun x : Fin n → ModelResidue M => residueRV ∘ x) '' normalizedResidueSet A s := by
  ext u
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨residueNormalize s t.val, residueNormalize_mem A s hval t, ?_⟩
    funext i
    exact residueRV_part (residue_ratio_inK (hval _ t.property i))
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨residueScale s x, hx.1⟩, ?_⟩
    funext i
    change (s i * residueRV (x i)) / s i = residueRV (x i)
    by_cases hsi : s i = 0
    · rw [hsi, zero_mul, div_zero, hx.2 i hsi, residueRV_zero]
    · exact mul_div_cancel_left₀ _ hsi

end SpecialTransformations.Section4.ResiduePurity

end
