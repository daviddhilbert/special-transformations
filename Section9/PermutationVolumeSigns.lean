import Section9.FiniteLiftReindexing
import Section9.GammaCompatibility
import Section4.CodeMaps

/-! Coordinate permutations preserve the total Gamma volume. Their
signs change the RV determinant through a parameter-free definable
multiplication by the RV class of one or minus one. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ} {S : Set M}
local notation "VF" => VFType (M := M)
local notation "RV" => CanonicalRV.RVSort M

theorem rvVolumeGamma_reindex (e : Equiv.Perm (Fin n)) (t : Fin n → RV)
    (ht : ∀ i, (t i).val ≠ iRVZero) :
    rvVolumeGamma (t ∘ e) (fun i => ht (e i)) = rvVolumeGamma t ht :=
  Equiv.prod_comp e (fun i => Values.gammaOf (t i) (ht i))

theorem vfPermSign_sq (e : Equiv.Perm (Fin n)) : (Equiv.Perm.sign e : VF) ^ 2 = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign e) with h | h <;> simp [h]

theorem vfPermSign_valuation {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation VF Γ) (e : Equiv.Perm (Fin n)) : v (Equiv.Perm.sign e : VF) = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign e) with h | h <;> simp [h]

private noncomputable def rvNegSignMap (S : Set M) :
    Map (DefSet.univ (rawRVSpace (M := M) 1) S) (DefSet.univ (rawRVSpace (M := M) 1) S) := by
  let Q := rawRVSpace (M := M) 1
  let a := CanonicalRV.encodedRv (-1 : VF)
  let F (x : Fin 1 → RV) := fun i => a * x i
  let c (z : Fin 1 → M) := fun i => iRVMul a.val (z i)
  have hOne : S.Definable₁ LRV {iVFOne} :=
    DefinableConstants.function_symbol (L := LRV) (A := S) Fn.vfOne Fin.elim0 (fun i => i.elim0)
  have hNeg : S.Definable₁ LRV {iVFNeg iVFOne} :=
    DefinableConstants.function_symbol Fn.vfNeg ![iVFOne] (fun i => by fin_cases i; exact hOne)
  have hRV : S.Definable₁ LRV {a.val} := by
    change S.Definable₁ LRV {iRv (iVFNeg iVFOne)}
    exact DefinableConstants.function_symbol Fn.rvMap ![iVFNeg iVFOne] (fun i => by fin_cases i; exact hNeg)
  have hd : S.DefinableMap LRV c := by
    intro i
    exact (Set.DefinableFun.of_empty (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.rvMul)).comp
      (show S.DefinableMap LRV (fun z : Fin 1 → M => ![a.val, z i]) from by
        intro j
        fin_cases j
        · exact DefinableConstants.constant hRV
        · exact Set.DefinableFun.proj LRV)
  have hcode (z : Q.domain) : rvValues (F (Q.decode z)) = c z.val := by
    funext i
    change (a * (Q.decode z) i).val = _
    rw [RVOperations.mul_val]
    exact congrArg (iRVMul a.val) (congrFun (rvValues_decode z) i)
  exact Map.ofCodes _ F c hd (fun z => ⟨F (Q.decode z), hcode z⟩)
    (fun z => rvValues_injective ((rvValues_decode ⟨c z.val, ⟨F (Q.decode z), hcode z⟩⟩).trans
      (hcode z).symm))

theorem exists_permutationSign_map (S : Set M) (e : Equiv.Perm (Fin n)) :
    ∃ F : Map (DefSet.univ (rawRVSpace (M := M) 1) S) (DefSet.univ (rawRVSpace (M := M) 1) S),
      ∀ a i, (F a).val i = CanonicalRV.encodedRv (Equiv.Perm.sign e : VF) * a.val i := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign e) with h | h
  · refine ⟨Map.id _, fun a i => ?_⟩
    simp [h, Map.id, RVOperations.oneRV_eq]
  · refine ⟨rvNegSignMap S, fun a i => ?_⟩
    rw [h, show ((↑(-1 : ℤˣ) : ℤ) : VF) = -1 by simp]
    rfl

end SpecialTransformations.Section9
