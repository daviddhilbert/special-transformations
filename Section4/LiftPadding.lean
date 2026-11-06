import Section4.CanonicalLift
import Section4.RVPadding
import Section4.MapCorestrict
import Mathlib.Data.Fin.Tuple.Basic

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

@[simp] theorem padVF_succ_castSucc (a : Fin k → VFType (M := M)) (i : Fin k) :
    padVF (Nat.le_succ k) a i.castSucc = a i := by
  simp [padVF, i.isLt]

@[simp] theorem padVF_succ_last (a : Fin k → VFType (M := M)) :
    padVF (Nat.le_succ k) a (Fin.last k) = 0 := by
  simp [padVF]

theorem tupleRV_padVF (a : Fin k → VFType (M := M)) :
    tupleRV (padVF (Nat.le_succ k) a) = padRV (tupleRV a) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · apply Subtype.ext
    simp only [tupleRV, padVF_succ_last, padRV, Fin.snoc_last]
    exact (CanonicalRV.encodedRv_zero_iff 0).mpr rfl
  · simp only [tupleRV, padVF_succ_castSucc, padRV, Fin.snoc_castSucc]

def rvLiftPaddingMap (U : RVObject (M := M) S k) :
    Map (rvLift U) (rvLift (rvPadObject U)) :=
  ((vfPadding (Nat.le_succ k) (rawRVSpace U.arity) S).restrict
    (Set.subset_univ _)).corestrict (by
      intro a
      obtain ⟨u, hu, hv⟩ := a.property
      refine ⟨u, hu, ?_⟩
      change padRV (U.value u) = tupleRV (padVF (Nat.le_succ k) a.val.1)
      rw [tupleRV_padVF, hv])

theorem rvLiftPaddingMap_bijective (U : RVObject (M := M) S k) :
    Function.Bijective (rvLiftPaddingMap U) := by
  constructor
  · intro a b he
    apply Subtype.ext
    apply Prod.ext
    · apply padVF_injective (Nat.le_succ k)
      exact congrArg (fun p : rvLift (rvPadObject U) => p.val.1) he
    · exact congrArg (fun p : rvLift (rvPadObject U) => p.val.2) he
  · intro b
    obtain ⟨u, hu, hv⟩ := b.property
    change padRV (U.value u) = tupleRV b.val.1 at hv
    have hz : b.val.1 (Fin.last k) = 0 := by
      apply (CanonicalRV.encodedRv_zero_iff _).mp
      have he := congrArg (fun t : CanonicalRV.RVSort M => t.val) (congrFun hv (Fin.last k))
      simpa only [padRV, Fin.snoc_last, tupleRV, CanonicalRV.encodedRv] using he.symm
    have hfirst : U.value u = tupleRV (Fin.init b.val.1) := by
      funext i
      simpa only [padRV, Fin.snoc_castSucc, tupleRV, Fin.init] using congrFun hv i.castSucc
    let a : rvLift U := ⟨(Fin.init b.val.1, b.val.2), u, hu, hfirst⟩
    refine ⟨a, Subtype.ext (Prod.ext ?_ rfl)⟩
    change padVF (Nat.le_succ k) (Fin.init b.val.1) = b.val.1
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [padVF_succ_last, hz]
    · rw [padVF_succ_castSucc]
      rfl

/-- Padding an RV label adds one forced zero VF coordinate to its lift,
so the two actual lifts are definably isomorphic in the ambient VF category. -/
def rvLiftPaddingIso (Γ : DefinableGeometry.Space LRV M) (U : RVObject (M := M) S k) :
    (rvLiftObject Γ U).obj ≅ (rvLiftObject Γ (rvPadObject U)).obj :=
  DefinableSetCat.isoOfBijective (rvLiftPaddingMap U) (rvLiftPaddingMap_bijective U)

end SpecialTransformations.Section4

end
