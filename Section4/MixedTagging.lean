module

public import Section4.VFAppend
public import Section4.RVTagging

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] {S : Set M} {n r m s : ℕ}

def mixedMapOfCode (A : DefSet (rawMixedSpace (M := M) n r) S)
    (f : (rawMixedSpace (M := M) n r).Carrier → (rawMixedSpace m s).Carrier)
    (F : (Fin n ⊕ Fin r → M) → Fin m ⊕ Fin s → M)
    (hF : S.DefinableMap LRV F)
    (hc : ∀ c : (rawMixedSpace (M := M) n r).domain,
      mixedValues (f ((rawMixedSpace n r).decode c)) = F c.val) :
    Map A (DefSet.univ (rawMixedSpace m s) S) := by
  refine Map.ofCodes A f F hF (fun c => ?_) ?_
  · rw [← hc c]
    exact mixedValues_mem_domain _
  · intro c
    apply mixedValues_injective
    exact (mixedValues_decode _).trans (hc c).symm

variable [hM : M ⊨ Axioms.ACVF]

def mixedLeftTag (m s : ℕ) (a : (rawMixedSpace (M := M) n r).Carrier) :
    (rawMixedSpace (M := M) (n + m) (1 + (r + s))).Carrier :=
  (vfAppend a.1 (fun _ => 0), rvLeftTag s a.2)

def mixedRightTag (n r : ℕ) (b : (rawMixedSpace (M := M) m s).Carrier) :
    (rawMixedSpace (M := M) (n + m) (1 + (r + s))).Carrier :=
  (vfAppend (fun _ => 0) b.1, rvRightTag r b.2)

theorem mixedLeftTag_injective (m s : ℕ) :
    Function.Injective (mixedLeftTag (M := M) (n := n) (r := r) m s) := by
  intro a b he
  apply Prod.ext
  · funext i
    simpa only [mixedLeftTag, vfAppend, Fin.append_left] using
      congrFun (congrArg Prod.fst he) (Fin.castAdd m i)
  · exact rvLeftTag_injective s (congrArg Prod.snd he)

theorem mixedRightTag_injective (n r : ℕ) :
    Function.Injective (mixedRightTag (M := M) (m := m) (s := s) n r) := by
  intro a b he
  apply Prod.ext
  · funext i
    simpa only [mixedRightTag, vfAppend, Fin.append_right] using
      congrFun (congrArg Prod.fst he) (Fin.natAdd n i)
  · exact rvRightTag_injective r (congrArg Prod.snd he)

theorem mixedTag_disjoint (a : (rawMixedSpace (M := M) n r).Carrier)
    (b : (rawMixedSpace (M := M) m s).Carrier) : mixedLeftTag m s a ≠ mixedRightTag n r b :=
  fun he => rvTag_disjoint a.2 b.2 (congrArg Prod.snd he)

theorem vfZeroCode_definable (S : Set M) {ι : Type} :
    S.DefinableFun LRV (fun _ : ι → M => iVFZero) :=
  (Set.DefinableFun.of_empty
    (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.vfZero)).comp
    (show S.DefinableMap LRV (fun _ : ι → M => Fin.elim0) from fun j => j.elim0)

def mixedLeftTagMap (A : DefSet (rawMixedSpace (M := M) n r) S) (m s : ℕ) :
    Map A (DefSet.univ (rawMixedSpace (n + m) (1 + (r + s))) S) := by
  let F (z : Fin n ⊕ Fin r → M) := Sum.elim
    (Fin.append (z ∘ Sum.inl) (fun _ : Fin m => iVFZero))
    (Fin.append (fun _ : Fin 1 => iRVZero)
      (Fin.append (z ∘ Sum.inr) (fun _ : Fin s => iRVZero)))
  apply mixedMapOfCode A (mixedLeftTag m s) F
  · intro i
    cases i with
    | inl i =>
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp only [F, Sum.elim_inl, Fin.append_left, Function.comp_apply]
        exact Set.DefinableFun.proj LRV
      · simpa only [F, Sum.elim_inl, Fin.append_right] using vfZeroCode_definable S
    | inr i =>
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simpa only [F, Sum.elim_inr, Fin.append_left, Bool.false_eq_true, ↓reduceIte] using
          rvConstantCode_definable S false
      · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
        · simp only [F, Sum.elim_inr, Fin.append_right, Fin.append_left, Function.comp_apply]
          exact Set.DefinableFun.proj LRV
        · simpa only [F, Sum.elim_inr, Fin.append_right, Bool.false_eq_true, ↓reduceIte] using
            rvConstantCode_definable S false
  · intro c
    have hc := mixedValues_decode c
    funext i
    cases i with
    | inl i =>
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simpa only [mixedValues, mixedLeftTag, vfValues, vfAppend, F,
          Sum.elim_inl, Fin.append_left, Function.comp_apply] using congrFun hc (.inl j)
      · simp only [mixedValues, mixedLeftTag, vfValues, vfAppend, F,
          Sum.elim_inl, Fin.append_right]
        rfl
    | inr i =>
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp only [mixedValues, mixedLeftTag, rvValues, rvLeftTag, F,
          Sum.elim_inr, Fin.append_left]
      · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
        · simpa only [mixedValues, mixedLeftTag, rvValues, rvLeftTag, rvAppend, F,
            Sum.elim_inr, Fin.append_right, Fin.append_left, Function.comp_apply]
            using congrFun hc (.inr j)
        · simp only [mixedValues, mixedLeftTag, rvValues, rvLeftTag, rvAppend, rvZeroTuple, F,
            Sum.elim_inr, Fin.append_right]

def mixedRightTagMap (B : DefSet (rawMixedSpace (M := M) m s) S) (n r : ℕ) :
    Map B (DefSet.univ (rawMixedSpace (n + m) (1 + (r + s))) S) := by
  let F (z : Fin m ⊕ Fin s → M) := Sum.elim
    (Fin.append (fun _ : Fin n => iVFZero) (z ∘ Sum.inl))
    (Fin.append (fun _ : Fin 1 => iRVOne)
      (Fin.append (fun _ : Fin r => iRVZero) (z ∘ Sum.inr)))
  apply mixedMapOfCode B (mixedRightTag n r) F
  · intro i
    cases i with
    | inl i =>
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simpa only [F, Sum.elim_inl, Fin.append_left] using vfZeroCode_definable S
      · simp only [F, Sum.elim_inl, Fin.append_right, Function.comp_apply]
        exact Set.DefinableFun.proj LRV
    | inr i =>
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simpa only [F, Sum.elim_inr, Fin.append_left, ↓reduceIte] using
          rvConstantCode_definable S true
      · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
        · simpa only [F, Sum.elim_inr, Fin.append_right, Fin.append_left,
            Bool.false_eq_true, ↓reduceIte] using rvConstantCode_definable S false
        · simp only [F, Sum.elim_inr, Fin.append_right, Function.comp_apply]
          exact Set.DefinableFun.proj LRV
  · intro c
    have hc := mixedValues_decode c
    funext i
    cases i with
    | inl i =>
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp only [mixedValues, mixedRightTag, vfValues, vfAppend, F,
          Sum.elim_inl, Fin.append_left]
        rfl
      · simpa only [mixedValues, mixedRightTag, vfValues, vfAppend, F,
          Sum.elim_inl, Fin.append_right, Function.comp_apply] using congrFun hc (.inl j)
    | inr i =>
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp only [mixedValues, mixedRightTag, rvValues, rvRightTag, F,
          Sum.elim_inr, Fin.append_left]
      · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
        · simp only [mixedValues, mixedRightTag, rvValues, rvRightTag, rvAppend, rvZeroTuple, F,
            Sum.elim_inr, Fin.append_right, Fin.append_left]
        · simpa only [mixedValues, mixedRightTag, rvValues, rvRightTag, rvAppend, F,
            Sum.elim_inr, Fin.append_right, Function.comp_apply] using congrFun hc (.inr j)

end SpecialTransformations.Section4

end
