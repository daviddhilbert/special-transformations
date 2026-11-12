module

public import Section4.RVAppend
public import Section4.FiniteGluing

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M} {n m : ℕ}

/-- The finite RV code-map specialization. The supplied point function
already lands in the actual RV sort, so its codes prove the target guard. -/
def rvMapOfCode (A : DefSet (rawRVSpace (M := M) n) S)
    (f : (Fin n → CanonicalRV.RVSort M) → Fin m → CanonicalRV.RVSort M)
    (F : (Fin n → M) → Fin m → M) (hF : S.DefinableMap LRV F)
    (hc : ∀ c : (rawRVSpace (M := M) n).domain,
      rvValues (f ((rawRVSpace n).decode c)) = F c.val) :
    Map A (DefSet.univ (rawRVSpace m) S) := by
  refine Map.ofCodes A f F hF (fun c => ⟨f ((rawRVSpace n).decode c), hc c⟩) ?_
  intro c
  apply rvValues_injective
  exact (rvValues_decode _).trans (hc c).symm

def rvZeroTuple (n : ℕ) : Fin n → CanonicalRV.RVSort M :=
  fun _ => ⟨iRVZero, rv_zero_mem hM⟩

def rvLeftTag (m : ℕ) (t : Fin n → CanonicalRV.RVSort M) :
    Fin (1 + (n + m)) → CanonicalRV.RVSort M :=
  Fin.append (fun _ : Fin 1 => ⟨iRVZero, rv_zero_mem hM⟩) (rvAppend t (rvZeroTuple m))

def rvRightTag (n : ℕ) (t : Fin m → CanonicalRV.RVSort M) :
    Fin (1 + (n + m)) → CanonicalRV.RVSort M :=
  Fin.append (fun _ : Fin 1 => ⟨iRVOne, rv_one_mem hM⟩) (rvAppend (rvZeroTuple n) t)

theorem rvLeftTag_injective (m : ℕ) : Function.Injective (rvLeftTag (M := M) (n := n) m) := by
  intro t u he
  funext i
  simpa only [rvLeftTag, rvAppend, Fin.append_right, Fin.append_left] using
    congrFun he (Fin.natAdd 1 (Fin.castAdd m i))

theorem rvRightTag_injective (n : ℕ) : Function.Injective (rvRightTag (M := M) (m := m) n) := by
  intro t u he
  funext i
  simpa only [rvRightTag, rvAppend, Fin.append_right] using
    congrFun he (Fin.natAdd 1 (Fin.natAdd n i))

theorem rvTag_disjoint (t : Fin n → CanonicalRV.RVSort M)
    (u : Fin m → CanonicalRV.RVSort M) : rvLeftTag m t ≠ rvRightTag n u := by
  intro he
  have hz : iRVZero (M := M) = iRVOne := by
    simpa only [rvLeftTag, rvRightTag, Fin.append_left] using
      congrArg (fun x : CanonicalRV.RVSort M => x.val)
        (congrFun he (Fin.castAdd (n + m) (0 : Fin 1)))
  exact RVCalc.rv_one_ne_zero hM hz.symm

theorem rvConstantCode_definable (S : Set M) {ι : Type} (b : Bool) :
    S.DefinableFun LRV (fun _ : ι → M => if b then iRVOne else iRVZero) := by
  cases b
  · exact (Set.DefinableFun.of_empty
      (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.rvZero)).comp
      (show S.DefinableMap LRV (fun _ : ι → M => Fin.elim0) from fun j => j.elim0)
  · exact (Set.DefinableFun.of_empty
      (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.rvOne)).comp
      (show S.DefinableMap LRV (fun _ : ι → M => Fin.elim0) from fun j => j.elim0)

def rvLeftTagMap (A : DefSet (rawRVSpace (M := M) n) S) (m : ℕ) :
    Map A (DefSet.univ (rawRVSpace (1 + (n + m))) S) := by
  let F (z : Fin n → M) := Fin.append (fun _ : Fin 1 => iRVZero)
    (Fin.append z (fun _ : Fin m => iRVZero))
  apply rvMapOfCode A (rvLeftTag m) F
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [F, Fin.append_left, Bool.false_eq_true, ↓reduceIte] using
        rvConstantCode_definable (M := M) S (ι := Fin n) false
    · refine Fin.addCases (fun k => ?_) (fun k => ?_) j
      · simpa only [F, Fin.append_right, Fin.append_left] using
          (Set.DefinableFun.proj (M := M) (L := LRV) (A := S) (i := k))
      · simpa only [F, Fin.append_right, Bool.false_eq_true, ↓reduceIte] using
          rvConstantCode_definable (M := M) S (ι := Fin n) false
  · intro c
    have hc := rvValues_decode c
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [rvValues, rvLeftTag, F, Fin.append_left]
    · refine Fin.addCases (fun k => ?_) (fun k => ?_) j
      · simpa only [rvValues, rvLeftTag, rvAppend, F, Fin.append_right, Fin.append_left] using
          congrFun hc k
      · simp only [rvValues, rvLeftTag, rvAppend, rvZeroTuple, F, Fin.append_right]

def rvRightTagMap (B : DefSet (rawRVSpace (M := M) m) S) (n : ℕ) :
    Map B (DefSet.univ (rawRVSpace (1 + (n + m))) S) := by
  let F (z : Fin m → M) := Fin.append (fun _ : Fin 1 => iRVOne)
    (Fin.append (fun _ : Fin n => iRVZero) z)
  apply rvMapOfCode B (rvRightTag n) F
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [F, Fin.append_left, ↓reduceIte] using
        rvConstantCode_definable (M := M) S (ι := Fin m) true
    · refine Fin.addCases (fun k => ?_) (fun k => ?_) j
      · simpa only [F, Fin.append_right, Fin.append_left, Bool.false_eq_true, ↓reduceIte] using
          rvConstantCode_definable (M := M) S (ι := Fin m) false
      · simpa only [F, Fin.append_right] using
          (Set.DefinableFun.proj (M := M) (L := LRV) (A := S) (i := k))
  · intro c
    have hc := rvValues_decode c
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [rvValues, rvRightTag, F, Fin.append_left]
    · refine Fin.addCases (fun k => ?_) (fun k => ?_) j
      · simp only [rvValues, rvRightTag, rvAppend, rvZeroTuple, F, Fin.append_right, Fin.append_left]
      · simpa only [rvValues, rvRightTag, rvAppend, F, Fin.append_right] using congrFun hc k

end SpecialTransformations.Section4

end
