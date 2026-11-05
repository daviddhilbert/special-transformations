import RVCalc

set_option backward.isDefEq.respectTransparency false

/-! The guarded formula originally used to audit the inverse-free transcription.
Its syntax and semantics also apply to the author-corrected language with RV
inversion. The historical note concerns only the earlier inverse-free language;
this file does not assert that the current QE target is false.
-/

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer

namespace RVRatioFormula

/-- Bound indices are A=0, B=1, C=2, u=3, v=4. -/
def body : Bf 5 :=
  pUnits &3 ⊓ (pUnits &4 ⊓
    (pEq (tRVMul &0 &3) &1 ⊓
      (pEq (tRVMul &0 &4) &2 ⊓ pEq (tKAdd &3 tRVOne) &4)))

/-- There are units u,v with A*u=B, A*v=C, and u+1=v in the residue field. -/
def ratioFormula : Bf 3 := exSorted .rv (exSorted .rv body)

theorem body_wellSorted :
    WellSorted (fun e : Empty => e.elim) (fun _ : Fin 5 => .rv) body := by
  unfold body
  refine wellSorted_inf _ _ (wellSorted_pUnitsG _ _ (by rfl)) ?_
  refine wellSorted_inf _ _ (wellSorted_pUnitsG _ _ (by rfl)) ?_
  refine wellSorted_inf _ _ ?_ ?_
  · exact wellSorted_pEqG (s := .rv) _ _ ((tmSort_rvMul _ _).mpr ⟨rfl, rfl⟩) rfl
  · refine wellSorted_inf _ _ ?_ ?_
    · exact wellSorted_pEqG (s := .rv) _ _ ((tmSort_rvMul _ _).mpr ⟨rfl, rfl⟩) rfl
    · exact wellSorted_pEqG (s := .rv) _ _
        ((tmSort_kAdd _ _).mpr ⟨rfl, tmSort_rvOne _ _⟩) rfl

theorem ratioFormula_wellSorted :
    WellSorted (fun e : Empty => e.elim) (fun _ : Fin 3 => .rv) ratioFormula := by
  unfold ratioFormula
  apply wellSorted_exSorted
  apply wellSorted_exSorted
  have hs : Fin.snoc (Fin.snoc (fun _ : Fin 3 => SortTag.rv) SortTag.rv) SortTag.rv =
      (fun _ : Fin 5 => SortTag.rv) := by
    funext i; fin_cases i <;> rfl
  rw [hs]
  exact body_wellSorted

section Semantics

variable {M : Type} [LRV.Structure M]

theorem realize_exSorted_rv {n : ℕ} (φ : Bf (n+1)) (xs : Fin n → M) :
    (exSorted .rv φ).Realize (default : Empty → M) xs ↔
      ∃ a : M, iRV a ∧ φ.Realize (default : Empty → M) (Fin.snoc xs a) := by
  simp only [exSorted, BoundedFormula.realize_ex, BoundedFormula.realize_inf,
    sortPred, pRVsort_realize]
  apply exists_congr
  intro a
  refine and_congr ?_ Iff.rfl
  change iRV ((Fin.snoc xs a : Fin (n+1) → M) (Fin.last n)) ↔ iRV a
  rw [Fin.snoc_last]

theorem body_realize (a b c u v : M) :
    body.Realize (default : Empty → M) ![a, b, c, u, v] ↔
      iUnits u ∧ (iUnits v ∧
        (iRVMul a u = b ∧ (iRVMul a v = c ∧ iKAdd u iRVOne = v))) := by
  simp [body, BoundedFormula.realize_inf, pUnits_realize, pEq,
    BoundedFormula.realize_bdEqual, realize_tRVMul, TrivCase.realize_tKAdd,
    realize_tRVOne_T, realize_tv]

theorem ratioFormula_realize (a b c : M) :
    ratioFormula.Realize (default : Empty → M) ![a, b, c] ↔
      ∃ u : M, iRV u ∧ ∃ v : M, iRV v ∧
        iUnits u ∧ (iUnits v ∧
          (iRVMul a u = b ∧ (iRVMul a v = c ∧ iKAdd u iRVOne = v))) := by
  unfold ratioFormula
  rw [realize_exSorted_rv]
  apply exists_congr
  intro u
  refine and_congr Iff.rfl ?_
  rw [realize_exSorted_rv]
  apply exists_congr
  intro v
  refine and_congr Iff.rfl ?_
  have ht : (Fin.snoc (Fin.snoc ![a, b, c] u) v : Fin 5 → M) = ![a, b, c, u, v] := by
    funext i; fin_cases i <;> rfl
  rw [ht]
  exact body_realize a b c u v

end Semantics

/-!
## Historical audit of the inverse-free transcription (not formalized below)

The author has since confirmed that RV inversion is a function, and that
symbol is now included in the local encoding. The term-normal-form argument
in this historical note applies only to the preceding inverse-free signature.

Work in an equicharacteristic-zero algebraically closed nontrivially valued
field with residue-field elements x,y algebraically independent over Q. Choose
an RV element t of strictly positive value, and compare the RV triples

    (t, x*t, (x+1)*t)    and    (t, x*t, y*t).

Here x,y denote the residue units inside RV, and t is nonzero. Every correctly
sorted VF term over three RV variables is a closed integer term. By induction,
every RV term at either triple is zero or a monomial c*A^i*B^j*C^k with
c a nonzero integer and i,j,k natural numbers. Indeed, every positive-degree
monomial lies outside K; the frozen kJunkZero/kNegJunkZero axioms collapse
residue operations on such inputs to zero. Operations at degree zero only
combine the integer constants.

The value of a nonzero monomial is (i+j+k)*value(t). At equal total degree,
equality of two evaluated monomials reduces to multiplicative dependence of
x,x+1, respectively x,y, over Q*. Both pairs are multiplicatively independent:
for x,x+1 this follows from the distinct polynomial factors X and X+1 and the
transcendence of x; for x,y it follows from algebraic independence. Thus the
two triples satisfy exactly the same quantifier-free formulas. Unit membership
and the order relation only see whether the degree is zero and its size.

The formula above holds at the first triple and fails at the second: cancellation
forces u=x and v=x+1, respectively v=y. Therefore this argument obstructs full
QE in the literal inverse-free signature with the frozen junk conventions.
An RV inverse symbol would make the comparison of the two unit ratios available
in a quantifier-free formula.

The paper explicitly omits inverse symbols and subsequently assumes substructure
RV parts are groups: https://arxiv.org/pdf/1006.1393, page 3. Passing from a
multiplicative submonoid to its group closure does not automatically preserve
residue addition of new unit ratios. The present Lean declarations establish
only the displayed formula's sortedness and semantic meaning; formal construction
of the models and the term-normal-form argument remains separate work.
-/

end RVRatioFormula

#print axioms RVRatioFormula.ratioFormula_wellSorted
#print axioms RVRatioFormula.body_realize
#print axioms RVRatioFormula.ratioFormula_realize
