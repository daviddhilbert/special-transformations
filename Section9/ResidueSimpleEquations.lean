module

public import Section4.ResiduePolynomialCover
public import Section4.PureFieldAlgebraicity
public import Section9.GlobalSimpleRootEquations
public import Section7.TupleCoordinates

@[expose] public section

/-! Residue correspondences admit one global equation for each output
coordinate. Removing repeated factors gives simple roots over independent
input coordinates. Each row involves the input and just one output. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language MvPolynomial
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4.ResiduePurity
open SpecialTransformations.Section4 SpecialTransformations.Section7

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}

private def outputSelection (i : Fin n) : Fin n ⊕ Unit → Fin (n + n) :=
  Sum.elim (productLeft n n) (fun _ => productRight n n i)

private theorem outputSelection_injective (i : Fin n) :
    Function.Injective (outputSelection i) := by
  rintro (a | a) (b | b) h
  · exact congrArg Sum.inl ((productLeft n n).injective h)
  · exact (productLeft_ne_right a i h).elim
  · exact (productLeft_ne_right b i h.symm).elim
  · exact congrArg Sum.inr (Subsingleton.elim a b)

private def oneOutputEquiv (n : ℕ) : Fin n ⊕ Unit ≃ Fin (n + 1) := by
  let e : Unit ≃ Fin 1 :=
    { toFun := fun _ => 0
      invFun := fun _ => ()
      left_inv := fun _ => Subsingleton.elim _ _
      right_inv := fun _ => Subsingleton.elim _ _ }
  exact (_root_.Equiv.sumCongr (_root_.Equiv.refl (Fin n)) e).trans finSumFinEquiv

private theorem exists_residue_simple_equations_of_dependent_selections [CharZero (ModelResidue M)]
    {κ : Cardinal} (hs : Saturated M κ) (B : LRV.Substructure M) (hB : Cardinal.mk B < κ)
    (C : Set (Fin (n + n) → ModelResidue M)) (hC : Relative.Def (residueParameterField B) C)
    (hdep : ∀ z ∈ C, ∀ i : Fin n,
      ¬ AlgebraicIndependent (residueParameterField B) (z ∘ outputSelection i)) :
    ∃ P : Fin n → MvPolynomial (Fin (n + n)) (residueParameterField B),
      (∀ z ∈ C, ∀ i, aeval z (P i) = 0) ∧
      (∀ i j : Fin n, j ≠ i → pderiv (productRight n n j) (P i) = 0) ∧
      ∀ z ∈ C, AlgebraicIndependent (residueParameterField B) (z ∘ productLeft n n) →
        ∀ i, aeval z (pderiv (productRight n n i) (P i)) ≠ 0 := by
  classical
  let E := residueParameterField B
  let e := oneOutputEquiv n
  let select (i : Fin n) := outputSelection i ∘ e.symm
  have hdep' (i : Fin n) (z : Fin (n + n) → ModelResidue M) (hz : z ∈ C) :
      ¬ AlgebraicIndependent E (z ∘ select i) := by
    intro h
    apply hdep z hz i
    have h' := h.comp e e.injective
    simpa only [select, Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id] using h'
  choose P hP hPzero using fun i => exists_residue_polynomial_vanishing_on_selection hs B hB C hC
    (select i) (hdep' i)
  let Q (i : Fin n) := rename e.symm (P i)
  have hQ (i : Fin n) : Q i ≠ 0 := fun h =>
    hP i (rename_injective _ e.symm.injective (h.trans (map_zero (rename e.symm)).symm))
  choose R hR hRs using fun i => exists_global_simpleRoot_mvPolynomial (K := ModelResidue M) (Q i) (hQ i)
  let L := productLeft n n
  let O := productRight n n
  have hzCode (z : Fin (n + n) → ModelResidue M) (i : Fin n) :
      z ∘ outputSelection i = Sum.elim (z ∘ L) (fun _ => z (O i)) := by
    funext j
    cases j <;> rfl
  have hzQ (z : Fin (n + n) → ModelResidue M) (hz : z ∈ C) (i : Fin n) :
      aeval (z ∘ outputSelection i) (Q i) = 0 := by
    change aeval (z ∘ outputSelection i) (rename e.symm (P i)) = 0
    rw [aeval_rename, aeval_def]
    exact hPzero i z hz
  refine ⟨fun i => rename (outputSelection i) (R i), ?_, ?_, ?_⟩
  · intro z hz i
    rw [aeval_rename, hzCode]
    exact hR i _ _ (by simpa only [hzCode] using hzQ z hz i)
  · intro i j hj
    apply pderiv_rename_eq_zero_of_notMem_range
    rintro ⟨a | a, he⟩
    · exact productLeft_ne_right a j he
    · exact hj ((productRight n n).injective he).symm
  · intro z hz hx i
    have hi : outputSelection i (.inr ()) = O i := rfl
    change aeval z (pderiv (O i) (rename (outputSelection i) (R i))) ≠ 0
    rw [← hi, pderiv_rename (outputSelection_injective i), aeval_rename, hzCode]
    exact hRs i _ _ hx (by simpa only [hzCode] using hzQ z hz i)

attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

theorem finite_residue_row_coordinate_isAlgebraic
    {K : Type} [Field K] [IsAlgClosed K] (E : Subfield K)
    (C : Set (Fin (n + n) → K)) (hC : (E : Set K).Definable Language.ring C)
    (x y : Fin n → K) (hxy : productTuple x y ∈ C)
    (hfin : {u : Fin n → K | productTuple x u ∈ C}.Finite) (i : Fin n) :
    IsAlgebraic (tupleField E x) (y i) := by
  let F := tupleField E x
  let D := {u : Fin n → K | productTuple x u ∈ C}
  have hmap : (F : Set K).DefinableMap Language.ring (fun u : Fin n → K => productTuple x u) := by
    intro j
    obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
    cases j with
    | inl j =>
      change (F : Set K).DefinableFun Language.ring (fun u => productTuple x u (productLeft n n j))
      simpa only [productTuple_left] using
        (Language.ring.definableFun_const (Fin n) (A := (F : Set K)) (tuple_mem_tupleField E x j))
    | inr j =>
      change (F : Set K).DefinableFun Language.ring (fun u => productTuple x u (productRight n n j))
      simpa only [productTuple_right] using
        (Set.DefinableFun.proj (A := (F : Set K)) Language.ring (i := j))
  have hD : (F : Set K).Definable Language.ring D :=
    (hC.mono (le_tupleField E x)).preimage_map hmap
  let Y := (fun y : Fin n → K => y i) '' D
  have hY : (F : Set K).Definable₁ Language.ring Y := by
    change (F : Set K).Definable Language.ring {z : Fin 1 → K | z 0 ∈ Y}
    convert hD.image_comp (fun _ : Fin 1 => i) using 1
    ext z
    constructor
    · rintro ⟨b, hb, he⟩
      exact ⟨b, hb, funext fun j => by fin_cases j; exact he⟩
    · rintro ⟨b, hb, he⟩
      exact ⟨b, hb, congrFun he 0⟩
  exact finite_field_definable_isAlgebraic F Y hY (hfin.image _) (y i) ⟨y, hxy, rfl⟩

/-- Finite rows of a residue correspondence give global polynomial
equations whose output block is diagonal and nonsingular at every
independent input. -/
theorem exists_residue_simple_equations [CharZero (ModelResidue M)]
    {κ : Cardinal} (hs : Saturated M κ) (B : LRV.Substructure M) (hB : Cardinal.mk B < κ)
    (C : Set (Fin (n + n) → ModelResidue M)) (hC : Relative.Def (residueParameterField B) C)
    (hfin : ∀ x : Fin n → ModelResidue M, {y | productTuple x y ∈ C}.Finite) :
    ∃ P : Fin n → MvPolynomial (Fin (n + n)) (residueParameterField B),
      (∀ z ∈ C, ∀ i, aeval z (P i) = 0) ∧
      (∀ i j : Fin n, j ≠ i → pderiv (productRight n n j) (P i) = 0) ∧
      ∀ z ∈ C, AlgebraicIndependent (residueParameterField B) (z ∘ productLeft n n) →
        ∀ i, aeval z (pderiv (productRight n n i) (P i)) ≠ 0 := by
  let E := residueParameterField B
  letI : IsAlgClosed (VFType (M := M)) := VFAlgClosed.isAlgClosed_vfType
  letI : IsAlgClosed (ModelResidue M) :=
    ValOneEC.Johnson.isAlgClosed_residueField Values.presentationValuation
  apply exists_residue_simple_equations_of_dependent_selections hs B hB C hC
  intro z hz i hind
  let x := z ∘ productLeft n n
  let y := z ∘ productRight n n
  have he : productTuple x y = z := by
    apply productTuple_ext
    · intro j; exact productTuple_left x y j
    · intro j; exact productTuple_right x y j
  have hy := finite_residue_row_coordinate_isAlgebraic E C hC x y (he.symm ▸ hz) (hfin x) i
  obtain ⟨P, hP, hs⟩ := exists_simpleRoot_equation_of_tupleField E x (y i) hy
  have hcode : z ∘ outputSelection i = Sum.elim x (fun _ => y i) := by
    funext j
    cases j <;> rfl
  rw [hcode] at hind
  rw [hind.eq_zero_of_aeval_eq_zero P hP, map_zero, map_zero] at hs
  exact hs rfl

end SpecialTransformations.Section9
