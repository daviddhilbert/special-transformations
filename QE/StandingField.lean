/-
**The residue field of a model of the frozen `ACVF`, `K = Kˣ ∪ {0}`, as a Mathlib `Field`.**

`QE/PaperRoute.lean`'s Lemma-3.3 decomposition consumes `K(M)` and `K(N)` as fields (the
`ClassicalProps.ACFExtendsAlgebraicEmbeddings` quote operates on them).  This file supplies them:

* `KOf M : Type` — the residue elements `{x : M // iUnits x ∨ x = iRVZero}`;
* closure under `iKAdd`, `TrivCase.iKNeg`, `iRVMul` from the sort-closure axioms `sdKAdd`, `sdKNeg`,
  `sdKMul` (each is `pInK`-in, `pInK`-out);
* `Field (KOf M)` from `Axioms.kField`, which states the field axioms of Definition 2.2 item 3
  *relativized to `K`* — additive associativity/commutativity/neutrality/inverses, multiplicative
  associativity/commutativity/neutrality, distributivity, `0 ≠ 1`, and invertibility of every
  nonzero element.

Extraction: `Jm2.allSortedK_realize` (`QE/Jm2T1.lean`) for the `K`-guarded axioms;
`TrivCase.pInK_realize` for `pInK`; the unit side of the inverse is witnessed at `M`, which lies
in the whole model, so `Field.inv`'s `Classical.choose` is sound at `M`.
-/
import RVCalc
import Standing
import Jm2T1

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
open SpecialTransformations.Milestone0.LRV

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace SpecialTransformations.Milestone0.StandingField

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- The residue elements of the `RV` sort: `K = Kˣ ∪ {0}` — units and the residue zero. -/
def KOf (M : Type) [LRV.Structure M] : Type := {x : M // iUnits x ∨ x = iRVZero}

/-- `/K = Kˣ ∪ {0}` as a predicate on `M`. -/
abbrev pInKof (a : M) : Prop := iUnits a ∨ a = iRVZero

/-- Zero of the residue field. -/
def KZero : KOf M := ⟨iRVZero, Or.inr rfl⟩

/-- One of the residue field. -/
noncomputable def KOne : KOf M := ⟨iRVOne, Or.inl (StandingTree.rv_one_units (M := M))⟩

/-- Realise the sorted side of `allSortedK` at all-`.rv` tuples of residue elements. -/
private theorem iRV_tup {k : ℕ} (x : Fin k → M) (hK : ∀ i, pInKof (x i)) :
    ∀ i, (match (fun _ : Fin k => SortTag.rv) i with
      | SortTag.rv => iRV (x i)
      | SortTag.vf => iVF (x i)) := by
  intro i
  exact Jm2.iRV_of_inK (hK i)

/-- Extract one `K`-guarded `pEq` from `Axioms.kField`. -/
private theorem eq_of_allSortedK {k : ℕ} {a b : LRV.Tm k}
    (hmem : LRV.allSortedK (fun _ : Fin k => SortTag.rv) (pEq a b) ∈ Axioms.ACVF)
    (x : Fin k → M) (hK : ∀ i, pInKof (x i)) :
    a.realize (Sum.elim (default : Empty → M) x) = b.realize (Sum.elim (default : Empty → M) x) := by
  have h := Jm2.allSortedK_realize (T := Axioms.ACVF) hM (ss := (fun _ : Fin k => SortTag.rv))
    (φ := pEq a b) hmem x (iRV_tup x hK) hK
  simpa only [pEq, BoundedFormula.realize_bdEqual] using h

/-- Membership of the `kField` axioms in `ACVF`. -/
private theorem mem_ACVF_kField {s : LRV.Sentence} (h : s ∈ Axioms.kField) :
    s ∈ Axioms.ACVF := by
  simp only [Axioms.ACVF, Axioms.ACVFpaper, Set.mem_union] at *
  tauto

/-- `kField` axiom membership by unfolding the one-variable `ofList` item (`.rv`-tag of
`asList`-form: every in-list item is allSortedK at `.rv`). -/
private theorem mem_ofList_kField1 (φ : LRV.BoundedFormula Empty 1 → LRV.Sentence)
    (h : (fun _ : Fin 1 => SortTag.rv) = (fun _ : Fin 1 => SortTag.rv)) : True := trivial

/-- The element of `![x]` at index `0` is `x`. -/
private theorem head1 (a : M) : (![a] : Fin 1 → M) 0 = a := rfl

/-- The element of `![a, b]` at indices. -/
private theorem head2 (a b : M) : (![a, b] : Fin 2 → M) 0 = a := rfl
private theorem tail2 (a b : M) : (![a, b] : Fin 2 → M) 1 = b := rfl
private theorem head3 (a b c : M) : (![a, b, c] : Fin 3 → M) 0 = a := rfl
private theorem mid3 (a b c : M) : (![a, b, c] : Fin 3 → M) 1 = b := rfl
private theorem last3 (a b c : M) : (![a, b, c] : Fin 3 → M) 2 = c := rfl

/-- `&`-variable realization at a `Fin.k` tuple: `(rv &i).realize (Sum.elim v x) = x i`. -/
private theorem var_val {k : ℕ} (x : Fin k → M) (i : Fin k) :
    ((&i : LRV.Tm k)).realize (Sum.elim (default : Empty → M) x) = x i := by
  show x i = x i
  rfl

/-! ### The field laws at the level of `M`, from `Axioms.kField` -/

/-- Additive associativity on `K`. -/
theorem kAdd_assoc (a b c : M) (ha : pInKof a) (hb : pInKof b) (hc : pInKof c) :
    iKAdd (iKAdd a b) c = iKAdd a (iKAdd b c) := by
  have hmem : LRV.allSortedK ![SortTag.rv, SortTag.rv, SortTag.rv]
      (pEq (tKAdd (tKAdd &0 &1) &2) (tKAdd &0 (tKAdd &1 &2))) ∈ Axioms.ACVF := by
    simp [Axioms.ACVF, Axioms.ACVFpaper, Axioms.kField, Axioms.ofList]
  have h := eq_of_allSortedK hmem ![a, b, c] (by
    intro i
    fin_cases i <;> simp only [pInKof]
    · simpa using ha
    · simpa using hb
    · simpa using hc)
  simpa only [TrivCase.realize_tKAdd, RVCalc.realize_var_inr, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] using h

/-- Additive commutativity on `K`. -/
theorem kAdd_comm (a b : M) (ha : pInKof a) (hb : pInKof b) : iKAdd a b = iKAdd b a :=
  Jm2.iKAdd_comm (M := M) ha hb

/-- `t + 0 = t` on `K`. -/
theorem kAdd_zero (a : M) (ha : pInKof a) : iKAdd a iRVZero = a :=
  Jm2.iKAdd_zero (M := M) ha

/-- `0 + t = t` on `K`. -/
theorem kZero_add (a : M) (ha : pInKof a) : iKAdd iRVZero a = a :=
  (kAdd_comm iRVZero a (Or.inr rfl) ha).trans (kAdd_zero a ha)

/-- Additive inverses cancel on `K`. -/
theorem kAdd_neg_cancel (a : M) (ha : pInKof a) : iKAdd a (TrivCase.iKNeg a) = iRVZero := by
  have hmem : LRV.allSortedK ![SortTag.rv]
      (pEq (tKAdd &0 (tKNeg &0)) tRVZero) ∈ Axioms.ACVF := by
    simp [Axioms.ACVF, Axioms.ACVFpaper, Axioms.kField, Axioms.ofList]
  have h := eq_of_allSortedK hmem ![a] (fun i => by fin_cases i; simpa using ha)
  simpa only [TrivCase.realize_tKAdd, TrivCase.realize_tKNeg, RVCalc.realize_var_inr, Transfer.realize_tRVZero,
    Matrix.cons_val_zero] using h

/-- Multiplicative associativity on `K`. -/
theorem kMul_assoc (a b c : M) (ha : pInKof a) (hb : pInKof b) (hc : pInKof c) :
    iRVMul (iRVMul a b) c = iRVMul a (iRVMul b c) := by
  have hmem : LRV.allSortedK ![SortTag.rv, SortTag.rv, SortTag.rv]
      (pEq (tRVMul (tRVMul &0 &1) &2) (tRVMul &0 (tRVMul &1 &2))) ∈ Axioms.ACVF := by
    simp [Axioms.ACVF, Axioms.ACVFpaper, Axioms.kField, Axioms.ofList]
  have h := eq_of_allSortedK hmem ![a, b, c] (by
    intro i
    fin_cases i <;> simp only [pInKof]
    · simpa using ha
    · simpa using hb
    · simpa using hc)
  simpa only [Transfer.realize_tRVMul, RVCalc.realize_var_inr, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] using h

/-- Multiplicative commutativity on `K`. -/
theorem kMul_comm (a b : M) (ha : pInKof a) (hb : pInKof b) : iRVMul a b = iRVMul b a := by
  have hmem : LRV.allSortedK ![SortTag.rv, SortTag.rv]
      (pEq (tRVMul &0 &1) (tRVMul &1 &0)) ∈ Axioms.ACVF := by
    simp [Axioms.ACVF, Axioms.ACVFpaper, Axioms.kField, Axioms.ofList]
  have h := eq_of_allSortedK hmem ![a, b] (by
    intro i
    fin_cases i <;> simp only [pInKof]
    · simpa using ha
    · simpa using hb)
  simpa only [Transfer.realize_tRVMul, RVCalc.realize_var_inr, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] using h

/-- `t · 1 = t` on `K`. -/
theorem kMul_one (a : M) (ha : pInKof a) : iRVMul a iRVOne = a := by
  have hmem : LRV.allSortedK ![SortTag.rv] (pEq (tRVMul &0 tRVOne) &0) ∈ Axioms.ACVF := by
    simp [Axioms.ACVF, Axioms.ACVFpaper, Axioms.kField, Axioms.ofList]
  have h := eq_of_allSortedK hmem ![a] (fun i => by fin_cases i; simpa using ha)
  simpa only [Transfer.realize_tRVMul, TrivCase.realize_tRVOne, RVCalc.realize_var_inr,
    Matrix.cons_val_zero] using h

/-- `1 · t = t` on `K`. -/
theorem kOne_mul (a : M) (ha : pInKof a) : iRVMul iRVOne a = a := by
  rw [kMul_comm iRVOne a (Or.inl (StandingTree.rv_one_units (M := M))) ha]
  exact kMul_one a ha

/-- Distributivity on `K`. -/
theorem kMul_add (a b c : M) (ha : pInKof a) (hb : pInKof b) (hc : pInKof c) :
    iRVMul a (iKAdd b c) = iKAdd (iRVMul a b) (iRVMul a c) := by
  have hmem : LRV.allSortedK ![SortTag.rv, SortTag.rv, SortTag.rv]
      (pEq (tRVMul &0 (tKAdd &1 &2)) (tKAdd (tRVMul &0 &1) (tRVMul &0 &2))) ∈ Axioms.ACVF := by
    simp [Axioms.ACVF, Axioms.ACVFpaper, Axioms.kField, Axioms.ofList]
  have h := eq_of_allSortedK hmem ![a, b, c] (by
    intro i
    fin_cases i <;> simp only [pInKof]
    · simpa using ha
    · simpa using hb
    · simpa using hc)
  simpa only [Transfer.realize_tRVMul, TrivCase.realize_tKAdd, RVCalc.realize_var_inr,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] using h

/-- `0 ≠ 1`. -/
private theorem kZero_ne_one : (iRVZero : M) ≠ iRVOne := (RVCalc.rv_one_ne_zero (M := M) hM).symm

/-! ### K is closed under its operations (sort-closure axioms) -/

/-- `sdKAdd`: `K` is closed under `iKAdd`. -/
theorem kAdd_mk (a b : M) (ha : pInKof a) (hb : pInKof b) : pInKof (iKAdd a b) := by
  have hmem : Axioms.sdKAdd ∈ Axioms.ACVF := by
    simp [Axioms.ACVF, Axioms.sortAxioms, Axioms.sortClosure, Axioms.ofList]
  have h' := Transfer.allSorted_realize hM (ss := ![SortTag.rv, SortTag.rv])
    (φ := (pInK &0 ⟹ (pInK &1 ⟹ pInK (tKAdd &0 &1)))) hmem ![a, b]
    (by intro i; fin_cases i <;> simp [Jm2.iRV_of_inK ha, Jm2.iRV_of_inK hb])
  have h3 := h'
  rw [BoundedFormula.realize_imp] at h3
  have h4 := h3 ((TrivCase.pInK_realize &0 (default : Empty → M) ![a, b]).mpr ha)
  rw [BoundedFormula.realize_imp] at h4
  have h5 := h4 ((TrivCase.pInK_realize &1 (default : Empty → M) ![a, b]).mpr hb)
  have h6 := (TrivCase.pInK_realize (tKAdd &0 &1) (default : Empty → M) ![a, b]).mp h5
  show iUnits (iKAdd a b) ∨ iKAdd a b = iRVZero
  rwa [TrivCase.realize_tKAdd] at h6

/-- `sdKNeg`: `K` is closed under `TrivCase.iKNeg`. -/
theorem kNeg_mk (a : M) (ha : pInKof a) : pInKof (TrivCase.iKNeg a) := by
  have hmem : Axioms.sdKNeg ∈ Axioms.ACVF := by
    simp [Axioms.ACVF, Axioms.sortAxioms, Axioms.sortClosure, Axioms.ofList]
  have h' := Transfer.allSorted_realize hM (ss := ![SortTag.rv])
    (φ := (pInK &0 ⟹ pInK (tKNeg &0))) hmem ![a]
    (by intro i; fin_cases i; simpa using Jm2.iRV_of_inK ha)
  rw [BoundedFormula.realize_imp] at h'
  have h4 := h' ((TrivCase.pInK_realize &0 (default : Empty → M) ![a]).mpr ha)
  have h5 := (TrivCase.pInK_realize (tKNeg &0) (default : Empty → M) ![a]).mp h4
  show iUnits (TrivCase.iKNeg a) ∨ TrivCase.iKNeg a = iRVZero
  rwa [TrivCase.realize_tKNeg] at h5

/-- `sdKMul`: `K` is closed under `iRVMul`. -/
theorem kMul_mk (a b : M) (ha : pInKof a) (hb : pInKof b) : pInKof (iRVMul a b) := by
  have hmem : Axioms.sdKMul ∈ Axioms.ACVF := by
    simp [Axioms.ACVF, Axioms.sortAxioms, Axioms.sortClosure, Axioms.ofList]
  have h' := Transfer.allSorted_realize hM (ss := ![SortTag.rv, SortTag.rv])
    (φ := (pInK &0 ⟹ (pInK &1 ⟹ pInK (tRVMul &0 &1)))) hmem ![a, b]
    (by intro i; fin_cases i <;> simp [Jm2.iRV_of_inK ha, Jm2.iRV_of_inK hb])
  have h3 := h'
  rw [BoundedFormula.realize_imp] at h3
  have h4 := h3 ((TrivCase.pInK_realize &0 (default : Empty → M) ![a, b]).mpr ha)
  rw [BoundedFormula.realize_imp] at h4
  have h5 := h4 ((TrivCase.pInK_realize &1 (default : Empty → M) ![a, b]).mpr hb)
  have h6 := (TrivCase.pInK_realize (tRVMul &0 &1) (default : Empty → M) ![a, b]).mp h5
  show iUnits (iRVMul a b) ∨ iRVMul a b = iRVZero
  rwa [Transfer.realize_tRVMul] at h6

/-! ### Multiplicative inversion at nonzero elements, from `kField`'s invertibility axiom -/

/-- `pInKof` excluding the absorbing element is a unit. -/
theorem iUnits_of_pInKof_ne_zero {a : M} (ha : pInKof a) (h0 : a ≠ iRVZero) : iUnits a :=
  ha.elim id (fun h => absurd h h0)

/-- The promise of invertibility at nonzero `K`-elements, from the `kField` axiom
"every nonzero element of `K` is invertible" (its last item). -/
theorem kField_exists_mul_inv (a : M) (ha : pInKof a) (ha0 : a ≠ iRVZero) :
    ∃ y : M, pInKof y ∧ iRVMul a y = iRVOne := by
  have hmem : LRV.allSortedK ![SortTag.rv]
      (pEq &0 tRVZero ⊔ exSortedK .rv (pEq (tRVMul &0 &1) tRVOne)) ∈ Axioms.ACVF := by
    simp [Axioms.ACVF, Axioms.ACVFpaper, Axioms.kField, Axioms.ofList]
  have h := Jm2.allSortedK_realize (T := Axioms.ACVF) hM (ss := ![SortTag.rv])
    (φ := pEq &0 tRVZero ⊔ exSortedK .rv (pEq (tRVMul &0 &1) tRVOne)) hmem ![a]
    (fun i => by fin_cases i; simpa using Jm2.iRV_of_inK ha)
    (fun i => by fin_cases i; simpa using ha)
  have h2 := h
  rw [BoundedFormula.realize_sup] at h2
  rcases h2 with h0 | h2ex
  · exact absurd (by simpa [pEq, BoundedFormula.realize_bdEqual, RVCalc.realize_var_inr,
      Matrix.cons_val_zero] using h0) ha0
  · have hsim : ∃ y : M, (iRV y ∧ (iUnits y ∨ y = iRVZero)) ∧ iRVMul a y = iRVOne := by
      simpa [LRV.exSortedK, BoundedFormula.realize_ex, BoundedFormula.realize_inf,
        Transfer.sortPred_realize, TrivCase.pInK_realize, BoundedFormula.realize_bdEqual,
        Transfer.realize_tRVMul, TrivCase.realize_tRVOne, TrivCase.realize_tv_nat,
        Fin.snoc_castSucc, Fin.snoc_last] using h2ex
    rcases hsim with ⟨y, hs⟩
    refine ⟨y, hs.1.2, hs.2⟩

/-! ### The `Field` operation instances on `KOf M` -/

/-- The `KOf` type has `0`, `1`, `+`, `-`, `·`, and inversion-by-choice. -/
instance : Zero (KOf M) := ⟨KZero⟩

noncomputable instance : One (KOf M) := ⟨KOne⟩

instance : Add (KOf M) := ⟨fun a b => ⟨iKAdd a.1 b.1, kAdd_mk a.1 b.1 a.2 b.2⟩⟩

instance : Neg (KOf M) := ⟨fun a => ⟨TrivCase.iKNeg a.1, kNeg_mk a.1 a.2⟩⟩

instance : Sub (KOf M) := ⟨fun a b => a + -b⟩

instance : Mul (KOf M) := ⟨fun a b => ⟨iRVMul a.1 b.1, kMul_mk a.1 b.1 a.2 b.2⟩⟩

/-- Moreover it has ` iRVMul`-function: the inverse of a nonzero element, chosen from
`kField`'s invertibility promise. -/
noncomputable def kInv (a : KOf M) : KOf M := by
  classical
  exact if h : a.1 = iRVZero then KZero
    else ⟨(Classical.choose (kField_exists_mul_inv a.1 a.2 h)),
      (Classical.choose_spec (kField_exists_mul_inv a.1 a.2 h)).1⟩

noncomputable instance : Inv (KOf M) := ⟨kInv⟩

/-- Inversion at nonzero `K`-elements cancels (`kField`'s invertibility promise, chosen): the
`mul_inv_cancel` side. -/
theorem kInv_cancel (a : KOf M) (h0 : a ≠ KZero) : a * a⁻¹ = KOne := by
  have h0' : a.1 ≠ iRVZero := fun h => h0 (Subtype.ext h)
  have hval : ((a⁻¹ : KOf M).1) = Classical.choose (kField_exists_mul_inv a.1 a.2 h0') := by
    change (kInv a).1 = Classical.choose (kField_exists_mul_inv a.1 a.2 h0')
    unfold kInv
    exact congrArg Subtype.val (dif_neg h0')
  have hs := Classical.choose_spec (kField_exists_mul_inv a.1 a.2 h0')
  apply Subtype.ext
  show (a * a⁻¹ : KOf M).1 = (KOne : KOf M).1
  show iRVMul a.1 ((a⁻¹ : KOf M).1) = iRVOne
  rw [hval]
  exact hs.2

/-- Inversion at `0` is `0` (convention, from the `dif` selection at `rvZero`). -/
theorem kInv_zero : (0 : KOf M)⁻¹ = (0 : KOf M) := dif_pos rfl

/-! ### The `Field` operation instances on `KOf M` -/

/-- The `KOf` type has `0`, `1`, `+`, `-`, `·`, and inversion-by-choice. -/
instance : Zero (KOf M) := ⟨KZero⟩

noncomputable instance : One (KOf M) := ⟨KOne⟩

instance : Add (KOf M) := ⟨fun a b => ⟨iKAdd a.1 b.1, kAdd_mk a.1 b.1 a.2 b.2⟩⟩

instance : Neg (KOf M) := ⟨fun a => ⟨TrivCase.iKNeg a.1, kNeg_mk a.1 a.2⟩⟩

instance : Sub (KOf M) := ⟨fun a b => a + -b⟩

instance : Mul (KOf M) := ⟨fun a b => ⟨iRVMul a.1 b.1, kMul_mk a.1 b.1 a.2 b.2⟩⟩

/-- **`KOf M` is a field.**  The whole structure is the `kField` axiom list realized. -/
noncomputable instance fieldKOf : Field (KOf M) := by
  exact Field.ofMinimalAxioms (KOf M)
    (fun a b c => Subtype.ext (kAdd_assoc a.1 b.1 c.1 a.2 b.2 c.2))
    (fun a => Subtype.ext (show iKAdd iRVZero a.1 = a.1 from kZero_add a.1 a.2))
    (fun a => Subtype.ext (by
      show iKAdd (TrivCase.iKNeg a.1) a.1 = iRVZero
      rw [kAdd_comm (TrivCase.iKNeg a.1) a.1 (kNeg_mk a.1 a.2) a.2]
      exact kAdd_neg_cancel a.1 a.2))
    (fun a b c => Subtype.ext (kMul_assoc a.1 b.1 c.1 a.2 b.2 c.2))
    (fun a b => Subtype.ext (kMul_comm a.1 b.1 a.2 b.2))
    (fun a => Subtype.ext (show iRVMul iRVOne a.1 = a.1 from kOne_mul a.1 a.2))
    (fun a h0 => kInv_cancel a h0)
    kInv_zero
    (fun a b c => Subtype.ext (kMul_add a.1 b.1 c.1 a.2 b.2 c.2))
    ⟨KZero, KOne, fun h => kZero_ne_one (congrArg Subtype.val h)⟩

end SpecialTransformations.Milestone0.StandingField
