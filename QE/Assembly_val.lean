 /-
**Partial**: hypothesis (i) of Johnson's criterion for the one-sorted `Language.val`.

What this file proves (all compiled, axioms clean):

* `Language.val` (ring language plus the binary predicate `v x ≤ v y`), the theory `valField` of
  valued fields with its seven predicate axioms (`axRefl`, `axTrans`, `axTotal`, `axZeroLe`,
  `axZeroEq`, `axUltra`, `axScale`), each with its semantic form;
* `isValPred_iff_model`, the dictionary between a `Language.val`-model of `valField` and a field
  with a `v x ≤ v y` predicate satisfying the semantic axioms, both directions;
* `valStructure_model`: every Mathlib `Valuation v` gives a model of `valField`;
* the **fraction-field step**: `predFrac` (cross multiplication) on `FractionRing R`,
  `predFrac_iff`, `predFrac_isValPred`, `valField_model` — no value group needed;
* the **coordinate ring** of an abstract `Language.val`-structure `S` embedded in a model:
  `relIdeal e = ker (FreeCommRing.lift e)`, `ker_lift_eq` (the relations are intrinsic to `S`),
  `coordRing e = FreeCommRing S ⧸ relIdeal e` with its ring/domain/compatible structure,
  the injective `coordEval`, `mk_of_valFunMap` (the language's function symbols agree with the
  quotient ring) and **`coordEmbedding : S ↪[val] coordRing e`**, plus `predCoord_isValPred`.

What it does **not** prove: `JohnsonCriterion.HasPrimeModels valField T`.  Missing exactly four
things, and no mathematics: `primeField e = FractionRing (coordRing e)` as a `valField.ModelType`
with the predicate `predFrac (predCoord e)`, the embedding `S ↪[val] primeField e`, the universal
property through `IsFractionRing.lift` (the only new obligation is that an `L_val`-embedding
preserves and reflects `v x ≤ v y`, which `pred_frac_iff` gives by cross multiplication), and the
packaging into `HasPrimeModels`.  The `Language.ring` skeleton of all four is
`QE/PrimeModels_full.lean`.

From swarm `smw0c60wk` member m4; compiled and axiom-checked by the reviewer, not edited.

Only import: Mathlib.
-/

/-
  **The theory of valued fields in Johnson's language `L_val`, and the fraction field of a
  valued domain** — infrastructure for Johnson (*Fun with Fields*, Chapter 2, §2.1),
  Lemma 2.1.4, hypothesis (i) "prime models over substructures", for valued fields.

  WHAT IS PROVED HERE (all unconditional, no `sorry`, no `axiom`):

  * §1 the one-sorted language `L_val` (`Language.val`, a verbatim copy of
    `FracValued.Language.val` from `QE/PrimeModels_valued.lean`), the `L_val`-structure
    `valStructure v` of a Mathlib valuation, the language inclusion `valRingHom : L_ring →ᴸ L_val`,
    and **the theory of valued fields** `valField` (`= valFieldCore ∪ {axTotal}`) in `L_val`:
    `valFieldCore = fieldPart ∪ valAxioms`, where `fieldPart` is the image of Mathlib's
    `Theory.field` under `valRingHom` and `valAxioms` is
    `{axRefl, axTrans, axZeroLe, axZeroEq, axUltra, axScale}`, the axioms of a valuation written
    with the predicate `v x ≤ v y` alone (§1b).
  * §2 realization lemmas: `M ⊨ axScale ↔ ∀ x y z, z ≠ 0 → (v x ≤ v y ↔ v (x z) ≤ v (y z))`,
    and similarly for the other five axioms (`axRefl_realize` … `axScale_realize`,
    `axTotal_realize`), for any `L_val`-structure whose field symbols are the ring operations
    (`[CommRing M] [CompatibleRing M] [valRingHom.IsExpansionOn M]`).
  * §3 **the fraction field of a valued domain is a valued field**: `IsValPred p` bundles the six
    semantic axioms for a predicate `p` on a commutative ring; `predFrac p` is the predicate on
    `FractionRing R` defined by cross multiplication, `predFrac_iff` characterizes it on
    representatives, and `predFrac_isValPred : IsValPred p → IsValPred (predFrac p)`.
  * §4 `valStructOf K p` (the `L_val`-structure attached to a predicate `p` on a field) and
    `valField_model : IsValPred p → valStructOf K p ⊨ valField`; `isValPred_of_valuation` and
    `valStructure_model : valStructure v ⊨ valField` for every Mathlib valuation `v`, i.e. the
    theory `valField` really is the theory of valued fields.

  NOT PROVED HERE (the remaining part of hypothesis (i)): the coordinate-ring construction that
  turns an abstract `L_val`-structure `S` embedded in a valued field into a *prime model* `S'`
  (the fraction field of `FreeCommRing S` modulo the polynomial relations of `S`), and hence
  `JohnsonCriterion.HasPrimeModels valField T`.  §3 is the algebraic heart of that step: `S'`
  inherits its predicate from `M` by cross multiplication, which is exactly what
  `predFrac_isValPred` verifies.  What is missing is Lean plumbing (assembling the
  `CompatibleRing`/`IsExpansionOn` instances for the divisor ring and the `L_val`-embedding of
  `S` into it), not mathematics.

  Everything is proved for `L_val`-structures of the form `valStructOf` / `valStructure`, and
  §1-§3 are independent of any valuation target (`Γ₀`), so they can be reused for the
  amalgamation reduction (`QE/Amalgamation_reduced.lean`) as well.

  Only import: Mathlib.  Check: `cd repo && lean .ultramath/smw0c60wk/m4/ValPrimeModels.lean`.
-/
import Mathlib

open FirstOrder FirstOrder.Language
open scoped FirstOrder

set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

/-! ## 1. The one-sorted language `L_val`

`L_val` is the language of rings together with a binary relation symbol `v x ≤ v y`.
This is a verbatim copy of `FracValued.Language.val` (`QE/PrimeModels_valued.lean`). -/

namespace FirstOrder

inductive ValFunc : ℕ → Type
  | add : ValFunc 2
  | mul : ValFunc 2
  | neg : ValFunc 1
  | zero : ValFunc 0
  | one : ValFunc 0
  deriving DecidableEq

inductive ValRel : ℕ → Type
  | le : ValRel 2
  deriving DecidableEq

namespace Language

/-- **Johnson's language `L_val`**: the language of rings expanded by a binary predicate for the
relation `v x ≤ v y`. -/
def val : FirstOrder.Language := ⟨ValFunc, ValRel⟩

end Language

/-- **The `L_val`-structure of a valued field.** -/
@[instance_reducible]
def valStructure {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation K Γ₀) : Language.val.Structure K where
  funMap := fun {_} f x =>
    match f with
    | ValFunc.add => x 0 + x 1
    | ValFunc.mul => x 0 * x 1
    | ValFunc.neg => - x 0
    | ValFunc.zero => 0
    | ValFunc.one => 1
  RelMap := fun {_} r x =>
    match r with
    | ValRel.le => v (x 0) ≤ v (x 1)

/-- The language inclusion `L_ring → L_val`. -/
def valRingHom : Language.ring →ᴸ Language.val where
  onFunction := fun {_} f => match f with
    | ringFunc.add => ValFunc.add
    | ringFunc.mul => ValFunc.mul
    | ringFunc.neg => ValFunc.neg
    | ringFunc.zero => ValFunc.zero
    | ringFunc.one => ValFunc.one
  onRelation := fun {_} r => isEmptyElim r

end FirstOrder

namespace ValPM

open FirstOrder FirstOrder.Language FirstOrder.Ring


/-! ## 1b. Term notation and the axioms of the theory of valued fields -/

section Terms

variable {α : Type*}

instance instZeroTerm : Zero (Language.val.Term α) := ⟨Term.func ValFunc.zero fun i => i.elim0⟩
instance instOneTerm : One (Language.val.Term α) := ⟨Term.func ValFunc.one fun i => i.elim0⟩
instance instAddTerm : Add (Language.val.Term α) := ⟨fun a b => Term.func ValFunc.add ![a, b]⟩
instance instMulTerm : Mul (Language.val.Term α) := ⟨fun a b => Term.func ValFunc.mul ![a, b]⟩
instance instNegTerm : Neg (Language.val.Term α) := ⟨fun a => Term.func ValFunc.neg ![a]⟩

end Terms

/-- The atomic formula `v a ≤ v b` of `L_val`. -/
abbrev leF {α : Type*} {n : ℕ} (a b : Language.val.Term (α ⊕ Fin n)) :
    Language.val.BoundedFormula α n :=
  Relations.boundedFormula ValRel.le (l := n) ![a, b]

/-- The valuation predicate of an `L_val`-structure. -/
abbrev predM {M : Type*} [Language.val.Structure M] (x y : M) : Prop :=
  @Structure.RelMap Language.val M _ 2 ValRel.le ![x, y]

/-! The axioms, each written as a formula with `k` free bound variables and then universally
closed with `BoundedFormula.alls`; this keeps the realization lemmas small. -/

/-- The relation `v x ≤ v y` is reflexive. -/
def axReflF : Language.val.BoundedFormula Empty 1 := leF (&0) (&0)
def axRefl : Language.val.Sentence := axReflF.alls

/-- The relation `v x ≤ v y` is transitive. -/
def axTransF : Language.val.BoundedFormula Empty 3 :=
  leF (&0) (&1) ⟹ leF (&1) (&2) ⟹ leF (&0) (&2)
def axTrans : Language.val.Sentence := axTransF.alls

/-- The relation `v x ≤ v y` is total. -/
def axTotalF : Language.val.BoundedFormula Empty 2 := leF (&0) (&1) ⊔ leF (&1) (&0)
def axTotal : Language.val.Sentence := axTotalF.alls

/-- `v 0` is minimal. -/
def axZeroLeF : Language.val.BoundedFormula Empty 1 := leF 0 (&0)
def axZeroLe : Language.val.Sentence := axZeroLeF.alls

/-- `v x ≤ v 0` only for `x = 0`. -/
def axZeroEqF : Language.val.BoundedFormula Empty 1 := leF (&0) 0 ⟹ (&0 =' 0)
def axZeroEq : Language.val.Sentence := axZeroEqF.alls

/-- The ultrametric inequality `v (x + y) ≤ max (v x) (v y)`, as a disjunction. -/
def axUltraF : Language.val.BoundedFormula Empty 2 :=
  leF (&0 + &1) &0 ⊔ leF (&0 + &1) &1
def axUltra : Language.val.Sentence := axUltraF.alls

/-- Multiplication by a nonzero element preserves and reflects the order: `v (x z) ≤ v (y z) ↔
v x ≤ v y`.  This is the multiplicative behaviour of `v`, expressed by the predicate alone. -/
def axScaleF : Language.val.BoundedFormula Empty 3 :=
  ∼(&2 =' 0) ⟹ (leF (&0) (&1) ⇔ leF (&0 * &2) (&1 * &2))
def axScale : Language.val.Sentence := axScaleF.alls

/-- The theory of fields, transported to `L_val`. -/
def fieldPart : Language.val.Theory := valRingHom.onBoundedFormula '' Theory.field

/-- The axioms of a valuation, expressed by the predicate `v x ≤ v y` alone. -/
def valAxioms : Language.val.Theory :=
  {axRefl, axTrans, axZeroLe, axZeroEq, axUltra, axScale}

/-- The part of the theory of valued fields which the arguments below actually use. -/
def valFieldCore : Language.val.Theory := fieldPart ∪ valAxioms

/-- **The theory of valued fields** in the language `L_val`: a field, together with a predicate
`v x ≤ v y` which behaves like comparison of valuations. -/
def valField : Language.val.Theory := valFieldCore ∪ {axTotal}

/-! ## 2. Realization of the axioms -/

section AxRealize

variable {M : Type*} [Language.val.Structure M]

@[simp] theorem realize_zeroTerm (v : M → M) :
    ((0 : Language.val.Term M)).realize v
      = @Structure.funMap Language.val M _ 0 ValFunc.zero (fun i => i.elim0) := by
  show Term.realize (L := Language.val) v (Term.func ValFunc.zero (fun i => i.elim0)) = _
  rw [Term.realize_func]
  congr 1
  funext i
  exact i.elim0

end AxRealize

section AxRealize2

variable {M : Type*} [Language.val.Structure M] {α : Type*}

@[simp] theorem realize_zeroTerm' (v : α → M) :
    ((0 : Language.val.Term α)).realize v
      = @Structure.funMap Language.val M _ 0 ValFunc.zero (fun i => i.elim0) := by
  show Term.realize (L := Language.val) v (Term.func ValFunc.zero (fun i => i.elim0)) = _
  rw [Term.realize_func]
  congr 1
  funext i
  exact i.elim0

@[simp] theorem realize_oneTerm' (v : α → M) :
    ((1 : Language.val.Term α)).realize v
      = @Structure.funMap Language.val M _ 0 ValFunc.one (fun i => i.elim0) := by
  show Term.realize (L := Language.val) v (Term.func ValFunc.one (fun i => i.elim0)) = _
  rw [Term.realize_func]
  congr 1
  funext i
  exact i.elim0

@[simp] theorem realize_addTerm' (a b : Language.val.Term α) (v : α → M) :
    (a + b).realize v
      = @Structure.funMap Language.val M _ 2 ValFunc.add ![a.realize v, b.realize v] := by
  show Term.realize (L := Language.val) v (Term.func ValFunc.add ![a, b]) = _
  rw [Term.realize_func]
  congr 1
  funext i
  fin_cases i <;> simp

@[simp] theorem realize_mulTerm' (a b : Language.val.Term α) (v : α → M) :
    (a * b).realize v
      = @Structure.funMap Language.val M _ 2 ValFunc.mul ![a.realize v, b.realize v] := by
  show Term.realize (L := Language.val) v (Term.func ValFunc.mul ![a, b]) = _
  rw [Term.realize_func]
  congr 1
  funext i
  fin_cases i <;> simp

@[simp] theorem realize_varTerm' {n : ℕ} (i : Fin n) (v : α → M) (xs : Fin n → M) :
    (Term.var (Sum.inr i) : Language.val.Term (α ⊕ Fin n)).realize (Sum.elim v xs) = xs i := rfl

end AxRealize2

section AxIff

variable {M : Type*} [CommRing M] [Language.val.Structure M] [CompatibleRing M]
  [valRingHom.IsExpansionOn M]

theorem valFunMap_add (x y : M) :
    @Structure.funMap Language.val M _ 2 ValFunc.add ![x, y] = x + y := by
  have h : @Structure.funMap Language.val M _ 2
      (valRingHom.onFunction (ringFunc.add : Language.ring.Functions 2)) ![x, y]
      = @Structure.funMap Language.ring M _ 2 (ringFunc.add : Language.ring.Functions 2) ![x, y] :=
    LHom.map_onFunction (ϕ := valRingHom) (f := (ringFunc.add : Language.ring.Functions 2))
      (x := ![x, y])
  refine h.trans ?_
  simpa using CompatibleRing.funMap_add (R := M) ![x, y]

theorem valFunMap_mul (x y : M) :
    @Structure.funMap Language.val M _ 2 ValFunc.mul ![x, y] = x * y := by
  have h : @Structure.funMap Language.val M _ 2
      (valRingHom.onFunction (ringFunc.mul : Language.ring.Functions 2)) ![x, y]
      = @Structure.funMap Language.ring M _ 2 (ringFunc.mul : Language.ring.Functions 2) ![x, y] :=
    LHom.map_onFunction (ϕ := valRingHom) (f := (ringFunc.mul : Language.ring.Functions 2))
      (x := ![x, y])
  refine h.trans ?_
  simpa using CompatibleRing.funMap_mul (R := M) ![x, y]

theorem valFunMap_zero :
    @Structure.funMap Language.val M _ 0 ValFunc.zero (fun i => i.elim0) = 0 := by
  have h : @Structure.funMap Language.val M _ 0
      (valRingHom.onFunction (ringFunc.zero : Language.ring.Functions 0)) (fun i => i.elim0)
      = @Structure.funMap Language.ring M _ 0
        (ringFunc.zero : Language.ring.Functions 0) (fun i => i.elim0) :=
    LHom.map_onFunction (ϕ := valRingHom) (f := (ringFunc.zero : Language.ring.Functions 0))
      (x := (fun i => i.elim0))
  refine h.trans ?_
  simpa using CompatibleRing.funMap_zero (R := M) (fun i => i.elim0)

theorem valFunMap_one :
    @Structure.funMap Language.val M _ 0 ValFunc.one (fun i => i.elim0) = 1 := by
  have h : @Structure.funMap Language.val M _ 0
      (valRingHom.onFunction (ringFunc.one : Language.ring.Functions 0)) (fun i => i.elim0)
      = @Structure.funMap Language.ring M _ 0
        (ringFunc.one : Language.ring.Functions 0) (fun i => i.elim0) :=
    LHom.map_onFunction (ϕ := valRingHom) (f := (ringFunc.one : Language.ring.Functions 0))
      (x := (fun i => i.elim0))
  refine h.trans ?_
  simpa using CompatibleRing.funMap_one (R := M) (fun i => i.elim0)

theorem relMap_val_two (r : Fin 2 → M) :
    Structure.RelMap (L := Language.val) ValRel.le r ↔ predM (r 0) (r 1) := by
  have h : ∀ (f : Fin 2 → M),
      Structure.RelMap (L := Language.val) ValRel.le f = predM (f 0) (f 1) := by
    intro f
    have h2 : f = ![f 0, f 1] := by funext i; fin_cases i <;> simp
    rw [h2]
    simp
  rw [h r]

theorem leF_realize {α : Type*} {n : ℕ} (a b : Language.val.Term (α ⊕ Fin n))
    (v : α → M) (xs : Fin n → M) :
    (leF a b).Realize v xs ↔
      predM (a.realize (Sum.elim v xs)) (b.realize (Sum.elim v xs)) := by
  rw [show leF a b = Relations.boundedFormula ValRel.le ![a, b] from rfl,
    BoundedFormula.realize_rel, relMap_val_two]
  simp

theorem axRefl_realize : (M ⊨ axRefl) ↔ ∀ x : M, predM x x := by
  simp only [axRefl, axReflF, Sentence.Realize, BoundedFormula.realize_alls, leF_realize,
    realize_varTerm', Function.comp_apply, Sum.elim_inr]
  constructor
  · intro h x; simpa using h ![x]
  · intro h xs; simpa using h (xs 0)

theorem axTrans_realize :
    (M ⊨ axTrans) ↔ ∀ x y z : M, predM x y → predM y z → predM x z := by
  simp only [axTrans, axTransF, Sentence.Realize, BoundedFormula.realize_alls,
    BoundedFormula.realize_imp, leF_realize, realize_varTerm', Function.comp_apply, Sum.elim_inr]
  constructor
  · intro h x y z; simpa using h ![x, y, z]
  · intro h xs; simpa using h (xs 0) (xs 1) (xs 2)

theorem axTotal_realize : (M ⊨ axTotal) ↔ ∀ x y : M, predM x y ∨ predM y x := by
  simp only [axTotal, axTotalF, Sentence.Realize, BoundedFormula.realize_alls,
    BoundedFormula.realize_sup, leF_realize, realize_varTerm', Function.comp_apply, Sum.elim_inr]
  constructor
  · intro h x y; simpa using h ![x, y]
  · intro h xs; simpa using h (xs 0) (xs 1)

theorem axZeroLe_realize : (M ⊨ axZeroLe) ↔ ∀ x : M, predM 0 x := by
  simp only [axZeroLe, axZeroLeF, Sentence.Realize, BoundedFormula.realize_alls, leF_realize,
    realize_varTerm', realize_zeroTerm', Function.comp_apply, Sum.elim_inr, valFunMap_zero]
  constructor
  · intro h x; simpa using h ![x]
  · intro h xs; simpa using h (xs 0)

theorem axZeroEq_realize : (M ⊨ axZeroEq) ↔ ∀ x : M, predM x 0 → x = 0 := by
  simp only [axZeroEq, axZeroEqF, Sentence.Realize, BoundedFormula.realize_alls,
    BoundedFormula.realize_imp, BoundedFormula.realize_bdEqual, leF_realize, realize_varTerm',
    realize_zeroTerm', Function.comp_apply, Sum.elim_inr, valFunMap_zero]
  constructor
  · intro h x; simpa using h ![x]
  · intro h xs; simpa using h (xs 0)

theorem axUltra_realize :
    (M ⊨ axUltra) ↔ ∀ x y : M, predM (x + y) x ∨ predM (x + y) y := by
  simp only [axUltra, axUltraF, Sentence.Realize, BoundedFormula.realize_alls,
    BoundedFormula.realize_sup, leF_realize, realize_varTerm', realize_addTerm',
    realize_zeroTerm', Function.comp_apply, Sum.elim_inr, valFunMap_zero, valFunMap_add]
  constructor
  · intro h x y; simpa using h ![x, y]
  · intro h xs; simpa using h (xs 0) (xs 1)

theorem axScale_realize :
    (M ⊨ axScale) ↔ ∀ x y z : M, z ≠ 0 → (predM x y ↔ predM (x * z) (y * z)) := by
  simp only [axScale, axScaleF, Sentence.Realize, BoundedFormula.realize_alls,
    BoundedFormula.realize_imp, BoundedFormula.realize_not, BoundedFormula.realize_iff,
    BoundedFormula.realize_bdEqual, leF_realize, realize_varTerm', realize_mulTerm',
    realize_zeroTerm', Function.comp_apply, Sum.elim_inr, valFunMap_zero, valFunMap_mul]
  constructor
  · intro h x y z
    simpa using h ![x, y, z]
  · intro h xs
    simpa using h (xs 0) (xs 1) (xs 2)

end AxIff

/-! ## 3. The predicate on a fraction field

A domain `R` carrying a predicate `p` satisfying the valuation axioms gets a predicate on its
fraction field by cross multiplication, `v (a/s) ≤ v (c/t) ↔ v (a t) ≤ v (c s)`.  This section
proves that the fraction field satisfies the same axioms. -/

/-- The semantic axioms of a valued field, stated for a predicate `p` on a commutative ring.
They are exactly the sentences of `valFieldCore` (`axRefl`, `axTrans`, `axZeroLe`, `axZeroEq`,
`axUltra`, `axScale`), read in a ring with the ring operations in place of the function symbols. -/
structure IsValPred {R : Type*} [CommRing R] (p : R → R → Prop) : Prop where
  refl : ∀ x, p x x
  trans : ∀ x y z, p x y → p y z → p x z
  zero_le : ∀ x, p 0 x
  zero_eq : ∀ x, p x 0 → x = 0
  ultra : ∀ x y, p (x + y) x ∨ p (x + y) y
  total : ∀ x y, p x y ∨ p y x
  scale : ∀ x y z, z ≠ 0 → (p x y ↔ p (x * z) (y * z))

section FracPred

variable {R : Type*} [CommRing R] [IsDomain R] {p : R → R → Prop}

/-- The predicate induced on the fraction field: `v (a/s) ≤ v (c/t)` iff `v (a t) ≤ v (c s)`. -/
def predFrac (p : R → R → Prop) (x y : FractionRing R) : Prop :=
  ∃ (a c : R) (s t : nonZeroDivisors R),
    x = IsLocalization.mk' (FractionRing R) a s ∧ y = IsLocalization.mk' (FractionRing R) c t ∧
      p (a * (t : R)) (c * (s : R))

/-- Two fractions are equal iff the cross products agree in `R`. -/
theorem mk'_cross {a c : R} {s t : nonZeroDivisors R}
    (h : IsLocalization.mk' (FractionRing R) a s = IsLocalization.mk' (FractionRing R) c t) :
    a * (t : R) = c * (s : R) :=
  IsFractionRing.injective R (FractionRing R) (IsLocalization.mk'_eq_iff_eq'.mp h)

/-- Two fractions are equal if the cross products agree in `R`. -/
theorem mk'_of_cross {a c : R} {s t : nonZeroDivisors R} (h : a * (t : R) = c * (s : R)) :
    IsLocalization.mk' (FractionRing R) a s = IsLocalization.mk' (FractionRing R) c t :=
  IsLocalization.mk'_eq_iff_eq'.mpr (by rw [h])

theorem predFrac_iff (hscale : ∀ x y z : R, z ≠ 0 → (p x y ↔ p (x * z) (y * z)))
    {a c : R} {s t : nonZeroDivisors R} :
    predFrac p (IsLocalization.mk' (FractionRing R) a s)
        (IsLocalization.mk' (FractionRing R) c t) ↔
      p (a * (t : R)) (c * (s : R)) := by
  constructor
  · rintro ⟨a', c', s', t', hx, hy, hp⟩
    have ha : a * (s' : R) = a' * (s : R) := mk'_cross hx
    have hc : c * (t' : R) = c' * (t : R) := mk'_cross hy
    have hs : (s : R) ≠ 0 := nonZeroDivisors.ne_zero s.2
    have ht : (t : R) ≠ 0 := nonZeroDivisors.ne_zero t.2
    have hs' : (s' : R) ≠ 0 := nonZeroDivisors.ne_zero s'.2
    have ht' : (t' : R) ≠ 0 := nonZeroDivisors.ne_zero t'.2
    have h1 : p ((a' * t') * ((s : R) * t)) ((c' * s') * ((s : R) * t)) :=
      (hscale (a' * t') (c' * s') ((s : R) * t) (mul_ne_zero hs ht)).1 hp
    have e1 : (a' * t') * ((s : R) * t) = (a * t) * ((s' : R) * t') := by
      rw [show (a' * t') * ((s : R) * t) = (a' * (s : R)) * (t' * t) from by ring, ha.symm]
      ring
    have e2 : (c' * s') * ((s : R) * t) = (c * s) * ((s' : R) * t') := by
      rw [show (c' * s') * ((s : R) * t) = (c' * (t : R)) * (s' * s) from by ring, hc.symm]
      ring
    rw [e1, e2] at h1
    exact (hscale (a * t) (c * s) ((s' : R) * t') (mul_ne_zero hs' ht')).2 h1
  · exact fun h => ⟨a, c, s, t, rfl, rfl, h⟩

/-- Changing the denominator of a fraction: `a/s = (a t)/(s t)`. -/
theorem mk'_denom_mul (a : R) (s t : nonZeroDivisors R) :
    IsLocalization.mk' (FractionRing R) a s
      = IsLocalization.mk' (FractionRing R) (a * (t : R)) (s * t) :=
  mk'_of_cross (by simp only [Submonoid.coe_mul]; ring)

/-- A fraction is zero iff its numerator is zero. -/
theorem mk'_eq_zero_iff' (a : R) (s : nonZeroDivisors R) :
    IsLocalization.mk' (FractionRing R) a s = 0 ↔ a = 0 := by
  constructor
  · intro h
    have h' : a * (s : R) = 0 * (s : R) :=
      mk'_cross (by rw [h, IsLocalization.mk'_zero])
    rw [zero_mul] at h'
    rcases mul_eq_zero.mp h' with h0 | h0
    · exact h0
    · exact absurd h0 (nonZeroDivisors.ne_zero s.2)
  · intro h
    subst h
    exact IsLocalization.mk'_zero s

/-- Sums of fractions with a common denominator. -/
theorem mk'_add_same (u v : R) (w : nonZeroDivisors R) :
    IsLocalization.mk' (FractionRing R) u w + IsLocalization.mk' (FractionRing R) v w
      = IsLocalization.mk' (FractionRing R) (u + v) w := by
  rw [← IsLocalization.mk'_add (M := nonZeroDivisors R) (S := FractionRing R) u v w w]
  exact mk'_of_cross (by simp only [Submonoid.coe_mul]; ring)

/-- The predicate on the fraction field, on a common denominator. -/
theorem predFrac_same_denom {h : IsValPred p} {a c : R} {w : nonZeroDivisors R} :
    predFrac p (IsLocalization.mk' (FractionRing R) a w)
        (IsLocalization.mk' (FractionRing R) c w) ↔ p a c := by
  rw [predFrac_iff h.scale]
  exact (h.scale a c (w : R) (nonZeroDivisors.ne_zero w.2)).symm

/-- **The fraction field of a domain with a valued predicate is again a valued predicate.** -/
theorem predFrac_isValPred (h : IsValPred p) : IsValPred (predFrac p) where
  refl := by
    intro x
    obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq (M := nonZeroDivisors R)
      (S := FractionRing R) x
    exact (predFrac_same_denom (h := h)).2 (h.refl a)
  trans := by
    intro x y z hxy hyz
    obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq (M := nonZeroDivisors R)
      (S := FractionRing R) x
    obtain ⟨b, t, rfl⟩ := IsLocalization.exists_mk'_eq (M := nonZeroDivisors R)
      (S := FractionRing R) y
    obtain ⟨c, u, rfl⟩ := IsLocalization.exists_mk'_eq (M := nonZeroDivisors R)
      (S := FractionRing R) z
    rw [predFrac_iff h.scale] at hxy hyz ⊢
    have hs : (s : R) ≠ 0 := nonZeroDivisors.ne_zero s.2
    have ht : (t : R) ≠ 0 := nonZeroDivisors.ne_zero t.2
    have hu : (u : R) ≠ 0 := nonZeroDivisors.ne_zero u.2
    have h1 : p ((a * t) * u) ((b * s) * u) := (h.scale (a * t) (b * s) u hu).1 hxy
    have h2 : p ((b * u) * s) ((c * t) * s) := (h.scale (b * u) (c * t) s hs).1 hyz
    have h1' : p (a * t * u) (b * u * s) := by
      rw [show b * s * u = b * u * s from by ring] at h1
      exact h1
    have h3 : p (a * t * u) (c * t * s) := h.trans _ _ _ h1' h2
    have h3' : p ((a * u) * t) ((c * s) * t) := by
      rw [show a * u * t = a * t * u from by ring, show c * s * t = c * t * s from by ring]
      exact h3
    exact (h.scale (a * u) (c * s) t ht).2 h3'
  zero_le := by
    intro x
    obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq (M := nonZeroDivisors R)
      (S := FractionRing R) x
    rw [show (0 : FractionRing R) = IsLocalization.mk' (FractionRing R) 0 s from
      (IsLocalization.mk'_zero s).symm, predFrac_iff h.scale]
    simpa using h.zero_le (a * (s : R))
  zero_eq := by
    intro x hx
    obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq (M := nonZeroDivisors R)
      (S := FractionRing R) x
    rw [show (0 : FractionRing R) = IsLocalization.mk' (FractionRing R) 0 s from
      (IsLocalization.mk'_zero s).symm, predFrac_iff h.scale] at hx
    have hzero : a * (s : R) = 0 := h.zero_eq _ (by simpa using hx)
    have ha : a = 0 := by
      rcases mul_eq_zero.mp hzero with h0 | h0
      · exact h0
      · exact absurd h0 (nonZeroDivisors.ne_zero s.2)
    rw [ha, IsLocalization.mk'_zero]
  ultra := by
    intro x y
    obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq (M := nonZeroDivisors R)
      (S := FractionRing R) x
    obtain ⟨b, t, rfl⟩ := IsLocalization.exists_mk'_eq (M := nonZeroDivisors R)
      (S := FractionRing R) y
    rw [show IsLocalization.mk' (FractionRing R) a s
        = IsLocalization.mk' (FractionRing R) (a * (t : R)) (s * t) from mk'_denom_mul a s t,
      show IsLocalization.mk' (FractionRing R) b t
        = IsLocalization.mk' (FractionRing R) (b * (s : R)) (s * t) from
        mk'_of_cross (by simp only [Submonoid.coe_mul]; ring),
      mk'_add_same (a * (t : R)) (b * (s : R)) (s * t)]
    simp only [predFrac_same_denom (h := h)]
    exact h.ultra _ _
  total := by
    intro x y
    obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq (M := nonZeroDivisors R)
      (S := FractionRing R) x
    obtain ⟨b, t, rfl⟩ := IsLocalization.exists_mk'_eq (M := nonZeroDivisors R)
      (S := FractionRing R) y
    rw [predFrac_iff h.scale, predFrac_iff h.scale]
    exact h.total _ _
  scale := by
    intro x y z hz
    obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq (M := nonZeroDivisors R)
      (S := FractionRing R) x
    obtain ⟨b, t, rfl⟩ := IsLocalization.exists_mk'_eq (M := nonZeroDivisors R)
      (S := FractionRing R) y
    obtain ⟨c, u, rfl⟩ := IsLocalization.exists_mk'_eq (M := nonZeroDivisors R)
      (S := FractionRing R) z
    have hc : c ≠ 0 := by
      intro hc0
      rw [hc0, IsLocalization.mk'_zero] at hz
      exact hz rfl
    have hu : (u : R) ≠ 0 := nonZeroDivisors.ne_zero u.2
    rw [← IsLocalization.mk'_mul (M := nonZeroDivisors R) (S := FractionRing R) a c s u,
    ← IsLocalization.mk'_mul (M := nonZeroDivisors R) (S := FractionRing R) b c t u,
      predFrac_iff h.scale, predFrac_iff h.scale]
    rw [show a * c * ((t * u : nonZeroDivisors R) : R) = (a * t * c) * u from by
        simp only [Submonoid.coe_mul]; ring,
      show b * c * ((s * u : nonZeroDivisors R) : R) = (b * s * c) * u from by
        simp only [Submonoid.coe_mul]; ring]
    rw [← h.scale (a * t * c) (b * s * c) u hu, ← h.scale (a * t) (b * s) c hc]

end FracPred


/-! ## 4. Every Mathlib valuation satisfies the axioms -/

/-- The `L_val`-structure on a field given by a predicate `p` playing the role of `v x ≤ v y`. -/
@[instance_reducible]
def valStructOf (K : Type*) [Field K] (p : K → K → Prop) : Language.val.Structure K where
  funMap := fun {_} f x =>
    match f with
    | ValFunc.add => x 0 + x 1
    | ValFunc.mul => x 0 * x 1
    | ValFunc.neg => - x 0
    | ValFunc.zero => 0
    | ValFunc.one => 1
  RelMap := fun {_} r x =>
    match r with
    | ValRel.le => p (x 0) (x 1)

/-- **A predicate satisfying the axioms makes its field a model of the theory of valued
fields.**  In particular `valStructOf K (fun x y => v x ≤ v y)` is a model of `valField` for any
Mathlib valuation `v`. -/
theorem valField_model {K : Type*} [Field K] {p : K → K → Prop} (h : IsValPred p) :
    @Theory.Model Language.val K (valStructOf K p) valField := by
  letI : Language.val.Structure K := valStructOf K p
  letI : CompatibleRing K := compatibleRingOfRing K
  haveI : LHom.IsExpansionOn valRingHom K :=
    { map_onFunction := by
        intro n f x
        cases f <;> rfl
      map_onRelation := by
        intro n r x
        exact isEmptyElim r }
  refine ⟨fun φ hφ => ?_⟩
  simp only [valField, valFieldCore, Set.mem_union, Set.mem_singleton_iff] at hφ
  rcases hφ with ((hφ | hφ) | rfl)
  · rw [fieldPart, Set.mem_image] at hφ
    obtain ⟨ψ, hψ, rfl⟩ := hφ
    simpa only [Sentence.Realize, Formula.Realize, LHom.realize_onBoundedFormula] using
      (Theory.realize_sentence_of_mem Theory.field hψ)
  · rw [valAxioms, Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_insert_iff,
      Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at hφ
    rcases hφ with rfl | rfl | rfl | rfl | rfl | rfl
    · exact axRefl_realize.2 h.refl
    · exact axTrans_realize.2 h.trans
    · exact axZeroLe_realize.2 h.zero_le
    · exact axZeroEq_realize.2 h.zero_eq
    · exact axUltra_realize.2 h.ultra
    · exact axScale_realize.2 h.scale
  · exact axTotal_realize.2 h.total


/-! ## 4b. The dictionary: models of `valField` are exactly valued predicates -/

/-- **A model of the theory of valued fields is a field with a valued predicate**, at the level
of the ring operations and the binary predicate, with no value group in sight. -/
theorem isValPred_of_model {K : Type*} [Field K] [Language.val.Structure K]
    [CompatibleRing K] [valRingHom.IsExpansionOn K] (h : K ⊨ valField) :
    @IsValPred K _ (predM : K → K → Prop) := by
  have hcore : K ⊨ valFieldCore := Theory.Model.mono h (by simp [valField, valFieldCore])
  haveI : K ⊨ valFieldCore := hcore
  haveI : K ⊨ valField := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact axRefl_realize.1
      (Theory.realize_sentence_of_mem valFieldCore (by simp [valFieldCore, valAxioms]))
  · exact axTrans_realize.1
      (Theory.realize_sentence_of_mem valFieldCore (by simp [valFieldCore, valAxioms]))
  · exact axZeroLe_realize.1
      (Theory.realize_sentence_of_mem valFieldCore (by simp [valFieldCore, valAxioms]))
  · exact axZeroEq_realize.1
      (Theory.realize_sentence_of_mem valFieldCore (by simp [valFieldCore, valAxioms]))
  · exact axUltra_realize.1
      (Theory.realize_sentence_of_mem valFieldCore (by simp [valFieldCore, valAxioms]))
  · exact axTotal_realize.1
      (Theory.realize_sentence_of_mem valField (by simp [valField]))
  · exact axScale_realize.1
      (Theory.realize_sentence_of_mem valFieldCore (by simp [valFieldCore, valAxioms]))

/-- **The dictionary in the other direction**: a valued predicate makes the field a model of the
theory of valued fields. -/
theorem model_of_isValPred {K : Type*} [Field K] [Language.val.Structure K]
    [CompatibleRing K] [valRingHom.IsExpansionOn K] (h : @IsValPred K _ (predM : K → K → Prop)) :
    K ⊨ valField := by
  refine ⟨fun φ hφ => ?_⟩
  simp only [valField, valFieldCore, Set.mem_union, Set.mem_singleton_iff] at hφ
  rcases hφ with (hφ | hφ) | rfl
  · rw [fieldPart, Set.mem_image] at hφ
    obtain ⟨ψ, hψ, rfl⟩ := hφ
    simpa only [Sentence.Realize, Formula.Realize, LHom.realize_onBoundedFormula] using
      (Theory.realize_sentence_of_mem Theory.field hψ)
  · rw [valAxioms, Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_insert_iff,
      Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at hφ
    rcases hφ with rfl | rfl | rfl | rfl | rfl | rfl
    · exact axRefl_realize.2 h.refl
    · exact axTrans_realize.2 h.trans
    · exact axZeroLe_realize.2 h.zero_le
    · exact axZeroEq_realize.2 h.zero_eq
    · exact axUltra_realize.2 h.ultra
    · exact axScale_realize.2 h.scale
  · exact axTotal_realize.2 h.total

/-- **A field with ring operations and a binary predicate is a model of the theory of valued
fields iff the predicate is a valued predicate.** -/
theorem isValPred_iff_model {K : Type*} [Field K] [Language.val.Structure K]
    [CompatibleRing K] [valRingHom.IsExpansionOn K] :
    K ⊨ valField ↔ IsValPred (predM : K → K → Prop) :=
  ⟨fun h => isValPred_of_model h, fun h => model_of_isValPred h⟩



/-! ## 5. A valuation gives a model of `valField` -/

/-- A nonzero element has nonzero value. -/
theorem val_ne_zero {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation K Γ₀) {z : K} (hz : z ≠ 0) : v z ≠ 0 := by
  intro h
  have h1 : v z * v z⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hz, map_one]
  rw [h, zero_mul] at h1
  exact zero_ne_one h1

/-- The predicate of a genuine valuation satisfies the axioms. -/
theorem isValPred_of_valuation {K : Type*} [Field K] {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀) :
    @IsValPred K _ (fun x y => v x ≤ v y) where
  refl := fun _ => le_refl _
  trans := fun _ _ _ h1 h2 => le_trans h1 h2
  zero_le := fun x => by
    rw [Valuation.map_zero]
    exact zero_le
  zero_eq := fun x hx => by
    by_contra h
    have h1 : v x = 0 := le_antisymm (by simpa using hx) zero_le
    have h2 : v x * v x⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ h, map_one]
    rw [h1, zero_mul] at h2
    exact zero_ne_one h2
  ultra := fun x y => (le_max_iff.mp (Valuation.map_add_le_max' v x y))
  total := fun x y => le_total (v x) (v y)
  scale := fun x y z hz => by
    rw [map_mul, map_mul, mul_comm (v x) (v z), mul_comm (v y) (v z)]
    exact (mul_le_mul_iff_right₀ (zero_lt_iff.mpr (val_ne_zero v hz))).symm

/-- **Every valued field is a model of `valField`.**  The `L_val`-structure `valStructure v` of a
field with a Mathlib valuation satisfies the theory of valued fields. -/
theorem valStructure_model {K : Type*} [Field K] {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀) :
    @Theory.Model Language.val K (valStructure v) valField :=
  valField_model (isValPred_of_valuation v)

/-! ## 6. The coordinate ring of an abstract `L_val`-structure -/

section RingBridge

variable {A B : Type*} [CommRing A] [CompatibleRing A] [CommRing B] [CompatibleRing B]

theorem ringHom_map_fun (f : A →+* B) {n : ℕ} (g : Language.ring.Functions n)
    (x : Fin n → A) : f (Structure.funMap g x) = Structure.funMap g (f ∘ x) := by
  cases g <;> simp

end RingBridge

/-- The zero of a ring structure, described intrinsically (no `CommRing` needed). -/
def zeroOf (T : Type*) [Language.ring.Structure T] : T :=
  @Structure.funMap Language.ring T _ 0 (ringFunc.zero : Language.ring.Functions 0)
    (fun i => i.elim0)

section Kernel

variable {S : Type} [Language.val.Structure S] [Language.ring.Structure S]
  [valRingHom.IsExpansionOn S]
variable {M : Type} [CommRing M] [Language.val.Structure M] [CompatibleRing M]
  [valRingHom.IsExpansionOn M]

/-- An `L_val`-embedding is in particular an `L_ring`-embedding. -/
def ringEmbOfVal (e : S ↪[Language.val] M) : S ↪[Language.ring] M where
  toFun := e
  inj' := e.inj'
  map_fun' := by
    intro n g x
    rw [← LHom.map_onFunction (ϕ := valRingHom) (M := M) (f := g) (x := ⇑e ∘ x),
      ← LHom.map_onFunction (ϕ := valRingHom) (M := S) (f := g) (x := x)]
    exact e.map_fun (valRingHom.onFunction g) x

/-- An embedding of valued structures preserves and reflects the predicate. -/
theorem pred_emb_iff (e : S ↪[Language.val] M) (u v : S) :
    predM (e u) (e v) ↔ predM u v := by
  have h := e.map_rel' ValRel.le ![u, v]
  rw [show (e.toFun ∘ ![u, v]) = ![e u, e v] from by funext i; fin_cases i <;> rfl] at h
  exact h

theorem map_zeroOf (e : S ↪[Language.val] M) : e (zeroOf S) = zeroOf M := by
  have h := e.map_fun (valRingHom.onFunction (ringFunc.zero : Language.ring.Functions 0))
    (fun i => i.elim0)
  have h1 : @Structure.funMap Language.val S _ 0
      (valRingHom.onFunction (ringFunc.zero : Language.ring.Functions 0)) (fun i => i.elim0)
      = zeroOf S :=
    LHom.map_onFunction (ϕ := valRingHom) (f := (ringFunc.zero : Language.ring.Functions 0))
      (x := (fun i => i.elim0))
  have h2 : @Structure.funMap Language.val M _ 0
      (valRingHom.onFunction (ringFunc.zero : Language.ring.Functions 0))
      (fun i => (i.elim0 : M)) = zeroOf M :=
    LHom.map_onFunction (ϕ := valRingHom) (f := (ringFunc.zero : Language.ring.Functions 0))
      (x := (fun i => i.elim0))
  have hcomp : (⇑e ∘ (fun i => i.elim0 : Fin 0 → S)) = (fun i => i.elim0 : Fin 0 → M) := by
    funext i
    exact i.elim0
  rw [hcomp, h1, h2] at h
  exact h

theorem zeroOf_eq_zero : zeroOf M = 0 := by
  rw [zeroOf]
  exact CompatibleRing.funMap_zero (fun i => i.elim0)

/-- The polynomial relations of `S`, computed in `M`. -/
noncomputable abbrev relIdeal (e : S ↪[Language.val] M) : Ideal (FreeCommRing S) :=
  RingHom.ker (FreeCommRing.lift (fun s => e s))

/-- `FreeCommRing.lift` evaluates at a term of the language of rings. -/
theorem lift_eq_apply_term (e : S ↪[Language.val] M) (p : FreeCommRing S) :
    FreeCommRing.lift (fun s => e s) p
      = e (Term.realize (L := Language.ring) (fun s => s) (Ring.termOfFreeCommRing p)) := by
  rw [← Ring.realize_termOfFreeCommRing p (fun s => e s)]
  exact HomClass.realize_term (ringEmbOfVal e) (v := fun s => s)

/-- The ideal of relations is the set of polynomials whose value in `S` is the zero of `S`: it is
intrinsic to `S`. -/
theorem mem_relIdeal_iff (e : S ↪[Language.val] M) (p : FreeCommRing S) :
    p ∈ relIdeal e ↔
      Term.realize (L := Language.ring) (fun s => s) (Ring.termOfFreeCommRing p) = zeroOf S := by
  rw [relIdeal, RingHom.mem_ker, lift_eq_apply_term]
  constructor
  · intro h
    apply e.injective
    rw [h, map_zeroOf, zeroOf_eq_zero]
  · intro h
    rw [h, map_zeroOf, zeroOf_eq_zero]

/-- **The polynomial relations of `S` do not depend on the valued field it is embedded in.** -/
theorem ker_lift_eq (e : S ↪[Language.val] M) {N : Type} [CommRing N]
    [Language.val.Structure N] [CompatibleRing N] [valRingHom.IsExpansionOn N]
    (f : S ↪[Language.val] N) : relIdeal e = relIdeal f := by
  ext p
  rw [mem_relIdeal_iff e p, mem_relIdeal_iff f p]

end Kernel

/-! ## 6b. Bridging the value-symbols to the ring symbols -/

/-- The function symbols of `L_val` are those of `L_ring`. -/
def valToRing : ∀ {n : ℕ}, Language.val.Functions n → Language.ring.Functions n
  | _, ValFunc.add => ringFunc.add
  | _, ValFunc.mul => ringFunc.mul
  | _, ValFunc.neg => ringFunc.neg
  | _, ValFunc.zero => ringFunc.zero
  | _, ValFunc.one => ringFunc.one

theorem valFunMap_eq_ringVal {N : Type*} [Language.val.Structure N] [Language.ring.Structure N]
    [valRingHom.IsExpansionOn N] {n : ℕ} (g : Language.val.Functions n) (x : Fin n → N) :
    Structure.funMap (L := Language.val) g x
      = Structure.funMap (L := Language.ring) (valToRing g) x := by
  cases g with
  | add => exact LHom.map_onFunction (ϕ := valRingHom) (f := ringFunc.add) (x := x)
  | mul => exact LHom.map_onFunction (ϕ := valRingHom) (f := ringFunc.mul) (x := x)
  | neg => exact LHom.map_onFunction (ϕ := valRingHom) (f := ringFunc.neg) (x := x)
  | zero => exact LHom.map_onFunction (ϕ := valRingHom) (f := ringFunc.zero) (x := x)
  | one => exact LHom.map_onFunction (ϕ := valRingHom) (f := ringFunc.one) (x := x)

theorem valToRing_onFunction {n : ℕ} (f : Language.ring.Functions n) :
    valToRing (valRingHom.onFunction f) = f := by
  cases f <;> rfl

/-- A ring homomorphism is compatible with the valuation symbols. -/
theorem valFunMap_ringHom_map {A B : Type*} [CommRing A] [CompatibleRing A]
    [Language.val.Structure A] [valRingHom.IsExpansionOn A]
    [CommRing B] [CompatibleRing B] [Language.val.Structure B]
    [valRingHom.IsExpansionOn B]
    (φ : A →+* B) {n : ℕ} (g : Language.val.Functions n) (x : Fin n → A) :
    φ (Structure.funMap (L := Language.val) g x)
      = Structure.funMap (L := Language.val) g (φ ∘ x) := by
  rw [valFunMap_eq_ringVal (g := g) (x := x),
    valFunMap_eq_ringVal (g := g) (x := ⇑φ ∘ x), ringHom_map_fun]

/-- Cross multiplication for a valued predicate in a field. -/
theorem pred_div_iff {K : Type*} [Field K] {p : K → K → Prop} (h : IsValPred p)
    {x y b d : K} (hb : b ≠ 0) (hd : d ≠ 0) :
    p (x / b) (y / d) ↔ p (x * d) (y * b) := by
  have hbd : b * d ≠ 0 := mul_ne_zero hb hd
  rw [div_eq_mul_inv x b, div_eq_mul_inv y d,
    h.scale (x * b⁻¹) (y * d⁻¹) (b * d) hbd]
  have e1 : x * b⁻¹ * (b * d) = x * d := by field_simp
  have e2 : y * d⁻¹ * (b * d) = y * b := by field_simp
  rw [e1, e2]

/-- The binary predicate on any `L_val`-structure, in components. -/
theorem relMap_two {N : Type*} [Language.val.Structure N] (r : Fin 2 → N) :
    Structure.RelMap (L := Language.val) ValRel.le r ↔ predM (r 0) (r 1) := by
  have h : ∀ (f : Fin 2 → N),
      Structure.RelMap (L := Language.val) ValRel.le f = predM (f 0) (f 1) := by
    intro f
    have h2 : f = ![f 0, f 1] := by funext i; fin_cases i <;> simp
    rw [h2]
    simp
  rw [h r]

/-! ## 7. The coordinate ring of `S` and the embedding of `S` into it -/

section Construction

variable {S : Type} [Language.val.Structure S] [Language.ring.Structure S]
  [valRingHom.IsExpansionOn S]
variable {M : Type} [CommRing M] [Language.val.Structure M] [CompatibleRing M]
  [valRingHom.IsExpansionOn M] [IsDomain M]

/-- The coordinate ring of `S` relative to an embedding into a valued domain `M`. -/
noncomputable abbrev coordRing (e : S ↪[Language.val] M) : Type :=
  FreeCommRing S ⧸ relIdeal e

noncomputable instance coordRing.instCommRing (e : S ↪[Language.val] M) :
    CommRing (coordRing e) :=
  inferInstanceAs (CommRing (FreeCommRing S ⧸ relIdeal e))

instance coordRing.relIdealIsPrime (e : S ↪[Language.val] M) : (relIdeal e).IsPrime :=
  RingHom.ker_isPrime _

noncomputable instance coordRing.instIsDomain (e : S ↪[Language.val] M) :
    IsDomain (coordRing e) :=
  inferInstanceAs (IsDomain (FreeCommRing S ⧸ relIdeal e))

noncomputable instance coordRing.instCompatibleRing (e : S ↪[Language.val] M) :
    CompatibleRing (coordRing e) :=
  compatibleRingOfRing _

/-- Evaluation of the coordinate ring in `M`. -/
noncomputable abbrev coordEval (e : S ↪[Language.val] M) : coordRing e →+* M :=
  Ideal.Quotient.lift (relIdeal e) (FreeCommRing.lift (fun s => e s)) (fun a ha => ha)

theorem coordEval_mk (e : S ↪[Language.val] M) (p : FreeCommRing S) :
    coordEval e (Ideal.Quotient.mk (relIdeal e) p) = FreeCommRing.lift (fun s => e s) p := rfl

theorem coordEval_injective (e : S ↪[Language.val] M) : Function.Injective (coordEval e) := by
  intro x y hxy
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective (I := relIdeal e) x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective (I := relIdeal e) y
  rw [coordEval_mk, coordEval_mk] at hxy
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, RingHom.mem_ker, map_sub, hxy, sub_self]

/-- The `L_val`-structure of the coordinate ring: ring operations, and the predicate pulled back
from `M`. -/
@[instance_reducible]
noncomputable instance coordValStruct (e : S ↪[Language.val] M) :
    Language.val.Structure (coordRing e) where
  funMap := fun {_} f x => Structure.funMap (L := Language.ring) (valToRing f) x
  RelMap := fun {_} r x =>
    match r with
    | ValRel.le => predM (coordEval e (x 0)) (coordEval e (x 1))

instance coordValStruct.expansion (e : S ↪[Language.val] M) :
    @LHom.IsExpansionOn Language.ring Language.val valRingHom (coordRing e) _ (coordValStruct e) where
  map_onFunction := by
    intro n f x
    cases f <;> rfl
  map_onRelation := fun {n} r x => isEmptyElim r

/-- The predicate of the coordinate ring. -/
def predCoord (e : S ↪[Language.val] M) (a c : coordRing e) : Prop :=
  predM (coordEval e a) (coordEval e c)

theorem mk_of_funMap (e : S ↪[Language.val] M) {n : ℕ}
    (g : Language.ring.Functions n) (x : Fin n → S) :
    Ideal.Quotient.mk (relIdeal e) (FreeCommRing.of (Structure.funMap (L := Language.ring) g x))
      = Structure.funMap (L := Language.ring) g
          (fun i => Ideal.Quotient.mk (relIdeal e) (FreeCommRing.of (x i))) := by
  letI : CompatibleRing (FreeCommRing S) := compatibleRingOfRing _
  have hq := ringHom_map_fun (Ideal.Quotient.mk (relIdeal e)) g
    (fun i => FreeCommRing.of (x i))
  simp only [Function.comp_def] at hq
  rw [← hq, Ideal.Quotient.mk_eq_mk_iff_sub_mem, RingHom.mem_ker, map_sub, FreeCommRing.lift_of]
  have h2 : FreeCommRing.lift (fun s => e s)
      (Structure.funMap (L := Language.ring) g (fun i => FreeCommRing.of (x i)))
        = e (Structure.funMap (L := Language.ring) g x) := by
    have he := ringHom_map_fun (FreeCommRing.lift (fun s => e s)) g
      (fun i => FreeCommRing.of (x i))
    simp only [Function.comp_def, FreeCommRing.lift_of] at he
    have he2 := (ringEmbOfVal e).map_fun g x
    simp only [Function.comp_def] at he2
    exact he.trans he2.symm
  rw [h2, sub_self]

theorem mk_of_valFunMap (e : S ↪[Language.val] M) {n : ℕ}
    (g : Language.val.Functions n) (x : Fin n → S) :
    Ideal.Quotient.mk (relIdeal e) (FreeCommRing.of (Structure.funMap (L := Language.val) g x))
      = Structure.funMap (L := Language.val) g
          (fun i => Ideal.Quotient.mk (relIdeal e) (FreeCommRing.of (x i))) := by
  rw [valFunMap_eq_ringVal (g := g) (x := x)]
  exact mk_of_funMap e (valToRing g) x

theorem coordMap_injective (e : S ↪[Language.val] M) :
    Function.Injective
      (fun s : S => Ideal.Quotient.mk (relIdeal e) (FreeCommRing.of s)) := by
  intro a b hab
  have h1 : FreeCommRing.of a - FreeCommRing.of b ∈ relIdeal e :=
    (Ideal.Quotient.mk_eq_mk_iff_sub_mem (I := relIdeal e) (x := FreeCommRing.of a)
      (y := FreeCommRing.of b)).mp hab
  have h2 : FreeCommRing.lift (fun s => e s) (FreeCommRing.of a - FreeCommRing.of b) = 0 := h1
  rw [map_sub, FreeCommRing.lift_of, FreeCommRing.lift_of, sub_eq_zero] at h2
  exact e.injective h2

/-- **`S` embeds in its coordinate ring as an `L_val`-structure.** -/
noncomputable def coordEmbedding (e : S ↪[Language.val] M) :
    S ↪[Language.val] coordRing e where
  toFun := fun s => Ideal.Quotient.mk (relIdeal e) (FreeCommRing.of s)
  inj' := coordMap_injective e
  map_fun' := fun {n} g x => mk_of_valFunMap e g x
  map_rel' := by
    intro n r x
    cases r with
    | le =>
      rw [show ((fun s => Ideal.Quotient.mk (relIdeal e) (FreeCommRing.of s)) ∘ x)
          = (fun i => Ideal.Quotient.mk (relIdeal e) (FreeCommRing.of (x i))) from rfl]
      rw [relMap_two (r := (fun i => Ideal.Quotient.mk (relIdeal e) (FreeCommRing.of (x i)))),
        relMap_two (r := x)]
      show predM (coordEval e (Ideal.Quotient.mk (relIdeal e) (FreeCommRing.of (x 0))))
             (coordEval e (Ideal.Quotient.mk (relIdeal e) (FreeCommRing.of (x 1))))
          ↔ predM (x 0) (x 1)
      rw [coordEval_mk, coordEval_mk, FreeCommRing.lift_of, FreeCommRing.lift_of]
      exact pred_emb_iff e (x 0) (x 1)

/-- The predicate of the coordinate ring is a valued predicate. -/
theorem predCoord_isValPred (e : S ↪[Language.val] M)
    (h : @IsValPred M _ (predM : M → M → Prop)) :
    @IsValPred (coordRing e) _ (predCoord e) where
  refl := fun x => h.refl (coordEval e x)
  trans := fun x y z hxy hyz => h.trans _ _ _ hxy hyz
  zero_le := fun x => by
    simp only [predCoord, map_zero]
    exact h.zero_le (coordEval e x)
  zero_eq := fun x hx => by
    simp only [predCoord, map_zero] at hx
    apply coordEval_injective e
    rw [map_zero]
    exact h.zero_eq (coordEval e x) hx
  ultra := fun x y => by
    simp only [predCoord, map_add]
    exact h.ultra (coordEval e x) (coordEval e y)
  total := fun x y => h.total (coordEval e x) (coordEval e y)
  scale := fun x y z hz => by
    have hz' : coordEval e z ≠ 0 := fun h0 =>
      hz (coordEval_injective e (by rw [h0, map_zero]))
    simp only [predCoord, map_mul]
    exact h.scale (coordEval e x) (coordEval e y) (coordEval e z) hz'

end Construction

/-! ## Axiom checks -/

#print axioms ValPM.axRefl_realize
#print axioms ValPM.axTrans_realize
#print axioms ValPM.axZeroLe_realize
#print axioms ValPM.axZeroEq_realize
#print axioms ValPM.axUltra_realize
#print axioms ValPM.axScale_realize
#print axioms ValPM.axTotal_realize
#print axioms ValPM.predFrac_iff
#print axioms ValPM.predFrac_isValPred
#print axioms ValPM.valField_model
#print axioms ValPM.isValPred_of_valuation
#print axioms ValPM.valStructure_model
#print axioms ValPM.isValPred_of_model
#print axioms ValPM.model_of_isValPred
#print axioms ValPM.isValPred_iff_model
#print axioms ValPM.ker_lift_eq
#print axioms ValPM.mem_relIdeal_iff
#print axioms ValPM.valFunMap_ringHom_map
#print axioms ValPM.pred_div_iff
#print axioms ValPM.mk_of_valFunMap
#print axioms ValPM.coordEmbedding
#print axioms ValPM.predCoord_isValPred

/-! ## 8. A model of `valField` is a field with a valued predicate

`valField` is stated in the one-sorted `L_val`, so a `valField.ModelType` carries no ring
structure and no field structure: the ring symbols are `L_val`-function symbols.  This section
rebuilds the `L_ring`-structure along `valRingHom`, checks that it models `Theory.field`, and so
obtains `Field`, `CompatibleRing` and (via `isValPred_of_model`) `IsValPred predM`.  This is the
bridge every hypothesis of Johnson's criterion needs, because `HasPrimeModels` and
`HasAmalgamation` quantify over `valField.ModelType`, while all the mathematics is done on
concrete valued fields. -/

section Reduct

/-- The `L_ring`-structure underlying an `L_val`-structure. -/
@[instance_reducible]
def ringStructOfVal (N : Type*) [Language.val.Structure N] : Language.ring.Structure N where
  funMap := fun {_} g x => Structure.funMap (L := Language.val) (valRingHom.onFunction g) x
  RelMap := fun {_} r _ => isEmptyElim r

/-- The `L_val`-structure expands `ringStructOfVal`. -/
instance ringStructOfVal.expansion (N : Type*) [s : Language.val.Structure N] :
    @LHom.IsExpansionOn Language.ring Language.val valRingHom N (ringStructOfVal N) s := by
  letI : Language.ring.Structure N := ringStructOfVal N
  exact ⟨fun {_} _ _ => rfl, fun {_} r _ => isEmptyElim r⟩

/-- **A model of `valField` models the theory of fields in the language of rings.** -/
theorem model_field_of_valField (N : Type*) [Language.val.Structure N] (hN : N ⊨ valField) :
    @Theory.Model Language.ring N (ringStructOfVal N) Theory.field := by
  letI : Language.ring.Structure N := ringStructOfVal N
  haveI : valRingHom.IsExpansionOn N := ringStructOfVal.expansion N
  refine ⟨fun φ hφ => ?_⟩
  have hmem : valRingHom.onBoundedFormula φ ∈ valField := Or.inl (Or.inl ⟨φ, hφ, rfl⟩)
  have h : N ⊨ valRingHom.onBoundedFormula φ := hN.realize_of_mem _ hmem
  simpa only [Sentence.Realize, Formula.Realize, LHom.realize_onBoundedFormula] using h

end Reduct

/-! ## 9. The prime model over a substructure of a valued field -/

section PrimeField

variable {S : Type} [Language.val.Structure S] [Language.ring.Structure S]
  [valRingHom.IsExpansionOn S]
variable {M : Type} [CommRing M] [Language.val.Structure M] [CompatibleRing M]
  [valRingHom.IsExpansionOn M] [IsDomain M]

/-- **The prime model of the theory of valued fields over `S`**: the fraction field of the
coordinate ring `FreeCommRing S ⧸ relIdeal e`. -/
noncomputable abbrev valPrimeField (e : S ↪[Language.val] M) : Type :=
  FractionRing (coordRing e)

/-- The valuation predicate of the prime model, by cross multiplication. -/
noncomputable abbrev predVal (e : S ↪[Language.val] M) (x y : valPrimeField e) : Prop :=
  predFrac (predCoord e) x y

noncomputable instance valPrimeField.instValStruct (e : S ↪[Language.val] M) :
    Language.val.Structure (valPrimeField e) :=
  valStructOf (valPrimeField e) (predVal e)

noncomputable instance valPrimeField.instField (e : S ↪[Language.val] M) :
    Field (valPrimeField e) :=
  inferInstanceAs (Field (FractionRing (coordRing e)))

noncomputable instance valPrimeField.instCompatibleRing (e : S ↪[Language.val] M) :
    CompatibleRing (valPrimeField e) :=
  compatibleRingOfRing (valPrimeField e)

noncomputable instance valPrimeField.instExpansion (e : S ↪[Language.val] M) :
    valRingHom.IsExpansionOn (valPrimeField e) :=
  ⟨fun {_} f _ => by cases f <;> rfl, fun {_} r _ => isEmptyElim r⟩

/-- The prime model's predicate satisfies the axioms. -/
theorem predVal_isValPred (e : S ↪[Language.val] M)
    (h : @IsValPred M _ (predM : M → M → Prop)) :
    @IsValPred (valPrimeField e) _ (predVal e) :=
  predFrac_isValPred (predCoord_isValPred e h)

/-- **The prime model is a model of `valField`.** -/
theorem valPrimeField_model (e : S ↪[Language.val] M)
    (h : @IsValPred M _ (predM : M → M → Prop)) :
    @Theory.Model Language.val (valPrimeField e) (valPrimeField.instValStruct e) valField :=
  valField_model (predVal_isValPred e h)

/-- The map on the prime model commutes with the function symbols. -/
theorem valPrimeMap_fun (e : S ↪[Language.val] M) {n : ℕ} (g : Language.val.Functions n)
    (x : Fin n → S) :
    algebraMap (coordRing e) (valPrimeField e)
        (coordEmbedding e (Structure.funMap (L := Language.val) (M := S) g x))
      = Structure.funMap (L := Language.val) (M := valPrimeField e) g
          (fun i => algebraMap (coordRing e) (valPrimeField e) (coordEmbedding e (x i))) := by
  have hce : coordEmbedding e (Structure.funMap (L := Language.val) (M := S) g x)
      = Structure.funMap (L := Language.val) (M := coordRing e) g
          (fun i => coordEmbedding e (x i)) :=
    (coordEmbedding e).map_fun g x
  rw [hce]
  conv_rhs => rw [valFunMap_eq_ringVal (N := valPrimeField e) (g := g)
    (x := fun i => algebraMap (coordRing e) (valPrimeField e) (coordEmbedding e (x i)))]
  conv_lhs => rw [valFunMap_eq_ringVal (N := coordRing e) (g := g)
    (x := fun i => coordEmbedding e (x i))]
  exact ringHom_map_fun (algebraMap (coordRing e) (valPrimeField e)) (valToRing g)
    (fun i => coordEmbedding e (x i))

/-- **The embedding of `S` into its prime model.** -/
noncomputable def valPrimeEmbedding (e : S ↪[Language.val] M)
    (h : @IsValPred M _ (predM : M → M → Prop)) :
    S ↪[Language.val] valPrimeField e where
  toFun := fun s => algebraMap (coordRing e) (valPrimeField e) (coordEmbedding e s)
  inj' := by
    intro a b hab
    exact (coordEmbedding e).injective
      (IsFractionRing.injective (coordRing e) (valPrimeField e) hab)
  map_fun' := fun {n} g x => valPrimeMap_fun e g x
  map_rel' := by
    intro n r x
    cases r with
    | le =>
      have hL : Structure.RelMap (L := Language.val) (M := valPrimeField e) ValRel.le
            ((fun s => algebraMap (coordRing e) (valPrimeField e) (coordEmbedding e s)) ∘ x)
          ↔ predFrac (predCoord e)
              (algebraMap (coordRing e) (valPrimeField e) (coordEmbedding e (x 0)))
              (algebraMap (coordRing e) (valPrimeField e) (coordEmbedding e (x 1))) := by
        rw [relMap_two]
        rfl
      have hR : Structure.RelMap (L := Language.val) (M := S) ValRel.le x
          ↔ predM (x 0) (x 1) := relMap_two x
      rw [hL, hR]
      rw [← IsLocalization.mk'_one (M := nonZeroDivisors (coordRing e)) (S := valPrimeField e)
          (x := coordEmbedding e (x 0)),
        ← IsLocalization.mk'_one (M := nonZeroDivisors (coordRing e)) (S := valPrimeField e)
          (x := coordEmbedding e (x 1)),
        predFrac_iff (IsValPred.scale (predCoord_isValPred e h))]
      show predM (coordEval e (coordEmbedding e (x 0) * 1))
             (coordEval e (coordEmbedding e (x 1) * 1)) ↔ predM (x 0) (x 1)
      rw [mul_one, mul_one]
      have h1 : coordEval e (Ideal.Quotient.mk (relIdeal e) (FreeCommRing.of (x 0))) = e (x 0) := by
        rw [coordEval_mk, FreeCommRing.lift_of]
      have h2 : coordEval e (Ideal.Quotient.mk (relIdeal e) (FreeCommRing.of (x 1))) = e (x 1) := by
        rw [coordEval_mk, FreeCommRing.lift_of]
      show predM (coordEval e (Ideal.Quotient.mk (relIdeal e) (FreeCommRing.of (x 0))))
             (coordEval e (Ideal.Quotient.mk (relIdeal e) (FreeCommRing.of (x 1)))) ↔ predM (x 0) (x 1)
      rw [h1, h2]
      exact pred_emb_iff e (x 0) (x 1)

end PrimeField


/-! ## 10. The universal property of the prime model -/

section Universal

variable {S : Type} [Language.val.Structure S] [Language.ring.Structure S]
  [valRingHom.IsExpansionOn S]
variable {M : Type} [CommRing M] [Language.val.Structure M] [CompatibleRing M]
  [valRingHom.IsExpansionOn M] [IsDomain M]
variable {N : Type} [Field N] [CompatibleRing N] [Language.val.Structure N]
  [valRingHom.IsExpansionOn N]

/-- **The predicate on `S` computed in two different valued fields agrees.**  This is the
`L_val` analogue of `ker_lift_eq`: the truth of `v (P x) ≤ v (Q x)` at a tuple of parameters from
`S` is intrinsic to `S`, because both `e` and `f` preserve and reflect the predicate. -/
theorem predM_lift_iff (e : S ↪[Language.val] M) (f : S ↪[Language.val] N)
    (p q : FreeCommRing S) :
    predM (FreeCommRing.lift (fun s => e s) p) (FreeCommRing.lift (fun s => e s) q)
      ↔ predM (FreeCommRing.lift (fun s => f s) p) (FreeCommRing.lift (fun s => f s) q) := by
  rw [lift_eq_apply_term e p, lift_eq_apply_term e q, lift_eq_apply_term f p,
    lift_eq_apply_term f q]
  exact (pred_emb_iff e _ _).trans (pred_emb_iff f _ _).symm

/-- The map `S → N` extended to the coordinate ring. -/
noncomputable def rHom (e : S ↪[Language.val] M) (f : S ↪[Language.val] N) :
    coordRing e →+* N :=
  Ideal.Quotient.lift (relIdeal e) (FreeCommRing.lift (fun s => f s)) (fun a ha => by
    rw [ker_lift_eq e f] at ha
    exact RingHom.mem_ker.mp ha)

theorem rHom_mk (e : S ↪[Language.val] M) (f : S ↪[Language.val] N) (p : FreeCommRing S) :
    rHom e f (Ideal.Quotient.mk (relIdeal e) p) = FreeCommRing.lift (fun s => f s) p := rfl

theorem rHom_injective (e : S ↪[Language.val] M) (f : S ↪[Language.val] N) :
    Function.Injective (rHom e f) := by
  intro x y hxy
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective (I := relIdeal e) x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective (I := relIdeal e) y
  rw [rHom_mk, rHom_mk] at hxy
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, ker_lift_eq e f, RingHom.mem_ker, map_sub, hxy,
    sub_self]

/-- The predicate of the coordinate ring is the same computed in `N`. -/
theorem pred_rHom_iff (e : S ↪[Language.val] M) (f : S ↪[Language.val] N)
    (z w : coordRing e) :
    predM (rHom e f z) (rHom e f w) ↔ predM (coordEval e z) (coordEval e w) := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective (I := relIdeal e) z
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective (I := relIdeal e) w
  rw [rHom_mk, rHom_mk, coordEval_mk, coordEval_mk]
  exact (predM_lift_iff e f p q).symm

/-- The induced map on the prime model. -/
noncomputable def gHom (e : S ↪[Language.val] M) (f : S ↪[Language.val] N) :
    valPrimeField e →+* N :=
  IsFractionRing.lift (A := coordRing e) (K := valPrimeField e) (L := N) (rHom_injective e f)

theorem gHom_algebraMap (e : S ↪[Language.val] M) (f : S ↪[Language.val] N)
    (z : coordRing e) :
    gHom e f (algebraMap (coordRing e) (valPrimeField e) z) = rHom e f z :=
  IsFractionRing.lift_algebraMap (rHom_injective e f) z

theorem gHom_injective (e : S ↪[Language.val] M) (f : S ↪[Language.val] N) :
    Function.Injective (gHom e f) := by
  intro x y hxy
  have h : gHom e f (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  by_contra hne
  have hne' : x - y ≠ 0 := sub_ne_zero.mpr hne
  have h1 : gHom e f (x - y) * gHom e f ((x - y)⁻¹) = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hne', map_one]
  rw [h, zero_mul] at h1
  exact zero_ne_one h1

/-- On a fraction, `gHom` is the corresponding quotient. -/
theorem gHom_mk' (e : S ↪[Language.val] M) (f : S ↪[Language.val] N)
    (a : coordRing e) (s : nonZeroDivisors (coordRing e)) :
    gHom e f (IsLocalization.mk' (valPrimeField e) a s)
      = rHom e f a * (rHom e f (s : coordRing e))⁻¹ := by
  have hs : ((s : coordRing e)) ≠ 0 := nonZeroDivisors.ne_zero s.2
  have hsr : rHom e f (s : coordRing e) ≠ 0 := fun h =>
    hs (rHom_injective e f (by rw [h, map_zero]))
  rw [eq_mul_inv_iff_mul_eq₀ hsr]
  have hspec : IsLocalization.mk' (valPrimeField e) a s
      * algebraMap (coordRing e) (valPrimeField e) (s : coordRing e)
      = algebraMap (coordRing e) (valPrimeField e) a :=
    IsLocalization.mk'_spec (valPrimeField e) a s
  have h := congrArg (gHom e f) hspec
  simp only [map_mul, gHom_algebraMap] at h
  simpa only [mul_comm] using h

/-- **`gHom` preserves and reflects the predicate.** -/
theorem pred_gHom_iff (e : S ↪[Language.val] M) (f : S ↪[Language.val] N)
    (hM : @IsValPred M _ (predM : M → M → Prop))
    (hN : @IsValPred N _ (predM : N → N → Prop)) (x y : valPrimeField e) :
    predM (gHom e f x) (gHom e f y) ↔ predVal e x y := by
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors (coordRing e)) x
  obtain ⟨⟨c, t⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors (coordRing e)) y
  rw [gHom_mk' e f a s, gHom_mk' e f c t]
  show predM (rHom e f a * (rHom e f (s : coordRing e))⁻¹)
        (rHom e f c * (rHom e f (t : coordRing e))⁻¹)
      ↔ predFrac (predCoord e) (IsLocalization.mk' (valPrimeField e) a s)
          (IsLocalization.mk' (valPrimeField e) c t)
  rw [predFrac_iff (IsValPred.scale (predCoord_isValPred e hM))]
  show predM (rHom e f a * (rHom e f (s : coordRing e))⁻¹)
        (rHom e f c * (rHom e f (t : coordRing e))⁻¹)
      ↔ predM (coordEval e (a * (t : coordRing e))) (coordEval e (c * (s : coordRing e)))
  have hkey : predM (rHom e f (a * (t : coordRing e))) (rHom e f (c * (s : coordRing e)))
      ↔ predM (coordEval e (a * (t : coordRing e))) (coordEval e (c * (s : coordRing e))) :=
    pred_rHom_iff e f _ _
  rw [← hkey]
  have hs : ((s : coordRing e)) ≠ 0 := nonZeroDivisors.ne_zero s.2
  have ht : ((t : coordRing e)) ≠ 0 := nonZeroDivisors.ne_zero t.2
  have hsr : rHom e f (s : coordRing e) ≠ 0 := fun h =>
    hs (rHom_injective e f (by rw [h, map_zero]))
  have htr : rHom e f (t : coordRing e) ≠ 0 := fun h =>
    ht (rHom_injective e f (by rw [h, map_zero]))
  rw [show predM (rHom e f a * (rHom e f (s : coordRing e))⁻¹)
        (rHom e f c * (rHom e f (t : coordRing e))⁻¹)
      ↔ predM ((rHom e f a * (rHom e f (s : coordRing e))⁻¹)
            * (rHom e f (s : coordRing e) * rHom e f (t : coordRing e)))
          ((rHom e f c * (rHom e f (t : coordRing e))⁻¹)
            * (rHom e f (s : coordRing e) * rHom e f (t : coordRing e)))
    from IsValPred.scale hN _ _ _ (mul_ne_zero hsr htr)]
  have e1 : (rHom e f a * (rHom e f (s : coordRing e))⁻¹)
      * (rHom e f (s : coordRing e) * rHom e f (t : coordRing e))
      = rHom e f a * rHom e f (t : coordRing e) := by
    field_simp
  have e2 : (rHom e f c * (rHom e f (t : coordRing e))⁻¹)
      * (rHom e f (s : coordRing e) * rHom e f (t : coordRing e))
      = rHom e f c * rHom e f (s : coordRing e) := by
    field_simp
  rw [e1, e2, map_mul, map_mul]

/-- **A ring hom between valued fields which preserves and reflects the predicate is an
`L_val`-embedding.** -/
def embeddingOfPredRingHom {A B : Type*} [CommRing A] [CommRing B]
    [Language.val.Structure A] [Language.val.Structure B]
    [CompatibleRing A] [CompatibleRing B]
    [valRingHom.IsExpansionOn A] [valRingHom.IsExpansionOn B]
    (f : A →+* B) (hf : Function.Injective f)
    (hpred : ∀ x y : A, predM (f x) (f y) ↔ predM x y) : A ↪[Language.val] B where
  toFun := f
  inj' := hf
  map_fun' := by
    intro n g x
    rw [valFunMap_eq_ringVal (N := A) (g := g) (x := x),
      valFunMap_eq_ringVal (N := B) (g := g) (x := f ∘ x)]
    exact ringHom_map_fun f (valToRing g) x
  map_rel' := by
    intro n r x
    cases r with
    | le =>
      have h1 : Structure.RelMap (L := Language.val) (M := B) ValRel.le (f ∘ x)
          ↔ predM (f (x 0)) (f (x 1)) := by
        rw [relMap_two]
        rfl
      have h2 : Structure.RelMap (L := Language.val) (M := A) ValRel.le x
          ↔ predM (x 0) (x 1) := relMap_two x
      rw [h1, h2]
      exact hpred (x 0) (x 1)

/-- **The prime model of `valField` over `S` embeds into every valued field over `S`.** -/
theorem valPrimeField_universal (e : S ↪[Language.val] M) (f : S ↪[Language.val] N)
    (hM : @IsValPred M _ (predM : M → M → Prop))
    (hN : @IsValPred N _ (predM : N → N → Prop)) :
    ∃ g : valPrimeField e ↪[Language.val] N, g.comp (valPrimeEmbedding e hM) = f := by
  refine ⟨embeddingOfPredRingHom (gHom e f) (gHom_injective e f)
    (fun x y => pred_gHom_iff e f hM hN x y), ?_⟩
  refine FirstOrder.Language.Embedding.ext ?_
  intro s
  rw [FirstOrder.Language.Embedding.comp_apply]
  show gHom e f (algebraMap (coordRing e) (valPrimeField e) (coordEmbedding e s)) = f s
  rw [gHom_algebraMap]
  show rHom e f (Ideal.Quotient.mk (relIdeal e) (FreeCommRing.of s)) = f s
  rw [rHom_mk, FreeCommRing.lift_of]

end Universal

#print axioms ValPM.valPrimeField_universal
#print axioms ValPM.valPrimeEmbedding
#print axioms ValPM.valPrimeField_model
#print axioms ValPM.pred_gHom_iff
#print axioms ValPM.predM_lift_iff
#print axioms ValPM.model_field_of_valField

/-! ## 11. `HasPrimeModels valField valField` -/

/-- Copy of `JohnsonCriterion.HasPrimeModels` (`QE/Johnson_criterion.lean`), specialised to
`L_val`: every structure `S` that embeds into a model of `T` has an extension `S'` modelling `T₀`
which embeds into every model of `T₀` under `S`. -/
def HasPrimeModels (T₀ T : Language.val.Theory) : Prop :=
  ∀ (S : Type) [Language.val.Structure S],
    (∃ (M : T₀.ModelType.{0, 0, 0}), M ⊨ T ∧ Nonempty (S ↪[Language.val] M)) →
    ∃ (S' : T₀.ModelType.{0, 0, 0}) (e : S ↪[Language.val] S'),
      ∀ (N : T₀.ModelType.{0, 0, 0}) (f : S ↪[Language.val] N),
        ∃ g : S' ↪[Language.val] N, g.comp e = f

/-- A `valField`-model becomes a field: the ring structure is `ringStructOfVal`, `Theory.field`
is inherited from `valField`, and `IsValPred predM` is the dictionary. -/
theorem isValPred_of_valFieldModel (M : valField.ModelType) :
    ∃ (_ : CommRing M) (_ : IsDomain M) (_ : CompatibleRing M)
      (_ : valRingHom.IsExpansionOn M), @IsValPred M _ (predM : M → M → Prop) := by
  letI : Language.ring.Structure M := ringStructOfVal M
  haveI hexp : valRingHom.IsExpansionOn M := ringStructOfVal.expansion M
  have hfield : M ⊨ Theory.field := model_field_of_valField M M.is_model
  letI : Field M := FirstOrder.Field.fieldOfModelField M
  letI : CompatibleRing M := FirstOrder.Field.compatibleRingOfModelField M
  exact ⟨inferInstance, inferInstance, inferInstance, hexp, isValPred_of_model M.is_model⟩

/-- **The prime model property for the theory of valued fields in `L_val`.** -/
theorem hasPrimeModels_valField : HasPrimeModels valField valField := by
  intro S instS hS
  letI := instS
  -- `S` has the ring structure read off its `L_val` structure
  letI : Language.ring.Structure S := ringStructOfVal S
  haveI hexpS : valRingHom.IsExpansionOn S := ringStructOfVal.expansion S
  obtain ⟨M, _hMT, ⟨e⟩⟩ := hS
  -- the composite ring/field structure on `M` and the valued predicate there
  letI : Language.ring.Structure M := ringStructOfVal M
  haveI hexpM : valRingHom.IsExpansionOn M := ringStructOfVal.expansion M
  have hfieldM : M ⊨ Theory.field := model_field_of_valField M M.is_model
  letI : Field M := FirstOrder.Field.fieldOfModelField M
  letI : CompatibleRing M := FirstOrder.Field.compatibleRingOfModelField M
  have hMpred : @IsValPred M _ (predM : M → M → Prop) := isValPred_of_model M.is_model
  -- the prime model
  haveI : valPrimeField e ⊨ valField := valPrimeField_model e hMpred
  refine ⟨Theory.ModelType.of (T := valField) (valPrimeField e), valPrimeEmbedding e hMpred, ?_⟩
  intro N f
  -- the same on `N`
  letI : Language.ring.Structure N := ringStructOfVal N
  haveI hexpN : valRingHom.IsExpansionOn N := ringStructOfVal.expansion N
  have hfieldN : N ⊨ Theory.field := model_field_of_valField N N.is_model
  letI : Field N := FirstOrder.Field.fieldOfModelField N
  letI : CompatibleRing N := FirstOrder.Field.compatibleRingOfModelField N
  have hNpred : @IsValPred N _ (predM : N → N → Prop) := isValPred_of_model N.is_model
  exact valPrimeField_universal e f hMpred hNpred

/-- A smaller target theory makes the prime model property easier: the hypothesis `M ⊨ T`
that has to be met is weaker. -/
theorem hasPrimeModels_mono {T₀ T T' : Language.val.Theory} (hTT' : T' ⊆ T)
    (h : HasPrimeModels T₀ T') : HasPrimeModels T₀ T := by
  intro S instS hS
  letI := instS
  obtain ⟨M, hM, he⟩ := hS
  exact h S ⟨M, ⟨fun φ hφ => hM.realize_of_mem φ (hTT' hφ)⟩, he⟩

#print axioms ValPM.hasPrimeModels_valField
#print axioms ValPM.hasPrimeModels_mono
#print axioms ValPM.isValPred_of_valFieldModel

/-! ## 12. The theory `ACVF` in `L_val` -/

/-- The `L_val`-sentence "every monic polynomial of degree `n` has a root", read along
`valRingHom` from the language of rings. -/
noncomputable def genericMonicPolyHasRoot (n : ℕ) : Language.val.Sentence :=
  valRingHom.onBoundedFormula (Field.genericMonicPolyHasRoot n)

/-- The valuation is nontrivial: some **nonzero** element is not in the valuation ring,
`v x < v 1`.

The `x ≠ 0` conjunct is essential and its absence was a real defect: `0` satisfies `v 0 < v 1` in
*every* valued field, so `∃ x, ¬ (v 1 ≤ v x)` alone is a tautology and says nothing about
nontriviality.  The sentence below is the one that has to be used. -/
def axNontrivialF : Language.val.BoundedFormula Empty 1 := ∼((&0) =' 0) ⊓ ∼(leF 1 (&0))

/-- **Nontriviality of the valuation**, as a sentence of `L_val`. -/
def axNontrivial : Language.val.Sentence := axNontrivialF.ex

/-- **The theory of nontrivially valued algebraically closed fields in `L_val`.** -/
noncomputable def ACVF_val : Language.val.Theory :=
  valField ∪ genericMonicPolyHasRoot '' {n : ℕ | 0 < n} ∪ {axNontrivial}

theorem valField_subset_ACVF_val : valField ⊆ ACVF_val := by
  intro φ hφ
  exact Or.inl (Or.inl hφ)


/-- **Hypothesis (i) of Johnson's criterion at `L_val`**: prime models over substructures, for
`ACVF` in the language of valued fields. -/
theorem hasPrimeModels_ACVF_val : HasPrimeModels valField ACVF_val :=
  hasPrimeModels_mono valField_subset_ACVF_val hasPrimeModels_valField

#print axioms ValPM.hasPrimeModels_ACVF_val

/-! ## 13. From a valued predicate to a Mathlib valuation -/

/-- **A predicate satisfying the axioms of `valField` is a `ValuativeRel`.**  This is what makes
the `L_val` side of the development talk to Mathlib's valuation theory: `ultra` in the form
`p (x + y) x ∨ p (x + y) y` gives the additive axiom, and `scale` (an iff) gives both
multiplicativity and cancellation.  `scale` only applies to nonzero multipliers, which is why
`vle_mul_cancel` splits on `z = 0`. -/
def valuativeRelOfIsValPred {K : Type*} [Field K] {p : K → K → Prop} (h : IsValPred p) :
    ValuativeRel K where
  vle := p
  vle_total := h.total
  vle_trans := fun hxy hyz => h.trans _ _ _ hxy hyz
  vle_add := fun {_ _ _} hxz hyz =>
    (h.ultra _ _).elim (fun h' => h.trans _ _ _ h' hxz) (fun h' => h.trans _ _ _ h' hyz)
  mul_vle_mul_left := fun {_ _} hxy z => by
    rcases eq_or_ne z 0 with rfl | hz
    · simpa using h.refl 0
    · exact (h.scale _ _ z hz).mp hxy
  vle_mul_cancel := fun {_ _ z} hz hxyz => by
    rcases eq_or_ne z 0 with rfl | hz0
    · exact absurd (h.refl 0) hz
    · exact (h.scale _ _ z hz0).mpr hxyz
  not_vle_one_zero := fun h10 => one_ne_zero (h.zero_eq 1 h10)
  vle_mul_comm := fun {x y} => by
    rw [mul_comm y x]
    exact h.refl (x * y)

/-- **Every valued predicate comes from a genuine valuation**, with the same relation.  Together
with `isValPred_of_valuation` this identifies the models of `valField` with Mathlib's valued
fields. -/
theorem exists_valuation_of_isValPred {K : Type} [Field K] {p : K → K → Prop}
    (h : IsValPred p) :
    ∃ (Γ : Type) (_ : LinearOrderedCommGroupWithZero Γ) (v : Valuation K Γ),
      ∀ x y : K, p x y ↔ v x ≤ v y := by
  letI : ValuativeRel K := valuativeRelOfIsValPred h
  exact ⟨ValuativeRel.ValueGroupWithZero K, inferInstance, ValuativeRel.valuation K,
    fun x y => Valuation.vle_iff_le (ValuativeRel.valuation K)⟩

/-! ## 14. The `L_val`-structure of a model of `valField` is `valStructOf` -/

section StructEq

/-- The `L_val`-structure of a `valField`-model agrees with the one built from its predicate: the
function symbols are the ring operations, which is exactly what `valRingHom.IsExpansionOn` says,
and the relation symbol is `predM` by definition.  This is what lets the concrete-field results,
which are all stated for `valStructOf`, be applied to `valField.ModelType`s. -/
theorem valStruct_ext (M : Type) [s : Language.val.Structure M] [Field M] [CompatibleRing M]
    [hexp : valRingHom.IsExpansionOn M] :
    s = valStructOf M (predM : M → M → Prop) := by
  haveI := hexp
  -- on the ring symbols, `valStructOf` and the ambient structure both give the ring operations
  have hval : ∀ {n : ℕ} (f : Language.ring.Functions n) (y : Fin n → M),
      @Structure.funMap Language.val M (valStructOf M (predM : M → M → Prop)) n
          (valRingHom.onFunction f) y
        = @Structure.funMap Language.ring M _ n f y := by
    intro n f y
    cases f <;> simp only [CompatibleRing.funMap_add, CompatibleRing.funMap_mul,
      CompatibleRing.funMap_neg, CompatibleRing.funMap_zero, CompatibleRing.funMap_one] <;> rfl
  have hfun : ∀ {n : ℕ} (g : Language.val.Functions n) (x : Fin n → M),
      @Structure.funMap Language.val M s n g x
        = @Structure.funMap Language.val M (valStructOf M (predM : M → M → Prop)) n g x := by
    intro n g x
    have hg : valRingHom.onFunction (valToRing g) = g := by cases g <;> rfl
    rw [← hg, LHom.map_onFunction (ϕ := valRingHom) (f := valToRing g) (x := x)]
    exact (hval (valToRing g) x).symm
  have hrel : ∀ {n : ℕ} (r : Language.val.Relations n) (x : Fin n → M),
      @Structure.RelMap Language.val M s n r x
        = @Structure.RelMap Language.val M (valStructOf M (predM : M → M → Prop)) n r x := by
    intro n r x
    cases r with
    | le =>
      have hx : x = ![x 0, x 1] := by funext i; fin_cases i <;> rfl
      rw [hx]
      rfl
  obtain ⟨fm, rm⟩ := s
  simp only [valStructOf]
  congr 1
  · funext n g x
    exact hfun g x
  · funext n r x
    exact hrel r x

end StructEq

#print axioms ValPM.valStruct_ext

/-- The `L_val`-structure given by a predicate and the one given by a Mathlib valuation carrying
the same relation are the same structure.  Together with `valStruct_ext` this chains a
`valField.ModelType`'s own structure to `valStructure v` for the valuation produced by
`exists_valuation_of_isValPred`, which is the form `oneECIn_of_inputs'` is stated in. -/
theorem valStructOf_eq_valStructure {K : Type} [Field K] {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] {v : Valuation K Γ₀} {p : K → K → Prop}
    (h : ∀ x y : K, p x y ↔ v x ≤ v y) :
    valStructOf K p = FirstOrder.valStructure v := by
  simp only [valStructOf, FirstOrder.valStructure]
  congr 1
  funext n r x
  cases r with
  | le => exact propext (h (x 0) (x 1))

#print axioms ValPM.valStructOf_eq_valStructure

/-- **The nontriviality sentence says what it should**: there is a *nonzero* element outside the
valuation ring.  Phrased with the value of the constant `1` rather than `(1 : M)`, because an
abstract `L_val`-structure carries no `One` instance. -/
theorem axNontrivial_realize {M : Type*} [CommRing M] [Language.val.Structure M]
    [CompatibleRing M] [valRingHom.IsExpansionOn M] :
    (M ⊨ axNontrivial) ↔
      ∃ x : M, x ≠ 0 ∧
        ¬ predM (@Structure.funMap Language.val M _ 0 ValFunc.one (fun i => i.elim0)) x := by
  have hone : (@Structure.funMap Language.val M _ 0 ValFunc.one (fun i => i.elim0)) = (1 : M) :=
    valFunMap_one
  have hval : ∀ a : M,
      (∼((&0) =' (0 : Language.val.Term (Empty ⊕ Fin 1)))
          ⊓ ∼(leF (1 : Language.val.Term (Empty ⊕ Fin 1)) (var (Sum.inr 0)))).Realize
          (default : Empty → M) (Fin.snoc (default : Fin 0 → M) a)
        ↔ a ≠ 0 ∧
            ¬ predM (@Structure.funMap Language.val M _ 0 ValFunc.one (fun i => i.elim0)) a := by
    intro a
    rw [show (1 : Language.val.Term (Empty ⊕ Fin 1))
        = (1 : Language.val.Term (Empty ⊕ Fin 1)) from rfl]
    simp only [BoundedFormula.realize_inf, BoundedFormula.realize_not,
      BoundedFormula.realize_bdEqual, leF_realize, realize_varTerm', realize_oneTerm',
      realize_zeroTerm', valFunMap_zero, Sum.elim_inr, Fin.snoc_last, hone]
    rfl
  simp only [axNontrivial, axNontrivialF, Sentence.Realize, Formula.Realize,
    BoundedFormula.realize_ex]
  exact ⟨fun ⟨a, ha⟩ => ⟨a, (hval a).mp ha⟩, fun ⟨a, ha⟩ => ⟨a, (hval a).mpr ha⟩⟩

#print axioms ValPM.axNontrivial_realize

end ValPM

namespace ValOneEC

open scoped Polynomial

/-- An `L_val`-embedding of valued fields is an injective ring homomorphism preserving the
predicate `v x ≤ v y`.  (Copy of `FracValued.embeddingOfIsValEmb`.) -/
def embeddingOfIsValEmb {K : Type*} [Field K] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    {L : Type*} [Field L] {Γ' : Type*} [LinearOrderedCommGroupWithZero Γ']
    (v : Valuation K Γ) (w : Valuation L Γ') (f : K →+* L)
    (hinj : Function.Injective f) (hord : ∀ x y : K, v x ≤ v y ↔ w (f x) ≤ w (f y)) :
    @FirstOrder.Language.Embedding Language.val K L (valStructure v) (valStructure w) := by
  letI := valStructure v
  letI := valStructure w
  refine { toFun := f, inj' := hinj, map_fun' := ?_, map_rel' := ?_ }
  · intro n g x
    cases g with
    | add => exact map_add f (x 0) (x 1)
    | mul => exact map_mul f (x 0) (x 1)
    | neg => exact map_neg f (x 0)
    | zero => exact map_zero f
    | one => exact map_one f
  · intro n r x
    cases r with
    | le => exact (hord (x 0) (x 1)).symm

/-- The ring homomorphism underlying an `L_val`-embedding.  (Copy of
`FracValued.ringHomOfEmbedding`.) -/
def ringHomOfEmbedding {K : Type*} [Field K] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    {L : Type*} [Field L] {Γ' : Type*} [LinearOrderedCommGroupWithZero Γ']
    (v : Valuation K Γ) (w : Valuation L Γ')
    (F : @FirstOrder.Language.Embedding Language.val K L (valStructure v) (valStructure w)) :
    K →+* L := by
  letI := valStructure v
  letI := valStructure w
  exact { toFun := F
          map_one' := F.map_fun' ValFunc.one (fun i => Fin.elim0 i)
          map_zero' := F.map_fun' ValFunc.zero (fun i => Fin.elim0 i)
          map_mul' := fun x y => F.map_fun' ValFunc.mul ![x, y]
          map_add' := fun x y => F.map_fun' ValFunc.add ![x, y] }

/-! ## 2. Johnson's 1-ec property

Copy of `JohnsonCriterion.OneECIn` (`QE/Johnson_criterion.lean`). -/

/-- **1-ec** (Johnson, Definition 2.1.3): `S` is 1-ec in `N` along the embedding `i` if every
non-empty quantifier-free `S`-definable subset of `N` in one variable meets `S`. -/
def OneECIn {L : FirstOrder.Language.{0, 0}} {S : Type} {N : Type}
    [L.Structure S] [L.Structure N] (i : S ↪[L] N) : Prop :=
  ∀ (φ : L.BoundedFormula S 1), φ.IsQF →
    (∃ a, φ.Realize (fun s => i s) (fun _ => a)) →
      ∃ s : S, φ.Realize (fun s' => i s') (fun _ => i s)

/-! ## 3. Balls with centre and radius in the base field, and Boolean combinations of them

Johnson's §2.3 works with the balls of an algebraically closed valued field `K` *inside* an
extension `N`.  Here `f : K →+* N` is the (injective) map of the base field into `N` and
`IsKBall f w D` says that `D` is one of Johnson's balls with centre and radius in the image of
`K`: `{x : w (x - f c) ≤ w (f b)}`, `{x : w (x - f c) < w (f b)}`, or the whole space.
(`IsValBall` of `QE/Johnson23_valuation.lean`, transported along `f`.) -/

section Balls

variable {N : Type} [Field N] {Γ' : Type*} [LinearOrderedCommGroupWithZero Γ']

/-- The closed ball of radius `γ` about `c`. -/
def closedBall (w : Valuation N Γ') (c : N) (γ : Γ') : Set N := {x | w (x - c) ≤ γ}

/-- The open ball of radius `γ` about `c`. -/
def openBall (w : Valuation N Γ') (c : N) (γ : Γ') : Set N := {x | w (x - c) < γ}

theorem mem_closedBall {w : Valuation N Γ'} {c x : N} {γ : Γ'} :
    x ∈ closedBall w c γ ↔ w (x - c) ≤ γ := Iff.rfl

theorem mem_openBall {w : Valuation N Γ'} {c x : N} {γ : Γ'} :
    x ∈ openBall w c γ ↔ w (x - c) < γ := Iff.rfl

/-- The closed ball of radius zero is a point. -/
theorem closedBall_zero_radius (w : Valuation N Γ') (c : N) : closedBall w c 0 = {c} := by
  ext x
  rw [mem_closedBall, Set.mem_singleton_iff]
  exact ⟨fun h => sub_eq_zero.mp (w.zero_iff.mp (le_antisymm h zero_le)),
    fun h => h ▸ by simp⟩

end Balls

section Good

variable {K : Type} [Field K] {N : Type} [Field N]
variable {Γ' : Type*} [LinearOrderedCommGroupWithZero Γ']

/-- A ball of `N` with centre and radius in the image of the base field `K`. -/
inductive IsKBall (f : K →+* N) (w : Valuation N Γ') : Set N → Prop
  | closed (c b : K) : IsKBall f w (closedBall w (f c) (w (f b)))
  | openball (c b : K) : IsKBall f w (openBall w (f c) (w (f b)))
  | univ : IsKBall f w Set.univ

/-- `D` is a finite Boolean combination of balls with centre and radius in the image of `K`
(Johnson's form of a quantifier-free `K`-definable subset of `N` in one variable, Lemma 2.3.1). -/
def Good (f : K →+* N) (w : Valuation N Γ') (D : Set N) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (b : ι → Set N) (t : Set ι → Bool),
    (∀ i, IsKBall f w (b i)) ∧ ∀ x : N, (x ∈ D ↔ t {i | x ∈ b i} = true)

theorem good_empty (f : K →+* N) (w : Valuation N Γ') : Good f w ∅ := by
  refine ⟨PEmpty, inferInstance, PEmpty.elim, fun _ => false, ?_, ?_⟩
  · intro i; exact i.elim
  · intro x
    simp

theorem good_univ (f : K →+* N) (w : Valuation N Γ') : Good f w Set.univ := by
  refine ⟨PUnit, inferInstance, fun _ => Set.univ, fun _ => true, ?_, ?_⟩
  · intro _; exact IsKBall.univ
  · intro x
    simp

theorem good_singleton (f : K →+* N) (w : Valuation N Γ') (c : K) : Good f w {f c} := by
  classical
  have hball : closedBall w (f c) (w (f 0)) = {f c} := by
    rw [show f 0 = (0 : N) from map_zero f, show w (0 : N) = (0 : Γ') from map_zero w,
      closedBall_zero_radius]
  refine ⟨PUnit, inferInstance, fun _ => closedBall w (f c) (w (f 0)),
    fun S => decide S.Nonempty, ?_, ?_⟩
  · intro _; exact IsKBall.closed c 0
  · intro x
    have hiff : ({i : PUnit | x ∈ closedBall w (f c) (w (f 0))}).Nonempty ↔ x = f c := by
      constructor
      · rintro ⟨i, hi⟩
        rwa [hball] at hi
      · intro hx
        exact ⟨PUnit.unit, by rw [hball]; exact hx⟩
    show (x ∈ ({f c} : Set N)) ↔ (fun S : Set PUnit => decide S.Nonempty)
      {i : PUnit | x ∈ (fun _ => closedBall w (f c) (w (f 0))) i} = true
    rw [Set.mem_singleton_iff]
    have hbeta : (fun S : Set PUnit => decide S.Nonempty)
        {i : PUnit | x ∈ (fun _ => closedBall w (f c) (w (f 0))) i}
        = decide ({i : PUnit | x ∈ closedBall w (f c) (w (f 0))}).Nonempty := rfl
    rw [hbeta, decide_eq_true_eq]
    exact hiff.symm

theorem good_compl {f : K →+* N} {w : Valuation N Γ'} {D : Set N} (h : Good f w D) :
    Good f w Dᶜ := by
  classical
  obtain ⟨ι, _, b, t, hb, ht⟩ := h
  refine ⟨ι, inferInstance, b, fun S => !(t S), hb, ?_⟩
  intro x
  rw [Set.mem_compl_iff, ht x, Bool.not_eq_true]
  simp

theorem good_union {f : K →+* N} {w : Valuation N Γ'} {D₁ D₂ : Set N}
    (h₁ : Good f w D₁) (h₂ : Good f w D₂) : Good f w (D₁ ∪ D₂) := by
  classical
  obtain ⟨ι₁, _, b₁, t₁, hb₁, ht₁⟩ := h₁
  obtain ⟨ι₂, _, b₂, t₂, hb₂, ht₂⟩ := h₂
  refine ⟨ι₁ ⊕ ι₂, inferInstance, Sum.elim b₁ b₂,
    fun S => t₁ (Sum.inl ⁻¹' S) || t₂ (Sum.inr ⁻¹' S), ?_, ?_⟩
  · rintro (i | i)
    · exact hb₁ i
    · exact hb₂ i
  · intro x
    have e₁ : Sum.inl ⁻¹' {i : ι₁ ⊕ ι₂ | x ∈ Sum.elim b₁ b₂ i} = {i : ι₁ | x ∈ b₁ i} := by
      ext i; simp
    have e₂ : Sum.inr ⁻¹' {i : ι₁ ⊕ ι₂ | x ∈ Sum.elim b₁ b₂ i} = {i : ι₂ | x ∈ b₂ i} := by
      ext i; simp
    rw [Set.mem_union, ht₁ x, ht₂ x]
    show (t₁ {i : ι₁ | x ∈ b₁ i} = true ∨ t₂ {i : ι₂ | x ∈ b₂ i} = true) ↔
      (t₁ (Sum.inl ⁻¹' {i : ι₁ ⊕ ι₂ | x ∈ Sum.elim b₁ b₂ i})
        || t₂ (Sum.inr ⁻¹' {i : ι₁ ⊕ ι₂ | x ∈ Sum.elim b₁ b₂ i})) = true
    rw [e₁, e₂, Bool.or_eq_true]

theorem good_iUnion_finset {f : K →+* N} {w : Valuation N Γ'} {ι : Type} (s : Finset ι)
    {b : ι → Set N} (hb : ∀ i ∈ s, Good f w (b i)) : Good f w (⋃ i ∈ s, b i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using good_empty f w
  | insert i s hi ih =>
    have hins : (⋃ j ∈ insert i s, b j) = b i ∪ ⋃ j ∈ s, b j := by
      ext x
      simp only [Set.mem_iUnion, Finset.mem_insert, exists_prop, Set.mem_union]
      constructor
      · rintro ⟨j, hj | hj, hx⟩
        · exact Or.inl (hj ▸ hx)
        · exact Or.inr ⟨j, hj, hx⟩
      · rintro (hx | ⟨j, hj, hx⟩)
        · exact ⟨i, Or.inl rfl, hx⟩
        · exact ⟨j, Or.inr hj, hx⟩
    rw [hins]
    exact good_union (hb i (Finset.mem_insert_self i s))
      (ih fun j hj => hb j (Finset.mem_insert_of_mem hj))

/-- A finite set of points of the image of `K` is good. -/
theorem good_of_finite_range {f : K →+* N} {w : Valuation N Γ'} {D : Set N}
    (hfin : D.Finite) (hsub : D ⊆ Set.range f) : Good f w D := by
  classical
  have hD : D = ⋃ x ∈ hfin.toFinset, ({x} : Set N) := by
    ext y
    constructor
    · intro hy
      exact Set.mem_iUnion.mpr ⟨y, Set.mem_iUnion.mpr ⟨by
        rw [hfin.mem_toFinset]; exact hy, rfl⟩⟩
    · intro hy
      obtain ⟨x, hx⟩ := Set.mem_iUnion.mp hy
      obtain ⟨hxs, hyx⟩ := Set.mem_iUnion.mp hx
      rw [Set.mem_singleton_iff] at hyx
      rw [hyx, ← hfin.mem_toFinset]
      exact hxs
  rw [hD]
  refine good_iUnion_finset (f := f) (w := w) (b := fun x => ({x} : Set N))
    hfin.toFinset (fun x hx => ?_)
  obtain ⟨c, rfl⟩ := hsub (by rwa [hfin.mem_toFinset] at hx)
  exact good_singleton f w c

end Good


/-! ## 4. The term bridge: an `L_val`-term with parameters in `K` is a polynomial over `K`

This is the syntactic half of Johnson's Lemma 2.3.1: the `L_val`-function symbols are `+`, `*`,
`-`, `0`, `1`, so a term in the parameters `K` and one free variable denotes a polynomial with
coefficients in `K`, evaluated in the larger field `N` along the embedding `f`.

The evaluation of terms and of bounded formulas is written through the wrapper definitions
`evalTerm` and `Holds`, which fix the `L_val`-structure on `N` to be `valStructure w`; this keeps
`valStructure` out of the type-class search in the statements. -/

section Poly

variable {K : Type} [Field K] {N : Type} [Field N] {Γ' : Type*} [LinearOrderedCommGroupWithZero Γ']

/-- The polynomial in one variable represented by an `L_val`-term with parameters in `K` and one
free variable. -/
noncomputable def termToPoly : Language.val.Term (K ⊕ Fin 1) → K[X]
  | .var s => Sum.rec (fun k => Polynomial.C k) (fun _ => Polynomial.X) s
  | .func fn args =>
    match fn with
    | ValFunc.add => termToPoly (args 0) + termToPoly (args 1)
    | ValFunc.mul => termToPoly (args 0) * termToPoly (args 1)
    | ValFunc.neg => - termToPoly (args 0)
    | ValFunc.zero => 0
    | ValFunc.one => 1

/-- Evaluation of an `L_val`-term in the valued field `N` (with the structure `valStructure w`). -/
def evalTerm (w : Valuation N Γ') (t : Language.val.Term (K ⊕ Fin 1))
    (v : K ⊕ Fin 1 → N) : N := by
  letI := valStructure w
  exact t.realize v

/-- **The term bridge.**  Evaluation of a term is evaluation of the associated polynomial. -/
theorem eval₂_termToPoly (w : Valuation N Γ') (f : K →+* N)
    (t : Language.val.Term (K ⊕ Fin 1)) (β : N) :
    (termToPoly t).eval₂ f β = evalTerm w t (Sum.elim (fun k => f k) (fun _ => β)) := by
  letI := valStructure w
  change (termToPoly t).eval₂ f β = t.realize (Sum.elim (fun k => f k) (fun _ => β))
  induction t with
  | var s =>
    cases s with
    | inl k => simp [termToPoly]
    | inr i => fin_cases i; simp [termToPoly]
  | func fn args ih =>
    cases fn with
    | add =>
      change Polynomial.eval₂ f β (termToPoly (args 0) + termToPoly (args 1))
        = Term.realize (Sum.elim (fun k => f k) (fun _ => β)) (args 0)
          + Term.realize (Sum.elim (fun k => f k) (fun _ => β)) (args 1)
      rw [Polynomial.eval₂_add, ih 0, ih 1]
    | mul =>
      change Polynomial.eval₂ f β (termToPoly (args 0) * termToPoly (args 1))
        = Term.realize (Sum.elim (fun k => f k) (fun _ => β)) (args 0)
          * Term.realize (Sum.elim (fun k => f k) (fun _ => β)) (args 1)
      rw [Polynomial.eval₂_mul, ih 0, ih 1]
    | neg =>
      change Polynomial.eval₂ f β (- termToPoly (args 0))
        = - Term.realize (Sum.elim (fun k => f k) (fun _ => β)) (args 0)
      rw [Polynomial.eval₂_neg, ih 0]
    | zero =>
      change Polynomial.eval₂ f β (0 : K[X]) = (0 : N)
      rw [Polynomial.eval₂_zero]
    | one =>
      change Polynomial.eval₂ f β (1 : K[X]) = (1 : N)
      rw [Polynomial.eval₂_one]

end Poly

/-! ## 5. The zero set of a polynomial over an algebraically closed field

Johnson 2.3.1(i): over an algebraically closed `K`, the roots in `N` of a polynomial over `K` are
finitely many and lie in the image of `K`.  (Copied from `QE/ACF_validation.lean`, where it is
`finite_rootSet`.) -/

section Roots

variable {K : Type} [Field K] [IsAlgClosed K]
variable {N : Type} [Field N]

theorem finite_rootSet (f : K →+* N) (q : K[X]) (hq : q ≠ 0) :
    {β : N | q.eval₂ f β = 0}.Finite ∧ {β : N | q.eval₂ f β = 0} ⊆ Set.range f := by
  suffices H : ∀ (n : ℕ) (q : K[X]), q.natDegree ≤ n → q ≠ 0 →
      ({β : N | q.eval₂ f β = 0}.Finite ∧
        {β : N | q.eval₂ f β = 0} ⊆ Set.range f) by
    exact H q.natDegree q le_rfl hq
  intro n
  induction n with
  | zero =>
    intro q hn hq
    have hdeg : q.natDegree = 0 := Nat.le_zero.mp hn
    have hqC : q = Polynomial.C (q.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hdeg
    have hc : q.coeff 0 ≠ 0 := by
      intro h; apply hq; rw [hqC, h, Polynomial.C_0]
    have hempty : {β : N | q.eval₂ f β = 0} = ∅ := by
      ext β
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rw [hqC, Polynomial.eval₂_C]
      intro h
      exact hc (f.injective (by simpa using h))
    rw [hempty]
    exact ⟨Set.finite_empty, Set.empty_subset _⟩
  | succ n ih =>
    intro q hn hq
    rcases Nat.eq_zero_or_pos q.natDegree with h0 | hpos
    · have hqC : q = Polynomial.C (q.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero h0
      have hc : q.coeff 0 ≠ 0 := by
        intro h; apply hq; rw [hqC, h, Polynomial.C_0]
      have hempty : {β : N | q.eval₂ f β = 0} = ∅ := by
        ext β
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rw [hqC, Polynomial.eval₂_C]
        intro h
        exact hc (f.injective (by simpa using h))
      rw [hempty]
      exact ⟨Set.finite_empty, Set.empty_subset _⟩
    · have hdeg : q.degree ≠ 0 := by
        rw [Polynomial.degree_eq_natDegree hq]
        simpa using hpos.ne'
      obtain ⟨r, hr⟩ := IsAlgClosed.exists_root q hdeg
      obtain ⟨q₁, hq₁⟩ := (Polynomial.dvd_iff_isRoot (p := q)).2 hr
      have hq₁ne : q₁ ≠ 0 := by
        rintro rfl; rw [mul_zero] at hq₁; exact hq hq₁
      have hdegq : q.natDegree = q₁.natDegree + 1 := by
        rw [hq₁, Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero r) hq₁ne,
          Polynomial.natDegree_X_sub_C, add_comm]
      have hle : q₁.natDegree ≤ n := by omega
      obtain ⟨hfin, hsub⟩ := ih q₁ hle hq₁ne
      have hset : {β : N | q.eval₂ f β = 0}
          = {f r} ∪ {β : N | q₁.eval₂ f β = 0} := by
        ext β
        simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff]
        rw [hq₁]
        simp only [Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_X,
          Polynomial.eval₂_C]
        constructor
        · intro h
          rcases mul_eq_zero.mp h with h' | h'
          · exact Or.inl (sub_eq_zero.mp h')
          · exact Or.inr h'
        · rintro (h' | h')
          · rw [h', sub_self, zero_mul]
          · rw [h', mul_zero]
      rw [hset]
      exact ⟨(Set.finite_singleton _).union hfin,
        Set.union_subset (fun x hx => ⟨r, hx.symm⟩) hsub⟩

end Roots

/-! ## 6. Quantifier-free definable sets are Boolean combinations of balls

The two inputs of Johnson §2.3 that this file does *not* prove are named here as `Prop`s:
`AtomGood` is Lemma 2.3.1(ii) (the valuation inequality `v (P x) ≤ v (Q x)` defines a Boolean
combination of balls), and `GoodMeetsBase` is the conclusion of 2.3.2 together with 2.3.8 (a
nonempty Boolean combination of balls with centre and radius in `K` meets `K`).  Everything
between them is proved here. -/

section Formula

variable {K : Type} [Field K] {N : Type} [Field N] {Γ' : Type*} [LinearOrderedCommGroupWithZero Γ']

/-- Realization of a quantifier-free formula in the valued field `N` along `f : K →+* N`, with the
`L_val`-structure on `N` being `valStructure w`. -/
def Holds (w : Valuation N Γ') (f : K →+* N) (φ : Language.val.BoundedFormula K 1) (a : N) : Prop := by
  letI := valStructure w
  exact φ.Realize (fun k => f k) (fun _ => a)

/-- **Johnson, Lemma 2.3.1(ii)** (input): the value-inequality set `{x : v (P x) ≤ v (Q x)}` is a
Boolean combination of balls with centre and radius in `K`. -/
def AtomGood (f : K →+* N) (w : Valuation N Γ') : Prop :=
  ∀ P Q : K[X], Good f w {x : N | w (P.eval₂ f x) ≤ w (Q.eval₂ f x)}

/-- **Johnson, Lemmas 2.3.2 and 2.3.8** (input, in one piece): a nonempty Boolean combination of
balls with centre and radius in `K` meets the image of `K`. -/
def GoodMeetsBase (f : K →+* N) (w : Valuation N Γ') : Prop :=
  ∀ D : Set N, Good f w D → D.Nonempty → ∃ c : K, f c ∈ D

/-- A **swiss cheese**: a ball `B₀` with centre and radius in `K`, with finitely many balls
`Bᵢ ⊆ B₀` (also with centre and radius in `K`) removed.  (Johnson §2.3.) -/
def SwissCheese (f : K →+* N) (w : Valuation N Γ') (D : Set N) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (B₀ : Set N) (B : ι → Set N),
    IsKBall f w B₀ ∧ (∀ i, IsKBall f w (B i)) ∧ (∀ i, B i ⊆ B₀)
      ∧ D = B₀ \ ⋃ i, B i

/-- **Johnson, Lemma 2.3.2** (input): every Boolean combination of balls with centre and radius in
`K` is a finite union of swiss cheeses. -/
def BoolCombCheese (f : K →+* N) (w : Valuation N Γ') : Prop :=
  ∀ D : Set N, Good f w D →
    ∃ (ι : Type) (_ : Fintype ι) (C : ι → Set N),
      (∀ i, SwissCheese f w (C i)) ∧ D = ⋃ i, C i

/-- **Johnson, Lemma 2.3.8** (input): a nonempty swiss cheese meets the image of `K`. -/
def CheeseMeetsBase (f : K →+* N) (w : Valuation N Γ') : Prop :=
  ∀ D : Set N, SwissCheese f w D → D.Nonempty → ∃ c : K, f c ∈ D

/-- Lemmas 2.3.2 and 2.3.8 together give `GoodMeetsBase`: a nonempty finite union of swiss
cheeses has a nonempty member, which meets the base field. -/
theorem goodMeetsBase_of_swissCheese {f : K →+* N} {w : Valuation N Γ'}
    (h232 : BoolCombCheese f w) (h238 : CheeseMeetsBase f w) : GoodMeetsBase f w := by
  intro D hD hne
  obtain ⟨ι, _, C, hC, hDC⟩ := h232 D hD
  obtain ⟨a, ha⟩ := hne
  rw [hDC] at ha
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp ha
  obtain ⟨c, hc⟩ := h238 (C i) (hC i) ⟨a, hi⟩
  exact ⟨c, by rw [hDC]; exact Set.mem_iUnion.mpr ⟨i, hc⟩⟩

/-- **Johnson, Lemma 2.3.1, assembled**: every quantifier-free `K`-definable subset of `N` in one
variable is a Boolean combination of balls with centre and radius in `K`.  The `{P = 0}` case of
2.3.1(i) is proved (from `IsAlgClosed K`); the case `v (P x) ≤ v (Q x)` is the input
`AtomGood`. -/
theorem good_solSet [IsAlgClosed K] {f : K →+* N} {w : Valuation N Γ'}
    (hAtom : AtomGood f w) (φ : Language.val.BoundedFormula K 1) (hφ : φ.IsQF) :
    Good f w {a : N | Holds w f φ a} := by
  letI := valStructure w
  change Good f w {a : N | φ.Realize (fun k => f k) (fun _ => a)}
  refine BoundedFormula.IsQF.recOn
    (motive := fun ψ _ => Good f w {a : N | ψ.Realize (fun k => f k) (fun _ => a)}) hφ ?_ ?_ ?_
  · -- `⊥`
    have hset : {a : N | (BoundedFormula.falsum : Language.val.BoundedFormula K 1).Realize
        (fun k => f k) (fun _ => a)} = ∅ := by
      ext a
      exact ⟨fun h => h, fun h => h.elim⟩
    rw [hset]
    exact good_empty f w
  · -- atomic
    intro ψ ha
    cases ha with
    | equal t₁ t₂ =>
      have hset : {a : N | (Term.bdEqual t₁ t₂).Realize (fun k => f k) (fun _ => a)}
          = {a : N | (termToPoly t₁ - termToPoly t₂).eval₂ f a = 0} := by
        ext a
        change (evalTerm w t₁ (Sum.elim (fun k => f k) (fun _ => a))
            = evalTerm w t₂ (Sum.elim (fun k => f k) (fun _ => a)))
          ↔ (termToPoly t₁ - termToPoly t₂).eval₂ f a = 0
        rw [← eval₂_termToPoly w f t₁ a, ← eval₂_termToPoly w f t₂ a,
          Polynomial.eval₂_sub, sub_eq_zero]
      rw [hset]
      by_cases hp : termToPoly t₁ - termToPoly t₂ = 0
      · have huniv : {a : N | (termToPoly t₁ - termToPoly t₂).eval₂ f a = 0} = Set.univ := by
          ext a; simp [hp]
        rw [huniv]
        exact good_univ f w
      · exact good_of_finite_range (finite_rootSet f _ hp).1 (finite_rootSet f _ hp).2
    | rel R ts =>
      cases R with
      | le =>
        simp only [Relations.boundedFormula]
        have hset : {a : N | (BoundedFormula.rel ValRel.le ts).Realize (fun k => f k)
              (fun _ => a)}
            = {a : N | w ((termToPoly (ts 0)).eval₂ f a)
                ≤ w ((termToPoly (ts 1)).eval₂ f a)} := by
          ext a
          change (w (evalTerm w (ts 0) (Sum.elim (fun k => f k) (fun _ => a)))
              ≤ w (evalTerm w (ts 1) (Sum.elim (fun k => f k) (fun _ => a))))
            ↔ w ((termToPoly (ts 0)).eval₂ f a) ≤ w ((termToPoly (ts 1)).eval₂ f a)
          rw [← eval₂_termToPoly w f (ts 0) a, ← eval₂_termToPoly w f (ts 1) a]
        rw [hset]
        exact hAtom (termToPoly (ts 0)) (termToPoly (ts 1))
  · -- `⟹`
    intro φ₁ φ₂ _ _ ih1 ih2
    have hset : {a : N | (φ₁.imp φ₂).Realize (fun k => f k) (fun _ => a)}
        = {a : N | φ₁.Realize (fun k => f k) (fun _ => a)}ᶜ
          ∪ {a : N | φ₂.Realize (fun k => f k) (fun _ => a)} := by
      ext a
      simp only [BoundedFormula.realize_imp, Set.mem_ofPred_eq, Set.mem_union,
        Set.mem_compl_iff]
      tauto
    rw [hset]
    exact good_union (good_compl ih1) ih2

/-- **Johnson's 1-ec property for a valued field**: every nonempty quantifier-free `K`-definable
subset of `N` in one variable meets `K`.  This is Claim 2.1.5 in the valued setting: the whole
content of Johnson §2.3 after the two named inputs. -/
theorem exists_solution_in_range [IsAlgClosed K] {f : K →+* N} {w : Valuation N Γ'}
    (hAtom : AtomGood f w) (hMeets : GoodMeetsBase f w)
    (φ : Language.val.BoundedFormula K 1) (hφ : φ.IsQF) (h : ∃ a : N, Holds w f φ a) :
    ∃ c : K, Holds w f φ (f c) := by
  obtain ⟨c, hc⟩ := hMeets _ (good_solSet hAtom φ hφ) ⟨h.choose, h.choose_spec⟩
  exact ⟨c, hc⟩

end Formula


/-! ## 8. Comparability of balls and swiss cheeses (Johnson's Lemma 2.3.2)

This section closes the input `BoolCombCheese` of §6: every Boolean combination of balls with
centre and radius in `K` is a finite union of swiss cheeses.  The proofs are the standard
ultrametric arguments (cf. `QE/Johnson23_valuation.lean`), transported to balls with centre and
radius in the image of the base field. -/

section Comparability

variable {N : Type} [Field N] {Γ' : Type*} [LinearOrderedCommGroupWithZero Γ']

/-- The value of a difference is bounded by the maximum of two others. -/
theorem val_sub_le_max (w : Valuation N Γ') (a b c : N) :
    w (a - c) ≤ max (w (a - b)) (w (b - c)) := by
  have h : a - c = (a - b) + (b - c) := by ring
  rw [h]
  exact map_add_le_max _ _ _

/-- A closed ball grows when the radius grows. -/
theorem closedBall_mono (w : Valuation N Γ') {c₁ c₂ : N} {γ₁ γ₂ : Γ'}
    (h : w (c₁ - c₂) ≤ γ₂) (hγ : γ₁ ≤ γ₂) :
    closedBall w c₁ γ₁ ⊆ closedBall w c₂ γ₂ := by
  intro x hx
  rw [mem_closedBall] at hx ⊢
  exact le_trans (val_sub_le_max w x c₁ c₂) (max_le (le_trans hx hγ) h)

/-- An open ball grows when the radius grows. -/
theorem openBall_mono (w : Valuation N Γ') {c₁ c₂ : N} {γ₁ γ₂ : Γ'}
    (h : w (c₁ - c₂) < γ₂) (hγ : γ₁ ≤ γ₂) :
    openBall w c₁ γ₁ ⊆ openBall w c₂ γ₂ := by
  intro x hx
  rw [mem_openBall] at hx ⊢
  refine lt_of_le_of_lt (val_sub_le_max w x c₁ c₂) (max_lt ?_ h)
  exact lt_of_lt_of_le hx hγ

/-- **Intersecting closed balls are comparable.** -/
theorem closedBall_subset_or_subset (w : Valuation N Γ') {c₁ c₂ : N} {γ₁ γ₂ : Γ'}
    (h : (closedBall w c₁ γ₁ ∩ closedBall w c₂ γ₂).Nonempty) :
    closedBall w c₁ γ₁ ⊆ closedBall w c₂ γ₂ ∨ closedBall w c₂ γ₂ ⊆ closedBall w c₁ γ₁ := by
  obtain ⟨z, hz₁, hz₂⟩ := h
  rw [mem_closedBall] at hz₁ hz₂
  have hz₁' : w (c₁ - z) ≤ γ₁ := by
    rw [show c₁ - z = -(z - c₁) by ring, Valuation.map_neg]; exact hz₁
  have hz₂' : w (c₂ - z) ≤ γ₂ := by
    rw [show c₂ - z = -(z - c₂) by ring, Valuation.map_neg]; exact hz₂
  have h12 : w (c₁ - c₂) ≤ max γ₁ γ₂ :=
    le_trans (val_sub_le_max w c₁ z c₂) (max_le_max hz₁' hz₂)
  have h21 : w (c₂ - c₁) ≤ max γ₂ γ₁ :=
    le_trans (val_sub_le_max w c₂ z c₁) (max_le_max hz₂' hz₁)
  rcases le_total γ₁ γ₂ with hγ | hγ
  · left
    refine closedBall_mono w ?_ hγ
    rwa [max_eq_right hγ] at h12
  · right
    refine closedBall_mono w ?_ hγ
    rwa [max_eq_right hγ] at h21

/-- **Intersecting open balls are comparable.** -/
theorem openBall_subset_or_subset (w : Valuation N Γ') {c₁ c₂ : N} {γ₁ γ₂ : Γ'}
    (h : (openBall w c₁ γ₁ ∩ openBall w c₂ γ₂).Nonempty) :
    openBall w c₁ γ₁ ⊆ openBall w c₂ γ₂ ∨ openBall w c₂ γ₂ ⊆ openBall w c₁ γ₁ := by
  obtain ⟨z, hz₁, hz₂⟩ := h
  rw [mem_openBall] at hz₁ hz₂
  have hz₁' : w (c₁ - z) < γ₁ := by
    rw [show c₁ - z = -(z - c₁) by ring, Valuation.map_neg]; exact hz₁
  have hz₂' : w (c₂ - z) < γ₂ := by
    rw [show c₂ - z = -(z - c₂) by ring, Valuation.map_neg]; exact hz₂
  have h12 : w (c₁ - c₂) < max γ₁ γ₂ :=
    lt_of_le_of_lt (val_sub_le_max w c₁ z c₂) (max_lt_max hz₁' hz₂)
  have h21 : w (c₂ - c₁) < max γ₂ γ₁ :=
    lt_of_le_of_lt (val_sub_le_max w c₂ z c₁) (max_lt_max hz₂' hz₁)
  rcases le_total γ₁ γ₂ with hγ | hγ
  · left
    refine openBall_mono w ?_ hγ
    rwa [max_eq_right hγ] at h12
  · right
    refine openBall_mono w ?_ hγ
    rwa [max_eq_right hγ] at h21

/-- A closed ball of smaller radius inside an open ball. -/
theorem closedBall_subset_openBall (w : Valuation N Γ') {c d : N} {a b : N}
    (hcd : w (c - d) < w b) (ha : w a < w b) :
    closedBall w c (w a) ⊆ openBall w d (w b) := by
  intro x hx
  simp only [mem_closedBall] at hx
  simp only [mem_openBall]
  exact lt_of_le_of_lt (val_sub_le_max w x c d) (max_lt (lt_of_le_of_lt hx ha) hcd)

/-- An open ball inside a closed ball. -/
theorem openBall_subset_closedBall (w : Valuation N Γ') {c d : N} {a b : N}
    (hcd : w (c - d) ≤ w b) (ha : w a ≤ w b) :
    openBall w c (w a) ⊆ closedBall w d (w b) := by
  intro x hx
  simp only [mem_openBall] at hx
  simp only [mem_closedBall]
  exact le_trans (val_sub_le_max w x c d) (max_le (le_of_lt (lt_of_lt_of_le hx ha)) hcd)

/-- The value of `c - d` is at most the larger of two radii, given a common point `z`. -/
theorem val_sub_le_max_of_mem (w : Valuation N Γ') {z c d : N} {a b : N}
    (hz₁ : w (z - c) ≤ w a) (hz₂ : w (z - d) ≤ w b) :
    w (c - d) ≤ max (w a) (w b) := by
  have h1 : w (c - z) ≤ w a := by
    rw [show c - z = -(z - c) by ring, Valuation.map_neg]; exact hz₁
  exact le_trans (val_sub_le_max w c z d) (max_le_max h1 hz₂)

end Comparability

section KBallComparability

variable {K : Type} [Field K] {N : Type} [Field N] {Γ' : Type*} [LinearOrderedCommGroupWithZero Γ']

/-- **Johnson (2.3)** for balls with centre and radius in `K`: two such balls that meet are
comparable. -/
theorem isKBall_subset_or_subset {f : K →+* N} {w : Valuation N Γ'} {B₁ B₂ : Set N}
    (h₁ : IsKBall f w B₁) (h₂ : IsKBall f w B₂) (h : (B₁ ∩ B₂).Nonempty) :
    B₁ ⊆ B₂ ∨ B₂ ⊆ B₁ := by
  obtain ⟨z, hz₁, hz₂⟩ := h
  cases h₁ with
  | univ => exact Or.inr (Set.subset_univ _)
  | closed c a =>
    cases h₂ with
    | univ => exact Or.inl (Set.subset_univ _)
    | closed d b => exact closedBall_subset_or_subset w ⟨z, hz₁, hz₂⟩
    | openball d b =>
      simp only [mem_closedBall] at hz₁
      simp only [mem_openBall] at hz₂
      rcases lt_or_ge (w (f a)) (w (f b)) with hab | hab
      · left
        have h2 : w (z - f d) < w (f b) := hz₂
        refine closedBall_subset_openBall w ?_ hab
        have h3 : w (f c - z) < w (f b) := by
          rw [show f c - z = -(z - f c) by ring, Valuation.map_neg]
          exact lt_of_le_of_lt hz₁ hab
        exact lt_of_le_of_lt (val_sub_le_max w (f c) z (f d)) (max_lt h3 h2)
      · right
        have h2 : w (z - f d) < w (f b) := hz₂
        refine openBall_subset_closedBall (w := w) (c := f d) (d := f c) (a := f b) (b := f a) ?_ hab
        have h1 : w (f d - z) ≤ w (f a) := by
          rw [show f d - z = -(z - f d) by ring, Valuation.map_neg]
          exact le_trans h2.le hab
        have h3 : w (z - f c) ≤ w (f a) := hz₁
        exact le_trans (val_sub_le_max w (f d) z (f c)) (max_le h1 h3)
  | openball c a =>
    simp only [mem_openBall] at hz₁
    cases h₂ with
    | univ => exact Or.inl (Set.subset_univ _)
    | closed d b =>
      simp only [mem_closedBall] at hz₂
      rcases le_or_gt (w (f a)) (w (f b)) with hab | hab
      · left
        refine openBall_subset_closedBall (w := w) ?_ hab
        have h := val_sub_le_max_of_mem w (z := z) hz₁.le hz₂
        rwa [max_eq_right hab] at h
      · right
        refine closedBall_subset_openBall (w := w) (c := f d) (d := f c) (a := f b) (b := f a) ?_ hab
        have h1 : w (f d - z) < w (f a) := by
          rw [show f d - z = -(z - f d) by ring, Valuation.map_neg]
          exact lt_of_le_of_lt hz₂ hab
        have h2 : w (z - f c) < w (f a) := hz₁
        exact lt_of_le_of_lt (val_sub_le_max w (f d) z (f c)) (max_lt h1 h2)
    | openball d b => exact openBall_subset_or_subset w ⟨z, hz₁, hz₂⟩

/-- A nonempty finite intersection of balls of `K`-radius is one of them. -/
theorem exists_mem_of_iInter_finset [DecidableEq ι] {f : K →+* N} {w : Valuation N Γ'}
    {b : ι → Set N} (hb : ∀ i, IsKBall f w (b i)) {S : Finset ι} (hS : S.Nonempty)
    (hne : (⋂ i ∈ S, b i).Nonempty) :
    ∃ j ∈ S, (⋂ i ∈ S, b i) = b j := by
  revert hS hne
  induction S using Finset.induction_on with
  | empty => intro hS; exact absurd hS Finset.not_nonempty_empty
  | insert i S hiS ih =>
    intro hS hne
    by_cases hS' : S.Nonempty
    · have hne' : (⋂ k ∈ S, b k).Nonempty := by
        obtain ⟨x, hx⟩ := hne
        exact ⟨x, by
          simp only [Set.mem_iInter] at hx ⊢
          exact fun k hk => hx k (Finset.mem_insert_of_mem hk)⟩
      obtain ⟨j, hjS, hj⟩ := ih hS' hne'
      have hinter : (⋂ k ∈ insert i S, b k) = b i ∩ b j := by
        rw [show (⋂ k ∈ insert i S, b k) = b i ∩ (⋂ k ∈ S, b k) from by
          ext x; simp [Finset.mem_insert], hj]
      have hne2 : (b i ∩ b j).Nonempty := hinter ▸ hne
      rcases isKBall_subset_or_subset (hb i) (hb j) hne2 with hh | hh
      · exact ⟨i, Finset.mem_insert_self i S, by rw [hinter, Set.inter_eq_left.mpr hh]⟩
      · exact ⟨j, Finset.mem_insert_of_mem hjS, by rw [hinter, Set.inter_eq_right.mpr hh]⟩
    · have hSe : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS'
      subst hSe
      refine ⟨i, Finset.mem_singleton_self i, ?_⟩
      simp

end KBallComparability

/-! ### The cell decomposition and Lemma 2.3.2 -/

section SwissCheese

variable {ι : Type} {K : Type} [Field K] {N : Type} [Field N]
variable {Γ' : Type*} [LinearOrderedCommGroupWithZero Γ']

/-- The cell of a finite set of balls: the points lying in exactly the balls indexed by `S`. -/
def cell [Fintype ι] [DecidableEq ι] (b : ι → Set N) (S : Finset ι) : Set N :=
  (⋂ i ∈ S, b i) \ (⋃ i ∈ Sᶜ, b i)

theorem mem_cell [Fintype ι] [DecidableEq ι] {b : ι → Set N} {S : Finset ι} {x : N} :
    x ∈ cell b S ↔ ∀ i, (x ∈ b i ↔ i ∈ S) := by
  classical
  constructor
  · intro h
    have h1 : ∀ k ∈ S, x ∈ b k := by
      intro k hk
      exact (Set.mem_iInter₂.mp h.1) k hk
    have h2 : ∀ k, k ∉ S → x ∉ b k := by
      intro k hk hx
      exact h.2 (Set.mem_iUnion₂.mpr ⟨k, by simpa using hk, hx⟩)
    exact fun i => ⟨fun hx => by_contra fun hcon => h2 i hcon hx, fun hi => h1 i hi⟩
  · intro h
    refine ⟨Set.mem_iInter₂.mpr fun k hk => (h k).mpr hk, ?_⟩
    intro hx
    obtain ⟨k, hk, hkx⟩ := Set.mem_iUnion₂.mp hx
    have hk' : k ∉ S := by simpa using hk
    exact hk' ((h k).mp hkx)

/-- **The swiss-cheese content of Lemma 2.3.2.**  Every cell of a finite family of balls with
centre and radius in `K` is a swiss cheese over `K`. -/
theorem cell_swissCheese [Fintype ι] [DecidableEq ι] {f : K →+* N} {w : Valuation N Γ'}
    {b : ι → Set N} (hb : ∀ i, IsKBall f w (b i)) (S : Finset ι) :
    ∃ (τ : Type) (_ : Fintype τ) (B₀ : Set N) (B : τ → Set N),
      IsKBall f w B₀ ∧ (∀ j, IsKBall f w (B j)) ∧ (∀ j, B j ⊆ B₀) ∧
        cell b S = B₀ \ ⋃ j, B j := by
  classical
  by_cases hS : S = ∅
  · -- the empty pattern: the whole space minus all the balls
    subst hS
    refine ⟨ι, inferInstance, Set.univ, b, IsKBall.univ, hb, fun _ => Set.subset_univ _, ?_⟩
    ext x
    simp [cell]
  by_cases hne : (⋂ i ∈ S, b i).Nonempty
  · -- the intersection is one of the balls
    obtain ⟨j, hjS, hj⟩ := exists_mem_of_iInter_finset hb (Finset.nonempty_iff_ne_empty.mpr hS) hne
    by_cases hcover : ∃ i ∈ Sᶜ, b j ⊆ b i
    · -- one of the removed balls covers `b j`, so the cell is empty
      obtain ⟨i, hiS, hsub⟩ := hcover
      have hempty : cell b S = ∅ := by
        rw [cell, hj]
        exact Set.diff_eq_empty.mpr (Set.subset_iUnion₂_of_subset i hiS hsub)
      refine ⟨PUnit, inferInstance, Set.univ, fun _ => Set.univ, IsKBall.univ,
        fun _ => IsKBall.univ, fun _ => Set.subset_univ _, ?_⟩
      rw [hempty]
      ext y
      simp
    · -- otherwise the removed balls that matter are the subballs of `b j`
      push_neg at hcover
      refine ⟨{i : ι // i ∉ S ∧ b i ⊆ b j}, inferInstance, b j, fun i => b i.1,
        hb j, fun i => hb i.1, fun i => i.2.2, ?_⟩
      rw [cell, hj, Set.diff_eq]
      ext x
      constructor
      · rintro ⟨hx, hx'⟩
        refine ⟨hx, ?_⟩
        intro hmem
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hmem
        exact hx' (Set.mem_iUnion₂.mpr ⟨i.1, by simpa using i.2.1, hi⟩)
      · rintro ⟨hx, hx'⟩
        refine ⟨hx, ?_⟩
        intro hmem
        obtain ⟨i, hiS, hxi⟩ := Set.mem_iUnion₂.mp hmem
        rcases isKBall_subset_or_subset (hb i) (hb j) ⟨x, hxi, hx⟩ with hsub | hsub
        · exact hx' (Set.mem_iUnion.mpr ⟨⟨i, by simpa using hiS, hsub⟩, hxi⟩)
        · exact absurd hsub (hcover i (by simpa using hiS))
  · -- the intersection is empty, so the cell is empty
    have hempty : (⋂ i ∈ S, b i) = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    refine ⟨PUnit, inferInstance, Set.univ, fun _ => Set.univ, IsKBall.univ,
      fun _ => IsKBall.univ, fun _ => Set.subset_univ _, ?_⟩
    rw [cell, hempty]
    ext y
    simp

/-- **Johnson, Lemma 2.3.2.**  Every Boolean combination of balls with centre and radius in `K`
is a finite union of swiss cheeses over `K`.  (This discharges the input `BoolCombCheese`.) -/
theorem boolCombCheese (f : K →+* N) (w : Valuation N Γ') : BoolCombCheese f w := by
  classical
  intro D hD
  obtain ⟨ι, hι, b, t, hb, ht⟩ := hD
  haveI := hι
  refine ⟨{S : Finset ι // t (S : Set ι) = true}, inferInstance, fun S => cell b S.1,
    fun S => cell_swissCheese hb S.1, ?_⟩
  ext x
  rw [ht x, Set.mem_iUnion]
  constructor
  · intro hx
    have hcoe : ((Finset.univ.filter (fun i => x ∈ b i) : Finset ι) : Set ι) = {i | x ∈ b i} := by
      ext i; simp
    have hS₀t : t ((Finset.univ.filter (fun i => x ∈ b i) : Finset ι) : Set ι) = true := by
      rw [hcoe]; exact hx
    refine ⟨⟨Finset.univ.filter (fun i => x ∈ b i), hS₀t⟩, ?_⟩
    rw [mem_cell]
    intro i
    simp
  · rintro ⟨S, hS⟩
    rw [mem_cell] at hS
    have hpat : ((S.1 : Finset ι) : Set ι) = {i | x ∈ b i} := by
      ext i
      exact (hS i).symm
    rw [← hpat]
    exact S.2

end SwissCheese

/-! ## 7. The 1-ec step in `L_val`

Johnson's hypothesis (iii) of Lemma 2.1.4 for `T` = algebraically closed nontrivially valued
fields, `T₀` = valued fields, stated in the `Valuation` framework (rather than through the
theory `T₀`, which would additionally need the dictionary between `T₀`-models and valued
fields). -/

section OneEC

variable {K : Type} [Field K] {L : Type} [Field L]
variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
variable {Γ' : Type*} [LinearOrderedCommGroupWithZero Γ']

/-- **Johnson, hypothesis (iii) of Lemma 2.1.4, for valued fields.**  An algebraically closed
nontrivially valued field `K` is 1-ec in every valued field extension `L`, modulo the two inputs
`AtomGood` (2.3.1(ii)) and `GoodMeetsBase` (2.3.2 + 2.3.8) of Johnson §2.3. -/
theorem oneECIn_of_inputs (v : Valuation K Γ) (w : Valuation L Γ')
    (F : @FirstOrder.Language.Embedding Language.val K L (valStructure v) (valStructure w))
    [IsAlgClosed K]
    (hAtom : AtomGood (ringHomOfEmbedding v w F) w)
    (h238 : CheeseMeetsBase (ringHomOfEmbedding v w F) w) :
    @OneECIn Language.val K L (valStructure v) (valStructure w) F := by
  intro φ hφ h
  exact exists_solution_in_range hAtom
    (goodMeetsBase_of_swissCheese (boolCombCheese _ w) h238) φ hφ h

/-- The same, with Lemma 2.3.2 also as an explicit hypothesis. -/
theorem oneECIn_of_inputs₃ (v : Valuation K Γ) (w : Valuation L Γ')
    (F : @FirstOrder.Language.Embedding Language.val K L (valStructure v) (valStructure w))
    [IsAlgClosed K]
    (hAtom : AtomGood (ringHomOfEmbedding v w F) w)
    (h232 : BoolCombCheese (ringHomOfEmbedding v w F) w)
    (h238 : CheeseMeetsBase (ringHomOfEmbedding v w F) w) :
    @OneECIn Language.val K L (valStructure v) (valStructure w) F := by
  intro φ hφ h
  exact exists_solution_in_range hAtom (goodMeetsBase_of_swissCheese h232 h238) φ hφ h

/-- The same, from the single packaged input `GoodMeetsBase`. -/
theorem oneECIn_of_inputs' (v : Valuation K Γ) (w : Valuation L Γ')
    (F : @FirstOrder.Language.Embedding Language.val K L (valStructure v) (valStructure w))
    [IsAlgClosed K]
    (hAtom : AtomGood (ringHomOfEmbedding v w F) w)
    (hMeets : GoodMeetsBase (ringHomOfEmbedding v w F) w) :
    @OneECIn Language.val K L (valStructure v) (valStructure w) F := by
  intro φ hφ h
  exact exists_solution_in_range hAtom hMeets φ hφ h

end OneEC

#print axioms ValOneEC.eval₂_termToPoly
#print axioms ValOneEC.good_solSet
#print axioms ValOneEC.exists_solution_in_range
#print axioms ValOneEC.goodMeetsBase_of_swissCheese
#print axioms ValOneEC.boolCombCheese
#print axioms ValOneEC.oneECIn_of_inputs
#print axioms ValOneEC.oneECIn_of_inputs₃
#print axioms ValOneEC.oneECIn_of_inputs'


/-! ## Johnson 2.3.1(ii): the value-inequality set is a Boolean combination of `K`-balls -/

section Atom

open Polynomial

variable {K : Type} [Field K] [IsAlgClosed K] {N : Type} [Field N]
variable {Γ' : Type*} [LinearOrderedCommGroupWithZero Γ']
variable {f : K →+* N} {w : Valuation N Γ'}

/-- Evaluating a polynomial over an algebraically closed field in an extension: the value is the
leading coefficient times the product over the roots in `K` (with multiplicities). -/
theorem eval₂_prod_roots_aux (p : K[X]) (x : N) :
    Polynomial.eval₂ f x ((p.roots.map (fun a => Polynomial.X - Polynomial.C a)).prod)
      = (p.roots.map (fun a => x - f a)).prod := by
  induction p.roots using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Polynomial.eval₂_mul,
      Multiset.map_cons, Multiset.prod_cons, ih]
    simp

theorem eval₂_eq_prod_roots (p : K[X]) (x : N) :
    p.eval₂ f x = f p.leadingCoeff * (p.roots.map (fun a => x - f a)).prod := by
  have hs : p.Splits := IsAlgClosed.splits p
  conv_lhs => rw [hs.eq_prod_roots]
  rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, eval₂_prod_roots_aux]

/-- The same for values. -/
theorem val_eval₂_eq_prod_roots (p : K[X]) (x : N) :
    w (p.eval₂ f x) = w (f p.leadingCoeff) * (p.roots.map (fun a => w (x - f a))).prod := by
  rw [eval₂_eq_prod_roots, map_mul, map_multiset_prod, Multiset.map_map]
  rfl

/-- **Far from the other roots, a factor is constant**: if `x` is closer to `a` than `a` is to
`b`, then `w (x - b) = w (a - b)`. -/
theorem val_sub_eq_of_lt {x : N} {a b : K} (h : w (x - f a) < w (f a - f b)) :
    w (x - f b) = w (f a - f b) := by
  have hsplit : f a - f b = (f a - x) + (x - f b) := by ring
  rcases lt_or_ge (w (x - f b)) (w (f a - f b)) with hlt | hge
  · -- both summands are strictly below `w (a - b)`, so their sum is too
    have h1 : w ((f a - x) + (x - f b)) ≤ max (w (f a - x)) (w (x - f b)) :=
      map_add_le_max w _ _
    have h1' : w (f a - x) = w (x - f a) := by
      rw [show f a - x = -(x - f a) by ring, Valuation.map_neg]
    rw [h1'] at h1
    have hbad : w ((f a - x) + (x - f b)) < w (f a - f b) :=
      lt_of_le_of_lt h1 (max_lt h hlt)
    rw [hsplit] at hbad
    exact absurd hbad (lt_irrefl _)
  · refine le_antisymm ?_ hge
    have h2 : x - f b = (x - f a) + (f a - f b) := by ring
    rw [h2]
    exact le_trans (map_add_le_max w (x - f a) (f a - f b)) (max_le h.le le_rfl)

/-- `P = 0`: the set is everything. -/
theorem atomGood_P_zero (Q : K[X]) :
    Good f w {x : N | w ((0 : K[X]).eval₂ f x) ≤ w (Q.eval₂ f x)} := by
  have h : {x : N | w ((0 : K[X]).eval₂ f x) ≤ w (Q.eval₂ f x)} = Set.univ := by
    ext x
    simp only [Set.mem_setOf_eq, Polynomial.eval₂_zero, map_zero, Set.mem_univ, iff_true]
    exact zero_le
  rw [h]; exact good_univ f w

/-- `Q = 0`: the set is the (finite) root set of `P`. -/
theorem atomGood_Q_zero (P : K[X]) :
    Good f w {x : N | w (P.eval₂ f x) ≤ w ((0 : K[X]).eval₂ f x)} := by
  rcases eq_or_ne P 0 with rfl | hP
  · rw [show {x : N | w ((0 : K[X]).eval₂ f x) ≤ w ((0 : K[X]).eval₂ f x)} = Set.univ from by
      ext x; simp]
    exact good_univ f w
  have h : {x : N | w (P.eval₂ f x) ≤ w ((0 : K[X]).eval₂ f x)} = {x : N | P.eval₂ f x = 0} := by
    ext x
    simp only [Set.mem_setOf_eq, Polynomial.eval₂_zero, map_zero]
    constructor
    · intro hx
      by_contra hne
      exact absurd hx (not_le.mpr (pos_iff_ne_zero.mpr (w.ne_zero_iff.mpr hne)))
    · intro hx; rw [hx, map_zero]
  rw [h]
  exact good_of_finite_range (finite_rootSet f P hP).1 (finite_rootSet f P hP).2

end Atom

/-! ### Closure of `Good` and the regions of the cluster induction -/

section Master

variable {K : Type} [Field K] [IsAlgClosed K] {N : Type} [Field N]
variable {Γ' : Type*} [LinearOrderedCommGroupWithZero Γ']
variable {f : K →+* N} {w : Valuation N Γ'}

/-- A single `K`-ball is a `Good` set. -/
theorem good_of_isKBall {B : Set N} (h : IsKBall f w B) : Good f w B := by
  classical
  refine ⟨PUnit, inferInstance, fun _ => B, fun S => decide S.Nonempty, fun _ => h, ?_⟩
  intro x
  show (x ∈ B) ↔ (decide {i : PUnit | x ∈ B}.Nonempty = true)
  rw [decide_eq_true_iff]
  exact ⟨fun hx => ⟨PUnit.unit, hx⟩, fun ⟨_, hx⟩ => hx⟩

theorem good_inter {D₁ D₂ : Set N} (h₁ : Good f w D₁) (h₂ : Good f w D₂) :
    Good f w (D₁ ∩ D₂) := by
  have h : (D₁ᶜ ∪ D₂ᶜ)ᶜ = D₁ ∩ D₂ := by
    ext x; simp
  rw [← h]
  exact good_compl (good_union (good_compl h₁) (good_compl h₂))

theorem good_diff {D₁ D₂ : Set N} (h₁ : Good f w D₁) (h₂ : Good f w D₂) :
    Good f w (D₁ \ D₂) := by
  rw [Set.diff_eq]
  exact good_inter h₁ (good_compl h₂)

/-- **The near region of a root**: for `a ≠ b`, `{x : w (x - f a) < w (f a - f b)}` is a `K`-ball. -/
theorem good_near {a b : K} : Good f w (openBall w (f a) (w (f a - f b))) := by
  have h : openBall w (f a) (w (f (a - b))) = openBall w (f a) (w (f a - f b)) := by
    rw [map_sub]
  rw [← h]
  exact good_of_isKBall (IsKBall.openball a (a - b))

/-- **The far region**: `{x : w (x - f a) ≥ w (f a - f b)}`. -/
theorem good_far {a b : K} :
    Good f w ((openBall w (f a) (w (f a - f b)))ᶜ) :=
  good_compl good_near

/-- **The sphere**: `{x : w (x - f a) = w (f a - f b)}`, a Boolean combination of `K`-balls. -/
theorem good_sphere {a b : K} :
    Good f w (closedBall w (f a) (w (f a - f b)) \ openBall w (f a) (w (f a - f b))) := by
  have h : closedBall w (f a) (w (f (a - b))) = closedBall w (f a) (w (f a - f b)) := by
    rw [map_sub]
  rw [← h]
  exact good_diff (good_of_isKBall (IsKBall.closed a (a - b))) good_near

/-- A closed `K`-ball of a value radius is `Good`. -/
theorem good_closed {c b : K} : Good f w (closedBall w (f c) (w (f b))) :=
  good_of_isKBall (IsKBall.closed c b)

end Master

/-! ### Multiset product bookkeeping -/

section ProdSplit

variable {K : Type} [Field K] [DecidableEq K] {Γ' : Type*} [LinearOrderedCommGroupWithZero Γ']

/-- The occurrences of one element contribute a power to the product. -/
theorem prod_filter_eq_pow (s : Multiset K) (g : K → Γ') (a : K) :
    ((s.filter (fun b => b = a)).map g).prod = g a ^ (s.count a) := by
  induction s using Multiset.induction with
  | empty => simp
  | cons b s ih =>
    by_cases h : b = a
    · subst h
      rw [Multiset.filter_cons_of_pos (p := fun x => x = b) s rfl,
        Multiset.count_cons_self, Multiset.map_cons, Multiset.prod_cons, ih, pow_succ]
      ac_rfl
    · rw [Multiset.filter_cons_of_neg (p := fun x => x = a) s h,
        Multiset.count_cons_of_ne (Ne.symm h), ih]

/-- **Splitting a product at one element.** -/
theorem prod_split (s : Multiset K) (g : K → Γ') (a : K) :
    (s.map g).prod = g a ^ (s.count a) * ((s.filter (fun b => b ≠ a)).map g).prod := by
  induction s using Multiset.induction with
  | empty => simp
  | cons b s ih =>
    by_cases h : b = a
    · subst h
      rw [Multiset.filter_cons_of_neg (p := fun x => x ≠ b) s (by simp), Multiset.count_cons_self]
      simp only [Multiset.map_cons, Multiset.prod_cons, ih, pow_succ]
      ac_rfl
    · rw [Multiset.filter_cons_of_pos (p := fun x => x ≠ a) s h,
        Multiset.count_cons_of_ne (Ne.symm h)]
      simp only [Multiset.map_cons, Multiset.prod_cons, ih]
      ac_rfl

end ProdSplit

/-! ### The master claim of the cluster induction -/

section GammaAlgebra

variable {Γ' : Type*} [LinearOrderedCommGroupWithZero Γ']

/-- Multiplying by a nonzero power is an order embedding. -/
theorem le_mul_pow_iff {a b δ : Γ'} (hδ : δ ≠ 0) (m : ℕ) :
    a * δ ^ m ≤ b * δ ^ m ↔ a ≤ b := by
  have hcancel : b * δ ^ m * (δ ^ m)⁻¹ = b := by
    rw [mul_assoc, mul_inv_cancel₀ (pow_ne_zero m hδ), mul_one]
  have hcancel' : a * δ ^ m * (δ ^ m)⁻¹ = a := by
    rw [mul_assoc, mul_inv_cancel₀ (pow_ne_zero m hδ), mul_one]
  constructor
  · intro h
    have h' := mul_le_mul_left h ((δ ^ m)⁻¹)
    rwa [hcancel, hcancel'] at h'
  · intro h; exact mul_le_mul_left h _

/-- Multiplying by a nonzero constant: `a / c ≤ b ↔ a ≤ b * c`. -/
theorem le_mul_iff_div {a b c : Γ'} (hc : c ≠ 0) :
    a * c⁻¹ ≤ b ↔ a ≤ b * c := by
  have hcancel : a * c⁻¹ * c = a := by rw [mul_assoc, inv_mul_cancel₀ hc, mul_one]
  have hcancel' : b * c * c⁻¹ = b := by rw [mul_assoc, mul_inv_cancel₀ hc, mul_one]
  constructor
  · intro h
    have h' := mul_le_mul_left h c
    rwa [hcancel] at h'
  · intro h
    have h' := mul_le_mul_left h c⁻¹
    rwa [hcancel'] at h'

end GammaAlgebra

section MasterClaim

variable {K : Type} [Field K] [DecidableEq K] [IsAlgClosed K] {N : Type} [Field N]
variable {Γ' : Type*} [LinearOrderedCommGroupWithZero Γ']
variable {f : K →+* N} {w : Valuation N Γ'}

/-- The set whose `Good`-ness the induction proves. -/
def prodLe (p q : Multiset K) (aP aQ : K) : Set N :=
  {x : N | w (f aP) * (p.map (fun a => w (x - f a))).prod
            ≤ w (f aQ) * (q.map (fun a => w (x - f a))).prod}

/-- If no root occurs, both multisets are empty. -/
theorem eq_zero_of_toFinset_eq_empty {p : Multiset K} (h : p.toFinset = ∅) : p = 0 := by
  rw [Multiset.toFinset_eq_empty] at h
  exact h


/-- **Near region, pointwise**: if `x` is closer to `a` than the nearest other root is to `a`,
then every other root contributes its constant value. -/
theorem val_eq_of_near {p q : Multiset K} {a b : K} (hb : b ∈ p + q)
    (hmin : ∀ c ∈ p + q, c ≠ a → w (f a - f b) ≤ w (f a - f c))
    {x : N} (hx : w (x - f a) < w (f a - f b)) :
    ∀ c ∈ p + q, c ≠ a → w (x - f c) = w (f a - f c) := by
  intro c hc hca
  exact val_sub_eq_of_lt (lt_of_lt_of_le hx (hmin c hc hca))

/-- **Near region, for the product over the roots of one polynomial**: the whole product is a
constant there. -/
theorem prod_map_eq_const_of_near {p q : Multiset K} {a b : K} (hb : b ∈ p + q)
    (hmin : ∀ c ∈ p + q, c ≠ a → w (f a - f b) ≤ w (f a - f c))
    {x : N} (hx : w (x - f a) < w (f a - f b)) :
    ((p.filter (fun c => c ≠ a)).map (fun c => w (x - f c))).prod
      = ((p.filter (fun c => c ≠ a)).map (fun c => w (f a - f c))).prod := by
  have h : (p.filter (fun c => c ≠ a)).map (fun c => w (x - f c))
      = (p.filter (fun c => c ≠ a)).map (fun c => w (f a - f c)) := by
    refine Multiset.map_congr rfl ?_
    intro c hc
    obtain ⟨hcp, hca⟩ := Multiset.mem_filter.mp hc
    exact val_eq_of_near (p := p) (q := q) hb hmin hx c (Multiset.mem_add.mpr (Or.inl hcp)) hca
  rw [h]


/-- The easiest case of the ball condition: equal powers of `δ`.  The set is everything when
`w (f cP) ≤ w (f cQ)`, and the singleton `{f a}` otherwise (at the centre both sides vanish). -/
theorem good_pow_le_pow_same {a cP cQ : K} (m : ℕ) :
    Good f w {x : N | w (f cP) * (w (x - f a)) ^ m ≤ w (f cQ) * (w (x - f a)) ^ m} := by
  by_cases h : w (f cP) ≤ w (f cQ)
  · have hset : {x : N | w (f cP) * (w (x - f a)) ^ m ≤ w (f cQ) * (w (x - f a)) ^ m}
        = Set.univ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact mul_le_mul_left h _
    rw [hset]; exact good_univ f w
  · push_neg at h
    rcases eq_or_ne m 0 with rfl | hm
    · have hset : {x : N | w (f cP) * (w (x - f a)) ^ 0 ≤ w (f cQ) * (w (x - f a)) ^ 0} = ∅ := by
        ext x
        simp only [pow_zero, mul_one, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        exact not_le.mpr h
      rw [hset]; exact good_empty f w
    · have hset : {x : N | w (f cP) * (w (x - f a)) ^ m ≤ w (f cQ) * (w (x - f a)) ^ m}
          = {f a} := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
        constructor
        · intro hx
          by_contra hne
          have hδ : w (x - f a) ≠ 0 := by
            intro h0
            exact hne (sub_eq_zero.mp (w.zero_iff.mp h0))
          have hle : w (f cP) ≤ w (f cQ) :=
            (le_mul_pow_iff (δ := w (x - f a)) hδ m).mp hx
          exact absurd hle (not_le.mpr h)
        · intro hx
          subst hx
          rw [show f a - f a = (0 : N) from sub_self _, map_zero,
            zero_pow hm, mul_zero, mul_zero]
      rw [hset]; exact good_singleton f w a

/-! #### The ball condition with unequal multiplicities -/

/-- `w (f c) = 0` only for `c = 0`. -/
theorem val_eq_zero_iff (c : K) : w (f c) = 0 ↔ c = 0 := by
  rw [w.zero_iff, ← map_zero f, f.injective.eq_iff]

/-- A `d`-th root of a quotient of two values is again a value of `w ∘ f`: `K` is algebraically
closed, so its group of values is divisible. -/
theorem exists_val_pow_div (cP cQ : K) {d : ℕ} (hd : 0 < d) :
    ∃ e : K, w (f e) ^ d = w (f cP) * (w (f cQ))⁻¹ := by
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq (cP * cQ⁻¹) hd
  refine ⟨b, ?_⟩
  rw [← map_pow w (f b), ← map_pow f b d, hb]
  simp only [map_mul, map_inv₀]

/-- `c * a ≤ b ↔ a ≤ b * c⁻¹` for `c ≠ 0`. -/
theorem mul_le_iff_le_mul_inv {a b c : Γ'} (hc : c ≠ 0) : c * a ≤ b ↔ a ≤ b * c⁻¹ := by
  constructor
  · intro h
    have h' := mul_le_mul_left h c⁻¹
    rw [mul_comm c a, mul_assoc, mul_inv_cancel₀ hc, mul_one] at h'
    exact h'
  · intro h
    have h' := mul_le_mul_left h c
    rw [mul_assoc, inv_mul_cancel₀ hc, mul_one] at h'
    rwa [mul_comm c a]

/-- `a ≤ b * c ↔ a * c⁻¹ ≤ b` for `c ≠ 0`. -/
theorem le_mul_iff_mul_inv_le {a b c : Γ'} (hc : c ≠ 0) : a ≤ b * c ↔ a * c⁻¹ ≤ b := by
  constructor
  · intro h
    have h' := mul_le_mul_left h c⁻¹
    rw [mul_assoc, mul_inv_cancel₀ hc, mul_one] at h'
    exact h'
  · intro h
    have h' := mul_le_mul_left h c
    rw [mul_assoc, inv_mul_cancel₀ hc, mul_one] at h'
    exact h'

/-- `a ≤ c * b ↔ a * c⁻¹ ≤ b` for `c ≠ 0`. -/
theorem le_mul_left_iff_mul_inv_le {a b c : Γ'} (hc : c ≠ 0) : a ≤ c * b ↔ a * c⁻¹ ≤ b := by
  rw [mul_comm c b]
  exact le_mul_iff_mul_inv_le hc

/-- **The ball condition when `m < n`.**  With `d = n - m > 0`, off the centre the condition
`c_P δ^m ≤ c_Q δ^{m+d}` reads `w (f e) ≤ δ`, and at the centre it holds exactly when `m > 0`.
Hence the complement of the open ball of radius `w (f e)`, together with the centre if `m > 0`. -/
theorem good_pow_le_pow_lt {a cP cQ e : K} (hcQ : cQ ≠ 0) {m d : ℕ} (hd : 0 < d)
    (he : w (f e) ^ d = w (f cP) * (w (f cQ))⁻¹) :
    Good f w {x : N | w (f cP) * (w (x - f a)) ^ m
      ≤ w (f cQ) * (w (x - f a)) ^ (m + d)} := by
  have hd0 : d ≠ 0 := Nat.pos_iff_ne_zero.mp hd
  have hQ : w (f cQ) ≠ 0 := fun h => hcQ ((val_eq_zero_iff cQ).mp h)
  by_cases hcP : cP = 0
  · have hset : {x : N | w (f cP) * (w (x - f a)) ^ m
        ≤ w (f cQ) * (w (x - f a)) ^ (m + d)} = Set.univ := by
      ext x
      simp only [hcP, map_zero, w.map_zero, zero_mul, Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact zero_le
    rw [hset]; exact good_univ f w
  · have hP : w (f cP) ≠ 0 := fun h => hcP ((val_eq_zero_iff cP).mp h)
    have hfe : w (f e) ≠ 0 := by
      intro h
      have h1 : w (f e) ^ d = 0 := by rw [h]; exact zero_pow hd0
      rw [he] at h1
      exact (mul_ne_zero hP (inv_ne_zero hQ)) h1
    have hoff : ∀ x : N, x ≠ f a →
        (w (f cP) * (w (x - f a)) ^ m ≤ w (f cQ) * (w (x - f a)) ^ (m + d)
          ↔ ¬ w (x - f a) < w (f e)) := by
      intro x hx
      have hδ : w (x - f a) ≠ 0 := fun h => hx (sub_eq_zero.mp (w.zero_iff.mp h))
      have hstep : w (f cQ) * (w (x - f a)) ^ (m + d)
          = (w (f cQ) * (w (x - f a)) ^ d) * (w (x - f a)) ^ m := by
        rw [pow_add, mul_comm ((w (x - f a)) ^ m) ((w (x - f a)) ^ d), mul_assoc]
      rw [hstep, le_mul_pow_iff (δ := w (x - f a)) hδ m, le_mul_left_iff_mul_inv_le hQ, ← he,
        not_lt]
      exact pow_le_pow_iff_left₀ (a := w (f e)) (b := w (x - f a)) zero_le zero_le hd0
    rcases eq_or_ne m 0 with hm | hm
    · subst hm
      have hset : {x : N | w (f cP) * (w (x - f a)) ^ 0
          ≤ w (f cQ) * (w (x - f a)) ^ (0 + d)}
          = (openBall w (f a) (w (f e)))ᶜ := by
        ext x
        simp only [openBall, Set.mem_setOf_eq, Set.mem_compl_iff]
        by_cases hx : x = f a
        · subst hx
          rw [sub_self, w.map_zero, Nat.zero_add, zero_pow hd0, mul_zero, pow_zero, mul_one]
          exact ⟨fun h => False.elim (hP (le_antisymm h zero_le)),
            fun h => False.elim (h (pos_iff_ne_zero.mpr hfe))⟩
        · exact hoff x hx
      rw [hset]
      exact good_compl (good_of_isKBall (IsKBall.openball a e))
    · have hmd : m + d ≠ 0 := by omega
      have hset : {x : N | w (f cP) * (w (x - f a)) ^ m
          ≤ w (f cQ) * (w (x - f a)) ^ (m + d)}
          = {f a} ∪ (openBall w (f a) (w (f e)))ᶜ := by
        ext x
        simp only [openBall, Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff,
          Set.mem_compl_iff]
        by_cases hx : x = f a
        · subst hx
          rw [sub_self, w.map_zero, zero_pow hm, zero_pow hmd, mul_zero, mul_zero]
          exact ⟨fun _ => Or.inl rfl, fun _ => le_refl 0⟩
        · rw [hoff x hx]
          exact ⟨fun h => Or.inr h, fun h => h.elim (fun h' => absurd h' hx) id⟩
      rw [hset]
      exact good_union (good_singleton f w a)
        (good_compl (good_of_isKBall (IsKBall.openball a e)))

/-- **The ball condition when `m > n`.**  With `d = m - n > 0`, the condition
`c_P δ^{n+d} ≤ c_Q δ^n` reads `δ ≤ w (f e)`, and the centre always satisfies it, so the set is
the closed ball of radius `w (f e)`. -/
theorem good_pow_le_pow_gt {a cP cQ e : K} (hcP : cP ≠ 0) {n d : ℕ} (hd : 0 < d)
    (he : w (f e) ^ d = w (f cQ) * (w (f cP))⁻¹) :
    Good f w {x : N | w (f cP) * (w (x - f a)) ^ (n + d)
      ≤ w (f cQ) * (w (x - f a)) ^ n} := by
  have hd0 : d ≠ 0 := Nat.pos_iff_ne_zero.mp hd
  have hP : w (f cP) ≠ 0 := fun h => hcP ((val_eq_zero_iff cP).mp h)
  have hnd : n + d ≠ 0 := by omega
  have hset : {x : N | w (f cP) * (w (x - f a)) ^ (n + d)
      ≤ w (f cQ) * (w (x - f a)) ^ n} = closedBall w (f a) (w (f e)) := by
    ext x
    simp only [closedBall, Set.mem_setOf_eq]
    by_cases hx : x = f a
    · subst hx
      rw [sub_self, w.map_zero, zero_pow hnd, mul_zero]
      rcases eq_or_ne n 0 with hn | hn
      · subst hn
        rw [pow_zero, mul_one]
        exact ⟨fun _ => zero_le, fun _ => zero_le⟩
      · rw [zero_pow hn, mul_zero]
        exact ⟨fun _ => zero_le, fun _ => le_refl 0⟩
    · have hδ : w (x - f a) ≠ 0 := fun h => hx (sub_eq_zero.mp (w.zero_iff.mp h))
      have hstep : w (f cP) * (w (x - f a)) ^ (n + d)
          = (w (f cP) * (w (x - f a)) ^ d) * (w (x - f a)) ^ n := by
        rw [pow_add, mul_comm ((w (x - f a)) ^ n) ((w (x - f a)) ^ d), mul_assoc]
      rw [hstep, le_mul_pow_iff (δ := w (x - f a)) hδ n, mul_le_iff_le_mul_inv hP, ← he]
      exact pow_le_pow_iff_left₀ (a := w (x - f a)) (b := w (f e)) zero_le zero_le hd0
  rw [hset]
  exact good_closed (c := a) (b := e)

/-!
## Johnson 2.3.1(ii) for an algebraically closed base field: the cell decomposition

Write `d_c := w (x - f c)` for `c : K`, `A` for the finite set of roots of `P` and `Q` in `K`
(algebraic closedness makes `P` split, so `w (P x) = w (f P.lc) * ∏_{c ∈ A} d_c ^ (count c)`,
`val_eval₂_eq_prod_roots`), and `γ_{ac} := w (f a - f c)`.

The two ultrametric facts used (both from `w (u + v) ≤ max (w u) (w v)`):

* `closer_eq` : `d_a ≤ d_c ↔ x` lies in the open ball of radius `γ_{ac}` around `f a`, or on the
  sphere of that radius around `f c`, or outside both closed balls;
* `prod_map_split` : if `a` is a nearest root and `S = {c ∈ A | γ_{ac} ≤ d_a}`, then `d_c = d_a`
  for `c ∈ S` (two roots at least as close as `c` forces the max rule) and `d_c = γ_{ac}` for
  `c ∉ S` (`val_sub_eq_of_lt`).

Hence, on the cell `cluster A a S` (a finite intersection of `K`-balls, so `Good`), the product
over `A` collapses to `d_a ^ (∑_{c ∈ S} count c)` times an explicit constant, which is absorbed
into the coefficients by `absorb`; the condition becomes the one-variable inequality
`w (f eP) * δ ^ m ≤ w (f eQ) * δ ^ n` (`good_pow_le_pow`, with `m < n`, `m > n` and `m = n`),
solved by `good_pow_le_pow_lt` / `good_pow_le_pow_gt` / `good_pow_le_pow_same` (the `d`-th root
exists because `K` is algebraically closed, `exists_val_pow_div`).

Since every `x` has a nearest root `a ∈ A` (`Finset.exists_min_image`) and the associated `S` is
determined by `x`, the whole set is the finite union of the `Good` pieces
`cluster A a S ∩ clusterCond …`; `prodLe_good` assembles this and `atomGood_of_isAlgClosed`
transfers it to `AtomGood` via `val_eval₂_eq_prod_roots` and the degenerate cases
`atomGood_P_zero` / `atomGood_Q_zero`.
-/

/-! #### Ultrametric comparisons of distances to the roots -/

/-- `w (f a - f c)` is bounded by the maximum of the two distances of `x` from `f a` and `f c`. -/
theorem val_sub_le_max_of_dist {x : N} (a c : K) :
    w (f a - f c) ≤ max (w (x - f a)) (w (x - f c)) := by
  have h : f a - f c = (f a - x) + (x - f c) := by ring
  rw [h]
  refine le_trans (map_add_le_max w _ _) (le_of_eq ?_)
  rw [show f a - x = -(x - f a) by ring, Valuation.map_neg]

/-- **Closest-root comparison.**  `x` is at least as close to `f a` as to `f c` exactly when one
of three `K`-ball conditions holds: it lies in the open ball of radius `w (f a - f c)` around
`f a`, or on the sphere of that radius around `f c`, or outside both closed balls. -/
theorem closer_eq (a c : K) :
    {x : N | w (x - f a) ≤ w (x - f c)} =
      openBall w (f a) (w (f a - f c))
        ∪ (closedBall w (f c) (w (f a - f c)) \ openBall w (f c) (w (f a - f c)))
        ∪ (closedBall w (f a) (w (f a - f c)) ∪ closedBall w (f c) (w (f a - f c)))ᶜ := by
  have key : ∀ x : N, (w (x - f a) ≤ w (x - f c) ↔
      (w (x - f a) < w (f a - f c) ∨
        (w (x - f c) ≤ w (f a - f c) ∧ w (f a - f c) ≤ w (x - f c)) ∨
        (w (f a - f c) < w (x - f a) ∧ w (f a - f c) < w (x - f c)))) := by
    intro x
    have U1 : w (x - f c) ≤ max (w (x - f a)) (w (f a - f c)) := by
      have h : x - f c = (x - f a) + (f a - f c) := by ring
      rw [h]
      exact map_add_le_max w _ _
    have U2 : w (x - f a) ≤ max (w (x - f c)) (w (f a - f c)) := by
      have h : x - f a = (x - f c) + (f c - f a) := by ring
      rw [h]
      refine le_trans (map_add_le_max w _ _) (le_of_eq ?_)
      rw [show f c - f a = -(f a - f c) by ring, Valuation.map_neg]
    have U3 := val_sub_le_max_of_dist (f := f) (w := w) (x := x) a c
    constructor
    · intro h
      by_cases h1 : w (x - f a) < w (f a - f c)
      · exact Or.inl h1
      · by_cases h2 : w (x - f c) ≤ w (f a - f c)
        · exact Or.inr (Or.inl ⟨h2, le_trans (not_lt.mp h1) h⟩)
        · have h3 : w (x - f c) ≤ w (x - f a) := by
            rw [max_eq_left (not_lt.mp h1)] at U1
            exact U1
          exact Or.inr (Or.inr ⟨lt_of_lt_of_le (not_le.mp h2) h3, not_le.mp h2⟩)
    · rintro (h1 | ⟨h2, h3⟩ | ⟨h2, h3⟩)
      · by_contra hcon
        rw [max_eq_left (not_le.mp hcon).le] at U3
        exact absurd U3 (not_le.mpr h1)
      · rw [max_eq_left h3] at U2
        exact U2
      · rw [max_eq_left h3.le] at U2
        exact U2
  ext x
  have hset : (x ∈ openBall w (f a) (w (f a - f c))
        ∪ (closedBall w (f c) (w (f a - f c)) \ openBall w (f c) (w (f a - f c)))
        ∪ (closedBall w (f a) (w (f a - f c)) ∪ closedBall w (f c) (w (f a - f c)))ᶜ) ↔
      (w (x - f a) < w (f a - f c) ∨
        (w (x - f c) ≤ w (f a - f c) ∧ w (f a - f c) ≤ w (x - f c)) ∨
        (w (f a - f c) < w (x - f a) ∧ w (f a - f c) < w (x - f c))) := by
    simp only [Set.mem_union, Set.mem_diff, Set.mem_compl_iff, mem_openBall, mem_closedBall,
      not_or, not_le, not_lt]
    tauto
  simp only [Set.mem_setOf_eq]
  exact (key x).trans hset.symm

/-- The points at least as close to `f a` as to `f c` form a `Good` set. -/
theorem good_closer (a c : K) : Good f w {x : N | w (x - f a) ≤ w (x - f c)} := by
  rw [closer_eq]
  have hγ : w (f a - f c) = w (f (a - c)) := by rw [← RingHom.map_sub f a c]
  rw [hγ]
  refine good_union (good_union ?_ ?_) ?_
  · exact good_of_isKBall (IsKBall.openball a (a - c))
  · exact good_diff (good_of_isKBall (IsKBall.closed c (a - c)))
      (good_of_isKBall (IsKBall.openball c (a - c)))
  · exact good_compl (good_union (good_of_isKBall (IsKBall.closed a (a - c)))
      (good_of_isKBall (IsKBall.closed c (a - c))))

/-- A finite intersection of `Good` sets is `Good`. -/
theorem good_iInter_finset {ι : Type} (s : Finset ι) {b : ι → Set N}
    (hb : ∀ i ∈ s, Good f w (b i)) : Good f w (⋂ i ∈ s, b i) := by
  classical
  have h : (⋂ i ∈ s, b i) = (⋃ i ∈ s, (b i)ᶜ)ᶜ := by
    ext x
    simp
  rw [h]
  exact good_compl (good_iUnion_finset s fun i hi => good_compl (hb i hi))

/-! #### Multiset products over a superset of the root set -/

/-- A product of distances depends only on the multiplicities of the roots. -/
theorem prod_map_count {p : Multiset K} {A : Finset K} (hA : p.toFinset ⊆ A) (x : N) :
    (p.map (fun c => w (x - f c))).prod = ∏ c ∈ A, (w (x - f c)) ^ (p.count c) := by
  rw [Finset.prod_multiset_map_count]
  refine Finset.prod_subset hA ?_
  intro c _ hc
  have hc' : c ∉ p := by simpa using hc
  rw [Multiset.count_eq_zero_of_notMem hc', pow_zero]

/-- **Splitting a product into the nearest roots and the constant factors.**  If `a` is a nearest
root to `x` and `S` is the set of roots whose distance from `f a` is at most `δ = w (x - f a)`,
then the product over the roots of `p` is `δ ^ (multiplicity in S)` times the product of the
constant values `w (f a - f c)` over the remaining roots. -/
theorem prod_map_split {p : Multiset K} {A : Finset K} (hA : p.toFinset ⊆ A)
    {a : K} {S : Finset K} (hSA : S ⊆ A) {x : N}
    (hcl : ∀ c ∈ A, w (x - f a) ≤ w (x - f c))
    (hS : ∀ c ∈ A, (w (f a - f c) ≤ w (x - f a) ↔ c ∈ S)) :
    (p.map (fun c => w (x - f c))).prod
      = (w (x - f a)) ^ (∑ c ∈ S, p.count c)
        * ∏ c ∈ A \ S, (w (f a - f c)) ^ (p.count c) := by
  have hT : ∀ c ∈ A \ S, (w (x - f c)) ^ (p.count c) = (w (f a - f c)) ^ (p.count c) := by
    intro c hc
    obtain ⟨hcA, hcS⟩ := Finset.mem_sdiff.mp hc
    have hgt : w (x - f a) < w (f a - f c) :=
      not_le.mp fun hle => hcS ((hS c hcA).mp hle)
    rw [val_sub_eq_of_lt hgt]
  have hU : ∀ c ∈ S, (w (x - f c)) ^ (p.count c) = (w (x - f a)) ^ (p.count c) := by
    intro c hc
    have hcA := hSA hc
    have hle : w (f a - f c) ≤ w (x - f a) := (hS c hcA).mpr hc
    have h1 : w (x - f c) ≤ max (w (x - f a)) (w (f a - f c)) := by
      have h : x - f c = (x - f a) + (f a - f c) := by ring
      rw [h]
      exact map_add_le_max w _ _
    rw [max_eq_left hle] at h1
    rw [show w (x - f c) = w (x - f a) from le_antisymm h1 (hcl c hcA)]
  rw [prod_map_count hA x, ← Finset.prod_sdiff hSA,
    Finset.prod_congr rfl hT, Finset.prod_congr rfl hU, Finset.prod_pow_eq_pow_sum]
  exact mul_comm _ _

/-! #### Absorbing the constant factors into a coefficient -/

/-- Multiply a coefficient by the constants `(a - c) ^ (multiplicity of c in p)` for `c ∈ T`. -/
def absorb (aP a : K) (p : Multiset K) (T : Finset K) : K :=
  aP * ∏ c ∈ T, (a - c) ^ (p.count c)

/-- The value of the absorbed coefficient. -/
theorem val_absorb (aP a : K) (p : Multiset K) (T : Finset K) :
    w (f (absorb aP a p T)) = w (f aP) * ∏ c ∈ T, (w (f a - f c)) ^ (p.count c) := by
  have hf : f (absorb aP a p T) = f aP * ∏ c ∈ T, (f a - f c) ^ (p.count c) := by
    unfold absorb
    rw [map_mul, map_prod]
    congr 1
    refine Finset.prod_congr rfl ?_
    intro c _
    rw [map_pow, RingHom.map_sub]
  rw [hf, map_mul, map_prod]
  congr 1
  refine Finset.prod_congr rfl ?_
  intro c _
  rw [map_pow]

/-- The absorbed form of the product, stated so that it can be rewritten in either direction. -/
theorem absorb_mul_pow (aP a : K) (p : Multiset K) (S T : Finset K) (δ : Γ') :
    w (f (absorb aP a p T)) * δ ^ (∑ c ∈ S, p.count c)
      = w (f aP) * (δ ^ (∑ c ∈ S, p.count c)
          * ∏ c ∈ T, (w (f a - f c)) ^ (p.count c)) := by
  rw [val_absorb]
  calc w (f aP) * (∏ c ∈ T, (w (f a - f c)) ^ (p.count c)) * δ ^ (∑ c ∈ S, p.count c)
      = w (f aP) * ((∏ c ∈ T, (w (f a - f c)) ^ (p.count c)) * δ ^ (∑ c ∈ S, p.count c)) :=
        mul_assoc _ _ _
    _ = w (f aP) * (δ ^ (∑ c ∈ S, p.count c)
          * ∏ c ∈ T, (w (f a - f c)) ^ (p.count c)) := by
        rw [mul_comm (∏ c ∈ T, (w (f a - f c)) ^ (p.count c)) (δ ^ (∑ c ∈ S, p.count c))]

/-! #### The one-variable condition -/

/-- A product is nonnegative, so `w (f eP) * δ ^ M ≤ 0` is `{x : δ ^ M = 0}` when `eP ≠ 0`. -/
theorem good_le_zero {a eP : K} (M : ℕ) :
    Good f w {x : N | w (f eP) * (w (x - f a)) ^ M ≤ 0} := by
  rcases eq_or_ne eP 0 with hP | hP
  · have h : {x : N | w (f eP) * (w (x - f a)) ^ M ≤ 0} = Set.univ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true, hP, map_zero, w.map_zero, zero_mul]
      exact zero_le
    rw [h]
    exact good_univ f w
  · have hP' : w (f eP) ≠ 0 := fun h => hP ((val_eq_zero_iff eP).mp h)
    rcases eq_or_ne M 0 with hM | hM
    · have h : {x : N | w (f eP) * (w (x - f a)) ^ M ≤ 0} = ∅ := by
        ext x
        simp only [Set.mem_setOf_eq, hM, pow_zero, mul_one, Set.mem_empty_iff_false, iff_false]
        exact not_le.mpr (pos_iff_ne_zero.mpr hP')
      rw [h]
      exact good_empty f w
    · have h : {x : N | w (f eP) * (w (x - f a)) ^ M ≤ 0} = {f a} := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
        constructor
        · intro hle
          have hzero : w (x - f a) = 0 := by
            by_contra hδ
            exact absurd hle (not_le.mpr (mul_pos (pos_iff_ne_zero.mpr hP')
              (pow_pos (pos_iff_ne_zero.mpr hδ) M)))
          exact sub_eq_zero.mp (w.zero_iff.mp hzero)
        · rintro rfl
          simp [hM]
      rw [h]
      exact good_singleton f w a

/-- **The one-variable condition in full generality**: `w (f eP) * δ ^ m ≤ w (f eQ) * δ ^ n`. -/
theorem good_pow_le_pow (a eP eQ : K) (m n : ℕ) :
    Good f w {x : N | w (f eP) * (w (x - f a)) ^ m ≤ w (f eQ) * (w (x - f a)) ^ n} := by
  rcases lt_trichotomy m n with h | h | h
  · obtain ⟨d, hd⟩ : ∃ d, n = m + d := ⟨n - m, (Nat.add_sub_cancel' h.le).symm⟩
    have hd0 : 0 < d := by omega
    rw [hd]
    rcases eq_or_ne eQ 0 with hQ | hQ
    · simp only [hQ, map_zero, w.map_zero, zero_mul]
      exact good_le_zero m
    · obtain ⟨e, he⟩ := exists_val_pow_div (w := w) eP eQ hd0
      exact good_pow_le_pow_lt hQ hd0 he
  · subst h
    exact good_pow_le_pow_same m
  · obtain ⟨d, hd⟩ : ∃ d, m = n + d := ⟨m - n, (Nat.add_sub_cancel' h.le).symm⟩
    have hd0 : 0 < d := by omega
    rw [hd]
    rcases eq_or_ne eP 0 with hP | hP
    · have hset : {x : N | w (f eP) * (w (x - f a)) ^ (n + d)
          ≤ w (f eQ) * (w (x - f a)) ^ n} = Set.univ := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true, hP, map_zero, w.map_zero, zero_mul]
        exact zero_le
      rw [hset]
      exact good_univ f w
    · obtain ⟨e, he⟩ := exists_val_pow_div (w := w) eQ eP hd0
      exact good_pow_le_pow_gt hP hd0 he

/-! #### The cells of the decomposition -/

/-- The cell indexed by a nearest root `a ∈ A` and the set `S` of roots at distance at most
`δ = w (x - f a)` from `f a`. -/
def cluster (f : K →+* N) (w : Valuation N Γ') (A : Finset K) (a : K)
    (S : Finset K) : Set N :=
  {x : N | (∀ c ∈ A, w (x - f a) ≤ w (x - f c)) ∧
    ∀ c ∈ A, (w (f a - f c) ≤ w (x - f a) ↔ c ∈ S)}

/-- A cell is a finite intersection of `K`-balls. -/
theorem cluster_eq_iInter (A : Finset K) (a : K) (S : Finset K) :
    cluster f w A a S = ⋂ c ∈ A, ({x : N | w (x - f a) ≤ w (x - f c)}
      ∩ (if c ∈ S then (openBall w (f a) (w (f a - f c)))ᶜ
         else openBall w (f a) (w (f a - f c)))) := by
  ext x
  simp only [cluster, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_inter_iff, Set.mem_compl_iff,
    mem_openBall]
  constructor
  · rintro ⟨h1, h2⟩ c hc
    refine ⟨h1 c hc, ?_⟩
    by_cases hcS : c ∈ S
    · rw [if_pos hcS]
      exact not_lt.mpr ((h2 c hc).mpr hcS)
    · rw [if_neg hcS]
      exact not_le.mp fun hle => hcS ((h2 c hc).mp hle)
  · intro h
    refine ⟨fun c hc => (h c hc).1, fun c hc => ?_⟩
    by_cases hcS : c ∈ S
    · have h2 := (h c hc).2
      rw [if_pos hcS] at h2
      exact ⟨fun _ => hcS, fun _ => not_lt.mp h2⟩
    · have h2 := (h c hc).2
      rw [if_neg hcS] at h2
      exact ⟨fun hle => absurd hle (not_le.mpr h2), fun hc' => absurd hc' hcS⟩

theorem cluster_good (A : Finset K) (a : K) (S : Finset K) : Good f w (cluster f w A a S) := by
  rw [cluster_eq_iInter]
  refine good_iInter_finset A fun c _ => ?_
  by_cases hcS : c ∈ S
  · rw [if_pos hcS]
    exact good_inter (good_closer a c) (good_compl (good_near (a := a) (b := c)))
  · rw [if_neg hcS]
    exact good_inter (good_closer a c) (good_near (a := a) (b := c))

/-- The reduced one-variable condition on a cell: only the distance `δ = w (x - f a)` survives,
with the multiplicities of the roots of `S` as exponents. -/
def clusterCond (f : K →+* N) (w : Valuation N Γ') (p q : Multiset K) (aP aQ a : K)
    (A S : Finset K) : Set N :=
  {x : N | w (f (absorb aP a p (A \ S))) * (w (x - f a)) ^ (∑ c ∈ S, p.count c)
      ≤ w (f (absorb aQ a q (A \ S))) * (w (x - f a)) ^ (∑ c ∈ S, q.count c)}

theorem clusterCond_good (p q : Multiset K) (aP aQ a : K) (A S : Finset K) :
    Good f w (clusterCond f w p q aP aQ a A S) :=
  good_pow_le_pow (f := f) (w := w) a (absorb aP a p (A \ S)) (absorb aQ a q (A \ S))
    (∑ c ∈ S, p.count c) (∑ c ∈ S, q.count c)

/-- **On a cell the compound condition reduces to the one-variable condition.** -/
theorem prodLe_iff_clusterCond {p q : Multiset K} {A : Finset K} (hp : p.toFinset ⊆ A)
    (hq : q.toFinset ⊆ A) {aP aQ a : K} {S : Finset K} (hSA : S ⊆ A) {x : N}
    (hx : x ∈ cluster f w A a S) :
    x ∈ prodLe (f := f) (w := w) p q aP aQ ↔ x ∈ clusterCond f w p q aP aQ a A S := by
  obtain ⟨hcl, hS⟩ := hx
  rw [prodLe, Set.mem_setOf_eq, prod_map_split hp hSA hcl hS,
    prod_map_split hq hSA hcl hS, clusterCond, Set.mem_setOf_eq,
    ← absorb_mul_pow aP a p S (A \ S) (w (x - f a)),
    ← absorb_mul_pow aQ a q S (A \ S) (w (x - f a))]

/-- **The compound condition is `Good`**: a finite union of cells, on each of which it reduces to
a one-variable condition. -/
theorem prodLe_good (p q : Multiset K) (aP aQ : K) :
    Good f w (prodLe (f := f) (w := w) p q aP aQ) := by
  classical
  set A : Finset K := p.toFinset ∪ q.toFinset with hA
  have hp : p.toFinset ⊆ A := hA ▸ Finset.subset_union_left
  have hq : q.toFinset ⊆ A := hA ▸ Finset.subset_union_right
  rcases A.eq_empty_or_nonempty with hAe | hAn
  · have hp0 : p = 0 := by
      refine eq_zero_of_toFinset_eq_empty ?_
      rw [hA] at hAe
      exact (Finset.union_eq_empty.mp hAe).1
    have hq0 : q = 0 := by
      refine eq_zero_of_toFinset_eq_empty ?_
      rw [hA] at hAe
      exact (Finset.union_eq_empty.mp hAe).2
    subst hp0
    subst hq0
    simp only [prodLe, Multiset.map_zero, Multiset.prod_zero, mul_one]
    by_cases hle : w (f aP) ≤ w (f aQ)
    · have h : {x : N | w (f aP) ≤ w (f aQ)} = Set.univ := by
        ext x
        simp [hle]
      rw [h]
      exact good_univ f w
    · have h : {x : N | w (f aP) ≤ w (f aQ)} = ∅ := by
        ext x
        simp [hle]
      rw [h]
      exact good_empty f w
  · have hcover : prodLe (f := f) (w := w) p q aP aQ
        = ⋃ a ∈ A, ⋃ S ∈ A.powerset, (cluster f w A a S ∩ clusterCond f w p q aP aQ a A S) := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_inter_iff]
      constructor
      · intro hx
        obtain ⟨a, haA, hmin⟩ := Finset.exists_min_image A (fun c => w (x - f c)) hAn
        refine ⟨a, haA, A.filter (fun c => w (f a - f c) ≤ w (x - f a)),
          Finset.mem_powerset.mpr (Finset.filter_subset _ _), ⟨?_, ?_⟩, ?_⟩
        · exact fun c hc => hmin c hc
        · intro c hc
          rw [Finset.mem_filter]
          exact ⟨fun h => ⟨hc, h⟩, fun h => h.2⟩
        · exact (prodLe_iff_clusterCond hp hq (Finset.filter_subset _ _)
            ⟨fun c hc => hmin c hc, fun c hc => by
              rw [Finset.mem_filter]
              exact ⟨fun h => ⟨hc, h⟩, fun h => h.2⟩⟩).mp hx
      · rintro ⟨a, _, S, hS, hx, hx'⟩
        exact (prodLe_iff_clusterCond hp hq (Finset.mem_powerset.mp hS) hx).mpr hx'
    rw [hcover]
    refine good_iUnion_finset A fun a _ => good_iUnion_finset A.powerset fun S _ => ?_
    exact good_inter (cluster_good A a S) (clusterCond_good p q aP aQ a A S)

/-- **Johnson's Lemma 2.3.1(ii)** for an algebraically closed base field. -/
theorem atomGood_of_isAlgClosed {K : Type} [Field K] [DecidableEq K] [IsAlgClosed K]
    {N : Type} [Field N] {Γ' : Type*} [LinearOrderedCommGroupWithZero Γ']
    {f : K →+* N} {w : Valuation N Γ'} : AtomGood f w := by
  intro P Q
  rcases eq_or_ne P 0 with hP | hP
  · subst hP
    exact atomGood_P_zero Q
  rcases eq_or_ne Q 0 with hQ | hQ
  · subst hQ
    exact atomGood_Q_zero P
  have hset : {x : N | w (P.eval₂ f x) ≤ w (Q.eval₂ f x)}
      = prodLe (f := f) (w := w) P.roots Q.roots P.leadingCoeff Q.leadingCoeff := by
    ext x
    simp only [prodLe, Set.mem_setOf_eq, val_eval₂_eq_prod_roots]
  rw [hset]
  exact prodLe_good (f := f) (w := w) P.roots Q.roots P.leadingCoeff Q.leadingCoeff

end MasterClaim


#print axioms ValOneEC.good_pow_le_pow_same
#print axioms ValOneEC.good_pow_le_pow_lt
#print axioms ValOneEC.good_pow_le_pow_gt
#print axioms ValOneEC.exists_val_pow_div
#print axioms ValOneEC.atomGood_of_isAlgClosed
#print axioms ValOneEC.prodLe_good

namespace Johnson

open Polynomial

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- From a strict inequality of squares in a linearly ordered commutative monoid with zero. -/
theorem lt_of_mul_self_lt_mul_self {x y : Γ₀} (h : x * x < y * y) : x < y := by
  by_contra hle
  push Not at hle
  exact absurd h (not_lt.mpr (mul_le_mul' hle hle))

/-- **Divisibility of the value group.**  In an algebraically closed field every element has an
`n`-th root, so every value has an `n`-th root as well. -/
theorem exists_pow_val_eq [IsAlgClosed K] (v : Valuation K Γ₀) (a : K) {n : ℕ} (hn : 0 < n) :
    ∃ b : K, v b ^ n = v a := by
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq a hn
  exact ⟨b, by rw [← map_pow, hb]⟩

/-- **Density.**  Between two nonzero values there is a third one. -/
theorem exists_val_between [IsAlgClosed K] (v : Valuation K Γ₀) {a c : K} (ha : a ≠ 0)
    (hc : c ≠ 0) (h : v a < v c) : ∃ b : K, b ≠ 0 ∧ v a < v b ∧ v b < v c := by
  obtain ⟨b, hb⟩ := exists_pow_val_eq v (a * c) (n := 2) (by norm_num)
  have hb' : v b * v b = v a * v c := by rw [← pow_two, hb, map_mul]
  have ha0 : 0 < v a := pos_iff_ne_zero.mpr (v.ne_zero_iff.mpr ha)
  have hc0 : 0 < v c := pos_iff_ne_zero.mpr (v.ne_zero_iff.mpr hc)
  have hb0 : v b ≠ 0 := by
    intro h0
    have hne : v a * v c ≠ 0 :=
      mul_ne_zero (v.ne_zero_iff.mpr ha) (v.ne_zero_iff.mpr hc)
    apply hne
    rw [← hb', h0]
    simp
  refine ⟨b, v.ne_zero_iff.mp hb0, ?_, ?_⟩
  · exact lt_of_mul_self_lt_mul_self (by rw [hb']; exact mul_lt_mul_of_pos_left h ha0)
  · exact lt_of_mul_self_lt_mul_self (by rw [hb']; exact mul_lt_mul_of_pos_right h hc0)

/-- The value group has no greatest element. -/
theorem exists_val_lt_val (v : Valuation K Γ₀) (hnt : ∃ x : K, x ≠ 0 ∧ v x < 1) {a : K}
    (ha : a ≠ 0) : ∃ b : K, b ≠ 0 ∧ v a < v b := by
  obtain ⟨x, hx0, hx⟩ := hnt
  have hxpos : 0 < v x := pos_iff_ne_zero.mpr (v.ne_zero_iff.mpr hx0)
  have hinv : 0 < (v x)⁻¹ := pos_iff_ne_zero.mpr (inv_ne_zero (ne_of_gt hxpos))
  have hxv : 1 < (v x)⁻¹ := by
    have h : (v x)⁻¹ * v x < (v x)⁻¹ * 1 := mul_lt_mul_of_pos_left hx hinv
    rw [inv_mul_cancel₀ (ne_of_gt hxpos), mul_one] at h
    exact h
  have ha0 : 0 < v a := pos_iff_ne_zero.mpr (v.ne_zero_iff.mpr ha)
  refine ⟨a * x⁻¹, mul_ne_zero ha (inv_ne_zero hx0), ?_⟩
  rw [map_mul, Valuation.map_inv]
  simpa using mul_lt_mul_of_pos_left hxv ha0

/-- The value group has no least element. -/
theorem exists_val_lt_val' (v : Valuation K Γ₀) (hnt : ∃ x : K, x ≠ 0 ∧ v x < 1) {a : K}
    (ha : a ≠ 0) : ∃ b : K, b ≠ 0 ∧ v b < v a := by
  obtain ⟨x, hx0, hx⟩ := hnt
  have ha0 : 0 < v a := pos_iff_ne_zero.mpr (v.ne_zero_iff.mpr ha)
  refine ⟨a * x, mul_ne_zero ha hx0, ?_⟩
  rw [map_mul]
  simpa using mul_lt_mul_of_pos_left hx ha0

/-- **Johnson, Lemma 2.3.6 (first half).**  The value group of a nontrivially valued
algebraically closed field is a dense linear order without endpoints. -/
theorem valueGroup_dlo [IsAlgClosed K] (v : Valuation K Γ₀)
    (hnt : ∃ x : K, x ≠ 0 ∧ v x < 1) :
    (∀ a : K, a ≠ 0 → ∃ b : K, b ≠ 0 ∧ v a < v b) ∧
    (∀ a : K, a ≠ 0 → ∃ b : K, b ≠ 0 ∧ v b < v a) ∧
    (∀ a c : K, a ≠ 0 → c ≠ 0 → v a < v c → ∃ b : K, b ≠ 0 ∧ v a < v b ∧ v b < v c) :=
  ⟨fun _ ha => exists_val_lt_val v hnt ha,
   fun _ ha => exists_val_lt_val' v hnt ha,
   fun _ _ ha hc h => exists_val_between v ha hc h⟩





/-!
# The residue field of an algebraically closed valued field

Johnson, *Fun with Fields*, Lemma 2.3.6 (second half), in the strengthened form: the residue
field of an algebraically closed valued field is itself algebraically closed, hence infinite.

The proof is the root-product argument: lift a monic `q` over the residue field `𝓀 = O/m` to a
monic `f` over `O`; over the algebraically closed `K = Frac O`, `f` splits as `∏ (X - aᵢ)`, and
`v (f.coeff 0) = ∏ v aᵢ ≤ 1` forces some `v aᵢ ≤ 1`, i.e. some root lies in `O`, and it reduces
to a root of `q`.
-/



variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-! ## Two elementary lemmas -/

/-- A nonempty product of elements `> 1` in a linearly ordered commutative monoid with zero
is `> 1`. -/
theorem one_lt_multiset_prod {α : Type*} [LinearOrderedCommMonoidWithZero α] (m : Multiset α)
    (h : ∀ a ∈ m, 1 < a) (hm : m ≠ 0) : 1 < m.prod := by
  revert h hm
  refine Multiset.induction_on m ?_ ?_
  · intro _ hm; exact absurd rfl hm
  · intro a s ih h hs
    rw [Multiset.prod_cons]
    have ha : 1 < a := h a (Multiset.mem_cons_self a s)
    rcases eq_or_ne s 0 with rfl | hne
    · simpa using ha
    · have hs' : 1 < s.prod := ih (fun b hb => h b (Multiset.mem_cons_of_mem hb)) hne
      exact one_lt_mul_of_lt_of_le ha hs'.le

/-- A polynomial is monic as soon as its degree is at most `n` and its `n`-th coefficient
is `1`. -/
theorem monic_of_natDegree_le_of_coeff_eq_one {R : Type*} [Semiring R] [Nontrivial R] {p : R[X]}
    {n : ℕ}
    (h : p.natDegree ≤ n) (h1 : p.coeff n = 1) : p.Monic := by
  have hn : p.natDegree = n := by
    rcases lt_or_eq_of_le h with hlt | heq
    · exfalso
      rw [coeff_eq_zero_of_natDegree_lt hlt] at h1
      exact zero_ne_one h1
    · exact heq
  rw [Monic, leadingCoeff, hn]
  exact h1

/-! ## Lifting a monic polynomial along a surjective ring homomorphism -/

/-- Every monic polynomial over a quotient lifts to a monic polynomial. -/
theorem exists_monic_map_eq {R S : Type*} [CommRing R] [Nontrivial R] [CommRing S] (φ : R →+* S)
    (hφ : Function.Surjective φ) {q : S[X]} (hq : q.Monic) :
    ∃ f : R[X], f.Monic ∧ f.map φ = q := by
  classical
  choose s hs using hφ
  set s' : S → R := fun c => if c = 1 then 1 else s c with hs'
  have hs'1 : s' 1 = 1 := by simp [hs']
  have hs'spec : ∀ c, φ (s' c) = c := by
    intro c
    by_cases hc : c = 1
    · rw [hc, hs'1, map_one]
    · simp only [hs', if_neg hc]; exact hs c
  refine ⟨X ^ q.natDegree + ∑ i ∈ Finset.range q.natDegree, C (s' (q.coeff i)) * X ^ i,
    ?_, ?_⟩
  · refine monic_of_natDegree_le_of_coeff_eq_one (n := q.natDegree) ?_ ?_
    · refine le_trans (natDegree_add_le _ _) (max_le (le_of_eq (natDegree_X_pow _)) ?_)
      refine natDegree_sum_le_of_forall_le (s := Finset.range q.natDegree)
        (f := fun i => C (s' (q.coeff i)) * X ^ i) (n := q.natDegree) (fun i hi => ?_)
      rw [Finset.mem_range] at hi
      exact le_trans (natDegree_C_mul_X_pow_le _ _) (le_of_lt hi)
    · rw [coeff_add, coeff_X_pow_self, finsetSum_coeff]
      have hzero : ∀ i ∈ Finset.range q.natDegree,
          (C (s' (q.coeff i)) * X ^ i).coeff q.natDegree = 0 := by
        intro i hi
        rw [Finset.mem_range] at hi
        rw [coeff_C_mul, coeff_X_pow, if_neg (Ne.symm (ne_of_lt hi)), mul_zero]
      rw [Finset.sum_eq_zero hzero, add_zero]
  · rw [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sum]
    simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X, hs'spec]
    conv_rhs => rw [hq.as_sum]

/-! ## The root-product argument -/

/-- A monic polynomial of positive degree over a valuation ring of an algebraically closed
field has a root modulo the maximal ideal. -/
theorem exists_residue_root [IsAlgClosed K] (v : Valuation K Γ₀)
    {f : (↥v.valuationSubring)[X]} (hf : f.Monic) (hd : 1 ≤ f.natDegree) :
    ∃ x : IsLocalRing.ResidueField ↥v.valuationSubring,
      (f.map (IsLocalRing.residue ↥v.valuationSubring)).eval x = 0 := by
  classical
  set F : K[X] := f.map v.valuationSubring.subtype with hF
  have hFmonic : F.Monic := hf.map _
  have hFn : F.natDegree = f.natDegree := by rw [hF, Monic.natDegree_map hf]
  have hcard : F.roots.card = F.natDegree := ((IsAlgClosed.splits F).natDegree_eq_card_roots).symm
  have hroots_ne : F.roots ≠ 0 := by
    intro h0
    have hc : F.roots.card = 0 := by rw [h0]; simp
    rw [hcard, hFn] at hc
    omega
  -- `v` turns a product into a product of values
  have hkey : ∀ m : Multiset K, v m.prod = (m.map v).prod := by
    intro m
    induction m using Multiset.induction_on with
    | empty => simp
    | cons a s ih => simp [Multiset.prod_cons, map_mul, ih]
  -- the value of a root product
  have hval : (F.roots.map v).prod ≤ 1 := by
    have h1 : (F.roots.map v).prod = v (F.eval 0) := by
      rw [(IsAlgClosed.splits F).eval_eq_prod_roots_of_monic hFmonic, hkey]
      congr 1
      rw [Multiset.map_map]
      congr 1
      funext r
      simp
    rw [h1, ← coeff_zero_eq_eval_zero]
    have hc0 : F.coeff 0 = v.valuationSubring.subtype (f.coeff 0) := by
      rw [hF, coeff_map]
    rw [hc0]
    exact (Valuation.mem_valuationSubring_iff v _).mp (f.coeff 0).2
  -- some root has value `≤ 1`
  obtain ⟨r, hr, hrv⟩ : ∃ r ∈ F.roots, v r ≤ 1 := by
    by_contra h
    push Not at h
    have hm : ∀ a ∈ F.roots.map v, 1 < a := by
      intro a ha
      obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.mp ha
      exact h b hb
    have hne : F.roots.map v ≠ 0 := by
      intro h0
      have hc : (F.roots.map v).card = 0 := by rw [h0]; simp
      rw [Multiset.card_map, hcard, hFn] at hc
      omega
    exact absurd (one_lt_multiset_prod _ hm hne) (not_lt.mpr hval)
  -- reduce the root
  set y : ↥v.valuationSubring := ⟨r, (Valuation.mem_valuationSubring_iff v r).mpr hrv⟩ with hy
  have hgen : ∀ (g : (↥v.valuationSubring)[X]) (z : ↥v.valuationSubring),
      (g.map v.valuationSubring.subtype).eval (v.valuationSubring.subtype z)
        = v.valuationSubring.subtype (g.eval z) := by
    intro g z
    rw [← eval₂_eq_eval_map]
    exact Polynomial.eval₂_hom v.valuationSubring.subtype z
  have hfev : f.eval y = 0 := by
    have h1 : v.valuationSubring.subtype (f.eval y) = 0 := by
      rw [← hgen f y, hy]
      exact isRoot_of_mem_roots (p := F) hr
    exact v.valuationSubring.subtype_injective (by rw [h1, map_zero])
  refine ⟨IsLocalRing.residue ↥v.valuationSubring y, ?_⟩
  have h2 : (f.map (IsLocalRing.residue ↥v.valuationSubring)).eval
      (IsLocalRing.residue ↥v.valuationSubring y)
        = IsLocalRing.residue ↥v.valuationSubring (f.eval y) := by
    rw [← eval₂_eq_eval_map]
    exact Polynomial.eval₂_hom (IsLocalRing.residue ↥v.valuationSubring) y
  rw [h2, hfev, map_zero]

/-! ## The residue field is algebraically closed -/

/-- **Johnson, Lemma 2.3.6 (second half).**  The residue field of an algebraically closed
valued field is algebraically closed. -/
theorem isAlgClosed_residueField [IsAlgClosed K] (v : Valuation K Γ₀) :
    IsAlgClosed (IsLocalRing.ResidueField ↥v.valuationSubring) := by
  refine IsAlgClosed.of_exists_root
    (k := IsLocalRing.ResidueField ↥v.valuationSubring) (fun p hp hpi => ?_)
  haveI : Nontrivial ↥v.valuationSubring :=
    ⟨0, 1, fun h => zero_ne_one (congrArg Subtype.val h)⟩
  have hne0 : p ≠ 0 := hp.ne_zero
  have hd : 1 ≤ p.natDegree := by
    rcases Nat.eq_zero_or_pos p.natDegree with h | h
    · exfalso
      have hC : p = C (p.coeff 0) := eq_C_of_natDegree_eq_zero h
      have hc0 : p.coeff 0 ≠ 0 := by
        rw [hC] at hne0
        simpa using hne0
      rw [hC] at hpi
      exact hpi.not_isUnit (isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc0))
    · exact h
  obtain ⟨f, hfmonic, hfmap⟩ :=
    exists_monic_map_eq (IsLocalRing.residue ↥v.valuationSubring)
      Ideal.Quotient.mk_surjective hp
  have hfdeg : 1 ≤ f.natDegree := by
    rw [← Monic.natDegree_map hfmonic (IsLocalRing.residue ↥v.valuationSubring), hfmap]
    exact hd
  obtain ⟨x, hx⟩ := exists_residue_root v hfmonic hfdeg
  exact ⟨x, by rw [← hfmap]; exact hx⟩

/-- **Johnson, Lemma 2.3.6 (second half), conclusion.**  The residue field of an algebraically
closed valued field is infinite. -/
theorem infinite_residueField [IsAlgClosed K] (v : Valuation K Γ₀) :
    Infinite (IsLocalRing.ResidueField ↥v.valuationSubring) := by
  haveI := isAlgClosed_residueField v
  exact inferInstance





/-!
# Balls in a valued field, and Johnson's Lemma 2.3.5

Johnson, *Fun with Fields*, §2.3.  A ball is `{x : v (x - c) ≤ γ}` (closed), `{x : v (x - c) < γ}`
(open), a singleton, or the whole field.  We prove that intersecting closed balls (resp. open
balls) are comparable, and Lemma 2.3.5: every proper subball of the valuation ring `O` is
contained in a residue class, i.e. in `{x : v (x - c) < 1}` for some `c`.

The multiplicative convention is used throughout: `v 0 = 0` is the bottom of `Γ₀`, so `v x ≤ γ`
is the additive `v x ≥ γ` and closed balls are the `≤` ones.
-/


variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- The closed ball of radius `γ` about `c`. -/
def closedBall (v : Valuation K Γ₀) (c : K) (γ : Γ₀) : Set K := {x | v (x - c) ≤ γ}

/-- The open ball of radius `γ` about `c`. -/
def openBall (v : Valuation K Γ₀) (c : K) (γ : Γ₀) : Set K := {x | v (x - c) < γ}

@[simp]
theorem mem_closedBall {v : Valuation K Γ₀} {c x : K} {γ : Γ₀} :
    x ∈ closedBall v c γ ↔ v (x - c) ≤ γ := Iff.rfl

@[simp]
theorem mem_openBall {v : Valuation K Γ₀} {c x : K} {γ : Γ₀} :
    x ∈ openBall v c γ ↔ v (x - c) < γ := Iff.rfl

theorem closedBall_self_mem (v : Valuation K Γ₀) (c : K) (γ : Γ₀) : c ∈ closedBall v c γ := by
  simp

theorem openBall_self_mem {v : Valuation K Γ₀} {c : K} {γ : Γ₀} (h : γ ≠ 0) :
    c ∈ openBall v c γ := by
  have hpos : (0 : Γ₀) < γ := pos_iff_ne_zero.mpr h
  simpa using hpos

/-- The value of a difference is bounded by the maximum of two others. -/
theorem val_sub_le_max (v : Valuation K Γ₀) (a b c : K) :
    v (a - c) ≤ max (v (a - b)) (v (b - c)) := by
  have h : a - c = (a - b) + (b - c) := by ring
  rw [h]
  exact map_add_le_max _ _ _

/-- The value of `x - c` is at most the maximum of `v x` and `v c`. -/
theorem val_sub_le_max_of (v : Valuation K Γ₀) (x c : K) :
    v (x - c) ≤ max (v x) (v c) := by
  have h : x - c = x + -c := by ring
  rw [h]
  refine le_trans (map_add_le_max (f := v) x (-c)) ?_
  rw [Valuation.map_neg]

/-- A closed ball grows when the radius grows. -/
theorem closedBall_mono (v : Valuation K Γ₀) {c₁ c₂ : K} {γ₁ γ₂ : Γ₀}
    (h : v (c₁ - c₂) ≤ γ₂) (hγ : γ₁ ≤ γ₂) :
    closedBall v c₁ γ₁ ⊆ closedBall v c₂ γ₂ := by
  intro x hx
  rw [mem_closedBall] at hx ⊢
  exact le_trans (val_sub_le_max v x c₁ c₂) (max_le (le_trans hx hγ) h)

/-- An open ball grows when the radius grows. -/
theorem openBall_mono (v : Valuation K Γ₀) {c₁ c₂ : K} {γ₁ γ₂ : Γ₀}
    (h : v (c₁ - c₂) < γ₂) (hγ : γ₁ ≤ γ₂) :
    openBall v c₁ γ₁ ⊆ openBall v c₂ γ₂ := by
  intro x hx
  rw [mem_openBall] at hx ⊢
  refine lt_of_le_of_lt (val_sub_le_max v x c₁ c₂) (max_lt ?_ h)
  exact lt_of_lt_of_le hx hγ

/-- **Intersecting closed balls are comparable.**  (Johnson's (2.3).) -/
theorem closedBall_subset_or_subset (v : Valuation K Γ₀) {c₁ c₂ : K} {γ₁ γ₂ : Γ₀}
    (h : (closedBall v c₁ γ₁ ∩ closedBall v c₂ γ₂).Nonempty) :
    closedBall v c₁ γ₁ ⊆ closedBall v c₂ γ₂ ∨ closedBall v c₂ γ₂ ⊆ closedBall v c₁ γ₁ := by
  obtain ⟨z, hz₁, hz₂⟩ := h
  rw [mem_closedBall] at hz₁ hz₂
  have hz₁' : v (c₁ - z) ≤ γ₁ := by
    rw [show c₁ - z = -(z - c₁) by ring, Valuation.map_neg]; exact hz₁
  have hz₂' : v (c₂ - z) ≤ γ₂ := by
    rw [show c₂ - z = -(z - c₂) by ring, Valuation.map_neg]; exact hz₂
  have h12 : v (c₁ - c₂) ≤ max γ₁ γ₂ :=
    le_trans (val_sub_le_max v c₁ z c₂) (max_le_max hz₁' hz₂)
  have h21 : v (c₂ - c₁) ≤ max γ₂ γ₁ :=
    le_trans (val_sub_le_max v c₂ z c₁) (max_le_max hz₂' hz₁)
  rcases le_total γ₁ γ₂ with hγ | hγ
  · left
    refine closedBall_mono v ?_ hγ
    rwa [max_eq_right hγ] at h12
  · right
    refine closedBall_mono v ?_ hγ
    rwa [max_eq_right hγ] at h21

/-- **Intersecting open balls are comparable.** -/
theorem openBall_subset_or_subset (v : Valuation K Γ₀) {c₁ c₂ : K} {γ₁ γ₂ : Γ₀}
    (h : (openBall v c₁ γ₁ ∩ openBall v c₂ γ₂).Nonempty) :
    openBall v c₁ γ₁ ⊆ openBall v c₂ γ₂ ∨ openBall v c₂ γ₂ ⊆ openBall v c₁ γ₁ := by
  obtain ⟨z, hz₁, hz₂⟩ := h
  rw [mem_openBall] at hz₁ hz₂
  have hz₁' : v (c₁ - z) < γ₁ := by
    rw [show c₁ - z = -(z - c₁) by ring, Valuation.map_neg]; exact hz₁
  have hz₂' : v (c₂ - z) < γ₂ := by
    rw [show c₂ - z = -(z - c₂) by ring, Valuation.map_neg]; exact hz₂
  have h12 : v (c₁ - c₂) < max γ₁ γ₂ :=
    lt_of_le_of_lt (val_sub_le_max v c₁ z c₂) (max_lt_max hz₁' hz₂)
  have h21 : v (c₂ - c₁) < max γ₂ γ₁ :=
    lt_of_le_of_lt (val_sub_le_max v c₂ z c₁) (max_lt_max hz₂' hz₁)
  rcases le_total γ₁ γ₂ with hγ | hγ
  · left
    refine openBall_mono v ?_ hγ
    rwa [max_eq_right hγ] at h12
  · right
    refine openBall_mono v ?_ hγ
    rwa [max_eq_right hγ] at h21

/-! ## Lemma 2.3.5: proper subballs of the valuation ring lie in a residue class -/

/-- The balls of a valued field: closed balls, open balls, singletons, and the whole field. -/
inductive IsBall (v : Valuation K Γ₀) : Set K → Prop
  | closed (c : K) (γ : Γ₀) : IsBall v (closedBall v c γ)
  | openball (c : K) (γ : Γ₀) : IsBall v (openBall v c γ)
  | singleton (c : K) : IsBall v {c}
  | univ : IsBall v Set.univ

/-- **Johnson, Lemma 2.3.5.**  Every proper subball of the valuation ring `O` is contained in a
residue class `{x : v (x - c) < 1}`.  (Nontriviality of the valuation is needed exactly to
exclude the ball `K`.) -/
theorem subset_residueClass_of_isBall (v : Valuation K Γ₀) (hnt : ∃ x : K, 1 < v x)
    {B : Set K} (hB : IsBall v B) (hsub : B ⊆ (v.valuationSubring : Set K))
    (hne : B ≠ (v.valuationSubring : Set K)) :
    ∃ c : ↥v.valuationSubring, B ⊆ openBall v (c : K) 1 := by
  cases hB with
  | univ =>
    obtain ⟨x, hx⟩ := hnt
    have hxO : v x ≤ 1 := (Valuation.mem_valuationSubring_iff v x).mp (hsub trivial)
    exact absurd hxO (not_le.mpr hx)
  | singleton c =>
    refine ⟨⟨c, hsub (Set.mem_singleton c)⟩, ?_⟩
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    simpa using zero_lt_one (α := Γ₀)
  | closed c γ =>
    -- the centre of a ball lies in the ball, hence in `O`
    have hcO : c ∈ v.valuationSubring := hsub (closedBall_self_mem v c γ)
    have hc : v c ≤ 1 := (Valuation.mem_valuationSubring_iff v c).mp hcO
    by_cases hγ : γ < 1
    · refine ⟨⟨c, hcO⟩, ?_⟩
      intro x hx
      rw [mem_closedBall] at hx
      rw [mem_openBall]
      exact lt_of_le_of_lt hx hγ
    · -- otherwise the ball swallows `O`, contradicting properness
      exfalso
      apply hne
      refine Set.Subset.antisymm hsub ?_
      intro x hx
      have hx1 : v x ≤ 1 := (Valuation.mem_valuationSubring_iff v x).mp hx
      rw [mem_closedBall]
      refine le_trans (val_sub_le_max_of v x c) (max_le ?_ ?_)
      · exact le_trans hx1 (not_lt.mp hγ)
      · exact le_trans hc (not_lt.mp hγ)
  | openball c γ =>
    by_cases hγ0 : γ = 0
    · subst hγ0
      refine ⟨⟨0, v.valuationSubring.zero_mem⟩, ?_⟩
      intro x hx
      rw [mem_openBall] at hx
      exact absurd hx (not_lt.mpr zero_le)
    have hcO : c ∈ v.valuationSubring := hsub (openBall_self_mem hγ0)
    have hc : v c ≤ 1 := (Valuation.mem_valuationSubring_iff v c).mp hcO
    by_cases hγ : γ ≤ 1
    · refine ⟨⟨c, hcO⟩, ?_⟩
      intro x hx
      rw [mem_openBall] at hx ⊢
      exact lt_of_lt_of_le hx hγ
    · exfalso
      apply hne
      refine Set.Subset.antisymm hsub ?_
      intro x hx
      have hx1 : v x ≤ 1 := (Valuation.mem_valuationSubring_iff v x).mp hx
      rw [mem_openBall]
      refine lt_of_le_of_lt (val_sub_le_max_of v x c) (max_lt ?_ ?_)
      · exact lt_of_le_of_lt hx1 (not_le.mp hγ)
      · exact lt_of_le_of_lt hc (not_le.mp hγ)






/-! ## The valuation ring is not a finite union of proper subballs (Johnson 2.3.7, `B = O`) -/

/-- **Johnson, Lemma 2.3.7, the case `B = O`.**  The valuation ring of an algebraically closed,
nontrivially valued field is not a finite union of proper subballs.  The inputs are Lemma 2.3.5
(proper subballs lie in residue classes) and the infinitude of the residue field, Lemma 2.3.6. -/
theorem valuationSubring_not_finite_union_isBall [IsAlgClosed K] (v : Valuation K Γ₀)
    (hnt : ∃ x : K, 1 < v x) {ι : Type*} (s : Finset ι) (B : ι → Set K)
    (hball : ∀ i ∈ s, IsBall v (B i))
    (hsub : ∀ i ∈ s, B i ⊆ (v.valuationSubring : Set K))
    (hne : ∀ i ∈ s, B i ≠ (v.valuationSubring : Set K)) :
    (v.valuationSubring : Set K) ≠ ⋃ i ∈ s, B i := by
  intro hcover
  classical
  have hex : ∀ i ∈ s, ∃ c : ↥v.valuationSubring, B i ⊆ openBall v (c : K) 1 :=
    fun i hi => subset_residueClass_of_isBall v hnt (hball i hi) (hsub i hi) (hne i hi)
  choose c hc using hex
  -- every element of `O` reduces to one of finitely many residues
  have key : ∀ x : ↥v.valuationSubring, ∃ (i : ι) (hi : i ∈ s),
      IsLocalRing.residue ↥v.valuationSubring x = IsLocalRing.residue _ (c i hi) := by
    intro x
    have hx : (x : K) ∈ ⋃ i ∈ s, B i := by rw [← hcover]; exact x.2
    simp only [Set.mem_iUnion] at hx
    obtain ⟨i, hi, hxB⟩ := hx
    refine ⟨i, hi, ?_⟩
    have h1 : v ((x : K) - ((c i hi : ↥v.valuationSubring) : K)) < 1 := hc i hi hxB
    have hmem : x - c i hi ∈ IsLocalRing.maximalIdeal ↥v.valuationSubring := by
      rw [Valuation.mem_maximalIdeal_iff (v := v)]
      simpa using h1
    have h2 : IsLocalRing.residue ↥v.valuationSubring (x - c i hi) = 0 :=
      (IsLocalRing.residue_eq_zero_iff (x - c i hi)).mpr hmem
    rw [map_sub, sub_eq_zero] at h2
    exact h2
  have hsurj : Function.Surjective
      (fun i : ↥s => IsLocalRing.residue ↥v.valuationSubring (c i.1 i.2)) := by
    intro y
    obtain ⟨x, rfl⟩ :=
      Ideal.Quotient.mk_surjective (I := IsLocalRing.maximalIdeal ↥v.valuationSubring) y
    obtain ⟨i, hi, hres⟩ := key x
    exact ⟨⟨i, hi⟩, hres.symm⟩
  haveI : Fintype ↥s := inferInstance
  have hfin : Finite (IsLocalRing.ResidueField ↥v.valuationSubring) :=
    Finite.of_surjective _ hsurj
  exact (not_finite_iff_infinite.mpr (infinite_residueField v)) hfin

/-! ## The `B = m` and `B = K` cases of Johnson 2.3.7 -/

/-- A finite union of closed balls about `0` is a single one, of the largest radius. -/
theorem exists_closedBall_zero_union (v : Valuation K Γ₀) {ι : Type*} {s : Finset ι}
    {γ : ι → Γ₀} (hne : s.Nonempty) :
    ∃ γm : Γ₀, (∃ i ∈ s, γm = γ i) ∧ (∀ i ∈ s, γ i ≤ γm) ∧
      (⋃ i ∈ s, closedBall v 0 (γ i)) = closedBall v 0 γm := by
  classical
  obtain ⟨i₀, hi₀, hmax⟩ := Finset.exists_mem_eq_sup s hne γ
  refine ⟨γ i₀, ⟨i₀, hi₀, rfl⟩, fun i hi => ?_, ?_⟩
  · rw [← hmax]; exact Finset.le_sup (f := γ) hi
  · ext x
    simp only [Set.mem_iUnion, mem_closedBall, sub_zero]
    constructor
    · rintro ⟨i, hi, hx⟩
      rw [← hmax]
      exact le_trans hx (Finset.le_sup (f := γ) hi)
    · intro hx
      exact ⟨i₀, hi₀, hx⟩

/-- **Johnson 2.3.7, the case `B = K`** (after the normalisation of Lemma 2.3.4): the whole
field is not a finite union of closed balls about `0` with radii in `vK`. -/
theorem univ_ne_finite_union_closedBall (v : Valuation K Γ₀)
    (hnt : ∃ x : K, x ≠ 0 ∧ v x < 1) {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (γ : ι → Γ₀)
    (hγ : ∀ i ∈ s, ∃ a : K, v a = γ i) :
    (Set.univ : Set K) ≠ ⋃ i ∈ s, closedBall v 0 (γ i) := by
  obtain ⟨γm, ⟨i₀, hi₀, rfl⟩, -, hunion⟩ := exists_closedBall_zero_union v hs (γ := γ)
  obtain ⟨a, ha⟩ := hγ i₀ hi₀
  -- an element of value strictly above `γ i₀`
  have hgt : ∃ b : K, γ i₀ < v b := by
    rcases eq_or_ne (γ i₀) 0 with h0 | h0
    · refine ⟨1, ?_⟩
      rw [h0, map_one]
      exact zero_lt_one
    · obtain ⟨b, -, hb⟩ := exists_val_lt_val v hnt (v.ne_zero_iff.mp (by rw [ha]; exact h0))
      exact ⟨b, by rwa [← ha]⟩
  obtain ⟨b, hb⟩ := hgt
  intro hcover
  have hmem : b ∈ ⋃ i ∈ s, closedBall v 0 (γ i) := by rw [← hcover]; trivial
  rw [hunion] at hmem
  rw [mem_closedBall] at hmem
  simp only [sub_zero] at hmem
  exact absurd hmem (not_le.mpr hb)

/-- **Johnson 2.3.7, the case `B = m`** (after the normalisation of Lemma 2.3.4): the maximal
ideal is not a finite union of closed balls about `0` of radius `< 1` with radii in `vK`.
This is where density of the value group is used. -/
theorem openBall_zero_ne_finite_union_closedBall [IsAlgClosed K] (v : Valuation K Γ₀)
    (hnt : ∃ x : K, x ≠ 0 ∧ v x < 1) {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (γ : ι → Γ₀) (hγ : ∀ i ∈ s, ∃ a : K, v a = γ i) (hlt : ∀ i ∈ s, γ i < 1) :
    openBall v 0 1 ≠ ⋃ i ∈ s, closedBall v 0 (γ i) := by
  obtain ⟨γm, ⟨i₀, hi₀, rfl⟩, -, hunion⟩ := exists_closedBall_zero_union v hs (γ := γ)
  obtain ⟨a, ha⟩ := hγ i₀ hi₀
  have hγlt : γ i₀ < 1 := hlt i₀ hi₀
  -- an element of the open ball of radius `1` lying strictly outside the closed ball
  have hgt : ∃ b : K, γ i₀ < v b ∧ v b < 1 := by
    rcases eq_or_ne (γ i₀) 0 with h0 | h0
    · obtain ⟨x, hx0, hx⟩ := hnt
      exact ⟨x, by rw [h0]; exact pos_iff_ne_zero.mpr (v.ne_zero_iff.mpr hx0), hx⟩
    · have ha0 : a ≠ 0 := v.ne_zero_iff.mp (by rw [ha]; exact h0)
      obtain ⟨b, -, h1, h2⟩ :=
        exists_val_between v ha0 (one_ne_zero) (by rw [ha, map_one]; exact hγlt)
      exact ⟨b, by rwa [ha] at h1, by rwa [map_one] at h2⟩
  obtain ⟨b, hb1, hb2⟩ := hgt
  intro hcover
  have hmem : b ∈ ⋃ i ∈ s, closedBall v 0 (γ i) := by
    rw [← hcover]
    simpa using hb2
  rw [hunion] at hmem
  rw [mem_closedBall] at hmem
  simp only [sub_zero] at hmem
  exact absurd hmem (not_le.mpr hb1)

/-- **Johnson, Lemma 2.3.6.**  For an algebraically closed field with a nontrivial valuation, the
value group is a dense linear order without endpoints and the residue field is infinite. -/
theorem lemma_2_3_6 [IsAlgClosed K] (v : Valuation K Γ₀)
    (hnt : ∃ x : K, x ≠ 0 ∧ v x < 1) :
    (∀ a : K, a ≠ 0 → ∃ b : K, b ≠ 0 ∧ v a < v b) ∧
    (∀ a : K, a ≠ 0 → ∃ b : K, b ≠ 0 ∧ v b < v a) ∧
    (∀ a c : K, a ≠ 0 → c ≠ 0 → v a < v c → ∃ b : K, b ≠ 0 ∧ v a < v b ∧ v b < v c) ∧
    Infinite (IsLocalRing.ResidueField ↥v.valuationSubring) :=
  ⟨(valueGroup_dlo v hnt).1, (valueGroup_dlo v hnt).2.1, (valueGroup_dlo v hnt).2.2,
   infinite_residueField v⟩


/-! ## Affine normalisation of balls

Johnson normalises a ball to one of `{0}`, `m`, `O` or `K` by an affine transformation
`x ↦ c + b x`; the lemmas here are that normalisation for closed and open balls, and the
identification of the closed unit ball with the valuation ring. -/

/-- A closed ball of radius zero is a point. -/
theorem closedBall_zero_eq_singleton (v : Valuation K Γ₀) (c : K) :
    closedBall v c 0 = {c} := by
  ext x
  rw [mem_closedBall, Set.mem_singleton_iff]
  constructor
  · intro h
    have h' : v (x - c) = 0 := le_antisymm h zero_le
    exact sub_eq_zero.mp (v.zero_iff.mp h')
  · rintro rfl
    rw [sub_self, map_zero]

/-- An open ball of radius zero is empty. -/
theorem openBall_zero_eq_empty (v : Valuation K Γ₀) (c : K) :
    openBall v c 0 = ∅ := by
  ext x
  rw [mem_openBall, Set.mem_empty_iff_false, iff_false]
  exact not_lt.mpr zero_le

/-- The closed unit ball about `0` is the valuation ring. -/
theorem closedBall_zero_one_eq_valuationSubring (v : Valuation K Γ₀) :
    closedBall v 0 1 = (v.valuationSubring : Set K) := by
  ext x
  rw [mem_closedBall, sub_zero]
  rfl

/-- An affine map with nonzero linear part sends the closed ball of radius `γ` about `d` to the
closed ball of radius `v b * γ` about `c + b * d`. -/
theorem affine_image_closedBall (v : Valuation K Γ₀) {b : K} (hb : b ≠ 0) (c d : K) (γ : Γ₀) :
    (fun y : K => c + b * y) '' closedBall v d γ = closedBall v (c + b * d) (v b * γ) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [mem_closedBall] at hy ⊢
    have h : c + b * y - (c + b * d) = b * (y - d) := by ring
    rw [h, map_mul]
    exact mul_le_mul_right hy _
  · intro hx
    rw [mem_closedBall] at hx
    refine ⟨d + b⁻¹ * (x - (c + b * d)), ?_, ?_⟩
    · rw [mem_closedBall]
      have h : d + b⁻¹ * (x - (c + b * d)) - d = b⁻¹ * (x - (c + b * d)) := by ring
      rw [h, map_mul, Valuation.map_inv]
      have h2 : (v b)⁻¹ * v (x - (c + b * d)) ≤ (v b)⁻¹ * (v b * γ) := mul_le_mul_right hx _
      rwa [← mul_assoc, inv_mul_cancel₀ (v.ne_zero_iff.mpr hb), one_mul] at h2
    · show c + b * (d + b⁻¹ * (x - (c + b * d))) = x
      have h : b * (b⁻¹ * (x - (c + b * d))) = x - (c + b * d) := by
        rw [← mul_assoc, mul_inv_cancel₀ hb, one_mul]
      rw [mul_add, h]; ring

/-- The same for open balls. -/
theorem affine_image_openBall (v : Valuation K Γ₀) {b : K} (hb : b ≠ 0) (c d : K) (γ : Γ₀) :
    (fun y : K => c + b * y) '' openBall v d γ = openBall v (c + b * d) (v b * γ) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [mem_openBall] at hy ⊢
    have h : c + b * y - (c + b * d) = b * (y - d) := by ring
    rw [h, map_mul]
    exact mul_lt_mul_of_pos_left hy (pos_iff_ne_zero.mpr (v.ne_zero_iff.mpr hb))
  · intro hx
    rw [mem_openBall] at hx
    refine ⟨d + b⁻¹ * (x - (c + b * d)), ?_, ?_⟩
    · rw [mem_openBall]
      have h : d + b⁻¹ * (x - (c + b * d)) - d = b⁻¹ * (x - (c + b * d)) := by ring
      rw [h, map_mul, Valuation.map_inv]
      have h2 : (v b)⁻¹ * v (x - (c + b * d)) < (v b)⁻¹ * (v b * γ) :=
        mul_lt_mul_of_pos_left hx (pos_iff_ne_zero.mpr (inv_ne_zero (v.ne_zero_iff.mpr hb)))
      rwa [← mul_assoc, inv_mul_cancel₀ (v.ne_zero_iff.mpr hb), one_mul] at h2
    · show c + b * (d + b⁻¹ * (x - (c + b * d))) = x
      have h : b * (b⁻¹ * (x - (c + b * d))) = x - (c + b * d) := by
        rw [← mul_assoc, mul_inv_cancel₀ hb, one_mul]
      rw [mul_add, h]; ring

/-- Every closed ball whose radius is a value is an affine image of the valuation ring. -/
theorem closedBall_eq_affine_image (v : Valuation K Γ₀) {b : K} (hb : b ≠ 0) (c : K) :
    closedBall v c (v b) = (fun y : K => c + b * y) '' (v.valuationSubring : Set K) := by
  rw [← closedBall_zero_one_eq_valuationSubring v]
  simpa using (affine_image_closedBall v hb c 0 1).symm

/-- Every open ball whose radius is a nonzero value is an affine image of the open unit ball. -/
theorem openBall_eq_affine_image (v : Valuation K Γ₀) {b : K} (hb : b ≠ 0) (c : K) :
    openBall v c (v b) = (fun y : K => c + b * y) '' openBall v 0 1 := by
  simpa using (affine_image_openBall v hb c 0 1).symm

/-- An affine map with nonzero linear part sends balls to balls. -/
theorem isBall_affine_image (v : Valuation K Γ₀) {b : K} (hb : b ≠ 0) (c : K) {D : Set K}
    (hD : IsBall v D) : IsBall v ((fun y : K => c + b * y) '' D) := by
  cases hD with
  | closed d γ =>
    exact (affine_image_closedBall v hb c d γ).symm ▸ IsBall.closed (c + b * d) (v b * γ)
  | openball d γ =>
    exact (affine_image_openBall v hb c d γ).symm ▸ IsBall.openball (c + b * d) (v b * γ)
  | singleton d =>
    exact (Set.image_singleton (f := fun y : K => c + b * y) (a := d)).symm ▸
      IsBall.singleton (c + b * d)
  | univ =>
    have h : (fun y : K => c + b * y) '' Set.univ = Set.univ := by
      rw [Set.image_univ, Set.range_eq_univ]
      intro x
      exact ⟨b⁻¹ * (x - c), by
        show c + b * (b⁻¹ * (x - c)) = x
        rw [← mul_assoc, mul_inv_cancel₀ hb, one_mul]; ring⟩
    exact h.symm ▸ IsBall.univ

/-! ## Balls with radii in `vK`, and Lemma 2.3.4

Johnson's balls of a valued field have centre and radius in the *value group*: the closed balls
`{x : v (x - c) ≤ v b}` and open balls `{x : v (x - c) < v b}` for `b : K`, the singletons and the
whole field.  (`IsBall` above allows an arbitrary `γ : Γ₀`; the lemmas of 2.3.4 and 2.3.7 are
stated for radii in `vK`, which is the form in which the paper uses them.) -/

/-- The balls of a valued field with radii in the value group: `B = {x : v (x - c) ≤ v b}`,
`B = {x : v (x - c) < v b}`, `B = {c}`, `B = K`. -/
inductive IsValBall (v : Valuation K Γ₀) : Set K → Prop
  | closed (c b : K) : IsValBall v (closedBall v c (v b))
  | openball (c b : K) : IsValBall v (openBall v c (v b))
  | singleton (c : K) : IsValBall v {c}
  | univ : IsValBall v Set.univ

theorem IsValBall.isBall {v : Valuation K Γ₀} {D : Set K} (h : IsValBall v D) : IsBall v D := by
  cases h with
  | closed c b => exact IsBall.closed c (v b)
  | openball c b => exact IsBall.openball c (v b)
  | singleton c => exact IsBall.singleton c
  | univ => exact IsBall.univ

/-- Nontriviality of the valuation, in the two equivalent forms used below. -/
theorem exists_ne_zero_val_lt_one_iff (v : Valuation K Γ₀) :
    (∃ x : K, x ≠ 0 ∧ v x < 1) ↔ (∃ x : K, 1 < v x) := by
  constructor
  · rintro ⟨x, hx0, hx⟩
    refine ⟨x⁻¹, ?_⟩
    rw [Valuation.map_inv]
    exact one_lt_inv_iff₀.mpr ⟨pos_iff_ne_zero.mpr (v.ne_zero_iff.mpr hx0), hx⟩
  · rintro ⟨x, hx⟩
    refine ⟨x⁻¹, inv_ne_zero (v.ne_zero_iff.mp (ne_of_gt (zero_lt_one.trans hx))), ?_⟩
    rw [Valuation.map_inv]
    exact inv_lt_one_of_one_lt₀ hx

/-- Some element whose value dominates both `v a` and `v c`. -/
theorem exists_val_gt_max (v : Valuation K Γ₀) (hnt : ∃ x : K, x ≠ 0 ∧ v x < 1) (a c : K) :
    ∃ b : K, b ≠ 0 ∧ v a < v b ∧ v c < v b := by
  rcases le_total (v a) (v c) with h | h
  · rcases eq_or_ne c 0 with rfl | hc
    · have hz : v a = 0 := le_antisymm (by simpa using h) zero_le
      obtain ⟨x, hx0, hx⟩ := hnt
      refine ⟨x, hx0, ?_, ?_⟩
      · rw [hz]; exact pos_iff_ne_zero.mpr (v.ne_zero_iff.mpr hx0)
      · rw [map_zero]; exact pos_iff_ne_zero.mpr (v.ne_zero_iff.mpr hx0)
    · obtain ⟨b, hb0, hb⟩ := exists_val_lt_val v hnt hc
      exact ⟨b, hb0, lt_of_le_of_lt h hb, hb⟩
  · rcases eq_or_ne a 0 with rfl | ha
    · have hz : v c = 0 := le_antisymm (by simpa using h) zero_le
      obtain ⟨x, hx0, hx⟩ := hnt
      refine ⟨x, hx0, ?_, ?_⟩
      · rw [map_zero]; exact pos_iff_ne_zero.mpr (v.ne_zero_iff.mpr hx0)
      · rw [hz]; exact pos_iff_ne_zero.mpr (v.ne_zero_iff.mpr hx0)
    · obtain ⟨b, hb0, hb⟩ := exists_val_lt_val v hnt ha
      exact ⟨b, hb0, hb, lt_of_le_of_lt h hb⟩

/-- Given two values below `1` there is one value above both and still below `1`. -/
theorem exists_val_between_max_one [IsAlgClosed K] (v : Valuation K Γ₀)
    (hnt : ∃ x : K, x ≠ 0 ∧ v x < 1) {a c : K} (ha : v a < 1) (hc : v c < 1) :
    ∃ b : K, b ≠ 0 ∧ v a ≤ v b ∧ v c ≤ v b ∧ v b < 1 := by
  rcases le_total (v a) (v c) with h | h
  · rcases eq_or_ne (v c) 0 with h0 | h0
    · have hz : v a = 0 := le_antisymm (by rw [h0] at h; exact h) zero_le
      obtain ⟨x, hx0, hx⟩ := hnt
      exact ⟨x, hx0, by rw [hz]; exact zero_le, by rw [h0]; exact zero_le, hx⟩
    · obtain ⟨b, hb0, hb1, hb2⟩ :=
        exists_val_between v (v.ne_zero_iff.mp h0) one_ne_zero (by rwa [map_one])
      exact ⟨b, hb0, le_of_lt (lt_of_le_of_lt h hb1), le_of_lt hb1, by rwa [map_one] at hb2⟩
  · rcases eq_or_ne (v a) 0 with h0 | h0
    · have hz : v c = 0 := le_antisymm (by rw [h0] at h; exact h) zero_le
      obtain ⟨x, hx0, hx⟩ := hnt
      exact ⟨x, hx0, by rw [h0]; exact zero_le, by rw [hz]; exact zero_le, hx⟩
    · obtain ⟨b, hb0, hb1, hb2⟩ :=
        exists_val_between v (v.ne_zero_iff.mp h0) one_ne_zero (by rwa [map_one])
      exact ⟨b, hb0, le_of_lt hb1, le_of_lt (lt_of_le_of_lt h hb1), by rwa [map_one] at hb2⟩

/-- An open ball of radius `1` about a centre inside the maximal ideal is the maximal ideal. -/
theorem openBall_one_eq_of_val_lt_one (v : Valuation K Γ₀) {c : K} (hc : v c < 1) :
    openBall v c 1 = openBall v 0 1 := by
  ext x
  simp only [mem_openBall, sub_zero]
  constructor
  · intro hx
    have h1 : v x ≤ max (v (x - c)) (v c) := by simpa using val_sub_le_max v x c 0
    exact lt_of_le_of_lt h1 (max_lt hx hc)
  · intro hx
    have h1 : v (x - c) ≤ max (v x) (v c) := by simpa using val_sub_le_max v x 0 c
    exact lt_of_le_of_lt h1 (max_lt hx hc)

/-- **Johnson, Lemma 2.3.4, the `m` case.** A ball properly contained in the maximal ideal is
contained in a closed ball about `0` of radius `v b < 1`. -/
theorem exists_closedBall_zero_of_isValBall_subset_openBall [IsAlgClosed K]
    (v : Valuation K Γ₀) (hnt : ∃ x : K, x ≠ 0 ∧ v x < 1) {D : Set K} (hD : IsValBall v D)
    (hsub : D ⊆ openBall v 0 1) (hne : D ≠ openBall v 0 1) :
    ∃ b : K, b ≠ 0 ∧ v b < 1 ∧ D ⊆ closedBall v 0 (v b) := by
  cases hD with
  | closed c a =>
    have hc : v c < 1 := by
      have h := hsub (closedBall_self_mem v c (v a))
      rwa [mem_openBall, sub_zero] at h
    have ha : v a < 1 := by
      by_contra hcon
      have h1 : (1 : K) ∈ closedBall v c (v a) := by
        rw [mem_closedBall]
        refine le_trans (val_sub_le_max_of v 1 c) (max_le ?_ ?_)
        · rw [map_one]; exact le_of_not_gt hcon
        · exact le_trans hc.le (le_of_not_gt hcon)
      have h2 := hsub h1
      rw [mem_openBall, sub_zero, map_one] at h2
      exact absurd h2 (lt_irrefl 1)
    obtain ⟨b, hb0, hba, hbc, hb1⟩ := exists_val_between_max_one v hnt ha hc
    refine ⟨b, hb0, hb1, ?_⟩
    intro x hx
    simp only [mem_closedBall, sub_zero] at hx ⊢
    have h1 : v x ≤ max (v (x - c)) (v c) := by simpa using val_sub_le_max v x c 0
    exact le_trans h1 (max_le (le_trans hx hba) hbc)
  | openball c a =>
    rcases eq_or_ne (v a) 0 with ha0 | ha0
    · obtain ⟨b, hb0, hb1⟩ := hnt
      refine ⟨b, hb0, hb1, ?_⟩
      rw [ha0, openBall_zero_eq_empty]
      exact Set.empty_subset _
    · have hc : v c < 1 := by
        have h := hsub (openBall_self_mem (v := v) ha0)
        rwa [mem_openBall, sub_zero] at h
      have ha : v a ≤ 1 := by
        by_contra hcon
        have h1 : (1 : K) ∈ openBall v c (v a) := by
          rw [mem_openBall]
          refine lt_of_le_of_lt (val_sub_le_max_of v 1 c) (max_lt ?_ ?_)
          · rw [map_one]; exact lt_of_not_ge hcon
          · exact lt_of_le_of_lt hc.le (lt_of_not_ge hcon)
        have h2 := hsub h1
        rw [mem_openBall, sub_zero, map_one] at h2
        exact absurd h2 (lt_irrefl 1)
      rcases lt_or_eq_of_le ha with ha' | ha'
      · obtain ⟨b, hb0, hba, hbc, hb1⟩ := exists_val_between_max_one v hnt ha' hc
        refine ⟨b, hb0, hb1, ?_⟩
        intro x hx
        simp only [mem_openBall, mem_closedBall, sub_zero] at hx ⊢
        have h1 : v x ≤ max (v (x - c)) (v c) := by simpa using val_sub_le_max v x c 0
        exact le_trans h1 (max_le (le_of_lt (lt_of_lt_of_le hx hba)) hbc)
      · rw [ha'] at hne
        exact absurd (openBall_one_eq_of_val_lt_one v hc) hne
  | singleton c =>
    have hc : v c < 1 := by
      have h := hsub (Set.mem_singleton c)
      rwa [mem_openBall, sub_zero] at h
    obtain ⟨b, hb0, hbc, -, hb1⟩ :=
      exists_val_between_max_one v hnt hc (by rw [map_zero]; exact zero_lt_one)
    refine ⟨b, hb0, hb1, ?_⟩
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    simpa using hbc
  | univ =>
    exfalso
    have h2 := hsub (Set.mem_univ (1 : K))
    rw [mem_openBall, sub_zero, map_one] at h2
    exact absurd h2 (lt_irrefl 1)

/-- **Johnson, Lemma 2.3.4, the `K` case.** A ball other than the whole field is contained in a
closed ball about `0`. -/
theorem exists_closedBall_zero_of_isValBall_of_ne_univ (v : Valuation K Γ₀)
    (hnt : ∃ x : K, x ≠ 0 ∧ v x < 1) {D : Set K} (hD : IsValBall v D) (hne : D ≠ Set.univ) :
    ∃ b : K, b ≠ 0 ∧ D ⊆ closedBall v 0 (v b) := by
  cases hD with
  | closed c a =>
    obtain ⟨b, hb0, hba, hbc⟩ := exists_val_gt_max v hnt a c
    refine ⟨b, hb0, ?_⟩
    intro x hx
    simp only [mem_closedBall, sub_zero] at hx ⊢
    have h1 : v x ≤ max (v (x - c)) (v c) := by simpa using val_sub_le_max v x c 0
    exact le_trans h1 (max_le (le_of_lt (lt_of_le_of_lt hx hba)) (le_of_lt hbc))
  | openball c a =>
    obtain ⟨b, hb0, hba, hbc⟩ := exists_val_gt_max v hnt a c
    refine ⟨b, hb0, ?_⟩
    intro x hx
    simp only [mem_openBall, mem_closedBall, sub_zero] at hx ⊢
    have h1 : v x ≤ max (v (x - c)) (v c) := by simpa using val_sub_le_max v x c 0
    exact le_trans h1 (max_le (le_of_lt (lt_trans hx hba)) (le_of_lt hbc))
  | singleton c =>
    obtain ⟨b, hb0, hbc, -⟩ := exists_val_gt_max v hnt c 0
    refine ⟨b, hb0, ?_⟩
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    simpa using le_of_lt hbc
  | univ => exact absurd rfl hne

/-- An affine map with nonzero linear part sends balls with radii in `vK` to such balls. -/
theorem isValBall_affine_image (v : Valuation K Γ₀) {b : K} (hb : b ≠ 0) (c : K) {D : Set K}
    (hD : IsValBall v D) : IsValBall v ((fun y : K => c + b * y) '' D) := by
  cases hD with
  | closed d a =>
    have h : (fun y : K => c + b * y) '' closedBall v d (v a)
        = closedBall v (c + b * d) (v (b * a)) := by
      rw [map_mul, affine_image_closedBall v hb c d (v a)]
    exact h ▸ IsValBall.closed (c + b * d) (b * a)
  | openball d a =>
    have h : (fun y : K => c + b * y) '' openBall v d (v a)
        = openBall v (c + b * d) (v (b * a)) := by
      rw [map_mul, affine_image_openBall v hb c d (v a)]
    exact h ▸ IsValBall.openball (c + b * d) (b * a)
  | singleton d =>
    have h : (fun y : K => c + b * y) '' ({d} : Set K) = {c + b * d} := by
      rw [Set.image_singleton]
    exact h ▸ IsValBall.singleton (c + b * d)
  | univ =>
    have h : (fun y : K => c + b * y) '' Set.univ = Set.univ := by
      rw [Set.image_univ, Set.range_eq_univ]
      intro x
      exact ⟨b⁻¹ * (x - c), by
        show c + b * (b⁻¹ * (x - c)) = x
        rw [← mul_assoc, mul_inv_cancel₀ hb, one_mul]; ring⟩
    rw [h]; exact IsValBall.univ

/-- **Johnson, Lemma 2.3.7, the `m` case** in general form: a finite union of balls properly
contained in the maximal ideal does not exhaust it. -/
theorem openBall_zero_ne_finite_union_of_isValBall [IsAlgClosed K] (v : Valuation K Γ₀)
    (hnt : ∃ x : K, x ≠ 0 ∧ v x < 1) {ι : Type*} (s : Finset ι) (D : ι → Set K)
    (hD : ∀ i ∈ s, IsValBall v (D i)) (hsub : ∀ i ∈ s, D i ⊆ openBall v 0 1)
    (hne : ∀ i ∈ s, D i ≠ openBall v 0 1) :
    openBall v 0 1 ≠ ⋃ i ∈ s, D i := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | hs
  · intro hcover
    have h0 : (0 : K) ∈ openBall v 0 1 := by simp
    rw [hcover] at h0
    simpa using h0
  · have hex : ∀ i ∈ s, ∃ b : K, b ≠ 0 ∧ v b < 1 ∧ D i ⊆ closedBall v 0 (v b) :=
      fun i hi => exists_closedBall_zero_of_isValBall_subset_openBall v hnt (hD i hi) (hsub i hi)
        (hne i hi)
    choose b hb0 hb1 hbsub using hex
    let γ : ι → Γ₀ := fun i => if h : i ∈ s then v (b i h) else 1
    have hγ : ∀ i ∈ s, ∃ a : K, v a = γ i := by
      intro i hi
      refine ⟨b i hi, ?_⟩
      show v (b i hi) = if h : i ∈ s then v (b i h) else 1
      rw [dif_pos hi]
    have hlt : ∀ i ∈ s, γ i < 1 := by
      intro i hi
      show (if h : i ∈ s then v (b i h) else 1) < 1
      rw [dif_pos hi]
      exact hb1 i hi
    have hkey := openBall_zero_ne_finite_union_closedBall v hnt s hs γ hγ hlt
    intro hcover
    apply hkey
    refine Set.Subset.antisymm ?_ ?_
    · rw [hcover]
      intro x hx
      simp only [Set.mem_iUnion] at hx ⊢
      obtain ⟨i, hi, hxi⟩ := hx
      refine ⟨i, hi, ?_⟩
      have hγi : γ i = v (b i hi) := by
        show (if h : i ∈ s then v (b i h) else 1) = v (b i hi)
        rw [dif_pos hi]
      rw [hγi]
      exact hbsub i hi hxi
    · intro x hx
      simp only [Set.mem_iUnion] at hx
      obtain ⟨i, hi, hxi⟩ := hx
      simp only [mem_closedBall, sub_zero] at hxi
      simp only [mem_openBall, sub_zero]
      refine lt_of_le_of_lt hxi ?_
      show (if h : i ∈ s then v (b i h) else 1) < 1
      rw [dif_pos hi]
      exact hb1 i hi

/-- **Johnson, Lemma 2.3.7, the `K` case** in general form: a finite union of balls properly
contained in the whole field does not exhaust it. -/
theorem univ_ne_finite_union_of_isValBall (v : Valuation K Γ₀)
    (hnt : ∃ x : K, x ≠ 0 ∧ v x < 1) {ι : Type*} (s : Finset ι) (D : ι → Set K)
    (hD : ∀ i ∈ s, IsValBall v (D i)) (hne : ∀ i ∈ s, D i ≠ Set.univ) :
    Set.univ ≠ ⋃ i ∈ s, D i := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | hs
  · intro hcover
    have h0 : (0 : K) ∈ (Set.univ : Set K) := Set.mem_univ 0
    rw [hcover] at h0
    simpa using h0
  · have hex : ∀ i ∈ s, ∃ b : K, b ≠ 0 ∧ D i ⊆ closedBall v 0 (v b) :=
      fun i hi => exists_closedBall_zero_of_isValBall_of_ne_univ v hnt (hD i hi) (hne i hi)
    choose b hb0 hbsub using hex
    let γ : ι → Γ₀ := fun i => if h : i ∈ s then v (b i h) else 1
    have hγ : ∀ i ∈ s, ∃ a : K, v a = γ i := by
      intro i hi
      refine ⟨b i hi, ?_⟩
      show v (b i hi) = if h : i ∈ s then v (b i h) else 1
      rw [dif_pos hi]
    have hkey := univ_ne_finite_union_closedBall v hnt s hs γ hγ
    intro hcover
    apply hkey
    rw [hcover]
    refine Set.Subset.antisymm ?_ ?_
    · intro x hx
      simp only [Set.mem_iUnion] at hx ⊢
      obtain ⟨i, hi, hxi⟩ := hx
      have hγi : γ i = v (b i hi) := by
        show (if h : i ∈ s then v (b i h) else 1) = v (b i hi)
        rw [dif_pos hi]
      exact ⟨i, hi, by rw [hγi]; exact hbsub i hi hxi⟩
    · rw [← hcover]
      exact Set.subset_univ _

/-- A cover transfers across an affine bijection of the field. -/
theorem cover_transfer {b c : K} (hb : b ≠ 0) {B₀ : Set K} {ι : Type*} (s : Finset ι)
    (D : ι → Set K) (hcover : (fun y : K => c + b * y) '' B₀ = ⋃ i ∈ s, D i) :
    B₀ = ⋃ i ∈ s, (fun y : K => (y - c) * b⁻¹) '' D i := by
  have hφψ : (fun y : K => (c + b * y - c) * b⁻¹) = id := by
    funext y
    have h1 : c + b * y - c = b * y := by ring
    rw [h1]
    show (b * y) * b⁻¹ = y
    rw [mul_comm b y, mul_assoc, mul_inv_cancel₀ hb, mul_one]
  have himg : (fun y : K => (y - c) * b⁻¹) ''
      ((fun y : K => c + b * y) '' B₀) = B₀ := by
    rw [Set.image_image, hφψ]
    exact Set.image_id B₀
  rw [← himg, hcover]
  simp only [Set.image_iUnion]

/-- **Johnson, Lemma 2.3.7.** No nonempty ball of an algebraically closed field with a nontrivial
valuation is a finite union of proper subballs. -/
theorem ne_finite_union_of_proper_subballs [IsAlgClosed K] (v : Valuation K Γ₀)
    (hnt : ∃ x : K, 1 < v x) {B : Set K} (hB : IsValBall v B) (hBne : B.Nonempty)
    {ι : Type*} (s : Finset ι) (D : ι → Set K)
    (hD : ∀ i ∈ s, IsValBall v (D i)) (hDsub : ∀ i ∈ s, D i ⊆ B)
    (hDne : ∀ i ∈ s, D i ≠ B) :
    B ≠ ⋃ i ∈ s, D i := by
  classical
  have hnt' : ∃ x : K, x ≠ 0 ∧ v x < 1 := (exists_ne_zero_val_lt_one_iff v).mpr hnt
  have hpsi : ∀ b c : K, (fun y : K => (y - c) * b⁻¹) = fun y => (-(c * b⁻¹)) + b⁻¹ * y := by
    intro b c; funext y; ring
  have hcomp : ∀ (b c : K), b ≠ 0 → (fun x : K => c + b * ((x - c) * b⁻¹)) = id := by
    intro b c hb
    funext x
    have h1 : b * ((x - c) * b⁻¹) = x - c := by
      rw [mul_comm b ((x - c) * b⁻¹), mul_assoc, inv_mul_cancel₀ hb, mul_one]
    rw [h1]
    show c + (x - c) = x
    ring
  cases hB with
  | univ => exact univ_ne_finite_union_of_isValBall v hnt' s D hD hDne
  | singleton c =>
    intro hcover
    have hDempty : ∀ i ∈ s, D i = ∅ := by
      intro i hi
      rcases Set.subset_singleton_iff_eq.mp (hDsub i hi) with h | h
      · exact h
      · exact absurd h (hDne i hi)
    have hc : c ∈ ⋃ i ∈ s, D i := by rw [← hcover]; exact Set.mem_singleton c
    simp only [Set.mem_iUnion] at hc
    obtain ⟨i, hi, hx⟩ := hc
    rw [hDempty i hi] at hx
    exact hx
  | closed c b =>
    rcases eq_or_ne (v b) 0 with hb0 | hb0
    · rw [hb0, closedBall_zero_eq_singleton] at hDsub hDne ⊢
      intro hcover
      have hDempty : ∀ i ∈ s, D i = ∅ := by
        intro i hi
        rcases Set.subset_singleton_iff_eq.mp (hDsub i hi) with h | h
        · exact h
        · exact absurd h (hDne i hi)
      have hc : c ∈ ⋃ i ∈ s, D i := by rw [← hcover]; exact Set.mem_singleton c
      simp only [Set.mem_iUnion] at hc
      obtain ⟨i, hi, hx⟩ := hc
      rw [hDempty i hi] at hx
      exact hx
    · have hbne : b ≠ 0 := v.ne_zero_iff.mp hb0
      rw [closedBall_eq_affine_image v hbne c] at hDsub hDne ⊢
      intro hcover
      have hcover' := cover_transfer hbne s D hcover
      have himg : (fun y : K => (y - c) * b⁻¹) ''
          ((fun y : K => c + b * y) '' (v.valuationSubring : Set K))
            = (v.valuationSubring : Set K) := by
        rw [Set.image_image]
        have hφψ : (fun y : K => (c + b * y - c) * b⁻¹) = id := by
          funext y
          have h1 : c + b * y - c = b * y := by ring
          rw [h1]
          show (b * y) * b⁻¹ = y
          rw [mul_comm b y, mul_assoc, mul_inv_cancel₀ hbne, mul_one]
        rw [hφψ]
        exact Set.image_id _
      have hball : ∀ i ∈ s, IsBall v ((fun y : K => (y - c) * b⁻¹) '' D i) := by
        intro i hi
        rw [hpsi b c]
        exact (isValBall_affine_image v (inv_ne_zero hbne) (-(c * b⁻¹)) (hD i hi)).isBall
      have hsubO : ∀ i ∈ s, ((fun y : K => (y - c) * b⁻¹) '' D i) ⊆ (v.valuationSubring : Set K) := by
        intro i hi
        rw [← himg]
        exact Set.image_mono (hDsub i hi)
      have hneO : ∀ i ∈ s, ((fun y : K => (y - c) * b⁻¹) '' D i) ≠ (v.valuationSubring : Set K) := by
        intro i hi hcon
        apply hDne i hi
        have hthis : (fun y : K => c + b * y) '' ((fun y : K => (y - c) * b⁻¹) '' D i)
            = (fun y : K => c + b * y) '' (v.valuationSubring : Set K) := by rw [hcon]
        rw [Set.image_image, hcomp b c hbne, Set.image_id] at hthis
        exact hthis
      exact valuationSubring_not_finite_union_isBall v hnt s _ hball hsubO hneO hcover'
  | openball c b =>
    rcases eq_or_ne (v b) 0 with hb0 | hb0
    · rw [hb0, openBall_zero_eq_empty] at hBne
      exact absurd hBne (Set.not_nonempty_empty)
    · have hbne : b ≠ 0 := v.ne_zero_iff.mp hb0
      rw [openBall_eq_affine_image v hbne c] at hDsub hDne ⊢
      intro hcover
      have hcover' := cover_transfer hbne s D hcover
      have himg : (fun y : K => (y - c) * b⁻¹) ''
          ((fun y : K => c + b * y) '' openBall v 0 1) = openBall v 0 1 := by
        rw [Set.image_image]
        have hφψ : (fun y : K => (c + b * y - c) * b⁻¹) = id := by
          funext y
          have h1 : c + b * y - c = b * y := by ring
          rw [h1]
          show (b * y) * b⁻¹ = y
          rw [mul_comm b y, mul_assoc, mul_inv_cancel₀ hbne, mul_one]
        rw [hφψ]
        exact Set.image_id _
      have hval : ∀ i ∈ s, IsValBall v ((fun y : K => (y - c) * b⁻¹) '' D i) := by
        intro i hi
        rw [hpsi b c]
        exact isValBall_affine_image v (inv_ne_zero hbne) (-(c * b⁻¹)) (hD i hi)
      have hsubm : ∀ i ∈ s, ((fun y : K => (y - c) * b⁻¹) '' D i) ⊆ openBall v 0 1 := by
        intro i hi
        rw [← himg]
        exact Set.image_mono (hDsub i hi)
      have hnem : ∀ i ∈ s, ((fun y : K => (y - c) * b⁻¹) '' D i) ≠ openBall v 0 1 := by
        intro i hi hcon
        apply hDne i hi
        have hthis : (fun y : K => c + b * y) '' ((fun y : K => (y - c) * b⁻¹) '' D i)
            = (fun y : K => c + b * y) '' openBall v 0 1 := by rw [hcon]
        rw [Set.image_image, hcomp b c hbne, Set.image_id] at hthis
        exact hthis
      exact openBall_zero_ne_finite_union_of_isValBall v hnt' s _ hval hsubm hnem hcover'



/-! ## Comparability of balls (Johnson's (2.3)), including the mixed radius cases

Johnson uses "any two balls which intersect are comparable" in the proof of Lemma 2.3.2.  The
closed/closed and open/open cases are `closedBall_subset_or_subset` and
`openBall_subset_or_subset` above; the mixed cases are proved here.  Which of the two balls is
the smaller one is decided by the comparison of the two radii. -/

/-- A closed ball of smaller radius inside an open ball. -/
theorem closedBall_subset_openBall (v : Valuation K Γ₀) {c d : K} {a b : K}
    (hcd : v (c - d) < v b) (ha : v a < v b) :
    closedBall v c (v a) ⊆ openBall v d (v b) := by
  intro x hx
  simp only [mem_closedBall] at hx
  simp only [mem_openBall]
  exact lt_of_le_of_lt (val_sub_le_max v x c d) (max_lt (lt_of_le_of_lt hx ha) hcd)

/-- An open ball inside a closed ball. -/
theorem openBall_subset_closedBall (v : Valuation K Γ₀) {c d : K} {a b : K}
    (hcd : v (c - d) ≤ v b) (ha : v a ≤ v b) :
    openBall v c (v a) ⊆ closedBall v d (v b) := by
  intro x hx
  simp only [mem_openBall] at hx
  simp only [mem_closedBall]
  exact le_trans (val_sub_le_max v x c d) (max_le (le_of_lt (lt_of_lt_of_le hx ha)) hcd)

/-- The value of `c - d` is at most the larger of two radii, given a common point `z`. -/
theorem val_sub_le_max_of_mem (v : Valuation K Γ₀) {z c d : K} {a b : K}
    (hz₁ : v (z - c) ≤ v a) (hz₂ : v (z - d) ≤ v b) :
    v (c - d) ≤ max (v a) (v b) := by
  have h1 : v (c - z) ≤ v a := by
    rw [show c - z = -(z - c) by ring, Valuation.map_neg]; exact hz₁
  exact le_trans (val_sub_le_max v c z d) (max_le_max h1 hz₂)

/-- **Johnson (2.3).** Two balls with radii in `vK` that meet are comparable. -/
theorem isValBall_subset_or_subset (v : Valuation K Γ₀) {B₁ B₂ : Set K}
    (h₁ : IsValBall v B₁) (h₂ : IsValBall v B₂) (h : (B₁ ∩ B₂).Nonempty) :
    B₁ ⊆ B₂ ∨ B₂ ⊆ B₁ := by
  obtain ⟨z, hz₁, hz₂⟩ := h
  cases h₁ with
  | univ => exact Or.inr (Set.subset_univ _)
  | singleton c =>
    rw [Set.mem_singleton_iff] at hz₁
    subst hz₁
    cases h₂ with
    | univ => exact Or.inl (Set.subset_univ _)
    | singleton d => exact Or.inl (Set.singleton_subset_iff.mpr hz₂)
    | closed d b => exact Or.inl (Set.singleton_subset_iff.mpr hz₂)
    | openball d b => exact Or.inl (Set.singleton_subset_iff.mpr hz₂)
  | closed c a =>
    cases h₂ with
    | univ => exact Or.inl (Set.subset_univ _)
    | singleton d =>
      rw [Set.mem_singleton_iff] at hz₂
      subst hz₂
      exact Or.inr (Set.singleton_subset_iff.mpr hz₁)
    | closed d b => exact closedBall_subset_or_subset v ⟨z, hz₁, hz₂⟩
    | openball d b =>
      simp only [mem_closedBall] at hz₁
      simp only [mem_openBall] at hz₂
      rcases lt_or_ge (v a) (v b) with hab | hab
      · left
        have h2 : v (z - d) < v b := hz₂
        refine closedBall_subset_openBall v ?_ hab
        have h3 : v (c - z) < v b := by
          rw [show c - z = -(z - c) by ring, Valuation.map_neg]
          exact lt_of_le_of_lt hz₁ hab
        exact lt_of_le_of_lt (val_sub_le_max v c z d) (max_lt h3 h2)
      · right
        have h2 : v (z - d) < v b := hz₂
        refine openBall_subset_closedBall (v := v) (c := d) (d := c) (a := b) (b := a) ?_ hab
        have h1 : v (d - z) ≤ v a := by
          rw [show d - z = -(z - d) by ring, Valuation.map_neg]
          exact le_trans h2.le hab
        have h3 : v (z - c) ≤ v a := hz₁
        exact le_trans (val_sub_le_max v d z c) (max_le h1 h3)
  | openball c a =>
    simp only [mem_openBall] at hz₁
    cases h₂ with
    | univ => exact Or.inl (Set.subset_univ _)
    | singleton d =>
      rw [Set.mem_singleton_iff] at hz₂
      subst hz₂
      exact Or.inr (Set.singleton_subset_iff.mpr hz₁)
    | closed d b =>
      simp only [mem_closedBall] at hz₂
      rcases le_or_gt (v a) (v b) with hab | hab
      · left
        refine openBall_subset_closedBall (v := v) ?_ hab
        have h := val_sub_le_max_of_mem v (z := z) hz₁.le hz₂
        rwa [max_eq_right hab] at h
      · right
        refine closedBall_subset_openBall (v := v) (c := d) (d := c) (a := b) (b := a) ?_ hab
        have h1 : v (d - z) < v a := by
          rw [show d - z = -(z - d) by ring, Valuation.map_neg]
          exact lt_of_le_of_lt hz₂ hab
        have h2 : v (z - c) < v a := hz₁
        exact lt_of_le_of_lt (val_sub_le_max v d z c) (max_lt h1 h2)
    | openball d b => exact openBall_subset_or_subset v ⟨z, hz₁, hz₂⟩



/-! ## Johnson, Lemma 2.3.2: Boolean combinations of balls are unions of swiss cheeses

A *swiss cheese* is `B₀ \ ⋃_{j} B j` with each `B j` a subball of `B₀`.  Johnson's Lemma 2.3.2
says that a Boolean combination of balls is a finite union of swiss cheeses.  The proof goes
through the cells of the pattern of balls containing a point: each cell is an intersection of
balls minus a union of the remaining balls, and by comparability (2.3) it collapses to a swiss
cheese (or is empty). -/

section Lemma232

variable {ι : Type*}

/-- Membership in a finite intersection of sets. -/
theorem mem_iInter_finset (b : ι → Set K) (S : Finset ι) (x : K) :
    x ∈ (⋂ i ∈ S, b i) ↔ ∀ i ∈ S, x ∈ b i := by
  simp

/-- Membership in a finite union of sets. -/
theorem mem_iUnion_finset (b : ι → Set K) (S : Finset ι) (x : K) :
    x ∈ (⋃ i ∈ S, b i) ↔ ∃ i ∈ S, x ∈ b i := by
  simp

/-- A nonempty finite intersection of balls of `vK`-radius is one of them. -/
theorem exists_mem_of_iInter_finset [DecidableEq ι] (v : Valuation K Γ₀)
    {b : ι → Set K} (hb : ∀ i, IsValBall v (b i)) {S : Finset ι} (hS : S.Nonempty)
    (hne : (⋂ i ∈ S, b i).Nonempty) :
    ∃ j ∈ S, (⋂ i ∈ S, b i) = b j := by
  classical
  revert hS hne
  induction S using Finset.induction_on with
  | empty => intro hS; exact absurd hS Finset.not_nonempty_empty
  | insert i S hiS ih =>
    intro hS hne
    by_cases hS' : S.Nonempty
    · have hne' : (⋂ k ∈ S, b k).Nonempty := by
        obtain ⟨x, hx⟩ := hne
        have hx' : ∀ k : ι, k ∈ insert i S → x ∈ b k := by
          simpa only [Set.mem_iInter] using hx
        exact ⟨x, (mem_iInter_finset b S x).mpr fun k hk =>
          hx' k (Finset.mem_insert_of_mem hk)⟩
      obtain ⟨j, hjS, hj⟩ := ih hS' hne'
      have hinter : (⋂ k ∈ insert i S, b k) = b i ∩ b j := by
        rw [show (⋂ k ∈ insert i S, b k) = b i ∩ (⋂ k ∈ S, b k) from by
          ext x; simp [Finset.mem_insert], hj]
      have hne2 : (b i ∩ b j).Nonempty := hinter ▸ hne
      rcases isValBall_subset_or_subset v (hb i) (hb j) hne2 with h | h
      · exact ⟨i, Finset.mem_insert_self i S, by rw [hinter, Set.inter_eq_left.mpr h]⟩
      · exact ⟨j, Finset.mem_insert_of_mem hjS, by rw [hinter, Set.inter_eq_right.mpr h]⟩
    · have hSe : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS'
      subst hSe
      refine ⟨i, Finset.mem_singleton_self i, ?_⟩
      simp

/-- `D` is a finite Boolean combination of balls of `vK`-radius: a Boolean function of the
pattern of balls containing a point. -/
def IsBoolCombOfBalls (v : Valuation K Γ₀) (D : Set K) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (b : ι → Set K) (t : Set ι → Bool),
    (∀ i, IsValBall v (b i)) ∧ ∀ x : K, (x ∈ D ↔ t {i | x ∈ b i} = true)

/-- The cell of a finite set of balls: the points lying in exactly the balls indexed by `S`. -/
def cell [Fintype ι] [DecidableEq ι] (b : ι → Set K) (S : Finset ι) : Set K :=
  (⋂ i ∈ S, b i) \ (⋃ i ∈ Sᶜ, b i)

/-- The cell of `S`, when the Boolean function accepts the pattern `S`, and `∅` otherwise. -/
noncomputable def cellIf [Fintype ι] [DecidableEq ι] (b : ι → Set K) (t : Set ι → Bool)
    (S : Finset ι) : Set K := by
  classical
  exact if t (S : Set ι) = true then cell b S else ∅

theorem mem_cell [Fintype ι] [DecidableEq ι] {b : ι → Set K} {S : Finset ι} {x : K} :
    x ∈ cell b S ↔ ∀ i, (x ∈ b i ↔ i ∈ S) := by
  classical
  constructor
  · intro h
    have h1 : ∀ k ∈ S, x ∈ b k := (mem_iInter_finset b S x).mp h.1
    have h2 : ∀ k, k ∉ S → x ∉ b k := by
      intro k hk hx
      exact h.2 ((mem_iUnion_finset b (Sᶜ) x).mpr ⟨k, by simpa using hk, hx⟩)
    exact fun i => ⟨fun hx => by_contra fun hcon => h2 i hcon hx, fun hi => h1 i hi⟩
  · intro h
    refine ⟨(mem_iInter_finset b S x).mpr fun k hk => (h k).mpr hk, ?_⟩
    intro hx
    obtain ⟨k, hk, hkx⟩ := (mem_iUnion_finset b (Sᶜ) x).mp hx
    have hk' : k ∉ S := by simpa using hk
    exact hk' ((h k).mp hkx)

/-- **The cell decomposition behind Lemma 2.3.2.** A Boolean combination of the balls `b` is the
union of the cells whose pattern the Boolean function accepts. -/
theorem eq_iUnion_cell [Fintype ι] [DecidableEq ι] (b : ι → Set K) (t : Set ι → Bool) :
    {x : K | t {i | x ∈ b i} = true} = ⋃ S : Finset ι, cellIf b t S := by
  classical
  ext x
  constructor
  · intro hx
    refine Set.mem_iUnion.mpr ⟨Finset.univ.filter (fun i => x ∈ b i), ?_⟩
    have hcoe : ((Finset.univ.filter (fun i => x ∈ b i) : Finset ι) : Set ι) = {i | x ∈ b i} := by
      ext i; simp
    have ht : t ((Finset.univ.filter (fun i => x ∈ b i) : Finset ι) : Set ι) = true := by
      rw [hcoe]; exact hx
    show x ∈ cellIf b t (Finset.univ.filter (fun i => x ∈ b i))
    rw [cellIf, if_pos ht]
    rw [mem_cell]
    intro i
    simp
  · intro hx
    obtain ⟨S, hS⟩ := Set.mem_iUnion.mp hx
    by_cases ht : t (S : Set ι) = true
    · rw [cellIf, if_pos ht] at hS
      have hpat : (S : Set ι) = {i | x ∈ b i} := by
        ext i
        exact (mem_cell.mp hS i).symm
      show t {i | x ∈ b i} = true
      rw [← hpat]
      exact ht
    · rw [cellIf, if_neg ht] at hS
      exact absurd hS (Set.notMem_empty x)

end Lemma232


end Johnson


/-! ## Johnson, Lemma 2.3.2: Boolean combinations of balls are finite unions of swiss cheeses

The content added here is:

* `Johnson.iUnion_equiv_reindex`, `Johnson.iUnion_finset_eq_iUnion_subtype` (index bookkeeping);
* `Johnson.diff_iUnion_swissCheese` — the normalisation step of Johnson's proof of 2.3.2: for a
  ball `B₀` and finitely many balls `bᵢ`, the set `B₀ \ ⋃ᵢ bᵢ` is `B₀ \ ⋃ⱼ Cⱼ` with every `Cⱼ` a
  ball *contained in* `B₀` (balls meeting `B₀` are comparable with it; balls disjoint from `B₀`
  contribute nothing);
* `Johnson.cell_eq_swissCheese` — each cell of the pattern of a finite family of balls is a swiss
  cheese;
* `Johnson.isBoolCombOfBalls_eq_iUnion_swissCheese` — **Lemma 2.3.2**: every Boolean combination
  of balls of `vK`-radius is a finite union of swiss cheeses `B₀ \ ⋃ⱼ Bⱼ` with `Bⱼ ⊆ B₀`.

Everything is proved in the framework of `QE/Johnson23_valuation.lean` (`Valuation K Γ₀`, `Γ₀` a
`LinearOrderedCommGroupWithZero`, `IsValBall` = closed balls / open balls of radius in `vK`,
singletons and `K`), using only the comparability of balls `isValBall_subset_or_subset`.
-/

namespace Johnson

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- Reindexing a union along an equivalence. -/
theorem iUnion_equiv_reindex {α β : Type*} (e : α ≃ β) (f : β → Set K) :
    (⋃ i : α, f (e i)) = ⋃ j : β, f j := by
  ext x
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨i, hi⟩; exact ⟨e i, hi⟩
  · rintro ⟨j, hj⟩; exact ⟨e.symm j, by simpa using hj⟩

/-- A union over a `Finset` is a union over the corresponding subtype. -/
theorem iUnion_finset_eq_iUnion_subtype {ι : Type*} (b : ι → Set K) (s : Finset ι) :
    (⋃ i ∈ s, b i) = ⋃ i : {i : ι // i ∈ s}, b i := by
  ext x; simp

/-- **The normalisation behind Johnson's Lemma 2.3.2.**  Given a ball `B₀` and finitely many
balls `bᵢ`, the set `B₀ \ ⋃ᵢ bᵢ` can be written as `B₀ \ ⋃ⱼ Cⱼ` with every `Cⱼ` a ball
contained in `B₀`. -/
theorem diff_iUnion_swissCheese (v : Valuation K Γ₀) {ι : Type*} [Fintype ι]
    {B₀ : Set K} (hB₀ : IsValBall v B₀) (b : ι → Set K) (hb : ∀ i, IsValBall v (b i)) :
    ∃ (m : ℕ) (C : Fin m → Set K), (∀ j, IsValBall v (C j)) ∧
      (∀ j, C j ⊆ B₀) ∧ B₀ \ (⋃ i, b i) = B₀ \ (⋃ j, C j) := by
  classical
  by_cases hP : ∃ i, B₀ ⊆ b i
  · -- some `bᵢ` swallows `B₀`, so both sides are empty
    obtain ⟨i₀, hi₀⟩ := hP
    refine ⟨1, fun _ => B₀, fun _ => hB₀, fun _ => subset_rfl, ?_⟩
    have hcover : B₀ ⊆ ⋃ i, b i := (hi₀.trans (Set.subset_iUnion b i₀))
    have h1 : B₀ \ (⋃ i, b i) = ∅ := Set.sdiff_eq_empty.mpr hcover
    have h2 : (⋃ _j : Fin 1, (B₀ : Set K)) = B₀ := by
      refine Set.Subset.antisymm (Set.iUnion_subset fun _ => subset_rfl) ?_
      intro x hx
      exact Set.mem_iUnion.mpr ⟨0, hx⟩
    rw [h1, h2, Set.sdiff_self]
  · -- keep exactly the balls contained in `B₀`
    push_neg at hP
    let κ := {i : ι // b i ⊆ B₀}
    haveI : Fintype κ := inferInstance
    let e := Fintype.equivFin κ
    refine ⟨Fintype.card κ, fun j => b (e.symm j).1, fun j => hb _,
      fun j => (e.symm j).2, ?_⟩
    rw [iUnion_equiv_reindex (e := e.symm) (f := fun i : κ => b i.1)]
    have hEq : B₀ ∩ (⋃ i : ι, b i) = B₀ ∩ (⋃ i : κ, b i.1) := by
      refine Set.Subset.antisymm ?_ ?_
      · rintro x ⟨hx, hxU⟩
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxU
        have hsub : b i ⊆ B₀ := by
          rcases isValBall_subset_or_subset v (hb i) hB₀ ⟨x, hi, hx⟩ with h | h
          · exact h
          · exact absurd h (hP i)
        exact ⟨hx, Set.mem_iUnion.mpr ⟨⟨i, hsub⟩, hi⟩⟩
      · rintro x ⟨hx, hxU⟩
        obtain ⟨⟨i, _⟩, hi⟩ := Set.mem_iUnion.mp hxU
        exact ⟨hx, Set.mem_iUnion.mpr ⟨i, hi⟩⟩
    ext x
    simp only [Set.mem_sdiff]
    constructor
    · rintro ⟨hx, hxU⟩
      refine ⟨hx, ?_⟩
      intro hxV
      have hmem : x ∈ B₀ ∩ (⋃ i : κ, b i.1) := ⟨hx, hxV⟩
      rw [← hEq] at hmem
      exact hxU hmem.2
    · rintro ⟨hx, hxV⟩
      refine ⟨hx, ?_⟩
      intro hxU
      have hmem : x ∈ B₀ ∩ (⋃ i : ι, b i) := ⟨hx, hxU⟩
      rw [hEq] at hmem
      exact hxV hmem.2

/-- The empty set as a swiss cheese (needed for the cells the Boolean function rejects). -/
theorem empty_swissCheese : (∅ : Set K) = Set.univ \ (⋃ _j : Fin 1, (Set.univ : Set K)) := by
  have hone : (⋃ _j : Fin 1, (Set.univ : Set K)) = Set.univ :=
    Set.eq_univ_iff_forall.mpr fun x => Set.mem_iUnion.mpr ⟨0, Set.mem_univ x⟩
  rw [hone, Set.sdiff_self]

/-- **Johnson, Lemma 2.3.2, one cell.**  The cell of a pattern `S` in a finite family of balls is
a swiss cheese (or empty). -/
theorem cell_eq_swissCheese (v : Valuation K Γ₀) {ι : Type*} [Fintype ι] [DecidableEq ι]
    {b : ι → Set K} (hb : ∀ i, IsValBall v (b i)) (S : Finset ι) :
    ∃ (m : ℕ) (B₀ : Set K) (C : Fin m → Set K),
      IsValBall v B₀ ∧ (∀ j, IsValBall v (C j)) ∧ (∀ j, C j ⊆ B₀) ∧
      cell b S = B₀ \ (⋃ j, C j) := by
  classical
  rcases eq_or_ne S ∅ with hS | hS
  · subst hS
    have hcell : cell b (∅ : Finset ι) = Set.univ \ (⋃ i : ι, b i) := by
      have h1 : (⋂ i ∈ (∅ : Finset ι), b i) = Set.univ := by ext x; simp
      have h2 : (⋃ i ∈ (∅ : Finset ι)ᶜ, b i) = ⋃ i : ι, b i := by
        rw [Finset.compl_empty]
        ext x; simp
      rw [cell, h1, h2]
    obtain ⟨m, C, hC, hCsub, heq⟩ :=
      diff_iUnion_swissCheese v (B₀ := Set.univ) IsValBall.univ b hb
    exact ⟨m, Set.univ, C, IsValBall.univ, hC, fun j => Set.subset_univ _,
      by rw [hcell, heq]⟩
  · by_cases hne : (⋂ i ∈ S, b i).Nonempty
    · -- the intersection of the balls of the pattern is one of them
      obtain ⟨j, hjS, hjeq⟩ :=
        exists_mem_of_iInter_finset v hb (Finset.nonempty_iff_ne_empty.mpr hS) hne
      have hcell : cell b S = b j \ (⋃ i : {i : ι // i ∈ Sᶜ}, b i.1) := by
        rw [cell, hjeq, iUnion_finset_eq_iUnion_subtype]
      obtain ⟨m, C, hC, hCsub, heq⟩ :=
        diff_iUnion_swissCheese v (B₀ := b j) (hb j) (fun i : {i : ι // i ∈ Sᶜ} => b i.1)
          (fun i => hb i.1)
      exact ⟨m, b j, C, hb j, hC, hCsub, by rw [hcell, heq]⟩
    · -- the cell is empty
      have hcell : cell b S = ∅ := by
        rw [cell, Set.not_nonempty_iff_eq_empty.mp hne, Set.empty_sdiff]
      refine ⟨1, Set.univ, fun _ => Set.univ, IsValBall.univ, fun _ => IsValBall.univ,
        fun _ => subset_rfl, ?_⟩
      rw [hcell]
      exact empty_swissCheese (K := K)

/-- **Johnson, Lemma 2.3.2.**  Every Boolean combination of balls of `vK`-radius is a finite union
of swiss cheeses: `⋃ᵢ (B₀ᵢ \ ⋃ⱼ Bᵢⱼ)` with each `Bᵢⱼ` a ball contained in `B₀ᵢ`. -/
theorem isBoolCombOfBalls_eq_iUnion_swissCheese (v : Valuation K Γ₀) {D : Set K}
    (hD : IsBoolCombOfBalls v D) :
    ∃ (n : ℕ) (B₀ : Fin n → Set K) (m : Fin n → ℕ) (C : ∀ i, Fin (m i) → Set K),
      (∀ i, IsValBall v (B₀ i)) ∧ (∀ i j, IsValBall v (C i j)) ∧
      (∀ i j, C i j ⊆ B₀ i) ∧ D = ⋃ i, (B₀ i \ (⋃ j, C i j)) := by
  classical
  obtain ⟨ι, hι, b, t, hb, hDdef⟩ := hD
  haveI := hι
  have key : ∀ S : Finset ι, ∃ (m : ℕ) (B₀ : Set K) (C : Fin m → Set K),
      IsValBall v B₀ ∧ (∀ j, IsValBall v (C j)) ∧ (∀ j, C j ⊆ B₀) ∧
      cellIf b t S = B₀ \ (⋃ j, C j) := by
    intro S
    by_cases ht : t (S : Set ι) = true
    · rw [cellIf, if_pos ht]
      exact cell_eq_swissCheese v hb S
    · refine ⟨1, Set.univ, fun _ => Set.univ, IsValBall.univ, fun _ => IsValBall.univ,
        fun _ => subset_rfl, ?_⟩
      rw [cellIf, if_neg ht]
      exact empty_swissCheese (K := K)
  choose m B₀ C hP using key
  have hB₀ : ∀ S, IsValBall v (B₀ S) := fun S => (hP S).1
  have hC : ∀ S j, IsValBall v (C S j) := fun S => (hP S).2.1
  have hCsub : ∀ S j, C S j ⊆ B₀ S := fun S => (hP S).2.2.1
  have hEq : ∀ S, cellIf b t S = B₀ S \ (⋃ j, C S j) := fun S => (hP S).2.2.2
  let e : Finset ι ≃ Fin (Fintype.card (Finset ι)) := Fintype.equivFin (Finset ι)
  let m' : Fin (Fintype.card (Finset ι)) → ℕ := fun i => m (e.symm i)
  refine ⟨Fintype.card (Finset ι), fun i => B₀ (e.symm i), m',
    fun i => C (e.symm i), fun i => hB₀ _, fun i j => hC _ _, fun i j => hCsub _ _, ?_⟩
  have hD' : D = ⋃ S : Finset ι, (B₀ S \ (⋃ j, C S j)) := by
    rw [show D = {x : K | t {i | x ∈ b i} = true} from Set.ext hDdef, eq_iUnion_cell b t]
    simp only [hEq]
  rw [hD']
  exact (iUnion_equiv_reindex (e := e.symm)
    (f := fun S : Finset ι => B₀ S \ (⋃ j, C S j))).symm


end Johnson

/-! ## Johnson, Lemmas 2.3.3 and 2.3.8: points of `K` in `K`-balls

`K` is a valued field embedded in a valued field `L` by `φ : K →+* L`; the valuation of `K` is
`v.comap φ`.  A *K-ball* of `L` is a ball of `L` whose centre and radius come from `K`.

* `isValBallK_trace`: the trace on `K` of a K-ball is a ball of `K`;
* `lemma_2_3_3`: if `B₁ ⊊ B₂` are K-balls and `vK` is a dense linear order (true when
  `K ⊨ ACVF`), then `B₂ \ B₁` contains a point of `K`;
* `lemma_2_3_8`: if `C = B₀ \ ⋃ᵢ Bᵢ` is nonempty, with `B₀` a K-ball and the `Bᵢ` subballs of
  `B₀` with centre and radius in `K`, then `C` contains a point of `K`.
-/

namespace Johnson

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
variable {L : Type*} [Field L]

/-- The closed ball of radius `0` is a singleton. -/
theorem closedBall_eq_singleton_zero (v : Valuation K Γ₀) (c : K) :
    closedBall v c 0 = {c} := by
  ext x
  rw [mem_closedBall, Set.mem_singleton_iff]
  constructor
  · intro h
    by_contra hx
    have hne : v (x - c) ≠ 0 := v.ne_zero_iff.mpr (sub_ne_zero.mpr hx)
    exact absurd h (not_le.mpr (pos_iff_ne_zero.mpr hne))
  · rintro rfl
    simp

/-- The open ball of radius `0` is empty. -/
theorem openBall_eq_empty_zero (v : Valuation K Γ₀) (c : K) :
    openBall v c 0 = ∅ := by
  ext x
  rw [mem_openBall, Set.mem_empty_iff_false, iff_false]
  exact not_lt.mpr zero_le

/-- Two closed balls of the same radius that meet are equal. -/
theorem closedBall_eq_of_val_sub_le (v : Valuation K Γ₀) {c₁ c₂ : K} {γ : Γ₀}
    (h : v (c₁ - c₂) ≤ γ) : closedBall v c₁ γ = closedBall v c₂ γ := by
  refine Set.Subset.antisymm (closedBall_mono v h le_rfl) ?_
  refine closedBall_mono v ?_ le_rfl
  rwa [show c₂ - c₁ = -(c₁ - c₂) by ring, Valuation.map_neg]

/-- Some element of value strictly between `0` and `1`. -/
theorem exists_val_between_zero_one (w : Valuation K Γ₀)
    (hnt : ∃ x : K, x ≠ 0 ∧ w x < 1) : ∃ u : K, 0 < w u ∧ w u < 1 := by
  obtain ⟨x, hx0, hx1⟩ := hnt
  exact ⟨x, pos_iff_ne_zero.mpr (w.ne_zero_iff.mpr hx0), hx1⟩

/-- Between two values, the lower one possibly `0`, there is a third one. -/
theorem exists_val_between' [IsAlgClosed K] (w : Valuation K Γ₀)
    (hnt : ∃ x : K, x ≠ 0 ∧ w x < 1) {a c : K} (h : w a < w c) :
    ∃ t : K, w a < w t ∧ w t < w c := by
  have hc0 : 0 < w c := lt_of_le_of_lt zero_le h
  have hc : c ≠ 0 := fun hc => by rw [hc, map_zero] at hc0; exact lt_irrefl _ hc0
  rcases eq_or_lt_of_le (zero_le (a := w a)) with ha | ha
  · obtain ⟨u, hu0, hu1⟩ := exists_val_between_zero_one w hnt
    refine ⟨c * u, ?_, ?_⟩
    · rw [map_mul, ← ha]
      exact mul_pos hc0 hu0
    · rw [map_mul]
      simpa using mul_lt_mul_of_pos_left hu1 hc0
  · have ha0 : a ≠ 0 := fun h => by rw [h, map_zero] at ha; exact lt_irrefl _ ha
    obtain ⟨t, -, h1, h2⟩ := exists_val_between w ha0 hc h
    exact ⟨t, h1, h2⟩

/-- Above finitely many values there is another one. -/
theorem exists_val_gt_finset [IsAlgClosed K] (w : Valuation K Γ₀)
    (hnt : ∃ x : K, x ≠ 0 ∧ w x < 1) (s : Finset K) :
    ∃ x : K, ∀ a ∈ s, w a < w x := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by simp⟩
  | insert a₀ s ha ih =>
    obtain ⟨x₀, hx₀⟩ := ih
    rcases le_or_gt (w a₀) (w x₀) with hle | hlt
    · rcases eq_or_lt_of_le (zero_le (a := w x₀)) with h0 | hpos
      · refine ⟨1, ?_⟩
        intro a ha'
        have h1 : w a ≤ w x₀ := by
          rcases Finset.mem_insert.mp ha' with rfl | hmem
          · exact hle
          · exact le_of_lt (hx₀ a hmem)
        have h2 : w a = 0 := by rw [← h0] at h1; exact le_antisymm h1 zero_le
        rw [h2, Valuation.map_one]
        exact zero_lt_one
      · have hx0ne : x₀ ≠ 0 := fun h => by
          rw [h, map_zero] at hpos; exact lt_irrefl _ hpos
        obtain ⟨x, -, hx⟩ := exists_val_lt_val w hnt hx0ne
        refine ⟨x, ?_⟩
        intro a ha'
        rcases Finset.mem_insert.mp ha' with rfl | hmem
        · exact lt_of_le_of_lt hle hx
        · exact lt_trans (hx₀ a hmem) hx
    · have ha0 : a₀ ≠ 0 := fun h => by
        rw [h, map_zero] at hlt; exact absurd hlt (not_lt_of_ge zero_le)
      obtain ⟨x, -, hx⟩ := exists_val_lt_val w hnt ha0
      refine ⟨x, ?_⟩
      intro a ha'
      rcases Finset.mem_insert.mp ha' with rfl | hmem
      · exact hx
      · exact lt_trans (lt_trans (hx₀ a hmem) hlt) hx

/-- K-balls of `L`: balls with centre and radius coming from `K`. -/
inductive IsValBallK (v : Valuation L Γ₀) (φ : K →+* L) : Set L → Prop
  | closed (c b : K) : IsValBallK v φ (closedBall v (φ c) ((v.comap φ) b))
  | openball (c b : K) : IsValBallK v φ (openBall v (φ c) ((v.comap φ) b))
  | singleton (c : K) : IsValBallK v φ {φ c}
  | univ : IsValBallK v φ Set.univ

/-- The trace on `K` of a K-ball is a ball of `K`. -/
theorem isValBallK_trace (v : Valuation L Γ₀) (φ : K →+* L) {B : Set L}
    (hB : IsValBallK v φ B) : IsValBall (v.comap φ) {x : K | φ x ∈ B} := by
  cases hB with
  | closed c b =>
    have h : {x : K | φ x ∈ closedBall v (φ c) ((v.comap φ) b)}
        = closedBall (v.comap φ) c ((v.comap φ) b) := by
      ext x
      simp only [Set.mem_setOf_eq, mem_closedBall, Valuation.comap_apply, map_sub]
    rw [h]; exact IsValBall.closed c b
  | openball c b =>
    have h : {x : K | φ x ∈ openBall v (φ c) ((v.comap φ) b)}
        = openBall (v.comap φ) c ((v.comap φ) b) := by
      ext x
      simp only [Set.mem_setOf_eq, mem_openBall, Valuation.comap_apply, map_sub]
    rw [h]; exact IsValBall.openball c b
  | singleton c =>
    have h : {x : K | φ x ∈ ({φ c} : Set L)} = {c} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      exact ⟨fun h => φ.injective h, fun h => by rw [h]⟩
    rw [h]; exact IsValBall.singleton c
  | univ =>
    have h : {x : K | φ x ∈ (Set.univ : Set L)} = Set.univ := by
      ext x; simp
    rw [h]; exact IsValBall.univ

/-- A nonempty K-ball has a point of `K`. -/
theorem isValBallK_exists_point (v : Valuation L Γ₀) (φ : K →+* L) {B : Set L}
    (hB : IsValBallK v φ B) (hne : B.Nonempty) : ∃ x : K, φ x ∈ B := by
  cases hB with
  | closed c b => exact ⟨c, closedBall_self_mem v (φ c) ((v.comap φ) b)⟩
  | openball c b =>
    rcases eq_or_ne b 0 with hb | hb
    · rw [hb, map_zero, openBall_eq_empty_zero] at hne ⊢
      obtain ⟨y, hy⟩ := hne
      exact absurd hy (by simp)
    · refine ⟨c, openBall_self_mem (v := v) ?_⟩
      rw [Valuation.comap_apply, v.ne_zero_iff]
      exact fun h => hb (φ.injective (by simpa using h))
  | singleton c => exact ⟨c, Set.mem_singleton _⟩
  | univ => exact ⟨0, Set.mem_univ _⟩

/-! ## Johnson, Lemma 2.3.3

If `B₁ ⊊ B₂` are K-balls of `L` and `vK` is a dense linear order (which holds when `K ⊨ ACVF`),
then `B₂ \ B₁` contains a point of `K`.
-/

/-- `c + 1 ≠ c` in a field. -/
theorem add_one_ne_self (c : K) : c + 1 ≠ c := by
  intro h
  exact one_ne_zero (add_left_cancel (a := c) (b := 1) (c := 0) (by rw [add_zero]; exact h))

/-- The value of `x - c` in `K` is the value of `φ x - φ c` in `L`. -/
theorem comap_apply_sub (v : Valuation L Γ₀) (φ : K →+* L) (x c : K) :
    (v.comap φ) (x - c) = v (φ x - φ c) := by
  rw [Valuation.comap_apply, map_sub φ x c]

/-- `v (φ c₂ - φ c₁)` is the value of `c₁ - c₂` in `K`. -/
theorem comap_sub_swap (v : Valuation L Γ₀) (φ : K →+* L) (c₁ c₂ : K) :
    v (φ c₂ - φ c₁) = (v.comap φ) (c₁ - c₂) := by
  rw [show φ c₂ - φ c₁ = -(φ c₁ - φ c₂) by ring, Valuation.map_neg, Valuation.comap_apply,
    map_sub φ c₁ c₂]

/-- A closed K-ball of positive radius contains points of `K` other than any prescribed one. -/
theorem exists_mem_closedBall_ne [IsAlgClosed K] (v : Valuation L Γ₀) (φ : K →+* L)
    (hnt : ∃ x : K, x ≠ 0 ∧ (v.comap φ) x < 1) {c b : K} (hb : b ≠ 0) (c' : K) :
    ∃ x : K, (v.comap φ) (x - c) ≤ (v.comap φ) b ∧ x ≠ c' := by
  classical
  obtain ⟨u, hu0, hu1⟩ := exists_val_between_zero_one (v.comap φ) hnt
  have hu : (v.comap φ) (1 + u) ≤ 1 := by
    have h := map_add_le_max (f := v.comap φ) (1 : K) u
    rw [(v.comap φ).map_one] at h
    exact le_trans h (max_le le_rfl hu1.le)
  by_cases h : c' - c = b
  · refine ⟨c + b * (1 + u), ?_, ?_⟩
    · rw [show c + b * (1 + u) - c = b * (1 + u) by ring, map_mul]
      calc (v.comap φ) b * (v.comap φ) (1 + u) ≤ (v.comap φ) b * 1 :=
            mul_le_mul_of_nonneg_left hu zero_le
        _ = (v.comap φ) b := mul_one _
    · intro hx
      have h1 : b * (1 + u) = c' - c := by rw [← hx]; ring
      rw [h] at h1
      have h2 : b * (1 + u) = b * 1 := by rw [mul_one]; exact h1
      have h3 : 1 + u = 1 := mul_left_cancel₀ hb h2
      have h4 : u = 0 := add_left_cancel (a := 1) (b := u) (c := 0) (by rw [add_zero]; exact h3)
      rw [h4, map_zero] at hu0
      exact absurd hu0 (lt_irrefl 0)
  · refine ⟨c + b, ?_, ?_⟩
    · rw [show c + b - c = b by ring]
    · intro hx
      exact h (by rw [← hx]; ring)

/-- An open K-ball of positive radius contains points of `K` other than any prescribed one. -/
theorem exists_mem_openBall_ne [IsAlgClosed K] (v : Valuation L Γ₀) (φ : K →+* L)
    (hnt : ∃ x : K, x ≠ 0 ∧ (v.comap φ) x < 1) {c b : K} (hb : 0 < (v.comap φ) b) (c' : K) :
    ∃ x : K, (v.comap φ) (x - c) < (v.comap φ) b ∧ x ≠ c' := by
  classical
  by_cases h : c = c'
  · subst h
    obtain ⟨u, hu0, hu1⟩ := exists_val_between_zero_one (v.comap φ) hnt
    refine ⟨c + b * u, ?_, ?_⟩
    · rw [show c + b * u - c = b * u by ring, map_mul]
      simpa using mul_lt_mul_of_pos_left hu1 hb
    · intro hx
      have h1 : b * u = 0 :=
        add_left_cancel (a := c) (b := b * u) (c := 0) (by rw [add_zero]; exact hx)
      rcases mul_eq_zero.mp h1 with h2 | h2
      · exact absurd h2 ((v.comap φ).ne_zero_iff.mp (ne_of_gt hb))
      · rw [h2, map_zero] at hu0
        exact absurd hu0 (lt_irrefl 0)
  · exact ⟨c, by rw [show c - c = 0 by ring, map_zero]; exact hb, h⟩

/-- **Johnson, Lemma 2.3.3.**  If `B₁ ⊊ B₂` are K-balls of `L`, then `B₂ \ B₁` contains a point
of `K`.  (`K` algebraically closed and nontrivially valued is used through the density of the
value group and the unboundedness of the values.) -/
theorem lemma_2_3_3 [IsAlgClosed K] (v : Valuation L Γ₀) (φ : K →+* L)
    (hnt : ∃ x : K, x ≠ 0 ∧ (v.comap φ) x < 1)
    {B₁ B₂ : Set L} (h₁ : IsValBallK v φ B₁) (h₂ : IsValBallK v φ B₂)
    (hsub : B₁ ⊆ B₂) (hne : B₁ ≠ B₂) :
    ∃ x : K, φ x ∈ B₂ ∧ φ x ∉ B₁ := by
  classical
  have hmem : ∀ (y c : K) (γ : Γ₀),
      φ y ∈ closedBall v (φ c) γ ↔ (v.comap φ) (y - c) ≤ γ := by
    intro y c γ
    rw [mem_closedBall, comap_apply_sub]
  have hmemO : ∀ (y c : K) (γ : Γ₀),
      φ y ∈ openBall v (φ c) γ ↔ (v.comap φ) (y - c) < γ := by
    intro y c γ
    rw [mem_openBall, comap_apply_sub]
  have hmemS : ∀ (y c : K), φ y ∈ ({φ c} : Set L) ↔ y = c := by
    intro y c
    rw [Set.mem_singleton_iff]
    exact ⟨fun h => φ.injective h, fun h => by rw [h]⟩
  revert hsub hne
  cases h₂ with
  | univ =>
    intro _ hne
    cases h₁ with
    | univ => exact absurd rfl hne
    | singleton c =>
      exact ⟨c + 1, Set.mem_univ _, by rw [hmemS]; exact add_one_ne_self c⟩
    | closed c b =>
      rcases eq_or_ne b 0 with hb | hb
      · rw [hb, map_zero, closedBall_eq_singleton_zero]
        exact ⟨c + 1, Set.mem_univ _, by rw [hmemS]; exact add_one_ne_self c⟩
      · obtain ⟨b', -, hb'⟩ := exists_val_lt_val (v.comap φ) hnt hb
        refine ⟨c + b', Set.mem_univ _, ?_⟩
        rw [hmem, show c + b' - c = b' by ring]
        exact not_le.mpr hb'
    | openball c b =>
      rcases eq_or_ne b 0 with hb | hb
      · rw [hb, map_zero, openBall_eq_empty_zero]
        exact ⟨0, Set.mem_univ _, Set.notMem_empty _⟩
      · obtain ⟨b', -, hb'⟩ := exists_val_lt_val (v.comap φ) hnt hb
        refine ⟨c + b', Set.mem_univ _, ?_⟩
        rw [hmemO, show c + b' - c = b' by ring]
        exact not_lt.mpr hb'.le
  | singleton c₂ =>
    intro hsub hne
    rcases Set.subset_singleton_iff_eq.mp hsub with h | h
    · exact ⟨c₂, Set.mem_singleton _, by rw [h]; exact Set.notMem_empty _⟩
    · exact absurd h hne
  | closed c₂ b₂ =>
    intro hsub hne
    rcases eq_or_ne b₂ 0 with hb₂ | hb₂
    · rw [hb₂, map_zero, closedBall_eq_singleton_zero] at hsub hne ⊢
      rcases Set.subset_singleton_iff_eq.mp hsub with h | h
      · exact ⟨c₂, Set.mem_singleton _, by rw [h]; exact Set.notMem_empty _⟩
      · exact absurd h hne
    · have hβpos : 0 < (v.comap φ) b₂ :=
        pos_iff_ne_zero.mpr ((v.comap φ).ne_zero_iff.mpr hb₂)
      cases h₁ with
      | univ =>
        exfalso
        obtain ⟨b', -, hb'⟩ := exists_val_lt_val (v.comap φ) hnt hb₂
        have hmem' : φ (c₂ + b') ∈ closedBall v (φ c₂) ((v.comap φ) b₂) :=
          hsub (Set.mem_univ _)
        rw [hmem, show c₂ + b' - c₂ = b' by ring] at hmem'
        exact absurd hmem' (not_le.mpr hb')
      | singleton c₁ =>
        obtain ⟨x, hx1, hx2⟩ := exists_mem_closedBall_ne v φ hnt hb₂ c₁
        exact ⟨x, by rw [hmem]; exact hx1, by rw [hmemS]; exact hx2⟩
      | closed c₁ b₁ =>
        have hc₁ : (v.comap φ) (c₁ - c₂) ≤ (v.comap φ) b₂ := by
          have h := hsub (closedBall_self_mem v (φ c₁) ((v.comap φ) b₁))
          rwa [hmem] at h
        have hγ : (v.comap φ) b₁ < (v.comap φ) b₂ := by
          by_contra hcon
          push Not at hcon
          have hEq : closedBall v (φ c₁) ((v.comap φ) b₁)
              = closedBall v (φ c₂) ((v.comap φ) b₂) := by
            refine Set.Subset.antisymm hsub ?_
            refine closedBall_mono v ?_ hcon
            rw [comap_sub_swap]
            exact le_trans hc₁ hcon
          exact hne hEq
        obtain ⟨t, ht1, ht2⟩ := exists_val_between' (v.comap φ) hnt hγ
        refine ⟨c₁ + t, ?_, ?_⟩
        · rw [hmem, show c₁ + t - c₂ = (c₁ - c₂) + t by ring]
          exact le_trans (map_add_le_max (f := v.comap φ) (c₁ - c₂) t)
            (max_le hc₁ ht2.le)
        · rw [hmem, show c₁ + t - c₁ = t by ring]
          exact not_le.mpr ht1
      | openball c₁ b₁ =>
        rcases eq_or_ne b₁ 0 with hb₁ | hb₁
        · rw [hb₁, map_zero, openBall_eq_empty_zero]
          refine ⟨c₂, ?_, Set.notMem_empty _⟩
          rw [hmem, show c₂ - c₂ = 0 by ring, map_zero]
          exact zero_le
        · have hc₁ : (v.comap φ) (c₁ - c₂) ≤ (v.comap φ) b₂ := by
            have h := hsub (openBall_self_mem (v := v) (c := φ c₁) (γ := (v.comap φ) b₁)
              ((v.comap φ).ne_zero_iff.mpr hb₁))
            rwa [hmem] at h
          have hγ : (v.comap φ) b₁ ≤ (v.comap φ) b₂ := by
            by_contra hcon
            push Not at hcon
            obtain ⟨t, ht1, ht2⟩ := exists_val_between' (v.comap φ) hnt hcon
            have hmemB₁ : φ (c₁ + t) ∈ openBall v (φ c₁) ((v.comap φ) b₁) := by
              rw [hmemO, show c₁ + t - c₁ = t by ring]; exact ht2
            have hmemB₂ := hsub hmemB₁
            rw [hmem, show c₁ + t - c₂ = (c₁ - c₂) + t by ring] at hmemB₂
            have hlt : (v.comap φ) t ≤
                max ((v.comap φ) ((c₁ - c₂) + t)) ((v.comap φ) (c₁ - c₂)) := by
              have hh := val_sub_le_max (v.comap φ) ((c₁ - c₂) + t) 0 (c₁ - c₂)
              rw [sub_zero, zero_sub, Valuation.map_neg,
                show ((c₁ - c₂) + t) - (c₁ - c₂) = t by ring] at hh
              exact hh
            exact absurd (le_trans hlt (max_le hmemB₂ hc₁)) (not_le.mpr ht1)
          rcases eq_or_lt_of_le hγ with hγ' | hγ'
          · refine ⟨c₁ + b₂, ?_, ?_⟩
            · rw [hmem, show c₁ + b₂ - c₂ = (c₁ - c₂) + b₂ by ring]
              exact le_trans (map_add_le_max (f := v.comap φ) (c₁ - c₂) b₂)
                (max_le hc₁ le_rfl)
            · rw [hmemO, show c₁ + b₂ - c₁ = b₂ by ring]
              exact not_lt.mpr hγ'.le
          · obtain ⟨t, ht1, ht2⟩ := exists_val_between' (v.comap φ) hnt hγ'
            refine ⟨c₁ + t, ?_, ?_⟩
            · rw [hmem, show c₁ + t - c₂ = (c₁ - c₂) + t by ring]
              exact le_trans (map_add_le_max (f := v.comap φ) (c₁ - c₂) t)
                (max_le hc₁ ht2.le)
            · rw [hmemO, show c₁ + t - c₁ = t by ring]
              exact not_lt.mpr ht1.le
  | openball c₂ b₂ =>
    intro hsub hne
    rcases eq_or_ne b₂ 0 with hb₂ | hb₂
    · rw [hb₂, map_zero, openBall_eq_empty_zero] at hsub hne ⊢
      exact absurd (Set.subset_empty_iff.mp hsub) hne
    · have hβpos : 0 < (v.comap φ) b₂ :=
        pos_iff_ne_zero.mpr ((v.comap φ).ne_zero_iff.mpr hb₂)
      cases h₁ with
      | univ =>
        exfalso
        have hmem' : φ (c₂ + b₂) ∈ openBall v (φ c₂) ((v.comap φ) b₂) := hsub (Set.mem_univ _)
        rw [hmemO, show c₂ + b₂ - c₂ = b₂ by ring] at hmem'
        exact absurd hmem' (not_lt.mpr le_rfl)
      | singleton c₁ =>
        obtain ⟨x, hx1, hx2⟩ := exists_mem_openBall_ne v φ hnt hβpos c₁
        exact ⟨x, by rw [hmemO]; exact hx1, by rw [hmemS]; exact hx2⟩
      | closed c₁ b₁ =>
        have hc₁lt : (v.comap φ) (c₁ - c₂) < (v.comap φ) b₂ := by
          have h := hsub (closedBall_self_mem v (φ c₁) ((v.comap φ) b₁))
          rwa [hmemO] at h
        have hγ : (v.comap φ) b₁ < (v.comap φ) b₂ := by
          by_contra hcon
          push Not at hcon
          have hmemB₁ : φ (c₁ + b₂) ∈ closedBall v (φ c₁) ((v.comap φ) b₁) := by
            rw [hmem, show c₁ + b₂ - c₁ = b₂ by ring]; exact hcon
          have hmemB₂ := hsub hmemB₁
          rw [hmemO, show c₁ + b₂ - c₂ = (c₁ - c₂) + b₂ by ring] at hmemB₂
          have hh : (v.comap φ) b₂ ≤
              max ((v.comap φ) ((c₁ - c₂) + b₂)) ((v.comap φ) (c₁ - c₂)) := by
            have hvv := val_sub_le_max (v.comap φ) ((c₁ - c₂) + b₂) 0 (c₁ - c₂)
            rw [sub_zero, zero_sub, Valuation.map_neg,
              show ((c₁ - c₂) + b₂) - (c₁ - c₂) = b₂ by ring] at hvv
            exact hvv
          exact absurd (lt_of_le_of_lt hh (max_lt hmemB₂ hc₁lt)) (lt_irrefl _)
        obtain ⟨t, ht1, ht2⟩ := exists_val_between' (v.comap φ) hnt hγ
        refine ⟨c₁ + t, ?_, ?_⟩
        · rw [hmemO, show c₁ + t - c₂ = (c₁ - c₂) + t by ring]
          exact lt_of_le_of_lt (map_add_le_max (f := v.comap φ) (c₁ - c₂) t)
            (max_lt hc₁lt ht2)
        · rw [hmem, show c₁ + t - c₁ = t by ring]
          exact not_le.mpr ht1
      | openball c₁ b₁ =>
        rcases eq_or_ne b₁ 0 with hb₁ | hb₁
        · rw [hb₁, map_zero, openBall_eq_empty_zero]
          refine ⟨c₂, ?_, Set.notMem_empty _⟩
          rw [hmemO, show c₂ - c₂ = 0 by ring, map_zero]
          exact hβpos
        · have hc₁lt : (v.comap φ) (c₁ - c₂) < (v.comap φ) b₂ := by
            have h := hsub (openBall_self_mem (v := v) (c := φ c₁) (γ := (v.comap φ) b₁)
              ((v.comap φ).ne_zero_iff.mpr hb₁))
            rwa [hmemO] at h
          have hγ : (v.comap φ) b₁ < (v.comap φ) b₂ := by
            rcases lt_trichotomy ((v.comap φ) b₁) ((v.comap φ) b₂) with h | h | h
            · exact h
            · exfalso
              apply hne
              have hsub' : openBall v (φ c₁) ((v.comap φ) b₂) ⊆
                  openBall v (φ c₂) ((v.comap φ) b₂) := by
                have hh2 := hsub
                rw [h] at hh2
                exact hh2
              rw [h]
              refine Set.Subset.antisymm hsub' ?_
              intro z hz
              rw [mem_openBall] at hz ⊢
              refine lt_of_le_of_lt (val_sub_le_max v z (φ c₂) (φ c₁)) (max_lt hz ?_)
              rw [comap_sub_swap]
              exact hc₁lt
            · obtain ⟨t, ht1, ht2⟩ := exists_val_between' (v.comap φ) hnt h
              have hmemB₁ : φ (c₁ + t) ∈ openBall v (φ c₁) ((v.comap φ) b₁) := by
                rw [hmemO, show c₁ + t - c₁ = t by ring]; exact ht2
              have hmemB₂ := hsub hmemB₁
              rw [hmemO, show c₁ + t - c₂ = (c₁ - c₂) + t by ring] at hmemB₂
              have hh : (v.comap φ) t ≤
                  max ((v.comap φ) ((c₁ - c₂) + t)) ((v.comap φ) (c₁ - c₂)) := by
                have hvv := val_sub_le_max (v.comap φ) ((c₁ - c₂) + t) 0 (c₁ - c₂)
                rw [sub_zero, zero_sub, Valuation.map_neg,
                  show ((c₁ - c₂) + t) - (c₁ - c₂) = t by ring] at hvv
                exact hvv
              exact absurd (lt_of_le_of_lt hh (max_lt hmemB₂ hc₁lt)) (not_lt.mpr ht1.le)
          obtain ⟨t, ht1, ht2⟩ := exists_val_between' (v.comap φ) hnt hγ
          refine ⟨c₁ + t, ?_, ?_⟩
          · rw [hmemO, show c₁ + t - c₂ = (c₁ - c₂) + t by ring]
            exact lt_of_le_of_lt (map_add_le_max (f := v.comap φ) (c₁ - c₂) t)
              (max_lt hc₁lt ht2)
          · rw [hmemO, show c₁ + t - c₁ = t by ring]
            exact not_lt.mpr ht1.le


/-! ## Johnson, Lemma 2.3.8

A nonempty swiss cheese cut out by K-balls meets `K`.
-/

/-- **Johnson, Lemma 2.3.8.**  Let `B₀` be a K-ball of `L` and `B₁, …, B_{n-1}` K-balls contained
in `B₀`.  If `B₀ \ ⋃ᵢ Bᵢ` is nonempty, then it contains a point of `K`. -/
theorem lemma_2_3_8 [IsAlgClosed K] (v : Valuation L Γ₀) (φ : K →+* L)
    (hnt : ∃ x : K, x ≠ 0 ∧ (v.comap φ) x < 1)
    {B₀ : Set L} (h₀ : IsValBallK v φ B₀) {n : ℕ} (B : Fin n → Set L)
    (hB : ∀ i, IsValBallK v φ (B i)) (hBsub : ∀ i, B i ⊆ B₀)
    (hne : (B₀ \ ⋃ i, B i).Nonempty) :
    ∃ x : K, φ x ∈ B₀ ∧ ∀ i, φ x ∉ B i := by
  classical
  obtain ⟨z, hz₀, hzU⟩ := hne
  have hzU' : ∀ i, z ∉ B i := fun i h => hzU (Set.mem_iUnion.mpr ⟨i, h⟩)
  -- every `Bᵢ` is strictly smaller than `B₀`
  have hproper : ∀ i, B i ≠ B₀ := by
    intro i hi
    exact hzU' i (hi ▸ hz₀)
  -- the traces on `K`
  set T : Fin n → Set K := fun i => {x : K | φ x ∈ B i} with hT
  set T₀ : Set K := {x : K | φ x ∈ B₀} with hT₀
  have hTball : ∀ i, IsValBall (v.comap φ) (T i) := fun i => isValBallK_trace v φ (hB i)
  have hT₀ball : IsValBall (v.comap φ) T₀ := isValBallK_trace v φ h₀
  have hTsub : ∀ i, T i ⊆ T₀ := fun i x hx => hBsub i hx
  -- each trace is properly contained in the trace of `B₀` (Lemma 2.3.3)
  have hTne : ∀ i, T i ≠ T₀ := by
    intro i hi
    obtain ⟨x, hx₀, hxi⟩ := lemma_2_3_3 v φ hnt (hB i) h₀ (hBsub i) (hproper i)
    have hxT₀ : x ∈ T₀ := hx₀
    rw [← hi] at hxT₀
    exact hxi hxT₀
  have hT₀ne : T₀.Nonempty := by
    obtain ⟨x, hx⟩ := isValBallK_exists_point v φ h₀ ⟨z, hz₀⟩
    exact ⟨x, hx⟩
  have hnt' : ∃ x : K, 1 < (v.comap φ) x := (exists_ne_zero_val_lt_one_iff (v.comap φ)).mp hnt
  -- Lemma 2.3.7 in `K`
  have hcover : T₀ ≠ ⋃ i ∈ (Finset.univ : Finset (Fin n)), T i :=
    ne_finite_union_of_proper_subballs (v.comap φ) hnt' hT₀ball hT₀ne Finset.univ T
      (fun i _ => hTball i) (fun i _ => hTsub i) (fun i _ => hTne i)
  have hwit : ∃ x : K, x ∈ T₀ ∧ x ∉ ⋃ i ∈ (Finset.univ : Finset (Fin n)), T i := by
    by_contra hcon
    push Not at hcon
    refine hcover (Set.Subset.antisymm hcon ?_)
    intro x hx
    have hx' : ∃ i : Fin n, x ∈ T i := by simpa using hx
    obtain ⟨i, hxi⟩ := hx'
    exact hTsub i hxi
  obtain ⟨x, hx₀, hxU⟩ := hwit
  refine ⟨x, hx₀, ?_⟩
  intro i hxi
  exact hxU (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨Finset.mem_univ i, hxi⟩⟩)


/-! ## The combination of 2.3.2 and 2.3.8: a nonempty Boolean combination of K-balls meets `K`

This is the geometric heart of Johnson's Lemma 2.3.9: a nonempty quantifier-free `K`-definable
subset of `L¹` is a Boolean combination of `K`-balls (Lemma 2.3.1, not formalised here), hence a
finite union of swiss cheeses (Lemma 2.3.2), and each nonempty swiss cheese meets `K`
(Lemma 2.3.8).  So only Lemma 2.3.1 is missing from the 1-ec step.
-/

/-- A K-ball of `L` is a ball of `L`. -/
theorem IsValBallK.toIsValBall {v : Valuation L Γ₀} {φ : K →+* L} {B : Set L}
    (h : IsValBallK v φ B) : IsValBall v B := by
  cases h with
  | closed c b => exact IsValBall.closed (φ c) (φ b)
  | openball c b => exact IsValBall.openball (φ c) (φ b)
  | singleton c => exact IsValBall.singleton (φ c)
  | univ => exact IsValBall.univ

/-- Two K-balls of `L` that meet are comparable. -/
theorem isValBallK_subset_or_subset (v : Valuation L Γ₀) (φ : K →+* L) {B₁ B₂ : Set L}
    (h₁ : IsValBallK v φ B₁) (h₂ : IsValBallK v φ B₂) (h : (B₁ ∩ B₂).Nonempty) :
    B₁ ⊆ B₂ ∨ B₂ ⊆ B₁ :=
  isValBall_subset_or_subset v h₁.toIsValBall h₂.toIsValBall h

/-- A nonempty finite intersection of K-balls is one of them. -/
theorem exists_mem_of_iInter_finsetK [DecidableEq ι] (v : Valuation L Γ₀) (φ : K →+* L)
    {b : ι → Set L} (hb : ∀ i, IsValBallK v φ (b i)) {S : Finset ι} (hS : S.Nonempty)
    (hne : (⋂ i ∈ S, b i).Nonempty) :
    ∃ j ∈ S, (⋂ i ∈ S, b i) = b j := by
  classical
  revert hS hne
  induction S using Finset.induction_on with
  | empty => intro hS; exact absurd hS Finset.not_nonempty_empty
  | insert i S hiS ih =>
    intro hS hne
    by_cases hS' : S.Nonempty
    · have hne' : (⋂ k ∈ S, b k).Nonempty := by
        obtain ⟨x, hx⟩ := hne
        have hx' : ∀ k : ι, k ∈ insert i S → x ∈ b k := by
          simpa only [Set.mem_iInter] using hx
        exact ⟨x, (mem_iInter_finset b S x).mpr fun k hk =>
          hx' k (Finset.mem_insert_of_mem hk)⟩
      obtain ⟨j, hjS, hj⟩ := ih hS' hne'
      have hinter : (⋂ k ∈ insert i S, b k) = b i ∩ b j := by
        rw [show (⋂ k ∈ insert i S, b k) = b i ∩ (⋂ k ∈ S, b k) from by
          ext x; simp [Finset.mem_insert], hj]
      have hne2 : (b i ∩ b j).Nonempty := hinter ▸ hne
      rcases isValBallK_subset_or_subset v φ (hb i) (hb j) hne2 with h | h
      · exact ⟨i, Finset.mem_insert_self i S, by rw [hinter, Set.inter_eq_left.mpr h]⟩
      · exact ⟨j, Finset.mem_insert_of_mem hjS, by rw [hinter, Set.inter_eq_right.mpr h]⟩
    · have hSe : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS'
      subst hSe
      refine ⟨i, Finset.mem_singleton_self i, ?_⟩
      simp

/-- The normalisation behind Lemma 2.3.2 for K-balls. -/
theorem diff_iUnion_swissCheeseK (v : Valuation L Γ₀) (φ : K →+* L) {ι : Type*} [Fintype ι]
    {B₀ : Set L} (hB₀ : IsValBallK v φ B₀) (b : ι → Set L)
    (hb : ∀ i, IsValBallK v φ (b i)) :
    ∃ (m : ℕ) (C : Fin m → Set L), (∀ j, IsValBallK v φ (C j)) ∧
      (∀ j, C j ⊆ B₀) ∧ B₀ \ (⋃ i, b i) = B₀ \ (⋃ j, C j) := by
  classical
  by_cases hP : ∃ i, B₀ ⊆ b i
  · obtain ⟨i₀, hi₀⟩ := hP
    refine ⟨1, fun _ => B₀, fun _ => hB₀, fun _ => subset_rfl, ?_⟩
    have hcover : B₀ ⊆ ⋃ i, b i := (hi₀.trans (Set.subset_iUnion b i₀))
    have h1 : B₀ \ (⋃ i, b i) = ∅ := Set.sdiff_eq_empty.mpr hcover
    have h2 : (⋃ _j : Fin 1, (B₀ : Set L)) = B₀ := by
      refine Set.Subset.antisymm (Set.iUnion_subset fun _ => subset_rfl) ?_
      intro x hx
      exact Set.mem_iUnion.mpr ⟨0, hx⟩
    rw [h1, h2, Set.sdiff_self]
  · push Not at hP
    let κ := {i : ι // b i ⊆ B₀}
    haveI : Fintype κ := inferInstance
    let e := Fintype.equivFin κ
    refine ⟨Fintype.card κ, fun j => b (e.symm j).1, fun j => hb _,
      fun j => (e.symm j).2, ?_⟩
    rw [iUnion_equiv_reindex (e := e.symm) (f := fun i : κ => b i.1)]
    have hEq : B₀ ∩ (⋃ i : ι, b i) = B₀ ∩ (⋃ i : κ, b i.1) := by
      refine Set.Subset.antisymm ?_ ?_
      · rintro x ⟨hx, hxU⟩
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxU
        have hsub : b i ⊆ B₀ := by
          rcases isValBallK_subset_or_subset v φ (hb i) hB₀ ⟨x, hi, hx⟩ with h | h
          · exact h
          · exact absurd h (hP i)
        exact ⟨hx, Set.mem_iUnion.mpr ⟨⟨i, hsub⟩, hi⟩⟩
      · rintro x ⟨hx, hxU⟩
        obtain ⟨⟨i, _⟩, hi⟩ := Set.mem_iUnion.mp hxU
        exact ⟨hx, Set.mem_iUnion.mpr ⟨i, hi⟩⟩
    ext x
    simp only [Set.mem_sdiff]
    constructor
    · rintro ⟨hx, hxU⟩
      refine ⟨hx, ?_⟩
      intro hxV
      have hmem : x ∈ B₀ ∩ (⋃ i : κ, b i.1) := ⟨hx, hxV⟩
      rw [← hEq] at hmem
      exact hxU hmem.2
    · rintro ⟨hx, hxV⟩
      refine ⟨hx, ?_⟩
      intro hxU
      have hmem : x ∈ B₀ ∩ (⋃ i : ι, b i) := ⟨hx, hxU⟩
      rw [hEq] at hmem
      exact hxV hmem.2

/-- Lemma 2.3.2 for one cell of a family of K-balls. -/
theorem cell_eq_swissCheeseK (v : Valuation L Γ₀) (φ : K →+* L) {ι : Type*} [Fintype ι]
    [DecidableEq ι] {b : ι → Set L} (hb : ∀ i, IsValBallK v φ (b i)) (S : Finset ι) :
    ∃ (m : ℕ) (B₀ : Set L) (C : Fin m → Set L),
      IsValBallK v φ B₀ ∧ (∀ j, IsValBallK v φ (C j)) ∧ (∀ j, C j ⊆ B₀) ∧
      cell b S = B₀ \ (⋃ j, C j) := by
  classical
  rcases eq_or_ne S ∅ with hS | hS
  · subst hS
    have hcell : cell b (∅ : Finset ι) = Set.univ \ (⋃ i : ι, b i) := by
      have h1 : (⋂ i ∈ (∅ : Finset ι), b i) = Set.univ := by ext x; simp
      have h2 : (⋃ i ∈ (∅ : Finset ι)ᶜ, b i) = ⋃ i : ι, b i := by
        rw [Finset.compl_empty]
        ext x; simp
      rw [cell, h1, h2]
    obtain ⟨m, C, hC, hCsub, heq⟩ :=
      diff_iUnion_swissCheeseK v φ (B₀ := Set.univ) IsValBallK.univ b hb
    exact ⟨m, Set.univ, C, IsValBallK.univ, hC, fun j => Set.subset_univ _,
      by rw [hcell, heq]⟩
  · by_cases hne : (⋂ i ∈ S, b i).Nonempty
    · obtain ⟨j, hjS, hjeq⟩ :=
        exists_mem_of_iInter_finsetK v φ hb (Finset.nonempty_iff_ne_empty.mpr hS) hne
      have hcell : cell b S = b j \ (⋃ i : {i : ι // i ∈ Sᶜ}, b i.1) := by
        rw [cell, hjeq, iUnion_finset_eq_iUnion_subtype]
      obtain ⟨m, C, hC, hCsub, heq⟩ :=
        diff_iUnion_swissCheeseK v φ (B₀ := b j) (hb j) (fun i : {i : ι // i ∈ Sᶜ} => b i.1)
          (fun i => hb i.1)
      exact ⟨m, b j, C, hb j, hC, hCsub, by rw [hcell, heq]⟩
    · have hcell : cell b S = ∅ := by
        rw [cell, Set.not_nonempty_iff_eq_empty.mp hne, Set.empty_sdiff]
      refine ⟨1, Set.univ, fun _ => Set.univ, IsValBallK.univ, fun _ => IsValBallK.univ,
        fun _ => subset_rfl, ?_⟩
      rw [hcell]
      exact empty_swissCheese (K := L)

/-- `D` is a Boolean combination of K-balls: a Boolean function of the pattern of K-balls
containing a point. -/
def IsBoolCombOfBallsK (v : Valuation L Γ₀) (φ : K →+* L) (D : Set L) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (b : ι → Set L) (t : Set ι → Bool),
    (∀ i, IsValBallK v φ (b i)) ∧ ∀ x : L, (x ∈ D ↔ t {i | x ∈ b i} = true)

/-- **Johnson, Lemma 2.3.2 for K-balls.**  A Boolean combination of K-balls is a finite union of
swiss cheeses `B₀ \ ⋃ⱼ Bⱼ` with `Bⱼ ⊆ B₀` K-balls. -/
theorem isBoolCombOfBallsK_eq_iUnion_swissCheese (v : Valuation L Γ₀) (φ : K →+* L)
    {D : Set L} (hD : IsBoolCombOfBallsK v φ D) :
    ∃ (n : ℕ) (B₀ : Fin n → Set L) (m : Fin n → ℕ) (C : ∀ i, Fin (m i) → Set L),
      (∀ i, IsValBallK v φ (B₀ i)) ∧ (∀ i j, IsValBallK v φ (C i j)) ∧
      (∀ i j, C i j ⊆ B₀ i) ∧ D = ⋃ i, (B₀ i \ (⋃ j, C i j)) := by
  classical
  obtain ⟨ι, hι, b, t, hb, hDdef⟩ := hD
  haveI := hι
  have key : ∀ S : Finset ι, ∃ (m : ℕ) (B₀ : Set L) (C : Fin m → Set L),
      IsValBallK v φ B₀ ∧ (∀ j, IsValBallK v φ (C j)) ∧ (∀ j, C j ⊆ B₀) ∧
      cellIf b t S = B₀ \ (⋃ j, C j) := by
    intro S
    by_cases ht : t (S : Set ι) = true
    · rw [cellIf, if_pos ht]
      exact cell_eq_swissCheeseK v φ hb S
    · refine ⟨1, Set.univ, fun _ => Set.univ, IsValBallK.univ, fun _ => IsValBallK.univ,
        fun _ => subset_rfl, ?_⟩
      rw [cellIf, if_neg ht]
      exact empty_swissCheese (K := L)
  choose m B₀ C hP using key
  have hB₀ : ∀ S, IsValBallK v φ (B₀ S) := fun S => (hP S).1
  have hC : ∀ S j, IsValBallK v φ (C S j) := fun S => (hP S).2.1
  have hCsub : ∀ S j, C S j ⊆ B₀ S := fun S => (hP S).2.2.1
  have hEq : ∀ S, cellIf b t S = B₀ S \ (⋃ j, C S j) := fun S => (hP S).2.2.2
  let e : Finset ι ≃ Fin (Fintype.card (Finset ι)) := Fintype.equivFin (Finset ι)
  let m' : Fin (Fintype.card (Finset ι)) → ℕ := fun i => m (e.symm i)
  refine ⟨Fintype.card (Finset ι), fun i => B₀ (e.symm i), m',
    fun i => C (e.symm i), fun i => hB₀ _, fun i j => hC _ _, fun i j => hCsub _ _, ?_⟩
  have hD' : D = ⋃ S : Finset ι, (B₀ S \ (⋃ j, C S j)) := by
    rw [show D = {x : L | t {i | x ∈ b i} = true} from Set.ext hDdef, eq_iUnion_cell b t]
    simp only [hEq]
  rw [hD']
  exact (iUnion_equiv_reindex (e := e.symm)
    (f := fun S : Finset ι => B₀ S \ (⋃ j, C S j))).symm

/-- **The geometric heart of Johnson, Lemma 2.3.9.**  If `K` is algebraically closed and
nontrivially valued and `D ⊆ L` is a nonempty Boolean combination of K-balls, then `D` contains a
point of `K`.  (Up to Lemma 2.3.1, which converts quantifier-free formulas into Boolean
combinations of balls, this is 1-existential closedness of `K` in `L`.) -/
theorem exists_point_of_isBoolCombOfBallsK [IsAlgClosed K] (v : Valuation L Γ₀) (φ : K →+* L)
    (hnt : ∃ x : K, x ≠ 0 ∧ (v.comap φ) x < 1) {D : Set L}
    (hD : IsBoolCombOfBallsK v φ D) (hne : D.Nonempty) :
    ∃ x : K, φ x ∈ D := by
  classical
  obtain ⟨n, B₀, m, C, hB₀, hC, hCsub, hDeq⟩ := isBoolCombOfBallsK_eq_iUnion_swissCheese v φ hD
  obtain ⟨z, hz⟩ := hne
  rw [hDeq] at hz
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
  obtain ⟨x, hx₀, hxU⟩ := lemma_2_3_8 v φ hnt (hB₀ i) (C i) (hC i) (hCsub i) ⟨z, hi⟩
  refine ⟨x, ?_⟩
  rw [hDeq]
  refine Set.mem_iUnion.mpr ⟨i, hx₀, ?_⟩
  intro hc
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hc
  exact hxU j hj


/-! ## Johnson, Lemma 2.3.3 in the trace form stated by Johnson

Johnson states 2.3.3 as: if `B₁ ⊊ B₂` are K-balls of `L` then `B₁ ∩ K ⊊ B₂ ∩ K`.
-/

/-- **Johnson, Lemma 2.3.3** (the form stated in the paper): for K-balls `B₁ ⊆ B₂` with
`B₁ ≠ B₂`, the traces on `K` satisfy `B₁ ∩ K ⊊ B₂ ∩ K`. -/
theorem lemma_2_3_3_trace [IsAlgClosed K] (v : Valuation L Γ₀) (φ : K →+* L)
    (hnt : ∃ x : K, x ≠ 0 ∧ (v.comap φ) x < 1)
    {B₁ B₂ : Set L} (h₁ : IsValBallK v φ B₁) (h₂ : IsValBallK v φ B₂)
    (hsub : B₁ ⊆ B₂) (hne : B₁ ≠ B₂) :
    {x : K | φ x ∈ B₁} ⊂ {x : K | φ x ∈ B₂} := by
  obtain ⟨x, hx₂, hx₁⟩ := lemma_2_3_3 v φ hnt h₁ h₂ hsub hne
  refine ⟨fun y hy => hsub hy, ?_⟩
  intro hBA
  exact hx₁ (hBA hx₂)

end Johnson


variable {K : Type} [Field K] {N : Type} [Field N]
variable {Γ' : Type*} [LinearOrderedCommGroupWithZero Γ']

/-! ## The bridge: `IsKBall` is Johnson's `IsValBallK`

`IsKBall f w` is `IsValBallK w f` with the `singleton` constructor dropped (it is the closed ball
of radius `w (f 0) = 0`), so every `IsKBall` is an `IsValBallK` and Johnson's trace lemma applies
to it: the trace on `K` of an `IsKBall` of `N` is an `IsValBall` for `w.comap f`. -/

/-- A `K`-ball in the sense of `IsKBall` is a `K`-ball in Johnson's sense. -/
theorem isValBallK_of_isKBall {f : K →+* N} {w : Valuation N Γ'} {B : Set N}
    (hB : IsKBall f w B) : Johnson.IsValBallK w f B := by
  cases hB with
  | closed c b => exact Johnson.IsValBallK.closed c b
  | openball c b => exact Johnson.IsValBallK.openball c b
  | univ => exact Johnson.IsValBallK.univ

/-- The trace on `K` of an `IsKBall` of `N` is an `IsValBall` for `w.comap f`. -/
theorem isValBall_trace_of_isKBall {f : K →+* N} {w : Valuation N Γ'} {B : Set N}
    (hB : IsKBall f w B) :
    Johnson.IsValBall (w.comap f) {x : K | f x ∈ B} :=
  Johnson.isValBallK_trace w f (isValBallK_of_isKBall hB)

/-- **Johnson, Lemma 2.3.8, for an arbitrary finite index type.**  Let `B₀` be a `K`-ball of `N`
and `Bᵢ ⊆ B₀` finitely many `K`-balls.  If `B₀ \ ⋃ᵢ Bᵢ` is nonempty, it contains a point of `K`.

The proof is the one of `Johnson.lemma_2_3_8`; only the index type is general (`Fintype ι` in
place of `Fin n`), as `SwissCheese` is stated for an arbitrary finite index type. -/
theorem exists_mem_of_cheese [IsAlgClosed K] (f : K →+* N) (w : Valuation N Γ')
    (hnt : ∃ x : K, x ≠ 0 ∧ w (f x) < 1)
    {B₀ : Set N} (h₀ : IsKBall f w B₀) {ι : Type} [Fintype ι] (B : ι → Set N)
    (hB : ∀ i, IsKBall f w (B i)) (hBsub : ∀ i, B i ⊆ B₀)
    (hne : (B₀ \ ⋃ i, B i).Nonempty) :
    ∃ x : K, f x ∈ B₀ ∧ ∀ i, f x ∉ B i := by
  classical
  -- `hnt` in the form used by Johnson's 2.3.3 and 2.3.7
  have hnt' : ∃ x : K, x ≠ 0 ∧ (w.comap f) x < 1 := by
    obtain ⟨x, hx0, hx⟩ := hnt
    exact ⟨x, hx0, hx⟩
  obtain ⟨z, hz₀, hzU⟩ := hne
  have hzU' : ∀ i, z ∉ B i := fun i h => hzU (Set.mem_iUnion.mpr ⟨i, h⟩)
  -- every `Bᵢ` is strictly smaller than `B₀`
  have hproper : ∀ i, B i ≠ B₀ := by
    intro i hi
    exact hzU' i (hi ▸ hz₀)
  -- the traces on `K`
  set T : ι → Set K := fun i => {x : K | f x ∈ B i} with hT
  set T₀ : Set K := {x : K | f x ∈ B₀} with hT₀
  have hTball : ∀ i, Johnson.IsValBall (w.comap f) (T i) :=
    fun i => isValBall_trace_of_isKBall (hB i)
  have hT₀ball : Johnson.IsValBall (w.comap f) T₀ := isValBall_trace_of_isKBall h₀
  have hTsub : ∀ i, T i ⊆ T₀ := fun i x hx => hBsub i hx
  -- each trace is properly contained in the trace of `B₀` (Lemma 2.3.3)
  have hTne : ∀ i, T i ≠ T₀ := by
    intro i hi
    obtain ⟨x, hx₀, hxi⟩ :=
      Johnson.lemma_2_3_3 w f hnt' (isValBallK_of_isKBall (hB i)) (isValBallK_of_isKBall h₀)
        (hBsub i) (hproper i)
    have hxT₀ : x ∈ T₀ := hx₀
    rw [← hi] at hxT₀
    exact hxi hxT₀
  have hT₀ne : T₀.Nonempty := by
    obtain ⟨x, hx⟩ :=
      Johnson.isValBallK_exists_point w f (isValBallK_of_isKBall h₀) ⟨z, hz₀⟩
    exact ⟨x, hx⟩
  have hnt'' : ∃ x : K, 1 < (w.comap f) x :=
    (Johnson.exists_ne_zero_val_lt_one_iff (w.comap f)).mp hnt'
  -- Lemma 2.3.7 in `K`
  have hcover : T₀ ≠ ⋃ i ∈ (Finset.univ : Finset ι), T i :=
    Johnson.ne_finite_union_of_proper_subballs (w.comap f) hnt'' hT₀ball hT₀ne Finset.univ T
      (fun i _ => hTball i) (fun i _ => hTsub i) (fun i _ => hTne i)
  have hwit : ∃ x : K, x ∈ T₀ ∧ x ∉ ⋃ i ∈ (Finset.univ : Finset ι), T i := by
    by_contra hcon
    push Not at hcon
    refine hcover (Set.Subset.antisymm hcon ?_)
    intro x hx
    have hx' : ∃ i : ι, x ∈ T i := by simpa using hx
    obtain ⟨i, hxi⟩ := hx'
    exact hTsub i hxi
  obtain ⟨x, hx₀, hxU⟩ := hwit
  refine ⟨x, hx₀, ?_⟩
  intro i hxi
  exact hxU (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨Finset.mem_univ i, hxi⟩⟩)

/-- **Johnson, Lemma 2.3.8** (`CheeseMeetsBase`): a nonempty swiss cheese cut out by `K`-balls
meets the image of the base field `K`.  `K` is algebraically closed and `w ∘ f` nontrivial on
`K`; the nontriviality is essential (with `w ∘ f` trivial on `K`, the maximal ideal of `w`
punctured at `0` is a cheese with no `K`-point). -/
theorem cheeseMeetsBase [IsAlgClosed K] (f : K →+* N) (w : Valuation N Γ')
    (hnt : ∃ x : K, x ≠ 0 ∧ w (f x) < 1) : CheeseMeetsBase f w := by
  intro D hD hne
  obtain ⟨ι, hι, B₀, B, h₀, hB, hBsub, hD'⟩ := hD
  letI := hι
  have hne' : (B₀ \ ⋃ i, B i).Nonempty := by rw [← hD']; exact hne
  obtain ⟨c, hc⟩ := exists_mem_of_cheese f w hnt h₀ B hB hBsub hne'
  refine ⟨c, ?_⟩
  rw [hD']
  exact ⟨hc.1, fun h => hc.2 _ (Set.mem_iUnion.mp h).choose_spec⟩


section CloseOneEC

variable {K : Type} [Field K] {L : Type} [Field L]
variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
variable {Γ' : Type*} [LinearOrderedCommGroupWithZero Γ']

/-- **Lemmas 2.3.2 and 2.3.8 together**: a nonempty Boolean combination of `K`-balls meets the
image of `K`, assuming the valuation is nontrivial on `K` (which 2.3.8 needs). -/
theorem goodMeetsBase_of_nontrivial [IsAlgClosed K] {f : K →+* N} {w : Valuation N Γ'}
    (hnt : ∃ x : K, x ≠ 0 ∧ w (f x) < 1) : GoodMeetsBase f w :=
  goodMeetsBase_of_swissCheese (boolCombCheese f w) (cheeseMeetsBase f w hnt)

/-- **Hypothesis (iii) of Johnson's criterion, with every input discharged.**  `OneECIn` holds for
every `L_val`-embedding of valued fields with `K` algebraically closed and the valuation nontrivial
on `K`. -/
theorem oneECIn_of_nontrivial [IsAlgClosed K] (v : Valuation K Γ) (w : Valuation L Γ')
    (F : @FirstOrder.Language.Embedding Language.val K L (valStructure v) (valStructure w))
    (hnt : ∃ x : K, x ≠ 0 ∧ w (ringHomOfEmbedding v w F x) < 1) :
    @OneECIn Language.val K L (valStructure v) (valStructure w) F := by
  classical
  exact oneECIn_of_inputs' v w F atomGood_of_isAlgClosed
    (goodMeetsBase_of_nontrivial (f := ringHomOfEmbedding v w F) (w := w) hnt)

end CloseOneEC

end ValOneEC

#print axioms ValOneEC.goodMeetsBase_of_nontrivial
#print axioms ValOneEC.oneECIn_of_nontrivial

/-! ## 16. Transport of `OneECIn` to `ValPM.valField.ModelType`, and hypothesis (iii) there -/

namespace ValOneEC

open FirstOrder FirstOrder.Language FirstOrder.Ring

section Transport

variable {L : FirstOrder.Language.{0, 0}} {M N : Type}

/-- An embedding transports along an equality of the two `L`-structures. -/
def embeddingCast {sM sM' : L.Structure M} {sN sN' : L.Structure N}
    (hM : sM = sM') (hN : sN = sN') (f : @Embedding L M N sM sN) :
    @Embedding L M N sM' sN' where
  toFun := f.toFun
  inj' := f.inj'
  map_fun' := by subst hM; subst hN; exact f.map_fun'
  map_rel' := by subst hM; subst hN; exact f.map_rel'

/-- The transported embedding is heterogeneously equal to the original. -/
theorem embeddingCast_heq {sM sM' : L.Structure M} {sN sN' : L.Structure N}
    (hM : sM = sM') (hN : sN = sN') (f : @Embedding L M N sM sN) :
    HEq f (embeddingCast hM hN f) := by
  subst hM
  subst hN
  exact HEq.rfl

/-- **`OneECIn` is invariant under equality of the structures**, provided the embeddings match. -/
theorem oneECIn_congr {sM sM' : L.Structure M} {sN sN' : L.Structure N}
    (hM : sM = sM') (hN : sN = sN') (f : @Embedding L M N sM sN)
    (f' : @Embedding L M N sM' sN') (hf : HEq f f') :
    (@OneECIn L M N sM sN f ↔ @OneECIn L M N sM' sN' f') := by
  subst hM
  subst hN
  rw [eq_of_heq hf]

/-- The form used in practice: transport the whole statement, embedding included. -/
theorem oneECIn_congr' {sM sM' : L.Structure M} {sN sN' : L.Structure N}
    (hM : sM = sM') (hN : sN = sN') (f : @Embedding L M N sM sN) :
    (@OneECIn L M N sM sN f ↔
      @OneECIn L M N sM' sN' (embeddingCast hM hN f)) :=
  oneECIn_congr hM hN f _ (embeddingCast_heq hM hN f)

end Transport

-- (the ModelType section is the remaining glue; see QE-PLAN.md.  It needs
-- `isAlgClosed_of_model`, i.e. ACVF_val's algebraic-closedness axioms connected to
-- Mathlib's IsAlgClosed through `Field.realize_genericMonicPolyHasRoot` and
-- `LHom.realize_onBoundedFormula`.)

end ValOneEC

namespace ValOneEC

/-! ## 16b. A model of `ACVF_val` is algebraically closed -/

section IsAlgClosedModel

open FirstOrder FirstOrder.Language FirstOrder.Ring

/-- **A model of `ACVF_val` is algebraically closed.**  This is the piece that connects the theory's
`genericMonicPolyHasRoot` sentences, which are `L_val` sentences transported along `valRingHom`, to
Mathlib's `IsAlgClosed`; without it the algebraically-closedness half of `ACVF_val` is never used.
The proof is Mathlib's `isAlgClosed_of_model_ACF` with `LHom.realize_onBoundedFormula` inserted. -/
theorem isAlgClosed_of_model (M : ValPM.valField.ModelType) [Field M] [CompatibleRing M]
    [valRingHom.IsExpansionOn M] (hM : M ⊨ ValPM.ACVF_val) : IsAlgClosed M := by
  refine IsAlgClosed.of_exists_root _ ?_
  intro p hpm hpi
  have hpos : 0 < p.natDegree :=
    Polynomial.natDegree_pos_iff_degree_pos.2 (Polynomial.degree_pos_of_irreducible hpi)
  have hmem : ValPM.genericMonicPolyHasRoot p.natDegree ∈ ValPM.ACVF_val :=
    Or.inl (Or.inr ⟨p.natDegree, hpos, rfl⟩)
  have h : M ⊨ ValPM.genericMonicPolyHasRoot p.natDegree := hM.realize_of_mem _ hmem
  have h2 : M ⊨ Field.genericMonicPolyHasRoot p.natDegree := by
    simpa only [Sentence.Realize, Formula.Realize, LHom.realize_onBoundedFormula,
      ValPM.genericMonicPolyHasRoot] using h
  rw [Field.realize_genericMonicPolyHasRoot] at h2
  exact h2 ⟨p, hpm, rfl⟩

end IsAlgClosedModel

/-! ## 16c. Hypothesis (iii) at the level of `valField.ModelType` -/

section ModelType

open FirstOrder FirstOrder.Language FirstOrder.Ring

variable {M : ValPM.valField.ModelType.{0, 0, 0}}

/-- A model of `valField` as a field, with the ring structure read off its `L_val` structure. -/
noncomputable def fieldOfModelValField (M : ValPM.valField.ModelType) : Field M := by
  letI : Language.ring.Structure M := ValPM.ringStructOfVal M
  haveI : valRingHom.IsExpansionOn M := ValPM.ringStructOfVal.expansion M
  haveI : M ⊨ Theory.field := ValPM.model_field_of_valField M M.is_model
  exact FirstOrder.Field.fieldOfModelField M

/-- **Hypothesis (iii) at the level of `valField.ModelType`s**: Johnson's 1-ec property for an
`L_val`-embedding of models of `valField`, read off the concrete-field version through the two
structure equalities.  A model of `ACVF_val` supplies every hypothesis: `IsValPred` (so it is a
Mathlib valued field), its own structure is `valStructure v`, `IsAlgClosed`
(`isAlgClosed_of_model`), and nontriviality (`axNontrivial_realize`). -/
theorem oneECIn_of_modelType (M N : ValPM.valField.ModelType.{0, 0, 0})
    (f : @Embedding Language.val M N M.struc N.struc) (hM : M ⊨ ValPM.ACVF_val) :
    @OneECIn Language.val M N M.struc N.struc f := by
  letI : Language.ring.Structure M := ValPM.ringStructOfVal M
  haveI hexpM : valRingHom.IsExpansionOn M := ValPM.ringStructOfVal.expansion M
  have hfieldM : M ⊨ Theory.field := ValPM.model_field_of_valField M M.is_model
  letI : Field M := FirstOrder.Field.fieldOfModelField M
  letI : CompatibleRing M := FirstOrder.Field.compatibleRingOfModelField M
  have hpredM : ValPM.IsValPred (ValPM.predM : M → M → Prop) := ValPM.isValPred_of_model M.is_model
  haveI hAcM : IsAlgClosed M := isAlgClosed_of_model M hM
  letI : Language.ring.Structure N := ValPM.ringStructOfVal N
  haveI hexpN : valRingHom.IsExpansionOn N := ValPM.ringStructOfVal.expansion N
  have hfieldN : N ⊨ Theory.field := ValPM.model_field_of_valField N N.is_model
  letI : Field N := FirstOrder.Field.fieldOfModelField N
  letI : CompatibleRing N := FirstOrder.Field.compatibleRingOfModelField N
  have hpredN : ValPM.IsValPred (ValPM.predM : N → N → Prop) := ValPM.isValPred_of_model N.is_model
  obtain ⟨Γ, hΓ, v, hv⟩ := ValPM.exists_valuation_of_isValPred hpredM
  letI := hΓ
  obtain ⟨Γ', hΓ', w, hw⟩ := ValPM.exists_valuation_of_isValPred hpredN
  letI := hΓ'
  have hMs : M.struc = FirstOrder.valStructure v :=
    (ValPM.valStruct_ext M).trans (ValPM.valStructOf_eq_valStructure
      (p := (ValPM.predM : M → M → Prop)) (v := v) hv)
  have hNs : N.struc = FirstOrder.valStructure w :=
    (ValPM.valStruct_ext N).trans (ValPM.valStructOf_eq_valStructure
      (p := (ValPM.predM : N → N → Prop)) (v := w) hw)
  let F : @Embedding Language.val M N (FirstOrder.valStructure v) (FirstOrder.valStructure w) :=
    embeddingCast hMs hNs f
  have hpred_emb : ∀ x y : M, ValPM.predM (f x) (f y) ↔ ValPM.predM x y := by
    intro x y
    have h := f.map_rel' ValRel.le ![x, y]
    have h' : (f.toFun ∘ ![x, y]) = ![f x, f y] := by
      funext i
      fin_cases i <;> rfl
    rw [h'] at h
    exact h
  have hord : ∀ x y : M, v x ≤ v y ↔ w (f x) ≤ w (f y) := by
    intro x y
    rw [← hv x y, ← hw]
    exact (hpred_emb x y).symm
  have hnt₀ : M ⊨ ValPM.axNontrivial := hM.realize_of_mem _ (Or.inr (by simp))
  obtain ⟨x, hx0, hx1⟩ := (ValPM.axNontrivial_realize (M := M)).mp hnt₀
  have hone : (@Structure.funMap Language.val M _ 0 ValFunc.one (fun i => i.elim0)) = (1 : M) :=
    ValPM.valFunMap_one
  have hfone : f 1 = 1 := by
    have h := f.map_fun' ValFunc.one (fun i => Fin.elim0 i)
    have hcongr : (f.toFun ∘ (fun i => Fin.elim0 i : Fin 0 → M)) = (fun i => Fin.elim0 i) := by
      funext i
      exact i.elim0
    rw [ValPM.valFunMap_one, hcongr, ValPM.valFunMap_one] at h
    exact h
  have hnt : ∃ y : M, y ≠ 0 ∧ w (f y) < 1 := by
    refine ⟨x, hx0, ?_⟩
    have hvx : ¬ (v (@Structure.funMap Language.val M _ 0 ValFunc.one (fun i => i.elim0)) ≤ v x) :=
      fun hc => hx1 ((hv _ _).mpr hc)
    rw [hone, map_one] at hvx
    have hnot : ¬ (w (f 1) ≤ w (f x)) := by
      intro hc
      have h' : v 1 ≤ v x := (hord 1 x).mpr hc
      rw [map_one] at h'
      exact hvx h'
    rw [hfone, map_one] at hnot
    exact not_le.mp hnot
  have hFeq : ∀ y, F.toFun y = f y := fun y => rfl
  have hntF : ∃ y : M, y ≠ 0 ∧ w (F.toFun y) < 1 := by
    obtain ⟨y, hy0, hy1⟩ := hnt
    exact ⟨y, hy0, by rwa [hFeq y]⟩
  exact (oneECIn_congr' hMs hNs f).mpr (oneECIn_of_nontrivial v w F hntF)

end ModelType

-- The transport to `valField.ModelType` is blocked on one specific thing, recorded with the exact
-- error in QE-PLAN.md: the structure equality `M.struc = FirstOrder.valStructure v` cannot be
-- *stated* without Lean reporting "synthesized type class instance is not definitionally equal to
-- expression inferred by typing rules, synthesized M.struc, inferred valStructure v" -- with
-- `Language.val.Structure` being a class, the equation itself trips instance checking, whichever
-- side is written first and whether or not the instance is first named by `letI`.  Everything else
-- in the proof is in place: `ValPM.valStruct_ext`, `ValPM.valStructOf_eq_valStructure`,
-- `embeddingCast`, `oneECIn_congr'`, `oneECIn_of_nontrivial`, `isAlgClosed_of_model`, and the
-- nontriviality transfer (`ValPM.axNontrivial_realize` plus `hord`).


end ValOneEC
#print axioms ValOneEC.oneECIn_congr
#print axioms ValOneEC.oneECIn_congr'
#print axioms ValOneEC.embeddingCast_heq
#print axioms ValOneEC.oneECIn_of_nontrivial
#print axioms ValOneEC.atomGood_of_isAlgClosed

#print axioms ValOneEC.isAlgClosed_of_model
#print axioms ValOneEC.fieldOfModelValField

#print axioms ValOneEC.oneECIn_of_modelType

/-! ## 17. Johnson §2.2: amalgamation of valuation rings (`star`) -/

set_option maxHeartbeats 1000000


/-!
# Johnson, Chapter 2, §2.2: amalgamation of valued fields

This file formalizes the ring-theoretic core of §2.2 of Will Johnson's thesis
"A direct proof of quantifier elimination and C-minimality in ACVF", the section which supplies
hypothesis (ii) (the amalgamation property) of the criterion Lemma 2.1.4.

Main results:

* `Johnson22.chevalley_subring` — **Chevalley's Lemma 2.2.1(1)**: for a subring `R` of a field
  `K` and a prime ideal `p` of `R` there is a valuation subring `O` of `K` with `R ≤ O` and
  `m_O ∩ R = p`, in the form `x ∈ p ↔ v_O x < 1` for `x ∈ R`.
  It is proved from `LocalSubring.exists_le_valuationSubring` (Mathlib's Chevalley).
* `Johnson22.valuedEmbedding_of_localHom` — **Remark 2.2.2**: an injective ring hom
  `O → O'` of valuation rings which pulls the maximal ideal back to the maximal ideal is induced
  by an embedding of valued fields `Frac O → Frac O'`, and that embedding preserves the relation
  `v x ≤ v y` of the language `L_val`.
* `Johnson22.amalgamation_of_ring_amalgamation` — **Lemma 2.2.7, reduced to its ring-theoretic
  content**: the amalgamation property for valued fields follows from the amalgamation statement
  `star` for valuation rings.
* `Johnson22.star` — **the amalgamation statement for valuation rings, proved** (Johnson's
  proof of 2.2.7 verbatim).  Write `S := B₁ ⊗_B B₂`.  `B₁, B₂` and the fraction fields `A₁, A₂`
  are torsion-free, hence flat, over the valuation ring `B` — this is NOT Johnson's Lemma 2.2.4
  but Mathlib's `Module.Flat.flat_iff_torsion_eq_bot_of_isBezout`, since a valuation ring is a
  Bezout domain (`flat_of_torsion_eq_bot`, `torsion_eq_bot_of_injective`).  Hence
  `B₁ ⊗_B B₂ ↪ A₁ ⊗_B A₂` (`TensorProduct.map_injective_of_flat_flat`), so a minimal prime of `S`
  lifts to a prime of `A₁ ⊗_B A₂`, which contracts to `0` in `A₁` and `A₂` — that is Lemma 2.2.6.
  For the prime `p`: the residue-field tensor `k₁ ⊗_{k₀} k₂` is nontrivial
  (`nontrivial_of_algebraMap_injective_of_isDomain`), and `p` is the pullback of one of its
  primes; `p` contracts to `m₁` and `m₂`.  Then a minimal prime `q ≤ p` contracts to `0`, and
  Chevalley in the two-prime form (`chevalley_hom'`, 2.2.1(2)) gives `S → O₃` with prescribed
  kernels.  The closing `example` typechecks `amalgamation_of_ring_amalgamation star`, i.e. the
  amalgamation property for valued fields, at universe `Type u`.
-/

open IsLocalRing

set_option linter.style.haveILetI false

namespace Johnson22

/-! ### Chevalley's lemma -/

/-- In a local ring, the maximal ideal is the set of non-units. -/
lemma mem_maximalIdeal_iff_not_isUnit {A : Type*} [CommSemiring A] [IsLocalRing A] (a : A) :
    a ∈ maximalIdeal A ↔ ¬ IsUnit a := by
  rw [mem_maximalIdeal, mem_nonunits_iff]

/-- **Chevalley's Lemma 2.2.1(1)** (subring form). Let `R` be a subring of a field `K` and let
`p` be a prime ideal of `R`. Then there is a valuation subring `O` of `K` containing `R` whose
maximal ideal meets `R` in `p`, expressed as: `x ∈ R` lies in `p` iff `v_O x < 1`. -/
theorem chevalley_subring {K : Type*} [Field K] (R : Subring K) (p : Ideal R) [p.IsPrime] :
    ∃ O : ValuationSubring K, R ≤ O.toSubring ∧ ∀ x : R, O.valuation (x : K) < 1 ↔ x ∈ p := by
  classical
  obtain ⟨O, hO⟩ := (LocalSubring.ofPrime R p).exists_le_valuationSubring
  set L := (LocalSubring.ofPrime R p).toSubring with hL
  refine ⟨O, fun x hx => hO.1 (LocalSubring.le_ofPrime R p hx), ?_⟩
  -- units and non-units agree for an inclusion `L ≤ O` of local subrings
  have hnonunit : ∀ (a : K) (ha : a ∈ L),
      (¬ IsUnit (⟨a, ha⟩ : L)) ↔ (¬ IsUnit (⟨a, hO.1 ha⟩ : O)) := by
    intro a ha
    have hEq : (Subring.inclusion hO.1 (⟨a, ha⟩ : L)) = (⟨a, hO.1 ha⟩ : O) := Subtype.ext rfl
    constructor
    · intro h u
      exact h (hO.2.map_nonunit _ (hEq ▸ u))
    · intro h u
      exact h (hEq ▸ u.map (Subring.inclusion hO.1))
  intro x
  have hxL : (x : K) ∈ L := LocalSubring.le_ofPrime R p x.2
  have hxO : (x : K) ∈ O := hO.1 hxL
  have halg : (algebraMap R L x) = (⟨(x : K), hxL⟩ : L) := Subtype.ext rfl
  have h1 : (⟨(x : K), hxO⟩ : O) ∈ maximalIdeal O ↔ ¬ IsUnit (⟨(x : K), hxO⟩ : O) :=
    mem_maximalIdeal_iff_not_isUnit _
  have h2 : ¬ IsUnit (⟨(x : K), hxO⟩ : O) ↔ ¬ IsUnit (⟨(x : K), hxL⟩ : L) :=
    (hnonunit _ hxL).symm
  have h3 : ¬ IsUnit (⟨(x : K), hxL⟩ : L) ↔ (⟨(x : K), hxL⟩ : L) ∈ maximalIdeal L :=
    (mem_maximalIdeal_iff_not_isUnit _).symm
  have h4 : (⟨(x : K), hxL⟩ : L) ∈ maximalIdeal L ↔ x ∈ p := by
    rw [← halg]; exact IsLocalization.AtPrime.to_map_mem_maximal_iff L p x
  rw [← ValuationSubring.valuation_lt_one_iff O ⟨(x : K), hxO⟩]
  exact h1.trans (h2.trans (h3.trans h4))

/-! ### Remark 2.2.2 -/

section Remark222

variable {K K' : Type*} [Field K] [Field K']

/-- Injectivity of `O → O' → K'`. -/
lemma comp_subtype_injective (O : ValuationSubring K) (O' : ValuationSubring K')
    (f : O →+* O') (hinj : Function.Injective f) :
    Function.Injective ⇑(O'.subtype.comp f) :=
  fun x y hxy => hinj (Subtype.ext (show ((f x : O') : K') = ((f y : O') : K') from hxy))

/-- The map of fraction fields induced by a ring hom of valuation rings. -/
noncomputable def fracLift (O : ValuationSubring K) (O' : ValuationSubring K')
    (f : O →+* O') (hinj : Function.Injective f) : K →+* K' :=
  IsFractionRing.lift (g := O'.subtype.comp f) (comp_subtype_injective O O' f hinj)

lemma fracLift_apply (O : ValuationSubring K) (O' : ValuationSubring K')
    (f : O →+* O') (hinj : Function.Injective f) (x : O) :
    fracLift O O' f hinj (x : K) = (f x : K') := by
  have h : fracLift O O' f hinj (algebraMap O K x) = (O'.subtype.comp f) x :=
    IsFractionRing.lift_algebraMap (A := O) (K := K) (L := K') (g := O'.subtype.comp f)
      (comp_subtype_injective O O' f hinj) x
  simpa [fracLift] using h

lemma fracLift_injective (O : ValuationSubring K) (O' : ValuationSubring K')
    (f : O →+* O') (hinj : Function.Injective f) :
    Function.Injective (fracLift O O' f hinj) := by
  intro x y hxy
  have hz : fracLift O O' f hinj (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  have hzero : x - y = 0 := by
    by_contra hne
    have h1 : fracLift O O' f hinj ((x - y) * (x - y)⁻¹) = 1 := by
      rw [mul_inv_cancel₀ hne, map_one]
    rw [map_mul, map_inv₀, hz] at h1
    simp at h1
  exact sub_eq_zero.mp hzero

/-- The fraction-field map preserves membership in the valuation ring. -/
lemma fracLift_mem_iff (O : ValuationSubring K) (O' : ValuationSubring K')
    (f : O →+* O') (hinj : Function.Injective f)
    (hmax : Ideal.comap f (maximalIdeal O') = maximalIdeal O) (x : K) :
    x ∈ O ↔ fracLift O O' f hinj x ∈ O' := by
  have hg := fracLift_apply O O' f hinj
  have hginj := fracLift_injective O O' f hinj
  constructor
  · intro hx
    have h2 : fracLift O O' f hinj x = (f ⟨x, hx⟩ : K') := hg ⟨x, hx⟩
    rw [h2]
    exact (f ⟨x, hx⟩).2
  · intro hx
    by_contra hxO
    have hxne : x ≠ 0 := by rintro rfl; exact hxO (O.zero_mem)
    have hnu : x⁻¹ ∈ O.nonunits :=
      (ValuationSubring.inv_mem_nonunits_iff (A := O)).mpr (Or.inr hxO)
    have hxinv : x⁻¹ ∈ O := ValuationSubring.nonunits_subset hnu
    have hmem : (⟨x⁻¹, hxinv⟩ : O) ∈ maximalIdeal O :=
      ValuationSubring.coe_mem_nonunits_iff.mp hnu
    have hmem' : f ⟨x⁻¹, hxinv⟩ ∈ maximalIdeal O' := by
      have h2 := hmem
      rw [← hmax] at h2
      exact Ideal.mem_comap.mp h2
    have hnn : (fracLift O O' f hinj x)⁻¹ ∈ O'.nonunits := by
      rw [← map_inv₀, hg ⟨x⁻¹, hxinv⟩]
      exact ValuationSubring.coe_mem_nonunits_iff.mpr hmem'
    have hmemO' : (fracLift O O' f hinj x)⁻¹ ∈ O' :=
      ValuationSubring.nonunits_subset hnn
    have hnonunit : ¬ IsUnit (⟨(fracLift O O' f hinj x)⁻¹, hmemO'⟩ : O') :=
      (mem_maximalIdeal_iff_not_isUnit _).mp (ValuationSubring.coe_mem_nonunits_iff.mp hnn)
    have hunit : IsUnit (⟨(fracLift O O' f hinj x)⁻¹, hmemO'⟩ : O') := by
      refine IsUnit.of_mul_eq_one (⟨fracLift O O' f hinj x, hx⟩ : O') ?_
      apply Subtype.ext
      show (fracLift O O' f hinj x)⁻¹ * fracLift O O' f hinj x = 1
      exact inv_mul_cancel₀ (fun h => hxne ((map_eq_zero_iff _ hginj).mp h))
    exact hnonunit hunit

/-- The fraction-field map preserves the relation `v x ≤ v y`. -/
lemma fracLift_val_le_iff (O : ValuationSubring K) (O' : ValuationSubring K')
    (f : O →+* O') (hinj : Function.Injective f)
    (hmax : Ideal.comap f (maximalIdeal O') = maximalIdeal O) (x y : K) :
    O.valuation x ≤ O.valuation y ↔
      O'.valuation (fracLift O O' f hinj x) ≤ O'.valuation (fracLift O O' f hinj y) := by
  have hginj := fracLift_injective O O' f hinj
  have hval := fracLift_mem_iff O O' f hinj hmax
  rw [ValuationSubring.valuation_le_iff, ValuationSubring.valuation_le_iff]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨⟨fracLift O O' f hinj (a : K), (hval (a : K)).mp a.2⟩, by rw [← map_mul, ha]⟩
  · rintro ⟨a, ha⟩
    by_cases hy : y = 0
    · subst hy
      have hgx : fracLift O O' f hinj x = 0 := by rw [← ha, map_zero, mul_zero]
      have hx0 : x = 0 := (map_eq_zero_iff _ hginj).mp hgx
      subst hx0
      exact ⟨0, by simp⟩
    · have hgy : fracLift O O' f hinj y ≠ 0 := fun h => hy ((map_eq_zero_iff _ hginj).mp h)
      have hxa : fracLift O O' f hinj (x * y⁻¹) = (a : K') := by
        rw [map_mul, map_inv₀, ← ha]
        exact mul_inv_cancel_right₀ hgy (a : K')
      refine ⟨⟨x * y⁻¹, (hval _).mpr (by rw [hxa]; exact a.2)⟩, ?_⟩
      show x * y⁻¹ * y = x
      rw [mul_assoc, inv_mul_cancel₀ hy, mul_one]

/-- **Remark 2.2.2** (Johnson, §2.2): a ring hom between valuation rings which is injective and
pulls the maximal ideal back to the maximal ideal is induced by an embedding of valued fields on
fraction fields, and that embedding preserves the relation `v x ≤ v y`. -/
theorem valuedEmbedding_of_localHom (O : ValuationSubring K) (O' : ValuationSubring K')
    (f : O →+* O') (hinj : Function.Injective f)
    (hmax : Ideal.comap f (maximalIdeal O') = maximalIdeal O) :
    ∃ g : K →+* K', Function.Injective g ∧ (∀ x : K, x ∈ O ↔ g x ∈ O') ∧
      ∀ x y : K, O.valuation x ≤ O.valuation y ↔ O'.valuation (g x) ≤ O'.valuation (g y) :=
  ⟨fracLift O O' f hinj, fracLift_injective O O' f hinj,
    fracLift_mem_iff O O' f hinj hmax, fracLift_val_le_iff O O' f hinj hmax⟩

end Remark222

/-! ### Valued embeddings and the amalgamation theorem -/

section Amalgamation

variable {K K' : Type*} [Field K] [Field K']

/-- An embedding of valued fields in Johnson's language `L_val`: an injective ring hom which
preserves the relation `v x ≤ v y`. -/
def IsValEmbedding {Γ Γ' : Type*} [LinearOrderedCommGroupWithZero Γ]
    [LinearOrderedCommGroupWithZero Γ'] (v : Valuation K Γ) (v' : Valuation K' Γ')
    (f : K →+* K') : Prop :=
  Function.Injective f ∧ ∀ x y : K, v x ≤ v y ↔ v' (f x) ≤ v' (f y)

/-- The hypotheses of Remark 2.2.2: an injective ring hom of valuation rings which pulls the
maximal ideal back to the maximal ideal. -/
def IsLocalValHom (O : ValuationSubring K) (O' : ValuationSubring K') (f : O →+* O') : Prop :=
  Function.Injective f ∧ Ideal.comap f (maximalIdeal O') = maximalIdeal O

lemma val_lt_one_iff_of_valEmbedding {Γ Γ' : Type*} [LinearOrderedCommGroupWithZero Γ]
    [LinearOrderedCommGroupWithZero Γ'] {v : Valuation K Γ} {v' : Valuation K' Γ'}
    {f : K →+* K'} (hf : IsValEmbedding v v' f) (x : K) : v x < 1 ↔ v' (f x) < 1 := by
  have h1 : v x < v 1 ↔ v' (f x) < v' (f 1) := by
    rw [lt_iff_not_ge, lt_iff_not_ge, hf.2 1 x]
  simpa using h1

/-- A valued embedding preserves membership in the valuation rings. -/
lemma IsValEmbedding.mem_iff (O : ValuationSubring K) (O' : ValuationSubring K')
    (i : K →+* K') (hi : IsValEmbedding O.valuation O'.valuation i) (x : K) :
    x ∈ O ↔ i x ∈ O' := by
  have h2 : ∀ y : K, O.valuation y ≤ 1 ↔ O'.valuation (i y) ≤ 1 := by
    intro y
    have e1 : (1 : O.ValueGroup) = O.valuation 1 := (map_one _).symm
    have e2 : (1 : O'.ValueGroup) = O'.valuation (i 1) := by rw [map_one, map_one]
    rw [e1, e2]
    exact hi.2 y 1
  rw [← ValuationSubring.valuation_le_one_iff O x,
    ← ValuationSubring.valuation_le_one_iff O' (i x)]
  exact h2 x

/-- The fraction-field map of Remark 2.2.2 is a valued embedding. -/
lemma fracLift_isValEmbedding (O : ValuationSubring K) (O' : ValuationSubring K')
    (f : O →+* O') (hinj : Function.Injective f)
    (hmax : Ideal.comap f (maximalIdeal O') = maximalIdeal O) :
    IsValEmbedding O.valuation O'.valuation (fracLift O O' f hinj) :=
  ⟨fracLift_injective O O' f hinj, fracLift_val_le_iff O O' f hinj hmax⟩

/-- Restricting a valued embedding to the valuation rings gives a local injective hom. -/
lemma isLocalValHom_restrict (O : ValuationSubring K) (O' : ValuationSubring K')
    (i : K →+* K') (hi : IsValEmbedding O.valuation O'.valuation i) :
    IsLocalValHom O O'
      (i.restrict O O' fun x hx => (IsValEmbedding.mem_iff O O' i hi x).mp hx) := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    have h := congrArg (fun z : O' => (z : K')) hxy
    simp only [RingHom.coe_restrict_apply] at h
    exact hi.1 h
  · ext x
    rw [Ideal.mem_comap, ValuationSubring.valuation_lt_one_iff O' (i.restrict _ _ _ x),
      ValuationSubring.valuation_lt_one_iff O x]
    exact (val_lt_one_iff_of_valEmbedding hi (x : K)).symm


/-- Conversely, an injective ring hom which preserves the valuation rings is an `L_val`-embedding:
the quantifier-free type of the language `L_val` is exactly the theory of the valuation ring. -/
theorem isValEmbedding_of_mem_iff (O : ValuationSubring K) (O' : ValuationSubring K')
    (i : K →+* K') (hinj : Function.Injective i) (hmem : ∀ x : K, x ∈ O ↔ i x ∈ O') :
    IsValEmbedding O.valuation O'.valuation i := by
  refine ⟨hinj, ?_⟩
  intro x y
  rw [ValuationSubring.valuation_le_iff, ValuationSubring.valuation_le_iff]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨⟨i (a : K), (hmem (a : K)).mp a.2⟩, by rw [← map_mul, ha]⟩
  · rintro ⟨a, ha⟩
    by_cases hy : y = 0
    · subst hy
      have hx : i x = 0 := by rw [← ha, map_zero, mul_zero]
      have hx0 : x = 0 := hinj (by simpa using hx)
      subst hx0
      exact ⟨0, by simp⟩
    · have hiy : i y ≠ 0 := fun h => hy (hinj (by simpa using h))
      have hxa : i (x * y⁻¹) = (a : K') := by
        rw [map_mul, map_inv₀, ← ha]
        exact mul_inv_cancel_right₀ hiy (a : K')
      refine ⟨⟨x * y⁻¹, (hmem _).mpr (by rw [hxa]; exact a.2)⟩, ?_⟩
      show x * y⁻¹ * y = x
      rw [mul_assoc, inv_mul_cancel₀ hy, mul_one]

universe u

/-- **Amalgamation of valued fields** (Johnson, Lemma 2.2.7), reduced to the ring-theoretic
amalgamation statement `star` for valuation rings, which is where Johnson uses Chevalley's lemma
2.2.1(2) together with the tensor product `O₁ ⊗_{O₀} O₂` (Lemmas 2.2.4-2.2.6). -/
theorem amalgamation_of_ring_amalgamation
    (star : ∀ {A A₁ A₂ : Type u} [Field A] [Field A₁] [Field A₂]
      (B : ValuationSubring A) (B₁ : ValuationSubring A₁) (B₂ : ValuationSubring A₂)
      (f₁ : B →+* B₁) (f₂ : B →+* B₂),
      IsLocalValHom B B₁ f₁ → IsLocalValHom B B₂ f₂ →
      ∃ (C : Type u) (_ : Field C) (B₃ : ValuationSubring C) (g₁ : B₁ →+* B₃) (g₂ : B₂ →+* B₃),
        IsLocalValHom B₁ B₃ g₁ ∧ IsLocalValHom B₂ B₃ g₂ ∧ g₁.comp f₁ = g₂.comp f₂)
    {F F₁ F₂ : Type u} [Field F] [Field F₁] [Field F₂]
    (O : ValuationSubring F) (O₁ : ValuationSubring F₁) (O₂ : ValuationSubring F₂)
    (i₁ : F →+* F₁) (i₂ : F →+* F₂)
    (h₁ : IsValEmbedding O.valuation O₁.valuation i₁)
    (h₂ : IsValEmbedding O.valuation O₂.valuation i₂) :
    ∃ (N : Type u) (_ : Field N) (O₃ : ValuationSubring N) (j₁ : F₁ →+* N) (j₂ : F₂ →+* N),
      IsValEmbedding O₁.valuation O₃.valuation j₁ ∧ IsValEmbedding O₂.valuation O₃.valuation j₂ ∧
      j₁.comp i₁ = j₂.comp i₂ := by
  classical
  -- Step 1: restrict the valued embeddings to local injective homs of valuation rings.
  set f₁ : O →+* O₁ := i₁.restrict O O₁ fun x hx => (IsValEmbedding.mem_iff O O₁ i₁ h₁ x).mp hx
    with hf₁def
  have hf₁ : IsLocalValHom O O₁ f₁ := isLocalValHom_restrict O O₁ i₁ h₁
  set f₂ : O →+* O₂ := i₂.restrict O O₂ fun x hx => (IsValEmbedding.mem_iff O O₂ i₂ h₂ x).mp hx
    with hf₂def
  have hf₂ : IsLocalValHom O O₂ f₂ := isLocalValHom_restrict O O₂ i₂ h₂
  -- Step 2: the ring-theoretic amalgamation.
  obtain ⟨N, hN, O₃, g₁, g₂, hg₁, hg₂, hcomm⟩ := star O O₁ O₂ f₁ f₂ hf₁ hf₂
  letI : Field N := hN
  -- Step 3: pass back to fraction fields (Remark 2.2.2).
  refine ⟨N, hN, O₃, fracLift O₁ O₃ g₁ hg₁.1, fracLift O₂ O₃ g₂ hg₂.1,
    fracLift_isValEmbedding O₁ O₃ g₁ hg₁.1 hg₁.2,
    fracLift_isValEmbedding O₂ O₃ g₂ hg₂.1 hg₂.2, ?_⟩
  -- Step 4: the square commutes, checked on the valuation ring `O` and extended to `F`.
  refine IsFractionRing.ringHom_ext (A := O) fun x => ?_
  have hx₁ : i₁ ((x : O) : F) ∈ O₁ := (IsValEmbedding.mem_iff O O₁ i₁ h₁ _).mp x.2
  have hx₂ : i₂ ((x : O) : F) ∈ O₂ := (IsValEmbedding.mem_iff O O₂ i₂ h₂ _).mp x.2
  have e₁ : fracLift O₁ O₃ g₁ hg₁.1 (i₁ ((x : O) : F)) = (g₁ (f₁ x) : N) :=
    fracLift_apply O₁ O₃ g₁ hg₁.1 (⟨i₁ ((x : O) : F), hx₁⟩ : O₁)
  have e₂ : fracLift O₂ O₃ g₂ hg₂.1 (i₂ ((x : O) : F)) = (g₂ (f₂ x) : N) :=
    fracLift_apply O₂ O₃ g₂ hg₂.1 (⟨i₂ ((x : O) : F), hx₂⟩ : O₂)
  have e₃ : g₁ (f₁ x) = g₂ (f₂ x) := RingHom.congr_fun hcomm x
  show fracLift O₁ O₃ g₁ hg₁.1 (i₁ ((x : O) : F)) =
    fracLift O₂ O₃ g₂ hg₂.1 (i₂ ((x : O) : F))
  rw [e₁, e₃, ← e₂]

end Amalgamation


/-! ### Chevalley's lemma, hom form, and the extension of valuations -/

/-- **Chevalley's Lemma 2.2.1(2)** (hom form). Let `φ : R →+* K` be a ring hom into a field and
let `p` be a prime ideal of `R` containing `ker φ`. Then there is a valuation subring `O` of `K`
containing the image of `φ` such that for all `x : R`, `φ x` lies in the maximal ideal of `O`
iff `x ∈ p`. -/
theorem chevalley_hom {R : Type*} [CommRing R] {K : Type*} [Field K]
    (φ : R →+* K) (p : Ideal R) [p.IsPrime] (hker : RingHom.ker φ ≤ p) :
    ∃ O : ValuationSubring K, φ.range ≤ O.toSubring ∧ ∀ x : R, O.valuation (φ x) < 1 ↔ x ∈ p := by
  classical
  have hker' : RingHom.ker φ.rangeRestrict ≤ p := by
    intro x hx
    apply hker
    have hx' : φ.rangeRestrict x = 0 := hx
    have h2 : (φ.rangeRestrict x : K) = 0 := by rw [hx']; rfl
    rwa [RingHom.coe_rangeRestrict] at h2
  haveI hp' : (Ideal.map φ.rangeRestrict p).IsPrime :=
    Ideal.map_isPrime_of_surjective φ.rangeRestrict_surjective hker'
  obtain ⟨O, hOle, hO⟩ := chevalley_subring φ.range (Ideal.map φ.rangeRestrict p)
  have hcomap : Ideal.comap φ.rangeRestrict (Ideal.map φ.rangeRestrict p) = p := by
    rw [Ideal.comap_map_of_surjective φ.rangeRestrict φ.rangeRestrict_surjective,
      ← RingHom.ker_eq_comap_bot, sup_eq_left.mpr hker']
  refine ⟨O, hOle, fun x => ?_⟩
  rw [show φ x = ((φ.rangeRestrict x : φ.range) : K) from (RingHom.coe_rangeRestrict φ x).symm,
    hO (φ.rangeRestrict x), ← Ideal.mem_comap, hcomap]

/-- **Corollary 2.2.3** (Johnson, §2.2): a valuation on a field extends to any field extension.
This is the content of Chevalley's lemma 2.2.1(1) used by Johnson in §2.2. -/
theorem valExtension_of_fieldExtension {K L : Type u} [Field K] [Field L] [Algebra K L]
    {Γ : Type u} [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) :
    ∃ (Γ' : Type u) (_ : LinearOrderedCommGroupWithZero Γ') (w : Valuation L Γ'), v.HasExtension w := by
  classical
  set O_K := v.valuationSubring with hO_K
  set φ : O_K →+* L := (algebraMap K L).comp O_K.subtype with hφ
  have halg_inj : Function.Injective (algebraMap K L) := by
    intro a b hab
    by_contra hne
    have h1 : algebraMap K L (a - b) = 0 := by rw [map_sub, hab, sub_self]
    have h2 : a - b ≠ 0 := sub_ne_zero.mpr hne
    have h3 : algebraMap K L 1 = 0 := by
      rw [← mul_inv_cancel₀ h2, map_mul, h1, zero_mul]
    rw [map_one] at h3
    exact one_ne_zero h3
  have hker : RingHom.ker φ ≤ maximalIdeal O_K := by
    intro y hy
    rw [RingHom.mem_ker] at hy
    have hy0 : ((y : O_K) : K) = 0 := halg_inj (by simpa [hφ] using hy)
    rw [show y = 0 from Subtype.ext hy0]
    exact (maximalIdeal O_K).zero_mem
  obtain ⟨O, hOle, hO⟩ := chevalley_hom φ (maximalIdeal O_K) hker
  have hle : ∀ y : O_K, (φ y : L) ∈ O := fun y => hOle (RingHom.mem_range_self φ y)
  refine ⟨O.ValueGroup, inferInstance, O.valuation, ?_⟩
  refine Valuation.HasExtension.ofComapInteger (vK := v) (vA := O.valuation) ?_
  rw [ValuationSubring.integer_valuation]
  show Subring.comap (algebraMap K L) O.toSubring = O_K.toSubring
  refine le_antisymm ?_ ?_
  · -- the harder inclusion: `O ∩ K ⊆ O_K`
    intro x hx
    by_contra hxO
    have hxne : x ≠ 0 := by rintro rfl; exact hxO (O_K.zero_mem)
    have hnu : x⁻¹ ∈ O_K.nonunits :=
      (ValuationSubring.inv_mem_nonunits_iff (A := O_K)).mpr (Or.inr hxO)
    have hxinv : x⁻¹ ∈ O_K := ValuationSubring.nonunits_subset hnu
    have hmO : (⟨φ ⟨x⁻¹, hxinv⟩, hle _⟩ : O) ∈ maximalIdeal O := by
      rw [ValuationSubring.valuation_lt_one_iff]
      exact (hO ⟨x⁻¹, hxinv⟩).mpr (ValuationSubring.coe_mem_nonunits_iff.mp hnu)
    have hunit : IsUnit (⟨φ ⟨x⁻¹, hxinv⟩, hle _⟩ : O) := by
      refine IsUnit.of_mul_eq_one (⟨algebraMap K L x, hx⟩ : O) ?_
      apply Subtype.ext
      show (φ ⟨x⁻¹, hxinv⟩ : L) * algebraMap K L x = 1
      have h1 : (φ ⟨x⁻¹, hxinv⟩ : L) = algebraMap K L x⁻¹ := rfl
      rw [h1, ← map_mul, inv_mul_cancel₀ hxne, map_one]
    exact (mem_maximalIdeal_iff_not_isUnit _).mp hmO hunit
  · intro x hx
    exact hle ⟨x, hx⟩


/-- **Chevalley's Lemma 2.2.1(2)** in the form in which Johnson applies it (to the tensor product
`O₁ ⊗_{O₀} O₂`): for a ring `R` and primes `q ⊆ p` there are a field `K`, a valuation subring
`O ⊆ K` and a ring hom `f : R →+* O` with `f⁻¹(0) = q` and `f⁻¹(m_O) = p`, the latter expressed
in the language `L_val` as `v_O (f x) < 1 ↔ x ∈ p`. -/
theorem chevalley_hom' {R : Type u} [CommRing R] (q p : Ideal R) [q.IsPrime] [p.IsPrime]
    (hqp : q ≤ p) :
    ∃ (K : Type u) (_ : Field K) (O : ValuationSubring K) (f : R →+* O),
      (∀ x : R, f x = 0 ↔ x ∈ q) ∧ ∀ x : R, O.valuation (f x : K) < 1 ↔ x ∈ p := by
  classical
  set K : Type u := FractionRing (R ⧸ q) with hK
  let φ : R →+* K := (algebraMap (R ⧸ q) K).comp (Ideal.Quotient.mk q)
  have hker : RingHom.ker φ = q := by
    ext x
    rw [RingHom.mem_ker]
    constructor
    · intro h
      have h' : (Ideal.Quotient.mk q x : R ⧸ q) = 0 :=
        IsFractionRing.injective (R ⧸ q) K (by simpa [φ] using h)
      exact (Ideal.Quotient.eq_zero_iff_mem).mp h'
    · intro h
      have h' : (Ideal.Quotient.mk q x : R ⧸ q) = 0 := (Ideal.Quotient.eq_zero_iff_mem).mpr h
      simp [φ, h']
  have hker' : RingHom.ker φ ≤ p := by rw [hker]; exact hqp
  obtain ⟨O, hOle, hO⟩ := chevalley_hom φ p hker'
  set f : R →+* O := φ.codRestrict O.toSubring (fun x => hOle (RingHom.mem_range_self φ x)) with hf
  refine ⟨K, inferInstance, O, f, ?_, ?_⟩
  · intro x
    have h1 : ((f x : O) : K) = φ x := RingHom.codRestrict_apply _ _ _ x
    constructor
    · intro h
      have h3 : ((f x : O) : K) = 0 := by rw [h]; rfl
      rw [h1] at h3
      have h4 : x ∈ RingHom.ker φ := h3
      rwa [hker] at h4
    · intro h
      have h4 : x ∈ RingHom.ker φ := by rw [hker]; exact h
      have h3 : φ x = 0 := h4
      apply Subtype.ext
      rw [h1, h3]
      rfl
  · intro x
    rw [show ((f x : O) : K) = φ x from RingHom.codRestrict_apply _ _ _ x]
    exact hO x


/-! ### Johnson, Lemma 2.2.4: torsion-free modules over a valuation ring are flat -/

section TorsionFree

/-- A torsion-free module over a valuation ring is flat (Johnson, Lemma 2.2.4.2), using
Mathlib's `Module.Flat.flat_iff_torsion_eq_bot_of_isBezout` and the fact that a valuation ring
is a Bezout domain. -/
theorem flat_of_torsion_eq_bot {R M : Type*} [CommRing R] [IsDomain R] [ValuationRing R]
    [AddCommGroup M] [Module R M] (h : Submodule.torsion R M = ⊥) : Module.Flat R M :=
  Module.Flat.flat_iff_torsion_eq_bot_of_isBezout.mpr h

/-- An algebra over a domain which is a domain and whose structure map is injective is
torsion-free. -/
theorem torsion_eq_bot_of_injective {R S : Type*} [CommRing R] [IsDomain R]
    [CommRing S] [IsDomain S] [Algebra R S] (h : Function.Injective (algebraMap R S)) :
    Submodule.torsion R S = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Submodule.mem_torsion_iff] at hx
  obtain ⟨⟨r, hr⟩, hrx⟩ := hx
  have hr0 : r ≠ 0 := fun h0 => zero_notMem_nonZeroDivisors (h0 ▸ hr)
  have h2 : algebraMap R S r * x = 0 := by simpa [Algebra.smul_def] using hrx
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd (h (by simpa using h3)) hr0
  · exact h3

end TorsionFree

/-! ### Lemma 2.2.6 and the two-prime Chevalley step: `star`

`star` is proved by Johnson's argument (Fun with Fields, §2.2, Lemmas 2.2.4-2.2.7):

* Step 1. `B₁`, `B₂`, `A₁`, `A₂` are flat over `B` (Lemma 2.2.4): they are torsion-free
  (`torsion_eq_bot_of_injective`) and a torsion-free module over a valuation ring is flat
  (`Module.Flat.flat_iff_torsion_eq_bot_of_isBezout`, using `ValuationRing → IsBezout`).
* Step 2. Hence `S = B₁ ⊗_B B₂ ↪ A₁ ⊗_B A₂` (Lemma 2.2.6's input), as a *ring* hom
  `Algebra.TensorProduct.map φ₁ φ₂`, whose injectivity follows from
  `TensorProduct.map_injective_of_flat_flat` on pure tensors.
* Step 3. Lemma 2.2.6: a minimal prime `q` of `S` contracts to `0` in `B₁` and `B₂`.  A prime of
  `A₁ ⊗_B A₂` restricts to `0` in the field `A₁`, and Lemma 2.2.5
  (`Ideal.exists_comap_eq_of_mem_minimalPrimes_of_injective`) lifts `q` to such a prime.
* Step 4. Lemma 2.2.7's prime `p`: `k₁ ⊗_{k₀} k₂` (residue fields) is nontrivial by
  `Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain`, so it has a maximal
  ideal `𝔪`; the pullback of `𝔪` along `B₁ ⊗_B B₂ → k₁ ⊗_{k₀} k₂` is a prime whose contractions to
  `B₁`, `B₂` are the maximal ideals (they contain them, and maximal ideals are maximal).
* Step 5. Take a minimal prime `q ≤ p`, apply Chevalley's Lemma 2.2.1(2) (`chevalley_hom'`) to get
  `m : S → O` with `m⁻¹(0) = q` and `m⁻¹(m_O) = p`; then `gᵢ = m ∘ (Bᵢ → S)` are local injective
  homs into `O`, with `g₁ ∘ f₁ = g₂ ∘ f₂`.

The only ingredient taken from Johnson without reproving it is Lemma 2.2.4.1 (finitely generated
torsion-free modules over a valuation ring are free); its consequence 2.2.4.2 is supplied by
Mathlib's Bezout-domain criterion.  Lemmas 2.2.5 and 2.2.1 (both parts) are also taken from
Mathlib resp. the earlier part of this file. -/

section Star

open scoped TensorProduct

/-- **Amalgamation for valuation rings** (`star`), Johnson, Lemma 2.2.7. -/
theorem star : ∀ {A A₁ A₂ : Type u} [Field A] [Field A₁] [Field A₂]
    (B : ValuationSubring A) (B₁ : ValuationSubring A₁) (B₂ : ValuationSubring A₂)
    (f₁ : B →+* B₁) (f₂ : B →+* B₂),
    IsLocalValHom B B₁ f₁ → IsLocalValHom B B₂ f₂ →
    ∃ (C : Type u) (_ : Field C) (B₃ : ValuationSubring C) (g₁ : B₁ →+* B₃) (g₂ : B₂ →+* B₃),
      IsLocalValHom B₁ B₃ g₁ ∧ IsLocalValHom B₂ B₃ g₂ ∧ g₁.comp f₁ = g₂.comp f₂ := by
  intro A A₁ A₂ _ _ _ B B₁ B₂ f₁ f₂ hf₁ hf₂
  classical
  -- ## Step 0: `B`-algebra structures and consequences of the hypotheses
  letI algBB₁ : Algebra B B₁ := f₁.toAlgebra
  letI algBB₂ : Algebra B B₂ := f₂.toAlgebra
  haveI hloc₁ : IsLocalHom (algebraMap B B₁) := by
    rw [RingHom.algebraMap_toAlgebra]
    exact ((IsLocalRing.local_hom_TFAE f₁).out 4 0 rfl rfl).mp hf₁.2
  haveI hloc₂ : IsLocalHom (algebraMap B B₂) := by
    rw [RingHom.algebraMap_toAlgebra]
    exact ((IsLocalRing.local_hom_TFAE f₂).out 4 0 rfl rfl).mp hf₂.2
  have hinj₁ : Function.Injective (algebraMap B B₁) := by
    rw [RingHom.algebraMap_toAlgebra]; exact hf₁.1
  have hinj₂ : Function.Injective (algebraMap B B₂) := by
    rw [RingHom.algebraMap_toAlgebra]; exact hf₂.1
  letI algBA₁ : Algebra B A₁ := ((algebraMap B₁ A₁).comp f₁).toAlgebra
  letI algBA₂ : Algebra B A₂ := ((algebraMap B₂ A₂).comp f₂).toAlgebra
  haveI htow₁ : IsScalarTower B B₁ A₁ := IsScalarTower.of_algebraMap_eq' rfl
  haveI htow₂ : IsScalarTower B B₂ A₂ := IsScalarTower.of_algebraMap_eq' rfl
  -- ## Step 1: flatness of `B₁`, `B₂`, `A₁`, `A₂` over `B` (Lemma 2.2.4)
  haveI hflat₁ : Module.Flat B B₁ := flat_of_torsion_eq_bot (torsion_eq_bot_of_injective hinj₁)
  haveI hflat₂ : Module.Flat B B₂ := flat_of_torsion_eq_bot (torsion_eq_bot_of_injective hinj₂)
  haveI hfrac₁ : Module.Flat B₁ A₁ := IsLocalization.flat A₁ (nonZeroDivisors B₁)
  haveI hfrac₂ : Module.Flat B₂ A₂ := IsLocalization.flat A₂ (nonZeroDivisors B₂)
  haveI hflatA₁ : Module.Flat B A₁ := Module.Flat.trans B B₁ A₁
  haveI hflatA₂ : Module.Flat B A₂ := Module.Flat.trans B B₂ A₂
  -- ## Step 2: the ring hom `S = B₁ ⊗_B B₂ → D = A₁ ⊗_B A₂` is injective
  set φ₁ : B₁ →ₐ[B] A₁ := IsScalarTower.toAlgHom B B₁ A₁ with hφ₁
  set φ₂ : B₂ →ₐ[B] A₂ := IsScalarTower.toAlgHom B B₂ A₂ with hφ₂
  set F₁ : B₁ →ₗ[B] A₁ := (Algebra.linearMap B₁ A₁).restrictScalars B with hF₁
  set F₂ : B₂ →ₗ[B] A₂ := (Algebra.linearMap B₂ A₂).restrictScalars B with hF₂
  have hF₁inj : Function.Injective F₁ := fun x y h => IsFractionRing.injective B₁ A₁ h
  have hF₂inj : Function.Injective F₂ := fun x y h => IsFractionRing.injective B₂ A₂ h
  have hinjT : Function.Injective
      (Algebra.TensorProduct.map φ₁ φ₂ : B₁ ⊗[B] B₂ →ₐ[B] A₁ ⊗[B] A₂) := by
    have hlin : Function.Injective (TensorProduct.map F₁ F₂ : B₁ ⊗[B] B₂ →ₗ[B] A₁ ⊗[B] A₂) :=
      TensorProduct.map_injective_of_flat_flat F₁ F₂ hF₁inj hF₂inj
    have hcoe : ∀ x : B₁ ⊗[B] B₂,
        (Algebra.TensorProduct.map φ₁ φ₂ : B₁ ⊗[B] B₂ →ₐ[B] A₁ ⊗[B] A₂) x =
          (TensorProduct.map F₁ F₂ : B₁ ⊗[B] B₂ →ₗ[B] A₁ ⊗[B] A₂) x := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp [hF₁, hF₂, hφ₁, hφ₂]
      | add x y hx hy => simp [hx, hy]
    rw [show ⇑(Algebra.TensorProduct.map φ₁ φ₂ : B₁ ⊗[B] B₂ →ₐ[B] A₁ ⊗[B] A₂) =
        ⇑(TensorProduct.map F₁ F₂ : B₁ ⊗[B] B₂ →ₗ[B] A₁ ⊗[B] A₂) from funext hcoe]
    exact hlin

  -- ## Step 3: minimal primes of `S = B₁ ⊗_B B₂` contract to `0` in `B₁` and `B₂` (Lemma 2.2.6)
  set ι : B₁ ⊗[B] B₂ →+* A₁ ⊗[B] A₂ :=
    (Algebra.TensorProduct.map φ₁ φ₂ : B₁ ⊗[B] B₂ →ₐ[B] A₁ ⊗[B] A₂).toRingHom with hι
  set incL : A₁ →+* A₁ ⊗[B] A₂ :=
    (Algebra.TensorProduct.includeLeft (R := B) (S := B) (A := A₁) (B := A₂)).toRingHom with hincL
  set incR : A₂ →+* A₁ ⊗[B] A₂ :=
    (Algebra.TensorProduct.includeRight (R := B) (A := A₁) (B := A₂)).toRingHom with hincR
  set i₁ : B₁ →+* B₁ ⊗[B] B₂ := Algebra.TensorProduct.includeLeftRingHom with hi₁
  set i₂ : B₂ →+* B₁ ⊗[B] B₂ :=
    (Algebra.TensorProduct.includeRight : B₂ →ₐ[B] B₁ ⊗[B] B₂).toRingHom with hi₂
  have hi₁inj : Function.Injective i₁ :=
    Algebra.TensorProduct.includeLeft_injective (R := B) (S := B) (A := B₁) (B := B₂) hinj₂
  have hi₂inj : Function.Injective i₂ :=
    Algebra.TensorProduct.includeRight_injective (R := B) (A := B₁) (B := B₂) hinj₁
  have hιi₁ : ι.comp i₁ = incL.comp (algebraMap B₁ A₁) := by
    ext a
    simp [hι, hi₁, hincL, hφ₁]
  have hιi₂ : ι.comp i₂ = incR.comp (algebraMap B₂ A₂) := by
    ext a
    simp [hι, hi₂, hincR, hφ₂, Algebra.TensorProduct.map_tmul]
  have h226₁ : ∀ q : Ideal (B₁ ⊗[B] B₂), q ∈ minimalPrimes (B₁ ⊗[B] B₂) →
      Ideal.comap i₁ q = ⊥ := by
    intro q hq
    obtain ⟨Q, hQprime, hQcomap⟩ :=
      Ideal.exists_comap_eq_of_mem_minimalPrimes_of_injective (f := ι) hinjT q hq
    haveI hQp : Q.IsPrime := hQprime
    have hQL : Ideal.comap incL Q = ⊥ := by
      rcases Ideal.eq_bot_or_top (Ideal.comap incL Q) with h | h
      · exact h
      · exfalso
        have h2 : (1 : A₁) ∈ Ideal.comap incL Q := h ▸ Submodule.mem_top
        rw [Ideal.mem_comap, map_one] at h2
        exact hQp.ne_top (Ideal.eq_top_iff_one Q |>.mpr h2)
    calc Ideal.comap i₁ q
        = Ideal.comap i₁ (Ideal.comap ι Q) := by rw [hQcomap]
      _ = Ideal.comap (ι.comp i₁) Q := Ideal.comap_comap _ _
      _ = Ideal.comap (incL.comp (algebraMap B₁ A₁)) Q := by rw [hιi₁]
      _ = Ideal.comap (algebraMap B₁ A₁) (Ideal.comap incL Q) := (Ideal.comap_comap _ _).symm
      _ = ⊥ := by rw [hQL]; exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective B₁ A₁)
  have h226₂ : ∀ q : Ideal (B₁ ⊗[B] B₂), q ∈ minimalPrimes (B₁ ⊗[B] B₂) →
      Ideal.comap i₂ q = ⊥ := by
    intro q hq
    obtain ⟨Q, hQprime, hQcomap⟩ :=
      Ideal.exists_comap_eq_of_mem_minimalPrimes_of_injective (f := ι) hinjT q hq
    haveI hQp : Q.IsPrime := hQprime
    have hQR : Ideal.comap incR Q = ⊥ := by
      rcases Ideal.eq_bot_or_top (Ideal.comap incR Q) with h | h
      · exact h
      · exfalso
        have h2 : (1 : A₂) ∈ Ideal.comap incR Q := h ▸ Submodule.mem_top
        rw [Ideal.mem_comap, map_one] at h2
        exact hQp.ne_top (Ideal.eq_top_iff_one Q |>.mpr h2)
    calc Ideal.comap i₂ q
        = Ideal.comap i₂ (Ideal.comap ι Q) := by rw [hQcomap]
      _ = Ideal.comap (ι.comp i₂) Q := Ideal.comap_comap _ _
      _ = Ideal.comap (incR.comp (algebraMap B₂ A₂)) Q := by rw [hιi₂]
      _ = Ideal.comap (algebraMap B₂ A₂) (Ideal.comap incR Q) := (Ideal.comap_comap _ _).symm
      _ = ⊥ := by rw [hQR]; exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective B₂ A₂)
  -- ## Step 4: a prime `p` of `S` whose contractions to `B₁`, `B₂` are the maximal ideals
  let k0 : Type u := IsLocalRing.ResidueField B
  let k1 : Type u := IsLocalRing.ResidueField B₁
  let k2 : Type u := IsLocalRing.ResidueField B₂
  let T : Type u := k1 ⊗[k0] k2
  haveI hTnontriv : Nontrivial T :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain k0 k1 k2
      (RingHom.injective (algebraMap k0 k1)) (RingHom.injective (algebraMap k0 k2))
  let ψ₁ : B₁ →ₐ[B] T :=
    ((Algebra.TensorProduct.includeLeft (R := k0) (S := k0) (A := k1) (B := k2)).restrictScalars B).comp
      (IsScalarTower.toAlgHom B B₁ k1)
  let ψ₂ : B₂ →ₐ[B] T :=
    ((Algebra.TensorProduct.includeRight (R := k0) (A := k1) (B := k2)).restrictScalars B).comp
      (IsScalarTower.toAlgHom B B₂ k2)
  have hψ₁ : ∀ a : B₁, ψ₁ a = (IsLocalRing.residue B₁ a) ⊗ₜ[k0] (1 : k2) := by
    intro a
    show (algebraMap B₁ k1) a ⊗ₜ[k0] (1 : k2) = _
    rw [show (algebraMap B₁ k1 : B₁ →+* k1) = IsLocalRing.residue B₁ from
      IsLocalRing.ResidueField.algebraMap_eq B₁]
  have hψ₂ : ∀ a : B₂, ψ₂ a = (1 : k1) ⊗ₜ[k0] (IsLocalRing.residue B₂ a) := by
    intro a
    show (1 : k1) ⊗ₜ[k0] (algebraMap B₂ k2) a = _
    rw [show (algebraMap B₂ k2 : B₂ →+* k2) = IsLocalRing.residue B₂ from
      IsLocalRing.ResidueField.algebraMap_eq B₂]
  let φ : B₁ ⊗[B] B₂ →ₐ[B] T := Algebra.TensorProduct.lift ψ₁ ψ₂ (fun x y => Commute.all _ _)
  have hφ₁ : ∀ a : B₁, φ (a ⊗ₜ[B] (1 : B₂)) = ψ₁ a := by
    intro a; simp [φ, Algebra.TensorProduct.lift_tmul]
  have hφ₂ : ∀ a : B₂, φ ((1 : B₁) ⊗ₜ[B] a) = ψ₂ a := by
    intro a; simp [φ, Algebra.TensorProduct.lift_tmul]
  obtain ⟨𝔪, h𝔪max⟩ := Ideal.exists_maximal T
  haveI h𝔪prime : 𝔪.IsPrime := h𝔪max.isPrime
  haveI hpprime : (Ideal.comap φ.toRingHom 𝔪).IsPrime := Ideal.comap_isPrime _ _
  have hle₁ : IsLocalRing.maximalIdeal B₁ ≤ Ideal.comap i₁ (Ideal.comap φ.toRingHom 𝔪) := by
    intro a ha
    rw [Ideal.mem_comap, Ideal.mem_comap]
    have h0 : IsLocalRing.residue B₁ a = 0 := (IsLocalRing.residue_eq_zero_iff a).mpr ha
    have h1 : i₁ a = a ⊗ₜ[B] (1 : B₂) := Algebra.TensorProduct.includeLeftRingHom_apply a
    rw [h1, show φ.toRingHom (a ⊗ₜ[B] (1 : B₂)) = ψ₁ a from hφ₁ a, hψ₁, h0,
      TensorProduct.zero_tmul]
    exact 𝔪.zero_mem
  have hpne₁ : Ideal.comap i₁ (Ideal.comap φ.toRingHom 𝔪) ≠ ⊤ := by
    intro h
    have h2 : (1 : B₁) ∈ Ideal.comap i₁ (Ideal.comap φ.toRingHom 𝔪) :=
      h ▸ Submodule.mem_top
    have h1 : (1 : B₁ ⊗[B] B₂) ∈ Ideal.comap φ.toRingHom 𝔪 := by simpa using h2
    exact hpprime.ne_top (Ideal.eq_top_iff_one _ |>.mpr h1)
  have hp₁ : Ideal.comap i₁ (Ideal.comap φ.toRingHom 𝔪) = IsLocalRing.maximalIdeal B₁ :=
    ((IsLocalRing.maximalIdeal.isMaximal B₁).eq_of_le hpne₁ hle₁).symm
  have hle₂ : IsLocalRing.maximalIdeal B₂ ≤ Ideal.comap i₂ (Ideal.comap φ.toRingHom 𝔪) := by
    intro a ha
    rw [Ideal.mem_comap, Ideal.mem_comap]
    have h0 : IsLocalRing.residue B₂ a = 0 := (IsLocalRing.residue_eq_zero_iff a).mpr ha
    have h1 : i₂ a = (1 : B₁) ⊗ₜ[B] a := Algebra.TensorProduct.includeRight_apply a
    rw [h1, show φ.toRingHom ((1 : B₁) ⊗ₜ[B] a) = ψ₂ a from hφ₂ a, hψ₂, h0,
      TensorProduct.tmul_zero]
    exact 𝔪.zero_mem
  have hpne₂ : Ideal.comap i₂ (Ideal.comap φ.toRingHom 𝔪) ≠ ⊤ := by
    intro h
    have h2 : (1 : B₂) ∈ Ideal.comap i₂ (Ideal.comap φ.toRingHom 𝔪) :=
      h ▸ Submodule.mem_top
    have h1 : (1 : B₁ ⊗[B] B₂) ∈ Ideal.comap φ.toRingHom 𝔪 := by simpa using h2
    exact hpprime.ne_top (Ideal.eq_top_iff_one _ |>.mpr h1)
  have hp₂ : Ideal.comap i₂ (Ideal.comap φ.toRingHom 𝔪) = IsLocalRing.maximalIdeal B₂ :=
    ((IsLocalRing.maximalIdeal.isMaximal B₂).eq_of_le hpne₂ hle₂).symm
  -- ## Step 5: Chevalley's Lemma 2.2.1(2) and the amalgam
  obtain ⟨q, hqmin, hqle⟩ :=
    Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal (B₁ ⊗[B] B₂)))
      (J := Ideal.comap φ.toRingHom 𝔪) bot_le
  have hq₁ : Ideal.comap i₁ q = ⊥ := h226₁ q hqmin
  have hq₂ : Ideal.comap i₂ q = ⊥ := h226₂ q hqmin
  haveI hqprime : q.IsPrime := hqmin.isPrime
  obtain ⟨K, hK, O, m, hm0, hmm⟩ := chevalley_hom' q (Ideal.comap φ.toRingHom 𝔪) hqle
  letI : Field K := hK
  have hker₁ : Function.Injective (m.comp i₁) := by
    intro x y hxy
    have h2 : i₁ (x - y) ∈ q := by
      rw [← hm0]
      show m (i₁ (x - y)) = 0
      simp only [map_sub]
      rw [show m (i₁ x) = m (i₁ y) from hxy, sub_self]
    rw [← Ideal.mem_comap, hq₁, Ideal.mem_bot] at h2
    exact sub_eq_zero.mp h2
  have hker₂ : Function.Injective (m.comp i₂) := by
    intro x y hxy
    have h2 : i₂ (x - y) ∈ q := by
      rw [← hm0]
      show m (i₂ (x - y)) = 0
      simp only [map_sub]
      rw [show m (i₂ x) = m (i₂ y) from hxy, sub_self]
    rw [← Ideal.mem_comap, hq₂, Ideal.mem_bot] at h2
    exact sub_eq_zero.mp h2
  have hmax₁ : Ideal.comap (m.comp i₁) (IsLocalRing.maximalIdeal O) = IsLocalRing.maximalIdeal B₁ := by
    ext x
    rw [Ideal.mem_comap]
    have h1 : (m.comp i₁) x ∈ IsLocalRing.maximalIdeal O ↔ O.valuation ((m.comp i₁) x) < 1 :=
      ValuationSubring.valuation_lt_one_iff O _
    have h2 : O.valuation ((m.comp i₁) x) < 1 ↔ i₁ x ∈ Ideal.comap φ.toRingHom 𝔪 := hmm (i₁ x)
    have h3 : i₁ x ∈ Ideal.comap φ.toRingHom 𝔪 ↔ x ∈ Ideal.comap i₁ (Ideal.comap φ.toRingHom 𝔪) :=
      Ideal.mem_comap
    have h4 : x ∈ Ideal.comap i₁ (Ideal.comap φ.toRingHom 𝔪) ↔ x ∈ IsLocalRing.maximalIdeal B₁ := by
      rw [hp₁]
    exact h1.trans (h2.trans (h3.trans h4))
  have hmax₂ : Ideal.comap (m.comp i₂) (IsLocalRing.maximalIdeal O) = IsLocalRing.maximalIdeal B₂ := by
    ext x
    rw [Ideal.mem_comap]
    have h1 : (m.comp i₂) x ∈ IsLocalRing.maximalIdeal O ↔ O.valuation ((m.comp i₂) x) < 1 :=
      ValuationSubring.valuation_lt_one_iff O _
    have h2 : O.valuation ((m.comp i₂) x) < 1 ↔ i₂ x ∈ Ideal.comap φ.toRingHom 𝔪 := hmm (i₂ x)
    have h3 : i₂ x ∈ Ideal.comap φ.toRingHom 𝔪 ↔ x ∈ Ideal.comap i₂ (Ideal.comap φ.toRingHom 𝔪) :=
      Ideal.mem_comap
    have h4 : x ∈ Ideal.comap i₂ (Ideal.comap φ.toRingHom 𝔪) ↔ x ∈ IsLocalRing.maximalIdeal B₂ := by
      rw [hp₂]
    exact h1.trans (h2.trans (h3.trans h4))
  refine ⟨K, hK, O, m.comp i₁, m.comp i₂, ⟨hker₁, hmax₁⟩, ⟨hker₂, hmax₂⟩, ?_⟩
  ext b
  have h2S : (algebraMap B (B₁ ⊗[B] B₂)) b = b • ((1:B₁) ⊗ₜ[B] (1:B₂)) := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.TensorProduct.one_def]
  have e1 : i₁ (f₁ b) = (algebraMap B (B₁ ⊗[B] B₂)) b := by
    have h1 : i₁ (f₁ b) = (b • (1:B₁)) ⊗ₜ[B] (1:B₂) := by
      rw [hi₁, Algebra.TensorProduct.includeLeftRingHom_apply, ← RingHom.algebraMap_toAlgebra f₁,
        Algebra.algebraMap_eq_smul_one (R := B) (A := B₁)]
    rw [h1, h2S, TensorProduct.smul_tmul, TensorProduct.tmul_smul]
  have e2 : i₂ (f₂ b) = (algebraMap B (B₁ ⊗[B] B₂)) b := by
    have h1 : i₂ (f₂ b) = (1:B₁) ⊗ₜ[B] (b • (1:B₂)) := by
      rw [hi₂, ← RingHom.algebraMap_toAlgebra f₂, Algebra.algebraMap_eq_smul_one (R := B) (A := B₂)]
      show (Algebra.TensorProduct.includeRight (R := B) (A := B₁) (B := B₂) (b • (1:B₂)))
        = (1:B₁) ⊗ₜ[B] (b • (1:B₂))
      rw [Algebra.TensorProduct.includeRight_apply]
    rw [h1, h2S, TensorProduct.tmul_smul]
  simp only [RingHom.comp_apply, e1, e2]

end Star

end Johnson22

#print axioms Johnson22.chevalley_subring
#print axioms Johnson22.chevalley_hom
#print axioms Johnson22.chevalley_hom'
#print axioms Johnson22.valuedEmbedding_of_localHom
#print axioms Johnson22.flat_of_torsion_eq_bot
#print axioms Johnson22.torsion_eq_bot_of_injective
#print axioms Johnson22.star
#check Johnson22.amalgamation_of_ring_amalgamation Johnson22.star
#check Johnson22.star

section EndToEnd
universe u

/-- End-to-end check: `star` has the exact shape that `amalgamation_of_ring_amalgamation` consumes,
and the amalgamation property for valued fields follows from it at universe `Type u`. -/
example {F F₁ F₂ : Type u} [Field F] [Field F₁] [Field F₂]
    (O : ValuationSubring F) (O₁ : ValuationSubring F₁) (O₂ : ValuationSubring F₂)
    (i₁ : F →+* F₁) (i₂ : F →+* F₂)
    (h₁ : Johnson22.IsValEmbedding O.valuation O₁.valuation i₁)
    (h₂ : Johnson22.IsValEmbedding O.valuation O₂.valuation i₂) :
    ∃ (N : Type u) (_ : Field N) (O₃ : ValuationSubring N) (j₁ : F₁ →+* N) (j₂ : F₂ →+* N),
      Johnson22.IsValEmbedding O₁.valuation O₃.valuation j₁ ∧
      Johnson22.IsValEmbedding O₂.valuation O₃.valuation j₂ ∧ j₁.comp i₁ = j₂.comp i₂ :=
  Johnson22.amalgamation_of_ring_amalgamation Johnson22.star O O₁ O₂ i₁ i₂ h₁ h₂

end EndToEnd

#print axioms Johnson22.isValEmbedding_of_mem_iff
#print axioms Johnson22.amalgamation_of_ring_amalgamation
#print axioms Johnson22.valExtension_of_fieldExtension

/-! ## 18. `HasAmalgamation valField` -/

namespace ValOneEC

section ValSubring

/-- The order of a valuation is the order of its valuation subring's canonical valuation.  This is
what lets Johnson's §2.2 amalgamation theorem, which is stated for `ValuationSubring`s, be applied
to the valuations `exists_valuation_of_isValPred` produces. -/
theorem le_iff_valuationSubring_valuation_le {K : Type} [Field K] {Γ : Type}
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) (x y : K) :
    v x ≤ v y ↔ v.valuationSubring.valuation x ≤ v.valuationSubring.valuation y := by
  rw [ValuationSubring.valuation_le_iff]
  constructor
  · intro h
    by_cases hy : y = 0
    · subst hy
      rw [map_zero] at h
      have hx : x = 0 := v.zero_iff.mp (le_antisymm h zero_le)
      subst hx
      exact ⟨0, by simp⟩
    · refine ⟨⟨x * y⁻¹, ?_⟩, by field_simp⟩
      rw [Valuation.mem_valuationSubring_iff, map_mul, map_inv₀]
      calc v x * (v y)⁻¹ ≤ v y * (v y)⁻¹ := by
            exact mul_le_mul_left h _
        _ = 1 := by rw [mul_inv_cancel₀ (v.ne_zero_iff.mpr hy)]
  · rintro ⟨a, ha⟩
    have hx : v x = v (a : K) * v y := by
      rw [← ha, map_mul]
    rw [hx]
    calc v (a : K) * v y ≤ 1 * v y := by
          exact mul_le_mul_left a.2 _
      _ = v y := one_mul _

/-- An `L_val`-embedding between `valStructure`s is a Johnson valued embedding of `ValuationSubring`s. -/
theorem isValEmbedding_of_valEmb {K : Type} [Field K] {K' : Type} [Field K'] {Γ : Type}
    [LinearOrderedCommGroupWithZero Γ] {Γ' : Type} [LinearOrderedCommGroupWithZero Γ']
    {v : Valuation K Γ} {w : Valuation K' Γ'}
    (F : @Embedding Language.val K K' (FirstOrder.valStructure v) (FirstOrder.valStructure w)) :
    Johnson22.IsValEmbedding v w (ringHomOfEmbedding v w F) := by
  letI := FirstOrder.valStructure v
  letI := FirstOrder.valStructure w
  refine ⟨fun x y h => F.inj' h, fun x y => ?_⟩
  have h := F.map_rel' ValRel.le ![x, y]
  have h' : (F.toFun ∘ ![x, y]) = ![F.toFun x, F.toFun y] := by
    funext i
    fin_cases i <;> rfl
  rw [h'] at h
  exact h.symm

end ValSubring

end ValOneEC

/-! ## 19. `HasAmalgamation valField` -/

namespace ValOneEC

section Amalgamation

open FirstOrder FirstOrder.Language FirstOrder.Ring

/-- Copy of `JohnsonCriterion.HasAmalgamation` (`QE/ACF_HasQE.lean`) specialised to `L_val`. -/
def HasAmalgamation (T : Language.val.Theory) : Prop :=
  ∀ (A B C : T.ModelType.{0, 0, 0}) (i : A ↪[Language.val] B) (j : A ↪[Language.val] C),
    ∃ (D : T.ModelType.{0, 0, 0}) (i' : B ↪[Language.val] D) (j' : C ↪[Language.val] D),
      i'.comp i = j'.comp j

/-- A Johnson valued embedding of valuations is one of their valuation subrings. -/
theorem isValEmbedding_subring {K : Type} [Field K] {K' : Type} [Field K'] {Γ : Type}
    [LinearOrderedCommGroupWithZero Γ] {Γ' : Type} [LinearOrderedCommGroupWithZero Γ']
    {v : Valuation K Γ} {w : Valuation K' Γ'} {f : K →+* K'}
    (h : Johnson22.IsValEmbedding v w f) :
    Johnson22.IsValEmbedding v.valuationSubring.valuation w.valuationSubring.valuation f := by
  refine ⟨h.1, fun x y => ?_⟩
  rw [← le_iff_valuationSubring_valuation_le v x y,
    ← le_iff_valuationSubring_valuation_le w (f x) (f y)]
  exact h.2 x y

/-- A model of `valField`, together with a valuation realising its predicate, has its own structure
equal to the `valStructure` of the valuation subring's canonical valuation. -/
theorem valStruct_eq_of_valuationSubring (M : ValPM.valField.ModelType.{0, 0, 0}) [Field M]
    [CompatibleRing M] [valRingHom.IsExpansionOn M] {Γ : Type}
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation M Γ)
    (hv : ∀ x y, (ValPM.predM : M → M → Prop) x y ↔ v x ≤ v y) :
    M.struc = FirstOrder.valStructure v.valuationSubring.valuation :=
  (ValPM.valStruct_ext M).trans
    (ValPM.valStructOf_eq_valStructure (p := (ValPM.predM : M → M → Prop))
      (v := v.valuationSubring.valuation) (fun x y =>
        (hv x y).trans (le_iff_valuationSubring_valuation_le v x y)))

/-- **The amalgamation property for `valField`**, from Johnson's §2.2 theorem for valuation
rings.  Each model of `valField` is a Mathlib valued field, its own `L_val`-structure is the
`valStructure` of the valuation subring's canonical valuation, and
`amalgamation_of_ring_amalgamation` then produces the amalgam, which is packaged as a model of
`valField` again through `valStructure_model`. -/
theorem hasAmalgamation_valField : HasAmalgamation ValPM.valField := by
  intro A B C i j
  -- field structures on `A`
  letI : Language.ring.Structure A := ValPM.ringStructOfVal A
  haveI hexpA : valRingHom.IsExpansionOn A := ValPM.ringStructOfVal.expansion A
  have hfieldA : A ⊨ Theory.field := ValPM.model_field_of_valField A A.is_model
  letI : Field A := FirstOrder.Field.fieldOfModelField A
  letI : CompatibleRing A := FirstOrder.Field.compatibleRingOfModelField A
  have hpredA : ValPM.IsValPred (ValPM.predM : A → A → Prop) := ValPM.isValPred_of_model A.is_model
  letI : Language.ring.Structure B := ValPM.ringStructOfVal B
  haveI hexpB : valRingHom.IsExpansionOn B := ValPM.ringStructOfVal.expansion B
  have hfieldB : B ⊨ Theory.field := ValPM.model_field_of_valField B B.is_model
  letI : Field B := FirstOrder.Field.fieldOfModelField B
  letI : CompatibleRing B := FirstOrder.Field.compatibleRingOfModelField B
  have hpredB : ValPM.IsValPred (ValPM.predM : B → B → Prop) := ValPM.isValPred_of_model B.is_model
  letI : Language.ring.Structure C := ValPM.ringStructOfVal C
  haveI hexpC : valRingHom.IsExpansionOn C := ValPM.ringStructOfVal.expansion C
  have hfieldC : C ⊨ Theory.field := ValPM.model_field_of_valField C C.is_model
  letI : Field C := FirstOrder.Field.fieldOfModelField C
  letI : CompatibleRing C := FirstOrder.Field.compatibleRingOfModelField C
  have hpredC : ValPM.IsValPred (ValPM.predM : C → C → Prop) := ValPM.isValPred_of_model C.is_model
  -- valuations
  obtain ⟨ΓA, hΓA, vA, hvA⟩ := ValPM.exists_valuation_of_isValPred hpredA
  letI := hΓA
  obtain ⟨ΓB, hΓB, vB, hvB⟩ := ValPM.exists_valuation_of_isValPred hpredB
  letI := hΓB
  obtain ⟨ΓC, hΓC, vC, hvC⟩ := ValPM.exists_valuation_of_isValPred hpredC
  letI := hΓC
  -- the structures realised by the valuation subrings
  have hAs : A.struc = FirstOrder.valStructure vA.valuationSubring.valuation :=
    valStruct_eq_of_valuationSubring A vA hvA
  have hBs : B.struc = FirstOrder.valStructure vB.valuationSubring.valuation :=
    valStruct_eq_of_valuationSubring B vB hvB
  have hCs : C.struc = FirstOrder.valStructure vC.valuationSubring.valuation :=
    valStruct_eq_of_valuationSubring C vC hvC
  -- the two embeddings, transported
  let FAB : @Embedding Language.val A B (FirstOrder.valStructure vA) (FirstOrder.valStructure vB) :=
    embeddingCast ((ValPM.valStruct_ext A).trans
      (ValPM.valStructOf_eq_valStructure (p := (ValPM.predM : A → A → Prop)) (v := vA) hvA))
      ((ValPM.valStruct_ext B).trans
      (ValPM.valStructOf_eq_valStructure (p := (ValPM.predM : B → B → Prop)) (v := vB) hvB)) i
  let FAC : @Embedding Language.val A C (FirstOrder.valStructure vA) (FirstOrder.valStructure vC) :=
    embeddingCast ((ValPM.valStruct_ext A).trans
      (ValPM.valStructOf_eq_valStructure (p := (ValPM.predM : A → A → Prop)) (v := vA) hvA))
      ((ValPM.valStruct_ext C).trans
      (ValPM.valStructOf_eq_valStructure (p := (ValPM.predM : C → C → Prop)) (v := vC) hvC)) j
  -- the amalgam
  obtain ⟨N, hN, O₃, j₁, j₂, hj₁, hj₂, hcomm⟩ :=
    Johnson22.amalgamation_of_ring_amalgamation Johnson22.star
      vA.valuationSubring vB.valuationSubring vC.valuationSubring
      (ringHomOfEmbedding vA vB FAB) (ringHomOfEmbedding vA vC FAC)
      (isValEmbedding_subring (isValEmbedding_of_valEmb FAB))
      (isValEmbedding_subring (isValEmbedding_of_valEmb FAC))
  letI : Field N := hN
  letI : Language.val.Structure N := FirstOrder.valStructure O₃.valuation
  haveI : N ⊨ ValPM.valField := ValPM.valStructure_model O₃.valuation
  -- the amalgam as a model of `valField`, with its structure and the two embeddings
  let D : ValPM.valField.ModelType.{0, 0, 0} := Theory.ModelType.of (T := ValPM.valField) N
  have hDs : (D.struc : Language.val.Structure N) = FirstOrder.valStructure O₃.valuation := rfl
  let innerB : @Embedding Language.val B N (FirstOrder.valStructure vB.valuationSubring.valuation)
      (FirstOrder.valStructure O₃.valuation) :=
    embeddingOfIsValEmb vB.valuationSubring.valuation O₃.valuation j₁ hj₁.1 hj₁.2
  let innerC : @Embedding Language.val C N (FirstOrder.valStructure vC.valuationSubring.valuation)
      (FirstOrder.valStructure O₃.valuation) :=
    embeddingOfIsValEmb vC.valuationSubring.valuation O₃.valuation j₂ hj₂.1 hj₂.2
  refine ⟨D, ?_, ?_, ?_⟩
  · exact embeddingCast hBs.symm hDs.symm innerB
  · exact embeddingCast hCs.symm hDs.symm innerC
  · -- the square commutes, because all the casts preserve the underlying function
    refine FirstOrder.Language.Embedding.ext ?_
    intro a
    have h := RingHom.congr_fun hcomm a
    exact h

end Amalgamation

end ValOneEC

#print axioms ValOneEC.hasAmalgamation_valField
#print axioms ValOneEC.isValEmbedding_subring
#print axioms ValOneEC.valStruct_eq_of_valuationSubring
#check @ValOneEC.hasAmalgamation_valField
#check @ValOneEC.oneECIn_of_modelType
#check @ValPM.hasPrimeModels_ACVF_val

/-! ## 20. Johnson's criterion (from `QE/ACF_HasQE.lean`) -/

set_option maxHeartbeats 1000000

open FirstOrder FirstOrder.Language
open scoped FirstOrder

set_option linter.style.haveILetI false

namespace JohnsonCriterion

universe u v w w'

variable {L : FirstOrder.Language.{u, v}}

/-! ## 1. Quantifier-free formulas are preserved and reflected by embeddings

Mathlib has `StrongHomClass.realize_boundedFormula`, but only for `EquivLike` maps (surjective
ones).  For a general embedding only quantifier-free formulas are preserved, and that lemma is
not in Mathlib.  (The same lemma is `embedding_realize_isQF` in
`QE/Semantics_saturation.lean`; it is restated here so that the file is self-contained.) -/

section QFPreserve

variable {M : Type w} {N : Type w'} [L.Structure M] [L.Structure N]

theorem embedding_realize_isAtomic (g : M ↪[L] N) {α : Type*} {n : ℕ}
    {φ : L.BoundedFormula α n} (h : φ.IsAtomic) (v : α → M) (xs : Fin n → M) :
    φ.Realize (fun a => g (v a)) (fun i => g (xs i)) ↔ φ.Realize v xs := by
  have hcomp : (Sum.elim (fun a => g (v a)) (fun i => g (xs i)))
      = (fun s => g (Sum.elim v xs s)) := by
    funext s; cases s <;> rfl
  have key : ∀ t : L.Term (α ⊕ Fin n),
      t.realize (Sum.elim (fun a => g (v a)) (fun i => g (xs i)))
        = g (t.realize (Sum.elim v xs)) := by
    intro t; rw [hcomp]; exact HomClass.realize_term g
  cases h with
  | equal t₁ t₂ =>
    simp only [BoundedFormula.realize_bdEqual]
    rw [key t₁, key t₂, g.injective.eq_iff]
  | rel R ts =>
    simp only [BoundedFormula.realize_rel]
    have hrs : (fun i => (ts i).realize (Sum.elim (fun a => g (v a)) (fun i => g (xs i))))
        = (fun i => g ((ts i).realize (Sum.elim v xs))) := by
      funext i; exact key (ts i)
    rw [hrs]
    exact StrongHomClass.map_rel (r := R) g (fun i => (ts i).realize (Sum.elim v xs))

theorem embedding_realize_isQF (g : M ↪[L] N) {α : Type*} {n : ℕ}
    {φ : L.BoundedFormula α n} (h : φ.IsQF) :
    ∀ (v : α → M) (xs : Fin n → M),
      φ.Realize (fun a => g (v a)) (fun i => g (xs i)) ↔ φ.Realize v xs := by
  induction h with
  | falsum => intro v xs; exact Iff.rfl
  | of_isAtomic ha => exact fun v xs => embedding_realize_isAtomic g ha v xs
  | imp _ _ ih1 ih2 => intro v xs; simp only [BoundedFormula.realize_imp, ih1 v xs, ih2 v xs]

end QFPreserve

/-! ## 2. Substituting parameters for terms preserves quantifier-freeness

Needed to move a formula's parameters along an embedding: `OneECIn` is stated for parameters in
the model, while the comparison below happens over a smaller base `S`. -/

section Subst

theorem isAtomic_subst {α β : Type*} {n : ℕ} {φ : L.BoundedFormula α n} (h : φ.IsAtomic)
    (tf : α → L.Term β) : (φ.subst tf).IsAtomic := by
  cases h with
  | equal t₁ t₂ => exact BoundedFormula.IsAtomic.equal _ _
  | rel R ts => exact BoundedFormula.IsAtomic.rel _ _

theorem isQF_subst {α β : Type*} {n : ℕ} {φ : L.BoundedFormula α n} (h : φ.IsQF)
    (tf : α → L.Term β) : (φ.subst tf).IsQF := by
  induction h with
  | falsum => exact BoundedFormula.isQF_bot
  | of_isAtomic ha => exact BoundedFormula.IsAtomic.isQF (isAtomic_subst ha tf)
  | imp _ _ ih1 ih2 => exact ih1.imp ih2

end Subst

/-! ## 3. The three hypotheses of Lemma 2.1.4

All three are stated for models of `T₀` bundled as `T₀.ModelType`; the models of `T` are
carried along by an explicit hypothesis `⊨ T`, which is legitimate because `T₀ ⊆ T` in every
application (models of `T` are models of `T₀`, so no generality is lost and no coercion
between bundled models of different theories is ever needed). -/

section Criterion

/-- **1-ec** (Johnson, Definition 2.1.3): `S` is 1-ec in `N` along the embedding `i` if every
non-empty quantifier-free `S`-definable subset of `N` in one variable meets `S`. -/
def OneECIn {S : Type w} {N : Type w'} [L.Structure S] [L.Structure N] (i : S ↪[L] N) : Prop :=
  ∀ (φ : L.BoundedFormula S 1), φ.IsQF →
    (∃ a, φ.Realize (fun s => i s) (fun _ => a)) →
      ∃ s : S, φ.Realize (fun s' => i s') (fun _ => i s)

/-- **Prime models over substructures** (Johnson, Definition 2.1.1), in the restricted form in
which the definition is used in the proof: every structure `S` that embeds into a model of `T`
has an extension `S'` modelling `T₀` which embeds into every model of `T₀` under `S`.  (In
Johnson's definition the last quantifier runs over all models of `T₀`; here only over models
that are themselves models of `T`, which is all the proof needs.) -/
def HasPrimeModels (T₀ T : L.Theory) : Prop :=
  ∀ (S : Type w) [L.Structure S],
    (∃ (M : T₀.ModelType.{u, v, w}), M ⊨ T ∧ Nonempty (S ↪[L] M)) →
    ∃ (S' : T₀.ModelType.{u, v, w}) (e : S ↪[L] S'),
      ∀ (N : T₀.ModelType.{u, v, w}) (f : S ↪[L] N), ∃ g : S' ↪[L] N, g.comp e = f

/-- **The amalgamation property** (Johnson, Definition 2.1.2). -/
def HasAmalgamation (T : L.Theory) : Prop :=
  ∀ (A B C : T.ModelType.{u, v, w}) (i : A ↪[L] B) (j : A ↪[L] C),
    ∃ (D : T.ModelType.{u, v, w}) (i' : B ↪[L] D) (j' : C ↪[L] D), i'.comp i = j'.comp j

/-- The **conclusion of Lemma 2.1.4**, in the semantic form which the proof establishes:
quantifier-free definable sets over a base have, in any two models of `T`, the same
one-variable existential theory. -/
theorem qfDetermined {T₀ T : L.Theory} (hsub : T₀ ⊆ T)
    (hprime : HasPrimeModels.{u, v, w} T₀ T) (hamal : HasAmalgamation.{u, v, w} T₀)
    (h1ec : ∀ (M N : T₀.ModelType.{u, v, w}) (f : M ↪[L] N), M ⊨ T → OneECIn f)
    (S : Type w) [L.Structure S] (M N : T₀.ModelType.{u, v, w}) (hM : M ⊨ T) (hN : N ⊨ T)
    (i : S ↪[L] M) (j : S ↪[L] N) (φ : L.BoundedFormula S 1) (hφ : φ.IsQF) :
    (∃ a : M, φ.Realize (fun s => i s) (fun _ => a)) ↔
      ∃ b : N, φ.Realize (fun s => j s) (fun _ => b) := by
  -- the prime model of `T₀` over the base `S`
  obtain ⟨S', e, huniv⟩ := hprime S ⟨M, hM, ⟨i⟩⟩
  obtain ⟨gM, hgM⟩ := huniv M i
  obtain ⟨gN, hgN⟩ := huniv N j
  -- amalgamate the two embeddings of `S'` into `M` and `N`
  obtain ⟨D, kM, kN, hcomm⟩ := hamal S' M N gM gN
  -- the formula `φ`, with its parameters moved along the embedding of `S'` into `N`
  set ψ : L.BoundedFormula N 1 := φ.subst (fun s => Term.var (gN.comp e s)) with hψdef
  have hψqf : ψ.IsQF := isQF_subst hφ _
  have hMN : ∀ s, kN ((gN.comp e) s) = kM ((gM.comp e) s) := by
    intro s
    have h := congrArg (fun g : ↑S' ↪[L] ↑D => g (e s)) hcomm
    simpa only [FirstOrder.Language.Embedding.comp_apply] using h.symm
  have hMi : ∀ s, (gM.comp e) s = i s := by
    intro s
    exact congrArg (fun g : S ↪[L] ↑M => g s) hgM
  have hψreal : ∀ a : M, ψ.Realize (fun n => kN n) (fun _ => kM a) ↔
      φ.Realize (fun s => i s) (fun _ => a) := by
    intro a
    rw [hψdef, BoundedFormula.realize_subst]
    simp only [Term.realize_var]
    have hfun : (fun s => kN ((gN.comp e) s)) = (fun s => kM (i s)) := by
      funext s
      rw [hMN s, hMi s]
    rw [hfun]
    exact embedding_realize_isQF kM hφ (fun s => i s) (fun _ => a)
  have hψunfold : ∀ a : N, ψ.Realize (fun n => kN n) (fun _ => kN a) ↔
      φ.Realize (fun s => kN ((gN.comp e) s)) (fun _ => kN a) := by
    intro a
    rw [hψdef, BoundedFormula.realize_subst]
    simp only [Term.realize_var]
  constructor
  · rintro ⟨a, ha⟩
    -- transport the witness to `D`, then use that `N` is 1-ec in `D`
    have hD : ψ.Realize (fun n => kN n) (fun _ => kM a) := (hψreal a).2 ha
    obtain ⟨n₀, hn₀⟩ := h1ec N D kN hN ψ hψqf ⟨kM a, hD⟩
    have h1 : φ.Realize (fun s => kN ((gN.comp e) s)) (fun _ => kN n₀) := (hψunfold n₀).1 hn₀
    have h2 : φ.Realize (fun s => (gN.comp e) s) (fun _ => n₀) :=
      (embedding_realize_isQF kN hφ (fun s => (gN.comp e) s) (fun _ => n₀)).1 h1
    exact ⟨n₀, by rwa [hgN] at h2⟩
  · rintro ⟨b, hb⟩
    -- transport the witness to `D`, now with the parameters written via `M`
    have hb' : φ.Realize (fun s => (gN.comp e) s) (fun _ => b) := by
      rwa [← hgN] at hb
    have hD : φ.Realize (fun s => kN ((gN.comp e) s)) (fun _ => kN b) :=
      (embedding_realize_isQF kN hφ (fun s => (gN.comp e) s) (fun _ => b)).2 hb'
    have hfun : (fun s => kM (i s)) = (fun s => kN ((gN.comp e) s)) := by
      funext s; rw [hMN s, hMi s]
    set χ : L.BoundedFormula M 1 := φ.subst (fun s => Term.var (i s)) with hχdef
    have hχqf : χ.IsQF := isQF_subst hφ _
    have hD' : χ.Realize (fun m => kM m) (fun _ => kN b) := by
      rw [hχdef, BoundedFormula.realize_subst]
      simp only [Term.realize_var]
      rw [hfun]
      exact hD
    -- `M` is a model of `T`, hence 1-ec in every model of `T₀`, in particular in `D`
    obtain ⟨m₀, hm₀⟩ := h1ec M D kM hM χ hχqf ⟨kN b, hD'⟩
    refine ⟨m₀, ?_⟩
    rw [hχdef, BoundedFormula.realize_subst] at hm₀
    simp only [Term.realize_var] at hm₀
    exact (embedding_realize_isQF kM hφ (fun s => i s) (fun _ => m₀)).1 hm₀

end Criterion

end JohnsonCriterion

#print axioms JohnsonCriterion.qfDetermined
#print axioms JohnsonCriterion.embedding_realize_isQF

/-!
## Part 2 — the last mile: from `qfDetermined` to the hypothesis `H`

`JohnsonCriterion.qfDetermined` (Part 1) is the semantic statement: over a structure `S` embedded
in two models `M`, `N` of `T` (with `T₀ ⊆ T`), a one-variable quantifier-free formula with
parameters in `S` has a solution in `M` iff it has one in `N`.

`H` says: the quantifier-free type of a tuple `(v, xs)` in `M` and `(w, ys)` in `N` determines the
truth of `∃ y, θ(v, xs, y)` for quantifier-free `θ`.

The reduction carried out here (nothing about `L` is assumed beyond `Language.{0,0}`):

* let `S₀` be the `L`-substructure of `M` whose carrier is the set of values of *all* `L`-terms
  under the assignment `gM = (v, xs)`;
* the quantifier-free type hypothesis says exactly that "evaluate the same term under
  `gN = (w, ys)`" is a well defined function `S₀ → N`, and that it preserves and reflects
  function and relation symbols: an `L`-embedding `Φ : S₀ ↪[L] N` (`termSubEmb`);
* the first `n` bound variables of `θ` are then substituted by parameters of `S₀` (and the free
  variables `α` by parameters of `S₀` too), leaving a one-variable quantifier-free formula
  `φ : L.BoundedFormula S₀ 1` whose solution set is that of `θ.ex` (`exists_qf_collapse`);
* `qfDetermined` applied to `φ`, the inclusion `S₀ ↪[L] M` and `Φ : S₀ ↪[L] N` gives the claim.

Only `import Mathlib`.
-/

open FirstOrder FirstOrder.Language
open scoped FirstOrder

namespace HQEDerive

variable {L : FirstOrder.Language.{0, 0}}

/-! ### 0. Two `Fin.snoc` evaluation lemmas -/

section Snoc

variable {P : Type} {n : ℕ}

/-- `Fin.snoc xs a` is the case analysis `Fin.lastCases a xs`. -/
theorem snoc_eq_lastCases (xs : Fin n → P) (a : P) :
    Fin.snoc (α := fun _ => P) xs a
      = Fin.lastCases (motive := fun _ => P) a xs := by
  funext i
  cases i using Fin.lastCases with
  | last => rw [Fin.snoc_last, Fin.lastCases_last]
  | cast j => rw [Fin.snoc_castSucc, Fin.lastCases_castSucc]

end Snoc

/-! ### 1. The substructure of values of terms -/

section TermSub

variable {M : Type} {N : Type} [L.Structure M] [L.Structure N] {γ : Type*}

/-- The `L`-substructure of `M` consisting of the values of all `L`-terms under the assignment
`g : γ → M`.  (It is the substructure generated by the range of `g`.) -/
def termSub (g : γ → M) : L.Substructure M where
  carrier := Set.range fun t : L.Term γ => t.realize g
  fun_mem := by
    intro k f x hx
    classical
    choose t ht using hx
    refine ⟨Term.func f t, ?_⟩
    show Structure.funMap f (fun i => (t i).realize g) = Structure.funMap f x
    simp only [ht]

theorem mem_termSub {g : γ → M} {x : M} :
    x ∈ (termSub g : L.Substructure M) ↔ ∃ t : L.Term γ, t.realize g = x :=
  Iff.rfl

theorem realize_mem_termSub {g : γ → M} (t : L.Term γ) :
    t.realize g ∈ (termSub g : L.Substructure M) :=
  ⟨t, rfl⟩

/-- The element of `termSub g` given by the variable `x`. -/
def termSubMk (g : γ → M) (x : γ) : termSub (L := L) g :=
  ⟨g x, Term.var x, rfl⟩

@[simp]
theorem termSubMk_val {g : γ → M} (x : γ) : (termSubMk (L := L) g x : M) = g x :=
  rfl

/-- The "same term, evaluated in `g'`" map, as a function on the term-substructure of `g`.  It is
well defined as soon as the two assignments have the same quantifier-free type in the form
`hker`. -/
noncomputable def termSubMap (g : γ → M) (g' : γ → N)
    (hker : ∀ t t' : L.Term γ, (t.realize g = t'.realize g ↔ t.realize g' = t'.realize g')) :
    termSub (L := L) g → N :=
  fun s => (Classical.choose (mem_termSub.1 s.2)).realize g'

theorem termSubMap_eq {g : γ → M} {g' : γ → N}
    {hker : ∀ t t' : L.Term γ,
      (t.realize g = t'.realize g ↔ t.realize g' = t'.realize g')}
    {s : termSub (L := L) g} {t : L.Term γ} (ht : t.realize g = (s : M)) :
    termSubMap (L := L) g g' hker s = t.realize g' :=
  (hker (Classical.choose (mem_termSub.1 s.2)) t).1
    ((Classical.choose_spec (mem_termSub.1 s.2)).trans ht.symm)

theorem termSubMap_injective {g : γ → M} {g' : γ → N}
    {hker : ∀ t t' : L.Term γ,
      (t.realize g = t'.realize g ↔ t.realize g' = t'.realize g')} :
    Function.Injective (termSubMap (L := L) g g' hker) := by
  intro s s' h
  have h2 : (Classical.choose (mem_termSub.1 s.2)).realize g
      = (Classical.choose (mem_termSub.1 s'.2)).realize g :=
    (hker _ _).2 h
  exact Subtype.ext ((Classical.choose_spec (mem_termSub.1 s.2)).symm.trans
    (h2.trans (Classical.choose_spec (mem_termSub.1 s'.2))))

theorem termSubMap_map_fun {g : γ → M} {g' : γ → N}
    {hker : ∀ t t' : L.Term γ,
      (t.realize g = t'.realize g ↔ t.realize g' = t'.realize g')}
    {k : ℕ} (f : L.Functions k) (x : Fin k → termSub (L := L) g) :
    termSubMap (L := L) g g' hker (Structure.funMap f x)
      = Structure.funMap f (fun i => termSubMap g g' hker (x i)) := by
  classical
  choose t ht using fun i => mem_termSub.1 (x i).2
  have hc : (Term.func f t).realize g = ((Structure.funMap f x : termSub g) : M) := by
    show Structure.funMap f (fun i => (t i).realize g) = Structure.funMap f (fun i => ((x i : termSub g) : M))
    simp only [ht]
  rw [termSubMap_eq (hker := hker) hc]
  show Structure.funMap f (fun i => (t i).realize g') = Structure.funMap f (fun i => termSubMap g g' hker (x i))
  congr 1
  funext i
  exact (termSubMap_eq (hker := hker) (s := x i) (t := t i) (ht i)).symm

theorem termSubMap_map_rel {g : γ → M} {g' : γ → N}
    {hker : ∀ t t' : L.Term γ,
      (t.realize g = t'.realize g ↔ t.realize g' = t'.realize g')}
    (hrel : ∀ {k : ℕ} (R : L.Relations k) (ts : Fin k → L.Term γ),
      (Structure.RelMap R (fun i => (ts i).realize g) ↔
        Structure.RelMap R (fun i => (ts i).realize g')))
    {k : ℕ} (R : L.Relations k) (x : Fin k → termSub (L := L) g) :
    Structure.RelMap R (fun i => termSubMap g g' hker (x i)) ↔ Structure.RelMap R x := by
  classical
  choose t ht using fun i => mem_termSub.1 (x i).2
  have hx : (fun i => ((x i : termSub g) : M)) = fun i => (t i).realize g := by
    funext i
    exact (ht i).symm
  have hN : (fun i => termSubMap g g' hker (x i)) = fun i => (t i).realize g' := by
    funext i
    exact termSubMap_eq (hker := hker) (s := x i) (t := t i) (ht i)
  rw [hN]
  show Structure.RelMap R (fun i => (t i).realize g')
    ↔ Structure.RelMap R (fun i => ((x i : termSub g) : M))
  rw [hx]
  exact (hrel R t).symm

/-- The induced `L`-embedding of the term-substructure of `g` into `N`, for two assignments with
the same quantifier-free type. -/
noncomputable def termSubEmb (g : γ → M) (g' : γ → N)
    (hker : ∀ t t' : L.Term γ,
      (t.realize g = t'.realize g ↔ t.realize g' = t'.realize g'))
    (hrel : ∀ {k : ℕ} (R : L.Relations k) (ts : Fin k → L.Term γ),
      (Structure.RelMap R (fun i => (ts i).realize g) ↔
        Structure.RelMap R (fun i => (ts i).realize g'))) :
    termSub (L := L) g ↪[L] N where
  toFun := termSubMap g g' hker
  inj' := termSubMap_injective (hker := hker)
  map_fun' := fun {k} f x => termSubMap_map_fun (hker := hker) f x
  map_rel' := fun {k} R x => termSubMap_map_rel (hker := hker) hrel R x

theorem termSubEmb_apply_var (g : γ → M) (g' : γ → N)
    (hker : ∀ t t' : L.Term γ,
      (t.realize g = t'.realize g ↔ t.realize g' = t'.realize g'))
    (hrel : ∀ {k : ℕ} (R : L.Relations k) (ts : Fin k → L.Term γ),
      (Structure.RelMap R (fun i => (ts i).realize g) ↔
        Structure.RelMap R (fun i => (ts i).realize g')))
    (x : γ) : termSubEmb (L := L) g g' hker hrel (termSubMk g x) = g' x :=
  termSubMap_eq (hker := hker) (s := termSubMk g x) (t := Term.var x) rfl

end TermSub

/-! ### 2. Collapsing bound variables to parameters -/

/-- `Sum.elim` of the two components of `ρ` is `ρ`. -/
theorem sumElim_self {γ δ P : Type*} (ρ : γ ⊕ δ → P) :
    Sum.elim (fun a => ρ (Sum.inl a)) (fun b => ρ (Sum.inr b)) = ρ := by
  funext x
  cases x <;> rfl

section Collapse

variable {α β : Type*} {n : ℕ}

/-- **Replacing every variable by a term.**  If every variable of the quantifier-free formula
`θ : L.BoundedFormula α (n+1)` is replaced by the term `σ` (a term over the free variables `β`
and one bound variable), the result is a quantifier-free formula `φ : L.BoundedFormula β 1` whose
truth under the assignment `ρ` is the truth of `θ` under the induced assignment. -/
theorem exists_qf_collapse (σ : α ⊕ Fin (n + 1) → L.Term (β ⊕ Fin 1))
    {θ : L.BoundedFormula α (n + 1)} (hθ : θ.IsQF) :
    ∃ φ : L.BoundedFormula β 1, φ.IsQF ∧
      ∀ (P : Type) [L.Structure P] (ρ : β ⊕ Fin 1 → P),
        (φ.Realize (fun b => ρ (Sum.inl b)) (fun i => ρ (Sum.inr i)) ↔
          θ.Realize (fun a => (σ (Sum.inl a)).realize ρ)
            (fun i => (σ (Sum.inr i)).realize ρ)) := by
  induction hθ with
  | falsum => exact ⟨⊥, BoundedFormula.isQF_bot, fun P _ ρ => Iff.rfl⟩
  | of_isAtomic h =>
      induction h with
      | equal t₁ t₂ =>
          exact ⟨Term.bdEqual (t₁.subst σ) (t₂.subst σ),
            (BoundedFormula.IsAtomic.equal _ _).isQF,
            fun P _ ρ => by
              simp only [BoundedFormula.realize_bdEqual, Term.realize_subst]
              rw [sumElim_self ρ, sumElim_self (fun a => Term.realize ρ (σ a))]⟩
      | rel R ts =>
          exact ⟨R.boundedFormula (fun i => (ts i).subst σ),
            (BoundedFormula.IsAtomic.rel _ _).isQF,
            fun P _ ρ => by
              simp only [BoundedFormula.realize_rel, Term.realize_subst]
              rw [sumElim_self ρ, sumElim_self (fun a => Term.realize ρ (σ a))]⟩
  | imp h1 h2 ih1 ih2 =>
      obtain ⟨φ₁, hφ₁, hr₁⟩ := ih1
      obtain ⟨φ₂, hφ₂, hr₂⟩ := ih2
      exact ⟨φ₁.imp φ₂, hφ₁.imp hφ₂, fun P _ ρ => by
        simp only [BoundedFormula.realize_imp, hr₁ P ρ, hr₂ P ρ]⟩

end Collapse

/-! ### 3. The main derivation: Johnson's criterion implies `H` -/

section Main

variable {T₀ T : L.Theory}

/-- **The last mile.**  Johnson's criterion (`JohnsonCriterion.qfDetermined`) and its three
hypotheses give the hypothesis `H` consumed by `hasQE_of_qfDet`
(`QE/Merged_end_to_end.lean`): the quantifier-free type of a tuple determines the truth of one
existential quantifier in front of a quantifier-free formula.

The statement is *exactly* the hypothesis `H` of `hasQE_of_qfDet` at `L : Language.{0,0}`,
`α : Type`, models `Theory.ModelType.{0,0,0}`. -/
theorem H_of_qfDetermined (hsub : T₀ ⊆ T)
    (hprime : JohnsonCriterion.HasPrimeModels.{0, 0, 0} T₀ T)
    (hamal : JohnsonCriterion.HasAmalgamation.{0, 0, 0} T₀)
    (h1ec : ∀ (M N : T₀.ModelType.{0, 0, 0}) (f : M ↪[L] N), M ⊨ T →
      JohnsonCriterion.OneECIn f) :
    ∀ (α : Type) (n : ℕ) (θ : L.BoundedFormula α (n + 1)), θ.IsQF →
      ∀ (M N : Theory.ModelType.{0, 0, 0} T) (v : α → M.Carrier) (xs : Fin n → M.Carrier)
        (w : α → N.Carrier) (ys : Fin n → N.Carrier),
        (∀ ψ : L.BoundedFormula α n, ψ.IsQF → (ψ.Realize v xs ↔ ψ.Realize w ys)) →
        ((θ.ex).Realize v xs ↔ (θ.ex).Realize w ys) := by
  intro α n θ hθ M N v xs w ys hQF
  classical
  -- the two assignments
  let gM : (α ⊕ Fin n) → M.Carrier := Sum.elim v xs
  let gN : (α ⊕ Fin n) → N.Carrier := Sum.elim w ys
  -- the substructure of `M` consisting of the values of the terms in the tuple
  let S₀ : L.Substructure M.Carrier := termSub (L := L) gM
  -- the quantifier-free type hypothesis, in the two forms used below
  have hker : ∀ t t' : L.Term (α ⊕ Fin n),
      (t.realize gM = t'.realize gM ↔ t.realize gN = t'.realize gN) := by
    intro t t'
    have h := hQF (Term.bdEqual t t') (BoundedFormula.IsAtomic.equal t t' |>.isQF)
    simpa only [BoundedFormula.realize_bdEqual, gM, gN] using h
  have hrel : ∀ {k : ℕ} (R : L.Relations k) (ts : Fin k → L.Term (α ⊕ Fin n)),
      (Structure.RelMap R (fun i => (ts i).realize gM) ↔
        Structure.RelMap R (fun i => (ts i).realize gN)) := by
    intro k R ts
    have h := hQF (R.boundedFormula ts) (BoundedFormula.IsAtomic.rel R ts |>.isQF)
    simpa only [BoundedFormula.realize_rel, gM, gN] using h
  -- the two embeddings of the base substructure into `M` and into `N`
  let incl : S₀ ↪[L] M.Carrier := S₀.subtype
  let Φ : S₀ ↪[L] N.Carrier := termSubEmb (L := L) gM gN hker hrel
  -- replace every variable of `θ` by a term: parameters of `S₀` for `α` and for the first `n`
  -- bound variables, and the single remaining bound variable for the last one
  let σ : α ⊕ Fin (n + 1) → L.Term (S₀ ⊕ Fin 1) := fun x =>
    match x with
    | Sum.inl a => Term.var (Sum.inl (termSubMk (L := L) gM (Sum.inl a)))
    | Sum.inr i =>
        Fin.lastCases (motive := fun _ => L.Term (S₀ ⊕ Fin 1)) (Term.var (Sum.inr 0))
          (fun j : Fin n => Term.var (Sum.inl (termSubMk (L := L) gM (Sum.inr j)))) i
  obtain ⟨φ, hφqf, hφreal⟩ := exists_qf_collapse (L := L) (β := S₀) σ hθ
  -- the two sides of `qfDetermined` are the two sides of `H`
  have hMreal : ∀ a : M.Carrier,
      (φ.Realize (fun s : S₀ => (incl s : M.Carrier)) (fun _ => a) ↔
        θ.Realize v (Fin.snoc xs a)) := by
    intro a
    let ρM : S₀ ⊕ Fin 1 → M.Carrier :=
      Sum.elim (fun s : S₀ => (s : M.Carrier)) (fun _ : Fin 1 => a)
    have h1 := hφreal M.Carrier ρM
    have hval1 : (fun a' => (σ (Sum.inl a')).realize ρM) = v := by
      funext a'
      show (termSubMk (L := L) gM (Sum.inl a') : M.Carrier) = v a'
      rfl
    have hval2 : (fun i => (σ (Sum.inr i)).realize ρM) = Fin.snoc xs a := by
      have h2 : (fun i => (σ (Sum.inr i)).realize ρM)
          = Fin.lastCases (motive := fun _ => M.Carrier) a xs := by
        funext i
        cases i using Fin.lastCases with
        | last =>
            simp only [σ, Fin.lastCases_last]
            rfl
        | cast j =>
            simp only [σ, Fin.lastCases_castSucc]
            rfl
      exact h2.trans (snoc_eq_lastCases xs a).symm
    exact h1.trans (by rw [hval1, hval2])
  have hNreal : ∀ b : N.Carrier,
      (φ.Realize (fun s : S₀ => (Φ s : N.Carrier)) (fun _ => b) ↔
        θ.Realize w (Fin.snoc ys b)) := by
    intro b
    let ρN : S₀ ⊕ Fin 1 → N.Carrier :=
      Sum.elim (fun s : S₀ => (Φ s : N.Carrier)) (fun _ : Fin 1 => b)
    have h1 := hφreal N.Carrier ρN
    have hval1 : (fun a' => (σ (Sum.inl a')).realize ρN) = w := by
      funext a'
      show (Φ (termSubMk (L := L) gM (Sum.inl a')) : N.Carrier) = w a'
      exact termSubEmb_apply_var (L := L) gM gN hker hrel (Sum.inl a')
    have hval2 : (fun i => (σ (Sum.inr i)).realize ρN) = Fin.snoc ys b := by
      have h2 : (fun i => (σ (Sum.inr i)).realize ρN)
          = Fin.lastCases (motive := fun _ => N.Carrier) b ys := by
        funext i
        cases i using Fin.lastCases with
        | last =>
            simp only [σ, Fin.lastCases_last]
            rfl
        | cast j =>
            simp only [σ, Fin.lastCases_castSucc]
            exact termSubEmb_apply_var (L := L) gM gN hker hrel (Sum.inr j)
      exact h2.trans (snoc_eq_lastCases ys b).symm
    exact h1.trans (by rw [hval1, hval2])
  -- the two models, now bundled over `T₀`
  haveI hMT₀ : M.Carrier ⊨ T₀ := Theory.Model.mono (Theory.ModelType.is_model (self := M)) hsub
  haveI hNT₀ : N.Carrier ⊨ T₀ := Theory.Model.mono (Theory.ModelType.is_model (self := N)) hsub
  let M' : T₀.ModelType.{0, 0, 0} := Theory.ModelType.of T₀ M.Carrier
  let N' : T₀.ModelType.{0, 0, 0} := Theory.ModelType.of T₀ N.Carrier
  have hM'T : M' ⊨ T := Theory.ModelType.is_model (self := M)
  have hN'T : N' ⊨ T := Theory.ModelType.is_model (self := N)
  -- Johnson's criterion, over the base `S₀`
  have hdet := JohnsonCriterion.qfDetermined (L := L) hsub hprime hamal h1ec
    S₀ M' N' hM'T hN'T incl Φ φ hφqf
  rw [BoundedFormula.realize_ex, BoundedFormula.realize_ex]
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨a', ha'⟩ := hdet.1 ⟨a, (hMreal a).2 ha⟩
    exact ⟨a', (hNreal a').1 ha'⟩
  · rintro ⟨b, hb⟩
    obtain ⟨b', hb'⟩ := hdet.2 ⟨b, (hNreal b).2 hb⟩
    exact ⟨b', (hMreal b').1 hb'⟩

end Main

end HQEDerive

#print axioms HQEDerive.H_of_qfDetermined
/-
A quantifier-elimination criterion in Mathlib's first-order syntax, with no
model-theoretic saturation.

`HasQEb T` says: every bounded formula is `T`-equivalent to a quantifier-free one.
`QEAllStep T` / `QEExStep T` say: one universal / existential quantifier applied to a
quantifier-free formula can be removed.

Main results:
* `QEAllStep_iff_QEExStep`  -- the two steps are equivalent;
* `hasQEb_iff_QEAllStep`    -- either step is *equivalent* to full QE;
* `hasQE_of_QEAllStep`      -- the step gives QE for `Formula` (the frozen notion).

# Where the criterion halves meet, and where they do not

This file is the **syntactic half** of the join between Johnson's criterion and the frozen
target. `QE/Johnson_criterion.lean` produces, from prime models + amalgamation + 1-ec, the
semantic statement that a quantifier-free type determines the truth of an existential over a
quantifier-free formula. `QE/QF_type_bridge.lean` turns *full* quantifier-free-type invariance
into `HasQE`. Between them sits `QEExStep` — one existential over a quantifier-free formula is
`T`-equivalent to a quantifier-free one — and this file proves that `QEExStep` gives `HasQE`.

What is still missing is `QFExDetermined → QEExStep`, and the obstruction is concrete:
`BoundedFormula.toFormula : BoundedFormula α n → Formula (α ⊕ Fin n)` has no converse in
Mathlib. The compactness argument (as in `QF_type_bridge.lean`) produces a quantifier-free
`ψ : Formula (α ⊕ Fin n)`, and turning it back into a `BoundedFormula α n` — the direction this
file's `QEExStep` consumes — requires either an inverse of `toFormula` on quantifier-free
formulas or a version of the compactness machinery stated for bounded formulas directly.
-/

set_option linter.unusedVariables false

open FirstOrder FirstOrder.Language

namespace QECriterion

variable {L : Language}

/-- A theory `T` of `L` admits **quantifier elimination on bounded formulas**: every
bounded formula with `n` bound variables is `T`-equivalent to a quantifier-free formula
with the same `n` bound variables. -/
def HasQEb (T : L.Theory) : Prop :=
  ∀ (α : Type) (n : ℕ) (φ : L.BoundedFormula α n),
    ∃ ψ : L.BoundedFormula α n, ψ.IsQF ∧ Theory.Iff T φ ψ

/-- **The universal QE step.**  One universal quantifier in front of a quantifier-free
formula can be removed, modulo `T`. -/
def QEAllStep (T : L.Theory) : Prop :=
  ∀ (α : Type) (n : ℕ) (θ : L.BoundedFormula α (n + 1)), θ.IsQF →
    ∃ ψ : L.BoundedFormula α n, ψ.IsQF ∧ Theory.Iff T θ.all ψ

/-- **The existential QE step.**  One existential quantifier in front of a
quantifier-free formula can be removed, modulo `T`. -/
def QEExStep (T : L.Theory) : Prop :=
  ∀ (α : Type) (n : ℕ) (θ : L.BoundedFormula α (n + 1)), θ.IsQF →
    ∃ ψ : L.BoundedFormula α n, ψ.IsQF ∧ Theory.Iff T θ.ex ψ

/-- `∀ x θ` is `¬∃x ¬θ`. -/
theorem all_iff_ex_not {T : L.Theory} {α : Type} {n : ℕ} (θ : L.BoundedFormula α (n + 1)) :
    Theory.Iff T θ.all θ.not.ex.not := by
  intro M v xs
  simp only [BoundedFormula.realize_iff, BoundedFormula.realize_all, BoundedFormula.realize_not,
    BoundedFormula.realize_ex]
  simp

/-- `∃ x θ` is `¬∀x ¬θ`. -/
theorem ex_iff_all_not {T : L.Theory} {α : Type} {n : ℕ} (θ : L.BoundedFormula α (n + 1)) :
    Theory.Iff T θ.ex θ.not.all.not := by
  intro M v xs
  simp only [BoundedFormula.realize_iff, BoundedFormula.realize_ex, BoundedFormula.realize_not,
    BoundedFormula.realize_all]
  simp

/-- The universal step and the existential step are equivalent. -/
theorem QEAllStep_iff_QEExStep {T : L.Theory} : QEAllStep T ↔ QEExStep T := by
  constructor
  · intro h α n θ hθ
    obtain ⟨ψ, hψ, hψ'⟩ := h α n θ.not hθ.not
    exact ⟨ψ.not, hψ.not, (ex_iff_all_not θ).trans (Theory.Iff.not hψ')⟩
  · intro h α n θ hθ
    obtain ⟨ψ, hψ, hψ'⟩ := h α n θ.not hθ.not
    exact ⟨ψ.not, hψ.not, (all_iff_ex_not θ).trans (Theory.Iff.not hψ')⟩

/-- The universal step gives quantifier elimination, by induction on formulas. -/
theorem hasQEb_of_QEAllStep {T : L.Theory} (h : QEAllStep T) : HasQEb T := by
  intro α n φ
  induction φ with
  | falsum => exact ⟨⊥, BoundedFormula.isQF_bot, Theory.Iff.refl _⟩
  | equal t₁ t₂ => exact ⟨_, BoundedFormula.IsAtomic.equal t₁ t₂ |>.isQF, Theory.Iff.refl _⟩
  | rel R ts => exact ⟨_, BoundedFormula.IsAtomic.rel R ts |>.isQF, Theory.Iff.refl _⟩
  | imp φ₁ φ₂ ih₁ ih₂ =>
      obtain ⟨ψ₁, h₁, h₁'⟩ := ih₁
      obtain ⟨ψ₂, h₂, h₂'⟩ := ih₂
      exact ⟨ψ₁.imp ψ₂, h₁.imp h₂, h₁'.imp h₂'⟩
  | all φ ih =>
      obtain ⟨ψ, hqf, heq⟩ := ih
      obtain ⟨χ, hχqf, hχ⟩ := h α _ ψ hqf
      exact ⟨χ, hχqf, (Theory.Iff.all heq).trans hχ⟩

/-- Conversely, full QE gives the universal step. -/
theorem QEAllStep_of_hasQEb {T : L.Theory} (h : HasQEb T) : QEAllStep T := by
  intro α n θ _
  obtain ⟨ψ, hψ, hψ'⟩ := h α n θ.all
  exact ⟨ψ, hψ, hψ'⟩

/-- **The criterion**: `T` admits quantifier elimination if and only if one universal
quantifier in front of a quantifier-free formula can always be removed. -/
theorem hasQEb_iff_QEAllStep {T : L.Theory} : HasQEb T ↔ QEAllStep T :=
  ⟨QEAllStep_of_hasQEb, hasQEb_of_QEAllStep⟩

theorem hasQEb_iff_QEExStep {T : L.Theory} : HasQEb T ↔ QEExStep T :=
  hasQEb_iff_QEAllStep.trans QEAllStep_iff_QEExStep

/-- Quantifier elimination as it is stated in `Milestone0/Encoding.lean`
(`SpecialTransformations.Milestone0.HasQE`): every `Formula` (i.e. every bounded formula
with no bound variables in scope) is `T`-equivalent to a quantifier-free formula. -/
def HasQE (T : L.Theory) : Prop :=
  ∀ (α : Type) (φ : L.Formula α), ∃ ψ : L.Formula α, ψ.IsQF ∧ Theory.Iff T φ ψ

theorem HasQE_of_hasQEb {T : L.Theory} (h : HasQEb T) : HasQE T :=
  fun α φ => h α 0 φ

/-- **The reduction**: the universal QE step gives quantifier elimination. -/
theorem HasQE_of_QEAllStep {T : L.Theory} (h : QEAllStep T) : HasQE T :=
  HasQE_of_hasQEb (hasQEb_of_QEAllStep h)

/-- **The reduction**, in the existential form. -/
theorem HasQE_of_QEExStep {T : L.Theory} (h : QEExStep T) : HasQE T :=
  HasQE_of_QEAllStep (QEAllStep_iff_QEExStep.2 h)

/-! ### Non-vacuity of the hypothesis

The step hypothesis is not vacuous: it holds for every inconsistent theory.  (This
records that `QEAllStep`/`QEExStep` are satisfiable, so the criterion is not an
unprovable-in-principle formulation.) -/

theorem iff_of_inconsistent {T : L.Theory} (h : (⊥ : L.Sentence) ∈ T)
    {α : Type} {n : ℕ} {φ ψ : L.BoundedFormula α n} : Theory.Iff T φ ψ :=
  fun M _ _ => absurd (Theory.realize_sentence_of_mem (T := T) h) (Sentence.not_realize_bot M)

theorem QEExStep_of_inconsistent {T : L.Theory} (h : (⊥ : L.Sentence) ∈ T) : QEExStep T :=
  fun _ _ _ _ => ⟨⊥, BoundedFormula.isQF_bot, iff_of_inconsistent h⟩

theorem HasQEb_of_inconsistent {T : L.Theory} (h : (⊥ : L.Sentence) ∈ T) : HasQEb T :=
  hasQEb_of_QEAllStep (QEAllStep_iff_QEExStep.2 (QEExStep_of_inconsistent h))

/-! ### Consequence: embeddings of models are elementary

This is the easy half of Shoenfield's test (QE `⟹` every `L`-embedding between models is
elementary, i.e. model completeness), and it shows that the QE notion used above is the
real one.  The proof is the standard one: reduce to a quantifier-free formula and use that
`L`-embeddings preserve quantifier-free formulas both ways. -/

theorem realize_embedding_of_HasQEb {T : L.Theory} (h : HasQEb T)
    {M : Type*} [L.Structure M] [Nonempty M] [M ⊨ T]
    {N : Type*} [L.Structure N] [Nonempty N] [N ⊨ T]
    (f : M ↪[L] N) {α : Type} {n : ℕ} (φ : L.BoundedFormula α n)
    {v : α → M} {xs : Fin n → M} :
    (φ.Realize v xs ↔ φ.Realize (f ∘ v) (f ∘ xs)) := by
  obtain ⟨ψ, hψ, hψ'⟩ := h α n φ
  rw [hψ'.realize_bd_iff (M := M), hψ'.realize_bd_iff (M := N), ← hψ.realize_embedding f]

/-- **Quantifier elimination means the quantifier-free type determines the type** — the
easy half of the back-and-forth / Shoenfield criterion, and the form in which the criterion
meets `PartialEquiv`-based assembly. -/
theorem realize_of_qfType_of_HasQEb {T : L.Theory} (h : HasQEb T)
    {M : Type*} [L.Structure M] [Nonempty M] [M ⊨ T]
    {N : Type*} [L.Structure N] [Nonempty N] [N ⊨ T]
    {α : Type} {n : ℕ} {v : α → M} {xs : Fin n → M} {w : α → N} {ys : Fin n → N}
    (hQF : ∀ ψ : L.BoundedFormula α n, ψ.IsQF → (ψ.Realize v xs ↔ ψ.Realize w ys))
    (φ : L.BoundedFormula α n) : (φ.Realize v xs ↔ φ.Realize w ys) := by
  obtain ⟨ψ, hψ, hψ'⟩ := h α n φ
  rw [hψ'.realize_bd_iff (M := M), hψ'.realize_bd_iff (M := N)]
  exact hQF ψ hψ

/-- **Quantifier elimination makes every embedding between models elementary.** -/
theorem elementary_of_HasQEb {T : L.Theory} (h : HasQEb T)
    {M : Type*} [L.Structure M] [Nonempty M] [M ⊨ T]
    {N : Type*} [L.Structure N] [Nonempty N] [N ⊨ T]
    (f : M ↪[L] N) (φ : L.Sentence) : M ⊨ φ → N ⊨ φ := by
  intro hφ
  have h2 := (realize_embedding_of_HasQEb (T := T) h f φ
    (v := (default : Empty → M)) (xs := (default : Fin 0 → M))).1 hφ
  have e1 : (⇑f ∘ (default : Empty → M)) = (default : Empty → N) := Subsingleton.elim _ _
  have e2 : (⇑f ∘ (default : Fin 0 → M)) = (default : Fin 0 → N) := Subsingleton.elim _ _
  rw [e1, e2] at h2
  simpa [Sentence.Realize, Formula.Realize] using h2


/-! ### The model-theoretic hypotheses

`Saturated`, `ExtensionProperty` (Proposition 3.9 of arXiv:1006.1393) and `SaturationExists`
are stated here as ordinary `Prop`s, so that the paper's hypothesis can be named exactly.
`QFTypeDetermines` is the type-theoretic statement that QE is classically routed through. -/

/-- `N` is **saturated** (realises every type over itself): every theory in the language
`L` with constants for the elements of `N` that is finitely satisfiable is satisfied by `N`.
This is the standard saturation hypothesis of Shoenfeld's test, stated in the form that needs
no cardinal arithmetic; it implies `#N⁺`-saturation at every use below. -/
def Saturated (N : Type*) [L.Structure N] : Prop :=
  ∀ (p : L[[N]].Theory),
    (∀ p₀ : Finset (L[[N]].Sentence), (↑p₀ : L[[N]].Theory) ⊆ p →
      Theory.IsSatisfiable (↑p₀ : (L[[N]]).Theory)) → N ⊨ p

/-- **Proposition 3.9 of arXiv:1006.1393 (`lrv:mono:lift`)**, as a `Prop`: for models
`M, N` of `T` with `N` saturated, every monomorphism into `N` from a substructure of `M`
extends to a monomorphism defined on all of `M`. -/
def ExtensionProperty (T : L.Theory) : Prop :=
  ∀ (M : Type*) [L.Structure M] [Nonempty M], M ⊨ T →
  ∀ (N : Type*) [L.Structure N] [Nonempty N], N ⊨ T → @Saturated L N _ →
  ∀ (S : L.Substructure M) (f : S ↪[L] N), ∃ (g : M ↪[L] N), ∀ s : S, g s = f s

/-- Every model of `T` has a saturated elementary extension.  This is a general theorem of
first-order logic (compactness plus ultrapowers); it is **not** formalised here. -/
def SaturationExists (T : L.Theory) : Prop :=
  ∀ (M : Type*) [L.Structure M] [Nonempty M], M ⊨ T →
    ∃ (N : Type*) (i : L.Structure N), Nonempty N ∧ @Theory.Model L N i T ∧
      @Saturated L N i ∧ Nonempty (FirstOrder.Language.ElementaryEmbedding L M N)

/-- The quantifier-free type of a tuple determines its type. -/
def QFTypeDetermines (T : L.Theory) : Prop :=
  ∀ (α : Type) (n : ℕ) (M : Type*) [L.Structure M] [Nonempty M], M ⊨ T →
  ∀ (N : Type*) [L.Structure N] [Nonempty N], N ⊨ T →
  ∀ (v : α → M) (xs : Fin n → M) (w : α → N) (ys : Fin n → N),
    (∀ ψ : L.BoundedFormula α n, ψ.IsQF → (ψ.Realize v xs ↔ ψ.Realize w ys)) →
    ∀ φ : L.BoundedFormula α n, (φ.Realize v xs ↔ φ.Realize w ys)

/-- The trivial half of the type criterion: QE makes the quantifier-free type of a tuple
determine its type. -/
theorem QFTypeDetermines_of_HasQEb {T : L.Theory} (h : HasQEb T) : QFTypeDetermines T :=
  fun α n M _ _ hM N _ _ hN v xs w ys hQF φ =>
    realize_of_qfType_of_HasQEb (T := T) h hQF φ

/-- **Shoenfield's test**, stated as a single `Prop`: the extension property of
Proposition 3.9 of arXiv:1006.1393, together with the existence of saturated elementary
extensions, implies quantifier elimination.  **This is the one implication of the paper's
Section 3 that is not formalised here**; everything downstream of it is
`HasQE_of_QEExStep`. -/
def ShoenfieldTest (T : L.Theory) : Prop :=
  SaturationExists T → ExtensionProperty T → QEExStep T

/-- The reduction, with the paper's hypothesis in place. -/
theorem HasQE_of_ShoenfieldTest {T : L.Theory} (h : ShoenfieldTest T) (hSat : SaturationExists T)
    (hEP : ExtensionProperty T) : HasQE T :=
  HasQE_of_QEExStep (h hSat hEP)

/-! ### A sanity instance

The theory of a one-element structure in the empty language admits QE, and both routes
give it: directly, and through the criterion above.  This checks that the step hypothesis
is satisfiable and that the criterion reproduces a known answer.  (A serious validation on
DLO or ACF is *not* attempted here.) -/

namespace OneElement

/-- The empty language. -/
def L0 : Language := ⟨fun _ => Empty, fun _ => Empty⟩

instance (M : Type) : L0.Structure M where
  funMap {_} f := f.elim
  RelMap {_} R := R.elim

/-- `x = y`, with both variables in scope. -/
def sub2 : L0.BoundedFormula Empty 2 :=
  BoundedFormula.equal (Term.var (Sum.inr (0 : Fin 2))) (Term.var (Sum.inr (1 : Fin 2)))

/-- `∀ x ∀ y, x = y`. -/
def subsingletonSentence : L0.Sentence := sub2.alls

/-- The theory of a one-element structure. -/
def T0 : L0.Theory := {subsingletonSentence}

theorem subsingleton_of_model {M : Type*} [L0.Structure M] [M ⊨ T0] : Subsingleton M := by
  have h : Formula.Realize sub2.alls (default : Empty → M) :=
    Theory.realize_sentence_of_mem (T := T0) (φ := subsingletonSentence) (M := M)
      (by simp [T0])
  have h0 : ∀ xs : Fin 2 → M, sub2.Realize (default : Empty → M) xs := by
    simpa only [BoundedFormula.realize_alls] using h
  exact ⟨fun a b => h0 ![a, b]⟩

/-- Every `L0`-formula is either true in every model of `T0` under every valuation, or
false in every model of `T0` under every valuation. -/
theorem valid_or_refutable {α : Type} {n : ℕ} (φ : L0.BoundedFormula α n) :
    T0 ⊨ᵇ φ ∨ T0 ⊨ᵇ φ.not := by
  induction φ with
  | falsum => exact Or.inr fun _ _ _ h => h
  | equal t₁ t₂ =>
      exact Or.inl fun M _ _ => by
        have hsub := subsingleton_of_model (M := M)
        exact hsub.elim _ _
  | rel R _ => exact R.elim
  | imp φ₁ φ₂ ih₁ ih₂ =>
      rcases ih₁ with h₁ | h₁
      · rcases ih₂ with h₂ | h₂
        · exact Or.inl fun M v xs _ => h₂ M v xs
        · exact Or.inr fun M v xs hp => h₂ M v xs (hp (h₁ M v xs))
      · exact Or.inl fun M v xs hp => absurd hp (h₁ M v xs)
  | all φ ih =>
      rcases ih with h | h
      · exact Or.inl fun M v xs => fun a => h M v (Fin.snoc xs a)
      · exact Or.inr fun M v xs hall =>
          h M v (Fin.snoc xs (Classical.arbitrary M)) (hall _)

theorem HasQEb_T0 : HasQEb T0 := by
  intro α n φ
  rcases valid_or_refutable φ with h | h
  · exact ⟨⊤, BoundedFormula.IsQF.top, fun M v xs => by
      rw [BoundedFormula.realize_iff, BoundedFormula.realize_top]
      exact iff_true_intro (h M v xs)⟩
  · exact ⟨⊥, BoundedFormula.isQF_bot, fun M v xs => by
      rw [BoundedFormula.realize_iff, BoundedFormula.realize_bot]
      exact iff_false_intro (h M v xs)⟩

theorem QEExStep_T0 : QEExStep T0 := by
  intro α n θ _
  rcases valid_or_refutable θ.ex with h | h
  · exact ⟨⊤, BoundedFormula.IsQF.top, fun M v xs => by
      rw [BoundedFormula.realize_iff, BoundedFormula.realize_top]
      exact iff_true_intro (h M v xs)⟩
  · exact ⟨⊥, BoundedFormula.isQF_bot, fun M v xs => by
      rw [BoundedFormula.realize_iff, BoundedFormula.realize_bot]
      exact iff_false_intro (h M v xs)⟩

/-- The criterion reproduces the direct proof of QE for `T0`. -/
theorem HasQEb_T0_via_criterion : HasQEb T0 :=
  hasQEb_of_QEAllStep (QEAllStep_iff_QEExStep.2 QEExStep_T0)

end OneElement

end QECriterion


namespace ShoenfieldQE

variable {L : FirstOrder.Language.{u, v}}

/-!
# The compactness argument for bounded formulas

`BoundedFormula.toFormula : BoundedFormula α n → Formula (α ⊕ Fin n)` has no converse in
Mathlib, and the formula-level compactness argument produces its output on the `Formula` side
while `QEExStep` consumes `BoundedFormula α n`. This file removes that obstruction by running
the whole argument in `BoundedFormula α n`, using `toFormula` **only on the way into**
compactness: given a finite set of `Formula`s in the image, the corresponding bounded formulas
are chosen by `Finset.attach` plus choice, and the witness is pushed forward again. No inverse
of `toFormula` is needed.

Contents, all in `BoundedFormula α n`:
* `exists_realize_bounded` — compactness for bounded formulas;
* `lifsup`/`liinf` with `isQF_lifsup`/`isQF_liinf` and `realize_lifsup`/`realize_liinf`;
* `exists_qf_imp_bounded` — isolation: under QF-type invariance for `β`, an assignment
  satisfying `β` is separated from its complement by a QF formula implying `β`.

Not yet done: the cover and the final `QEExStep` assembly, which is mechanical given
`exists_qf_imp_bounded` and `exists_realize_bounded`.
-/

/-! ## Quantifier elimination, formula level

`HasQE T` is the formula-level statement that every `L`-formula is `T`-equivalent to a
quantifier-free one.  It has the same shape as `SpecialTransformations.Milestone0.HasQE`
(`Milestone0/Encoding.lean`), only at a general language `L`. -/

/-- `T` admits quantifier elimination. -/
def HasQE (T : L.Theory) : Prop :=
  ∀ (α : Type u) (φ : L.Formula α), ∃ ψ : L.Formula α, ψ.IsQF ∧ T ⊨ᵇ (φ ⇔ ψ)

/-! ## Finite conjunctions and disjunctions -/

section Finite

variable {α : Type u} {β : Type*}

lemma isQF_listFoldr_sup (l : List β) (f : β → L.Formula α) (h : ∀ b ∈ l, (f b).IsQF) :
    (l.map f).foldr (· ⊔ ·) ⊥ |>.IsQF := by
  induction l with
  | nil => exact BoundedFormula.isQF_bot
  | cons a l ih =>
      rw [List.map_cons, List.foldr_cons]
      exact (h a (by simp)).sup (ih (fun b hb => h b (by simp [hb])))

lemma isQF_listFoldr_inf (l : List β) (f : β → L.Formula α)
    (h : ∀ b ∈ l, (f b).IsQF) : (l.map f).foldr (· ⊓ ·) ⊤ |>.IsQF := by
  induction l with
  | nil => exact BoundedFormula.IsQF.top
  | cons a l ih =>
      rw [List.map_cons, List.foldr_cons]
      exact (h a (by simp)).inf (ih (fun b hb => h b (by simp [hb])))

/-- A finite disjunction of quantifier-free formulas is quantifier-free. -/
lemma isQF_iSup {β : Type*} [Finite β] (f : β → L.Formula α) (h : ∀ b, (f b).IsQF) :
    (Formula.iSup f).IsQF := by
  classical
  rw [Formula.iSup, BoundedFormula.iSup]
  exact isQF_listFoldr_sup _ f (fun b _ => h b)

/-- A finite conjunction of quantifier-free formulas is quantifier-free. -/
lemma isQF_iInf {β : Type*} [Finite β] (f : β → L.Formula α) (h : ∀ b, (f b).IsQF) :
    (Formula.iInf f).IsQF := by
  classical
  rw [Formula.iInf, BoundedFormula.iInf]
  exact isQF_listFoldr_inf _ f (fun b _ => h b)

/-- The realization of a finite disjunction of formulas. -/
lemma realize_iSup {β : Type*} [Finite β] (f : β → L.Formula α) {M : Type*} [L.Structure M]
    (v : α → M) : (Formula.iSup f).Realize v ↔ ∃ b, (f b).Realize v :=
  BoundedFormula.realize_iSup

/-- The realization of a finite conjunction of formulas. -/
lemma realize_iInf {β : Type*} [Finite β] (f : β → L.Formula α) {M : Type*} [L.Structure M]
    (v : α → M) : (Formula.iInf f).Realize v ↔ ∀ b, (f b).Realize v :=
  BoundedFormula.realize_iInf

end Finite

/-! ## Compactness for a set of formulas with free variables -/

/-- **Compactness, realization form.** If every finite set of formulas taken from `Γ` can be
realized together with `φ` in a model of `T`, then `Γ` itself can be realized together with `φ`. -/
theorem exists_model_realize_of_finset {α : Type u} {T : L.Theory} {Γ : Set (L.Formula α)}
    {φ : L.Formula α}
    (h : ∀ Γ0 : Finset (L.Formula α), (∀ ψ ∈ Γ0, ψ ∈ Γ) →
      ∃ (M : Theory.ModelType.{u, v, max u v} T) (v : α → M.Carrier),
        (∀ ψ ∈ Γ0, ψ.Realize v) ∧ φ.Realize v) :
    ∃ (M : Theory.ModelType.{u, v, max u v} T) (v : α → M.Carrier),
      (∀ ψ ∈ Γ, ψ.Realize v) ∧ φ.Realize v := by
  classical
  set U : (L[[α]]).Theory :=
    (L.lhomWithConstants α).onTheory T ∪ Formula.equivSentence '' Γ ∪
      {Formula.equivSentence φ} with hUdef
  have hfin : U.IsFinitelySatisfiable := by
    intro U0 hU0
    -- the part of `Γ` that shows up in `U0`
    set Γ0 : Finset (L.Formula α) :=
      (U0.filter (fun s => s ∈ Formula.equivSentence '' Γ)).image
        (fun s => Formula.equivSentence.symm s) with hΓ0def
    have hΓ0 : ∀ ψ ∈ Γ0, ψ ∈ Γ := by
      intro ψ hψ
      obtain ⟨s, hs, hseq⟩ := Finset.mem_image.mp hψ
      obtain ⟨-, hs2⟩ := Finset.mem_filter.mp hs
      obtain ⟨ψ', hψ', hψ'eq⟩ := (Set.mem_image _ _ _).mp hs2
      rw [← hseq, ← hψ'eq, Equiv.symm_apply_apply]
      exact hψ'
    obtain ⟨M, v, hv, hφv⟩ := h Γ0 hΓ0
    letI : (constantsOn α).Structure M.Carrier := constantsOn.structure v
    have hmem : ∀ s ∈ U0, M.Carrier ⊨ s := by
      intro s hs
      have hsU : s ∈ U := hU0 hs
      simp only [hUdef, Set.mem_union, Set.mem_image, Set.mem_singleton_iff] at hsU
      rcases hsU with (hsT | ⟨ψ, hψ, hψs⟩) | hφs
      · exact ((LHom.onTheory_model (L.lhomWithConstants α) T).2 M.is_model).realize_of_mem s hsT
      · rw [← hψs] at hs ⊢
        refine (Formula.realize_equivSentence M.Carrier ψ).2 (hv ψ ?_)
        rw [hΓ0def]
        exact Finset.mem_image.mpr
          ⟨Formula.equivSentence ψ, Finset.mem_filter.mpr ⟨hs, ⟨ψ, hψ, rfl⟩⟩, by simp⟩
      · rw [hφs]
        exact (Formula.realize_equivSentence M.Carrier φ).2 hφv
    haveI : M.Carrier ⊨ (U0 : (L[[α]]).Theory) := ⟨fun s hs => hmem s hs⟩
    exact Theory.Model.isSatisfiable M.Carrier
  obtain ⟨N⟩ := Theory.isSatisfiable_iff_isFinitelySatisfiable.2 hfin
  have hNU : ∀ s ∈ U, N.Carrier ⊨ s := fun s hs => N.is_model.realize_of_mem s hs
  letI : L.Structure N.Carrier := (L.lhomWithConstants α).reduct N.Carrier
  have hNT : N.Carrier ⊨ T :=
    (LHom.onTheory_model (L.lhomWithConstants α) T).1
      ⟨fun s hs => hNU s (by rw [hUdef]; exact Or.inl (Or.inl hs))⟩
  refine ⟨Theory.ModelType.of T N.Carrier, fun a => (L.con a : N.Carrier), ?_, ?_⟩
  · intro ψ hψ
    refine (Formula.realize_equivSentence N.Carrier ψ).1 (hNU _ ?_)
    rw [hUdef]
    exact Or.inl (Or.inr ⟨ψ, hψ, rfl⟩)
  · refine (Formula.realize_equivSentence N.Carrier φ).1 (hNU _ ?_)
    rw [hUdef]
    exact Or.inr rfl


end ShoenfieldQE

namespace BoundedQE

open ShoenfieldQE

variable {L : FirstOrder.Language.{u, v}}

/-- `T`-equivalence of bounded formulas with the same context. -/
def IffB (T : L.Theory) {α : Type u} {n : ℕ} (φ ψ : L.BoundedFormula α n) : Prop :=
  ∀ (M : Theory.ModelType.{u, v, max u v} T) (v : α → M.Carrier) (xs : Fin n → M.Carrier),
    (φ.Realize v xs ↔ ψ.Realize v xs)

/-- One existential quantifier in front of a quantifier-free formula can be removed. -/
def QEExStep (T : L.Theory) : Prop :=
  ∀ (α : Type u) (n : ℕ) (θ : L.BoundedFormula α (n + 1)), θ.IsQF →
    ∃ ψ : L.BoundedFormula α n, ψ.IsQF ∧ IffB T θ.ex ψ

/-- **Compactness for bounded formulas.** Only the *forward* map `toFormula` is used: finite sets
are pulled back along membership in its image by choice, which needs no inverse. -/
theorem exists_realize_bounded {α : Type u} {n : ℕ} {T : L.Theory}
    {Γ : Set (L.BoundedFormula α n)} {β : L.BoundedFormula α n}
    (h : ∀ Γ0 : Finset (L.BoundedFormula α n), (∀ ψ ∈ Γ0, ψ ∈ Γ) →
      ∃ (M : Theory.ModelType.{u, v, max u v} T) (v : α → M.Carrier) (xs : Fin n → M.Carrier),
        (∀ ψ ∈ Γ0, ψ.Realize v xs) ∧ β.Realize v xs) :
    ∃ (M : Theory.ModelType.{u, v, max u v} T) (v : α → M.Carrier) (xs : Fin n → M.Carrier),
      (∀ ψ ∈ Γ, ψ.Realize v xs) ∧ β.Realize v xs := by
  classical
  set Γ' : Set (L.Formula (α ⊕ Fin n)) := BoundedFormula.toFormula '' Γ with hΓ'def
  have hfin : ∀ Γ0 : Finset (L.Formula (α ⊕ Fin n)), (∀ ψ ∈ Γ0, ψ ∈ Γ') →
      ∃ (M : Theory.ModelType.{u, v, max u v} T) (V : α ⊕ Fin n → M.Carrier),
        (∀ ψ ∈ Γ0, ψ.Realize V) ∧ β.toFormula.Realize V := by
    intro Γ0 hΓ0
    choose f hfΓ hfeq using fun (ψ : ↥Γ0) => (Set.mem_image _ _ _).mp (hΓ0 ψ.1 ψ.2)
    set Γ0' : Finset (L.BoundedFormula α n) := Γ0.attach.image f with hΓ0'def
    have hΓ0'mem : ∀ ψ ∈ Γ0', ψ ∈ Γ := by
      intro ψ hψ
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hψ
      exact hfΓ j
    obtain ⟨M, v, xs, hall, hβ⟩ := h Γ0' hΓ0'mem
    refine ⟨M, Sum.elim v xs, ?_, ?_⟩
    · intro ψ hψ
      have hmem : f ⟨ψ, hψ⟩ ∈ Γ0' :=
        Finset.mem_image.mpr ⟨⟨ψ, hψ⟩, Finset.mem_attach _ _, rfl⟩
      have h1 := hall _ hmem
      have h2 : (f ⟨ψ, hψ⟩).toFormula = ψ := hfeq ⟨ψ, hψ⟩
      rw [← h2, BoundedFormula.realize_toFormula]
      simpa using h1
    · rw [BoundedFormula.realize_toFormula]
      simpa using hβ
  obtain ⟨M, V, hV, hβV⟩ :=
    ShoenfieldQE.exists_model_realize_of_finset (T := T) (Γ := Γ') (φ := β.toFormula) hfin
  refine ⟨M, V ∘ Sum.inl, V ∘ Sum.inr, ?_, ?_⟩
  · intro ψ hψ
    have h1 := hV _ (Set.mem_image_of_mem _ hψ)
    rwa [BoundedFormula.realize_toFormula] at h1
  · have h1 := hβV
    rwa [BoundedFormula.realize_toFormula] at h1

end BoundedQE

namespace BoundedQE

open ShoenfieldQE

variable {L : FirstOrder.Language.{u, v}}

/-- Finite disjunction of bounded formulas, by a list fold. -/
noncomputable def lifsup {α : Type u} {n : ℕ} (l : List (L.BoundedFormula α n)) :
    L.BoundedFormula α n :=
  l.foldr (· ⊔ ·) ⊥

/-- Finite conjunction of bounded formulas, by a list fold. -/
noncomputable def liinf {α : Type u} {n : ℕ} (l : List (L.BoundedFormula α n)) :
    L.BoundedFormula α n :=
  l.foldr (· ⊓ ·) ⊤

theorem isQF_lifsup {α : Type u} {n : ℕ} {l : List (L.BoundedFormula α n)}
    (h : ∀ ψ ∈ l, ψ.IsQF) : (lifsup l).IsQF := by
  induction l with
  | nil => exact BoundedFormula.isQF_bot
  | cons a t ih =>
    exact BoundedFormula.IsQF.sup (h a (List.mem_cons_self))
      (ih fun ψ hψ => h ψ (List.mem_cons_of_mem _ hψ))

theorem isQF_liinf {α : Type u} {n : ℕ} {l : List (L.BoundedFormula α n)}
    (h : ∀ ψ ∈ l, ψ.IsQF) : (liinf l).IsQF := by
  induction l with
  | nil => exact BoundedFormula.IsQF.top
  | cons a t ih =>
    exact BoundedFormula.IsQF.inf (h a (List.mem_cons_self))
      (ih fun ψ hψ => h ψ (List.mem_cons_of_mem _ hψ))

theorem realize_lifsup {α : Type u} {n : ℕ} {l : List (L.BoundedFormula α n)}
    {M : Type*} [L.Structure M] (v : α → M) (xs : Fin n → M) :
    (lifsup l).Realize v xs ↔ ∃ ψ ∈ l, ψ.Realize v xs := by
  induction l with
  | nil => simp [lifsup, BoundedFormula.realize_bot]
  | cons a t ih =>
    rw [show lifsup (a :: t) = a ⊔ lifsup t from rfl, BoundedFormula.realize_sup, ih]
    simp only [List.mem_cons]
    constructor
    · rintro (h | ⟨ψ, hψ, hreal⟩)
      · exact ⟨a, Or.inl rfl, h⟩
      · exact ⟨ψ, Or.inr hψ, hreal⟩
    · rintro ⟨ψ, (rfl | hψ), hreal⟩
      · exact Or.inl hreal
      · exact Or.inr ⟨ψ, hψ, hreal⟩

theorem realize_liinf {α : Type u} {n : ℕ} {l : List (L.BoundedFormula α n)}
    {M : Type*} [L.Structure M] (v : α → M) (xs : Fin n → M) :
    (liinf l).Realize v xs ↔ ∀ ψ ∈ l, ψ.Realize v xs := by
  induction l with
  | nil => simp [liinf, BoundedFormula.realize_top]
  | cons a t ih =>
    rw [show liinf (a :: t) = a ⊓ liinf t from rfl, BoundedFormula.realize_inf, ih]
    simp only [List.mem_cons]
    constructor
    · rintro ⟨h, ht⟩ ψ (rfl | hψ)
      · exact h
      · exact ht ψ hψ
    · intro h
      exact ⟨h a (Or.inl rfl), fun ψ hψ => h ψ (Or.inr hψ)⟩

/-- **Isolation**, bounded form. -/
theorem exists_qf_imp_bounded {α : Type u} {n : ℕ} {T : L.Theory} {β : L.BoundedFormula α n}
    (Hβ : ∀ (M N : Theory.ModelType.{u, v, max u v} T) (v : α → M.Carrier)
      (xs : Fin n → M.Carrier) (w : α → N.Carrier) (ys : Fin n → N.Carrier),
      (∀ ψ : L.BoundedFormula α n, ψ.IsQF → (ψ.Realize v xs ↔ ψ.Realize w ys)) →
      (β.Realize v xs ↔ β.Realize w ys))
    (M : Theory.ModelType.{u, v, max u v} T) (v : α → M.Carrier) (xs : Fin n → M.Carrier)
    (hβ : β.Realize v xs) :
    ∃ ψ : L.BoundedFormula α n, ψ.IsQF ∧ ψ.Realize v xs ∧
      ∀ (N : Theory.ModelType.{u, v, max u v} T) (w : α → N.Carrier) (ys : Fin n → N.Carrier),
        ψ.Realize w ys → β.Realize w ys := by
  classical
  by_contra hcon
  push Not at hcon
  set Γ : Set (L.BoundedFormula α n) := {ψ | ψ.IsQF ∧ ψ.Realize v xs} with hΓdef
  have hfin : ∀ Γ0 : Finset (L.BoundedFormula α n), (∀ ψ ∈ Γ0, ψ ∈ Γ) →
      ∃ (N : Theory.ModelType.{u, v, max u v} T) (w : α → N.Carrier) (ys : Fin n → N.Carrier),
        (∀ ψ ∈ Γ0, ψ.Realize w ys) ∧ β.not.Realize w ys := by
    intro Γ0 hΓ0
    have hq : ∀ ψ ∈ Γ0.val.toList, ψ.IsQF :=
      fun ψ hψ => (hΓ0 ψ (Finset.mem_val.mp (Multiset.mem_toList.mp hψ))).1
    have hr : ∀ ψ ∈ Γ0.val.toList, ψ.Realize v xs :=
      fun ψ hψ => (hΓ0 ψ (Finset.mem_val.mp (Multiset.mem_toList.mp hψ))).2
    obtain ⟨N, w, ys, h1, h2⟩ :=
      hcon _ (isQF_liinf hq) ((realize_liinf v xs).2 hr)
    exact ⟨N, w, ys,
      fun ψ hψ => (realize_liinf w ys).1 h1 ψ
        (Multiset.mem_toList.mpr (Finset.mem_val.mpr hψ)),
      (BoundedFormula.realize_not).2 h2⟩
  obtain ⟨N, w, ys, hw, hnβ⟩ := exists_realize_bounded (T := T) hfin
  have htypes : ∀ ψ : L.BoundedFormula α n, ψ.IsQF → (ψ.Realize v xs ↔ ψ.Realize w ys) := by
    intro ψ hψ
    constructor
    · intro hvψ
      exact hw ψ ⟨hψ, hvψ⟩
    · intro hwψ
      by_contra hvψ
      have hcontr := hw ψ.not ⟨hψ.not, (BoundedFormula.realize_not).2 hvψ⟩
      rw [BoundedFormula.realize_not] at hcontr
      exact hcontr hwψ
  have hiff := Hβ M N v xs w ys htypes
  rw [BoundedFormula.realize_not] at hnβ
  exact hnβ (hiff.mp hβ)

/-! ## The cover and the assembly -/

/-- **`QFExDetermined` gives `QEExStep`.** The cover is produced by contradiction: if no finite
set of quantifier-free consequences covered `θ.ex`, bounded compactness would give a tuple
satisfying `θ.ex` and falsifying every quantifier-free consequence of it, contradicting the
isolation lemma. -/
theorem qeExStep_of_qfDet {T : L.Theory}
    (H : ∀ (α : Type u) (n : ℕ) (θ : L.BoundedFormula α (n + 1)), θ.IsQF →
      ∀ (M N : Theory.ModelType.{u, v, max u v} T) (v : α → M.Carrier)
        (xs : Fin n → M.Carrier) (w : α → N.Carrier) (ys : Fin n → N.Carrier),
        (∀ ψ : L.BoundedFormula α n, ψ.IsQF → (ψ.Realize v xs ↔ ψ.Realize w ys)) →
        ((θ.ex).Realize v xs ↔ (θ.ex).Realize w ys)) :
    QEExStep (L := L) T := by
  intro α n θ hθ
  classical
  have Hβ := H α n θ hθ
  set Ψ : Set (L.BoundedFormula α n) :=
    {ψ | ψ.IsQF ∧ ∀ (M : Theory.ModelType.{u, v, max u v} T) (v : α → M.Carrier)
      (xs : Fin n → M.Carrier), ψ.Realize v xs → (θ.ex).Realize v xs} with hΨdef
  have hcov : ∃ Ψ0 : Finset (L.BoundedFormula α n), (∀ ψ ∈ Ψ0, ψ ∈ Ψ) ∧
      ∀ (M : Theory.ModelType.{u, v, max u v} T) (v : α → M.Carrier) (xs : Fin n → M.Carrier),
        (θ.ex).Realize v xs → (lifsup Ψ0.val.toList).Realize v xs := by
    by_contra hno
    push Not at hno
    set Γ : Set (L.BoundedFormula α n) := {η | ∃ ψ ∈ Ψ, ψ.not = η} with hΓdef
    have hfin : ∀ Γ0 : Finset (L.BoundedFormula α n), (∀ η ∈ Γ0, η ∈ Γ) →
        ∃ (M : Theory.ModelType.{u, v, max u v} T) (v : α → M.Carrier)
          (xs : Fin n → M.Carrier),
          (∀ η ∈ Γ0, η.Realize v xs) ∧ (θ.ex).Realize v xs := by
      intro Γ0 hΓ0
      have hchoice : ∀ η : ↥Γ0, ∃ ψ ∈ Ψ, ψ.not = η.1 := fun η => hΓ0 η.1 η.2
      choose f hfΨ hfeq using hchoice
      set Ψ0 : Finset (L.BoundedFormula α n) := Γ0.attach.image f with hΨ0def
      have hΨ0 : ∀ ψ ∈ Ψ0, ψ ∈ Ψ := by
        intro ψ hψ
        obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hψ
        exact hfΨ j
      obtain ⟨M, v, xs, hθex, hnoψ⟩ := hno Ψ0 hΨ0
      refine ⟨M, v, xs, ?_, hθex⟩
      intro η hη
      have hmem : f ⟨η, hη⟩ ∈ Ψ0 :=
        Finset.mem_image.mpr ⟨⟨η, hη⟩, Finset.mem_attach _ _, rfl⟩
      have hfalse : ¬ (f ⟨η, hη⟩).Realize v xs := by
        intro htrue
        exact hnoψ ((realize_lifsup v xs).2 ⟨_, Multiset.mem_toList.mpr hmem, htrue⟩)
      have heq : (f ⟨η, hη⟩).not = η := hfeq ⟨η, hη⟩
      rw [← heq, BoundedFormula.realize_not]
      exact hfalse
    obtain ⟨M, v, xs, hΓ0, hθex⟩ := exists_realize_bounded (T := T) hfin
    obtain ⟨ψ0, hqf0, htrue0, himp0⟩ := exists_qf_imp_bounded (T := T) Hβ M v xs hθex
    have hmemΨ : ψ0 ∈ Ψ := ⟨hqf0, himp0⟩
    have hnotmem : ψ0.not ∈ Γ := ⟨ψ0, hmemΨ, rfl⟩
    have hcontra := hΓ0 ψ0.not hnotmem
    rw [BoundedFormula.realize_not] at hcontra
    exact hcontra htrue0
  obtain ⟨Ψ0, hΨ0, hcov⟩ := hcov
  refine ⟨lifsup Ψ0.val.toList,
    isQF_lifsup (fun ψ hψ => (hΨ0 ψ (Multiset.mem_toList.mp hψ)).1), ?_⟩
  intro M v xs
  constructor
  · intro h
    exact hcov M v xs h
  · intro h
    obtain ⟨ψ, hψl, hψtrue⟩ := (realize_lifsup v xs).1 h
    exact (hΨ0 ψ (Multiset.mem_toList.mp hψl)).2 M v xs hψtrue

end BoundedQE


#print axioms BoundedQE.exists_realize_bounded
#print axioms BoundedQE.exists_qf_imp_bounded
#print axioms BoundedQE.isQF_lifsup
#print axioms BoundedQE.realize_liinf

namespace BoundedQE

open QECriterion

/-- **The join.** `QEExStep` in the form `QE_step_induction.lean` consumes, from the
quantifier-free-existential determinism that Johnson's criterion produces.

Stated at `L₀ : Language.{0, 0}` and `α : Type`, the universe level of `QECriterion.QEExStep`. -/
theorem qeExStep_theoryIff {L₀ : FirstOrder.Language.{0, 0}} {T : L₀.Theory}
    (H : ∀ (α : Type) (n : ℕ) (θ : L₀.BoundedFormula α (n + 1)), θ.IsQF →
      ∀ (M N : Theory.ModelType.{0, 0, 0} T) (v : α → M.Carrier)
        (xs : Fin n → M.Carrier) (w : α → N.Carrier) (ys : Fin n → N.Carrier),
        (∀ ψ : L₀.BoundedFormula α n, ψ.IsQF → (ψ.Realize v xs ↔ ψ.Realize w ys)) →
        ((θ.ex).Realize v xs ↔ (θ.ex).Realize w ys)) :
    QECriterion.QEExStep (L := L₀) T := by
  intro α n θ hθ
  obtain ⟨ψ, hqf, hiffB⟩ := qeExStep_of_qfDet (L := L₀) H α n θ hθ
  refine ⟨ψ, hqf, ?_⟩
  intro M v xs
  rw [BoundedFormula.realize_iff]
  exact hiffB M v xs

end BoundedQE

/-- **End to end**: quantifier-free-existential determinism gives quantifier elimination, in the
shape stated in `Milestone0/Encoding.lean`.

Stated at `L : Language.{0, 0}` and `α : Type`, which is the universe level at which
`QECriterion.HasQE` (and the frozen `SpecialTransformations.Milestone0.HasQE`) live. -/
theorem hasQE_of_qfDet {L₀ : FirstOrder.Language.{0, 0}} {T : L₀.Theory}
    (H : ∀ (α : Type) (n : ℕ) (θ : L₀.BoundedFormula α (n + 1)), θ.IsQF →
      ∀ (M N : Theory.ModelType.{0, 0, 0} T) (v : α → M.Carrier)
        (xs : Fin n → M.Carrier) (w : α → N.Carrier) (ys : Fin n → N.Carrier),
        (∀ ψ : L₀.BoundedFormula α n, ψ.IsQF → (ψ.Realize v xs ↔ ψ.Realize w ys)) →
        ((θ.ex).Realize v xs ↔ (θ.ex).Realize w ys)) :
    QECriterion.HasQE (L := L₀) T :=
  QECriterion.HasQE_of_QEExStep (BoundedQE.qeExStep_theoryIff (L₀ := L₀) H)

#print axioms hasQE_of_qfDet

/-! ## The join: Johnson's hypotheses give quantifier elimination -/

namespace HQEDerive

variable {L : FirstOrder.Language.{0, 0}} {T₀ T : L.Theory}

/-- **Johnson's Lemma 2.1.4, syntactically**: prime models over substructures, amalgamation and
`T`-models 1-ec in models of `T₀` give quantifier elimination for `T`, in the frozen shape
(`QECriterion.HasQE`, the same as `SpecialTransformations.Milestone0.HasQE`).

No hypothesis beyond Johnson's three is left over: the last mile `H` is
`HQEDerive.H_of_qfDetermined` (proved above) and the compactness join is `hasQE_of_qfDet`. -/
theorem hasQE_of_johnson (hsub : T₀ ⊆ T)
    (hprime : JohnsonCriterion.HasPrimeModels.{0, 0, 0} T₀ T)
    (hamal : JohnsonCriterion.HasAmalgamation.{0, 0, 0} T₀)
    (h1ec : ∀ (M N : T₀.ModelType.{0, 0, 0}) (f : M ↪[L] N), M ⊨ T →
      JohnsonCriterion.OneECIn f) :
    QECriterion.HasQE (L := L) T :=
  hasQE_of_qfDet (L₀ := L) (T := T) (H_of_qfDetermined hsub hprime hamal h1ec)

end HQEDerive

#print axioms HQEDerive.hasQE_of_johnson
/-
  **Validation of the criterion at ACF**: quantifier elimination for algebraically closed
  fields through Johnson's Lemma 2.1.4 (`Criterion.lean`), with `T₀` = the theory of fields and
  `T` = the theory of algebraically closed fields.  This is Johnson's Claim 2.1.5 together with
  the one-page derivation in Chapter 2 §2.1 of *Fun with Fields*.

  The three hypotheses of the criterion are proved here:
  * prime models over substructures: the fraction field of a domain (`IsFractionRing.lift`);
  * amalgamation: `K₁ ⊗_{K₀} K₂` is nontrivial and a quotient by a maximal ideal is a field
    (`Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain`);
  * 1-ec = algebraically closed: a quantifier-free `K`-definable set in a field extension of an
    algebraically closed `K` is finite or cofinite *with the finite set inside `K`*, because a
    nonzero polynomial over `K` splits over `K` and hence has all its roots in `K`.

  Only import: Mathlib.
-/

open FirstOrder FirstOrder.Language
open FirstOrder.Ring
open Polynomial
open scoped FirstOrder

set_option linter.style.haveILetI false

set_option backward.isDefEq.respectTransparency false

namespace ACFValidation

/-! ## 1. The theory of algebraically closed fields (no characteristic fixed) -/

/-- The theory of algebraically closed fields, as a theory in the language of rings
(characteristic is not fixed: `Theory.ACF p` for a fixed `p` is not the class of 1-ec fields,
since a field of characteristic `0` is 1-ec in the theory of fields and does not model
`Theory.ACF p` for `p > 0`). -/
noncomputable def acf : Theory Language.ring :=
  Theory.field ∪ Field.genericMonicPolyHasRoot '' {n : ℕ | 0 < n}

theorem field_subset_acf : Theory.field ⊆ acf := Set.subset_union_left

instance acfModel {K : Type*} [Field K] [CompatibleRing K] [IsAlgClosed K] : acf.Model K := by
  refine Theory.model_union_iff.2 ⟨inferInstance, ?_⟩
  simp only [Theory.model_iff, Set.mem_image, forall_exists_index, and_imp]
  rintro _ n hn0 rfl
  simp only [Field.realize_genericMonicPolyHasRoot]
  rintro ⟨p, _, rfl⟩
  exact IsAlgClosed.exists_root p
    (ne_of_gt (Polynomial.natDegree_pos_iff_degree_pos.1 hn0))

/-- A model of `acf` (with its ring structure made compatible) is algebraically closed. -/
theorem isAlgClosed_of_model_acf (K : Type*) [Field K] [CompatibleRing K] [h : acf.Model K] :
    IsAlgClosed K := by
  refine IsAlgClosed.of_exists_root _ ?_
  intro p hpm hpi
  have h' : K ⊨ Field.genericMonicPolyHasRoot '' {n : ℕ | 0 < n} :=
    Theory.Model.mono h (by simp [acf])
  simp only [Theory.model_iff, Set.mem_image, forall_exists_index, and_imp] at h'
  have hp := h' _ p.natDegree (Polynomial.natDegree_pos_iff_degree_pos.2
    (Polynomial.degree_pos_of_irreducible hpi)) rfl
  rw [Field.realize_genericMonicPolyHasRoot] at hp
  exact hp ⟨p, hpm, rfl⟩

/-! ## 2. Ring homomorphisms and `Language.ring`-embeddings -/

section Conversions

variable {A B : Type*} [CommRing A] [CommRing B] [CompatibleRing A] [CompatibleRing B]

theorem ringHom_map_fun (f : A →+* B) {n : ℕ} (g : Language.ring.Functions n)
    (x : Fin n → A) : f (Structure.funMap g x) = Structure.funMap g (f ∘ x) := by
  cases g <;> simp

/-- A ring homomorphism is a homomorphism for the language of rings. -/
def homOfRingHom (f : A →+* B) : A →[Language.ring] B where
  toFun := f
  map_fun' := ringHom_map_fun f
  map_rel' := by intro n R; exact isEmptyElim R

/-- An injective ring homomorphism is an embedding for the language of rings. -/
def embeddingOfInjectiveRingHom (f : A →+* B) (hf : Function.Injective f) :
    A ↪[Language.ring] B where
  toFun := f
  inj' := hf
  map_fun' := ringHom_map_fun f
  map_rel' := by intro n R; exact isEmptyElim R

/-- An embedding for the language of rings gives a ring homomorphism. -/
def ringHomOfEmbedding (f : A ↪[Language.ring] B) : A →+* B where
  toFun := f
  map_zero' := by simpa using f.map_fun (zeroFunc) (fun i => i.elim0)
  map_one' := by simpa using f.map_fun (oneFunc) (fun i => i.elim0)
  map_add' x y := by
    have h := f.map_fun (addFunc) ![x, y]
    simpa using h
  map_mul' x y := by
    have h := f.map_fun (mulFunc) ![x, y]
    simpa using h

theorem ringHomOfEmbedding_injective (f : A ↪[Language.ring] B) :
    Function.Injective (ringHomOfEmbedding f) := fun x y h => f.injective h

end Conversions

/-! ## 3. Terms are polynomials, and roots of a polynomial over an algebraically closed field
lie in the field -/

section Poly

variable {K : Type*} [CommRing K]

/-- Read a term of the language of rings (with parameters in `K` and one free variable) in the
free commutative ring on the parameters and the variable. -/
noncomputable def termToFreeCommRing (t : Language.ring.Term (K ⊕ Fin 1)) :
    FreeCommRing (K ⊕ Fin 1) :=
  letI : CompatibleRing (FreeCommRing (K ⊕ Fin 1)) := compatibleRingOfRing _
  t.realize FreeCommRing.of

/-- The polynomial in one variable represented by a term of the language of rings with
parameters in `K` and a single free variable: send the free variable to `X` and the parameters
to constants. -/
noncomputable def termToPoly (t : Language.ring.Term (K ⊕ Fin 1)) : K[X] :=
  FreeCommRing.lift (Sum.elim (fun k => Polynomial.C k) (fun _ => Polynomial.X))
    (termToFreeCommRing t)

variable {N : Type*} [CommRing N] [CompatibleRing N]

theorem realize_eq_lift (t : Language.ring.Term (K ⊕ Fin 1)) (v : K ⊕ Fin 1 → N) :
    t.realize v = FreeCommRing.lift v (termToFreeCommRing t) := by
  letI : CompatibleRing (FreeCommRing (K ⊕ Fin 1)) := compatibleRingOfRing _
  induction t with
  | var s => simp [termToFreeCommRing]
  | func g ts ih =>
    cases g with
    | add => simp only [termToFreeCommRing, Term.realize_func, CompatibleRing.funMap_add,
        map_add, ih]
    | mul => simp only [termToFreeCommRing, Term.realize_func, CompatibleRing.funMap_mul,
        map_mul, ih]
    | neg => simp only [termToFreeCommRing, Term.realize_func, CompatibleRing.funMap_neg,
        map_neg, ih]
    | zero => simp only [termToFreeCommRing, Term.realize_func, CompatibleRing.funMap_zero,
        map_zero]
    | one => simp only [termToFreeCommRing, Term.realize_func, CompatibleRing.funMap_one,
        map_one]

theorem eval₂_termToPoly (f : K →+* N) (t : Language.ring.Term (K ⊕ Fin 1)) (β : N) :
    t.realize (Sum.elim (fun k => f k) (fun _ => β)) = (termToPoly t).eval₂ f β := by
  rw [realize_eq_lift, termToPoly]
  have key : ∀ y : FreeCommRing (K ⊕ Fin 1),
      (FreeCommRing.lift (Sum.elim (fun k => Polynomial.C k) (fun _ => Polynomial.X)) y).eval₂ f β
        = FreeCommRing.lift (Sum.elim (fun k => f k) (fun _ => β)) y := by
    intro y
    induction y using FreeCommRing.induction_on with
    | neg_one => simp
    | of a =>
      cases a with
      | inl k => simp
      | inr i => fin_cases i; simp
    | add x y hx hy => simp [hx, hy]
    | mul x y hx hy => simp [hx, hy]
  exact (key (termToFreeCommRing t)).symm

end Poly

section Roots

variable {K : Type*} [Field K] [IsAlgClosed K]
variable {N : Type*} [Field N]

/-- Over an algebraically closed field, the roots in an extension of a nonzero polynomial are
finite and lie in the base field. -/
theorem finite_rootSet (f : K →+* N) (q : K[X]) (hq : q ≠ 0) :
    {β : N | q.eval₂ f β = 0}.Finite ∧ {β : N | q.eval₂ f β = 0} ⊆ Set.range f := by
  suffices H : ∀ (n : ℕ) (q : K[X]), q.natDegree ≤ n → q ≠ 0 →
      ({β : N | q.eval₂ f β = 0}.Finite ∧
        {β : N | q.eval₂ f β = 0} ⊆ Set.range f) by
    exact H q.natDegree q le_rfl hq
  intro n
  induction n with
  | zero =>
    intro q hn hq
    have hdeg : q.natDegree = 0 := Nat.le_zero.mp hn
    have hqC : q = Polynomial.C (q.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hdeg
    have hc : q.coeff 0 ≠ 0 := by
      intro h; apply hq; rw [hqC, h, Polynomial.C_0]
    have hempty : {β : N | q.eval₂ f β = 0} = ∅ := by
      ext β
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rw [hqC, Polynomial.eval₂_C]
      intro h
      exact hc (f.injective (by simpa using h))
    rw [hempty]
    exact ⟨Set.finite_empty, Set.empty_subset _⟩
  | succ n ih =>
    intro q hn hq
    rcases Nat.eq_zero_or_pos q.natDegree with h0 | hpos
    · have hqC : q = Polynomial.C (q.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero h0
      have hc : q.coeff 0 ≠ 0 := by
        intro h; apply hq; rw [hqC, h, Polynomial.C_0]
      have hempty : {β : N | q.eval₂ f β = 0} = ∅ := by
        ext β
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rw [hqC, Polynomial.eval₂_C]
        intro h
        exact hc (f.injective (by simpa using h))
      rw [hempty]
      exact ⟨Set.finite_empty, Set.empty_subset _⟩
    · have hdeg : q.degree ≠ 0 := by
        rw [Polynomial.degree_eq_natDegree hq]
        simpa using hpos.ne'
      obtain ⟨r, hr⟩ := IsAlgClosed.exists_root q hdeg
      obtain ⟨q₁, hq₁⟩ := (Polynomial.dvd_iff_isRoot (p := q)).2 hr
      have hq₁ne : q₁ ≠ 0 := by
        rintro rfl; rw [mul_zero] at hq₁; exact hq hq₁
      have hdegq : q.natDegree = q₁.natDegree + 1 := by
        rw [hq₁, Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero r) hq₁ne,
          Polynomial.natDegree_X_sub_C, add_comm]
      have hle : q₁.natDegree ≤ n := by omega
      obtain ⟨hfin, hsub⟩ := ih q₁ hle hq₁ne
      have hset : {β : N | q.eval₂ f β = 0}
          = {f r} ∪ {β : N | q₁.eval₂ f β = 0} := by
        ext β
        simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff]
        rw [hq₁]
        simp only [Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_X,
          Polynomial.eval₂_C]
        constructor
        · intro h
          rcases mul_eq_zero.mp h with h' | h'
          · exact Or.inl (sub_eq_zero.mp h')
          · exact Or.inr h'
        · rintro (h' | h')
          · rw [h', sub_self, zero_mul]
          · rw [h', mul_zero]
      rw [hset]
      exact ⟨(Set.finite_singleton _).union hfin,
        Set.union_subset (fun x hx => ⟨r, hx.symm⟩) hsub⟩

end Roots

/-! ## 4. Claim 2.1.5: a quantifier-free definable set over an algebraically closed field

The substantive half: if `K` is algebraically closed and `f : K →+* N` is an injection into a
field, every non-empty quantifier-free `K`-definable subset of `N` in one variable meets `K`. -/

section OneEC

variable {K : Type*} [Field K] [IsAlgClosed K]
variable {N : Type*} [Field N] [CompatibleRing N]

/-- The Boolean algebra of "good" subsets of an extension `N` of `K`: finite sets inside `K`, or
complements of such.  Johnson's Claim 2.1.5 is that quantifier-free `K`-definable sets are
good; the point of the notion is that a non-empty good set meets `K`. -/
def Good (f : K →+* N) (S : Set N) : Prop :=
  (S.Finite ∧ S ⊆ Set.range f) ∨ (Sᶜ.Finite ∧ Sᶜ ⊆ Set.range f)

theorem good_empty (f : K →+* N) : Good f ∅ :=
  Or.inl ⟨Set.finite_empty, Set.empty_subset _⟩

theorem good_compl {f : K →+* N} {S : Set N} (h : Good f S) : Good f Sᶜ := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inr ⟨by simpa using h1, by simpa using h2⟩
  · exact Or.inl ⟨by simpa using h1, by simpa using h2⟩

theorem good_univ (f : K →+* N) : Good f (Set.univ : Set N) := by
  simpa using good_compl (good_empty f)

theorem good_union {f : K →+* N} {S T : Set N} (hS : Good f S) (hT : Good f T) :
    Good f (S ∪ T) := by
  have hsub : (S ∪ T)ᶜ ⊆ Sᶜ := Set.compl_subset_compl.mpr (Set.subset_union_left)
  have hsub' : (S ∪ T)ᶜ ⊆ Tᶜ := Set.compl_subset_compl.mpr (Set.subset_union_right)
  rcases hS with ⟨hS1, hS2⟩ | ⟨hS1, hS2⟩
  · rcases hT with ⟨hT1, hT2⟩ | ⟨hT1, hT2⟩
    · exact Or.inl ⟨hS1.union hT1, Set.union_subset hS2 hT2⟩
    · exact Or.inr ⟨hT1.subset hsub', fun x hx => hT2 (hsub' hx)⟩
  · rcases hT with ⟨hT1, hT2⟩ | ⟨hT1, hT2⟩
    · exact Or.inr ⟨hS1.subset hsub, fun x hx => hS2 (hsub hx)⟩
    · exact Or.inr ⟨hS1.subset hsub, fun x hx => hS2 (hsub hx)⟩

/-- A non-empty good set meets the image of `K` (this is where infinitude of `K` is used). -/
theorem exists_mem_range_of_good {f : K →+* N} {S : Set N} (hS : Good f S)
    (hne : S.Nonempty) : ∃ k : K, f k ∈ S := by
  rcases hS with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · obtain ⟨a, ha⟩ := hne
    obtain ⟨k, hk⟩ := h2 ha
    exact ⟨k, hk ▸ ha⟩
  · obtain ⟨a, ha⟩ := hne
    have hcoe : ((h1.toFinset : Finset N) : Set N) = Sᶜ := h1.coe_toFinset
    have hpre : (f ⁻¹' Sᶜ).Finite := by
      have hsub : f ⁻¹' Sᶜ ⊆ ((h1.toFinset.preimage f (fun x _ y _ h => f.injective h) : Finset K) : Set K) := by
        intro k hk
        simp only [Set.mem_preimage] at hk
        refine Finset.mem_preimage.mpr ?_
        have hmem : f k ∈ (h1.toFinset : Set N) := by rw [hcoe]; exact hk
        simpa using hmem
      exact (h1.toFinset.preimage f (fun x _ y _ h => f.injective h)).finite_toSet.subset hsub
    obtain ⟨k, hk⟩ := Infinite.exists_notMem_finset
      (h1.toFinset.preimage f (fun x _ y _ h => f.injective h))
    exact ⟨k, by simpa using hk⟩

/-- **Quantifier-free definable sets over an algebraically closed field are good.** -/
theorem good_solSet {f : K →+* N} (φ : Language.ring.BoundedFormula K 1) (hφ : φ.IsQF) :
    Good f {a : N | φ.Realize (fun k => f k) (fun _ => a)} := by
  refine BoundedFormula.IsQF.recOn
    (motive := fun ψ _ => Good f {a : N | ψ.Realize (fun k => f k) (fun _ => a)}) hφ ?_ ?_ ?_
  · -- `⊥`
    have hset : {a : N | (BoundedFormula.falsum : Language.ring.BoundedFormula K 1).Realize
        (fun k => f k) (fun _ => a)} = ∅ := by
      ext a
      exact ⟨fun h => h, fun h => h.elim⟩
    rw [hset]; exact good_empty f
  · -- atomic
    intro ψ ha
    cases ha with
    | equal t₁ t₂ =>
      set p : K[X] := termToPoly t₁ - termToPoly t₂ with hp
      have hset : {a : N | (Term.bdEqual t₁ t₂).Realize (fun k => f k) (fun _ => a)}
          = {a : N | p.eval₂ f a = 0} := by
        ext a
        simp only [BoundedFormula.realize_bdEqual, Set.mem_setOf_eq, hp]
        rw [eval₂_termToPoly f t₁ a, eval₂_termToPoly f t₂ a,
          Polynomial.eval₂_sub, sub_eq_zero]
      rw [hset]
      by_cases hp0 : p = 0
      · have huniv : {a : N | p.eval₂ f a = 0} = Set.univ := by
          ext a; simp [hp0]
        rw [huniv]; exact good_univ f
      · exact Or.inl (finite_rootSet f p hp0)
    | rel R ts => exact isEmptyElim R
  · -- `⟹`
    intro φ₁ φ₂ _ _ ih1 ih2
    have hset : {a : N | (φ₁.imp φ₂).Realize (fun k => f k) (fun _ => a)}
        = {a : N | φ₁.Realize (fun k => f k) (fun _ => a)}ᶜ
          ∪ {a : N | φ₂.Realize (fun k => f k) (fun _ => a)} := by
      ext a
      simp only [BoundedFormula.realize_imp, Set.mem_setOf_eq, Set.mem_union,
        Set.mem_compl_iff]
      tauto
    rw [hset]
    exact good_union (good_compl ih1) ih2

/-- **Claim 2.1.5, hard direction**: an algebraically closed field is 1-ec in every field
extension, for quantifier-free formulas in one variable. -/
theorem exists_solution_in_range {f : K →+* N} (φ : Language.ring.BoundedFormula K 1)
    (hφ : φ.IsQF) (h : ∃ a : N, φ.Realize (fun k => f k) (fun _ => a)) :
    ∃ k : K, φ.Realize (fun k' => f k') (fun _ => f k) := by
  obtain ⟨k, hk⟩ := exists_mem_range_of_good (good_solSet φ hφ) ⟨_, h.choose_spec⟩
  exact ⟨k, hk⟩

end OneEC


/-! ## 5. The criterion of Lemma 2.1.4 (self-contained copy of `Criterion.lean`)

`Criterion.lean` proves Johnson's Lemma 2.1.4 for an arbitrary language, with
`import Mathlib` as its only import.  It is copied here so that this file, too, has
`import Mathlib` as its only import and can instantiate the criterion at ACF. -/

open FirstOrder FirstOrder.Language
open scoped FirstOrder

set_option linter.style.haveILetI false

namespace JohnsonCriterion

universe u v w w'

variable {L : FirstOrder.Language.{u, v}}

/-! ## 1. Quantifier-free formulas are preserved and reflected by embeddings

Mathlib has `StrongHomClass.realize_boundedFormula`, but only for `EquivLike` maps (surjective
ones).  For a general embedding only quantifier-free formulas are preserved, and that lemma is
not in Mathlib.  (The same lemma is `embedding_realize_isQF` in
`QE/Semantics_saturation.lean`; it is restated here so that the file is self-contained.) -/

section QFPreserve

variable {M : Type w} {N : Type w'} [L.Structure M] [L.Structure N]

theorem embedding_realize_isAtomic (g : M ↪[L] N) {α : Type*} {n : ℕ}
    {φ : L.BoundedFormula α n} (h : φ.IsAtomic) (v : α → M) (xs : Fin n → M) :
    φ.Realize (fun a => g (v a)) (fun i => g (xs i)) ↔ φ.Realize v xs := by
  have hcomp : (Sum.elim (fun a => g (v a)) (fun i => g (xs i)))
      = (fun s => g (Sum.elim v xs s)) := by
    funext s; cases s <;> rfl
  have key : ∀ t : L.Term (α ⊕ Fin n),
      t.realize (Sum.elim (fun a => g (v a)) (fun i => g (xs i)))
        = g (t.realize (Sum.elim v xs)) := by
    intro t; rw [hcomp]; exact HomClass.realize_term g
  cases h with
  | equal t₁ t₂ =>
    simp only [BoundedFormula.realize_bdEqual]
    rw [key t₁, key t₂, g.injective.eq_iff]
  | rel R ts =>
    simp only [BoundedFormula.realize_rel]
    have hrs : (fun i => (ts i).realize (Sum.elim (fun a => g (v a)) (fun i => g (xs i))))
        = (fun i => g ((ts i).realize (Sum.elim v xs))) := by
      funext i; exact key (ts i)
    rw [hrs]
    exact StrongHomClass.map_rel (r := R) g (fun i => (ts i).realize (Sum.elim v xs))

theorem embedding_realize_isQF (g : M ↪[L] N) {α : Type*} {n : ℕ}
    {φ : L.BoundedFormula α n} (h : φ.IsQF) :
    ∀ (v : α → M) (xs : Fin n → M),
      φ.Realize (fun a => g (v a)) (fun i => g (xs i)) ↔ φ.Realize v xs := by
  induction h with
  | falsum => intro v xs; exact Iff.rfl
  | of_isAtomic ha => exact fun v xs => embedding_realize_isAtomic g ha v xs
  | imp _ _ ih1 ih2 => intro v xs; simp only [BoundedFormula.realize_imp, ih1 v xs, ih2 v xs]

end QFPreserve

/-! ## 2. Substituting parameters for terms preserves quantifier-freeness

Needed to move a formula's parameters along an embedding: `OneECIn` is stated for parameters in
the model, while the comparison below happens over a smaller base `S`. -/

section Subst

theorem isAtomic_subst {α β : Type*} {n : ℕ} {φ : L.BoundedFormula α n} (h : φ.IsAtomic)
    (tf : α → L.Term β) : (φ.subst tf).IsAtomic := by
  cases h with
  | equal t₁ t₂ => exact BoundedFormula.IsAtomic.equal _ _
  | rel R ts => exact BoundedFormula.IsAtomic.rel _ _

theorem isQF_subst {α β : Type*} {n : ℕ} {φ : L.BoundedFormula α n} (h : φ.IsQF)
    (tf : α → L.Term β) : (φ.subst tf).IsQF := by
  induction h with
  | falsum => exact BoundedFormula.isQF_bot
  | of_isAtomic ha => exact BoundedFormula.IsAtomic.isQF (isAtomic_subst ha tf)
  | imp _ _ ih1 ih2 => exact ih1.imp ih2

end Subst

/-! ## 3. The three hypotheses of Lemma 2.1.4

All three are stated for models of `T₀` bundled as `T₀.ModelType`; the models of `T` are
carried along by an explicit hypothesis `⊨ T`, which is legitimate because `T₀ ⊆ T` in every
application (models of `T` are models of `T₀`, so no generality is lost and no coercion
between bundled models of different theories is ever needed). -/

section Criterion

/-- **1-ec** (Johnson, Definition 2.1.3): `S` is 1-ec in `N` along the embedding `i` if every
non-empty quantifier-free `S`-definable subset of `N` in one variable meets `S`. -/
def OneECIn {S : Type w} {N : Type w'} [L.Structure S] [L.Structure N] (i : S ↪[L] N) : Prop :=
  ∀ (φ : L.BoundedFormula S 1), φ.IsQF →
    (∃ a, φ.Realize (fun s => i s) (fun _ => a)) →
      ∃ s : S, φ.Realize (fun s' => i s') (fun _ => i s)

/-- **Prime models over substructures** (Johnson, Definition 2.1.1), in the restricted form in
which the definition is used in the proof: every structure `S` that embeds into a model of `T`
has an extension `S'` modelling `T₀` which embeds into every model of `T₀` under `S`.  (In
Johnson's definition the last quantifier runs over all models of `T₀`; here only over models
that are themselves models of `T`, which is all the proof needs.) -/
def HasPrimeModels (T₀ T : L.Theory) : Prop :=
  ∀ (S : Type w) [L.Structure S],
    (∃ (M : T₀.ModelType.{u, v, w}), M ⊨ T ∧ Nonempty (S ↪[L] M)) →
    ∃ (S' : T₀.ModelType.{u, v, w}) (e : S ↪[L] S'),
      ∀ (N : T₀.ModelType.{u, v, w}) (f : S ↪[L] N), ∃ g : S' ↪[L] N, g.comp e = f

/-- **The amalgamation property** (Johnson, Definition 2.1.2). -/
def HasAmalgamation (T : L.Theory) : Prop :=
  ∀ (A B C : T.ModelType.{u, v, w}) (i : A ↪[L] B) (j : A ↪[L] C),
    ∃ (D : T.ModelType.{u, v, w}) (i' : B ↪[L] D) (j' : C ↪[L] D), i'.comp i = j'.comp j

/-- The **conclusion of Lemma 2.1.4**, in the semantic form which the proof establishes:
quantifier-free definable sets over a base have, in any two models of `T`, the same
one-variable existential theory. -/
theorem qfDetermined {T₀ T : L.Theory} (hsub : T₀ ⊆ T)
    (hprime : HasPrimeModels.{u, v, w} T₀ T) (hamal : HasAmalgamation.{u, v, w} T₀)
    (h1ec : ∀ (M N : T₀.ModelType.{u, v, w}) (f : M ↪[L] N), M ⊨ T → OneECIn f)
    (S : Type w) [L.Structure S] (M N : T₀.ModelType.{u, v, w}) (hM : M ⊨ T) (hN : N ⊨ T)
    (i : S ↪[L] M) (j : S ↪[L] N) (φ : L.BoundedFormula S 1) (hφ : φ.IsQF) :
    (∃ a : M, φ.Realize (fun s => i s) (fun _ => a)) ↔
      ∃ b : N, φ.Realize (fun s => j s) (fun _ => b) := by
  -- the prime model of `T₀` over the base `S`
  obtain ⟨S', e, huniv⟩ := hprime S ⟨M, hM, ⟨i⟩⟩
  obtain ⟨gM, hgM⟩ := huniv M i
  obtain ⟨gN, hgN⟩ := huniv N j
  -- amalgamate the two embeddings of `S'` into `M` and `N`
  obtain ⟨D, kM, kN, hcomm⟩ := hamal S' M N gM gN
  -- the formula `φ`, with its parameters moved along the embedding of `S'` into `N`
  set ψ : L.BoundedFormula N 1 := φ.subst (fun s => Term.var (gN.comp e s)) with hψdef
  have hψqf : ψ.IsQF := isQF_subst hφ _
  have hMN : ∀ s, kN ((gN.comp e) s) = kM ((gM.comp e) s) := by
    intro s
    have h := congrArg (fun g : ↑S' ↪[L] ↑D => g (e s)) hcomm
    simpa only [FirstOrder.Language.Embedding.comp_apply] using h.symm
  have hMi : ∀ s, (gM.comp e) s = i s := by
    intro s
    exact congrArg (fun g : S ↪[L] ↑M => g s) hgM
  have hψreal : ∀ a : M, ψ.Realize (fun n => kN n) (fun _ => kM a) ↔
      φ.Realize (fun s => i s) (fun _ => a) := by
    intro a
    rw [hψdef, BoundedFormula.realize_subst]
    simp only [Term.realize_var]
    have hfun : (fun s => kN ((gN.comp e) s)) = (fun s => kM (i s)) := by
      funext s
      rw [hMN s, hMi s]
    rw [hfun]
    exact embedding_realize_isQF kM hφ (fun s => i s) (fun _ => a)
  have hψunfold : ∀ a : N, ψ.Realize (fun n => kN n) (fun _ => kN a) ↔
      φ.Realize (fun s => kN ((gN.comp e) s)) (fun _ => kN a) := by
    intro a
    rw [hψdef, BoundedFormula.realize_subst]
    simp only [Term.realize_var]
  constructor
  · rintro ⟨a, ha⟩
    -- transport the witness to `D`, then use that `N` is 1-ec in `D`
    have hD : ψ.Realize (fun n => kN n) (fun _ => kM a) := (hψreal a).2 ha
    obtain ⟨n₀, hn₀⟩ := h1ec N D kN hN ψ hψqf ⟨kM a, hD⟩
    have h1 : φ.Realize (fun s => kN ((gN.comp e) s)) (fun _ => kN n₀) := (hψunfold n₀).1 hn₀
    have h2 : φ.Realize (fun s => (gN.comp e) s) (fun _ => n₀) :=
      (embedding_realize_isQF kN hφ (fun s => (gN.comp e) s) (fun _ => n₀)).1 h1
    exact ⟨n₀, by rwa [hgN] at h2⟩
  · rintro ⟨b, hb⟩
    -- transport the witness to `D`, now with the parameters written via `M`
    have hb' : φ.Realize (fun s => (gN.comp e) s) (fun _ => b) := by
      rwa [← hgN] at hb
    have hD : φ.Realize (fun s => kN ((gN.comp e) s)) (fun _ => kN b) :=
      (embedding_realize_isQF kN hφ (fun s => (gN.comp e) s) (fun _ => b)).2 hb'
    have hfun : (fun s => kM (i s)) = (fun s => kN ((gN.comp e) s)) := by
      funext s; rw [hMN s, hMi s]
    set χ : L.BoundedFormula M 1 := φ.subst (fun s => Term.var (i s)) with hχdef
    have hχqf : χ.IsQF := isQF_subst hφ _
    have hD' : χ.Realize (fun m => kM m) (fun _ => kN b) := by
      rw [hχdef, BoundedFormula.realize_subst]
      simp only [Term.realize_var]
      rw [hfun]
      exact hD
    -- `M` is a model of `T`, hence 1-ec in every model of `T₀`, in particular in `D`
    obtain ⟨m₀, hm₀⟩ := h1ec M D kM hM χ hχqf ⟨kN b, hD'⟩
    refine ⟨m₀, ?_⟩
    rw [hχdef, BoundedFormula.realize_subst] at hm₀
    simp only [Term.realize_var] at hm₀
    exact (embedding_realize_isQF kM hφ (fun s => i s) (fun _ => m₀)).1 hm₀

end Criterion

end JohnsonCriterion


/-! ## 6. Discharging the hypotheses at ACF -/


section Hypotheses

open scoped TensorProduct

/-! ### 6.1 Models of `acf` are 1-ec in every field extension (Claim 2.1.5, via §4) -/

theorem oneEC_field_acf (M N : Theory.field.ModelType) (f : M ↪[Language.ring] N)
    (hM : M ⊨ acf) : JohnsonCriterion.OneECIn f := by
  letI : Field M := FirstOrder.Field.fieldOfModelField M
  letI : CompatibleRing M := FirstOrder.Field.compatibleRingOfModelField M
  letI : Field N := FirstOrder.Field.fieldOfModelField N
  letI : CompatibleRing N := FirstOrder.Field.compatibleRingOfModelField N
  haveI : acf.Model M := hM
  haveI : IsAlgClosed M := isAlgClosed_of_model_acf M
  intro φ hφ h
  exact exists_solution_in_range (f := ringHomOfEmbedding f) φ hφ h

/-! ### 6.2 Amalgamation of the theory of fields (§2.2: `K₁ ⊗_{K₀} K₂`) -/

universe u

theorem ringHom_injective_of_field {F R : Type*} [Field F] [CommRing R] [Nontrivial R]
    (g : F →+* R) : Function.Injective g := by
  intro x y hxy
  have h : g (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  have h' : x - y = 0 := by
    by_contra hne
    have hunit : IsUnit (x - y) := isUnit_iff_ne_zero.mpr hne
    have hunit' : IsUnit (g (x - y)) := hunit.map g
    rw [h] at hunit'
    exact not_isUnit_zero hunit'
  exact sub_eq_zero.mp h'

theorem amalgamation_field (A B C : Theory.field.ModelType.{0, 0, u})
    (i : A ↪[Language.ring] B) (j : A ↪[Language.ring] C) :
    ∃ (D : Theory.field.ModelType.{0, 0, u}) (i' : B ↪[Language.ring] D)
      (j' : C ↪[Language.ring] D), i'.comp i = j'.comp j := by
  letI : Field A := FirstOrder.Field.fieldOfModelField A
  letI : CompatibleRing A := FirstOrder.Field.compatibleRingOfModelField A
  letI : Field B := FirstOrder.Field.fieldOfModelField B
  letI : CompatibleRing B := FirstOrder.Field.compatibleRingOfModelField B
  letI : Field C := FirstOrder.Field.fieldOfModelField C
  letI : CompatibleRing C := FirstOrder.Field.compatibleRingOfModelField C
  let fA : A →+* B := ringHomOfEmbedding i
  let fB : A →+* C := ringHomOfEmbedding j
  letI : Algebra A B := fA.toAlgebra
  letI : Algebra A C := fB.toAlgebra
  have hfA : Function.Injective (algebraMap A B) := by
    rw [RingHom.algebraMap_toAlgebra]
    exact ringHomOfEmbedding_injective i
  have hfB : Function.Injective (algebraMap A C) := by
    rw [RingHom.algebraMap_toAlgebra]
    exact ringHomOfEmbedding_injective j
  haveI : Nontrivial (B ⊗[A] C) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain A B C hfA hfB
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (B ⊗[A] C)
  haveI : m.IsMaximal := hm
  letI : Field ((B ⊗[A] C) ⧸ m) := Ideal.Quotient.field m
  letI : CompatibleRing ((B ⊗[A] C) ⧸ m) := compatibleRingOfRing _
  let D : Theory.field.ModelType.{0, 0, u} :=
    Theory.ModelType.of Theory.field ((B ⊗[A] C) ⧸ m)
  let iB : B →+* ((B ⊗[A] C) ⧸ m) :=
    (Ideal.Quotient.mk m).comp (Algebra.TensorProduct.includeLeftRingHom (R := A))
  let jC : C →+* ((B ⊗[A] C) ⧸ m) :=
    (Ideal.Quotient.mk m).comp (Algebra.TensorProduct.includeRight.toRingHom)
  have hiB : Function.Injective iB := ringHom_injective_of_field iB
  have hjC : Function.Injective jC := ringHom_injective_of_field jC
  refine ⟨D, embeddingOfInjectiveRingHom iB hiB, embeddingOfInjectiveRingHom jC hjC, ?_⟩
  ext a
  show iB (fA a) = jC (fB a)
  have h1 : iB (fA a) = Ideal.Quotient.mk m (algebraMap A B a ⊗ₜ[A] 1) := by
    simp [iB, Algebra.TensorProduct.includeLeft_apply, RingHom.algebraMap_toAlgebra]
  have h2 : jC (fB a) = Ideal.Quotient.mk m (1 ⊗ₜ[A] algebraMap A C a) := by
    simp [jC, Algebra.TensorProduct.includeRight_apply, RingHom.algebraMap_toAlgebra]
  rw [h1, h2, Algebra.TensorProduct.tmul_one_eq_one_tmul]

end Hypotheses


/-! ## 7. Quantifier elimination for ACF through the criterion

The instance of Lemma 2.1.4 used here takes the **base to be a model of `T₀`** (a field): that
is the standard formulation of quantifier elimination for ACF (`E` a field, `M`, `N`
algebraically closed extensions of `E`), and for such bases the prime-model hypothesis of
Definition 2.1.1 is trivial (`S' = S`).  The general hypothesis — prime models over *arbitrary*
substructures of models of `T`, i.e. `S' = Frac(S)` for an abstract integral domain `S` in the
language of rings — is not discharged in this file; see the notes at the end. -/

namespace JohnsonCriterion

universe uq vq wq

/-- Lemma 2.1.4 with the base required to be a model of `T₀` (for such a base the
prime-model hypothesis is automatic). -/
theorem qfDetermined_base_model {L : FirstOrder.Language.{uq, vq}}
    {T₀ T : L.Theory}
    (hamal : HasAmalgamation.{uq, vq, wq} T₀)
    (h1ec : ∀ (M N : T₀.ModelType.{uq, vq, wq}) (f : M ↪[L] N), M ⊨ T → OneECIn f)
    (E : T₀.ModelType.{uq, vq, wq}) (M N : T₀.ModelType.{uq, vq, wq}) (hM : M ⊨ T) (hN : N ⊨ T)
    (i : E ↪[L] M) (j : E ↪[L] N) (φ : L.BoundedFormula E 1) (hφ : φ.IsQF) :
    (∃ a : M, φ.Realize (fun s => i s) (fun _ => a)) ↔
      ∃ b : N, φ.Realize (fun s => j s) (fun _ => b) := by
  obtain ⟨D, kM, kN, hcomm⟩ := hamal E M N i j
  set ψ : L.BoundedFormula N 1 := φ.subst (fun s => Term.var (j s)) with hψdef
  have hψqf : ψ.IsQF := isQF_subst hφ _
  have hMN : ∀ s : E, kN (j s) = kM (i s) := by
    intro s
    have h := congrArg (fun g : E ↪[L] D => g s) hcomm
    simpa only [FirstOrder.Language.Embedding.comp_apply] using h.symm
  have hψunfold : ∀ d : D, ψ.Realize (fun n => kN n) (fun _ => d) ↔
      φ.Realize (fun s => kN (j s)) (fun _ => d) := by
    intro d
    rw [hψdef, BoundedFormula.realize_subst]
    simp only [Term.realize_var]
  have hψreal : ∀ a : M, ψ.Realize (fun n => kN n) (fun _ => kM a) ↔
      φ.Realize (fun s => i s) (fun _ => a) := by
    intro a
    rw [hψunfold]
    have hfun : (fun s => kN (j s)) = (fun s => kM (i s)) := funext hMN
    rw [hfun]
    exact embedding_realize_isQF kM hφ (fun s => i s) (fun _ => a)
  constructor
  · rintro ⟨a, ha⟩
    have hD : ψ.Realize (fun n => kN n) (fun _ => kM a) := (hψreal a).2 ha
    obtain ⟨n₀, hn₀⟩ := h1ec N D kN hN ψ hψqf ⟨kM a, hD⟩
    have h1 : φ.Realize (fun s => kN (j s)) (fun _ => kN n₀) := (hψunfold (kN n₀)).1 hn₀
    have h2 : φ.Realize (fun s => j s) (fun _ => n₀) :=
      (embedding_realize_isQF kN hφ (fun s => j s) (fun _ => n₀)).1 h1
    exact ⟨n₀, h2⟩
  · rintro ⟨b, hb⟩
    have hb' : φ.Realize (fun s => kN (j s)) (fun _ => kN b) :=
      (embedding_realize_isQF kN hφ (fun s => j s) (fun _ => b)).2 hb
    have hfun : (fun s => kM (i s)) = (fun s => kN (j s)) := by
      funext s; exact (hMN s).symm
    set χ : L.BoundedFormula M 1 := φ.subst (fun s => Term.var (i s)) with hχdef
    have hχqf : χ.IsQF := isQF_subst hφ _
    have hD' : χ.Realize (fun m => kM m) (fun _ => kN b) := by
      rw [hχdef, BoundedFormula.realize_subst]
      simp only [Term.realize_var]
      rw [hfun]
      exact hb'
    obtain ⟨m₀, hm₀⟩ := h1ec M D kM hM χ hχqf ⟨kN b, hD'⟩
    refine ⟨m₀, ?_⟩
    rw [hχdef, BoundedFormula.realize_subst] at hm₀
    simp only [Term.realize_var] at hm₀
    exact (embedding_realize_isQF kM hφ (fun s => i s) (fun _ => m₀)).1 hm₀

end JohnsonCriterion


universe uacf

theorem hasAmalgamation_field : JohnsonCriterion.HasAmalgamation Theory.field :=
  fun A B C i j => amalgamation_field A B C i j

/-- **Quantifier elimination for algebraically closed fields**, in the form the criterion
yields: over any base field `E`, the one-variable quantifier-free definable sets have the same
existential theory in any two algebraically closed fields containing `E`. -/
theorem acf_qfDetermined (E M N : Theory.field.ModelType.{0, 0, uacf})
    (hM : M ⊨ acf) (hN : N ⊨ acf)
    (i : E ↪[Language.ring] M) (j : E ↪[Language.ring] N)
    (φ : Language.ring.BoundedFormula E 1) (hφ : φ.IsQF) :
    (∃ a : M, φ.Realize (fun s => i s) (fun _ => a)) ↔
      ∃ b : N, φ.Realize (fun s => j s) (fun _ => b) :=
  JohnsonCriterion.qfDetermined_base_model hasAmalgamation_field oneEC_field_acf
    E M N hM hN i j φ hφ


/-- **Prime models over field bases**: for a base that is itself a model of `Theory.field`, the
prime-model hypothesis of Definition 2.1.1 is trivially satisfied (`S' = S`).  This is the form
of the hypothesis used by `qfDetermined_base_model`. -/
theorem primeModels_over_field_model (S : Theory.field.ModelType.{0, 0, uacf})
    (M : Theory.field.ModelType.{0, 0, uacf}) (hM : M ⊨ acf)
    (i : S ↪[Language.ring] M) :
    ∃ (S' : Theory.field.ModelType.{0, 0, uacf}) (e : S ↪[Language.ring] S'),
      ∀ (N : Theory.field.ModelType.{0, 0, uacf}) (f : S ↪[Language.ring] N),
        ∃ g : S' ↪[Language.ring] N, g.comp e = f :=
  ⟨S, FirstOrder.Language.Embedding.refl Language.ring S, fun N f =>
    ⟨f, by simp only [FirstOrder.Language.Embedding.comp_refl]⟩⟩

/-- **The general form of Lemma 2.1.4 at ACF**, conditional on the one hypothesis not discharged
here: prime models over *arbitrary* substructures of models of `T` (Johnson's Definition 2.1.1).
Granting it, the criterion gives quantifier-free type determinism over an arbitrary base
structure `S`, not merely over a base field. -/
theorem acf_qfDetermined_general
    (hprime : JohnsonCriterion.HasPrimeModels.{0, 0, uacf} Theory.field acf)
    (S : Type uacf) [Language.ring.Structure S]
    (M N : Theory.field.ModelType.{0, 0, uacf}) (hM : M ⊨ acf) (hN : N ⊨ acf)
    (i : S ↪[Language.ring] M) (j : S ↪[Language.ring] N)
    (φ : Language.ring.BoundedFormula S 1) (hφ : φ.IsQF) :
    (∃ a : M, φ.Realize (fun s => i s) (fun _ => a)) ↔
      ∃ b : N, φ.Realize (fun s => j s) (fun _ => b) :=
  JohnsonCriterion.qfDetermined field_subset_acf hprime hasAmalgamation_field
    oneEC_field_acf S M N hM hN i j φ hφ

#print axioms ACFValidation.acf_qfDetermined
#print axioms ACFValidation.exists_solution_in_range
#print axioms JohnsonCriterion.qfDetermined

end ACFValidation

/-! ## The ACF instantiation: `HasQE acf` from the prime-model hypothesis alone -/

namespace HQEDerive

/-- **Quantifier elimination for algebraically closed fields** via Johnson's Lemma 2.1.4, with
every hypothesis discharged except the prime-model statement
`JohnsonCriterion.HasPrimeModels Theory.field acf` (gap B).

The three inputs are `ACFValidation.field_subset_acf`, `ACFValidation.amalgamation_field`
(Johnson §2.2, tensor product of fields) and `ACFValidation.oneEC_field_acf`
(Johnson Claim 2.1.5: an algebraically closed field is 1-ec in every field extension). The last
mile `H` is `HQEDerive.H_of_qfDetermined` and the compactness join is `hasQE_of_qfDet`. -/
theorem HasQE_acf_of_primeModels
    (hprime : JohnsonCriterion.HasPrimeModels.{0, 0, 0} Theory.field ACFValidation.acf) :
    QECriterion.HasQE (L := Language.ring) ACFValidation.acf :=
  hasQE_of_johnson (L := Language.ring) ACFValidation.field_subset_acf hprime
    (fun A B C i j => ACFValidation.amalgamation_field A B C i j)
    (fun M N f hM => ACFValidation.oneEC_field_acf M N f hM)

end HQEDerive

#print axioms HQEDerive.HasQE_acf_of_primeModels

namespace HQEDerive

/-- The prime-model hypothesis in the namespace where `QE/ACF_validation.lean` states its own
copy of the criterion (`ACFValidation.JohnsonCriterion`), plugged into the one used by
`H_of_qfDetermined` (top-level `JohnsonCriterion`).  The two definitions have the same body, so
this is a definitional-equality bridge: whichever form gap (B) is proved in, it plugs in. -/
theorem hasPrimeModels_of_ACFValidation
    (h : ACFValidation.JohnsonCriterion.HasPrimeModels.{0, 0, 0} Theory.field ACFValidation.acf) :
    JohnsonCriterion.HasPrimeModels.{0, 0, 0} Theory.field ACFValidation.acf :=
  h

/-- **Quantifier elimination for `acf`, in the frozen shape of `Milestone0/Encoding.lean`**:
every `Language.ring`-formula is `acf`-equivalent to a quantifier-free one, stated with `⊨ᵇ`
and `⇔` as in the frozen `SpecialTransformations.Milestone0.HasQE`.  (This is the same
proposition as `HasQE_acf_of_primeModels`: `Theory.Iff T φ ψ` *is* `T ⊨ᵇ (φ ⇔ ψ)`.) -/
theorem HasQE_acf_frozen_of_primeModels
    (hprime : JohnsonCriterion.HasPrimeModels.{0, 0, 0} Theory.field ACFValidation.acf) :
    ∀ (α : Type) (φ : Language.ring.Formula α),
      ∃ ψ : Language.ring.Formula α, ψ.IsQF ∧ ACFValidation.acf ⊨ᵇ (φ ⇔ ψ) :=
  HasQE_acf_of_primeModels hprime

/-- The same, as `ShoenfieldQE.HasQE` (the frozen shape at general `α`). -/
theorem hasQE_frozen_acf_of_primeModels
    (hprime : JohnsonCriterion.HasPrimeModels.{0, 0, 0} Theory.field ACFValidation.acf) :
    ShoenfieldQE.HasQE (L := Language.ring) ACFValidation.acf :=
  HasQE_acf_of_primeModels hprime

end HQEDerive

#print axioms HQEDerive.HasQE_acf_frozen_of_primeModels
#print axioms HQEDerive.hasQE_frozen_acf_of_primeModels

namespace HQEDerive

/-- Bounded quantifier elimination for `acf` from the same single hypothesis: every bounded
formula with `n` bound variables is `acf`-equivalent to a quantifier-free one. -/
theorem HasQEb_acf_of_primeModels
    (hprime : JohnsonCriterion.HasPrimeModels.{0, 0, 0} Theory.field ACFValidation.acf) :
    QECriterion.HasQEb (L := Language.ring) ACFValidation.acf :=
  QECriterion.hasQEb_of_QEAllStep (QECriterion.QEAllStep_iff_QEExStep.2
    (BoundedQE.qeExStep_theoryIff (L₀ := Language.ring)
      (H_of_qfDetermined ACFValidation.field_subset_acf hprime
        (fun A B C i j => ACFValidation.amalgamation_field A B C i j)
        (fun M N f hM => ACFValidation.oneEC_field_acf M N f hM))))

end HQEDerive

#print axioms HQEDerive.HasQEb_acf_of_primeModels

/-! ## 4. Gap (B): prime models over substructures of models of `acf`

The content of this section is the compiled file `.ultramath/smw0bll3t/m3/PrimeModels_full.lean`
of member m3 of this swarm, copied verbatim and wrapped in `namespace M3` so that its own copies
of `acf` and of `JohnsonCriterion.HasPrimeModels` do not clash with the ones used above.  Both
copies are the same definitions, so the bridge used in §5 is a definitional equality.

m3's theorem: `M3.hasPrimeModels_field_acf :
JohnsonCriterion.HasPrimeModels.{0,0,u} Theory.field acf`, proved by taking the fraction field of
`FreeCommRing S` modulo the kernel of the polynomial relations of an embedding of `S` into a field
(`PrimeField.primeField`), with universality from `IsFractionRing.lift` and independence of the
embedding from `PrimeField.ker_lift_eq`. -/

namespace M3

/-
  **Prime models over arbitrary substructures of fields** (Johnson, *Fun with Fields*,
  Definition 2.1.1) for `T₀ = Theory.field`, `T = acf`: `HasPrimeModels Theory.field acf`,
  unconditionally.  This closes the only hypothesis of `ACFValidation.acf_qfDetermined_general`
  that was left open in `QE/ACF_validation.lean`.

  Given an abstract `S : Type u` with `Language.ring.Structure S` that embeds into a field `M`
  (`e : S ↪[Language.ring] M`), let

    `R := FreeCommRing S ⧸ ker (FreeCommRing.lift (fun s => e s))`   (`coordRing`)

  be the coordinate ring of `S`: the free commutative ring on the generators `S` modulo the
  polynomial relations that hold in `M`.  `R` is a domain, and the prime model of the theory of
  fields over `S` is its fraction field

    `F := FractionRing R`   (`primeField`)

  together with `S ↪[Language.ring] F`, `s ↦ of s / 1` (`primeEmbedding`), which is an embedding
  because `S ↪ M` is injective.

  The universal property (`primeField_universal`): for every field `N` and every embedding
  `f : S ↪[Language.ring] N` there is `g : F ↪[Language.ring] N` with `g.comp e₀ = f`.  Proof:
  `FreeCommRing.lift f` and `FreeCommRing.lift e` have the SAME kernel (`ker_lift_eq`: the
  polynomial relations of `S` do not depend on the field it is embedded into), so the induced
  map `R →+* N` is injective, and `IsFractionRing.lift` extends it to `F →+* N`; a ring
  homomorphism out of a field into a nontrivial ring is injective.

  This file is self-contained (`import Mathlib` only).  The definitions `HasPrimeModels` and
  `acf` are copies of those in `QE/Johnson_criterion.lean` and `QE/ACF_validation.lean` (same
  definitions), so that the final statement is literally
  `JohnsonCriterion.HasPrimeModels Theory.field acf`.

  Main results:
  * `PrimeField.primeEmbedding`, `PrimeField.primeField_universal`
  * `hasPrimeModels_field_acf : JohnsonCriterion.HasPrimeModels Theory.field acf`

  No `sorry`, no `axiom`; axioms are checked at the end of the file.
-/

open FirstOrder FirstOrder.Language
open FirstOrder.Ring
open scoped FirstOrder

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

/-! ## 0. Copies of the two definitions appearing in the statement -/

/-- Copy of `ACFValidation.acf` (`QE/ACF_validation.lean`): the theory of algebraically closed
fields, characteristic not fixed. -/
noncomputable def acf : Theory Language.ring :=
  Theory.field ∪ Field.genericMonicPolyHasRoot '' {n : ℕ | 0 < n}

namespace JohnsonCriterion

universe u v w

variable {L : FirstOrder.Language.{u, v}}

/-- Copy of `JohnsonCriterion.HasPrimeModels` (`QE/Johnson_criterion.lean`), with the same
universe signature.  Prime models over substructures (Johnson, Definition 2.1.1): every structure
`S` that embeds into a model of `T` has an extension `S'` modelling `T₀` which embeds into every
model of `T₀` under `S`. -/
def HasPrimeModels (T₀ T : L.Theory) : Prop :=
  ∀ (S : Type w) [L.Structure S],
    (∃ (M : T₀.ModelType.{u, v, w}), M ⊨ T ∧ Nonempty (S ↪[L] M)) →
    ∃ (S' : T₀.ModelType.{u, v, w}) (e : S ↪[L] S'),
      ∀ (N : T₀.ModelType.{u, v, w}) (f : S ↪[L] N),
        ∃ g : S' ↪[L] N, g.comp e = f

end JohnsonCriterion

namespace PrimeField

universe u

/-! ## 1. Ring homomorphisms and `Language.ring`-embeddings

(Copied from `QE/PrimeModels_partial.lean`, where the same lemmas are proved.) -/

section Conversions

variable {A B : Type*} [CommRing A] [CommRing B] [CompatibleRing A] [CompatibleRing B]

theorem ringHom_map_fun (f : A →+* B) {n : ℕ} (g : Language.ring.Functions n)
    (x : Fin n → A) : f (Structure.funMap g x) = Structure.funMap g (f ∘ x) := by
  cases g <;> simp

/-- An injective ring homomorphism is an embedding for the language of rings. -/
def embeddingOfInjectiveRingHom (f : A →+* B) (hf : Function.Injective f) :
    A ↪[Language.ring] B where
  toFun := f
  inj' := hf
  map_fun' := ringHom_map_fun f
  map_rel' := by intro n R; exact isEmptyElim R

end Conversions

/-! ## 2. Two embeddings of one structure have the same polynomial relations

(Copied from `QE/PrimeModels_partial.lean`.) -/

section Kernel

variable {S : Type u} [Language.ring.Structure S]
variable {M : Type u} [CommRing M] [CompatibleRing M]
variable {N : Type u} [CommRing N] [CompatibleRing N]

/-- `FreeCommRing.lift (fun s => e s) p` only depends on the term that `p` represents. -/
theorem lift_eq_apply_term (e : S ↪[Language.ring] M) (p : FreeCommRing S) :
    FreeCommRing.lift (fun s => e s) p
      = e (Term.realize (fun s => s) (Ring.termOfFreeCommRing p)) := by
  rw [← Ring.realize_termOfFreeCommRing p (fun s => e s)]
  exact HomClass.realize_term (g := e) (v := fun s => s)

/-- The zero of `S`, described intrinsically (as the value of the zero term), so that no ring
structure on `S` is needed. -/
def zeroTerm : Language.ring.Term S :=
  Term.func (FirstOrder.Ring.zeroFunc) (fun i => (i.elim0 : Language.ring.Term S))

theorem apply_zeroTerm {R : Type u} [CommRing R] [CompatibleRing R] (g : S ↪[Language.ring] R) :
    g (Term.realize (fun s => s) (zeroTerm (S := S))) = 0 := by
  rw [zeroTerm, Term.realize_func]
  rw [g.map_fun (FirstOrder.Ring.zeroFunc)]
  exact CompatibleRing.funMap_zero _

theorem apply_eq_zero_iff {R : Type u} [CommRing R] [CompatibleRing R]
    (g : S ↪[Language.ring] R) (w : S) :
    g w = 0 ↔ w = Term.realize (fun s => s) (zeroTerm (S := S)) := by
  constructor
  · intro h
    apply g.injective
    rw [h, apply_zeroTerm]
  · intro h
    rw [h, apply_zeroTerm]

/-- **The polynomial relations of an abstract structure are the same in every field it embeds
into.** -/
theorem ker_lift_eq (e : S ↪[Language.ring] M) (f : S ↪[Language.ring] N) :
    RingHom.ker (FreeCommRing.lift (fun s => e s))
      = RingHom.ker (FreeCommRing.lift (fun s => f s)) := by
  ext p
  rw [RingHom.mem_ker, RingHom.mem_ker, lift_eq_apply_term e, lift_eq_apply_term f,
    apply_eq_zero_iff e, apply_eq_zero_iff f]

end Kernel

/-! ## 3. The prime model of `Theory.field` over `S`: the fraction field of the coordinate ring -/

section Construction

variable {S : Type u} [Language.ring.Structure S]
variable {M : Type u} [CommRing M] [CompatibleRing M] [IsDomain M]

/-- The ideal of polynomial relations of `S`, computed in `M`. -/
noncomputable abbrev relIdeal (e : S ↪[Language.ring] M) : Ideal (FreeCommRing S) :=
  RingHom.ker (FreeCommRing.lift (fun s => e s))

/-- The coordinate ring of `S` relative to an embedding into a field `M`: the free commutative
ring on the generators `S` modulo the polynomial relations holding in `M`.  By `ker_lift_eq` it
does not depend on `M`. -/
noncomputable abbrev coordRing (e : S ↪[Language.ring] M) : Type u :=
  FreeCommRing S ⧸ relIdeal e

/-- The relations of `S` form a prime ideal, because they are the kernel of a homomorphism into
the domain `M`. -/
instance relIdeal.isPrime (e : S ↪[Language.ring] M) : (relIdeal e).IsPrime :=
  RingHom.ker_isPrime _

noncomputable instance coordRing.instCommRing (e : S ↪[Language.ring] M) :
    CommRing (coordRing e) :=
  inferInstanceAs (CommRing (FreeCommRing S ⧸ relIdeal e))

noncomputable instance coordRing.instIsDomain (e : S ↪[Language.ring] M) :
    IsDomain (coordRing e) :=
  inferInstanceAs (IsDomain (FreeCommRing S ⧸ relIdeal e))

noncomputable instance coordRing.instCompatibleRing (e : S ↪[Language.ring] M) :
    CompatibleRing (coordRing e) :=
  compatibleRingOfRing _

/-- The prime model of the theory of fields over `S`: the fraction field of the coordinate
ring. -/
noncomputable abbrev primeField (e : S ↪[Language.ring] M) : Type u :=
  FractionRing (coordRing e)

noncomputable instance primeField.instField (e : S ↪[Language.ring] M) : Field (primeField e) :=
  inferInstanceAs (Field (FractionRing (coordRing e)))

noncomputable instance primeField.instCompatibleRing (e : S ↪[Language.ring] M) :
    CompatibleRing (primeField e) :=
  compatibleRingOfRing _

/-- The map from `S` to its prime model, `s ↦ of s / 1`. -/
noncomputable abbrev primeMapFun (e : S ↪[Language.ring] M) : S → primeField e :=
  fun s => algebraMap (coordRing e) (primeField e)
    (Ideal.Quotient.mk (relIdeal e) (FreeCommRing.of s))

/-- In the coordinate ring, evaluating a term built from `x` in `S` agrees with the ring
operation on the images: for every function symbol `g` of the language of rings,
`of (g(x)) = g(of x)` holds modulo the relations.  This is where the choice of the relations
(as the kernel of an embedding into a domain) is used. -/
theorem mk_of_funMap (e : S ↪[Language.ring] M) {n : ℕ}
    (g : Language.ring.Functions n) (x : Fin n → S) :
    Ideal.Quotient.mk (relIdeal e) (FreeCommRing.of (Structure.funMap g x))
      = Structure.funMap g
          (fun i => Ideal.Quotient.mk (relIdeal e) (FreeCommRing.of (x i))) := by
  letI : CompatibleRing (FreeCommRing S) := compatibleRingOfRing _
  have hq := ringHom_map_fun (Ideal.Quotient.mk (relIdeal e)) g
    (fun i => FreeCommRing.of (x i))
  simp only [Function.comp_def] at hq
  rw [← hq]
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, RingHom.mem_ker, map_sub, FreeCommRing.lift_of]
  have h2 : FreeCommRing.lift (fun s => e s)
      (Structure.funMap g (fun i => FreeCommRing.of (x i)))
        = e (Structure.funMap g x) := by
    have he := ringHom_map_fun (FreeCommRing.lift (fun s => e s)) g
      (fun i => FreeCommRing.of (x i))
    simp only [Function.comp_def, FreeCommRing.lift_of] at he
    have he2 := e.map_fun g x
    simp only [Function.comp_def] at he2
    exact he.trans he2.symm
  rw [h2, sub_self]

@[simp]
theorem primeMapFun_apply (e : S ↪[Language.ring] M) (s : S) :
    primeMapFun e s = algebraMap (coordRing e) (primeField e)
      (Ideal.Quotient.mk (relIdeal e) (FreeCommRing.of s)) := rfl

/-- The map `s ↦ of s / 1` commutes with the ring operations of the language. -/
theorem primeMapFun_funMap (e : S ↪[Language.ring] M) {n : ℕ}
    (g : Language.ring.Functions n) (x : Fin n → S) :
    primeMapFun e (Structure.funMap g x)
      = Structure.funMap g (fun i => primeMapFun e (x i)) := by
  have hq := ringHom_map_fun (algebraMap (coordRing e) (primeField e)) g
    (fun i => Ideal.Quotient.mk (relIdeal e) (FreeCommRing.of (x i)))
  simp only [Function.comp_def] at hq
  rw [primeMapFun_apply, mk_of_funMap e g x]
  simpa only [primeMapFun_apply] using hq

/-- The same statement in the shape of `Language.Embedding.map_fun'`. -/
theorem primeMapFun_comp (e : S ↪[Language.ring] M) {n : ℕ}
    (g : Language.ring.Functions n) (x : Fin n → S) :
    primeMapFun e (Structure.funMap g x) = Structure.funMap g (primeMapFun e ∘ x) := by
  rw [primeMapFun_funMap e g x]
  simp only [Function.comp_def]

/-- **The embedding of `S` into its prime model.** -/
noncomputable def primeEmbedding (e : S ↪[Language.ring] M) :
    S ↪[Language.ring] primeField e where
  toFun := primeMapFun e
  inj' := by
    intro a b hab
    have h1 : Ideal.Quotient.mk (relIdeal e) (FreeCommRing.of a)
        = Ideal.Quotient.mk (relIdeal e) (FreeCommRing.of b) :=
      IsFractionRing.injective (coordRing e) (primeField e) hab
    have h2 : FreeCommRing.of a - FreeCommRing.of b ∈ relIdeal e :=
      (Ideal.Quotient.mk_eq_mk_iff_sub_mem
        (I := relIdeal e) (x := FreeCommRing.of a) (y := FreeCommRing.of b)).mp h1
    have h3 : FreeCommRing.lift (fun s => e s)
        (FreeCommRing.of a - FreeCommRing.of b) = 0 := RingHom.mem_ker.mp h2
    rw [map_sub, FreeCommRing.lift_of, FreeCommRing.lift_of, sub_eq_zero] at h3
    exact e.injective h3
  map_fun' := fun {n} g x => primeMapFun_comp e g x
  map_rel' := by intro n R; exact isEmptyElim R

/-! ## 4. The universal property of the prime model -/

section Universal

variable {N : Type u} [Field N] [CompatibleRing N]

/-- **The prime model of `Theory.field` over `S` embeds into every field over `S`.** -/
theorem primeField_universal (e : S ↪[Language.ring] M) (f : S ↪[Language.ring] N) :
    ∃ g : primeField e ↪[Language.ring] N, g.comp (primeEmbedding e) = f := by
  have hker : relIdeal e = relIdeal f := ker_lift_eq e f
  -- the map on coordinate rings induced by `f`, well defined because the kernels agree
  let rHom : coordRing e →+* N :=
    Ideal.Quotient.lift (relIdeal e) (FreeCommRing.lift (fun s => f s)) (fun a ha => by
      rw [hker] at ha
      exact RingHom.mem_ker.mp ha)
  have rHom_inj : Function.Injective rHom := by
    intro x y hxy
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    simp only [rHom, Ideal.Quotient.lift_mk] at hxy
    rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, hker, RingHom.mem_ker, map_sub, hxy, sub_self]
  -- extend it to the fraction field
  let gHom : primeField e →+* N :=
    IsFractionRing.lift (A := coordRing e) (K := primeField e) (L := N) rHom_inj
  have gHom_inj : Function.Injective gHom := by
    intro x y hxy
    have h : gHom (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    by_contra hne
    have hne' : x - y ≠ 0 := sub_ne_zero.mpr hne
    have h1 : gHom (x - y) * gHom ((x - y)⁻¹) = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hne', map_one]
    rw [h, zero_mul] at h1
    exact zero_ne_one h1
  have hgl : ∀ z : coordRing e,
      gHom (algebraMap (coordRing e) (primeField e) z) = rHom z :=
    fun z => IsFractionRing.lift_algebraMap rHom_inj z
  refine ⟨embeddingOfInjectiveRingHom gHom gHom_inj, ?_⟩
  refine FirstOrder.Language.Embedding.ext ?_
  intro s
  simp only [FirstOrder.Language.Embedding.comp_apply]
  have h7 : (embeddingOfInjectiveRingHom gHom gHom_inj : primeField e ↪[Language.ring] N)
      (primeEmbedding e s) = gHom (primeMapFun e s) := rfl
  rw [h7]
  have h4 : rHom (Ideal.Quotient.mk (relIdeal e) (FreeCommRing.of s))
      = FreeCommRing.lift (fun s => f s) (FreeCommRing.of s) := by
    simp only [rHom, Ideal.Quotient.lift_mk]
  rw [primeMapFun_apply, hgl, h4, FreeCommRing.lift_of]

end Universal

end Construction

end PrimeField

/-! ## 5. `HasPrimeModels Theory.field acf` -/

universe u

theorem hasPrimeModels_field_acf :
    JohnsonCriterion.HasPrimeModels.{0, 0, u} Theory.field acf := by
  intro S inst hS
  letI := inst
  obtain ⟨M, _hMacf, ⟨e⟩⟩ := hS
  letI : Field M := FirstOrder.Field.fieldOfModelField M
  letI : CompatibleRing M := FirstOrder.Field.compatibleRingOfModelField M
  refine ⟨Theory.ModelType.of Theory.field (PrimeField.primeField e), PrimeField.primeEmbedding e, ?_⟩
  intro N f
  letI : Field N := FirstOrder.Field.fieldOfModelField N
  letI : CompatibleRing N := FirstOrder.Field.compatibleRingOfModelField N
  exact PrimeField.primeField_universal e f

#print axioms hasPrimeModels_field_acf
#print axioms PrimeField.primeField_universal
#print axioms PrimeField.primeEmbedding
#print axioms PrimeField.mk_of_funMap
#print axioms PrimeField.ker_lift_eq

end M3

/-! ## 5. Quantifier elimination for `acf`, unconditional -/

namespace HQEDerive

/-- **Quantifier elimination for algebraically closed fields**: every `Language.ring`-formula is
`acf`-equivalent to a quantifier-free one, in the frozen shape.

Chain: Johnson's Lemma 2.1.4 (`JohnsonCriterion.qfDetermined`, Part 1)
→ the last mile `H_of_qfDetermined` (Part 2/3)
→ the compactness join `hasQE_of_qfDet`
→ the ACF hypotheses `field_subset_acf`, `amalgamation_field`, `oneEC_field_acf`
→ and the prime-model statement `M3.hasPrimeModels_field_acf` (member m3's compiled
`PrimeModels_full.lean`, wrapped in `namespace M3`), whose only mismatch with this file is the
pair of copied definitions `acf` and `JohnsonCriterion.HasPrimeModels`, which are definitionally
the same. -/
theorem HasQE_acf : QECriterion.HasQE (L := Language.ring) ACFValidation.acf :=
  HasQE_acf_of_primeModels
    (show JohnsonCriterion.HasPrimeModels.{0, 0, 0} Theory.field ACFValidation.acf from
      M3.hasPrimeModels_field_acf)

/-- The frozen shape of `Milestone0/Encoding.lean`: every `Language.ring`-formula is
`acf`-equivalent to a quantifier-free one, stated with `⊨ᵇ` and `⇔`. -/
theorem HasQE_acf_frozen :
    ∀ (α : Type) (φ : Language.ring.Formula α),
      ∃ ψ : Language.ring.Formula α, ψ.IsQF ∧ ACFValidation.acf ⊨ᵇ (φ ⇔ ψ) :=
  HasQE_acf

/-- The same as `ShoenfieldQE.HasQE` (frozen shape at general `α`). -/
theorem hasQE_frozen_acf : ShoenfieldQE.HasQE (L := Language.ring) ACFValidation.acf :=
  HasQE_acf

/-- Bounded quantifier elimination for `acf`. -/
theorem HasQEb_acf : QECriterion.HasQEb (L := Language.ring) ACFValidation.acf :=
  QECriterion.hasQEb_of_QEAllStep (QECriterion.QEAllStep_iff_QEExStep.2
    (BoundedQE.qeExStep_theoryIff (L₀ := Language.ring)
      (H_of_qfDetermined ACFValidation.field_subset_acf M3.hasPrimeModels_field_acf
        (fun A B C i j => ACFValidation.amalgamation_field A B C i j)
        (fun M N f hM => ACFValidation.oneEC_field_acf M N f hM))))

end HQEDerive

#print axioms HQEDerive.HasQE_acf
#print axioms HQEDerive.HasQE_acf_frozen
#print axioms HQEDerive.hasQE_frozen_acf
#print axioms HQEDerive.HasQEb_acf

/-! ## 21. Quantifier elimination for `ACVF` in the language `L_val` -/

/-- **Quantifier elimination in `L_val`.**  Johnson's criterion (`HQEDerive.hasQE_of_johnson`)
with its four hypotheses all proved in this file: `valField ⊆ ACVF_val`, prime models over
substructures (`ValPM.hasPrimeModels_ACVF_val`), amalgamation (`ValOneEC.hasAmalgamation_valField`)
and 1-ec (`ValOneEC.oneECIn_of_modelType`). -/
theorem hasQE_ACVF_val : QECriterion.HasQE (L := Language.val) ValPM.ACVF_val :=
  HQEDerive.hasQE_of_johnson (L := Language.val) (T₀ := ValPM.valField) (T := ValPM.ACVF_val)
    ValPM.valField_subset_ACVF_val
    ValPM.hasPrimeModels_ACVF_val
    ValOneEC.hasAmalgamation_valField
    ValOneEC.oneECIn_of_modelType

#print axioms hasQE_ACVF_val

/-! ## 22. The frozen language `L_RV` and the theory `ACVF` (from `Milestone0/Encoding.lean`) -/

set_option maxHeartbeats 1000000

namespace SpecialTransformations
namespace Milestone0

/-! ## Part 0. The paper's `RV` sort (conventions of `SpecialTransformations/Basic.lean`) -/

/- The algebraic layer of the paper, as it exists in the repository: `RV^× = Kˣ/(1+M)`,
`RV = RV^× ∪ {rv 0}` and `rv : K → RV`.  The paper's `∞` is `rv 0`; the `RV` sort has one
absorbing element, which is also the residue field's zero. -/
namespace Valued

open Valuation

variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]
  (v : Valuation K Γ₀)

/-- `RV× = Kˣ / (1 + M)`, the multiplicative RV sort. -/
abbrev RVUnit : Type _ := Kˣ ⧸ v.valuationSubring.principalUnitGroup

/-- The `RV` sort: `RV = RV^× ∪ {rv 0}`.  `none` is `rv 0`, the absorbing element — the paper's
`∞`, which is also the residue field's zero `0`. -/
abbrev RV : Type _ := Option (RVUnit v)

/-- The paper's `RV₀ = RV ∪ {0}`.  Since `0 = ∞ = rv 0` is already the element `none` of `RV`,
`RV₀` is the same type; the alias is kept for the paper's notation. -/
abbrev RV0 : Type _ := RV v

/-- The quotient map `rv : K → RV`, with `rv 0 = 0` (the paper's `∞`). -/
noncomputable def rv (x : K) : RV v := by
  classical
  exact if h : x = 0 then none else some (QuotientGroup.mk (Units.mk0 x h))

end Valued

/-! ## Part 1. The sorts and the symbols of `L_RV` (Definition 2.1)

Definition 2.1 of the paper gives a language with two sorts:

* a `VF`-sort with the language of rings `L_R = {0, 1, +, -, ×}`;
* an `RV`-sort with the group language `{1, ×}`, two constants `0` and `∞`, a unary
  predicate `Kˣ`, a binary function `+ : K² → K` and a unary function `- : K → K`
  (where `K = Kˣ ∪ {0}`), and a binary relation `≤`;
* a function symbol `rv` from the `VF`-sort into the `RV`-sort.

### Encoding

Mathlib's `FirstOrder.Language` is one-sorted: `Language.Functions n` and
`Language.Relations n` are the `n`-ary symbols of a language over *one* carrier type.
We therefore use a single carrier `M` with a tag `SortTag` for the sorts, plus a unary
sort predicate for each sort.  The *names* of the function symbols record their sort
signature: `vfAdd` is the addition of the ring language of the `VF` sort, `kAdd` is the
addition of `K = Kˣ ∪ {0}` inside the `RV` sort, and so on.
-/

/-- The sorts of `L_RV`, as tags on the single carrier. -/
inductive SortTag where
  | vf
  | rv
  deriving DecidableEq, Repr

/-- Function symbols of `L_RV`, tagged by arity. -/
inductive Fn : ℕ → Type where
  /-- `0` of the ring language of the `VF` sort -/
  | vfZero : Fn 0
  /-- `1` of the ring language of the `VF` sort -/
  | vfOne : Fn 0
  /-- `+` of the ring language of the `VF` sort -/
  | vfAdd : Fn 2
  /-- `-` of the ring language of the `VF` sort -/
  | vfNeg : Fn 1
  /-- `×` of the ring language of the `VF` sort -/
  | vfMul : Fn 2
  /-- `1` of the group language of the `RV` sort -/
  | rvOne : Fn 0
  /-- the constant `0` of the `RV` sort: the residue field's zero, which is also `rv(0)` and
  the absorbing element of `RV`.  The paper writes this element both as `0` and as `∞`; it is
  one element, so the language has one constant. -/
  | rvZero : Fn 0
  /-- `×` of the `RV` sort -/
  | rvMul : Fn 2
  /-- `+ : K² → K` of the `RV` sort -/
  | kAdd : Fn 2
  /-- `- : K → K` of the `RV` sort -/
  | kNeg : Fn 1
  /-- the projection `rv : VF → RV` -/
  | rvMap : Fn 1

/-- Relation symbols of `L_RV`, tagged by arity.  The first two are the sort predicates
of the encoding (they are not part of the paper's signature); the last two are the
paper's unary predicate `Kˣ` and its preorder `≤`. -/
inductive Rel : ℕ → Type where
  /-- encoding: the `VF` sort -/
  | memVF : Rel 1
  /-- encoding: the `RV` sort -/
  | memRV : Rel 1
  /-- the paper's unary predicate `Kˣ` -/
  | memUnits : Rel 1
  /-- the paper's preorder `≤` on `RV` -/
  | rvLe : Rel 2

/-- **The language `L_RV` of Definition 2.1**, in the tagged one-sorted encoding. -/
def LRV : Language := ⟨Fn, Rel⟩

namespace LRV

/-! ### Terms and formulas of `L_RV` with variables among `Fin n` and no parameters -/

/-- Terms of `L_RV` whose (free) variables are indexed by `Fin n`. -/
abbrev Tm (n : ℕ) : Type := LRV.Term (Empty ⊕ Fin n)

/-- Bounded formulas of `L_RV` with `n` variables in scope and no free parameters. -/
abbrev Bf (n : ℕ) : Type := LRV.BoundedFormula Empty n

variable {n : ℕ}

/-! #### Term constructors -/

/-- `0` of the `VF` sort -/
def tVFZero : Tm n := Term.func Fn.vfZero fun i => i.elim0
/-- `1` of the `VF` sort -/
def tVFOne : Tm n := Term.func Fn.vfOne fun i => i.elim0
/-- `+` of the `VF` sort -/
def tVFAdd (t u : Tm n) : Tm n := Term.func Fn.vfAdd ![t, u]
/-- `-` of the `VF` sort -/
def tVFNeg (t : Tm n) : Tm n := Term.func Fn.vfNeg ![t]
/-- `×` of the `VF` sort -/
def tVFMul (t u : Tm n) : Tm n := Term.func Fn.vfMul ![t, u]
/-- `1` of the `RV` sort -/
def tRVOne : Tm n := Term.func Fn.rvOne fun i => i.elim0
/-- `0` of the `RV` sort -/
def tRVZero : Tm n := Term.func Fn.rvZero fun i => i.elim0
/-- The paper's `∞` is `rv(0)`, i.e. the absorbing element `rvZero` of the `RV` sort: the paper's
two symbols `0` and `∞` name one element.  Kept as a definition so that the axioms can be read
in the paper's notation. -/
def tRVInfty : Tm n := tRVZero
/-- `×` of the `RV` sort -/
def tRVMul (t u : Tm n) : Tm n := Term.func Fn.rvMul ![t, u]
/-- `+ : K² → K` of the `RV` sort -/
def tKAdd (t u : Tm n) : Tm n := Term.func Fn.kAdd ![t, u]
/-- `- : K → K` of the `RV` sort -/
def tKNeg (t : Tm n) : Tm n := Term.func Fn.kNeg ![t]
/-- the projection `rv : VF → RV` -/
def tRv (t : Tm n) : Tm n := Term.func Fn.rvMap ![t]

/-- the bound variable of index `i < n` -/
def tv (i : ℕ) (h : i < n) : Tm n := Term.var (Sum.inr ⟨i, h⟩)

/-- the numeral `k · 1` of the `VF` sort -/
def tVFNumeral : ℕ → Tm n
  | 0 => tVFZero
  | k + 1 => tVFAdd (tVFNumeral k) tVFOne

/-- `t ^ k`, in the `VF` sort -/
def tVFPow (t : Tm n) : ℕ → Tm n
  | 0 => tVFOne
  | k + 1 => tVFMul (tVFPow t k) t

/-- `t ^ k`, in the `RV` sort -/
def tRVPow (t : Tm n) : ℕ → Tm n
  | 0 => tRVOne
  | k + 1 => tRVMul (tRVPow t k) t

/-! #### Formula constructors -/

/-- `t ∈ VF`, the encoding's sort predicate for the `VF` sort -/
def pVF (t : Tm n) : Bf n := FirstOrder.Language.Relations.boundedFormula₁ Rel.memVF t
/-- `t ∈ RV`, the encoding's sort predicate for the `RV` sort -/
def pRVsort (t : Tm n) : Bf n := FirstOrder.Language.Relations.boundedFormula₁ Rel.memRV t
/-- the paper's unary predicate `Kˣ` -/
def pUnits (t : Tm n) : Bf n := FirstOrder.Language.Relations.boundedFormula₁ Rel.memUnits t
/-- the paper's preorder `≤` -/
def pLe (t u : Tm n) : Bf n := FirstOrder.Language.Relations.boundedFormula₂ Rel.rvLe t u
/-- `t = u` -/
def pEq (t u : Tm n) : Bf n := t =' u
/-- the paper's `RV = RV-sort ∖ {0}` -/
def pRV (t : Tm n) : Bf n := ∼(pEq t tRVZero)
/-- the paper's `RV-sort ∖ {∞}`.

**Caution.**  Since `∞ = rv(0) = 0`, this predicate is `RV ∖ {0}` — the multiplicative group
`RV^×` — and *not* the residue field `K`: `K = K^× ∪ {0}` is `pInK`, which does contain the
absorbing element.  The name is kept only because the paper's own notation `RV ∖ {∞}` appears
in its statements; `pK` is the same predicate as `pRV`. -/
def pK (t : Tm n) : Bf n := ∼(pEq t tRVInfty)
/-- the paper's `RV₀ = RV ∪ {0}`, i.e. the whole `RV` sort -/
def pRV0 (_t : Tm n) : Bf n := ⊤
/-- the strict order `t > 1` of the `RV` sort -/
def pGtOne (t : Tm n) : Bf n := pLe tRVOne t ⊓ ∼(pLe t tRVOne)
/-- `t ∈ K = K^× ∪ {0}`, the residue field inside the `RV` sort.

Not the same as `t ≠ 0`: when `Γ` is nontrivial the elements of `RV ∖ {0}` of value `≠ 1`
are not in `K`, and the residue-field operations are junk there.  Definition 2.1(d)
defines `K` as `K^× ∪ {0}`, with `K^×` the predicate, i.e. axiom (4)'s class of `1`.  The
`0` here is `rv(0)`, the absorbing element of `RV`. -/
def pInK (t : Tm n) : Bf n := pUnits t ⊔ pEq t tRVZero

end LRV

/-! ## Part 2 is below; the enclosing namespaces stay open to the end of the file. -/

namespace LRV

/-! ## Part 2. Guarded quantifiers

Since the carrier of a model of the encoding holds both sorts, every axiom of the paper
has to say which sort its variables range over.  `allSorted ss φ` is the sentence
`∀ x̄, (⋀ i, x_i ∈ s_i) → φ`, and `exSorted s φ` is the formula `∃ x ∈ s, φ`. -/

/-- the sort predicate of the sort `s`, as a formula -/
def sortPred (s : SortTag) (t : Tm n) : Bf n :=
  match s with
  | .vf => pVF t
  | .rv => pRVsort t

/-- `⋀ i, x_i ∈ s_i`, for the variables `x_i` of index `i` -/
def sortedHyps {k : ℕ} (ss : Fin k → SortTag) : Bf k :=
  (List.finRange k).foldr (fun i acc => sortPred (ss i) (tv i.val i.isLt) ⊓ acc) ⊤

/-- the guarded universal sentence `∀ x̄, (⋀ i, x_i ∈ s_i) → φ` -/
def allSorted {k : ℕ} (ss : Fin k → SortTag) (φ : Bf k) : LRV.Sentence :=
  BoundedFormula.alls (sortedHyps ss ⟹ φ)

/-- the guarded existential formula `∃ x ∈ s, φ`, where `x` is the variable of index `k` -/
def exSorted {k : ℕ} (s : SortTag) (φ : Bf (k + 1)) : Bf k :=
  BoundedFormula.ex (sortPred s (tv k (Nat.lt_succ_self k)) ⊓ φ)

/-! ### Quantification over the residue field `K = K^× ∪ {0}`

The `RV` sort's carrier is the multiplicative group `RV^×` together with one absorbing element,
`rv 0 = 0 = ∞`, which is also the residue field's zero.  The paper's field is
`K = K^× ∪ {0}` — the units together with the absorbing element — and that is *not* the same as
`RV ∖ {0}`, which is the group `RV^×`: when `Γ` is nontrivial there are elements of value
`≠ 1` in `RV^×` at which the residue operations are junk.  Axioms about the field `K` are
therefore relativised to `pInK t = (t ∈ K^×) ⊔ (t = 0)`, not to `t ≠ ∞ = 0`. -/

/-- `⋀ i < k, x_i ∈ K`: the tuple lies in `K = K^× ∪ {0}` -/
def kHyps {k : ℕ} : Bf k :=
  (List.finRange k).foldr (fun i acc => pInK (tv i.val i.isLt) ⊓ acc) ⊤

/-- the universal sentence `∀ x̄ ∈ s̄ ∩ K, φ` -/
def allSortedK {k : ℕ} (ss : Fin k → SortTag) (φ : Bf k) : LRV.Sentence :=
  BoundedFormula.alls ((sortedHyps ss ⊓ kHyps) ⟹ φ)

/-- the guarded existential formula `∃ x ∈ s ∩ K, φ`, with `x` the variable of index `k` -/
def exSortedK {k : ℕ} (s : SortTag) (φ : Bf (k + 1)) : Bf k :=
  BoundedFormula.ex (sortPred s (tv k (Nat.lt_succ_self k)) ⊓
    pInK (tv k (Nat.lt_succ_self k)) ⊓ φ)

/-- the universal closure of a formula in a single variable -/
def allOne (φ : Bf 1) : LRV.Sentence := BoundedFormula.alls φ

/-- Horner form `x^k + a_{k-1} x^{k-1} + ⋯ + a_0` of the monic polynomial of degree `k`
whose coefficients are the variables `0, …, k-1` and whose variable is the variable `k`.

The leading term is `x ^ k`, so `acfScheme` quantifies over *all* monic polynomials of
degree `k`.  (An earlier version started the Horner fold at `x` instead of at `x + a_{k-1}`,
which silently produced `x^{k+1} + a_{k-1}x^{k-1} + ⋯ + a_0` — a monic polynomial of degree
`k+1` with zero `x^k` coefficient, so the scheme covered only a proper subclass and did not
give algebraic closedness.)  For `k = 0` the value is immaterial: `acfScheme` is only used
with `1 ≤ k`. -/
def hornerPoly {k : ℕ} (add mul : {n : ℕ} → Tm n → Tm n → Tm n) : Tm (k + 1) :=
  match k with
  | 0 => tv 0 Nat.zero_lt_one
  | (n + 1) =>
    let x : Tm (n + 1 + 1) := tv (n + 1) (by omega)
    (List.finRange n).reverse.foldl
      (fun acc i => add (mul acc x) (tv i.val (by omega)))
      (add x (tv n (by omega)))

/-- Sanity check on the Horner form: at `k = 1` it is the monic linear `x + a₀`. -/
theorem hornerPoly_one :
    hornerPoly (k := 1) tKAdd tRVMul = tKAdd (tv 1 Nat.one_lt_two) (tv 0 Nat.zero_lt_two) := rfl

/-- Sanity check on the Horner form: at `k = 2` it is the monic quadratic `x² + a₁x + a₀`
(the `x²` coefficient is `1`, not `0`). -/
theorem hornerPoly_two :
    hornerPoly (k := 2) tKAdd tRVMul =
      tKAdd (tRVMul (tKAdd (tv 2 (Nat.lt_succ_self 2)) (tv 1 (Nat.one_lt_succ_succ 1)))
        (tv 2 (Nat.lt_succ_self 2))) (tv 0 (Nat.zero_lt_succ 2)) := rfl

end LRV

namespace Axioms

open LRV

/-- The sentences of a finite list, as a theory. -/
def ofList (l : List LRV.Sentence) : LRV.Theory := {s | s ∈ l}

/-! ### 3.1 The sort discipline of the encoding

These sentences are not part of the paper's Definition 2.2: they are what makes a
one-sorted structure behave like a two-sorted one.  They say that the carrier is the
disjoint union of the two sorts, and that each sort is closed under its own symbols. -/

/-- the carrier is covered by the two sorts -/
def sdCover : LRV.Sentence := allOne (pVF &0 ⊔ pRVsort &0)
/-- the two sorts are disjoint -/
def sdDisjoint : LRV.Sentence := allOne (∼(pVF &0 ⊓ pRVsort &0))
/-- `0` of the ring language lies in the `VF` sort -/
def sdVFZero : LRV.Sentence := pVF tVFZero
/-- `1` of the ring language lies in the `VF` sort -/
def sdVFOne : LRV.Sentence := pVF tVFOne
/-- the `VF` sort is closed under `+` -/
def sdVFAdd : LRV.Sentence := allSorted ![.vf, .vf] (pVF (tVFAdd &0 &1))
/-- the `VF` sort is closed under `-` -/
def sdVFNeg : LRV.Sentence := allSorted ![.vf] (pVF (tVFNeg &0))
/-- the `VF` sort is closed under `×` -/
def sdVFMul : LRV.Sentence := allSorted ![.vf, .vf] (pVF (tVFMul &0 &1))
/-- `rv` maps the `VF` sort into the `RV` sort -/
def sdRv : LRV.Sentence := allSorted ![.vf] (pRVsort (tRv &0))
/-- `0` of the `RV` sort lies in the `RV` sort -/
def sdRVZero : LRV.Sentence := pRVsort tRVZero
/-- `∞` lies in the `RV` sort -/
def sdRVInfty : LRV.Sentence := pRVsort tRVInfty
/-- `1` of the `RV` sort lies in the `RV` sort -/
def sdRVOne : LRV.Sentence := pRVsort tRVOne
/-- the `RV` sort is closed under `×` -/
def sdRVMul : LRV.Sentence := allSorted ![.rv, .rv] (pRVsort (tRVMul &0 &1))
/-- The predicate `Kˣ` holds only of elements of the `RV` sort.

Its actual content is axiom (4)'s `leClassOne`, which makes `Kˣ` the class of `1` — a
*proper* subgroup of the multiplicative group `RV ∖ {0}` whenever `Γ` is nontrivial.
Identifying `Kˣ` with all of `RV ∖ {0}` puts every `x ≠ 0` in the class of `1`, hence
`1 ≤ x ≤ 1`, hence makes the preorder trivial and `Γ` trivial — contradicting the paper's
standing hypothesis that `Γ(S)` is nontrivial. -/
def sdUnits : LRV.Sentence := allOne (pUnits &0 ⟹ pRVsort &0)
/-- `K = Kˣ ∪ {0}` is closed under `+` -/
def sdKAdd : LRV.Sentence :=
  allSorted ![.rv, .rv] (pInK &0 ⟹ (pInK &1 ⟹ pInK (tKAdd &0 &1)))
/-- `K` is closed under unary `-` -/
def sdKNeg : LRV.Sentence := allSorted ![.rv] (pInK &0 ⟹ pInK (tKNeg &0))
/-- `K` is closed under `×`: the paper's `K = K^× ∪ {0}` is a field, so the product of two
elements of `K` is in `K` and not `∞`.  Without this the field axioms of `kField` (which are
guarded by `pK`) constrain only the products that happen to land in `K`. -/
def sdKMul : LRV.Sentence :=
  allSorted ![.rv, .rv] (pInK &0 ⟹ (pInK &1 ⟹ pInK (tRVMul &0 &1)))

/-- The closure part of the sort discipline: each sort is closed under its own symbols,
and the two sorts are related through the symbols that cross them. -/
def sortClosure : LRV.Theory :=
  ofList [sdVFZero, sdVFOne, sdVFAdd, sdVFNeg, sdVFMul, sdRv,
    sdRVZero, sdRVInfty, sdRVOne, sdRVMul, sdUnits, sdKAdd, sdKNeg, sdKMul]

/-- the sort discipline of the encoding, as a theory -/
def sortAxioms : LRV.Theory := sortClosure ∪ ofList [sdCover, sdDisjoint]

/-! ### 3.2 Fields

The field axioms of Definition 2.2 items 1 and 3 are the same list of sentences read in
the two sorts, so they are generated from the sort tag and that sort's symbols. -/

/-- the field axioms for the sort `s`, with that sort's `0`, `1`, `+`, `-`, `×` -/
def fieldAxioms (s : SortTag) (zero one : {n : ℕ} → Tm n)
    (add mul : {n : ℕ} → Tm n → Tm n → Tm n) (neg : {n : ℕ} → Tm n → Tm n) :
    List LRV.Sentence :=
  [ /- associativity of `+` -/
    allSorted ![s, s, s] (pEq (add (add &0 &1) &2) (add &0 (add &1 &2))),
    /- commutativity of `+` -/
    allSorted ![s, s] (pEq (add &0 &1) (add &1 &0)),
    /- `0` is neutral for `+` -/
    allSorted ![s] (pEq (add &0 zero) &0),
    /- additive inverses -/
    allSorted ![s] (pEq (add &0 (neg &0)) zero),
    /- associativity of `×` -/
    allSorted ![s, s, s] (pEq (mul (mul &0 &1) &2) (mul &0 (mul &1 &2))),
    /- commutativity of `×` -/
    allSorted ![s, s] (pEq (mul &0 &1) (mul &1 &0)),
    /- `1` is neutral for `×` -/
    allSorted ![s] (pEq (mul &0 one) &0),
    /- distributivity -/
    allSorted ![s, s, s] (pEq (mul &0 (add &1 &2)) (add (mul &0 &1) (mul &0 &2))),
    /- `0 ≠ 1` -/
    ∼(pEq zero one),
    /- every nonzero element is invertible: the language has no inverse symbol -/
    allSorted ![s] (pEq &0 zero ⊔ exSorted s (pEq (mul &0 &1) one)) ]

/-- the algebraic-closedness scheme for the sort `s`:
`∀ a₀ … a_{k-1} ∃ x, x^k + a_{k-1} x^{k-1} + ⋯ + a₀ = 0` -/
def acfScheme (s : SortTag) (zero : {n : ℕ} → Tm n)
    (add mul : {n : ℕ} → Tm n → Tm n → Tm n) (k : ℕ) : LRV.Sentence :=
  allSorted (fun _ : Fin k => s) (exSorted s (pEq (hornerPoly add mul) zero))

/-- Definition 2.2 item 1: `(VF, 0, 1, +, -, ×)` is an algebraically closed field. -/
def vfField : LRV.Theory :=
  ofList (fieldAxioms .vf tVFZero tVFOne tVFAdd tVFMul tVFNeg)
/-- algebraic closedness of the `VF` sort -/
def vfAlgClosed : LRV.Theory := {s | ∃ k, 1 ≤ k ∧ s = acfScheme .vf tVFZero tVFAdd tVFMul k}

/-- Definition 2.2 item 3: `(K, 0, 1, +, -, ×)` is an algebraically closed field, where
`K = K^× ∪ {0}`, the units of `RV` together with the absorbing element `0 = ∞ = rv 0`.

Every quantifier is relativised to `K` (`allSortedK`, `exSortedK`), not merely to the `RV`
sort.  This is not cosmetic: `RV^×` also contains the elements of value `≠ 1`, where the
residue operations are junk, so asserting the field axioms at every element of `RV`
(equivalently at every `t ≠ ∞`, since `RV ∖ {0}` *is* the group) would force `Γ` trivial. -/
def kField : LRV.Theory :=
  ofList
    [ /- associativity of `+` -/
      allSortedK ![.rv, .rv, .rv] (pEq (tKAdd (tKAdd &0 &1) &2) (tKAdd &0 (tKAdd &1 &2))),
      /- commutativity of `+` -/
      allSortedK ![.rv, .rv] (pEq (tKAdd &0 &1) (tKAdd &1 &0)),
      /- `0` is neutral for `+` -/
      allSortedK ![.rv] (pEq (tKAdd &0 tRVZero) &0),
      /- additive inverses -/
      allSortedK ![.rv] (pEq (tKAdd &0 (tKNeg &0)) tRVZero),
      /- associativity of `×` -/
      allSortedK ![.rv, .rv, .rv] (pEq (tRVMul (tRVMul &0 &1) &2) (tRVMul &0 (tRVMul &1 &2))),
      /- commutativity of `×` -/
      allSortedK ![.rv, .rv] (pEq (tRVMul &0 &1) (tRVMul &1 &0)),
      /- `1` is neutral for `×` -/
      allSortedK ![.rv] (pEq (tRVMul &0 tRVOne) &0),
      /- distributivity -/
      allSortedK ![.rv, .rv, .rv]
        (pEq (tRVMul &0 (tKAdd &1 &2)) (tKAdd (tRVMul &0 &1) (tRVMul &0 &2))),
      /- `0 ≠ 1` -/
      ∼(pEq tRVZero tRVOne),
      /- every nonzero element of `K` is invertible -/
      allSortedK ![.rv] (pEq &0 tRVZero ⊔ exSortedK .rv (pEq (tRVMul &0 &1) tRVOne)) ]

/-- the algebraic-closedness scheme for `K = K^× ∪ {0}`: coefficients and root in `K` -/
def acfSchemeK (k : ℕ) : LRV.Sentence :=
  allSortedK (fun _ : Fin k => .rv)
    (exSortedK .rv (pEq (hornerPoly tKAdd tRVMul) tRVZero))

/-- algebraic closedness of `K = K^× ∪ {0}` -/
def kAlgClosed : LRV.Theory := {s | ∃ k, 1 ≤ k ∧ s = acfSchemeK k}

/-! ### 3.3 The multiplicative structure of the `RV` sort (Definition 2.2 items 2 and 4) -/

/-- `1 ∈ Kˣ` -/
def rvOneMem : LRV.Sentence := pUnits tRVOne
/-- `Kˣ` is closed under `×` -/
def rvMulMem : LRV.Sentence := allSorted ![.rv, .rv] (pUnits &0 ⟹ (pUnits &1 ⟹ pUnits (tRVMul &0 &1)))
/-- `×` is associative on `RV` -/
def rvMulAssoc : LRV.Sentence :=
  allSorted ![.rv, .rv, .rv] (pEq (tRVMul (tRVMul &0 &1) &2) (tRVMul &0 (tRVMul &1 &2)))
/-- `×` is commutative on `RV` -/
def rvMulComm : LRV.Sentence := allSorted ![.rv, .rv] (pEq (tRVMul &0 &1) (tRVMul &1 &0))
/-- `1` is neutral for `×` on `Kˣ` -/
def rvMulOne : LRV.Sentence := allSorted ![.rv] (pUnits &0 ⟹ pEq (tRVMul tRVOne &0) &0)
/-- every element of `Kˣ` is invertible in `Kˣ` -/
def rvMulInv : LRV.Sentence :=
  allSorted ![.rv] (pUnits &0 ⟹ exSorted .rv (pUnits &1 ⊓ pEq (tRVMul &1 &0) tRVOne))
/-- divisibility of `Kˣ`: for every `k ≥ 1`, `∀ x ∈ Kˣ ∃ y ∈ Kˣ, y^k = x` -/
def rvDivisible (k : ℕ) : LRV.Sentence :=
  allSorted ![.rv] (pUnits &0 ⟹ exSorted .rv (pUnits &1 ⊓ pEq (tRVPow &1 k) &0))
/-- `t × 0 = 0` for `t ∈ K` -/
def rvMulZeroK : LRV.Sentence := allSorted ![.rv] (pInK &0 ⟹ pEq (tRVMul &0 tRVZero) tRVZero)
/-- `t × 0 = 0` for every `t` of the `RV` sort: the absorbing element.  (This is the paper's
`t × ∞ = ∞`; `∞ = rv 0 = 0`.) -/
def rvMulInfty : LRV.Sentence := allSorted ![.rv] (pEq (tRVMul &0 tRVInfty) tRVInfty)

/-- Definition 2.2 item 2: `(RV^×, 1, ×)` is a divisible abelian group, with `×`
augmented by `t × 0 = 0`, i.e. `0 = ∞ = rv 0` absorbing. -/
def rvGroup : LRV.Theory :=
  ofList [rvOneMem, rvMulMem, rvMulAssoc, rvMulComm, rvMulOne, rvMulInv, rvMulZeroK,
      rvMulInfty] ∪
    {s | ∃ k, 1 ≤ k ∧ s = rvDivisible k}

/-! ### 3.4 The preorder on `RV` (Definition 2.2 item 4) -/

/-- `≤` is reflexive on `RV` -/
def leRefl : LRV.Sentence := allSorted ![.rv] (pRV &0 ⟹ pLe &0 &0)
/-- `≤` is transitive on `RV` -/
def leTrans : LRV.Sentence :=
  allSorted ![.rv, .rv, .rv] (pRV &0 ⟹ (pRV &1 ⟹ (pRV &2 ⟹ (pLe &0 &1 ⟹ (pLe &1 &2 ⟹ pLe &0 &2)))))
/-- `≤` is total on `RV` -/
def leTotal : LRV.Sentence := allSorted ![.rv, .rv] (pRV &0 ⟹ (pRV &1 ⟹ (pLe &0 &1 ⊔ pLe &1 &0)))
/-- `∞` is the top element of `RV` -/
def leTop : LRV.Sentence := allSorted ![.rv] (pRV &0 ⟹ pLe &0 tRVInfty)
/-- `∞ ≤ x` forces `x = ∞`, i.e. `∞` is alone in its class -/
def leInftyEq : LRV.Sentence := allSorted ![.rv] (pRV &0 ⟹ (pLe tRVInfty &0 ⟹ pEq &0 tRVInfty))
/-- `Kˣ` is the equivalence class of `1` -/
def leClassOne : LRV.Sentence :=
  allSorted ![.rv] (pRV &0 ⟹ (pUnits &0 ⇔ (pLe tRVOne &0 ⊓ pLe &0 tRVOne)))
/-- `≤` is compatible with `×` on the left, i.e. the induced order on `RV/Kˣ` is a
translation-invariant order -/
def leMulCompat : LRV.Sentence :=
  allSorted ![.rv, .rv, .rv] (pRV &0 ⟹ (pRV &1 ⟹ (pRV &2 ⟹ (pUnits &2 ⟹ (pLe &0 &1 ⟹ pLe (tRVMul &0 &2) (tRVMul &1 &2))))))
/-- Definition 2.2 item 4: `≤` is a preorder on `RV` with `∞` the top element and `Kˣ`
the equivalence class of `1`. -/
def preorderRV : LRV.Theory :=
  ofList [leRefl, leTrans, leTotal, leTop, leInftyEq, leClassOne, leMulCompat]

/-! ### 3.5 The projection `rv` (Definition 2.2 item 6) -/

/-- `rv(0) = ∞` -/
def rvZeroEq : LRV.Sentence := pEq (tRv tVFZero) tRVInfty
/-- `rv(x) = ∞` forces `x = 0` -/
def rvEqInfty : LRV.Sentence := allSorted ![.vf] (pEq (tRv &0) tRVInfty ⟹ pEq &0 tVFZero)
/-- `rv` is a group homomorphism on `VF^×` -/
def rvMulHom : LRV.Sentence :=
  allSorted ![.vf, .vf] (pEq (tRv (tVFMul &0 &1)) (tRVMul (tRv &0) (tRv &1)))
/-- **`rv` is surjective**: every element of the `RV` sort other than `rv(0)` is `rv(x)` for
some `x ∈ VF`.  (Definition 2.2(6): `rv : VF^× → RV^×` is surjective, augmented by
`rv(0) = ∞ = 0`.  With `RV^× = RV ∖ {0}` this says: `RV = rv(VF^×) ∪ {0}`, so there are no
`RV`-elements outside the image of `rv`.) -/
def rvSurj : LRV.Sentence :=
  allSorted ![.rv] (∼(pEq &0 tRVZero) ⟹ exSorted .vf (pEq (tRv &1) &0))
/-- the ultrametric inequality for `vv = vrv ∘ rv`: `vv(x+y) ≥ min(vv x, vv y)` -/
def rvUltrametric : LRV.Sentence :=
  allSorted ![.vf, .vf] (pLe (tRv &0) (tRv (tVFAdd &0 &1)) ⊔ pLe (tRv &1) (tRv (tVFAdd &0 &1)))

/-- Definition 2.2 item 6: `rv : VF^× → RV^×` is a surjective group homomorphism
augmented by `rv(0) = ∞`, and `vv = vrv ∘ rv` is a valuation.  (The valuation ring
`O = rv⁻¹(RV^{≥1})` and the maximal ideal `M = rv⁻¹(RV^{>1})` are *defined* from `rv`,
so — exactly as in the paper — they need no symbols of their own.) -/
def rvAxioms : LRV.Theory :=
  ofList [rvZeroEq, rvEqInfty, rvMulHom, rvSurj, rvUltrametric]

/-! ### 3.6 `ACVF` and `ACVF(0,0)` -/

/-! ### 3.6a The repaired axioms: `RV^×` is a group, the order scales, the residue field is
the residue field, and the valuation is nontrivial

Each sentence below is **added** to Definition 2.2's axioms, never substituted for one: every
`ACVF`-theorem proved before the repair stays proved, and each added sentence is true in the
intended structure.  They exist because the transcription of Definition 2.2 left four things unsaid,
and a model violating each of them refutes Theorem 2.3 (see `QE-PLAN.md` for the three explicit
refutations):

* `rvMulOneRV`, `rvMulInvRV` — item 2 makes `(RV^×, 1, ×)` a divisible **group**, i.e. decidability
  of `rv`-equality needs cancellation by any nonzero element, not only by units;
* `leMulCompatFull` — item 5 makes `RV/Kˣ = Γ` an **ordered** group, i.e. the order is invariant
  under scaling by any `c ≠ rv 0`, not only by `Kˣ` (which is the identity class of `Γ`);
* `kAddLink`, `kNegLink`, `rvEqLink`, `kJunkZero`, `kNegJunkZero` — items 3 and 6 say `K` is *the
  residue field* of `vv = vrv ∘ rv`; without a link through `rv`, `kAdd` may be any field addition
  on `K` sharing `×`, and twisting it by an automorphism of `(K^×, ·)` preserves every axiom while
  destroying quantifier elimination;
* `axNontrivialRV` — the target theorems are false for a trivially valued field: trivially and
  nontrivially valued fields of the same residue characteristic agree on every quantifier-free
  `L_RV` sentence, because closed terms are numerals and `rv` of numerals.
-/

/-- `1` is neutral for `×` on every nonzero `RV`-element. -/
def rvMulOneRV : LRV.Sentence := allSorted ![.rv] (pRV &0 ⟹ pEq (tRVMul tRVOne &0) &0)

/-- every nonzero `RV`-element is invertible in `RV^×`. -/
def rvMulInvRV : LRV.Sentence :=
  allSorted ![.rv] (pRV &0 ⟹ exSorted .rv (pRV &1 ⊓ pEq (tRVMul &1 &0) tRVOne))

/-- the order on `RV` is invariant under scaling by any `c ≠ rv 0`, in both directions.  The guards
on the first two variables are dropped because `∞ = rv 0` is absorbing and top, so both sides hold
there. -/
def leMulCompatFull : LRV.Sentence :=
  allSorted ![.rv, .rv, .rv] (pRV &2 ⟹ (pLe &0 &1 ⇔ pLe (tRVMul &0 &2) (tRVMul &1 &2)))

/-- `kAdd` is the residue addition at units: `rv (x + y)` if that is a unit, and `0` if `x + y`
drops into the maximal ideal. -/
def kAddLink : LRV.Sentence :=
  allSorted ![.vf, .vf]
    (pUnits (tRv &0) ⟹ (pUnits (tRv &1) ⟹
      ((pUnits (tRv (tVFAdd &0 &1)) ⟹
          pEq (tKAdd (tRv &0) (tRv &1)) (tRv (tVFAdd &0 &1))) ⊓
        (∼(pUnits (tRv (tVFAdd &0 &1))) ⟹
          pEq (tKAdd (tRv &0) (tRv &1)) tRVZero))))

/-- `kNeg` is the residue negation at units. -/
def kNegLink : LRV.Sentence :=
  allSorted ![.vf] (pUnits (tRv &0) ⟹ pEq (tKNeg (tRv &0)) (tRv (tVFNeg &0)))

/-- two elements of `VF` have the same residue iff their difference has strictly larger value than
the second: `rv a = rv b ↔ ¬ (v (a - b) ≤ v b)`.  (The first transcription had the two `pLe`
arguments transposed, which made the axiom false at `a = b = 1` and the whole theory
inconsistent — see `QE-PLAN.md` and `.ultramath/smw163dd5/m5/Audit.lean`.) -/
def rvEqLink : LRV.Sentence :=
  allSorted ![.vf, .vf]
    (∼(pEq &1 tVFZero) ⟹
      (pEq (tRv &0) (tRv &1) ⇔ ∼(pLe (tRv (tVFAdd &0 (tVFNeg &1))) (tRv &1))))

/-- the junk convention for `kAdd` off `K`: the value is `0`. -/
def kJunkZero : LRV.Sentence :=
  allSorted ![.rv, .rv] ((∼(pInK &0) ⊔ ∼(pInK &1)) ⟹ pEq (tKAdd &0 &1) tRVZero)

/-- the junk convention for `kNeg` off `K`. -/
def kNegJunkZero : LRV.Sentence := allSorted ![.rv] (∼(pInK &0) ⟹ pEq (tKNeg &0) tRVZero)

/-- **Nontriviality**: some nonzero element of `VF` has value strictly below the value of `1`,
i.e. lies in the maximal ideal. -/
def axNontrivialRV : LRV.Sentence :=
  exSorted .vf (∼(pEq &0 tVFZero) ⊓ ∼(pLe (tRv &0) (tRv tVFOne)))

/-- The added axioms, in one theory. -/
def repairRV : LRV.Theory :=
  ofList [rvMulOneRV, rvMulInvRV, leMulCompatFull, kAddLink, kNegLink, rvEqLink, kJunkZero,
    kNegJunkZero, axNontrivialRV]

/-- the paper's own content of `ACVF`: Definition 2.2, items 1–6 -/
def ACVFpaper : LRV.Theory :=
  vfField ∪ vfAlgClosed ∪ rvGroup ∪ kField ∪ kAlgClosed ∪ preorderRV ∪ rvAxioms ∪ repairRV ∪ repairRV

/-- **The theory `ACVF` of Definition 2.2**, in the tagged encoding: items 1–6 plus the
sort discipline of the encoding. -/
def ACVF : LRV.Theory := sortAxioms ∪ ACVFpaper

/-- characteristic zero of the `VF` sort -/
def charZeroVF (k : ℕ) : LRV.Sentence := ∼(pEq (tVFNumeral (k + 1)) tVFZero)

/-- residue characteristic zero: for each prime `p`, `p · 1` is a unit of the valuation
ring, i.e. `¬ (1 < rv(p·1))` -/
def residueCharZero (p : ℕ) : LRV.Sentence := ∼(pGtOne (tRv (tVFNumeral p)))

/-- the paper's content of `ACVF(0,0)`: `ACVF` together with pure characteristic `0` -/
def ACVF00paper : LRV.Theory :=
  ACVFpaper ∪ {s | ∃ k, s = charZeroVF k} ∪ {s | ∃ p, p.Prime ∧ s = residueCharZero p}

/-- **The theory `ACVF(0,0)`**: `ACVF` with pure characteristic `0`, i.e. characteristic
`0` for the valued field and characteristic `0` for its residue field. -/
def ACVF00 : LRV.Theory := ACVF ∪ {s | ∃ k, s = charZeroVF k} ∪ {s | ∃ p, p.Prime ∧ s = residueCharZero p}

end Axioms

end Milestone0
end SpecialTransformations

/-! ## 22b. `HasQE` and the interpretation of the symbols -/

namespace SpecialTransformations.Milestone0

/-! ## Part 6. The two target theorems, stated -/

open Axioms

/-- A theory `T` of `L_RV` **admits quantifier elimination**: every formula is
`T`-equivalent to a quantifier-free formula.  This is the paper's Theorem 2.3
("the theory `ACVF` admits quantifier elimination"). -/
def HasQE (T : LRV.Theory) : Prop :=
  ∀ (α : Type) (φ : LRV.Formula α), ∃ ψ : LRV.Formula α,
    FirstOrder.Language.BoundedFormula.IsQF ψ ∧ T ⊨ᵇ (φ ⇔ ψ)

/-! ### 6.1 The interpretation of the symbols in a model, for use in the statements -/

variable {M : Type*} [LRV.Structure M]

/-- `x` lies in the `VF` sort -/
def iVF (x : M) : Prop := FirstOrder.Language.Structure.RelMap (L := LRV) Rel.memVF ![x]

/-- `x` lies in the `RV` sort -/
def iRV (x : M) : Prop := FirstOrder.Language.Structure.RelMap (L := LRV) Rel.memRV ![x]

/-- `x ∈ Kˣ`, i.e. `x` satisfies the paper's unary predicate `Kˣ` -/
def iUnits (x : M) : Prop := FirstOrder.Language.Structure.RelMap (L := LRV) Rel.memUnits ![x]

/-- the preorder `≤` of the `RV` sort -/
def iLe (x y : M) : Prop := FirstOrder.Language.Structure.RelMap (L := LRV) Rel.rvLe ![x, y]

/-- the interpretation of `+` of the `VF` sort -/
def iVFAdd (x y : M) : M := FirstOrder.Language.Structure.funMap (L := LRV) Fn.vfAdd ![x, y]

/-- the interpretation of `-` of the `VF` sort -/
def iVFNeg (x : M) : M := FirstOrder.Language.Structure.funMap (L := LRV) Fn.vfNeg ![x]

/-- the interpretation of `×` of the `VF` sort -/
def iVFMul (x y : M) : M := FirstOrder.Language.Structure.funMap (L := LRV) Fn.vfMul ![x, y]

/-- the interpretation of `+ : K² → K` of the `RV` sort -/
def iKAdd (x y : M) : M := FirstOrder.Language.Structure.funMap (L := LRV) Fn.kAdd ![x, y]

/-- the interpretation of `×` of the `RV` sort -/
def iRVMul (x y : M) : M := FirstOrder.Language.Structure.funMap (L := LRV) Fn.rvMul ![x, y]

/-- the interpretation of the projection `rv : VF → RV` -/
def iRv (x : M) : M := FirstOrder.Language.Structure.funMap (L := LRV) Fn.rvMap ![x]

/-- the interpretation of `0` of the `RV` sort -/
def iRVZero : M := FirstOrder.Language.Structure.funMap (L := LRV) Fn.rvZero fun i => i.elim0

/-- The interpretation of the paper's `∞`, which is the interpretation of `0` of the `RV` sort -/
def iRVInfty : M := iRVZero (M := M)

/-- the interpretation of `1` of the `RV` sort -/
def iRVOne : M := FirstOrder.Language.Structure.funMap (L := LRV) Fn.rvOne fun i => i.elim0

/-- `b` is a **closed ball** in the sense of Definition 2.6: there are `a ∈ VF` and a
radius `γ = vrv(t)` — i.e. an `RV`-element `t ≠ 0`, since the preorder is only defined on
`RV = RV ∖ {0}` — such that `b = {x ∈ VF : t ≤ rv(x - a)}`.  With `t = ∞` this is the
degenerate ball `{a}`. -/
def IsClosedBall (b : Set M) : Prop :=
  ∃ a t : M, iVF a ∧ iRV t ∧ t ≠ iRVZero ∧
    b = {x | iVF x ∧ iLe t (iRv (iVFAdd x (iVFNeg a)))}

/-- `b` is an **open ball**: `{x ∈ VF : t < rv(x - a)}` for a radius `t ≠ 0`, together
with the paper's convention `O(a, ∞) = C(a, ∞) = {a}`. -/
def IsOpenBall (b : Set M) : Prop :=
  (∃ a t : M, iVF a ∧ iRV t ∧ t ≠ iRVZero ∧
      b = {x | iVF x ∧ iLe t (iRv (iVFAdd x (iVFNeg a))) ∧
        ¬ iLe (iRv (iVFAdd x (iVFNeg a))) t}) ∨
    ∃ a : M, iVF a ∧ b = {x | iVF x ∧ x = a}

/-- **A ball** in the sense of Definition 2.6: `VF` itself (the ball of radius `-∞`), a
closed ball, or an open ball. -/
def IsBall (b : Set M) : Prop :=
  b = {x | iVF x} ∨ IsClosedBall b ∨ IsOpenBall b

/-- the Boolean algebra generated by a family of subsets -/
inductive IsBoolComb (B : Set (Set M)) : Set M → Prop
  /-- a member of the family -/
  | basic {b : Set M} : b ∈ B → IsBoolComb B b
  /-- the whole carrier -/
  | univ : IsBoolComb B Set.univ
  /-- complements -/
  | compl {s : Set M} : IsBoolComb B s → IsBoolComb B sᶜ
  /-- finite unions -/
  | union {s t : Set M} : IsBoolComb B s → IsBoolComb B t → IsBoolComb B (s ∪ t)

/-- **C-minimality** (Definition 2.7): every parametrically definable subset of the
`VF` sort is a Boolean combination of balls. -/
def IsCMinimal (M : Type*) [LRV.Structure M] : Prop :=
  ∀ (A : Set M) (s : Set M), A.Definable₁ LRV s → IsBoolComb {b | IsBall b} s

/-- **Theorem 2.3** (Yin, *Special transformations in algebraically closed valued
fields*, APAL 2010; quoted there from arXiv:1006.1393, Theorem 3.10): the theory `ACVF`
admits quantifier elimination. -/
theorem theorem_2_3_quantifier_elimination : HasQE ACVF := by
  sorry

/-- **Theorem 2.8** (Yin, op. cit.; quoted from arXiv:1006.1393, Theorem 4.2):
`ACVF` is C-minimal, i.e. every model of `ACVF` is C-minimal in the sense of
Definition 2.7. -/
theorem theorem_2_8_c_minimal :
    ∀ (M : Type) [LRV.Structure M] [Nonempty M], M ⊨ ACVF → IsCMinimal M := by
  sorry

/-! ## Part 7. Definable subsets of `VF^n × RV^m`

The paper's Notation 2.10 indexes the coordinates of a subset of `VF^n × RV^m` by
`I_n ⊎ I_m`.  In the encoding that disjoint union is the type `Fin n ⊕ Fin m`, which is
exactly Mathlib's index type for `Definable`-sets of tuples: no translation is needed. -/


end SpecialTransformations.Milestone0

/-! ## 23. The transfer `L_val → L_RV`: the syntactic translation -/

namespace SpecialTransformations.Milestone0.Transfer

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 LRV

/-! ### Terms -/

/-- `L_val`-terms with variables among `Fin n` translate into `L_RV`-terms: the ring symbols
become the `VF`-sorted symbols of `L_RV`.  There are no parameters, so this is complete. -/
def valTermToRV {n : ℕ} : Language.val.Term (Empty ⊕ Fin n) → Tm n
  | .var v => Sum.rec (fun e => e.elim) (fun i => tv i.1 i.2) v
  | .func f args =>
    match f with
    | ValFunc.add => tVFAdd (valTermToRV (args 0)) (valTermToRV (args 1))
    | ValFunc.mul => tVFMul (valTermToRV (args 0)) (valTermToRV (args 1))
    | ValFunc.neg => tVFNeg (valTermToRV (args 0))
    | ValFunc.zero => tVFZero
    | ValFunc.one => tVFOne

/-- `0` of the `VF` sort, as an element of an `L_RV`-structure. -/
def iVFZero {M : Type} [LRV.Structure M] : M :=
  FirstOrder.Language.Structure.funMap (L := LRV) Fn.vfZero fun i => i.elim0

/-- `1` of the `VF` sort, as an element of an `L_RV`-structure. -/
def iVFOne {M : Type} [LRV.Structure M] : M :=
  FirstOrder.Language.Structure.funMap (L := LRV) Fn.vfOne fun i => i.elim0

/-- The same term read in an `L_RV`-structure, using the `VF`-sorted operations. -/
def valTermEval {M : Type} [LRV.Structure M] {n : ℕ} (x : Fin n → M) :
    Language.val.Term (Empty ⊕ Fin n) → M
  | .var v => Sum.rec (fun e => e.elim) (fun i => x i) v
  | .func f args =>
    match f with
    | ValFunc.add => iVFAdd (valTermEval x (args 0)) (valTermEval x (args 1))
    | ValFunc.mul => iVFMul (valTermEval x (args 0)) (valTermEval x (args 1))
    | ValFunc.neg => iVFNeg (valTermEval x (args 0))
    | ValFunc.zero => iVFZero
    | ValFunc.one => iVFOne

/-! ### How `L_RV` reads the translated symbols -/

theorem realize_tVFZero {M : Type} [LRV.Structure M] {n : ℕ} (v : Empty ⊕ Fin n → M) :
    (tVFZero (n := n)).realize v = iVFZero := by
  show FirstOrder.Language.Structure.funMap (L := LRV) Fn.vfZero
      (fun i => Term.realize (L := LRV) v ((fun j : Fin 0 => j.elim0) i)) = iVFZero
  rw [show (fun i => Term.realize (L := LRV) v ((fun j : Fin 0 => j.elim0) i))
      = (fun i => i.elim0) from by funext i; exact i.elim0]
  rfl

theorem realize_tVFOne {M : Type} [LRV.Structure M] {n : ℕ} (v : Empty ⊕ Fin n → M) :
    (tVFOne (n := n)).realize v = iVFOne := by
  show FirstOrder.Language.Structure.funMap (L := LRV) Fn.vfOne
      (fun i => Term.realize (L := LRV) v ((fun j : Fin 0 => j.elim0) i)) = iVFOne
  rw [show (fun i => Term.realize (L := LRV) v ((fun j : Fin 0 => j.elim0) i))
      = (fun i => i.elim0) from by funext i; exact i.elim0]
  rfl

theorem realize_tVFAdd {M : Type} [LRV.Structure M] {n : ℕ} (v : Empty ⊕ Fin n → M)
    (a b : Tm n) : (tVFAdd a b).realize v = iVFAdd (a.realize v) (b.realize v) := by
  show FirstOrder.Language.Structure.funMap (L := LRV) Fn.vfAdd
      (fun i => Term.realize (L := LRV) v (![a, b] i)) = iVFAdd (a.realize v) (b.realize v)
  rw [show (fun i => Term.realize (L := LRV) v (![a, b] i)) = ![a.realize v, b.realize v] from by
    funext i
    fin_cases i <;> simp]
  rfl

theorem realize_tVFMul {M : Type} [LRV.Structure M] {n : ℕ} (v : Empty ⊕ Fin n → M)
    (a b : Tm n) : (tVFMul a b).realize v = iVFMul (a.realize v) (b.realize v) := by
  show FirstOrder.Language.Structure.funMap (L := LRV) Fn.vfMul
      (fun i => Term.realize (L := LRV) v (![a, b] i)) = iVFMul (a.realize v) (b.realize v)
  rw [show (fun i => Term.realize (L := LRV) v (![a, b] i)) = ![a.realize v, b.realize v] from by
    funext i
    fin_cases i <;> simp]
  rfl

theorem realize_tVFNeg {M : Type} [LRV.Structure M] {n : ℕ} (v : Empty ⊕ Fin n → M)
    (a : Tm n) : (tVFNeg a).realize v = iVFNeg (a.realize v) := by
  show FirstOrder.Language.Structure.funMap (L := LRV) Fn.vfNeg
      (fun i => Term.realize (L := LRV) v (![a] i)) = iVFNeg (a.realize v)
  rw [show (fun i => Term.realize (L := LRV) v (![a] i)) = ![a.realize v] from by
    funext i
    fin_cases i
    simp]
  rfl

/-- **A translated term realises as the `L_val`-evaluation**: this is where the two languages'
ring symbols are matched up. -/
theorem valTermToRV_realize {M : Type} [LRV.Structure M] {n : ℕ} (x : Fin n → M)
    (t : Language.val.Term (Empty ⊕ Fin n)) :
    (valTermToRV t).realize (Sum.elim (default : Empty → M) x) = valTermEval x t := by
  induction t with
  | var v =>
    rcases v with e | i
    · exact e.elim
    · simp [valTermToRV, valTermEval, tv, Term.realize]
  | func f args ih =>
    cases f with
    | add => simp only [valTermToRV, valTermEval, realize_tVFAdd, ih 0, ih 1]
    | mul => simp only [valTermToRV, valTermEval, realize_tVFMul, ih 0, ih 1]
    | neg => simp only [valTermToRV, valTermEval, realize_tVFNeg, ih 0]
    | zero => simp only [valTermToRV, valTermEval, realize_tVFZero]
    | one => simp only [valTermToRV, valTermEval, realize_tVFOne]

/-! ### Formulas -/

/-- **The syntactic translation of `L_val`-formulas into `L_RV`.**  The predicate `v x ≤ v y`
becomes `rv x ≤ rv y`, which is the paper's identification `vv = vrv ∘ rv`; everything else is
symbol-for-symbol.  `BoundedFormula` has five constructors, so `⊓`, `⊔`, `∃` and `¬` are handled
through their definitions. -/
def valFormulaToRV {n : ℕ} : Language.val.BoundedFormula Empty n → Bf n
  | BoundedFormula.falsum => BoundedFormula.falsum
  | BoundedFormula.equal t u => BoundedFormula.equal (valTermToRV t) (valTermToRV u)
  | BoundedFormula.rel r ts =>
    match r with
    | ValRel.le => pLe (tRv (valTermToRV (ts 1))) (tRv (valTermToRV (ts 0)))
  | BoundedFormula.imp φ ψ => BoundedFormula.imp (valFormulaToRV φ) (valFormulaToRV ψ)
  | BoundedFormula.all φ => BoundedFormula.all (valFormulaToRV φ)

/-! ### Realization of translated formulas -/

theorem realize_tRv {M : Type} [LRV.Structure M] {n : ℕ} (v : Empty ⊕ Fin n → M) (a : Tm n) :
    (tRv a).realize v = iRv (a.realize v) := by
  show FirstOrder.Language.Structure.funMap (L := LRV) Fn.rvMap
      (fun i => Term.realize (L := LRV) v (![a] i)) = iRv (a.realize v)
  rw [show (fun i => Term.realize (L := LRV) v (![a] i)) = ![a.realize v] from by
    funext i
    fin_cases i
    simp]
  rfl

theorem realize_pLe {M : Type} [LRV.Structure M] {n : ℕ} (a b : Tm n) (v : Empty → M)
    (x : Fin n → M) :
    (pLe a b).Realize v x ↔ iLe (a.realize (Sum.elim v x)) (b.realize (Sum.elim v x)) := by
  have h : (fun i => Term.realize (L := LRV) (Sum.elim v x) (![a, b] i))
      = ![a.realize (Sum.elim v x), b.realize (Sum.elim v x)] := by
    funext i
    fin_cases i <;> simp
  show FirstOrder.Language.Structure.RelMap (L := LRV) Rel.rvLe
      (fun i => Term.realize (L := LRV) (Sum.elim v x) (![a, b] i)) ↔ iLe
        (a.realize (Sum.elim v x)) (b.realize (Sum.elim v x))
  rw [h]
  rfl

/-- Reading an `L_val`-formula in an `L_RV`-structure: variables are elements of the carrier, the
ring symbols are the `VF`-sorted ones, and the predicate is `vv x ≤ vv y` with `vv = vrv ∘ rv`. -/
def valFormulaEval {M : Type} [LRV.Structure M] {n : ℕ} (x : Fin n → M) :
    Language.val.BoundedFormula Empty n → Prop
  | BoundedFormula.falsum => False
  | BoundedFormula.equal t u => valTermEval x t = valTermEval x u
  | BoundedFormula.rel r ts =>
    match r with
    | ValRel.le => iLe (iRv (valTermEval x (ts 1))) (iRv (valTermEval x (ts 0)))
  | BoundedFormula.imp φ ψ => valFormulaEval x φ → valFormulaEval x ψ
  | BoundedFormula.all φ => ∀ a : M, valFormulaEval (Fin.snoc x a) φ

/-- **A translated formula realises exactly as the `L_val`-formula does**, read in the `L_RV`-
structure.  This is the semantic half of step 1 of the transfer. -/
theorem valFormulaToRV_realize {M : Type} [LRV.Structure M] {n : ℕ}
    (φ : Language.val.BoundedFormula Empty n) (x : Fin n → M) :
    (valFormulaToRV φ).Realize (default : Empty → M) x ↔ valFormulaEval x φ := by
  induction φ with
  | falsum => exact Iff.rfl
  | equal t u =>
    show (valTermToRV t).realize (Sum.elim (default : Empty → M) x)
        = (valTermToRV u).realize (Sum.elim (default : Empty → M) x)
      ↔ valTermEval x t = valTermEval x u
    rw [valTermToRV_realize x t, valTermToRV_realize x u]
  | rel r ts =>
    cases r with
    | le =>
      rw [valFormulaToRV, realize_pLe, realize_tRv, realize_tRv, valTermToRV_realize,
        valTermToRV_realize]
      exact Iff.rfl
  | imp φ ψ ihφ ihψ =>
    simp only [valFormulaToRV, valFormulaEval, BoundedFormula.realize_imp, ihφ, ihψ]
  | all φ ih =>
    simp only [valFormulaToRV, valFormulaEval, BoundedFormula.realize_all, ih]

/-! ### The `L_val`-structure induced by an `L_RV`-structure -/

/-- The `L_val`-structure that an `L_RV`-structure induces on its carrier: the ring symbols are the
`VF`-sorted ones and the predicate is `vv x ≤ vv y` with `vv = vrv ∘ rv` (Definition 2.2).

This is a structure on the **whole** carrier; the field axioms of `valField` hold only on the `VF`
sort, so anything that uses them is stated for tuples with all entries in `VF`. -/
@[instance_reducible]
def valStructOfLRV (M : Type) [LRV.Structure M] : Language.val.Structure M where
  funMap := fun {_} f x =>
    match f with
    | ValFunc.add => iVFAdd (x 0) (x 1)
    | ValFunc.mul => iVFMul (x 0) (x 1)
    | ValFunc.neg => iVFNeg (x 0)
    | ValFunc.zero => iVFZero
    | ValFunc.one => iVFOne
  RelMap := fun {_} r x =>
    match r with
    | ValRel.le => iLe (iRv (x 1)) (iRv (x 0))

/-- **Terms evaluate the same way** in `valStructOfLRV M` as by `valTermEval`. -/
theorem realize_valTermEval {M : Type} [LRV.Structure M] {n : ℕ} (x : Fin n → M)
    (t : Language.val.Term (Empty ⊕ Fin n)) :
    @Term.realize Language.val M (valStructOfLRV M) (Empty ⊕ Fin n)
        (Sum.elim (default : Empty → M) x) t = valTermEval x t := by
  induction t with
  | var v =>
    rcases v with e | i
    · exact e.elim
    · rfl
  | func f args ih =>
    cases f with
    | add =>
      show iVFAdd (@Term.realize Language.val M (valStructOfLRV M) (Empty ⊕ Fin n)
          (Sum.elim default x) (args 0)) (@Term.realize Language.val M (valStructOfLRV M)
            (Empty ⊕ Fin n) (Sum.elim default x) (args 1)) = _
      rw [ih 0, ih 1]
      rfl
    | mul =>
      show iVFMul (@Term.realize Language.val M (valStructOfLRV M) (Empty ⊕ Fin n)
          (Sum.elim default x) (args 0)) (@Term.realize Language.val M (valStructOfLRV M)
            (Empty ⊕ Fin n) (Sum.elim default x) (args 1)) = _
      rw [ih 0, ih 1]
      rfl
    | neg =>
      show iVFNeg (@Term.realize Language.val M (valStructOfLRV M) (Empty ⊕ Fin n)
          (Sum.elim default x) (args 0)) = _
      rw [ih 0]
      rfl
    | zero => rfl
    | one => rfl

-- NOTE.  `valFormulaEval` is by construction the `L_val`-realisation in `valStructOfLRV M`; the
-- identification `valFormulaEval x φ ↔ (φ.Realize default x in valStructOfLRV M)` is therefore
-- true by the same recursion, but stating it runs into `RelMap`'s implicit-language argument
-- (the raw `BoundedFormula.rel` constructor versus the `Relations.boundedFormula` wrapper that
-- `BoundedFormula.realize_rel` is stated for).  It is not needed: `valFormulaToRV_realize` above
-- is the substantive statement, and the model correspondence works directly with
-- `valStructOfLRV`.

/-! ### The sort discipline, semantically -/

theorem realize_tv {M : Type} [LRV.Structure M] {k : ℕ} (i : Fin k) (v : Empty → M)
    (x : Fin k → M) : (tv i.1 i.2).realize (Sum.elim v x) = x i := rfl

theorem pVF_realize {M : Type} [LRV.Structure M] {k : ℕ} (t : Tm k) (v : Empty → M)
    (x : Fin k → M) : (pVF t).Realize v x ↔ iVF (t.realize (Sum.elim v x)) := by
  show FirstOrder.Language.Structure.RelMap (L := LRV) Rel.memVF
      (fun i => Term.realize (L := LRV) (Sum.elim v x) (![t] i))
      ↔ iVF (t.realize (Sum.elim v x))
  rw [show (fun i => Term.realize (L := LRV) (Sum.elim v x) (![t] i))
      = ![t.realize (Sum.elim v x)] from by
    funext i
    fin_cases i
    simp]
  rfl

theorem pRVsort_realize {M : Type} [LRV.Structure M] {k : ℕ} (t : Tm k) (v : Empty → M)
    (x : Fin k → M) : (pRVsort t).Realize v x ↔ iRV (t.realize (Sum.elim v x)) := by
  show FirstOrder.Language.Structure.RelMap (L := LRV) Rel.memRV
      (fun i => Term.realize (L := LRV) (Sum.elim v x) (![t] i))
      ↔ iRV (t.realize (Sum.elim v x))
  rw [show (fun i => Term.realize (L := LRV) (Sum.elim v x) (![t] i))
      = ![t.realize (Sum.elim v x)] from by
    funext i
    fin_cases i
    simp]
  rfl

theorem sortPred_realize {M : Type} [LRV.Structure M] {k : ℕ} (s : SortTag) (t : Tm k)
    (v : Empty → M) (x : Fin k → M) :
    (sortPred s t).Realize v x ↔
      (match s with
        | .vf => iVF (t.realize (Sum.elim v x))
        | .rv => iRV (t.realize (Sum.elim v x))) := by
  cases s with
  | vf => exact pVF_realize t v x
  | rv => exact pRVsort_realize t v x

/-- **The conjunction of sort hypotheses realises as the pointwise sort conditions.** -/
theorem sortedHyps_foldr_realize {M : Type} [LRV.Structure M] {k : ℕ} (ss : Fin k → SortTag)
    (l : List (Fin k)) (v : Empty → M) (x : Fin k → M) :
    (l.foldr (fun i acc => sortPred (ss i) (tv i.1 i.2) ⊓ acc) ⊤).Realize v x
      ↔ ∀ i ∈ l, (match ss i with
          | .vf => iVF (x i)
          | .rv => iRV (x i)) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.foldr_cons, BoundedFormula.realize_inf, ih]
    have hhead : (sortPred (ss a) (tv a.1 a.2)).Realize v x
        ↔ (match ss a with | .vf => iVF (x a) | .rv => iRV (x a)) := by
      rw [sortPred_realize, realize_tv]
    rw [hhead]
    constructor
    · rintro ⟨ha, hall⟩ i hi
      rcases List.mem_cons.mp hi with rfl | hi
      · exact ha
      · exact hall i hi
    · intro h
      exact ⟨h a List.mem_cons_self, fun i hi => h i (List.mem_cons_of_mem a hi)⟩

/-- **The gateway lemma**: `sortedHyps ss` realises as the pointwise sort conditions. -/
theorem sortedHyps_realize {M : Type} [LRV.Structure M] {k : ℕ} (ss : Fin k → SortTag)
    (v : Empty → M) (x : Fin k → M) :
    (sortedHyps ss).Realize v x ↔ ∀ i, (match ss i with
        | .vf => iVF (x i)
        | .rv => iRV (x i)) := by
  rw [sortedHyps, sortedHyps_foldr_realize]
  constructor
  · intro h i
    exact h i (List.mem_finRange i)
  · intro h i _
    exact h i

/-- **Uniform extraction from an `allSorted`-guarded sentence.**  If `∀ x̄ ∈ s̄, φ` is in a theory
`T` and `M ⊨ T`, then `φ` holds at every tuple of the prescribed sorts.  Every axiom of `ACVF`
that constrains the `VF` order or the `RV` order has this shape. -/
theorem allSorted_realize {M : Type} [LRV.Structure M] {T : LRV.Theory} (hM : M ⊨ T)
    {k : ℕ} {ss : Fin k → SortTag} {φ : Bf k} (hmem : allSorted ss φ ∈ T) :
    ∀ x : Fin k → M, (∀ i, (match ss i with
        | .vf => iVF (x i)
        | .rv => iRV (x i)))
      → @BoundedFormula.Realize LRV M _ Empty k φ (default : Empty → M) x := by
  intro x hx
  have h := hM.realize_of_mem (allSorted ss φ) hmem
  simp only [allSorted, Sentence.Realize, BoundedFormula.realize_alls,
    BoundedFormula.realize_imp] at h
  exact h x ((sortedHyps_realize ss (default : Empty → M) x).mpr hx)

/-- Extraction from a sentence closed by a single universal quantifier. -/
theorem allOne_realize {M : Type} [LRV.Structure M] {T : LRV.Theory} (hM : M ⊨ T)
    {φ : Bf 1} (hmem : allOne φ ∈ T) :
    ∀ x : Fin 1 → M,
      @BoundedFormula.Realize LRV M _ Empty 1 φ (default : Empty → M) x := by
  intro x
  have h := hM.realize_of_mem (allOne φ) hmem
  simp only [allOne, Sentence.Realize, BoundedFormula.realize_alls] at h
  exact h x

/-- Extraction from a sentence with no quantifiers. -/
theorem sentence_realize {M : Type} [LRV.Structure M] {T : LRV.Theory} (hM : M ⊨ T)
    {φ : LRV.Sentence} (hmem : φ ∈ T) : M ⊨ φ :=
  hM.realize_of_mem φ hmem
/-! ### Membership of the axioms, and closure of the `VF` sort -/

/-- A member of the sort closure is an axiom of `ACVF`. -/
theorem mem_ACVF_sortClosure {s : LRV.Sentence} (h : s ∈ Axioms.sortClosure) : s ∈ Axioms.ACVF := by
  simp only [Axioms.ACVF, Axioms.sortAxioms, Set.mem_union]
  tauto

/-- A member of `vfField` is an axiom of `ACVF`. -/
theorem mem_ACVF_vfField {s : LRV.Sentence} (h : s ∈ Axioms.vfField) : s ∈ Axioms.ACVF := by
  simp only [Axioms.ACVF, Axioms.ACVFpaper, Set.mem_union]
  tauto

/-- A member of `vfAlgClosed` is an axiom of `ACVF`. -/
theorem mem_ACVF_vfAlgClosed {s : LRV.Sentence} (h : s ∈ Axioms.vfAlgClosed) : s ∈ Axioms.ACVF := by
  simp only [Axioms.ACVF, Axioms.ACVFpaper, Set.mem_union]
  tauto

/-- A member of `preorderRV` is an axiom of `ACVF`. -/
theorem mem_ACVF_preorderRV {s : LRV.Sentence} (h : s ∈ Axioms.preorderRV) : s ∈ Axioms.ACVF := by
  simp only [Axioms.ACVF, Axioms.ACVFpaper, Set.mem_union]
  tauto

/-- A member of `rvAxioms` is an axiom of `ACVF`. -/
theorem mem_ACVF_rvAxioms {s : LRV.Sentence} (h : s ∈ Axioms.rvAxioms) : s ∈ Axioms.ACVF := by
  simp only [Axioms.ACVF, Axioms.ACVFpaper, Set.mem_union]
  tauto

theorem mem_ACVF_sdVFZero : Axioms.sdVFZero ∈ Axioms.ACVF :=
  mem_ACVF_sortClosure (by simp [Axioms.sortClosure, Axioms.ofList])

theorem mem_ACVF_sdVFOne : Axioms.sdVFOne ∈ Axioms.ACVF :=
  mem_ACVF_sortClosure (by simp [Axioms.sortClosure, Axioms.ofList])

theorem mem_ACVF_sdVFAdd : Axioms.sdVFAdd ∈ Axioms.ACVF :=
  mem_ACVF_sortClosure (by simp [Axioms.sortClosure, Axioms.ofList])

theorem mem_ACVF_sdVFNeg : Axioms.sdVFNeg ∈ Axioms.ACVF :=
  mem_ACVF_sortClosure (by simp [Axioms.sortClosure, Axioms.ofList])

theorem mem_ACVF_sdVFMul : Axioms.sdVFMul ∈ Axioms.ACVF :=
  mem_ACVF_sortClosure (by simp [Axioms.sortClosure, Axioms.ofList])

/-- `0` of the ring language lies in the `VF` sort. -/
theorem vf_zero_mem {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) :
    iVF (iVFZero (M := M)) := by
  have h := sentence_realize hM (φ := Axioms.sdVFZero) mem_ACVF_sdVFZero
  rw [Axioms.sdVFZero, Sentence.Realize] at h
  simp only [Formula.Realize] at h
  rw [pVF_realize, realize_tVFZero] at h
  exact h

/-- `1` of the ring language lies in the `VF` sort. -/
theorem vf_one_mem {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) :
    iVF (iVFOne (M := M)) := by
  have h := sentence_realize hM (φ := Axioms.sdVFOne) mem_ACVF_sdVFOne
  rw [Axioms.sdVFOne, Sentence.Realize] at h
  simp only [Formula.Realize] at h
  rw [pVF_realize, realize_tVFOne] at h
  exact h

/-- The `VF` sort is closed under `+`. -/
theorem vf_add_mem {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {x y : M}
    (hx : iVF x) (hy : iVF y) : iVF (iVFAdd x y) := by
  have h := allSorted_realize hM (T := Axioms.ACVF) mem_ACVF_sdVFAdd ![x, y] (by
    intro i
    fin_cases i <;> simp [hx, hy])
  rw [pVF_realize, realize_tVFAdd] at h
  simpa using h

/-- The `VF` sort is closed under `-`. -/
theorem vf_neg_mem {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {x : M}
    (hx : iVF x) : iVF (iVFNeg x) := by
  have h := allSorted_realize hM (T := Axioms.ACVF) mem_ACVF_sdVFNeg ![x] (by
    intro i
    fin_cases i
    simpa using hx)
  rw [pVF_realize, realize_tVFNeg] at h
  simpa using h

/-- The `VF` sort is closed under `×`. -/
theorem vf_mul_mem {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {x y : M}
    (hx : iVF x) (hy : iVF y) : iVF (iVFMul x y) := by
  have h := allSorted_realize hM (T := Axioms.ACVF) mem_ACVF_sdVFMul ![x, y] (by
    intro i
    fin_cases i <;> simp [hx, hy])
  rw [pVF_realize, realize_tVFMul] at h
  simpa using h

/-! ### The field laws on the `VF` sort -/

/-- Extract an equation from an `allSorted`-guarded `pEq` sentence. -/
theorem eq_of_allSorted {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {k : ℕ}
    {ss : Fin k → SortTag} {a b : Tm k} (hmem : allSorted ss (pEq a b) ∈ Axioms.ACVF)
    (x : Fin k → M) (hx : ∀ i, (match ss i with
      | .vf => iVF (x i)
      | .rv => iRV (x i))) :
    a.realize (Sum.elim (default : Empty → M) x)
      = b.realize (Sum.elim (default : Empty → M) x) := by
  have h := allSorted_realize hM hmem x hx
  simpa only [pEq, BoundedFormula.realize_bdEqual] using h

/-- The reduction of the `VF` field axioms to a list membership in `vfField`. -/
theorem mem_vfField {s : LRV.Sentence} (h : s ∈ Axioms.vfField) : s ∈ Axioms.ACVF :=
  mem_ACVF_vfField h

theorem vf_add_assoc {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {x y z : M}
    (hx : iVF x) (hy : iVF y) (hz : iVF z) :
    iVFAdd (iVFAdd x y) z = iVFAdd x (iVFAdd y z) := by
  have hmem : allSorted ![.vf, .vf, .vf]
      (pEq (tVFAdd (tVFAdd &0 &1) &2) (tVFAdd &0 (tVFAdd &1 &2))) ∈ Axioms.ACVF :=
    mem_vfField (by simp [Axioms.vfField, Axioms.ofList, Axioms.fieldAxioms])
  have h := eq_of_allSorted hM hmem ![x, y, z] (by intro i; fin_cases i <;> simp [hx, hy, hz])
  simpa [realize_tVFAdd, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    using h

theorem vf_add_comm {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {x y : M}
    (hx : iVF x) (hy : iVF y) : iVFAdd x y = iVFAdd y x := by
  have hmem : allSorted ![.vf, .vf] (pEq (tVFAdd &0 &1) (tVFAdd &1 &0)) ∈ Axioms.ACVF :=
    mem_vfField (by simp [Axioms.vfField, Axioms.ofList, Axioms.fieldAxioms])
  have h := eq_of_allSorted hM hmem ![x, y] (by intro i; fin_cases i <;> simp [hx, hy])
  simpa [realize_tVFAdd, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] using h

theorem vf_add_zero {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {x : M}
    (hx : iVF x) : iVFAdd x iVFZero = x := by
  have hmem : allSorted ![.vf] (pEq (tVFAdd &0 tVFZero) &0) ∈ Axioms.ACVF :=
    mem_vfField (by simp [Axioms.vfField, Axioms.ofList, Axioms.fieldAxioms])
  have h := eq_of_allSorted hM hmem ![x] (by intro i; fin_cases i; simpa using hx)
  simpa [realize_tVFAdd, realize_tVFZero, Matrix.cons_val_zero] using h

theorem vf_add_neg {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {x : M}
    (hx : iVF x) : iVFAdd x (iVFNeg x) = iVFZero := by
  have hmem : allSorted ![.vf] (pEq (tVFAdd &0 (tVFNeg &0)) tVFZero) ∈ Axioms.ACVF :=
    mem_vfField (by simp [Axioms.vfField, Axioms.ofList, Axioms.fieldAxioms])
  have h := eq_of_allSorted hM hmem ![x] (by intro i; fin_cases i; simpa using hx)
  simpa [realize_tVFAdd, realize_tVFNeg, realize_tVFZero, Matrix.cons_val_zero] using h

theorem vf_mul_assoc {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {x y z : M}
    (hx : iVF x) (hy : iVF y) (hz : iVF z) :
    iVFMul (iVFMul x y) z = iVFMul x (iVFMul y z) := by
  have hmem : allSorted ![.vf, .vf, .vf]
      (pEq (tVFMul (tVFMul &0 &1) &2) (tVFMul &0 (tVFMul &1 &2))) ∈ Axioms.ACVF :=
    mem_vfField (by simp [Axioms.vfField, Axioms.ofList, Axioms.fieldAxioms])
  have h := eq_of_allSorted hM hmem ![x, y, z] (by intro i; fin_cases i <;> simp [hx, hy, hz])
  simpa [realize_tVFMul, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    using h

theorem vf_mul_comm {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {x y : M}
    (hx : iVF x) (hy : iVF y) : iVFMul x y = iVFMul y x := by
  have hmem : allSorted ![.vf, .vf] (pEq (tVFMul &0 &1) (tVFMul &1 &0)) ∈ Axioms.ACVF :=
    mem_vfField (by simp [Axioms.vfField, Axioms.ofList, Axioms.fieldAxioms])
  have h := eq_of_allSorted hM hmem ![x, y] (by intro i; fin_cases i <;> simp [hx, hy])
  simpa [realize_tVFMul, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] using h

theorem vf_mul_one {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {x : M}
    (hx : iVF x) : iVFMul x iVFOne = x := by
  have hmem : allSorted ![.vf] (pEq (tVFMul &0 tVFOne) &0) ∈ Axioms.ACVF :=
    mem_vfField (by simp [Axioms.vfField, Axioms.ofList, Axioms.fieldAxioms])
  have h := eq_of_allSorted hM hmem ![x] (by intro i; fin_cases i; simpa using hx)
  simpa [realize_tVFMul, realize_tVFOne, Matrix.cons_val_zero] using h

theorem vf_left_distrib {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {x y z : M}
    (hx : iVF x) (hy : iVF y) (hz : iVF z) :
    iVFMul x (iVFAdd y z) = iVFAdd (iVFMul x y) (iVFMul x z) := by
  have hmem : allSorted ![.vf, .vf, .vf]
      (pEq (tVFMul &0 (tVFAdd &1 &2)) (tVFAdd (tVFMul &0 &1) (tVFMul &0 &2)))
      ∈ Axioms.ACVF :=
    mem_vfField (by simp [Axioms.vfField, Axioms.ofList, Axioms.fieldAxioms])
  have h := eq_of_allSorted hM hmem ![x, y, z] (by intro i; fin_cases i <;> simp [hx, hy, hz])
  simpa [realize_tVFAdd, realize_tVFMul, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons] using h

/-- `0 ≠ 1` on the `VF` sort. -/
theorem vf_zero_ne_one {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) :
    iVFZero (M := M) ≠ iVFOne := by
  have hmem : (∼(pEq tVFZero tVFOne)) ∈ Axioms.ACVF :=
    mem_vfField (by simp [Axioms.vfField, Axioms.ofList, Axioms.fieldAxioms])
  have h := sentence_realize hM hmem
  rw [Sentence.Realize] at h
  simp only [Formula.Realize, BoundedFormula.realize_not, pEq, BoundedFormula.realize_bdEqual,
    realize_tVFZero, realize_tVFOne] at h
  exact h

/-- **The invertibility law**: a `VF`-element is `0` or has a multiplicative inverse.  The
encoding states it this way because the language has no inverse symbol. -/
theorem vf_mul_inv_or_zero {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {x : M}
    (hx : iVF x) : x = iVFZero ∨ ∃ y : M, iVF y ∧ iVFMul x y = iVFOne := by
  have hmem : allSorted ![.vf]
      (pEq &0 tVFZero ⊔ exSorted .vf (pEq (tVFMul &0 &1) tVFOne)) ∈ Axioms.ACVF :=
    mem_vfField (by simp [Axioms.vfField, Axioms.ofList, Axioms.fieldAxioms])
  have h := allSorted_realize hM hmem ![x] (by intro i; fin_cases i; simpa using hx)
  simp only [BoundedFormula.realize_sup, exSorted, BoundedFormula.realize_ex,
    BoundedFormula.realize_inf, sortPred, pEq, BoundedFormula.realize_bdEqual, realize_tVFZero,
    realize_tVFMul, realize_tVFOne, realize_tv, Term.realize_var, Sum.elim_inr, Function.comp_apply, pVF_realize, Term.realize_var,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h
  exact h
/-! ### The `VF` sort as a field -/

section VFField

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- The `VF` sort of an `ACVF`-model, as a type. -/
def VFType : Type := {x : M // iVF x}

instance vfInstZero : Zero (VFType (M := M)) := ⟨⟨iVFZero, vf_zero_mem hM⟩⟩

instance vfInstOne : One (VFType (M := M)) := ⟨⟨iVFOne, vf_one_mem hM⟩⟩

instance vfInstAdd : Add (VFType (M := M)) :=
  ⟨fun x y => ⟨iVFAdd x.1 y.1, vf_add_mem hM x.2 y.2⟩⟩

instance vfInstNeg : Neg (VFType (M := M)) :=
  ⟨fun x => ⟨iVFNeg x.1, vf_neg_mem hM x.2⟩⟩

instance vfInstMul : Mul (VFType (M := M)) :=
  ⟨fun x y => ⟨iVFMul x.1 y.1, vf_mul_mem hM x.2 y.2⟩⟩

/-- The inverse on the `VF` sort: `0⁻¹ = 0`, and a nonzero element inverts by the
invertibility law. -/
noncomputable def vfInvFun (x : VFType (M := M)) : VFType (M := M) := by
  classical
  exact if h : x.1 = iVFZero then 0
    else
      let w := (vf_mul_inv_or_zero hM x.2).resolve_left h
      ⟨Classical.choose w, (Classical.choose_spec w).1⟩

noncomputable instance vfInstInv : Inv (VFType (M := M)) := ⟨vfInvFun⟩

theorem vfInv_zero : (0 : VFType (M := M))⁻¹ = 0 := dif_pos rfl

theorem vfInv_val {x : VFType (M := M)} (hx : x ≠ 0) :
    iVFMul x.1 ((x⁻¹ : VFType (M := M))).1 = iVFOne := by
  have hx' : x.1 ≠ iVFZero := fun h => hx (Subtype.ext h)
  have hval : ((x⁻¹ : VFType (M := M))).1
      = Classical.choose ((vf_mul_inv_or_zero hM x.2).resolve_left hx') := by
    show (vfInvFun x).1 = _
    unfold vfInvFun
    exact congrArg Subtype.val (dif_neg hx')
  rw [hval]
  exact (Classical.choose_spec ((vf_mul_inv_or_zero hM x.2).resolve_left hx')).2

/-- **The `VF` sort is a field.** -/
noncomputable def vfFieldOfModel : Field (VFType (M := M)) :=
  Field.ofMinimalAxioms (VFType (M := M))
    (fun a b c => Subtype.ext (vf_add_assoc hM a.2 b.2 c.2))
    (fun a => Subtype.ext (by
      show iVFAdd iVFZero a.1 = a.1
      rw [vf_add_comm hM (vf_zero_mem hM) a.2]
      exact vf_add_zero hM a.2))
    (fun a => Subtype.ext (by
      show iVFAdd (iVFNeg a.1) a.1 = iVFZero
      rw [vf_add_comm hM (vf_neg_mem hM a.2) a.2]
      exact vf_add_neg hM a.2))
    (fun a b c => Subtype.ext (vf_mul_assoc hM a.2 b.2 c.2))
    (fun a b => Subtype.ext (vf_mul_comm hM a.2 b.2))
    (fun a => Subtype.ext (by
      show iVFMul iVFOne a.1 = a.1
      rw [vf_mul_comm hM (vf_one_mem hM) a.2]
      exact vf_mul_one hM a.2))
    (fun a ha => Subtype.ext (vfInv_val ha))
    vfInv_zero
    (fun a b c => Subtype.ext (vf_left_distrib hM a.2 b.2 c.2))
    ⟨0, 1, fun h => vf_zero_ne_one hM (congrArg Subtype.val h)⟩

end VFField
/-! ### The preorder and the axioms of `rv`, semantically -/

theorem realize_tRVZero {M : Type} [LRV.Structure M] {k : ℕ} (v : Empty ⊕ Fin k → M) :
    (tRVZero (n := k)).realize v = iRVZero := by
  show FirstOrder.Language.Structure.funMap (L := LRV) Fn.rvZero
      (fun i => Term.realize (L := LRV) v ((fun j : Fin 0 => j.elim0) i)) = iRVZero
  rw [show (fun i => Term.realize (L := LRV) v ((fun j : Fin 0 => j.elim0) i))
      = (fun i => i.elim0) from by funext i; exact i.elim0]
  rfl

theorem realize_tRVMul {M : Type} [LRV.Structure M] {k : ℕ} (v : Empty ⊕ Fin k → M)
    (a b : Tm k) : (tRVMul a b).realize v = iRVMul (a.realize v) (b.realize v) := by
  show FirstOrder.Language.Structure.funMap (L := LRV) Fn.rvMul
      (fun i => Term.realize (L := LRV) v (![a, b] i)) = iRVMul (a.realize v) (b.realize v)
  rw [show (fun i => Term.realize (L := LRV) v (![a, b] i))
      = ![a.realize v, b.realize v] from by
    funext i
    fin_cases i <;> simp]
  rfl

theorem pRV_realize {M : Type} [LRV.Structure M] {k : ℕ} (t : Tm k) (v : Empty → M)
    (x : Fin k → M) : (pRV t).Realize v x ↔ t.realize (Sum.elim v x) ≠ iRVZero := by
  simp only [pRV, pEq, BoundedFormula.realize_not, BoundedFormula.realize_bdEqual,
    realize_tRVZero]

theorem pUnits_realize {M : Type} [LRV.Structure M] {k : ℕ} (t : Tm k) (v : Empty → M)
    (x : Fin k → M) : (pUnits t).Realize v x ↔ iUnits (t.realize (Sum.elim v x)) := by
  show FirstOrder.Language.Structure.RelMap (L := LRV) Rel.memUnits
      (fun i => Term.realize (L := LRV) (Sum.elim v x) (![t] i))
      ↔ iUnits (t.realize (Sum.elim v x))
  rw [show (fun i => Term.realize (L := LRV) (Sum.elim v x) (![t] i))
      = ![t.realize (Sum.elim v x)] from by
    funext i
    fin_cases i
    simp]
  rfl

theorem mem_ACVF_leRefl : Axioms.leRefl ∈ Axioms.ACVF :=
  mem_ACVF_preorderRV (by simp [Axioms.preorderRV, Axioms.ofList])

theorem mem_ACVF_leTrans : Axioms.leTrans ∈ Axioms.ACVF :=
  mem_ACVF_preorderRV (by simp [Axioms.preorderRV, Axioms.ofList])

theorem mem_ACVF_leTotal : Axioms.leTotal ∈ Axioms.ACVF :=
  mem_ACVF_preorderRV (by simp [Axioms.preorderRV, Axioms.ofList])

theorem mem_ACVF_leTop : Axioms.leTop ∈ Axioms.ACVF :=
  mem_ACVF_preorderRV (by simp [Axioms.preorderRV, Axioms.ofList])

theorem mem_ACVF_leInftyEq : Axioms.leInftyEq ∈ Axioms.ACVF :=
  mem_ACVF_preorderRV (by simp [Axioms.preorderRV, Axioms.ofList])

theorem mem_ACVF_rvEqInfty : Axioms.rvEqInfty ∈ Axioms.ACVF :=
  mem_ACVF_rvAxioms (by simp [Axioms.rvAxioms, Axioms.ofList])

theorem mem_ACVF_rvMulHom : Axioms.rvMulHom ∈ Axioms.ACVF :=
  mem_ACVF_rvAxioms (by simp [Axioms.rvAxioms, Axioms.ofList])

theorem mem_ACVF_rvUltrametric : Axioms.rvUltrametric ∈ Axioms.ACVF :=
  mem_ACVF_rvAxioms (by simp [Axioms.rvAxioms, Axioms.ofList])

theorem mem_ACVF_rvZeroEq : Axioms.rvZeroEq ∈ Axioms.ACVF :=
  mem_ACVF_rvAxioms (by simp [Axioms.rvAxioms, Axioms.ofList])

/-- Unfolding helper: the hypothesis block of `allSorted ![.rv, .rv]`. -/
theorem rv_le_of_realize {M : Type} [LRV.Structure M] {k : ℕ} {ss : Fin k → SortTag}
    {φ : Bf k} (hM : M ⊨ Axioms.ACVF) (hmem : allSorted ss φ ∈ Axioms.ACVF)
    (x : Fin k → M) (hx : ∀ i, (match ss i with
      | .vf => iVF (x i)
      | .rv => iRV (x i))) :
    @BoundedFormula.Realize LRV M _ Empty k φ (default : Empty → M) x :=
  allSorted_realize hM hmem x hx

theorem le_refl {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) (x : M) (hx : iRV x)
    (hx0 : x ≠ iRVZero) : iLe x x := by
  have h := allSorted_realize hM mem_ACVF_leRefl ![x] (by intro i; fin_cases i; simpa using hx)
  have h' : x ≠ iRVZero → iLe x x := by simpa [pRV_realize, realize_pLe] using h
  exact h' hx0

theorem le_trans {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {x y z : M}
    (hx : iRV x) (hy : iRV y) (hz : iRV z) (hx0 : x ≠ iRVZero) (hy0 : y ≠ iRVZero)
    (hz0 : z ≠ iRVZero) (h1 : iLe x y) (h2 : iLe y z) : iLe x z := by
  have h := allSorted_realize hM mem_ACVF_leTrans ![x, y, z] (by
    intro i; fin_cases i <;> simp [hx, hy, hz])
  have h' : x ≠ iRVZero → y ≠ iRVZero → z ≠ iRVZero → iLe x y → iLe y z → iLe x z := by
    simpa [pRV_realize, realize_pLe] using h
  exact h' hx0 hy0 hz0 h1 h2

theorem le_total {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) (x y : M)
    (hx : iRV x) (hy : iRV y) (hx0 : x ≠ iRVZero) (hy0 : y ≠ iRVZero) :
    iLe x y ∨ iLe y x := by
  have h := allSorted_realize hM mem_ACVF_leTotal ![x, y] (by
    intro i; fin_cases i <;> simp [hx, hy])
  have h' : x ≠ iRVZero → y ≠ iRVZero → iLe x y ∨ iLe y x := by
    simpa [pRV_realize, realize_pLe] using h
  exact h' hx0 hy0

theorem le_top {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) (x : M) (hx : iRV x)
    (hx0 : x ≠ iRVZero) : iLe x iRVZero := by
  have h := allSorted_realize hM mem_ACVF_leTop ![x] (by intro i; fin_cases i; simpa using hx)
  have h' : x ≠ iRVZero → iLe x iRVZero := by
    simpa [pRV_realize, realize_pLe, tRVInfty, realize_tRVZero] using h
  exact h' hx0

theorem le_infty_eq {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) (x : M) (hx : iRV x)
    (hx0 : x ≠ iRVZero) (h : iLe iRVZero x) : x = iRVZero := by
  have h0 := allSorted_realize hM mem_ACVF_leInftyEq ![x] (by intro i; fin_cases i; simpa using hx)
  have h' : x ≠ iRVZero → iLe iRVZero x → x = iRVZero := by
    simpa [pRV_realize, realize_pLe, pEq, tRVInfty, realize_tRVZero] using h0
  exact absurd (h' hx0 h) hx0

theorem rv_zero_eq {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) :
    iRv (iVFZero (M := M)) = iRVZero := by
  have h := sentence_realize hM mem_ACVF_rvZeroEq
  rw [Sentence.Realize] at h
  simpa only [Axioms.rvZeroEq, Formula.Realize, pEq, BoundedFormula.realize_bdEqual,
    realize_tRv, realize_tVFZero, tRVInfty, realize_tRVZero] using h

theorem rv_eq_infty {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {x : M} (hx : iVF x)
    (h : iRv x = iRVZero) : x = iVFZero := by
  have h0 := allSorted_realize hM mem_ACVF_rvEqInfty ![x] (by intro i; fin_cases i; simpa using hx)
  have h' : iRv x = iRVZero → x = iVFZero := by
    simpa [pEq, realize_tRv, realize_tVFZero, tRVInfty, realize_tRVZero] using h0
  exact h' h

theorem rv_mul_hom {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {x y : M}
    (hx : iVF x) (hy : iVF y) :
    iRv (iVFMul x y) = iRVMul (iRv x) (iRv y) := by
  have h := allSorted_realize hM mem_ACVF_rvMulHom ![x, y] (by
    intro i; fin_cases i <;> simp [hx, hy])
  simpa only [pEq, BoundedFormula.realize_bdEqual, realize_tRv, realize_tVFMul, realize_tRVMul,
    realize_tv, Term.realize_var, Sum.elim_inr, Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_one] using h

theorem rv_ultrametric {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {x y : M}
    (hx : iVF x) (hy : iVF y) :
    iLe (iRv x) (iRv (iVFAdd x y)) ∨ iLe (iRv y) (iRv (iVFAdd x y)) := by
  have h := allSorted_realize hM mem_ACVF_rvUltrametric ![x, y] (by
    intro i; fin_cases i <;> simp [hx, hy])
  simpa only [BoundedFormula.realize_sup, realize_pLe, realize_tRv, realize_tVFAdd, realize_tv, Term.realize_var, Sum.elim_inr, Function.comp_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one] using h

/-- `rv` of a `VF`-element is an `RV`-element. -/
theorem rv_mem {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {x : M} (hx : iVF x) :
    iRV (iRv x) := by
  have hmem : allSorted ![.vf] (pRVsort (tRv &0)) ∈ Axioms.ACVF :=
    mem_ACVF_sortClosure (by simp [Axioms.sortClosure, Axioms.ofList, Axioms.sdRv])
  have h := allSorted_realize hM hmem ![x] (by intro i; fin_cases i; simpa using hx)
  simpa only [pRVsort_realize, realize_tRv, realize_tv, Term.realize_var, Sum.elim_inr,
    Function.comp_apply, Matrix.cons_val_zero] using h

/-! ### The seven axioms for the extracted predicate -/

section Extract

variable {M : Type} [LRV.Structure M]

/-- The predicate of the `L_val`-structure on the `VF` sort: `v x ≤ v y`, i.e. `rv y ≤ rv x` in
the paper's `RV`-order (the two orders are reversed). -/
def predV (x y : VFType (M := M)) : Prop := iLe (iRv y.1) (iRv x.1)

/-- Reflexivity, unguarded: at `x = 0` it is the ultrametric inequality at `0 + 0`. -/
theorem le_self (hM : M ⊨ Axioms.ACVF) {a : M} (ha : iRV a) : iLe a a := by
  by_cases h : a = iRVZero
  · subst h
    have h1 := rv_ultrametric hM (vf_zero_mem hM) (vf_zero_mem hM)
    simpa [rv_zero_eq hM, vf_add_zero hM (vf_zero_mem hM)] using h1
  · exact le_refl hM a ha h

/-- Everything is below `∞ = rv 0`, unguarded. -/
theorem le_top' (hM : M ⊨ Axioms.ACVF) {a : M} (ha : iRV a) : iLe a iRVZero := by
  by_cases h : a = iRVZero
  · subst h; exact le_self hM ha
  · exact le_top hM a ha h

theorem predV_refl (hM : M ⊨ Axioms.ACVF) (x : VFType (M := M)) : predV x x :=
  le_self hM (rv_mem hM x.2)

theorem predV_trans (hM : M ⊨ Axioms.ACVF) {x y z : VFType (M := M)}
    (h1 : predV x y) (h2 : predV y z) : predV x z := by
  have h1' : iLe (iRv y.1) (iRv x.1) := h1
  have h2' : iLe (iRv z.1) (iRv y.1) := h2
  show iLe (iRv z.1) (iRv x.1)
  by_cases hx : iRv x.1 = iRVZero
  · rw [hx]; exact le_top' hM (rv_mem hM z.2)
  by_cases hz : iRv z.1 = iRVZero
  · have hy : iRv y.1 = iRVZero := by
      by_cases h : iRv y.1 = iRVZero
      · exact h
      · exact absurd (le_infty_eq hM _ (rv_mem hM y.2) h (by simpa [hz] using h2')) h
    simpa [hz, hy] using h1'
  · have hy : iRv y.1 ≠ iRVZero := by
      intro h
      exact hx (le_infty_eq hM _ (rv_mem hM x.2) hx (by simpa [h] using h1'))
    exact le_trans hM (rv_mem hM z.2) (rv_mem hM y.2) (rv_mem hM x.2) hz hy hx h2' h1'

theorem predV_zero_le (hM : M ⊨ Axioms.ACVF) (x : VFType (M := M)) :
    predV (0 : VFType (M := M)) x := by
  show iLe (iRv x.1) (iRv iVFZero)
  rw [rv_zero_eq hM]
  exact le_top' hM (rv_mem hM x.2)

theorem predV_zero_eq (hM : M ⊨ Axioms.ACVF) {x : VFType (M := M)}
    (h : predV x (0 : VFType (M := M))) : x = 0 := by
  have h' : iLe (iRv iVFZero) (iRv x.1) := h
  rw [rv_zero_eq hM] at h'
  by_cases hx : iRv x.1 = iRVZero
  · exact Subtype.ext (rv_eq_infty hM x.2 hx)
  · exact absurd (le_infty_eq hM _ (rv_mem hM x.2) hx h') hx

theorem predV_ultra (hM : M ⊨ Axioms.ACVF) (x y : VFType (M := M)) :
    predV (x + y) x ∨ predV (x + y) y := by
  have h := rv_ultrametric hM x.2 y.2
  show iLe (iRv x.1) (iRv (iVFAdd x.1 y.1)) ∨ iLe (iRv y.1) (iRv (iVFAdd x.1 y.1))
  exact h

theorem predV_total (hM : M ⊨ Axioms.ACVF) (x y : VFType (M := M)) :
    predV x y ∨ predV y x := by
  by_cases hx : iRv x.1 = iRVZero
  · left; show iLe (iRv y.1) (iRv x.1); rw [hx]; exact le_top' hM (rv_mem hM y.2)
  by_cases hy : iRv y.1 = iRVZero
  · right; show iLe (iRv x.1) (iRv y.1); rw [hy]; exact le_top' hM (rv_mem hM x.2)
  · exact Or.symm (le_total (M := M) hM (iRv x.1) (iRv y.1)
      (rv_mem hM x.2) (rv_mem hM y.2) hx hy)

end Extract

/-! ### The unfolding lemmas about the `VF → RV` boundary that the transfer of `axScale` needs -/

variable {M : Type} [LRV.Structure M]

/-- The sort-closure axiom `sdRv` (`rv` maps the `VF` sort into the `RV` sort) is an axiom of
`ACVF`. -/
theorem mem_ACVF_sdRv : Axioms.sdRv ∈ Axioms.ACVF :=
  mem_ACVF_sortClosure (by simp [Axioms.sortClosure, Axioms.ofList])

/-- A nonzero `VF`-element has `rv ≠ ∞`: this is `rv_eq_infty` contrapositively, and it is the
guard that turns `z ≠ 0` in the `L_val`-structure into `rv z ≠ rv 0` in the `L_RV`-structure. -/
theorem rv_ne_zero {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {x : M} (hx : iVF x)
    (h : x ≠ iVFZero) : iRv x ≠ iRVZero :=
  fun hh => h (rv_eq_infty hM hx hh)

/-- **`rv` is surjective** onto the nonzero part of `RV` (the frozen axiom `Axioms.rvSurj`). -/
theorem mem_ACVF_rvSurj : Axioms.rvSurj ∈ Axioms.ACVF :=
  mem_ACVF_rvAxioms (by simp [Axioms.rvAxioms, Axioms.ofList])

theorem rv_surj {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {a : M} (ha : iRV a)
    (ha0 : a ≠ iRVZero) : ∃ x : M, iVF x ∧ iRv x = a := by
  have h := allSorted_realize hM (T := Axioms.ACVF) mem_ACVF_rvSurj ![a] (by
    intro i
    fin_cases i
    simpa using ha)
  simp only [Axioms.rvSurj, BoundedFormula.realize_imp, BoundedFormula.realize_not, pEq,
    BoundedFormula.realize_bdEqual, realize_tRVZero, exSorted, BoundedFormula.realize_ex,
    BoundedFormula.realize_inf, sortPred, pVF_realize, realize_tRv, realize_tv,
    Term.realize_var, Sum.elim_inr, Function.comp_apply, Fin.snoc_last, Fin.snoc_castSucc,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h
  exact h ha0

/-- Any `RV`-element is the `rv` of a `VF`-element (`rv 0` covers the case `rv 0`). -/
theorem exists_vf_of_rv {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {a : M}
    (ha : iRV a) : ∃ x : M, iVF x ∧ iRv x = a := by
  by_cases ha0 : a = iRVZero
  · exact ⟨iVFZero, vf_zero_mem hM, by rw [rv_zero_eq hM, ha0]⟩
  · exact rv_surj hM ha ha0

/-! ### The paper's scaling law, as a hypothesis -/

/-- **The missing half of Definition 2.2 item 5**, stated over `L_RV`: `≤` on `RV` is invariant
under multiplication by any element of `RV` other than `rv 0`, in the strong (iff) form that
`L_val`'s `axScale` has.  The frozen encoding only provides the case `iUnits c`. -/
def PaperScale (M : Type) [LRV.Structure M] : Prop :=
  ∀ a b c : M, iRV a → iRV b → iRV c → c ≠ iRVZero →
    (iLe a b ↔ iLe (iRVMul a c) (iRVMul b c))

/-! ### The extracted predicate on the `VF` sort -/

section Extract

variable [hM : M ⊨ Axioms.ACVF]

/-- The `L_val`-predicate extracted from an `L_RV`-model.  The two orders are **reversed**:
`L_val`'s `v 0` is minimal, the paper's `rv 0 = ∞` is on top. -/
def vfPred (x y : VFType (M := M)) : Prop := iLe (iRv y.1) (iRv x.1)

theorem vfPred_def (x y : VFType (M := M)) : vfPred x y = iLe (iRv y.1) (iRv x.1) := rfl

@[simp] theorem vfPred_apply (x y : VFType (M := M)) : vfPred x y ↔ iLe (iRv y.1) (iRv x.1) :=
  Iff.rfl

/-- The underlying carrier computation for the subtype multiplication: it is `iVFMul`. -/
theorem vfType_mul_val (x y : VFType (M := M)) : (x * y).1 = iVFMul x.1 y.1 := rfl

theorem vfType_zero_val : (0 : VFType (M := M)).1 = iVFZero := rfl

/-- `rv` is multiplicative on the `VF` sort, read through the subtype multiplication. -/
theorem rv_mul_val (x y : VFType (M := M)) :
    iRv ((x * y).1) = iRVMul (iRv x.1) (iRv y.1) :=
  rv_mul_hom hM x.2 y.2

/-- `z ≠ 0` in the subtype field is `iRv z ≠ iRVZero` in `RV`. -/
theorem rv_ne_zero_of_vfPred_ne_zero {z : VFType (M := M)} (hz : z ≠ 0) :
    iRv z.1 ≠ iRVZero :=
  rv_ne_zero hM z.2 (fun h => hz (Subtype.ext h))

/-- The core of the transfer of `axScale`, written on the underlying carrier. -/
theorem vfPred_scale_raw (hscale : PaperScale M) (x y z : VFType (M := M)) (hz : z ≠ 0) :
    iLe (iRv y.1) (iRv x.1) ↔ iLe (iRv (iVFMul y.1 z.1)) (iRv (iVFMul x.1 z.1)) := by
  rw [rv_mul_hom hM y.2 z.2, rv_mul_hom hM x.2 z.2]
  exact hscale (iRv y.1) (iRv x.1) (iRv z.1) (rv_mem hM y.2) (rv_mem hM x.2) (rv_mem hM z.2)
    (rv_ne_zero_of_vfPred_ne_zero hz)

/-- **The repair is sufficient.**  Assume the paper's scaling law as an extra hypothesis on the
`L_RV`-model.  Then the extracted predicate `vfPred` on the `VF` sort satisfies the semantic form
of `ValPM.axScale`:

`z ≠ 0 → (vfPred x y ↔ vfPred (x * z) (y * z))`,

where multiplication and `0` are those of the subtype field `vfFieldOfModel`
(`iVFMul` / `iVFZero` on the carrier).  Note the reversal: the hypothesis is applied at
`a = rv y`, `b = rv x`, `c = rv z`. -/
theorem vfPred_scale (hscale : PaperScale M) (x y z : VFType (M := M)) (hz : z ≠ 0) :
    vfPred x y ↔ vfPred (x * z) (y * z) :=
  vfPred_scale_raw hscale x y z hz

/-- The same statement in the `∀`-form of `ValPM.IsValPred.scale` and of the right-hand side of
`ValPM.axScale_realize`. -/
theorem vfPred_scale_forall (hscale : PaperScale M) :
    ∀ x y z : VFType (M := M), z ≠ 0 → (vfPred x y ↔ vfPred (x * z) (y * z)) :=
  fun x y z hz => vfPred_scale hscale x y z hz

/-- The forward (one-sided) direction, which is all that a proof of the forward direction of
`axScale` needs. -/
theorem vfPred_scale_mp (hscale : PaperScale M) {x y z : VFType (M := M)} (hz : z ≠ 0)
    (h : vfPred x y) : vfPred (x * z) (y * z) :=
  (vfPred_scale hscale x y z hz).1 h

/-- And the reverse direction (cancellation). -/
theorem vfPred_scale_mpr (hscale : PaperScale M) {x y z : VFType (M := M)} (hz : z ≠ 0)
    (h : vfPred (x * z) (y * z)) : vfPred x y :=
  (vfPred_scale hscale x y z hz).2 h

/-! ### Necessity: the hypothesis is exactly the transported `axScale`

The other direction costs nothing mathematically but pins the repair down: the extracted
`axScale` (an `L_val`-statement about `VF`) and the paper's law (`L_RV`, about all of `RV`) are
*equivalent*, using `rvSurj` and the multiplicativity of `rv`.  So adding `PaperScale` to the
encoding is exactly what `L_val`'s `axScale` transports to, no more. -/

/-- **Necessity.**  If the extracted predicate satisfies `axScale`, then `≤` on `RV` is invariant
under multiplication by every nonzero element of `RV`. -/
theorem paperScale_of_vfPred_scale
    (h : ∀ x y z : VFType (M := M), z ≠ 0 → (vfPred x y ↔ vfPred (x * z) (y * z))) :
    PaperScale M := by
  intro a b c ha hb hc hc0
  obtain ⟨x, hx, rfl⟩ := exists_vf_of_rv hM ha
  obtain ⟨y, hy, rfl⟩ := exists_vf_of_rv hM hb
  obtain ⟨z, hz, rfl⟩ := exists_vf_of_rv hM hc
  have hz0 : z ≠ iVFZero := by
    intro hz'
    exact hc0 (by rw [hz', rv_zero_eq hM])
  have hz0' : (⟨z, hz⟩ : VFType (M := M)) ≠ (0 : VFType (M := M)) :=
    fun h' => hz0 (congrArg Subtype.val h')
  have key := h ⟨y, hy⟩ ⟨x, hx⟩ ⟨z, hz⟩ hz0'
  rw [← rv_mul_hom hM hx hz, ← rv_mul_hom hM hy hz]
  exact key

/-- **The two are equivalent**: the paper's scaling law on `RV` is exactly the `axScale`-condition
of the extracted `L_val`-structure. -/
theorem paperScale_iff_vfPred_scale :
    PaperScale M ↔ ∀ x y z : VFType (M := M), z ≠ 0 →
      (vfPred x y ↔ vfPred (x * z) (y * z)) :=
  ⟨fun h => vfPred_scale_forall h, fun h => paperScale_of_vfPred_scale h⟩

/-! ### Assembly: `IsValPred vfPred` ⟹ the extracted structure models `valField`

`ValPM.valField_model` turns a predicate satisfying `ValPM.IsValPred` into a model of `valField`
on `ValPM.valStructOf K p`, with no `CompatibleRing` or `IsExpansionOn` obligations: the structure
is *defined* from the field operations.  So once the six non-scaling axioms hold for `vfPred`
(the `d4` direction) they combine with `vfPred_scale` into `S ⊨ ValPM.valField` by this one
application.  The statements below take the six as explicit hypotheses, so they are independent of
the file the six are proved in; `hrefl`–`htotal` are exactly the fields of `ValPM.IsValPred`. -/

/-- **Assembly of `valField` on the `VF` sort** from the six non-scaling axioms and the paper's
scaling law: the structure `ValPM.valStructOf (VFType) vfPred` (the ring symbols being those of
`vfFieldOfModel`) is a model of `ValPM.valField`. -/
theorem valField_model_of_PaperScale
    (hrefl : ∀ x : VFType (M := M), vfPred x x)
    (htrans : ∀ x y z : VFType (M := M), vfPred x y → vfPred y z → vfPred x z)
    (hzero_le : ∀ x : VFType (M := M), vfPred (0 : VFType (M := M)) x)
    (hzero_eq : ∀ x : VFType (M := M), vfPred x (0 : VFType (M := M)) → x = 0)
    (hultra : ∀ x y : VFType (M := M), vfPred (x + y) x ∨ vfPred (x + y) y)
    (htotal : ∀ x y : VFType (M := M), vfPred x y ∨ vfPred y x)
    (hscale : PaperScale M) :
    @Theory.Model Language.val (VFType (M := M))
      (@ValPM.valStructOf (VFType (M := M)) (vfFieldOfModel (M := M)) vfPred) ValPM.valField := by
  letI : Field (VFType (M := M)) := vfFieldOfModel
  exact ValPM.valField_model ⟨hrefl, htrans, hzero_le, hzero_eq, hultra, htotal,
    vfPred_scale_forall hscale⟩

/-- The same with the scaling law in its semantic (`IsValPred.scale`-shaped) form, so that it can
be fed directly with a lemma proved from a different hypothesis. -/
theorem valField_model_of_scale
    (hrefl : ∀ x : VFType (M := M), vfPred x x)
    (htrans : ∀ x y z : VFType (M := M), vfPred x y → vfPred y z → vfPred x z)
    (hzero_le : ∀ x : VFType (M := M), vfPred (0 : VFType (M := M)) x)
    (hzero_eq : ∀ x : VFType (M := M), vfPred x (0 : VFType (M := M)) → x = 0)
    (hultra : ∀ x y : VFType (M := M), vfPred (x + y) x ∨ vfPred (x + y) y)
    (htotal : ∀ x y : VFType (M := M), vfPred x y ∨ vfPred y x)
    (hscale : ∀ x y z : VFType (M := M), z ≠ 0 → (vfPred x y ↔ vfPred (x * z) (y * z))) :
    @Theory.Model Language.val (VFType (M := M))
      (@ValPM.valStructOf (VFType (M := M)) (vfFieldOfModel (M := M)) vfPred) ValPM.valField :=
  valField_model_of_PaperScale hrefl htrans hzero_le hzero_eq hultra htotal
    (paperScale_of_vfPred_scale hscale)


/-! ### The `L_val`-structure of the extraction, and its ring reduct

The extracted predicate is put on `ValPM.valStructOf`, whose ring symbols are *defined* to be the
field operations of `vfFieldOfModel`; so `S` is a `Language.ring`-structure too, and
`Ring.CompatibleRing` / `valRingHom.IsExpansionOn` hold for it by `rfl`.  These instances are what
`Field.realize_genericMonicPolyHasRoot` needs.  (`ValPM.valField_model`, used above, does not need
them: it works with any `Field` and `IsValPred`.) -/

/-- The `L_val`-structure extracted from an `L_RV`-model: `ValPM.valStructOf` at the reversed
predicate `vfPred`, with the ring symbols of `vfFieldOfModel`. -/
@[instance_reducible]
noncomputable def vfValStruct : Language.val.Structure (VFType (M := M)) :=
  @ValPM.valStructOf (VFType (M := M)) (vfFieldOfModel (M := M)) vfPred

/-- Its `L_ring`-reduct (the underlying `Language.ring`-structure). -/
@[instance_reducible]
noncomputable def vfRingStruct : Language.ring.Structure (VFType (M := M)) :=
  @ValPM.ringStructOfVal (VFType (M := M)) vfValStruct

/-- **`S` is a `CompatibleRing`**: the ring symbols of the extracted `L_val`-structure are the
field operations.  Each field is `rfl`. -/
@[instance_reducible]
noncomputable def vfCompatibleRing :
    @Ring.CompatibleRing (VFType (M := M)) _ _ _ _ _ where
  toStructure := vfRingStruct
  funMap_add := fun _ => rfl
  funMap_mul := fun _ => rfl
  funMap_neg := fun _ => rfl
  funMap_zero := fun _ => rfl
  funMap_one := fun _ => rfl

/-- `vfValStruct` expands `vfRingStruct`. -/
theorem vfValStruct_expansion : @LHom.IsExpansionOn Language.ring Language.val valRingHom
    (VFType (M := M)) (@Ring.CompatibleRing.toStructure (VFType (M := M)) _ _ _ _ _
      vfCompatibleRing) vfValStruct := by
  letI : Language.val.Structure (VFType (M := M)) := vfValStruct
  letI : Language.ring.Structure (VFType (M := M)) := vfRingStruct
  exact ValPM.ringStructOfVal.expansion (VFType (M := M))

/-! ### The algebraic-closedness part of `S ⊨ ValPM.ACVF_val` -/

/-- **`ValPM.genericMonicPolyHasRoot n` holds in `S` if `S` is algebraically closed.**  This is the
bridge from `IsAlgClosed` (what `Axioms.vfAlgClosed` gives) to the sentence scheme of
`ValPM.ACVF_val`: transport the sentence along `valRingHom`, then use
`Field.realize_genericMonicPolyHasRoot` and `IsAlgClosed.exists_root`. -/
theorem realize_genericMonicPolyHasRoot_of_isAlgClosed
    (hacf : @IsAlgClosed (VFType (M := M)) (vfFieldOfModel (M := M))) {n : ℕ} (hn : 0 < n) :
    @Sentence.Realize Language.val (VFType (M := M)) vfValStruct (ValPM.genericMonicPolyHasRoot n) := by
  letI : Field (VFType (M := M)) := vfFieldOfModel
  rw [ValPM.genericMonicPolyHasRoot]
  refine (@LHom.realize_onSentence Language.ring Language.val (VFType (M := M))
    vfRingStruct vfValStruct valRingHom vfValStruct_expansion
    (Field.genericMonicPolyHasRoot n)).mpr ?_
  have key := @Field.realize_genericMonicPolyHasRoot (VFType (M := M)) (vfFieldOfModel (M := M))
    (vfCompatibleRing) n
  refine key.mpr ?_
  rintro ⟨p, -, hdeg⟩
  exact @IsAlgClosed.exists_root (VFType (M := M)) (vfFieldOfModel (M := M)) hacf p
    (ne_of_gt (Polynomial.natDegree_pos_iff_degree_pos.1 (by rw [hdeg]; exact hn)))


/-! ### Nontriviality, and the whole of `S ⊨ ValPM.ACVF_val` -/

/-- **Nontriviality of the valuation**, in the form the encoding can supply: a nonzero
`VF`-element outside the valuation ring, `∃ x ≠ 0, ¬ (v 1 ≤ v x)` — exactly the content of
`ValPM.axNontrivial`.

This is *not* a consequence of the frozen `Axioms.ACVF`, which contains no nontriviality
sentence.  The trivially valued structure on an algebraically closed field `F` (`VF = F`,
`RV = F^× ∪ {∞}`, `rv` the identity on `F^×` and `rv 0 = ∞`, `iUnits` all of `RV^×`, `≤` the
two-class preorder with `∞` on top, the residue-field operations transported along `rv`) satisfies
every axiom of `ACVF` — `vfField`/`vfAlgClosed` are those of the ACF `F`, `kField`/`kAlgClosed`
those of the residue field `F`, `rvGroup` holds because `F` algebraically closed makes `F^×`
divisible, `preorderRV` because `iUnits` is exactly the class of `1`, and `rvUltrametric` because
all nonzero values are equivalent — while failing `HasNontrivVal`: there every nonzero `x` has
`rv x` in the class of `1`, so `v x ≤ v 1`. -/
def HasNontrivVal (M : Type) [LRV.Structure M] : Prop :=
  ∃ x : M, iVF x ∧ x ≠ iVFZero ∧ ¬ iLe (iRv x) (iRv (iVFOne (M := M)))

/-- **`ValPM.axNontrivial` holds in `S`** as soon as the valuation is nontrivial. -/
theorem realize_axNontrivial (hnontriv : HasNontrivVal M) :
    @Sentence.Realize Language.val (VFType (M := M)) vfValStruct ValPM.axNontrivial := by
  obtain ⟨x, hx, hx0, hlt⟩ := hnontriv
  simp only [ValPM.axNontrivial, ValPM.axNontrivialF, Sentence.Realize, Formula.Realize,
    BoundedFormula.realize_ex, BoundedFormula.realize_imp, BoundedFormula.realize_not,
    BoundedFormula.realize_all, BoundedFormula.realize_inf, BoundedFormula.realize_bdEqual]
  refine ⟨⟨x, hx⟩, ?_, ?_⟩
  · intro h
    exact hx0 (congrArg Subtype.val h)
  · exact hlt

/-- **The ACF and nontriviality parts of `S ⊨ ValPM.ACVF_val`.** -/
theorem model_ACF_part (hacf : @IsAlgClosed (VFType (M := M)) (vfFieldOfModel (M := M)))
    (hnontriv : HasNontrivVal M) :
    ∀ φ ∈ ValPM.genericMonicPolyHasRoot '' {n : ℕ | 0 < n} ∪ {ValPM.axNontrivial},
      @Sentence.Realize Language.val (VFType (M := M)) vfValStruct φ := by
  rintro φ (⟨ψ, hψ, rfl⟩ | rfl)
  · exact realize_genericMonicPolyHasRoot_of_isAlgClosed hacf hψ
  · exact realize_axNontrivial hnontriv

/-- **`S ⊨ ValPM.ACVF_val`.**  The extraction from an `L_RV`-model of the frozen `ACVF` is a model
of the `L_val`-theory of nontrivially valued algebraically closed fields, from four inputs:

* the six non-scaling `valField` axioms for `vfPred` (the `d4` direction);
* `PaperScale` (the paper's Definition 2.2 item 5, the missing half of `leMulCompat`) — the `d3`
  repair;
* `IsAlgClosed` of the `VF` sort, which `Axioms.vfAlgClosed` supplies (the `d5` direction);
* `HasNontrivVal`, nontriviality of the valuation, which the frozen axioms do **not** supply. -/
theorem model_ACVF_val_of_axioms
    (hrefl : ∀ x : VFType (M := M), vfPred x x)
    (htrans : ∀ x y z : VFType (M := M), vfPred x y → vfPred y z → vfPred x z)
    (hzero_le : ∀ x : VFType (M := M), vfPred (0 : VFType (M := M)) x)
    (hzero_eq : ∀ x : VFType (M := M), vfPred x (0 : VFType (M := M)) → x = 0)
    (hultra : ∀ x y : VFType (M := M), vfPred (x + y) x ∨ vfPred (x + y) y)
    (htotal : ∀ x y : VFType (M := M), vfPred x y ∨ vfPred y x)
    (hscale : PaperScale M)
    (hacf : @IsAlgClosed (VFType (M := M)) (vfFieldOfModel (M := M)))
    (hnontriv : HasNontrivVal M) :
    @Theory.Model Language.val (VFType (M := M)) vfValStruct ValPM.ACVF_val := by
  letI : Language.val.Structure (VFType (M := M)) := vfValStruct
  refine ⟨fun φ hφ => ?_⟩
  simp only [ValPM.ACVF_val, Set.mem_union, Set.mem_image, Set.mem_singleton_iff] at hφ
  rcases hφ with (hφ | hφ) | rfl
  · exact (valField_model_of_PaperScale hrefl htrans hzero_le hzero_eq hultra htotal
      hscale).realize_of_mem φ hφ
  · exact model_ACF_part hacf hnontriv φ (Or.inl hφ)
  · exact realize_axNontrivial hnontriv

end Extract

end SpecialTransformations.Milestone0.Transfer

/-
  d5 — `IsAlgClosed` of the `VF` sort of a model of the frozen theory `Axioms.ACVF`.

  Main result: `isAlgClosed_vfType : IsAlgClosed (VFType (M := M))` for every
  `hM : M ⊨ Axioms.ACVF`, where `VFType = {x : M // iVF x}` carries the field structure
  `vfFieldOfModel`.

  The mathematical content is the frozen scheme `Axioms.vfAlgClosed`
  (`∀ a₀ … a_{k-1} ∃ x ∈ VF, x^k + a_{k-1}x^{k-1} + … + a₀ = 0`), read through the
  syntax `hornerPoly tVFAdd tVFMul`; the work is to identify the *evaluated Horner fold*
  with `Polynomial.eval` of the monic polynomial of the coefficient tuple.
-/

set_option maxHeartbeats 1000000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer

namespace VFAlgClosed

/-! ## 1. The Horner fold and `Polynomial.eval`

`hornerPoly (k := m+1) add mul` is `((x + a_m) * x + a_{m-1}) * x + ⋯ + a_0`, folded over the
list `(List.finRange m).reverse`.  We compute the value of such a fold. -/

/-- `(List.finRange (m+1)).reverse = m :: (m-1) :: ⋯ :: 0`, expressed as the list
`[m-1, …, 0]` pushed forward by `Fin.succ` and with `0` appended. -/
theorem finRange_reverse_succ (m : ℕ) :
    (List.finRange (m + 1)).reverse = (List.finRange m).reverse.map Fin.succ ++ [⟨0, by omega⟩] := by
  rw [List.finRange_succ, List.reverse_cons, List.map_reverse]
  simp

/-- **The value of a Horner fold.**  For an arbitrary initial accumulator `c`,

`((c * r + A_{m-1}) * r + ⋯ + A_0) = c * r^m + ∑_{j<m} A_j r^j`.

The induction has to be stated for a general coefficient family `A : ℕ → R` so that the shift
`A ↦ (fun i => A (i+1))` in the induction step is available. -/
theorem foldl_finRange_reverse {R : Type*} [CommRing R] (A : ℕ → R) (r c : R) (m : ℕ) :
    (List.finRange m).reverse.foldl (fun acc (j : Fin m) => acc * r + A (j : ℕ)) c
      = c * r ^ m + ∑ j : Fin m, A (j : ℕ) * r ^ (j : ℕ) := by
  induction m generalizing c A with
  | zero => simp
  | succ m ih =>
    rw [finRange_reverse_succ, List.foldl_append, List.foldl_map]
    have h1 : List.foldl (fun x y => x * r + A (↑(Fin.succ y))) c (List.finRange m).reverse
        = c * r ^ m + ∑ j : Fin m, A ((j : ℕ) + 1) * r ^ (j : ℕ) :=
      ih (fun i => A (i + 1)) c
    rw [h1, List.foldl_cons, List.foldl_nil]
    have hS : (∑ j : Fin m, A ((j : ℕ) + 1) * r ^ (j : ℕ)) * r
        = ∑ j : Fin m, A ((j : ℕ) + 1) * r ^ ((j : ℕ) + 1) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun j _ => by rw [mul_assoc, ← pow_succ])
    have hshift : (∑ j : Fin m, A ((j : ℕ) + 1) * r ^ ((j : ℕ) + 1)) + A 0
        = ∑ j : Fin m, A (j : ℕ) * r ^ (j : ℕ) + A m * r ^ m := by
      rw [Fin.sum_univ_eq_sum_range (fun i => A (i + 1) * r ^ (i + 1)) m,
        Fin.sum_univ_eq_sum_range (fun i => A i * r ^ i) m,
        show A 0 = A 0 * r ^ 0 from by rw [pow_zero, mul_one],
        ← Finset.sum_range_succ' (fun i => A i * r ^ i) m,
        Finset.sum_range_succ (fun i => A i * r ^ i) m]
    rw [add_mul, mul_assoc, ← pow_succ, hS,
      Fin.sum_univ_castSucc (fun j : Fin (m + 1) => A (j : ℕ) * r ^ (j : ℕ))]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [add_assoc, hshift]

/-- **The Horner value of the monic polynomial with coefficient tuple `A`**:
`x^{m+1} + A_m x^m + ⋯ + A_0`. -/
theorem horner_fold_eq {R : Type*} [CommRing R] (A : ℕ → R) (r : R) (m : ℕ) :
    (List.finRange m).reverse.foldl (fun acc (j : Fin m) => acc * r + A (j : ℕ)) (r + A m)
      = r ^ (m + 1) + ∑ j : Fin (m + 1), A (j : ℕ) * r ^ (j : ℕ) := by
  rw [foldl_finRange_reverse]
  rw [Fin.sum_univ_castSucc (fun j : Fin (m + 1) => A (j : ℕ) * r ^ (j : ℕ))]
  simp only [Fin.val_castSucc, Fin.val_last]
  rw [add_mul, mul_comm r (r ^ m), ← pow_succ]
  ring

/-- **`Polynomial.eval` of a monic polynomial in terms of its coefficients.** -/
theorem eval_monic_eq {R : Type*} [CommRing R] {p : Polynomial R} {m : ℕ} (hp : p.Monic)
    (hd : p.natDegree = m + 1) (r : R) :
    p.eval r = r ^ (m + 1) + ∑ j : Fin (m + 1), p.coeff (j : ℕ) * r ^ (j : ℕ) := by
  have hsum : p.eval r = ∑ i ∈ Finset.range (m + 2), p.coeff i * r ^ i := by
    conv_lhs => rw [Polynomial.as_sum_range_C_mul_X_pow p]
    rw [Polynomial.eval_finsetSum]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    rw [hd]
  rw [hsum, Finset.sum_range_succ,
    Fin.sum_univ_eq_sum_range (fun i => p.coeff i * r ^ i) (m + 1)]
  have hc : p.coeff (m + 1) = 1 := by rw [← hd]; exact hp.coeff_natDegree
  rw [hc, one_mul, add_comm]

end VFAlgClosed

namespace VFAlgClosed

/-! ## 2. The frozen Horner syntax, evaluated

`acfScheme .vf tVFZero tVFAdd tVFMul k` is
`∀ a₀ … a_{k-1} ∈ VF, ∃ x ∈ VF, (hornerPoly tVFAdd tVFMul) = 0`.  We read it semantically. -/

section HornerRealize

variable {M : Type} [LRV.Structure M]

/-- `Fin.snoc` evaluated at a coefficient position. -/
theorem snoc_castSucc_castSucc {k : ℕ} (a : Fin (k + 1) → M) (x : M) (i : Fin k) :
    (Fin.snoc a x : Fin (k + 1 + 1) → M) ⟨i.val, by omega⟩ = a i.castSucc :=
  Fin.snoc_castSucc (α := fun _ : Fin (k + 1 + 1) => M) (x := x) (p := a) (i := i.castSucc)

/-- `Fin.snoc` evaluated at the last coefficient position. -/
theorem snoc_last_coeff {k : ℕ} (a : Fin (k + 1) → M) (x : M) :
    (Fin.snoc a x : Fin (k + 1 + 1) → M) ⟨k, by omega⟩ = a (Fin.last k) :=
  Fin.snoc_castSucc (α := fun _ : Fin (k + 1 + 1) => M) (x := x) (p := a) (i := Fin.last k)

/-- `Fin.snoc` evaluated at the root position. -/
theorem snoc_root {k : ℕ} (a : Fin (k + 1) → M) (x : M) :
    (Fin.snoc a x : Fin (k + 1 + 1) → M) ⟨k + 1, by omega⟩ = x :=
  Fin.snoc_last (α := fun _ : Fin (k + 1 + 1) => M) (x := x) (p := a)

/-- `Fin.snoc` evaluated at its own last position. -/
theorem snoc_last_apply {k : ℕ} (a : Fin k → M) (x : M) :
    (Fin.snoc a x : Fin (k + 1) → M) ⟨k, by omega⟩ = x :=
  Fin.snoc_last (α := fun _ : Fin (k + 1) => M) (x := x) (p := a)

/-- **The value of the frozen Horner term** at a coefficient tuple `a` and a root candidate `x`. -/
theorem hornerPoly_realize {m : ℕ} (a : Fin (m + 1) → M) (x : M) :
    (hornerPoly (k := m + 1) tVFAdd tVFMul).realize
        (Sum.elim (default : Empty → M) (Fin.snoc a x : Fin (m + 1 + 1) → M))
      = (List.finRange m).reverse.foldl
          (fun acc (i : Fin m) => iVFAdd (iVFMul acc x) (a i.castSucc))
          (iVFAdd x (a (Fin.last m))) := by
  rw [hornerPoly]
  have hstep : ∀ (acc : Tm (m + 1 + 1)) (i : Fin m),
      (tVFAdd (tVFMul acc (tv (m + 1) (by omega))) (tv i.val (by omega))).realize
          (Sum.elim (default : Empty → M) (Fin.snoc a x : Fin (m + 1 + 1) → M))
        = iVFAdd (iVFMul ((acc).realize
            (Sum.elim (default : Empty → M) (Fin.snoc a x : Fin (m + 1 + 1) → M))) x)
            (a i.castSucc) := by
    intro acc i
    rw [realize_tVFAdd, realize_tVFMul,
      show (tv (m + 1) (by omega) : Tm (m + 1 + 1)).realize
          (Sum.elim (default : Empty → M) (Fin.snoc a x : Fin (m + 1 + 1) → M))
          = (Fin.snoc a x : Fin (m + 1 + 1) → M) ⟨m + 1, by omega⟩ from rfl,
      show (tv i.val (by omega) : Tm (m + 1 + 1)).realize
          (Sum.elim (default : Empty → M) (Fin.snoc a x : Fin (m + 1 + 1) → M))
          = (Fin.snoc a x : Fin (m + 1 + 1) → M) ⟨i.val, by omega⟩ from rfl,
      snoc_root a x, snoc_castSucc_castSucc a x i]
  have hinit : (tVFAdd (tv (m + 1) (by omega)) (tv m (by omega))).realize
      (Sum.elim (default : Empty → M) (Fin.snoc a x : Fin (m + 1 + 1) → M))
      = iVFAdd x (a (Fin.last m)) := by
    rw [realize_tVFAdd,
      show (tv (m + 1) (by omega) : Tm (m + 1 + 1)).realize
          (Sum.elim (default : Empty → M) (Fin.snoc a x : Fin (m + 1 + 1) → M))
          = (Fin.snoc a x : Fin (m + 1 + 1) → M) ⟨m + 1, by omega⟩ from rfl,
      show (tv m (by omega) : Tm (m + 1 + 1)).realize
          (Sum.elim (default : Empty → M) (Fin.snoc a x : Fin (m + 1 + 1) → M))
          = (Fin.snoc a x : Fin (m + 1 + 1) → M) ⟨m, by omega⟩ from rfl,
      snoc_root a x, snoc_last_coeff a x]
  have h := List.foldl_hom
    (fun t : Tm (m + 1 + 1) => t.realize
      (Sum.elim (default : Empty → M) (Fin.snoc a x : Fin (m + 1 + 1) → M)))
    (g₁ := fun (acc : Tm (m + 1 + 1)) (i : Fin m) =>
      tVFAdd (tVFMul acc (tv (m + 1) (by omega))) (tv i.val (by omega)))
    (g₂ := fun (acc : M) (i : Fin m) => iVFAdd (iVFMul acc x) (a i.castSucc))
    (l := (List.finRange m).reverse)
    (init := tVFAdd (tv (m + 1) (by omega)) (tv m (by omega)))
    (fun acc i => (hstep acc i).symm)
  rw [hinit] at h
  exact h.symm

/-- **The algebraic-closedness scheme of the frozen encoding, semantically.** -/
theorem acfScheme_realize {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {k : ℕ}
    (hk : 1 ≤ k) (a : Fin k → M) (ha : ∀ i, iVF (a i)) :
    ∃ x : M, iVF x ∧ (hornerPoly (k := k) tVFAdd tVFMul).realize
        (Sum.elim (default : Empty → M) (Fin.snoc a x)) = iVFZero := by
  have hmem : allSorted (fun _ : Fin k => SortTag.vf)
      (exSorted SortTag.vf (pEq (hornerPoly tVFAdd tVFMul) tVFZero)) ∈ Axioms.ACVF :=
    mem_ACVF_vfAlgClosed ⟨k, hk, rfl⟩
  have h := allSorted_realize hM hmem a ha
  simp only [exSorted, BoundedFormula.realize_ex, BoundedFormula.realize_inf, sortPred_realize,
    pEq, BoundedFormula.realize_bdEqual, realize_tVFZero, realize_tv] at h
  obtain ⟨x, hx, hxz⟩ := h
  exact ⟨x, snoc_last_apply a x ▸ hx, hxz⟩

end HornerRealize

/-! ## 3. The `VF` sort as a field: the ring operations are the frozen symbols -/

section VFVal

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

@[simp] theorem vf_add_val (u v : VFType (M := M)) : (u + v).1 = iVFAdd u.1 v.1 := rfl

@[simp] theorem vf_mul_val (u v : VFType (M := M)) : (u * v).1 = iVFMul u.1 v.1 := rfl

@[simp] theorem vf_zero_val : (0 : VFType (M := M)).1 = iVFZero := rfl

/-- **The Horner fold computed in `VFType` agrees, on values, with the frozen fold in `M`.** -/
theorem fold_val_eq {m : ℕ} (a : Fin (m + 1) → VFType (M := M)) (x : VFType (M := M)) :
    ((List.finRange m).reverse.foldl
        (fun acc (i : Fin m) => acc * x + a i.castSucc) (x + a (Fin.last m))).1
      = (List.finRange m).reverse.foldl
          (fun acc (i : Fin m) => iVFAdd (iVFMul acc x.1) (a i.castSucc).1)
          (iVFAdd x.1 (a (Fin.last m)).1) := by
  refine Eq.trans ?_ (List.foldl_hom (Subtype.val)
    (g₁ := fun (acc : VFType (M := M)) (i : Fin m) => acc * x + a i.castSucc)
    (g₂ := fun (acc : M) (i : Fin m) => iVFAdd (iVFMul acc x.1) (a i.castSucc).1)
    (l := (List.finRange m).reverse)
    (init := x + a (Fin.last m)) (fun acc i => rfl)).symm
  rfl

end VFVal

/-! ## 4. `IsAlgClosed` of the `VF` sort -/

section Main

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- **The `VF` sort of a model of the frozen `ACVF` is an algebraically closed field.** -/
theorem isAlgClosed_vfType :
    @IsAlgClosed (VFType (M := M)) (vfFieldOfModel (M := M) (hM := hM)) := by
  letI : Field (VFType (M := M)) := vfFieldOfModel (M := M) (hM := hM)
  refine IsAlgClosed.of_exists_root _ ?_
  intro p hpm hpi
  have hdeg : 0 < p.natDegree :=
    Polynomial.natDegree_pos_iff_degree_pos.2 (Polynomial.degree_pos_of_irreducible hpi)
  obtain ⟨m, hm⟩ : ∃ m, p.natDegree = m + 1 := ⟨p.natDegree - 1, by omega⟩
  -- the coefficient tuple, in `M` and in `VFType`
  obtain ⟨x, hx, hxeq⟩ := acfScheme_realize (M := M) hM (k := m + 1) (by omega)
    (fun i => (p.coeff (i : ℕ)).1) (fun i => (p.coeff (i : ℕ)).2)
  set x' : VFType (M := M) := ⟨x, hx⟩ with hx'def
  have hxeq' : (List.finRange m).reverse.foldl
      (fun acc (i : Fin m) => iVFAdd (iVFMul acc x) ((p.coeff (i.castSucc : ℕ)).1))
      (iVFAdd x ((p.coeff (Fin.last m : ℕ)).1)) = iVFZero :=
    (hornerPoly_realize (fun i => (p.coeff (i : ℕ)).1) x).symm.trans hxeq
  refine ⟨x', ?_⟩
  have hK : (List.finRange m).reverse.foldl
      (fun acc (i : Fin m) => acc * x' + p.coeff (i.castSucc : ℕ)) (x' + p.coeff m) = 0 := by
    apply Subtype.ext
    exact (fold_val_eq (a := fun i => p.coeff (i : ℕ)) (x := x')).trans hxeq'
  refine Eq.trans (eval_monic_eq hpm hm x') ?_
  refine Eq.trans (horner_fold_eq (fun i => p.coeff i) x' m).symm ?_
  exact hK

end Main

end VFAlgClosed

/-! ## Axiom checks -/

#print axioms VFAlgClosed.foldl_finRange_reverse
#print axioms VFAlgClosed.horner_fold_eq
#print axioms VFAlgClosed.eval_monic_eq
#print axioms VFAlgClosed.hornerPoly_realize
#print axioms VFAlgClosed.acfScheme_realize
#print axioms VFAlgClosed.fold_val_eq
#print axioms VFAlgClosed.isAlgClosed_vfType

/-
  Packaging: the `VF` sort of a frozen `ACVF`-model as a model of `ValPM.ACVF_val`.

  `ACVF_val = valField ∪ genericMonicPolyHasRoot '' {n | 0 < n} ∪ {axNontrivial}`.  The three
  parts are assembled here:

  * `valField` from `ValPM.valField_model` and the extracted predicate axioms
    (`model_valField`), which is where members d1/d3/d4 plug in;
  * the monic-polynomial scheme and `axNontrivial` are taken as the *sentence-level*
    realization hypotheses `hgen` and `hnt`, because supplying them needs a
    `Language.ring.Structure` on the `VF` sort compatible with the `L_val` one, which is
    plumbing rather than mathematics.

  **Obstruction worth recording.** `axNontrivial` is *not* a consequence of the frozen
  `Axioms.ACVF`: the theory does not force the valuation to be nontrivial, so the model of
  `Axioms.ACVF` whose valuation is trivial (all nonzero elements of value `1`, `Kˣ` = all of
  `RV^×`) satisfies every frozen axiom — its residue field is the algebraically closed field
  itself, its `RV^×` group is divisible, and the preorder collapses to equality of classes —
  but there is no nonzero `x` with `¬ (v 1 ≤ v x)`.  Hence `S ⊨ ValPM.ACVF_val` needs
  nontriviality as an extra hypothesis, exactly as `QE-PLAN.md` records an extra hypothesis
  for `leMulCompat`.
-/

open FirstOrder FirstOrder.Language FirstOrder.Ring
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer

namespace VFPack

section Pack

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

attribute [local instance] vfFieldOfModel

/-- The `L_val`-predicate `v x ≤ v y` extracted from the paper's *reversed* order on `RV`:
`v x ≤ v y` is `iLe (rv y) (rv x)`. -/
def predV (x y : VFType (M := M)) : Prop := iLe (iRv y.1) (iRv x.1)

/-- The `L_val`-structure on the `VF` sort (the ring symbols of `VF`, the reversed order). -/
noncomputable abbrev structV : Language.val.Structure (VFType (M := M)) :=
  ValPM.valStructOf (VFType (M := M)) predV

theorem predM_iff_predV (x y : VFType (M := M)) :
    @ValPM.predM (VFType (M := M)) (structV (M := M)) x y ↔ predV x y :=
  Iff.rfl

/-- **`valField` holds on the `VF` sort**, given the extracted predicate axioms. -/
theorem model_valField (hp : ValPM.IsValPred (predV (M := M))) :
    @Theory.Model Language.val (VFType (M := M)) (structV (M := M)) ValPM.valField :=
  ValPM.valField_model hp

/-- **Assembly of `ACVF_val`** from its three parts: the theory of valued fields, the
monic-polynomial scheme at every positive degree, and nontriviality. -/
theorem model_ACVF_val (hp : ValPM.IsValPred (predV (M := M)))
    (hgen : ∀ n : ℕ, 0 < n → @Sentence.Realize Language.val (VFType (M := M))
      (structV (M := M)) (ValPM.genericMonicPolyHasRoot n))
    (hnt : @Sentence.Realize Language.val (VFType (M := M)) (structV (M := M))
      ValPM.axNontrivial) :
    @Theory.Model Language.val (VFType (M := M)) (structV (M := M)) ValPM.ACVF_val := by
  letI : Language.val.Structure (VFType (M := M)) := structV
  have hval : @Theory.Model Language.val (VFType (M := M)) (structV (M := M))
      ValPM.valField := model_valField hp
  refine ⟨fun φ hφ => ?_⟩
  simp only [ValPM.ACVF_val, Set.mem_union, Set.mem_image, Set.mem_setOf_eq,
    Set.mem_singleton_iff] at hφ
  rcases hφ with (hφ | ⟨n, hn, rfl⟩) | rfl
  · exact hval.realize_of_mem φ hφ
  · exact hgen n hn
  · exact hnt

end Pack

end VFPack

#print axioms VFPack.predM_iff_predV
#print axioms VFPack.model_valField
#print axioms VFPack.model_ACVF_val


/-!
# The sort-restricted `L_val`-evaluator

`valFormulaEval` (section 23 of `QE/Assembly_val.lean`) reads an `L_val`-formula in the *whole*
carrier `M` of an `L_RV`-structure: `| BoundedFormula.all φ => ∀ a : M, …`.  That is the wrong
reading for the transfer, where the `L_val`-structure lives on the `VF` sort `S = {x // iVF x}`.

This file

* puts the `Language.val`-structure of the campaign goal on `S = VFType` (`vfStruct`),
* defines the sort-restricted evaluator `valFormulaEvalVF` (`∀ a, iVF a → …`),
* proves `realize_valFormulaVF`: realisation of an `L_val`-formula at a tuple `Fin n → S` in that
  structure is the restricted evaluator,
* proves the syntactic bridge `valFormulaToRVvf_realize` against the *relativised* translation
  `valFormulaToRVvf`, which inserts the sort guard at every quantifier — the guard cannot be
  dropped: `unguarded_bridge_fails` exhibits the sentence `∀ x, x + (-x) = 0`, which the plain
  `valFormulaToRV` reads with the wrong quantifier range as soon as the carrier has a `VF`-junk
  element at which that equation fails,
* shows that on quantifier-free formulas the relativised translation and the restricted evaluator
  coincide with the existing `valFormulaToRV` / `valFormulaEval`, which is the case a
  quantifier-eliminated output lands in, and packages the sentence/theory-level transfer,
* closes the `NOTE` in `Assembly_val.lean` by proving `valStructOfLRV_realize`
  (`valFormulaEval` is realisation in `valStructOfLRV M`),
* and records that the symbols of `vfStruct` are the operations of `vfFieldOfModel`
  (`vfStruct_add_apply` … `vfStruct_le_apply`), so statements phrased with `+ * - 0 1` on
  `VFType` read in `vfStruct` without transport.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 LRV
open SpecialTransformations.Milestone0.Transfer

namespace VFRestrict

variable {M : Type} [LRV.Structure M]

/-! ### The `L_val`-structure on the `VF` sort -/

/-- The `Language.val`-structure on the `VF` sort `S = {x // iVF x}` of an `ACVF`-model: the ring
symbols are the `VF`-sorted symbols of `L_RV`, and the predicate is `iLe (rv y) (rv x)` — the
paper's `vv x ≤ vv y` under the reversal `vv = vrv ∘ rv`, since `L_val` puts `v 0` at the bottom
and the `RV`-order puts `rv 0 = ∞` at the top. -/
@[instance_reducible]
noncomputable def vfStruct (hM : M ⊨ Axioms.ACVF) :
    Language.val.Structure (VFType (M := M)) where
  funMap := fun {_} f x =>
    match f with
    | ValFunc.add => ⟨iVFAdd (x 0).1 (x 1).1, vf_add_mem hM (x 0).2 (x 1).2⟩
    | ValFunc.mul => ⟨iVFMul (x 0).1 (x 1).1, vf_mul_mem hM (x 0).2 (x 1).2⟩
    | ValFunc.neg => ⟨iVFNeg (x 0).1, vf_neg_mem hM (x 0).2⟩
    | ValFunc.zero => ⟨iVFZero, vf_zero_mem hM⟩
    | ValFunc.one => ⟨iVFOne, vf_one_mem hM⟩
  RelMap := fun {_} r x =>
    match r with
    | ValRel.le => iLe (iRv (x 1).1) (iRv (x 0).1)

section Unfold

variable {n : ℕ}

/-- Unfolding lemma for the ring symbols of `vfStruct`. -/
theorem vfStruct_add (hM : M ⊨ Axioms.ACVF) (x : Fin 2 → VFType (M := M)) :
    (@Structure.funMap Language.val (VFType (M := M)) (vfStruct hM) 2 ValFunc.add x).1
      = iVFAdd (x 0).1 (x 1).1 := rfl

theorem vfStruct_mul (hM : M ⊨ Axioms.ACVF) (x : Fin 2 → VFType (M := M)) :
    (@Structure.funMap Language.val (VFType (M := M)) (vfStruct hM) 2 ValFunc.mul x).1
      = iVFMul (x 0).1 (x 1).1 := rfl

theorem vfStruct_neg (hM : M ⊨ Axioms.ACVF) (x : Fin 1 → VFType (M := M)) :
    (@Structure.funMap Language.val (VFType (M := M)) (vfStruct hM) 1 ValFunc.neg x).1
      = iVFNeg (x 0).1 := rfl

theorem vfStruct_zero (hM : M ⊨ Axioms.ACVF) (x : Fin 0 → VFType (M := M)) :
    (@Structure.funMap Language.val (VFType (M := M)) (vfStruct hM) 0 ValFunc.zero x).1
      = iVFZero := rfl

theorem vfStruct_one (hM : M ⊨ Axioms.ACVF) (x : Fin 0 → VFType (M := M)) :
    (@Structure.funMap Language.val (VFType (M := M)) (vfStruct hM) 0 ValFunc.one x).1
      = iVFOne := rfl

/-- Unfolding lemma for the predicate of `vfStruct`: **the order is reversed**. -/
theorem vfStruct_le (hM : M ⊨ Axioms.ACVF) (x : Fin 2 → VFType (M := M)) :
    (@Structure.RelMap Language.val (VFType (M := M)) (vfStruct hM) 2 ValRel.le x)
      ↔ iLe (iRv (x 1).1) (iRv (x 0).1) := Iff.rfl

end Unfold


/-! ### Agreement with the field structure and the predicate of the campaign goal

`vfStruct` is *the* structure of the campaign: its symbols are the `VF`-sorted `L_RV`-symbols, which
are also the operations of `vfFieldOfModel`.  The lemmas below say so, so that statements phrased
with `+ * - 0 1` on `VFType` (as the field axioms are) can be read in `vfStruct` without any
transport. -/

theorem vfStruct_add_apply (hM : M ⊨ Axioms.ACVF) (x y : VFType (M := M)) :
    (@Structure.funMap Language.val (VFType (M := M)) (vfStruct hM) 2 ValFunc.add ![x, y])
      = x + y := rfl

theorem vfStruct_mul_apply (hM : M ⊨ Axioms.ACVF) (x y : VFType (M := M)) :
    (@Structure.funMap Language.val (VFType (M := M)) (vfStruct hM) 2 ValFunc.mul ![x, y])
      = x * y := rfl

theorem vfStruct_neg_apply (hM : M ⊨ Axioms.ACVF) (x : VFType (M := M)) :
    (@Structure.funMap Language.val (VFType (M := M)) (vfStruct hM) 1 ValFunc.neg ![x]) = -x := rfl

theorem vfStruct_zero_apply (hM : M ⊨ Axioms.ACVF) :
    (@Structure.funMap Language.val (VFType (M := M)) (vfStruct hM) 0 ValFunc.zero
      (fun i => i.elim0)) = (0 : VFType (M := M)) := rfl

theorem vfStruct_one_apply (hM : M ⊨ Axioms.ACVF) :
    (@Structure.funMap Language.val (VFType (M := M)) (vfStruct hM) 0 ValFunc.one
      (fun i => i.elim0)) = (1 : VFType (M := M)) := rfl

/-- The predicate of `vfStruct` is the campaign's `pred x y := iLe (iRv y.1) (iRv x.1)`. -/
theorem vfStruct_le_apply (hM : M ⊨ Axioms.ACVF) (x y : VFType (M := M)) :
    (@Structure.RelMap Language.val (VFType (M := M)) (vfStruct hM) 2 ValRel.le ![x, y])
      ↔ iLe (iRv y.1) (iRv x.1) :=
  vfStruct_le hM ![x, y]

/-! ### Terms -/

/-- `L_val`-terms evaluate in `vfStruct` to the `VF`-sorted `L_RV`-evaluation `valTermEval`, on the
nose. -/
theorem realize_term_vf (hM : M ⊨ Axioms.ACVF) {n : ℕ} (x : Fin n → VFType (M := M))
    (t : Language.val.Term (Empty ⊕ Fin n)) :
    (@Term.realize Language.val (VFType (M := M)) (vfStruct hM) (Empty ⊕ Fin n)
        (Sum.elim (default : Empty → VFType (M := M)) x) t).1
      = valTermEval (fun i => (x i).1) t := by
  induction t with
  | var v =>
    rcases v with e | i
    · exact e.elim
    · rfl
  | func f args ih =>
    cases f with
    | add =>
      simp only [Term.realize_func, vfStruct_add, ih, valTermEval]
    | mul =>
      simp only [Term.realize_func, vfStruct_mul, ih, valTermEval]
    | neg =>
      simp only [Term.realize_func, vfStruct_neg, ih, valTermEval]
    | zero =>
      simp only [Term.realize_func, vfStruct_zero, valTermEval]
    | one =>
      simp only [Term.realize_func, vfStruct_one, valTermEval]

/-! ### The sort-restricted evaluator -/

/-- **The sort-restricted `L_val`-evaluator**: like `valFormulaEval`, but every quantifier ranges
over the `VF` sort only.  This is the reading of an `L_val`-formula in the structure on
`S = {x // iVF x}`. -/
def valFormulaEvalVF {n : ℕ} (x : Fin n → M) :
    Language.val.BoundedFormula Empty n → Prop
  | BoundedFormula.falsum => False
  | BoundedFormula.equal t u => valTermEval x t = valTermEval x u
  | BoundedFormula.rel r ts =>
    match r with
    | ValRel.le => iLe (iRv (valTermEval x (ts 1))) (iRv (valTermEval x (ts 0)))
  | BoundedFormula.imp φ ψ => valFormulaEvalVF x φ → valFormulaEvalVF x ψ
  | BoundedFormula.all φ => ∀ a : M, iVF a → valFormulaEvalVF (Fin.snoc x a) φ

/-- Pushing a map through `Fin.snoc`. -/
theorem map_snoc {α β : Type*} {n : ℕ} (f : α → β) (x : Fin n → α) (a : α) :
    (fun i => f ((Fin.snoc x a : Fin (n + 1) → α) i))
      = Fin.snoc (fun i => f (x i)) (f a) := by
  funext i
  refine Fin.lastCases ?_ ?_ i <;> simp

/-- The same for the `VF` sort, in the exact shape the induction below needs. -/
theorem val_snoc {n : ℕ} (x : Fin n → VFType (M := M)) (a : VFType (M := M)) :
    (fun i => ((Fin.snoc x a : Fin (n + 1) → VFType (M := M)) i).1)
      = Fin.snoc (fun i => (x i).1) a.1 :=
  map_snoc (Subtype.val : VFType (M := M) → M) x a

/-- **Realisation in `vfStruct` is the sort-restricted evaluator.**  This is the statement the
transfer needs: `L_val`-formulas read in the `L_val`-structure on the `VF` sort agree with the
evaluator whose quantifiers are relativised to `iVF`. -/
theorem realize_valFormulaVF (hM : M ⊨ Axioms.ACVF) {n : ℕ}
    (φ : Language.val.BoundedFormula Empty n) (x : Fin n → VFType (M := M)) :
    (@BoundedFormula.Realize Language.val (VFType (M := M)) (vfStruct hM) Empty n φ
        (default : Empty → VFType (M := M)) x)
      ↔ valFormulaEvalVF (fun i => (x i).1) φ := by
  induction φ with
  | falsum => exact Iff.rfl
  | equal t u =>
    simp only [BoundedFormula.Realize, valFormulaEvalVF]
    rw [Subtype.ext_iff, realize_term_vf hM x t, realize_term_vf hM x u]
  | rel r ts =>
    cases r with
    | le =>
      simp only [BoundedFormula.Realize, valFormulaEvalVF, vfStruct_le,
        realize_term_vf hM x (ts 1), realize_term_vf hM x (ts 0)]
  | imp φ ψ ihφ ihψ =>
    simp only [BoundedFormula.Realize, valFormulaEvalVF, ihφ, ihψ]
  | all φ ih =>
    simp only [BoundedFormula.Realize, valFormulaEvalVF]
    constructor
    · intro h a ha
      have h1 := (ih (Fin.snoc x ⟨a, ha⟩)).1 (h ⟨a, ha⟩)
      rwa [val_snoc x ⟨a, ha⟩] at h1
    · intro h a
      refine (ih (Fin.snoc x a)).2 ?_
      rw [val_snoc x a]
      exact h a.1 a.2

/-! ### The syntactic bridge: the relativised translation -/

/-- Reading the sort guard at the quantifier introduced by `BoundedFormula.all`. -/
theorem realize_pVF_last {n : ℕ} (v : Empty → M) (y : Fin (n + 1) → M) :
    (pVF (tv n (Nat.lt_succ_self n))).Realize v y ↔ iVF (y (Fin.last n)) := by
  rw [pVF_realize]
  have h : ((tv n (Nat.lt_succ_self n)).realize (Sum.elim v y)) = y (Fin.last n) :=
    realize_tv (Fin.last n) v y
  rw [h]

/-- `valFormulaToRV` with the sort guard inserted at every quantifier: the quantifiers of the
`L_val`-formula are read in the `VF` sort, so the translation has to relativise them.  Without the
guard the bridge below is false — see `unguarded_bridge_fails` at the end of the file, which uses
`∀ x, x + (-x) = 0`. -/
def valFormulaToRVvf {n : ℕ} : Language.val.BoundedFormula Empty n → Bf n
  | BoundedFormula.falsum => BoundedFormula.falsum
  | BoundedFormula.equal t u => BoundedFormula.equal (valTermToRV t) (valTermToRV u)
  | BoundedFormula.rel r ts =>
    match r with
    | ValRel.le => pLe (tRv (valTermToRV (ts 1))) (tRv (valTermToRV (ts 0)))
  | BoundedFormula.imp φ ψ => BoundedFormula.imp (valFormulaToRVvf φ) (valFormulaToRVvf ψ)
  | BoundedFormula.all φ =>
    BoundedFormula.all (pVF (tv n (Nat.lt_succ_self n)) ⟹ valFormulaToRVvf φ)

/-- **The bridge**: the relativised translation realises in `M` exactly as the sort-restricted
evaluator does.  (`valFormulaToRV_realize` is the same proof with the quantifier guard absent.) -/
theorem valFormulaToRVvf_realize {n : ℕ} (φ : Language.val.BoundedFormula Empty n)
    (x : Fin n → M) :
    (valFormulaToRVvf φ).Realize (default : Empty → M) x ↔ valFormulaEvalVF x φ := by
  induction φ with
  | falsum => exact Iff.rfl
  | equal t u =>
    show (valTermToRV t).realize (Sum.elim (default : Empty → M) x)
        = (valTermToRV u).realize (Sum.elim (default : Empty → M) x)
      ↔ valTermEval x t = valTermEval x u
    rw [valTermToRV_realize x t, valTermToRV_realize x u]
  | rel r ts =>
    cases r with
    | le =>
      rw [valFormulaToRVvf, realize_pLe, realize_tRv, realize_tRv, valTermToRV_realize,
        valTermToRV_realize]
      exact Iff.rfl
  | imp φ ψ ihφ ihψ =>
    simp only [valFormulaToRVvf, valFormulaEvalVF, BoundedFormula.realize_imp, ihφ, ihψ]
  | all φ ih =>
    simp only [valFormulaToRVvf, valFormulaEvalVF, BoundedFormula.realize_imp,
      BoundedFormula.realize_all, realize_pVF_last, Fin.snoc_last]
    exact ⟨fun h a ha => (ih (Fin.snoc x a)).1 (h a ha),
      fun h a ha => (ih (Fin.snoc x a)).2 (h a ha)⟩


/-! ### Quantifier-free formulas need no guard -/

/-- Quantifier-freeness of an `L_val`-formula: the fragment on which the guard is inert. -/
def IsQFVal {n : ℕ} : Language.val.BoundedFormula Empty n → Prop
  | BoundedFormula.falsum => True
  | BoundedFormula.equal _ _ => True
  | BoundedFormula.rel _ _ => True
  | BoundedFormula.imp φ ψ => IsQFVal φ ∧ IsQFVal ψ
  | BoundedFormula.all _ => False

/-- On quantifier-free formulas the relativised translation is the original one. -/
theorem valFormulaToRVvf_eq_of_QF {n : ℕ} {φ : Language.val.BoundedFormula Empty n}
    (h : IsQFVal φ) : valFormulaToRVvf φ = valFormulaToRV φ := by
  induction φ with
  | falsum => rfl
  | equal t u => rfl
  | rel r ts => cases r with | le => rfl
  | imp φ ψ ihφ ihψ =>
    obtain ⟨h1, h2⟩ := h
    rw [valFormulaToRVvf, valFormulaToRV, ihφ h1, ihψ h2]
  | all φ ih => exact absurd h (by simp [IsQFVal])

/-- On quantifier-free formulas the sort-restricted evaluator is the unrestricted one. -/
theorem valFormulaEvalVF_eq_of_QF {n : ℕ} {φ : Language.val.BoundedFormula Empty n}
    (x : Fin n → M) (h : IsQFVal φ) :
    (valFormulaEvalVF x φ ↔ valFormulaEval x φ) := by
  induction φ with
  | falsum => exact Iff.rfl
  | equal t u => exact Iff.rfl
  | rel r ts => cases r with | le => exact Iff.rfl
  | imp φ ψ ihφ ihψ =>
    obtain ⟨h1, h2⟩ := h
    rw [valFormulaEvalVF, valFormulaEval, ihφ x h1, ihψ x h2]
  | all φ ih => exact absurd h (by simp [IsQFVal])

/-- Quantifier-free formulas: the existing translation `valFormulaToRV` agrees with the
sort-restricted evaluator.  This is `valFormulaToRV_realize` with the reading of the formula
restricted to the `VF` sort, and it is what lets a quantifier-eliminated output be read back. -/
theorem valFormulaToRV_realize_of_QF {n : ℕ} {φ : Language.val.BoundedFormula Empty n}
    (h : IsQFVal φ) (x : Fin n → M) :
    (valFormulaToRV φ).Realize (default : Empty → M) x ↔ valFormulaEvalVF x φ := by
  rw [← valFormulaToRVvf_eq_of_QF h]
  exact valFormulaToRVvf_realize φ x


/-- Mathlib's `BoundedFormula.IsQF` implies the bespoke `IsQFVal` used here, so the output of a
quantifier-elimination run (`ψ.IsQF`) can be fed to the lemmas above. -/
theorem isQFVal_of_isQF {n : ℕ} {φ : Language.val.BoundedFormula Empty n} (h : φ.IsQF) :
    IsQFVal φ := by
  induction h with
  | falsum => trivial
  | of_isAtomic h => induction h with
    | equal t u => trivial
    | rel R ts => trivial
  | imp h1 h2 ih1 ih2 => exact ⟨ih1, ih2⟩

/-- Composed form: a quantifier-eliminated output read back into `L_RV`. -/
theorem valFormulaToRV_realize_of_isQF {n : ℕ} {φ : Language.val.BoundedFormula Empty n}
    (h : φ.IsQF) (x : Fin n → M) :
    (valFormulaToRV φ).Realize (default : Empty → M) x ↔ valFormulaEvalVF x φ :=
  valFormulaToRV_realize_of_QF (isQFVal_of_isQF h) x


/-! ### Tuples of `VF`-elements given by their trace in `M` -/

/-- Realisation in `vfStruct` for a tuple of `M`-elements known to lie in the `VF` sort. -/
theorem realize_valFormulaVF' (hM : M ⊨ Axioms.ACVF) {n : ℕ}
    (φ : Language.val.BoundedFormula Empty n) (x : Fin n → M) (hx : ∀ i, iVF (x i)) :
    (@BoundedFormula.Realize Language.val (VFType (M := M)) (vfStruct hM) Empty n φ
        (default : Empty → VFType (M := M)) (fun i => (⟨x i, hx i⟩ : VFType (M := M))))
      ↔ valFormulaEvalVF x φ := by
  have := realize_valFormulaVF hM φ (fun i => (⟨x i, hx i⟩ : VFType (M := M)))
  simpa using this

/-- **Semantic transfer at the level of formulas.**  If an `L_val`-formula is realised in the
`L_val`-structure on the `VF` sort by a tuple of `VF`-elements of `M`, then its guarded `L_RV`
image is realised by the same tuple in `M`. -/
theorem valFormulaToRVvf_realize_VF (hM : M ⊨ Axioms.ACVF) {n : ℕ}
    (φ : Language.val.BoundedFormula Empty n) (x : Fin n → M) (hx : ∀ i, iVF (x i)) :
    (valFormulaToRVvf φ).Realize (default : Empty → M) x
      ↔ (@BoundedFormula.Realize Language.val (VFType (M := M)) (vfStruct hM) Empty n φ
          (default : Empty → VFType (M := M)) (fun i => (⟨x i, hx i⟩ : VFType (M := M)))) := by
  rw [valFormulaToRVvf_realize, realize_valFormulaVF']

/-- **Semantic transfer of an equivalence.**  If two `L_val`-formulas agree on the `VF` sort, then
their `L_RV` images agree on every tuple of `VF`-elements of `M`. -/
theorem transfer_iff (hM : M ⊨ Axioms.ACVF) {n : ℕ}
    {φ ψ : Language.val.BoundedFormula Empty n}
    (h : ∀ x : Fin n → VFType (M := M),
      (@BoundedFormula.Realize Language.val (VFType (M := M)) (vfStruct hM) Empty n φ
        (default : Empty → VFType (M := M)) x)
      ↔ (@BoundedFormula.Realize Language.val (VFType (M := M)) (vfStruct hM) Empty n ψ
        (default : Empty → VFType (M := M)) x))
    (y : Fin n → M) (hy : ∀ i, iVF (y i)) :
    (valFormulaToRVvf φ).Realize (default : Empty → M) y
      ↔ (valFormulaToRVvf ψ).Realize (default : Empty → M) y := by
  rw [valFormulaToRVvf_realize_VF hM φ y hy, valFormulaToRVvf_realize_VF hM ψ y hy]
  exact h _

/-- **Sentences**: realisation of an `L_val`-sentence in the `L_val`-structure on the `VF` sort is
realisation of its guarded `L_RV` image in `M`.  This is the statement that turns a model of
`ValPM.ACVF_val` on the `VF` sort into `L_RV`-sentences true in `M`. -/
theorem sentence_realize_iff (hM : M ⊨ Axioms.ACVF) (φ : Language.val.Sentence) :
    (@Sentence.Realize Language.val (VFType (M := M)) (vfStruct hM) φ)
      ↔ (valFormulaToRVvf φ).Realize (default : Empty → M) (default : Fin 0 → M) := by
  have h1 : (@Sentence.Realize Language.val (VFType (M := M)) (vfStruct hM) φ)
      ↔ valFormulaEvalVF (fun i => ((default : Fin 0 → VFType (M := M)) i).1) φ := by
    rw [Sentence.Realize]
    exact realize_valFormulaVF hM φ (default : Fin 0 → VFType (M := M))
  have hsub : (fun i => ((default : Fin 0 → VFType (M := M)) i).1) = (default : Fin 0 → M) :=
    Subsingleton.elim _ _
  rw [hsub] at h1
  exact h1.trans (valFormulaToRVvf_realize φ (default : Fin 0 → M)).symm

/-- **Axiom-level transport**: every `L_val`-sentence true in the `L_val`-structure on the `VF` sort
has a guarded `L_RV` image that is true in `M`.  In particular a proof of
`ValPM.ACVF_val.Model (VFType)` gives, sentence by sentence, an `L_RV`-theory realised in `M`. -/
theorem theory_transfer (hM : M ⊨ Axioms.ACVF) {T : Language.val.Theory}
    (hT : @Theory.Model Language.val (VFType (M := M)) (vfStruct hM) T) :
    ∀ φ ∈ T, (valFormulaToRVvf φ).Realize (default : Empty → M) (default : Fin 0 → M) :=
  fun φ hφ => (sentence_realize_iff hM φ).1 (hT.realize_of_mem φ hφ)

/-! ### `valFormulaEval` is realisation in `valStructOfLRV`

`Assembly_val.lean` defines `valStructOfLRV M : Language.val.Structure M` on the whole carrier and
records in a NOTE that `valFormulaEval x φ ↔ (φ.Realize default x)` in that structure "is true by
the same recursion" but "runs into `RelMap`'s implicit-language argument".  It does not: the
induction is the one below.  With it, the unrestricted evaluator has a *meaning* (the `L_val`
semantics on the whole carrier) and the restricted one is exactly its restriction to the `VF` sort.
-/

/-- The predicate of `valStructOfLRV`, unfolded. -/
theorem valStructOfLRV_le (x : Fin 2 → M) :
    (@Structure.RelMap Language.val M (valStructOfLRV M) 2 ValRel.le x)
      ↔ iLe (iRv (x 1)) (iRv (x 0)) := Iff.rfl

/-- **`valFormulaEval` is the `L_val`-realisation in `valStructOfLRV M`.** -/
theorem valStructOfLRV_realize {n : ℕ} (φ : Language.val.BoundedFormula Empty n)
    (x : Fin n → M) :
    (@BoundedFormula.Realize Language.val M (valStructOfLRV M) Empty n φ
        (default : Empty → M) x)
      ↔ valFormulaEval x φ := by
  induction φ with
  | falsum => exact Iff.rfl
  | equal t u =>
    simp only [BoundedFormula.Realize, valFormulaEval, realize_valTermEval]
  | rel r ts =>
    cases r with
    | le =>
      simp only [BoundedFormula.Realize, valFormulaEval, valStructOfLRV_le, realize_valTermEval]
  | imp φ ψ ihφ ihψ =>
    simp only [BoundedFormula.Realize, valFormulaEval, ihφ, ihψ]
  | all φ ih =>
    simp only [BoundedFormula.Realize, valFormulaEval]
    exact ⟨fun h a => (ih (Fin.snoc x a)).1 (h a), fun h a => (ih (Fin.snoc x a)).2 (h a)⟩

/-- Realisation of an `L_val`-formula at a tuple of `VF`-elements: the `L_val`-structure on the
`VF` sort and the structure `valStructOfLRV M` on the whole carrier agree. -/
theorem realize_vfStruct_iff_valStructOfLRV (hM : M ⊨ Axioms.ACVF) {n : ℕ}
    {φ : Language.val.BoundedFormula Empty n} (hφ : IsQFVal φ) (x : Fin n → VFType (M := M)) :
    (@BoundedFormula.Realize Language.val (VFType (M := M)) (vfStruct hM) Empty n φ
        (default : Empty → VFType (M := M)) x)
      ↔ (@BoundedFormula.Realize Language.val M (valStructOfLRV M) Empty n φ
        (default : Empty → M) (fun i => (x i).1)) := by
  rw [realize_valFormulaVF hM φ x, valStructOfLRV_realize]
  exact valFormulaEvalVF_eq_of_QF _ hφ
/-- **The packaged transfer**: an `L_val`-formula equivalent on the `VF` sort to a quantifier-free
one has, as its `L_RV` image, the guard-free `valFormulaToRV` image of the quantifier-free one —
for every tuple of `VF`-elements of `M`.  This is the step that reads a quantifier-eliminated
answer back into `L_RV`. -/
theorem transfer_of_isQF (hM : M ⊨ Axioms.ACVF) {n : ℕ}
    {φ ψ : Language.val.BoundedFormula Empty n} (hψ : ψ.IsQF)
    (h : ∀ x : Fin n → VFType (M := M),
      (@BoundedFormula.Realize Language.val (VFType (M := M)) (vfStruct hM) Empty n φ
        (default : Empty → VFType (M := M)) x)
      ↔ (@BoundedFormula.Realize Language.val (VFType (M := M)) (vfStruct hM) Empty n ψ
        (default : Empty → VFType (M := M)) x))
    (y : Fin n → M) (hy : ∀ i, iVF (y i)) :
    (valFormulaToRVvf φ).Realize (default : Empty → M) y
      ↔ (valFormulaToRV ψ).Realize (default : Empty → M) y := by
  have h1 := transfer_iff hM h y hy
  rw [valFormulaToRVvf_eq_of_QF (isQFVal_of_isQF hψ)] at h1
  exact h1

/-- **Sentence-level packaged transfer**: if an `L_val`-sentence is equivalent in the `VF`-sort
structure to a quantifier-free sentence, then its `L_RV` image is equivalent in `M` to the
guard-free image of that quantifier-free sentence. -/
theorem sentence_transfer_of_isQF (hM : M ⊨ Axioms.ACVF)
    {φ ψ : Language.val.Sentence} (hψ : ψ.IsQF)
    (h : @Sentence.Realize Language.val (VFType (M := M)) (vfStruct hM) φ
      ↔ @Sentence.Realize Language.val (VFType (M := M)) (vfStruct hM) ψ) :
    (valFormulaToRVvf φ).Realize (default : Empty → M) (default : Fin 0 → M)
      ↔ (valFormulaToRV ψ).Realize (default : Empty → M) (default : Fin 0 → M) := by
  rw [← sentence_realize_iff hM φ, h, sentence_realize_iff hM ψ,
    valFormulaToRVvf_eq_of_QF (isQFVal_of_isQF hψ)]


/-! ### Why the guard cannot be dropped

The unrestricted evaluator `valFormulaEval` is *not* the `L_val`-semantics of the `VF` sort, so the
guard `pVF` in `valFormulaToRVvf` is not bookkeeping: the unguarded translation
`valFormulaToRV` read with `valFormulaEval` gets quantified sentences wrong in every `ACVF`-model
that has a `VF`-junk element (`iRv 0` is one) at which `x + (-x) = 0` fails.  The axioms say
nothing about `iVFAdd` outside the `VF` sort, so this is the generic situation.
-/

/-- The `L_val`-formula `x + (-x) = 0`. -/
def negForm : Language.val.BoundedFormula Empty 1 :=
  BoundedFormula.equal
    (Term.func ValFunc.add
      ![Term.var (Sum.inr (0 : Fin 1)),
        (Term.func ValFunc.neg ![Term.var (Sum.inr (0 : Fin 1))])])
    (Term.func ValFunc.zero fun i => i.elim0)

/-- The `L_val`-sentence `∀ x, x + (-x) = 0`. -/
def negSent : Language.val.Sentence := BoundedFormula.all negForm

/-- The sort-restricted evaluator satisfies `∀ x, x + (-x) = 0` — the `VF` sort is a ring. -/
theorem valFormulaEvalVF_negSent (hM : M ⊨ Axioms.ACVF) (x : Fin 0 → M) :
    valFormulaEvalVF x negSent := by
  intro a ha
  simp only [negForm, valFormulaEvalVF, valTermEval]
  exact vf_add_neg hM ha

/-- The unrestricted evaluator does not, as soon as some element of the carrier is not in `VF`. -/
theorem not_valFormulaEval_negSent (a : M)
    (hne : iVFAdd a (iVFNeg a) ≠ iVFZero) :
    ¬ valFormulaEval (default : Fin 0 → M) negSent := by
  intro h
  have h1 := h a
  simp only [negForm, valFormulaEval] at h1
  exact hne h1

/-- **The counterexample**: in an `ACVF`-model with a `VF`-junk element at which `x + (-x) = 0`
fails, `valFormulaEval` and `valFormulaEvalVF` disagree on `∀ x, x + (-x) = 0`.  So the
unrestricted evaluator is not a semantics of the `VF` sort, and the quantifier guard in
`valFormulaToRVvf` is necessary. -/
theorem valFormulaEval_ne_valFormulaEvalVF (hM : M ⊨ Axioms.ACVF) (a : M)
    (hne : iVFAdd a (iVFNeg a) ≠ iVFZero) :
    valFormulaEvalVF (default : Fin 0 → M) negSent
      ∧ ¬ valFormulaEval (default : Fin 0 → M) negSent :=
  ⟨valFormulaEvalVF_negSent hM _, not_valFormulaEval_negSent a hne⟩


/-- **The unguarded bridge is false**: as soon as the carrier has a `VF`-junk element at which
`x + (-x) = 0` fails, the plain `valFormulaToRV` does *not* satisfy the bridge to the restricted
evaluator, for the sentence `∀ x, x + (-x) = 0`.  This is why `valFormulaToRVvf` carries the guard;
`valFormulaToRV` is still the right translation on the quantifier-free fragment (see below). -/
theorem unguarded_bridge_fails (hM : M ⊨ Axioms.ACVF) (a : M)
    (hne : iVFAdd a (iVFNeg a) ≠ iVFZero) :
    ∃ φ : Language.val.Sentence,
      ¬ ((valFormulaToRV φ).Realize (default : Empty → M) (default : Fin 0 → M)
        ↔ valFormulaEvalVF (default : Fin 0 → M) φ) := by
  refine ⟨negSent, fun h => ?_⟩
  have hne' := valFormulaEval_ne_valFormulaEvalVF hM a hne
  have hL : (valFormulaToRV negSent).Realize (default : Empty → M) (default : Fin 0 → M) :=
    h.2 hne'.1
  rw [valFormulaToRV_realize] at hL
  exact hne'.2 hL

#print axioms VFRestrict.realize_term_vf
#print axioms VFRestrict.realize_valFormulaVF
#print axioms VFRestrict.valFormulaToRVvf_realize
#print axioms VFRestrict.valFormulaToRV_realize_of_QF
#print axioms VFRestrict.realize_valFormulaVF'
#print axioms VFRestrict.sentence_realize_iff
#print axioms VFRestrict.theory_transfer
#print axioms VFRestrict.valFormulaToRV_realize_of_isQF
#print axioms VFRestrict.valStructOfLRV_realize
#print axioms VFRestrict.transfer_of_isQF
#print axioms VFRestrict.sentence_transfer_of_isQF
#print axioms VFRestrict.valFormulaEval_ne_valFormulaEvalVF
#print axioms VFRestrict.vfStruct_mul_apply
#print axioms VFRestrict.vfStruct_le_apply
#print axioms VFRestrict.unguarded_bridge_fails

end VFRestrict

/-
  **Formula-level half of the `L_val → L_RV` transfer** (swarm `smw14elno`, member m3,
  direction d6: "QE transfer at the formula level").

  Context.  The campaign proves quantifier elimination for the frozen `L_RV`-theory `ACVF` by
  transferring it from `ValPM.ACVF_val` (QE in `L_val`, `hasQE_ACVF_val`) along the syntactic
  translation `Transfer.valFormulaToRV : Language.val.BoundedFormula Empty n → Bf n`, whose
  semantic half is `Transfer.valFormulaToRV_realize`.  This file supplies the formula-level
  pieces of that transfer:

  §1 `isQF_valFormulaToRV` — the translation preserves quantifier-freeness, so a QE witness
     produced in `L_val` translates to a quantifier-free `L_RV`-formula.
  §2 `valFormulaEval_iff_realize` — `valFormulaEval` is exactly the `L_val`-realisation in
     `Transfer.valStructOfLRV M`, the whole-carrier `L_val`-structure of the file.  This closes
     the gap recorded as a NOTE in `QE/Assembly_val.lean` after `realize_valTermEval`.
  §3 The `L_val`-structure `valStructVF` on the `VF` sort `S = {x // iVF x}` (ring symbols from
     `iVFAdd`/`iVFMul`/`iVFNeg`/`iVFZero`/`iVFOne`, predicate `iLe (iRv y) (iRv x)`), the
     VF-closure of the values of `L_val`-terms (`valTermEval_mem`), and the **sort-independence
     of quantifier-free formulas**: at `VF`-tuples, a QF `L_val`-formula has the same truth value
     in the whole-carrier structure and in the structure on `VF` (`realize_QF_iff`,
     `valFormulaEval_QF_iff`).  This is false for quantified formulas — their quantifiers range
     over the junk outside `VF` — which is precisely the defect repaired by the sort-restricted
     evaluator of the sibling direction d6.
  §4 The sort-restricted evaluator `valFormulaEvalS` (quantifiers `∀ a, iVF a → …`) and its
     agreement with genuine `Language.val`-realisation in `valStructVF`
     (`valFormulaEvalS_iff_realize`, `valFormulaEvalS_iff_realize_x`).  This is the L_val-side
     semantic half of the transfer; it is checked independently of d6's file.
  §5 `qf_transfer`/`qf_transfer'` — a quantifier-free equivalence proved in `S` transfers to `M`
     at `VF`-tuples through `valFormulaToRV`, with a quantifier-free translate.  This is what
     lets a QF formula produced by `hasQE_ACVF_val` in `L_val` be read back in `L_RV`.

  Everything is unconditional: no scaling axiom and no other extra hypothesis is used.  All the
  statements are for any `M` with `M ⊨ Axioms.ACVF` (the translation half, §1-§2, needs no
  hypothesis at all).  No `sorry`, no `axiom`.
-/
open FirstOrder FirstOrder.Language
open scoped FirstOrder
open SpecialTransformations.Milestone0 LRV

set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option warn.classDefReducibility false
set_option linter.unusedSectionVars false

namespace Smw14elno.M3

/-! ## 1. `valFormulaToRV` preserves the quantifier-free fragment -/

theorem isQF_of_isAtomic {n : ℕ} {φ : Language.val.BoundedFormula Empty n} (h : φ.IsAtomic) :
    (Transfer.valFormulaToRV φ).IsQF := by
  induction h with
  | equal t₁ t₂ =>
    show BoundedFormula.IsQF ((Transfer.valTermToRV t₁) =' (Transfer.valTermToRV t₂))
    exact BoundedFormula.IsAtomic.equal _ _ |>.isQF
  | rel R ts =>
    cases R with
    | le =>
      show BoundedFormula.IsQF (pLe (tRv (Transfer.valTermToRV (ts 1)))
        (tRv (Transfer.valTermToRV (ts 0))))
      exact (BoundedFormula.IsAtomic.rel (l := 2) Rel.rvLe
        ![tRv (Transfer.valTermToRV (ts 1)), tRv (Transfer.valTermToRV (ts 0))]).isQF

/-- **The translation preserves quantifier-freeness.** -/
theorem isQF_valFormulaToRV {n : ℕ} {φ : Language.val.BoundedFormula Empty n} (h : φ.IsQF) :
    (Transfer.valFormulaToRV φ).IsQF := by
  induction h with
  | falsum => exact BoundedFormula.IsQF.falsum
  | of_isAtomic hA => exact isQF_of_isAtomic hA
  | imp _ _ ih1 ih2 => exact ih1.imp ih2

/-! ## 2. `valFormulaEval` is the realisation in `valStructOfLRV` -/

/-- `valFormulaEval` is exactly the `L_val`-realisation in `valStructOfLRV M` (the whole-carrier
`L_val`-structure induced by an `L_RV`-structure). -/
theorem valFormulaEval_iff_realize {M : Type} [LRV.Structure M] {n : ℕ}
    (φ : Language.val.BoundedFormula Empty n) (x : Fin n → M) :
    (@BoundedFormula.Realize Language.val M (Transfer.valStructOfLRV M) Empty n φ
        (default : Empty → M) x) ↔ Transfer.valFormulaEval x φ := by
  letI : Language.val.Structure M := Transfer.valStructOfLRV M
  induction φ with
  | falsum => exact Iff.rfl
  | equal t u =>
    show ((t =' u).Realize (default : Empty → M) x) ↔
      Transfer.valTermEval x t = Transfer.valTermEval x u
    rw [BoundedFormula.realize_bdEqual, Transfer.realize_valTermEval,
      Transfer.realize_valTermEval]
  | rel r ts =>
    cases r with
    | le =>
      show iLe (iRv ((ts 1).realize (Sum.elim (default : Empty → M) x)))
          (iRv ((ts 0).realize (Sum.elim (default : Empty → M) x)))
        ↔ iLe (iRv (Transfer.valTermEval x (ts 1))) (iRv (Transfer.valTermEval x (ts 0)))
      rw [Transfer.realize_valTermEval, Transfer.realize_valTermEval]
  | imp φ ψ ihφ ihψ =>
    simp only [BoundedFormula.realize_imp, Transfer.valFormulaEval]
    exact ⟨fun h ha' => (ihψ x).mp (h ((ihφ x).mpr ha')),
      fun h ha => (ihψ x).mpr (h ((ihφ x).mp ha))⟩
  | all φ ih =>
    simp only [BoundedFormula.realize_all, Transfer.valFormulaEval]
    exact forall_congr' fun a => ih (Fin.snoc x a)

/-! ## 3. The `L_val`-structure on the `VF` sort, and the sort-independence of QF formulas -/

section VFStruct

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- The `L_val`-structure on the `VF` sort of an `ACVF`-model: ring symbols from the `VF`-sorted
symbols of `L_RV`, and the predicate `v x ≤ v y := iLe (iRv y) (iRv x)` (the two orders are
reversed: in `L_val` the value of `0` is minimal, in the paper's `RV`-order `∞` is on top). -/
@[instance_reducible]
noncomputable def valStructVF : Language.val.Structure (Transfer.VFType (M := M)) where
  funMap := fun {_} f x =>
    match f with
    | ValFunc.add => x 0 + x 1
    | ValFunc.mul => x 0 * x 1
    | ValFunc.neg => - x 0
    | ValFunc.zero => 0
    | ValFunc.one => 1
  RelMap := fun {_} r x =>
    match r with
    | ValRel.le => iLe (iRv (x 1).1) (iRv (x 0).1)

/-- The `VF` sort is closed under the evaluation of `L_val`-terms at `VF`-tuples. -/
theorem valTermEval_mem {n : ℕ} (x : Fin n → M) (hx : ∀ i, iVF (x i))
    (t : Language.val.Term (Empty ⊕ Fin n)) : iVF (Transfer.valTermEval x t) := by
  induction t with
  | var v =>
    rcases v with e | i
    · exact e.elim
    · exact hx i
  | func f args ih =>
    cases f with
    | add => exact Transfer.vf_add_mem hM (ih 0) (ih 1)
    | mul => exact Transfer.vf_mul_mem hM (ih 0) (ih 1)
    | neg => exact Transfer.vf_neg_mem hM (ih 0)
    | zero => exact Transfer.vf_zero_mem hM
    | one => exact Transfer.vf_one_mem hM

/-- **Term evaluation agrees** between the `L_val`-structure on the whole carrier and the one on
the `VF` sort, at `VF`-tuples. -/
theorem realize_valTermEval_vf {n : ℕ} (x : Fin n → M) (hx : ∀ i, iVF (x i))
    (t : Language.val.Term (Empty ⊕ Fin n)) :
    @Term.realize Language.val (Transfer.VFType (M := M)) valStructVF (Empty ⊕ Fin n)
        (Sum.elim (default : Empty → Transfer.VFType (M := M)) (fun i => ⟨x i, hx i⟩)) t
      = ⟨Transfer.valTermEval x t, valTermEval_mem x hx t⟩ := by
  letI : Language.val.Structure (Transfer.VFType (M := M)) := valStructVF
  induction t with
  | var v =>
    rcases v with e | i
    · exact e.elim
    · rfl
  | func f args ih =>
    cases f with
    | add =>
      rw [Term.realize_func]
      show (Term.realize _ (args 0) + Term.realize _ (args 1) : Transfer.VFType (M := M)) = _
      rw [ih 0, ih 1]
      rfl
    | mul =>
      rw [Term.realize_func]
      show (Term.realize _ (args 0) * Term.realize _ (args 1) : Transfer.VFType (M := M)) = _
      rw [ih 0, ih 1]
      rfl
    | neg =>
      rw [Term.realize_func]
      show (- Term.realize _ (args 0) : Transfer.VFType (M := M)) = _
      rw [ih 0]
      rfl
    | zero => rw [Term.realize_func]; rfl
    | one => rw [Term.realize_func]; rfl

/-- **Atomic formulas are sort-independent** on `VF`-tuples. -/
theorem realize_atomic_iff {n : ℕ} {φ : Language.val.BoundedFormula Empty n} (hA : φ.IsAtomic)
    (x : Fin n → M) (hx : ∀ i, iVF (x i)) :
    (@BoundedFormula.Realize Language.val M (Transfer.valStructOfLRV M) Empty n φ
        (default : Empty → M) x)
      ↔ (@BoundedFormula.Realize Language.val (Transfer.VFType (M := M)) valStructVF Empty n φ
        (default : Empty → Transfer.VFType (M := M)) (fun i => ⟨x i, hx i⟩)) := by
  letI : Language.val.Structure M := Transfer.valStructOfLRV M
  letI : Language.val.Structure (Transfer.VFType (M := M)) := valStructVF
  induction hA with
  | equal t u =>
    show ((t =' u).Realize (default : Empty → M) x)
      ↔ ((t =' u).Realize (default : Empty → Transfer.VFType (M := M))
          (fun i => ⟨x i, hx i⟩))
    rw [BoundedFormula.realize_bdEqual, BoundedFormula.realize_bdEqual,
      Transfer.realize_valTermEval, Transfer.realize_valTermEval,
      realize_valTermEval_vf, realize_valTermEval_vf]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  | rel R ts =>
    cases R with
    | le =>
      show iLe (iRv ((ts 1).realize (Sum.elim (default : Empty → M) x)))
          (iRv ((ts 0).realize (Sum.elim (default : Empty → M) x)))
        ↔ iLe (iRv (Subtype.val ((ts 1).realize (Sum.elim
              (default : Empty → Transfer.VFType (M := M)) (fun i => ⟨x i, hx i⟩))
                : Transfer.VFType (M := M))))
            (iRv (Subtype.val ((ts 0).realize (Sum.elim
              (default : Empty → Transfer.VFType (M := M)) (fun i => ⟨x i, hx i⟩))
                : Transfer.VFType (M := M))))
      rw [Transfer.realize_valTermEval, Transfer.realize_valTermEval,
        realize_valTermEval_vf, realize_valTermEval_vf]

/-- **Quantifier-free formulas are sort-independent** on `VF`-tuples: they have the same truth
value in the whole-carrier `L_val`-structure and in the `L_val`-structure on `VF`. -/
theorem realize_QF_iff {n : ℕ} {φ : Language.val.BoundedFormula Empty n} (hQF : φ.IsQF)
    (x : Fin n → M) (hx : ∀ i, iVF (x i)) :
    (@BoundedFormula.Realize Language.val M (Transfer.valStructOfLRV M) Empty n φ
        (default : Empty → M) x)
      ↔ (@BoundedFormula.Realize Language.val (Transfer.VFType (M := M)) valStructVF Empty n φ
        (default : Empty → Transfer.VFType (M := M)) (fun i => ⟨x i, hx i⟩)) := by
  letI : Language.val.Structure M := Transfer.valStructOfLRV M
  letI : Language.val.Structure (Transfer.VFType (M := M)) := valStructVF
  induction hQF with
  | falsum => exact Iff.rfl
  | of_isAtomic hA => exact realize_atomic_iff hA x hx
  | imp φ ψ ihφ ihψ =>
    simp only [BoundedFormula.realize_imp]
    exact ⟨fun h ha' => ihψ.mp (h (ihφ.mpr ha')), fun h ha => ihψ.mpr (h (ihφ.mp ha))⟩

/-- The evaluator form of the same statement: a quantifier-free `L_val`-formula evaluated by
`valFormulaEval` at a `VF`-tuple agrees with its realisation in the `VF` sort. -/
theorem valFormulaEval_QF_iff {n : ℕ} {φ : Language.val.BoundedFormula Empty n} (hQF : φ.IsQF)
    (x : Fin n → M) (hx : ∀ i, iVF (x i)) :
    Transfer.valFormulaEval x φ
      ↔ (@BoundedFormula.Realize Language.val (Transfer.VFType (M := M)) valStructVF Empty n φ
        (default : Empty → Transfer.VFType (M := M)) (fun i => ⟨x i, hx i⟩)) :=
  (valFormulaEval_iff_realize φ x).symm.trans (realize_QF_iff hQF x hx)

/-! ## 4b. The sort-restricted evaluator and its agreement with the `VF` sort -/

/-- The sort-restricted evaluation of an `L_val`-formula in an `L_RV`-structure: the `VF`-sorted
symbols are `iVFAdd`, …, and quantifiers range over the `VF` sort only. -/
def valFormulaEvalS {M : Type} [LRV.Structure M] {n : ℕ} (x : Fin n → M) :
    Language.val.BoundedFormula Empty n → Prop
  | BoundedFormula.falsum => False
  | BoundedFormula.equal t u => Transfer.valTermEval x t = Transfer.valTermEval x u
  | BoundedFormula.rel r ts =>
    match r with
    | ValRel.le =>
      iLe (iRv (Transfer.valTermEval x (ts 1))) (iRv (Transfer.valTermEval x (ts 0)))
  | BoundedFormula.imp φ ψ => valFormulaEvalS x φ → valFormulaEvalS x ψ
  | BoundedFormula.all φ => ∀ a : M, iVF a → valFormulaEvalS (Fin.snoc x a) φ


/-- The same term lemma, phrased for a tuple of `VF`-elements (the form used below). -/
theorem realize_valTermEval_vf' {n : ℕ} (y : Fin n → Transfer.VFType (M := M))
    (t : Language.val.Term (Empty ⊕ Fin n)) :
    @Term.realize Language.val (Transfer.VFType (M := M)) valStructVF (Empty ⊕ Fin n)
        (Sum.elim (default : Empty → Transfer.VFType (M := M)) y) t
      = ⟨Transfer.valTermEval (fun i => (y i).1) t,
          valTermEval_mem (fun i => (y i).1) (fun i => (y i).2) t⟩ :=
  realize_valTermEval_vf (fun i => (y i).1) (fun i => (y i).2) t

/-- `Fin.snoc` on values, read through the projection to the carrier. -/
theorem snoc_val_eq {n : ℕ} (y : Fin n → Transfer.VFType (M := M))
    (a : Transfer.VFType (M := M)) :
    Fin.snoc (fun i => (y i).1) a.1
      = fun i => ((Fin.snoc (α := fun _ => Transfer.VFType (M := M)) y a) i).1 := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [Fin.snoc_last]
  · simp [Fin.snoc_castSucc]


theorem valFormulaEvalS_iff_realize {n : ℕ} (φ : Language.val.BoundedFormula Empty n)
    (y : Fin n → Transfer.VFType (M := M)) :
    valFormulaEvalS (fun i => (y i).1) φ
      ↔ (@BoundedFormula.Realize Language.val (Transfer.VFType (M := M)) valStructVF Empty n φ
        (default : Empty → Transfer.VFType (M := M)) y) := by
  letI : Language.val.Structure (Transfer.VFType (M := M)) := valStructVF
  induction φ with
  | falsum => exact Iff.rfl
  | equal t u =>
    show (Transfer.valTermEval (fun i => (y i).1) t = Transfer.valTermEval (fun i => (y i).1) u) ↔
      ((t =' u).Realize (default : Empty → Transfer.VFType (M := M)) y)
    rw [BoundedFormula.realize_bdEqual, realize_valTermEval_vf', realize_valTermEval_vf']
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  | rel r ts =>
    cases r with
    | le =>
      show iLe (iRv (Transfer.valTermEval (fun i => (y i).1) (ts 1)))
          (iRv (Transfer.valTermEval (fun i => (y i).1) (ts 0)))
        ↔ iLe (iRv (Subtype.val ((ts 1).realize (Sum.elim
              (default : Empty → Transfer.VFType (M := M)) y) : Transfer.VFType (M := M))))
            (iRv (Subtype.val ((ts 0).realize (Sum.elim
              (default : Empty → Transfer.VFType (M := M)) y) : Transfer.VFType (M := M))))
      rw [realize_valTermEval_vf', realize_valTermEval_vf']
  | imp φ ψ ihφ ihψ =>
    simp only [valFormulaEvalS, BoundedFormula.realize_imp]
    exact ⟨fun h ha' => (ihψ y).mp (h ((ihφ y).mpr ha')),
      fun h ha => (ihψ y).mpr (h ((ihφ y).mp ha))⟩
  | all φ ih =>
    simp only [valFormulaEvalS, BoundedFormula.realize_all]
    constructor
    · intro h a
      have h' : valFormulaEvalS
          (fun i => ((Fin.snoc (α := fun _ => Transfer.VFType (M := M)) y a) i).1) φ := by
        rw [← snoc_val_eq y a]
        exact h a.1 a.2
      exact (ih (Fin.snoc (α := fun _ => Transfer.VFType (M := M)) y a)).mp h'
    · intro h a ha
      rw [snoc_val_eq y ⟨a, ha⟩]
      exact (ih (Fin.snoc (α := fun _ => Transfer.VFType (M := M)) y ⟨a, ha⟩)).mpr (h ⟨a, ha⟩)


/-- The restricted-evaluator agreement in the form used in the transfer: at a `VF`-sorted tuple
`x` of the carrier. -/
theorem valFormulaEvalS_iff_realize_x {n : ℕ} (φ : Language.val.BoundedFormula Empty n)
    (x : Fin n → M) (hx : ∀ i, iVF (x i)) :
    valFormulaEvalS x φ
      ↔ (@BoundedFormula.Realize Language.val (Transfer.VFType (M := M)) valStructVF Empty n φ
        (default : Empty → Transfer.VFType (M := M)) (fun i => ⟨x i, hx i⟩)) := by
  have h := valFormulaEvalS_iff_realize φ (fun i => ⟨x i, hx i⟩)
  simpa using h

/-! ## 5. The QF half of the QE transfer

If two `L_val`-formulas are equivalent in `valStructVF` on `S = {x // iVF x}`, and both are
quantifier-free, then their `L_RV`-translates are equivalent in `M` at `VF`-tuples, and the
translate of the quantifier-free witness is quantifier-free.  This is the step that lets a
quantifier-free formula produced by `hasQE_ACVF_val` in `L_val` be read back in `L_RV`. -/

theorem qf_transfer {n : ℕ} {ψ ψ' : Language.val.BoundedFormula Empty n}
    (hψ : ψ.IsQF) (hψ' : ψ'.IsQF)
    (hS : ∀ y : Fin n → Transfer.VFType (M := M),
      (@BoundedFormula.Realize Language.val (Transfer.VFType (M := M)) valStructVF Empty n ψ
        (default : Empty → Transfer.VFType (M := M)) y)
      ↔ (@BoundedFormula.Realize Language.val (Transfer.VFType (M := M)) valStructVF Empty n ψ'
        (default : Empty → Transfer.VFType (M := M)) y))
    (x : Fin n → M) (hx : ∀ i, iVF (x i)) :
    (@BoundedFormula.Realize LRV M _ Empty n (Transfer.valFormulaToRV ψ) (default : Empty → M) x)
      ↔ (@BoundedFormula.Realize LRV M _ Empty n (Transfer.valFormulaToRV ψ')
        (default : Empty → M) x) := by
  rw [Transfer.valFormulaToRV_realize, Transfer.valFormulaToRV_realize]
  refine (valFormulaEval_QF_iff hψ x hx).trans ?_
  refine ((hS (fun i => ⟨x i, hx i⟩)).trans ?_)
  exact (valFormulaEval_QF_iff hψ' x hx).symm

/-- The same transfer, with the quantifier-freeness of the translated witness exposed. -/
theorem qf_transfer' {n : ℕ} {ψ ψ' : Language.val.BoundedFormula Empty n}
    (hψ : ψ.IsQF) (hψ' : ψ'.IsQF)
    (hS : ∀ y : Fin n → Transfer.VFType (M := M),
      (@BoundedFormula.Realize Language.val (Transfer.VFType (M := M)) valStructVF Empty n ψ
        (default : Empty → Transfer.VFType (M := M)) y)
      ↔ (@BoundedFormula.Realize Language.val (Transfer.VFType (M := M)) valStructVF Empty n ψ'
        (default : Empty → Transfer.VFType (M := M)) y)) :
    (Transfer.valFormulaToRV ψ').IsQF ∧
      ∀ (x : Fin n → M), (∀ i, iVF (x i)) →
        ((@BoundedFormula.Realize LRV M _ Empty n (Transfer.valFormulaToRV ψ)
            (default : Empty → M) x)
          ↔ (@BoundedFormula.Realize LRV M _ Empty n (Transfer.valFormulaToRV ψ')
            (default : Empty → M) x)) :=
  ⟨isQF_valFormulaToRV hψ', fun x hx => qf_transfer hψ hψ' hS x hx⟩

end VFStruct

/-! ## Axiom checks -/

#print axioms Smw14elno.M3.isQF_valFormulaToRV
#print axioms Smw14elno.M3.valFormulaEval_iff_realize
#print axioms Smw14elno.M3.realize_QF_iff
#print axioms Smw14elno.M3.valFormulaEval_QF_iff
#print axioms Smw14elno.M3.valFormulaEvalS_iff_realize
#print axioms Smw14elno.M3.qf_transfer
#print axioms Smw14elno.M3.qf_transfer'

end Smw14elno.M3

#print axioms SpecialTransformations.Milestone0.Transfer.valTermToRV_realize

#print axioms SpecialTransformations.Milestone0.Transfer.valFormulaToRV_realize

#print axioms SpecialTransformations.Milestone0.Transfer.sortedHyps_realize
#print axioms SpecialTransformations.Milestone0.Transfer.allSorted_realize

#print axioms SpecialTransformations.Milestone0.Transfer.vfFieldOfModel

#print axioms SpecialTransformations.Milestone0.Transfer.le_refl
#print axioms SpecialTransformations.Milestone0.Transfer.le_trans
#print axioms SpecialTransformations.Milestone0.Transfer.le_total
#print axioms SpecialTransformations.Milestone0.Transfer.le_top
#print axioms SpecialTransformations.Milestone0.Transfer.le_infty_eq
#print axioms SpecialTransformations.Milestone0.Transfer.rv_zero_eq
#print axioms SpecialTransformations.Milestone0.Transfer.rv_eq_infty
#print axioms SpecialTransformations.Milestone0.Transfer.rv_mul_hom
#print axioms SpecialTransformations.Milestone0.Transfer.rv_ultrametric

#print axioms SpecialTransformations.Milestone0.Transfer.rv_mem
#print axioms SpecialTransformations.Milestone0.Transfer.le_self
#print axioms SpecialTransformations.Milestone0.Transfer.predV_refl
#print axioms SpecialTransformations.Milestone0.Transfer.predV_trans
#print axioms SpecialTransformations.Milestone0.Transfer.predV_zero_le
#print axioms SpecialTransformations.Milestone0.Transfer.predV_zero_eq
#print axioms SpecialTransformations.Milestone0.Transfer.predV_ultra
#print axioms SpecialTransformations.Milestone0.Transfer.predV_total

#print axioms SpecialTransformations.Milestone0.Transfer.paperScale_iff_vfPred_scale
#print axioms SpecialTransformations.Milestone0.Transfer.valField_model_of_PaperScale
#print axioms SpecialTransformations.Milestone0.Transfer.model_ACVF_val_of_axioms
#print axioms VFAlgClosed.isAlgClosed_vfType
#print axioms VFPack.model_ACVF_val
#print axioms VFRestrict.valFormulaToRVvf_realize
#print axioms VFRestrict.transfer_of_isQF
#print axioms Smw14elno.M3.isQF_valFormulaToRV
#print axioms Smw14elno.M3.qf_transfer

namespace SpecialTransformations.Milestone0.Transfer

set_option linter.style.haveILetI false

/-- Definition 2.2 item 5 in full: `≤` on `RV` is invariant under multiplication by **every**
nonzero `RV`-element, in the iff form (the frozen `Axioms.leMulCompat` has `pUnits` — the class
of `1` — in place of `pRV`, which only covers the identity class of `Γ`). -/
def leMulCompatFull : LRV.Sentence :=
  allSorted ![.rv, .rv, .rv]
    (pRV &2 ⟹ (pLe &0 &1 ⇔ pLe (tRVMul &0 &2) (tRVMul &1 &2)))

/-- **The repaired theory**: the frozen `ACVF` with item 5 stated in full. -/
def ACVFplus : LRV.Theory := Axioms.ACVF ∪ {leMulCompatFull}

theorem mem_ACVFplus_leMulCompatFull : leMulCompatFull ∈ ACVFplus := by
  simp [ACVFplus]

/-- The repaired theory is stronger than the frozen one. -/
theorem model_ACVF_of_model_ACVFplus {M : Type} [LRV.Structure M] (hM : M ⊨ ACVFplus) :
    M ⊨ Axioms.ACVF :=
  ⟨fun φ hφ => hM.realize_of_mem φ (Or.inl hφ)⟩

/-- **The semantic form of the repaired axiom.** -/
theorem le_mul_compat_full {M : Type} [LRV.Structure M] (hM : M ⊨ ACVFplus) {a b c : M}
    (ha : iRV a) (hb : iRV b) (hc : iRV c) (h0 : c ≠ iRVZero) :
    iLe a b ↔ iLe (iRVMul a c) (iRVMul b c) := by
  have h := allSorted_realize (T := ACVFplus) hM mem_ACVFplus_leMulCompatFull ![a, b, c]
    (by intro i; fin_cases i <;> simp [ha, hb, hc])
  have h' : c ≠ iRVZero → (iLe a b ↔ iLe (iRVMul a c) (iRVMul b c)) := by
    simpa [pRV_realize, realize_pLe, realize_tRVMul] using h
  exact h' h0

/-- **The repaired theory implies the paper's item 5** in the form the transfer uses. -/
theorem paperScale_of_model_ACVFplus {M : Type} [LRV.Structure M] (hM : M ⊨ ACVFplus) :
    PaperScale M :=
  fun _a _b _c ha hb hc h0 => le_mul_compat_full hM ha hb hc h0

/-- **The extraction, from the repaired theory**: the `VF` sort of a nontrivially valued model of
`ACVFplus` models `ValPM.ACVF_val`. -/
theorem model_ACVF_val_of_model_ACVFplus {M : Type} [LRV.Structure M] (hM : M ⊨ ACVFplus)
    (hnontriv : HasNontrivVal M) :
    @Theory.Model Language.val (VFType (M := M)) (vfValStruct (hM := model_ACVF_of_model_ACVFplus hM))
      ValPM.ACVF_val := by
  letI hA : M ⊨ Axioms.ACVF := model_ACVF_of_model_ACVFplus hM
  exact model_ACVF_val_of_axioms (M := M)
    (fun x => predV_refl hA x) (fun x y z h1 h2 => predV_trans hA h1 h2)
    (fun x => predV_zero_le hA x) (fun x h => predV_zero_eq hA h)
    (fun x y => predV_ultra hA x y) (fun x y => predV_total hA x y)
    (paperScale_of_model_ACVFplus hM) (VFAlgClosed.isAlgClosed_vfType (M := M)) hnontriv

end SpecialTransformations.Milestone0.Transfer

#print axioms SpecialTransformations.Milestone0.Transfer.le_mul_compat_full
#print axioms SpecialTransformations.Milestone0.Transfer.paperScale_of_model_ACVFplus
#print axioms SpecialTransformations.Milestone0.Transfer.model_ACVF_val_of_model_ACVFplus

/-
Direction **d5** of swarm `smw1541fr`: the *trivial-valuation case* of the frozen `L_RV`
encoding (`SpecialTransformations.Milestone0.Axioms.ACVF`).

WHAT IS PROVED HERE (all green, `import Pre`, no `sorry`, no `axiom`, no `native_decide`,
footprints ⊆ {propext, Classical.choice, Quot.sound}; all statements are about an arbitrary
`M` with `[LRV.Structure M]` and `hM : M ⊨ Axioms.ACVF`).

**1. The coarse case is empty** (§9).  With
`TrivVal M : ∀ x, iVF x → x = iVFZero ∨ iRv x = iRv iVFOne` (`rv` constant on `VF ∖ {0}`):

* `TrivCase.no_coarse_triv (hM) (hT : TrivVal M) : False`,
* `TrivCase.exists_rv_ne_one (hM) : ∃ x, iVF x ∧ x ≠ 0 ∧ iRv x ≠ iRv 1`.

Reason: `TrivVal` + `rvSurj` give `RV = {∞, 1}` (`rv_mem_two`), so `K = pInK ⊆ RV` has at most
two elements, but `kAlgClosed` at degree 2 needs a root of `x² + a₁x + a₀` in `K` for all
`a₀, a₁ ∈ K`, and at `a₀ = a₁ = 1` both candidates `∞` and `1` evaluate to `1 ≠ ∞`
(`kAdd_one_one : 1 + 1 = 0`, from `kNeg_one` and `kAdd_neg`).  So the "trivially valued" case
of `QE-PLAN.md` must be read as *order-trivial with `rv` injective*, not as `rv` constant.

**2. The fine case: dictionary and `RV`-quantifier elimination** (§10).
`FineTriv M` bundles: `rv` injective on `VF`, the order trivial (`v x ≤ v y ↔ x ≠ 0 ∨ y = 0`),
`Kˣ = VF ∖ {0}`, the residue `+`, `-` and `1` matching the field's along `rv`.  Under it:

* `fine_rv_eq : iRv x = iRv y ↔ x = y`;
* `fine_dictionary`: the `L_RV`-atoms `rv x = rv y`, `rv x ≤ rv y`, `iUnits (rv x)`,
  `rv x + rv y = rv (x+y)`, `-rv x = rv (-x)`, `rv x · rv y = rv (xy)` are all quantifier-free
  conditions in the *field* language of `VF`;
* `rv_exists_vf : (∃ a, iRV a ∧ ψ a) ↔ ψ ∞ ∨ ∃ x (VF), x ≠ 0 ∧ ψ (rv x)` — the elimination of
  `RV`-quantifiers that the cover of `e1` needs on the trivial side (it uses only `rvSurj`).

What does **not** follow, and why (documented at `fine_dictionary`): terms of the form
`iVFAdd (rv s) (rv t)`, `iVFNeg (rv s)`, `iVFMul (rv s) (rv t)` — the `VF` operations applied to
`RV`-elements — are *junk*, constrained by no axiom.  So no quantifier-free translation of an
arbitrary `L_RV`-formula can exist in the trivial case without an extra junk hypothesis (or
the repaired encoding), independently of the residue-field question.

**3. Also unconditional** (true in every model, useful to d1/d2):
`units_ne_infty : ¬ iUnits iRVZero` (`rvMulInv` at `∞` + `rvMulInfty` force `1 = ∞`),
`rvZero_ne_rvOne`, `iRV_of_inK`, `kAdd_zero_left/right`, `kAdd_comm`, `kAdd_neg`, `kMul_one`,
`kHyps_realize`, `allSortedK_realize` (extraction from `allSortedK`-guarded axioms, which the
tree did not have), `exSortedK_realize`, and simp lemmas for `tKAdd`, `tKNeg`, `tRVOne`, `tv`.

**4. The coarse-case dictionary is kept** (§4–§8) as the proof of the refutation: under
`TrivVal` one gets `rv 1 = 1`, `rv x = rv y ↔ x = y ∨ (x ≠ 0 ∧ y ≠ 0)`,
`iLe (rv x) (rv y) ↔ x ≠ 0 ∨ y = 0`, `iUnits (rv x) ↔ x ≠ 0`, the residue tables on `{∞, 1}`
and `rv_exists_two` (every `RV`-quantifier is a two-term disjunction).  These are conditional
theorems about an inconsistent hypothesis; §9 is what makes the inconsistency explicit.
-/

open FirstOrder FirstOrder.Language
open scoped FirstOrder
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.Transfer LRV Axioms

namespace TrivCase

variable {M : Type} [LRV.Structure M]

/-- The interpretation of the unary residue-field `-`; the frozen encoding has no such
definition (only `iKAdd`, `iRVMul`), so we add it here. -/
def iKNeg (x : M) : M := FirstOrder.Language.Structure.funMap (L := LRV) Fn.kNeg ![x]

/-! ## 0. Realization of the `RV`-sorted term constructors not in the tree -/

theorem realize_tKAdd {n : ℕ} (v : Empty ⊕ Fin n → M) (a b : Tm n) :
    (tKAdd a b).realize v = iKAdd (a.realize v) (b.realize v) := by
  show FirstOrder.Language.Structure.funMap (L := LRV) Fn.kAdd
      (fun i => Term.realize (L := LRV) v (![a, b] i)) = iKAdd (a.realize v) (b.realize v)
  rw [show (fun i => Term.realize (L := LRV) v (![a, b] i)) = ![a.realize v, b.realize v]
    from by funext i; fin_cases i <;> simp]
  rfl

theorem realize_tKNeg {n : ℕ} (v : Empty ⊕ Fin n → M) (a : Tm n) :
    (tKNeg a).realize v = iKNeg (a.realize v) := by
  show FirstOrder.Language.Structure.funMap (L := LRV) Fn.kNeg
      (fun i => Term.realize (L := LRV) v (![a] i)) = iKNeg (a.realize v)
  rw [show (fun i => Term.realize (L := LRV) v (![a] i)) = ![a.realize v]
    from by funext i; fin_cases i; simp]
  rfl

theorem realize_tRVOne {n : ℕ} (v : Empty ⊕ Fin n → M) :
    (tRVOne (n := n)).realize v = iRVOne := by
  show FirstOrder.Language.Structure.funMap (L := LRV) Fn.rvOne
      (fun i => Term.realize (L := LRV) v ((fun j : Fin 0 => j.elim0) i)) = iRVOne
  rw [show (fun i => Term.realize (L := LRV) v ((fun j : Fin 0 => j.elim0) i))
      = (fun i => i.elim0) from by funext i; exact i.elim0]
  rfl

/-- A `simp`-friendly form of `Transfer.realize_tv` with the index given as a numeral. -/
@[simp] theorem realize_tv_nat {n : ℕ} (i : ℕ) (h : i < n) (v : Empty → M) (x : Fin n → M) :
    (tv i h).realize (Sum.elim v x) = x ⟨i, h⟩ := rfl

/-! ## 1. `pInK`, `kHyps` and the `allSortedK` extraction -/

theorem pInK_realize {k : ℕ} (t : Tm k) (v : Empty → M) (x : Fin k → M) :
    (pInK t).Realize v x ↔
      iUnits (t.realize (Sum.elim v x)) ∨ t.realize (Sum.elim v x) = iRVZero := by
  simp only [pInK, BoundedFormula.realize_sup, pUnits_realize, pEq,
    BoundedFormula.realize_bdEqual, realize_tRVZero]

theorem kHyps_foldr_realize {k : ℕ} (l : List (Fin k)) (v : Empty → M) (x : Fin k → M) :
    (l.foldr (fun i acc => pInK (tv i.1 i.2) ⊓ acc) ⊤).Realize v x ↔
      ∀ i ∈ l, iUnits (x i) ∨ x i = iRVZero := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.foldr_cons, BoundedFormula.realize_inf, ih, pInK_realize, realize_tv]
    constructor
    · rintro ⟨ha, hall⟩ i hi
      rcases List.mem_cons.mp hi with rfl | hi
      · exact ha
      · exact hall i hi
    · intro h
      exact ⟨h a List.mem_cons_self, fun i hi => h i (List.mem_cons_of_mem a hi)⟩

theorem kHyps_realize {k : ℕ} (v : Empty → M) (x : Fin k → M) :
    (kHyps (k := k)).Realize v x ↔ ∀ i, iUnits (x i) ∨ x i = iRVZero := by
  rw [kHyps, kHyps_foldr_realize]
  constructor
  · intro h i
    exact h i (List.mem_finRange i)
  · intro h i _
    exact h i

/-- **Uniform extraction from an `allSortedK`-guarded sentence.** -/
theorem allSortedK_realize {T : LRV.Theory} (hM : M ⊨ T)
    {k : ℕ} {ss : Fin k → SortTag} {φ : Bf k} (hmem : allSortedK ss φ ∈ T) :
    ∀ (x : Fin k → M), (∀ i, (match ss i with
        | .vf => iVF (x i)
        | .rv => iRV (x i)))
      → (∀ i, iUnits (x i) ∨ x i = iRVZero)
      → @BoundedFormula.Realize LRV M _ Empty k φ (default : Empty → M) x := by
  intro x hx hK
  have h := hM.realize_of_mem (allSortedK ss φ) hmem
  simp only [allSortedK, Sentence.Realize, BoundedFormula.realize_alls,
    BoundedFormula.realize_imp, BoundedFormula.realize_inf] at h
  exact h x ⟨(sortedHyps_realize ss (default : Empty → M) x).mpr hx,
    (kHyps_realize (default : Empty → M) x).mpr hK⟩

/-! ## 2. Membership of the axioms used below, and the constants -/

theorem mem_ACVF_sdRVZero : Axioms.sdRVZero ∈ Axioms.ACVF :=
  mem_ACVF_sortClosure (by simp [Axioms.sortClosure, Axioms.ofList])

theorem mem_ACVF_sdRVOne : Axioms.sdRVOne ∈ Axioms.ACVF :=
  mem_ACVF_sortClosure (by simp [Axioms.sortClosure, Axioms.ofList])

theorem mem_ACVF_sdUnits : Axioms.sdUnits ∈ Axioms.ACVF :=
  mem_ACVF_sortClosure (by simp [Axioms.sortClosure, Axioms.ofList])

theorem mem_ACVF_sdKAdd : Axioms.sdKAdd ∈ Axioms.ACVF :=
  mem_ACVF_sortClosure (by simp [Axioms.sortClosure, Axioms.ofList])

theorem mem_ACVF_sdKNeg : Axioms.sdKNeg ∈ Axioms.ACVF :=
  mem_ACVF_sortClosure (by simp [Axioms.sortClosure, Axioms.ofList])

theorem mem_ACVF_kField {s : LRV.Sentence} (h : s ∈ Axioms.kField) : s ∈ Axioms.ACVF := by
  simp only [Axioms.ACVF, Axioms.ACVFpaper, Set.mem_union] at *
  tauto

theorem mem_ACVF_rvGroup {s : LRV.Sentence} (h : s ∈ Axioms.rvGroup) : s ∈ Axioms.ACVF := by
  simp only [Axioms.ACVF, Axioms.ACVFpaper, Set.mem_union] at *
  tauto

theorem mem_ACVF_rvOneMem : Axioms.rvOneMem ∈ Axioms.ACVF :=
  mem_ACVF_rvGroup (by simp [Axioms.rvGroup, Axioms.ofList])

theorem mem_ACVF_rvMulOne : Axioms.rvMulOne ∈ Axioms.ACVF :=
  mem_ACVF_rvGroup (by simp [Axioms.rvGroup, Axioms.ofList])

theorem mem_ACVF_rvMulInv : Axioms.rvMulInv ∈ Axioms.ACVF :=
  mem_ACVF_rvGroup (by simp [Axioms.rvGroup, Axioms.ofList])

theorem mem_ACVF_rvMulInfty : Axioms.rvMulInfty ∈ Axioms.ACVF :=
  mem_ACVF_rvGroup (by simp [Axioms.rvGroup, Axioms.ofList])

theorem mem_ACVF_rvSurj : Axioms.rvSurj ∈ Axioms.ACVF :=
  mem_ACVF_rvAxioms (by simp [Axioms.rvAxioms, Axioms.ofList])

/-- **`rv` is surjective onto `RV ∖ {∞}`** (the frozen axiom `Axioms.rvSurj`), extracted. -/
theorem rv_surj (hM : M ⊨ Axioms.ACVF) {a : M} (ha : iRV a) (ha0 : a ≠ iRVZero) :
    ∃ x : M, iVF x ∧ iRv x = a := by
  have h := allSorted_realize hM mem_ACVF_rvSurj ![a] (by
    intro i; fin_cases i; simpa using ha)
  simp only [Axioms.rvSurj, BoundedFormula.realize_imp, BoundedFormula.realize_not, pEq,
    BoundedFormula.realize_bdEqual, realize_tRVZero, exSorted, BoundedFormula.realize_ex,
    BoundedFormula.realize_inf, sortPred, pVF_realize, realize_tRv, realize_tv,
    Term.realize_var, Sum.elim_inr, Function.comp_apply, Fin.snoc_last, Fin.snoc_castSucc,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h
  exact h ha0

/-- The two `RV` constants are distinct (`kField`'s `0 ≠ 1`). -/
theorem rvZero_ne_rvOne (hM : M ⊨ Axioms.ACVF) : iRVZero (M := M) ≠ iRVOne := by
  have hmem : (∼(pEq (tRVZero (n := 0)) tRVOne)) ∈ Axioms.ACVF :=
    mem_ACVF_kField (by simp [Axioms.kField, Axioms.ofList])
  have h := sentence_realize hM hmem
  rw [Sentence.Realize] at h
  simpa only [Formula.Realize, pEq, BoundedFormula.realize_not, BoundedFormula.realize_bdEqual,
    realize_tRVZero, realize_tRVOne] using h

/-- `1` of the `RV` sort lies in `RV`. -/
theorem iRV_rvOne (hM : M ⊨ Axioms.ACVF) : iRV (iRVOne (M := M)) := by
  have h := sentence_realize hM mem_ACVF_sdRVOne
  rw [Sentence.Realize] at h
  simpa only [Axioms.sdRVOne, Formula.Realize, pRVsort_realize, realize_tRVOne] using h

/-- `0 = ∞` of the `RV` sort lies in `RV`. -/
theorem iRV_rvZero (hM : M ⊨ Axioms.ACVF) : iRV (iRVZero (M := M)) := by
  have h := sentence_realize hM mem_ACVF_sdRVZero
  rw [Sentence.Realize] at h
  simpa only [Axioms.sdRVZero, Formula.Realize, pRVsort_realize, realize_tRVZero] using h

/-- `1` of the `RV` sort satisfies the unit predicate `Kˣ` (`rvOneMem`). -/
theorem iUnits_rvOne (hM : M ⊨ Axioms.ACVF) : iUnits (iRVOne (M := M)) := by
  have h := sentence_realize hM mem_ACVF_rvOneMem
  rw [Sentence.Realize] at h
  simpa only [Axioms.rvOneMem, Formula.Realize, pUnits_realize, realize_tRVOne] using h

/-- `Kˣ` is contained in the `RV` sort (`sdUnits`). -/
theorem rv_of_units (hM : M ⊨ Axioms.ACVF) {a : M} (ha : iUnits a) : iRV a := by
  have h := sentence_realize hM mem_ACVF_sdUnits
  rw [Sentence.Realize] at h
  simp only [Axioms.sdUnits, allOne, BoundedFormula.realize_alls] at h
  have h2 := h ![a]
  simp only [BoundedFormula.realize_imp, pUnits_realize, pRVsort_realize] at h2
  simp at h2
  exact h2 ha

/-- every element of `K = Kˣ ∪ {0}` is an `RV`-element. -/
theorem iRV_of_inK (hM : M ⊨ Axioms.ACVF) {a : M} (ha : iUnits a ∨ a = iRVZero) : iRV a := by
  rcases ha with h | h
  · exact rv_of_units hM h
  · rw [h]; exact iRV_rvZero hM

/-- `K` is closed under `+` (`sdKAdd`): the `pInK` predicate is preserved. -/
theorem inK_kAdd (hM : M ⊨ Axioms.ACVF) {a b : M}
    (ha : iUnits a ∨ a = iRVZero) (hb : iUnits b ∨ b = iRVZero) :
    iUnits (iKAdd a b) ∨ iKAdd a b = iRVZero := by
  have h := allSorted_realize hM mem_ACVF_sdKAdd ![a, b] (by
    intro i
    fin_cases i
    · simpa using iRV_of_inK hM ha
    · simpa using iRV_of_inK hM hb)
  simp only [Axioms.sdKAdd, BoundedFormula.realize_imp, pInK_realize, realize_tKAdd,
    realize_tv, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  exact h ha hb

/-- `K` is closed under unary `-` (`sdKNeg`). -/
theorem inK_kNeg (hM : M ⊨ Axioms.ACVF) {a : M} (ha : iUnits a ∨ a = iRVZero) :
    iUnits (iKNeg a) ∨ iKNeg a = iRVZero := by
  have h := allSorted_realize hM mem_ACVF_sdKNeg ![a] (by
    intro i
    fin_cases i
    simpa using iRV_of_inK hM ha)
  simp only [Axioms.sdKNeg, BoundedFormula.realize_imp, pInK_realize, realize_tKNeg,
    realize_tv, Matrix.cons_val_zero] at h
  exact h ha

/-- `∞` is not a unit: `rvMulInv` at `∞` would force `1 = ∞` by absorption
(`rvMulInfty`).  This is an **unconditional** fact: it holds in every model of `Axioms.ACVF`,
with or without a trivial valuation. -/
theorem units_ne_infty (hM : M ⊨ Axioms.ACVF) : ¬ iUnits (iRVZero (M := M)) := by
  intro h0
  have hinv := allSorted_realize hM mem_ACVF_rvMulInv ![iRVZero] (by
    intro i; fin_cases i; simpa using iRV_rvZero hM)
  simp only [Axioms.rvMulInv, BoundedFormula.realize_imp, pUnits_realize,
    BoundedFormula.realize_ex, exSorted, BoundedFormula.realize_inf, sortPred,
    pRVsort_realize, pVF_realize, pEq, BoundedFormula.realize_bdEqual, realize_tRVMul,
    realize_tRVOne, realize_tv, Term.realize_var, Sum.elim_inr, Function.comp_apply,
    Fin.snoc_last, Fin.snoc_castSucc, Nat.succ_eq_add_one, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons] at hinv
  obtain ⟨y, -, hunit, hmul⟩ := hinv h0
  have hinf := allSorted_realize hM mem_ACVF_rvMulInfty ![y] (by
    intro i; fin_cases i; simpa using rv_of_units hM hunit)
  simp only [Axioms.rvMulInfty, pEq, BoundedFormula.realize_bdEqual, realize_tRVMul,
    tRVInfty, realize_tRVZero, realize_tv] at hinf
  simp at hinf
  exact rvZero_ne_rvOne hM (hinf.symm.trans hmul)

/-! ## 3. The `kField` laws at `K`, and `rvGroup`'s multiplicative laws -/

/-- `0` is neutral for `+` in `K`. -/
theorem kAdd_zero_right (hM : M ⊨ Axioms.ACVF) {a : M} (ha : iUnits a ∨ a = iRVZero) :
    iKAdd a iRVZero = a := by
  have hmem : allSortedK ![.rv] (pEq (tKAdd (&0 : Tm 1) tRVZero) (&0 : Tm 1)) ∈ Axioms.ACVF :=
    mem_ACVF_kField (by simp [Axioms.kField, Axioms.ofList])
  have h := allSortedK_realize hM hmem ![a]
    (by intro i; fin_cases i; exact iRV_of_inK hM ha)
    (by intro i; fin_cases i; exact ha)
  simp only [pEq, BoundedFormula.realize_bdEqual, realize_tKAdd, realize_tRVZero,
    realize_tv, Matrix.cons_val_zero] at h
  simpa using h

/-- Additive inverses in `K`. -/
theorem kAdd_neg (hM : M ⊨ Axioms.ACVF) {a : M} (ha : iUnits a ∨ a = iRVZero) :
    iKAdd a (iKNeg a) = iRVZero := by
  have hmem : allSortedK ![.rv]
      (pEq (tKAdd (&0 : Tm 1) (tKNeg (&0 : Tm 1))) tRVZero) ∈ Axioms.ACVF :=
    mem_ACVF_kField (by simp [Axioms.kField, Axioms.ofList])
  have h := allSortedK_realize hM hmem ![a]
    (by intro i; fin_cases i; exact iRV_of_inK hM ha)
    (by intro i; fin_cases i; exact ha)
  simp only [pEq, BoundedFormula.realize_bdEqual, realize_tKAdd, realize_tKNeg,
    realize_tRVZero, realize_tv, Matrix.cons_val_zero] at h
  simpa using h

/-- `1` is neutral for `×` in `K`. -/
theorem kMul_one (hM : M ⊨ Axioms.ACVF) {a : M} (ha : iUnits a ∨ a = iRVZero) :
    iRVMul a iRVOne = a := by
  have hmem : allSortedK ![.rv] (pEq (tRVMul (&0 : Tm 1) tRVOne) (&0 : Tm 1)) ∈ Axioms.ACVF :=
    mem_ACVF_kField (by simp [Axioms.kField, Axioms.ofList])
  have h := allSortedK_realize hM hmem ![a]
    (by intro i; fin_cases i; exact iRV_of_inK hM ha)
    (by intro i; fin_cases i; exact ha)
  simp only [pEq, BoundedFormula.realize_bdEqual, realize_tRVMul, realize_tRVOne,
    realize_tv, Matrix.cons_val_zero] at h
  simpa using h

/-- `1` is neutral for `×` on the units (`rvMulOne`). -/
theorem rvMul_one_of_units (hM : M ⊨ Axioms.ACVF) {a : M} (ha : iUnits a) :
    iRVMul iRVOne a = a := by
  have h := allSorted_realize hM mem_ACVF_rvMulOne ![a] (by
    intro i; fin_cases i; simpa using rv_of_units hM ha)
  simp only [Axioms.rvMulOne, BoundedFormula.realize_imp, pUnits_realize, pEq,
    BoundedFormula.realize_bdEqual, realize_tRVMul, realize_tRVOne, realize_tv,
    Matrix.cons_val_zero] at h
  exact h ha

/-- `∞` absorbs `×` (`rvMulInfty`). -/
theorem rvMul_infty (hM : M ⊨ Axioms.ACVF) {a : M} (ha : iRV a) :
    iRVMul a iRVZero = iRVZero := by
  have h := allSorted_realize hM mem_ACVF_rvMulInfty ![a] (by
    intro i; fin_cases i; simpa using ha)
  simp only [Axioms.rvMulInfty, pEq, BoundedFormula.realize_bdEqual, realize_tRVMul,
    tRVInfty, realize_tRVZero, realize_tv, Matrix.cons_val_zero] at h
  simpa using h

/-! ## 4. The triviality hypothesis and the dictionary it forces -/

/-- **Trivial valuation, coarse form**: every nonzero `VF`-element has the same value, namely
`rv 1`.  (This is the elementary form of `Γ = 1` together with the collapse of the residue map;
`Axioms.ACVF` admits such models, e.g. the trivially valued structure on an algebraically closed
field of residue characteristic `2`, see `QE-PLAN.md`.) -/
def TrivVal (M : Type) [LRV.Structure M] : Prop :=
  ∀ x : M, iVF x → x = iVFZero (M := M) ∨ iRv x = iRv iVFOne

/-- **`rv 1 = 1`**: under a trivial valuation the two one-constants are identified. -/
theorem rv_one_eq (hM : M ⊨ Axioms.ACVF) (hT : TrivVal M) :
    iRv (iVFOne (M := M)) = iRVOne := by
  obtain ⟨x, hxVF, hx⟩ := rv_surj hM (iRV_rvOne hM) (fun h => rvZero_ne_rvOne hM h.symm)
  rcases hT x hxVF with h | h
  · rw [h, rv_zero_eq hM] at hx
    exact absurd hx.symm (fun h => rvZero_ne_rvOne hM h.symm)
  · exact h.symm.trans hx

/-- Under a trivial valuation every nonzero `VF`-element has value `1`. -/
theorem rv_val_one (hM : M ⊨ Axioms.ACVF) (hT : TrivVal M) {x : M} (hx : iVF x)
    (hx0 : x ≠ iVFZero) : iRv x = iRVOne := by
  rcases hT x hx with h | h
  · exact absurd h hx0
  · rw [h, rv_one_eq hM hT]

/-- `rv x = ∞ ↔ x = 0` (unconditional). -/
theorem rv_eq_inf_iff (hM : M ⊨ Axioms.ACVF) {x : M} (hx : iVF x) :
    iRv x = iRVZero ↔ x = iVFZero :=
  ⟨rv_eq_infty hM hx, fun h => by rw [h]; exact rv_zero_eq hM⟩

/-- **When is `rv` injective?**  Under a trivial valuation it is injective off `0`, and it
identifies exactly the two nonzero elements: `rv x = rv y ↔ x = y ∨ (x ≠ 0 ∧ y ≠ 0)`. -/
theorem rv_eq_iff (hM : M ⊨ Axioms.ACVF) (hT : TrivVal M) {x y : M} (hx : iVF x) (hy : iVF y) :
    iRv x = iRv y ↔ x = y ∨ (x ≠ iVFZero ∧ y ≠ iVFZero) := by
  constructor
  · intro h
    by_cases hx0 : x = iVFZero
    · left
      have h1 : iRv y = iRVZero := by rw [← h, hx0]; exact rv_zero_eq hM
      rw [hx0, (rv_eq_inf_iff hM hy).mp h1]
    · right
      refine ⟨hx0, ?_⟩
      by_contra hy0
      rw [hy0, rv_zero_eq hM] at h
      exact hx0 ((rv_eq_inf_iff hM hx).mp h)
  · rintro (rfl | ⟨hx0, hy0⟩)
    · rfl
    · rw [rv_val_one hM hT hx hx0, rv_val_one hM hT hy hy0]

/-- **The valuation order is trivial**: `v x ≤ v y ↔ x ≠ 0 ∨ y = 0`. -/
theorem le_rv_iff (hM : M ⊨ Axioms.ACVF) (hT : TrivVal M) {x y : M} (hx : iVF x) (hy : iVF y) :
    iLe (iRv x) (iRv y) ↔ x ≠ iVFZero ∨ y = iVFZero := by
  have hx' : iRV (iRv x) := rv_mem hM hx
  have hy' : iRV (iRv y) := rv_mem hM hy
  constructor
  · intro h
    by_cases hx0 : x = iVFZero
    · right
      by_contra hy0
      have hy0' : iRv y ≠ iRVZero := fun hh => hy0 ((rv_eq_inf_iff hM hy).mp hh)
      have h' : iLe iRVZero (iRv y) := by rw [← rv_zero_eq hM, ← hx0]; exact h
      exact hy0' (le_infty_eq hM _ hy' hy0' h')
    · exact Or.inl hx0
  · rintro (hx0 | hy0)
    · rw [rv_val_one hM hT hx hx0]
      by_cases hy0 : y = iVFZero
      · rw [hy0, rv_zero_eq hM]
        exact le_top' hM (by rw [← rv_one_eq hM hT]; exact rv_mem hM (vf_one_mem hM))
      · rw [rv_val_one hM hT hy hy0]
        exact Transfer.le_refl hM iRVOne (iRV_rvOne hM) (fun h => rvZero_ne_rvOne hM h.symm)
    · rw [hy0, rv_zero_eq hM]
      exact le_top' hM hx'

/-- **The units are the nonzero `VF`-elements**: `iUnits (rv x) ↔ x ≠ 0`. -/
theorem units_rv_iff (hM : M ⊨ Axioms.ACVF) (hT : TrivVal M) {x : M} (hx : iVF x) :
    iUnits (iRv x) ↔ x ≠ iVFZero := by
  constructor
  · intro h hx0
    rw [hx0, rv_zero_eq hM] at h
    exact units_ne_infty hM h
  · intro hx0
    rw [rv_val_one hM hT hx hx0]
    exact iUnits_rvOne hM

/-- **`RV` has two elements**: under a trivial valuation every `RV`-element is `∞ = rv 0` or
`1 = rv 1`.  So `RV` is a *definitional* two-element expansion of the field on `VF`. -/
theorem rv_mem_two (hM : M ⊨ Axioms.ACVF) (hT : TrivVal M) {a : M} (ha : iRV a) :
    a = iRVZero ∨ a = iRVOne := by
  by_cases h0 : a = iRVZero
  · exact Or.inl h0
  · obtain ⟨x, hxVF, hx⟩ := rv_surj hM ha h0
    rcases hT x hxVF with h | h
    · exact Or.inl (by rw [← hx, h, rv_zero_eq hM])
    · exact Or.inr (by rw [← hx, h, rv_one_eq hM hT])

/-! ## 5. The residue-field tables on `{∞, 1}` -/

/-- `+` in `K` is commutative (`kField`). -/
theorem kAdd_comm (hM : M ⊨ Axioms.ACVF) {a b : M}
    (ha : iUnits a ∨ a = iRVZero) (hb : iUnits b ∨ b = iRVZero) :
    iKAdd a b = iKAdd b a := by
  have hmem : allSortedK ![.rv, .rv] (pEq (tKAdd (&0 : Tm 2) &1) (tKAdd &1 &0)) ∈ Axioms.ACVF :=
    mem_ACVF_kField (by simp [Axioms.kField, Axioms.ofList])
  have h := allSortedK_realize hM hmem ![a, b]
    (by intro i; fin_cases i
        · exact iRV_of_inK hM ha
        · exact iRV_of_inK hM hb)
    (by intro i; fin_cases i
        · exact ha
        · exact hb)
  simp only [pEq, BoundedFormula.realize_bdEqual, realize_tKAdd, realize_tv] at h
  simpa using h

/-- `0` is neutral for `+` in `K`, on the left. -/
theorem kAdd_zero_left (hM : M ⊨ Axioms.ACVF) {a : M} (ha : iUnits a ∨ a = iRVZero) :
    iKAdd iRVZero a = a := by
  rw [kAdd_comm hM (Or.inr rfl) ha]
  exact kAdd_zero_right hM ha

/-- `-1 = 1`: negation in the two-element residue field. -/
theorem kNeg_one (hM : M ⊨ Axioms.ACVF) (hT : TrivVal M) :
    iKNeg (iRVOne (M := M)) = iRVOne := by
  have hunit : iUnits (iRVOne (M := M)) ∨ iRVOne (M := M) = iRVZero := Or.inl (iUnits_rvOne hM)
  have hneg : iKAdd iRVOne (iKNeg iRVOne) = iRVZero := kAdd_neg hM hunit
  rcases rv_mem_two hM hT (iRV_of_inK hM (inK_kNeg hM hunit)) with h | h
  · rw [h] at hneg
    rw [kAdd_zero_right hM hunit] at hneg
    exact absurd hneg.symm (rvZero_ne_rvOne hM)
  · exact h

/-- `-0 = 0`: negation fixes the zero of the residue field. -/
theorem kNeg_zero (hM : M ⊨ Axioms.ACVF) : iKNeg (iRVZero (M := M)) = iRVZero := by
  have h0 : iUnits (iRVZero (M := M)) ∨ iRVZero (M := M) = iRVZero := Or.inr rfl
  have hneg : iKAdd iRVZero (iKNeg iRVZero) = iRVZero := kAdd_neg hM h0
  rw [kAdd_zero_left hM (inK_kNeg hM h0)] at hneg
  exact hneg

/-- `1 + 1 = 0` in the two-element residue field. -/
theorem kAdd_one_one (hM : M ⊨ Axioms.ACVF) (hT : TrivVal M) :
    iKAdd (iRVOne (M := M)) iRVOne = iRVZero := by
  have h : iKAdd (iRVOne (M := M)) (iKNeg iRVOne) = iRVZero :=
    kAdd_neg hM (Or.inl (iUnits_rvOne hM))
  rwa [kNeg_one hM hT] at h

/-! ## 6. The residue operations on `rv`-images -/

/-- `rv x ∈ K = Kˣ ∪ {0}` under a trivial valuation. -/
theorem inK_rv (hM : M ⊨ Axioms.ACVF) (hT : TrivVal M) {x : M} (hx : iVF x) :
    iUnits (iRv x) ∨ iRv x = iRVZero := by
  by_cases h0 : x = iVFZero
  · exact Or.inr (by rw [h0]; exact rv_zero_eq hM)
  · exact Or.inl ((units_rv_iff hM hT hx).mpr h0)

/-- `0` is neutral for `+` on `rv`-images, on the left. -/
theorem kAdd_rv_zero_left (hM : M ⊨ Axioms.ACVF) (hT : TrivVal M) {s t : M}
    (hs : iVF s) (ht : iVF t) (h : s = iVFZero) :
    iKAdd (iRv s) (iRv t) = iRv t := by
  rw [h, rv_zero_eq hM]
  exact kAdd_zero_left hM (inK_rv hM hT ht)

/-- `0` is neutral for `+` on `rv`-images, on the right. -/
theorem kAdd_rv_zero_right (hM : M ⊨ Axioms.ACVF) (hT : TrivVal M) {s t : M}
    (hs : iVF s) (ht : iVF t) (h : t = iVFZero) :
    iKAdd (iRv s) (iRv t) = iRv s := by
  rw [h, rv_zero_eq hM]
  exact kAdd_zero_right hM (inK_rv hM hT hs)

/-- On two nonzero `rv`-images, `+` is the zero of the two-element residue field:
`rv s + rv t = rv 0`. -/
theorem kAdd_rv_ne (hM : M ⊨ Axioms.ACVF) (hT : TrivVal M) {s t : M}
    (hs : iVF s) (ht : iVF t) (h1 : s ≠ iVFZero) (h2 : t ≠ iVFZero) :
    iKAdd (iRv s) (iRv t) = iRVZero := by
  rw [rv_val_one hM hT hs h1, rv_val_one hM hT ht h2]
  exact kAdd_one_one hM hT

/-- Negation fixes `rv`-images. -/
theorem kNeg_rv (hM : M ⊨ Axioms.ACVF) (hT : TrivVal M) {s : M} (hs : iVF s) :
    iKNeg (iRv s) = iRv s := by
  by_cases h0 : s = iVFZero
  · rw [h0, rv_zero_eq hM]
    exact kNeg_zero hM
  · rw [rv_val_one hM hT hs h0]
    exact kNeg_one hM hT

/-- `×` on `rv`-images is `rv` of the product (this is `rvMulHom` of the frozen axioms). -/
theorem kMul_rv (hM : M ⊨ Axioms.ACVF) {s t : M} (hs : iVF s) (ht : iVF t) :
    iRVMul (iRv s) (iRv t) = iRv (iVFMul s t) :=
  (rv_mul_hom hM hs ht).symm

/-- `∞` absorbs `×` on `rv`-images. -/
theorem kMul_rv_zero (hM : M ⊨ Axioms.ACVF) {s t : M} (hs : iVF s) (ht : iVF t)
    (h : t = iVFZero) : iRVMul (iRv s) (iRv t) = iRVZero := by
  rw [h, rv_zero_eq hM]
  exact rvMul_infty hM (rv_mem hM hs)

/-! ## 7. Eliminating quantifiers over `RV` -/

/-- **`RV`-quantifiers are eliminable**: because `RV = {∞, 1}`, an existential over the `RV` sort
is a two-term disjunction.  This is the only quantifier elimination the trivial case needs on
the `RV` side. -/
theorem rv_exists_two (hM : M ⊨ Axioms.ACVF) (hT : TrivVal M) {ψ : M → Prop} :
    (∃ a : M, iRV a ∧ ψ a) ↔ ψ iRVZero ∨ ψ iRVOne := by
  constructor
  · rintro ⟨a, ha, hψ⟩
    rcases rv_mem_two hM hT ha with h | h
    · exact Or.inl (h ▸ hψ)
    · exact Or.inr (h ▸ hψ)
  · rintro (h | h)
    · exact ⟨_, iRV_rvZero hM, h⟩
    · exact ⟨_, iRV_rvOne hM, h⟩

/-- The formula-level form of `rv_exists_two`: the guarded existential `exSorted .rv` is a
disjunction over the two `RV`-elements. -/
theorem exSorted_rv_realize (hM : M ⊨ Axioms.ACVF) (hT : TrivVal M) {k : ℕ} (φ : Bf (k + 1))
    (x : Fin k → M) :
    (exSorted .rv φ).Realize (default : Empty → M) x ↔
      φ.Realize (default : Empty → M) (Fin.snoc x iRVZero) ∨
        φ.Realize (default : Empty → M) (Fin.snoc x iRVOne) := by
  simp only [exSorted, BoundedFormula.realize_ex, BoundedFormula.realize_inf, sortPred,
    pRVsort_realize]
  have hterm : ∀ a : M, Term.realize (Sum.elim (default : Empty → M) (Fin.snoc x a))
      (tv k (Nat.lt_succ_self k)) = a := by
    intro a
    show Term.realize (Sum.elim (default : Empty → M) (Fin.snoc x a))
      (Term.var (Sum.inr ⟨k, Nat.lt_succ_self k⟩)) = a
    rw [Term.realize_var]
    simp only [Sum.elim_inr]
    rw [show (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1)) = Fin.last k from rfl, Fin.snoc_last]
  have h := rv_exists_two hM hT (ψ := fun a : M => φ.Realize (default : Empty → M) (Fin.snoc x a))
  simp only [hterm]
  exact h

/-! ## 8. The dictionary, packaged -/

/-- **The trivial-valuation dictionary.**  In a model of `Axioms.ACVF` whose valuation is
trivial, the entire `L_RV`-structure is a *definitional* expansion of the algebraically closed
field on the `VF` sort:

* `rv 1 = 1`, every nonzero element has value `1`;
* `rv x = ∞ ↔ x = 0` and `rv x = rv y ↔ x = y ∨ (x ≠ 0 ∧ y ≠ 0)`;
* the valuation order is `v x ≤ v y ↔ x ≠ 0 ∨ y = 0`;
* the units are exactly the nonzero elements: `Kˣ = rv (VF ∖ {0})`;
* `RV = {∞, 1}` has two elements, so `RV`-quantifiers are two-term disjunctions
  (`rv_exists_two`, `exSorted_rv_realize`). -/
theorem triv_dictionary (hM : M ⊨ Axioms.ACVF) (hT : TrivVal M) :
    (iRv (iVFOne (M := M)) = iRVOne) ∧
    (∀ x : M, iVF x → x ≠ iVFZero → iRv x = iRVOne) ∧
    (∀ x : M, iVF x → (iRv x = iRVZero ↔ x = iVFZero)) ∧
    (∀ x y : M, iVF x → iVF y →
      (iRv x = iRv y ↔ x = y ∨ (x ≠ iVFZero ∧ y ≠ iVFZero))) ∧
    (∀ x y : M, iVF x → iVF y → (iLe (iRv x) (iRv y) ↔ x ≠ iVFZero ∨ y = iVFZero)) ∧
    (∀ x : M, iVF x → (iUnits (iRv x) ↔ x ≠ iVFZero)) ∧
    (∀ a : M, iRV a → a = iRVZero ∨ a = iRVOne) :=
  ⟨rv_one_eq hM hT, fun _ hx h0 => rv_val_one hM hT hx h0,
    fun _ hx => rv_eq_inf_iff hM hx,
    fun _ _ hx hy => rv_eq_iff hM hT hx hy,
    fun _ _ hx hy => le_rv_iff hM hT hx hy,
    fun _ hx => units_rv_iff hM hT hx,
    fun _ ha => rv_mem_two hM hT ha⟩

/-! ## 9. `kAlgClosed` extraction and the refutation of the coarse case -/

theorem mem_ACVF_kAlgClosed {s : LRV.Sentence} (h : s ∈ Axioms.kAlgClosed) : s ∈ Axioms.ACVF := by
  simp only [Axioms.ACVF, Axioms.ACVFpaper, Set.mem_union] at *
  tauto

theorem mem_ACVF_acfSchemeK_two : Axioms.acfSchemeK 2 ∈ Axioms.ACVF :=
  mem_ACVF_kAlgClosed (by
    simp only [Axioms.kAlgClosed, Set.mem_setOf_eq]
    exact ⟨2, by norm_num, rfl⟩)

/-- Realization of the `K`-guarded existential `exSortedK .rv`, with the fresh variable
reduced to the quantified element. -/
theorem exSortedK_realize {k : ℕ} (φ : Bf (k + 1)) (x : Fin k → M) :
    (exSortedK .rv φ).Realize (default : Empty → M) x ↔
      ∃ a : M, iRV a ∧ (iUnits a ∨ a = iRVZero) ∧
        φ.Realize (default : Empty → M) (Fin.snoc x a) := by
  have hterm : ∀ a : M, Term.realize (Sum.elim (default : Empty → M) (Fin.snoc x a))
      (tv k (Nat.lt_succ_self k)) = a := by
    intro a
    show Term.realize (Sum.elim (default : Empty → M) (Fin.snoc x a))
      (Term.var (Sum.inr ⟨k, Nat.lt_succ_self k⟩)) = a
    rw [Term.realize_var]
    simp only [Sum.elim_inr]
    rw [show (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1)) = Fin.last k from rfl, Fin.snoc_last]
  simp only [exSortedK, BoundedFormula.realize_ex, BoundedFormula.realize_inf, sortPred,
    pRVsort_realize, pInK_realize, hterm, and_assoc]

/-- **The coarse trivial-valuation case does not exist.**  A model of `Axioms.ACVF` cannot have
all nonzero `VF`-elements of the same value: then `RV = {∞, 1}` (`rv_mem_two`), hence the residue
field `K ⊆ RV` has at most two elements, but `kAlgClosed` makes `K` algebraically closed, and the
two-element field has no root for `x² + x + 1`.

So the "trivially valued" case of the case split in `QE-PLAN.md` has to be read as
*order-trivial with `rv` injective* (the intended model), not as `rv`-constant. -/
theorem no_coarse_triv (hM : M ⊨ Axioms.ACVF) (hT : TrivVal M) : False := by
  have hsort : ∀ i : Fin 2, iRV (![(iRVOne (M := M)), (iRVOne (M := M))] i) := by
    intro i; fin_cases i <;> simp [iRV_rvOne hM]
  have hK : ∀ i : Fin 2, iUnits (![(iRVOne (M := M)), (iRVOne (M := M))] i) ∨
      ![(iRVOne (M := M)), (iRVOne (M := M))] i = iRVZero := by
    intro i; fin_cases i <;> simp [iUnits_rvOne hM]
  have hmain := allSortedK_realize hM mem_ACVF_acfSchemeK_two
    ![(iRVOne (M := M)), (iRVOne (M := M))] hsort hK
  obtain ⟨a, haRV, -, haeq⟩ := (exSortedK_realize (k := 2)
    (pEq (hornerPoly tKAdd tRVMul) tRVZero) ![(iRVOne (M := M)), (iRVOne (M := M))]).mp hmain
  rw [hornerPoly_two] at haeq
  simp only [pEq, BoundedFormula.realize_bdEqual, realize_tKAdd, realize_tRVMul,
    realize_tRVZero] at haeq
  simp at haeq
  rcases rv_mem_two hM hT haRV with h | h
  · rw [h] at haeq
    rw [kAdd_zero_left hM (Or.inl (iUnits_rvOne hM))] at haeq
    rw [rvMul_infty hM (iRV_rvOne hM)] at haeq
    rw [kAdd_zero_left hM (Or.inl (iUnits_rvOne hM))] at haeq
    exact rvZero_ne_rvOne hM haeq.symm
  · rw [h] at haeq
    rw [kAdd_one_one hM hT] at haeq
    rw [kMul_one hM (Or.inr rfl)] at haeq
    rw [kAdd_zero_left hM (Or.inl (iUnits_rvOne hM))] at haeq
    exact rvZero_ne_rvOne hM haeq.symm

/-- The negation, in positive form: in every model of `Axioms.ACVF` some nonzero `VF`-element has
a value different from `rv 1`.  Hence `rv` is not constant on `VF ∖ {0}`. -/
theorem exists_rv_ne_one (hM : M ⊨ Axioms.ACVF) :
    ∃ x : M, iVF x ∧ x ≠ iVFZero ∧ iRv x ≠ iRv (iVFOne (M := M)) := by
  by_contra h
  apply no_coarse_triv hM
  intro x hx
  by_cases h0 : x = iVFZero
  · exact Or.inl h0
  · exact Or.inr (by by_contra hne; exact h ⟨x, hx, h0, hne⟩)

/-! ## 10. The fine trivial case: order-trivial with injective `rv`

`no_coarse_triv` shows that the coarse reading of "trivial valuation" (`rv` constant on
`VF ∖ {0}`) is *empty*.  The trivially valued models of `Axioms.ACVF` are instead the ones where
the valuation *order* is trivial and `rv` is injective — the intended model, where the residue
field is the whole field and `Kˣ = VF ∖ {0}`.  This section isolates exactly the hypothesis set
the trivial case needs and proves the atom dictionary under it. -/

/-- **The fine trivial case**: the valuation order is trivial, `rv` is injective on `VF`, the
units are the nonzero elements, and the residue operations agree with the field operations along
`rv`.  (All of these hold in the trivially valued algebraically closed field, the intended model
of the second case of the case split in `QE-PLAN.md`.) -/
structure FineTriv (M : Type) [LRV.Structure M] : Prop where
  /-- `rv` is injective on the `VF` sort -/
  inj : ∀ x y : M, iVF x → iVF y → iRv x = iRv y → x = y
  /-- the valuation order is trivial: `v x ≤ v y ↔ x ≠ 0 ∨ y = 0` -/
  ord : ∀ x y : M, iVF x → iVF y → (iLe (iRv x) (iRv y) ↔ x ≠ iVFZero ∨ y = iVFZero)
  /-- `Kˣ` is the set of nonzero elements -/
  units : ∀ x : M, iVF x → (iUnits (iRv x) ↔ x ≠ iVFZero)
  /-- the residue addition is the field addition -/
  add : ∀ x y : M, iVF x → iVF y → iKAdd (iRv x) (iRv y) = iRv (iVFAdd x y)
  /-- the residue negation is the field negation -/
  neg : ∀ x : M, iVF x → iKNeg (iRv x) = iRv (iVFNeg x)
  /-- the residue one is the value of the field one -/
  one : iRv (iVFOne (M := M)) = iRVOne

/-- In the fine trivial case `rv` is injective on `VF`. -/
theorem fine_rv_eq (h : FineTriv M) {x y : M} (hx : iVF x) (hy : iVF y) :
    iRv x = iRv y ↔ x = y :=
  ⟨fun hh => h.inj x y hx hy hh, fun hh => by rw [hh]⟩

/-- **Elimination of `RV`-quantifiers in the fine trivial case**: using `rvSurj`, an existential
over `RV` becomes `∞` or the `rv` of a nonzero `VF`-element — the step that replaces
`∃ y (RV), ψ` by `y = rv 0 ∨ ∃ x (VF), x ≠ 0 ∧ ψ[rv x / y]` in the cover of `e1`. -/
theorem rv_exists_vf (hM : M ⊨ Axioms.ACVF) {ψ : M → Prop} :
    (∃ a : M, iRV a ∧ ψ a) ↔
      ψ iRVZero ∨ ∃ x : M, iVF x ∧ x ≠ iVFZero ∧ ψ (iRv x) := by
  constructor
  · rintro ⟨a, ha, hψ⟩
    by_cases h0 : a = iRVZero
    · exact Or.inl (h0 ▸ hψ)
    · right
      obtain ⟨x, hxVF, hx⟩ := rv_surj hM ha h0
      refine ⟨x, hxVF, ?_, ?_⟩
      · intro hx0
        rw [hx0, rv_zero_eq hM] at hx
        exact h0 hx.symm
      · rw [hx]; exact hψ
  · rintro (h | ⟨x, hx, -, hψ⟩)
    · exact ⟨_, iRV_rvZero hM, h⟩
    · exact ⟨_, rv_mem hM hx, hψ⟩

/-- **The fine-case dictionary**: under `FineTriv`, every atomic `L_RV`-formula whose terms are
`rv`-images of `VF`-terms is equivalent to a quantifier-free condition in the *field* language of
the `VF` sort.  Together with `rv_exists_vf` this is the trivial case's half of the cover of `e1`;
the other half — terms of the form `iVFAdd (rv s) (rv t)` and `iVFNeg (rv s)`, i.e. the `VF`
operations applied to `RV`-elements — is *junk*: no axiom of `Axioms.ACVF` constrains it, so no
`QF` translation of an arbitrary `L_RV`-formula can exist in the trivial case without an extra
junk convention. -/
theorem fine_dictionary (hM : M ⊨ Axioms.ACVF) (h : FineTriv M) :
    (∀ x y : M, iVF x → iVF y → (iRv x = iRv y ↔ x = y)) ∧
    (∀ x y : M, iVF x → iVF y → (iLe (iRv x) (iRv y) ↔ x ≠ iVFZero ∨ y = iVFZero)) ∧
    (∀ x : M, iVF x → (iUnits (iRv x) ↔ x ≠ iVFZero)) ∧
    (∀ x y : M, iVF x → iVF y → iKAdd (iRv x) (iRv y) = iRv (iVFAdd x y)) ∧
    (∀ x : M, iVF x → iKNeg (iRv x) = iRv (iVFNeg x)) ∧
    (∀ x : M, iVF x → iKNeg (iRv x) = iRv (iVFNeg x)) ∧
    (∀ x y : M, iVF x → iVF y → iRVMul (iRv x) (iRv y) = iRv (iVFMul x y)) :=
  ⟨fun x y hx hy => fine_rv_eq h hx hy, h.ord, h.units, h.add, h.neg, h.neg,
    fun x y hx hy => (rv_mul_hom hM hx hy).symm⟩

/-! ## 11. The trivial case's atom eliminations, in the form the cover consumes -/

/-- In the fine case, `rv x + rv y = rv u` is the field equation `x + y = u`. -/
theorem fine_kAdd_atom (hM : M ⊨ Axioms.ACVF) (h : FineTriv M) {x y u : M}
    (hx : iVF x) (hy : iVF y) (hu : iVF u) :
    (iKAdd (iRv x) (iRv y) = iRv u) ↔ iVFAdd x y = u := by
  rw [h.add x y hx hy]
  exact fine_rv_eq h (vf_add_mem hM hx hy) hu

/-- In the fine case, `- rv x = rv u` is the field equation `-x = u`. -/
theorem fine_kNeg_atom (hM : M ⊨ Axioms.ACVF) (h : FineTriv M) {x u : M}
    (hx : iVF x) (hu : iVF u) :
    (iKNeg (iRv x) = iRv u) ↔ iVFNeg x = u := by
  rw [h.neg x hx]
  exact fine_rv_eq h (vf_neg_mem hM hx) hu

/-- In the fine case, `rv x · rv y = rv u` is the field equation `x y = u`. -/
theorem fine_kMul_atom (hM : M ⊨ Axioms.ACVF) (h : FineTriv M) {x y u : M}
    (hx : iVF x) (hy : iVF y) (hu : iVF u) :
    (iRVMul (iRv x) (iRv y) = iRv u) ↔ iVFMul x y = u := by
  rw [← rv_mul_hom hM hx hy]
  exact fine_rv_eq h (vf_mul_mem hM hx hy) hu

/-- **The `RV`-quantifier elimination of `e1`'s cover, on the trivial side, at formula level**:
`∃ y (RV), ψ` is `ψ(∞) ∨ ∃ x (VF), x ≠ 0 ∧ ψ(rv x)`. -/
theorem exSorted_rv_realize_vf (hM : M ⊨ Axioms.ACVF) {k : ℕ} (φ : Bf (k + 1))
    (x : Fin k → M) :
    (exSorted .rv φ).Realize (default : Empty → M) x ↔
      φ.Realize (default : Empty → M) (Fin.snoc x iRVZero) ∨
        ∃ a : M, iVF a ∧ a ≠ iVFZero ∧
          φ.Realize (default : Empty → M) (Fin.snoc x (iRv a)) := by
  have hterm : ∀ a : M, Term.realize (Sum.elim (default : Empty → M) (Fin.snoc x a))
      (tv k (Nat.lt_succ_self k)) = a := by
    intro a
    show Term.realize (Sum.elim (default : Empty → M) (Fin.snoc x a))
      (Term.var (Sum.inr ⟨k, Nat.lt_succ_self k⟩)) = a
    rw [Term.realize_var]
    simp only [Sum.elim_inr]
    rw [show (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1)) = Fin.last k from rfl, Fin.snoc_last]
  simp only [exSorted, BoundedFormula.realize_ex, BoundedFormula.realize_inf, sortPred,
    pRVsort_realize, hterm]
  exact rv_exists_vf hM

/-! ## Axiom checks -/

#print axioms TrivCase.units_ne_infty
#print axioms TrivCase.allSortedK_realize
#print axioms TrivCase.rvZero_ne_rvOne
#print axioms TrivCase.kAdd_neg
#print axioms TrivCase.kNeg_one
#print axioms TrivCase.kAdd_one_one
#print axioms TrivCase.rv_one_eq
#print axioms TrivCase.rv_eq_iff
#print axioms TrivCase.le_rv_iff
#print axioms TrivCase.units_rv_iff
#print axioms TrivCase.rv_mem_two
#print axioms TrivCase.kAdd_rv_ne
#print axioms TrivCase.rv_exists_two
#print axioms TrivCase.exSorted_rv_realize
#print axioms TrivCase.triv_dictionary
#print axioms TrivCase.exSortedK_realize
#print axioms TrivCase.no_coarse_triv
#print axioms TrivCase.exists_rv_ne_one
#print axioms TrivCase.fine_rv_eq
#print axioms TrivCase.rv_exists_vf
#print axioms TrivCase.fine_dictionary

#print axioms TrivCase.fine_kAdd_atom
#print axioms TrivCase.fine_kNeg_atom
#print axioms TrivCase.fine_kMul_atom
#print axioms TrivCase.exSorted_rv_realize_vf

#print axioms TrivCase.no_coarse_triv
#print axioms TrivCase.rv_exists_vf
#print axioms TrivCase.fine_dictionary
#print axioms TrivCase.allSortedK_realize


/-!
# Per-model quantifier elimination versus quantifier elimination of a theory

`QECriterion.HasQE T` says: every formula is `T`-equivalent to a quantifier-free formula, with
*one* quantifier-free formula working in **all** models of `T`.

The per-model statement — every model of `T`, on its own, eliminates quantifiers — is strictly
weaker, and the gap is not a technicality: it is the reason a "two cases" assembly (nontrivially
valued / trivially valued models of `ACVF`) cannot be closed by a case split alone. What has to be
added is uniformity across models: two models of `T` that agree on all quantifier-free *sentences*
must be elementarily equivalent (`sentence_iff_of_qfSentence_iff`), and a case split can be glued
only when a quantifier-free separator exists for the two classes (`hasQE_of_qfSeparated`).

The last section is a machine-checked counterexample to the general step "per-model QE implies QE
of the theory", in the smallest language where the statement can be made.
-/

set_option linter.style.haveILetI false

open FirstOrder FirstOrder.Language
open scoped FirstOrder

end TrivCase

namespace Smw1541fr.M1

universe u v

variable {L : FirstOrder.Language.{u, v}}

/-! ## 0. Bridging `M ⊨ φ` with bounded realization -/

lemma sentence_realize_iff {ψ : L.Sentence} {M : Type} [L.Structure M] :
    (M ⊨ ψ) ↔ BoundedFormula.Realize ψ (default : Empty → M) (default : Fin 0 → M) :=
  Iff.rfl

/-! ## 1. The two notions -/

/-- **Per-model quantifier elimination.** Every model of `T` eliminates quantifiers *in itself*:
each formula is, uniformly in the tuple, equivalent in that model to a quantifier-free formula
with the same free variables.  Nothing is required to be uniform across different models of `T`.

(Quantification over the tuple is essential: without it the condition would be vacuous, `⊤` and
`⊥` being available at each single tuple.) -/
def PerModelQE (T : L.Theory) : Prop :=
  ∀ (α : Type) (φ : L.Formula α) (M : Type) [L.Structure M] [Nonempty M], M ⊨ T →
    ∃ ψ : L.Formula α, ψ.IsQF ∧ ∀ v : α → M, (φ.Realize v ↔ ψ.Realize v)

/-- Quantifier elimination of a theory gives quantifier elimination in each of its models. -/
theorem HasQE.perModelQE {T : L.Theory} (h : QECriterion.HasQE T) : PerModelQE T := by
  intro α φ M _ _ hM
  obtain ⟨ψ, hqf, hiff⟩ := h α φ
  haveI : M ⊨ T := hM
  refine ⟨ψ, hqf, fun v => ?_⟩
  have h' := hiff.realize_boundedFormula (M := M) (v := v) (xs := default)
  simpa only [BoundedFormula.realize_iff, Formula.Realize] using h'

/-! ## 2. What QE really buys: quantifier-free sentences determine the theory of a model -/

/-- **The uniformity step.** If `T` has quantifier elimination, then any two of its models that
agree on all quantifier-free *sentences* are elementarily equivalent.  Contrapositively: two
models of `T` that agree on quantifier-free sentences but disagree on some sentence refute
`HasQE T`.  This is the test a two-case assembly has to pass: the trivially valued and the
nontrivially valued models of the frozen `ACVF` must be separated by a quantifier-free sentence. -/
theorem sentence_iff_of_qfSentence_iff {T : L.Theory} (hT : QECriterion.HasQE T)
    {M : Type} [L.Structure M] [Nonempty M] {N : Type} [L.Structure N] [Nonempty N]
    (hM : M ⊨ T) (hN : N ⊨ T)
    (hQF : ∀ ψ : L.Sentence, ψ.IsQF → ((M ⊨ ψ) ↔ (N ⊨ ψ))) :
    ∀ σ : L.Sentence, ((M ⊨ σ) ↔ (N ⊨ σ)) := by
  intro σ
  obtain ⟨ψ, hqf, hiff⟩ := hT Empty σ
  haveI : M ⊨ T := hM
  haveI : N ⊨ T := hN
  have h1 : (M ⊨ σ) ↔ (M ⊨ ψ) := by
    rw [sentence_realize_iff, sentence_realize_iff]
    have h' := hiff.realize_boundedFormula (M := M) (v := (default : Empty → M))
      (xs := (default : Fin 0 → M))
    simpa only [BoundedFormula.realize_iff] using h'
  have h2 : (N ⊨ σ) ↔ (N ⊨ ψ) := by
    rw [sentence_realize_iff, sentence_realize_iff]
    have h' := hiff.realize_boundedFormula (M := N) (v := (default : Empty → N))
      (xs := (default : Fin 0 → N))
    simpa only [BoundedFormula.realize_iff] using h'
  exact h1.trans ((hQF ψ hqf).trans h2.symm)

/-- The refutation form: two models of `T` that agree on quantifier-free sentences and disagree
on some sentence show that `T` does *not* have quantifier elimination. -/
theorem not_hasQE_of_qfSentence_equiv {T : L.Theory}
    {M : Type} [L.Structure M] [Nonempty M] {N : Type} [L.Structure N] [Nonempty N]
    (hM : M ⊨ T) (hN : N ⊨ T)
    (hQF : ∀ ψ : L.Sentence, ψ.IsQF → ((M ⊨ ψ) ↔ (N ⊨ ψ)))
    (σ : L.Sentence) (hσ : (M ⊨ σ) ↔ ¬ (N ⊨ σ)) :
    ¬ QECriterion.HasQE T := by
  intro hT
  have h1 := sentence_iff_of_qfSentence_iff hT hM hN hQF σ
  tauto

/-! ## 3. Gluing a case split: what a two-case assembly actually needs

If the models of `T` split into two classes, quantifier elimination is known on each class, and a
**quantifier-free** formula separator exists for the two classes, then `T` has quantifier
elimination.  The separator is not a convenience: by `not_hasQE_of_qfSentence_equiv` something of
this kind is necessary for any such gluing, and for the frozen `ACVF` there is none (see
`NOTE.md`). -/

theorem hasQE_of_qfSeparated {T T₁ T₂ : L.Theory}
    (hcov : ∀ (M : Theory.ModelType.{u, v, max u v} T), (M.Carrier ⊨ T₁) ∨ (M.Carrier ⊨ T₂))
    (h₁ : QECriterion.HasQE T₁) (h₂ : QECriterion.HasQE T₂)
    (sep : ∀ (α : Type), ∃ τ : L.Formula α, τ.IsQF ∧ T₁ ⊨ᵇ τ ∧ T₂ ⊨ᵇ τ.not) :
    QECriterion.HasQE T := by
  intro α φ
  obtain ⟨ψ₁, hqf₁, hiff₁⟩ := h₁ α φ
  obtain ⟨ψ₂, hqf₂, hiff₂⟩ := h₂ α φ
  obtain ⟨τ, hτqf, hτ₁, hτ₂⟩ := sep α
  refine ⟨(ψ₁ ⊓ τ) ⊔ (ψ₂ ⊓ τ.not), hqf₁.inf hτqf |>.sup (hqf₂.inf hτqf.not), ?_⟩
  show T ⊨ᵇ (BoundedFormula.iff φ ((ψ₁ ⊓ τ) ⊔ (ψ₂ ⊓ τ.not)))
  rw [Theory.models_formula_iff]
  intro M v
  rcases hcov M with hc | hc
  · haveI : M.Carrier ⊨ T₁ := hc
    have hsep := hτ₁.realize_boundedFormula (M := M.Carrier) (v := v) (xs := default)
    have hiff := hiff₁.realize_boundedFormula (M := M.Carrier) (v := v) (xs := default)
    simp only [Formula.Realize, BoundedFormula.realize_iff, BoundedFormula.realize_sup,
      BoundedFormula.realize_inf, BoundedFormula.realize_not] at hsep hiff ⊢
    tauto
  · haveI : M.Carrier ⊨ T₂ := hc
    have hsep := hτ₂.realize_boundedFormula (M := M.Carrier) (v := v) (xs := default)
    have hiff := hiff₂.realize_boundedFormula (M := M.Carrier) (v := v) (xs := default)
    simp only [Formula.Realize, BoundedFormula.realize_iff, BoundedFormula.realize_sup,
      BoundedFormula.realize_inf, BoundedFormula.realize_not] at hsep hiff ⊢
    tauto

end Smw1541fr.M1

#print axioms Smw1541fr.M1.HasQE.perModelQE
#print axioms Smw1541fr.M1.sentence_iff_of_qfSentence_iff
#print axioms Smw1541fr.M1.not_hasQE_of_qfSentence_equiv
#print axioms Smw1541fr.M1.hasQE_of_qfSeparated

/-
  **Direction e2: `pLe` and `pUnits` inside `L_val`.**

  The frozen `L_RV` encoding of `ACVF` (`QE/Assembly_val.lean`, module `Pre`) has two atoms that
  mention `rv` of a `VF`-term: `pLe (tRv s) (tRv t)` and `pUnits (tRv s)`.  The cover direction of
  the transfer (every `L_RV`-formula is `ACVF`-equivalent to a translated `L_val`-formula) needs
  their `L_val`-preimages, *and* it needs them to be exact, junk cases included.

  What this file proves (all unconditional, no `sorry`, no `axiom`):

  * `not_units_zero` — **`Kˣ` does not contain `∞ = rv 0`**, from the frozen axioms alone.  This is
    not stated by any axiom of the encoding (every `Kˣ`-axiom is guarded by `pUnits`, and
    `leClassOne` is guarded by `pRV`), but it *is* a consequence: `rvMulInv` at `0` produces
    `y ∈ Kˣ` with `y · 0 = 1`, and `rvMulInfty` at `y` gives `y · 0 = 0`, so `0 = 1` against
    `kField`.  This is what makes the guard in `leClassOne` removable (`iUnits_iff'`), i.e. it is
    the junk case of `pUnits` at `s = 0`.
  * `iUnits_iff'` — the semantic form of `Axioms.leClassOne`, **unguarded**: for `x ∈ RV`,
    `x ∈ Kˣ ↔ 1 ≤ x ∧ x ≤ 1`.
  * `pLe_rv_iff` — the `pLe` atom at `rv`-of-terms is `predV` with its arguments swapped:
    `pLe (tRv s) (tRv t) ↔ predV t s`, i.e. `↔ |t| ≤ |s|`  (the two orders are opposite: `∞` is
    the top of the `RV` order and the bottom of the `L_val` order).
  * `leOneF` — the `L_val`-formula `v s ≤ v 1 ∧ v 1 ≤ v s`, with `leOneF_realize`, and
    `leOneF_iff_pUnits` : its realisation is *exactly* `pUnits (tRv s)`, junk case `s = 0`
    included; likewise `translate_pLe` for the order atom, and `pInK` for `K = Kˣ ∪ {0}`.
  * the junk cases explicitly: `not_units_rv_zero`, `pUnits_tRv_zero`, `leOneF_zero`.

  Direction of the reversal, checked against `Transfer.predV` (`predV x y = iLe (iRv y) (iRv x)`):
  `leF s t` (`L_val`'s `v s ≤ v t`) realises as `iLe (iRv t) (iRv s) = predV s t`, so the `L_RV`
  atom `pLe (tRv s) (tRv t)` — which realises as `iLe (iRv s) (iRv t)` — is `predV t s` and has
  `L_val` preimage `leF t s`.

  `realize_tRVOne`, `exSorted_realize`, `realize_tv_last_apply`, `snoc_apply_zero_one/one_one`
  are re-derived here from `.ultramath/smw14elno/m4/d4.lean` (same proofs; that file is a separate
  module and not importable without rebuilding it).
-/

namespace SpecialTransformations.Milestone0.Transfer
namespace M2

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 LRV ValPM
open scoped FirstOrder

/-! ## 0. Re-derived helpers -/

/-- The realiser of the `1` of the `RV` sort. -/
theorem realize_tRVOne {M : Type} [LRV.Structure M] {k : ℕ} (v : Empty ⊕ Fin k → M) :
    (tRVOne (n := k)).realize v = iRVOne := by
  show FirstOrder.Language.Structure.funMap (L := LRV) Fn.rvOne
      (fun i => Term.realize (L := LRV) v ((fun j : Fin 0 => j.elim0) i)) = iRVOne
  rw [show (fun i => Term.realize (L := LRV) v ((fun j : Fin 0 => j.elim0) i))
      = (fun i => i.elim0) from by funext i; exact i.elim0]
  rfl

/-- The value of the last variable of `Fin.snoc x a`, as `exSorted` presents it. -/
theorem realize_tv_last_apply {M : Type} [LRV.Structure M] {k : ℕ} (v : Empty → M)
    (x : Fin k → M) (a : M) (h : k < k + 1) :
    (tv k h).realize (Sum.elim v (Fin.snoc x a)) = a := by
  rw [show tv k h = tv (⟨k, h⟩ : Fin (k + 1)).1 (⟨k, h⟩ : Fin (k + 1)).2 from rfl,
    realize_tv]
  simp [Fin.snoc]

/-- `Fin.snoc` at the first index, for a one-entry tuple. -/
theorem snoc_apply_zero_one {M : Type} (x : Fin 1 → M) (a : M) :
    (Fin.snoc (α := fun _ : Fin 2 => M) x a) (0 : Fin 2) = x 0 := by
  simp [Fin.snoc]

/-- `Fin.snoc` at the last index, for a one-entry tuple. -/
theorem snoc_apply_one_one {M : Type} (x : Fin 1 → M) (a : M) :
    (Fin.snoc (α := fun _ : Fin 2 => M) x a) (1 : Fin 2) = a := by
  simp [Fin.snoc]

/-- **Guard-free realisation of `exSorted`**: `∃ x ∈ s, φ`. -/
theorem exSorted_realize {M : Type} [LRV.Structure M] {k : ℕ} (s : SortTag) (φ : Bf (k + 1))
    (v : Empty → M) (x : Fin k → M) :
    (exSorted s φ).Realize v x ↔
      ∃ a : M, (match s with
          | .vf => iVF a
          | .rv => iRV a) ∧ φ.Realize v (Fin.snoc x a) := by
  cases s with
  | vf =>
    simp only [exSorted, BoundedFormula.realize_ex, BoundedFormula.realize_inf, sortPred,
      pVF_realize, realize_tv_last_apply]
  | rv =>
    simp only [exSorted, BoundedFormula.realize_ex, BoundedFormula.realize_inf, sortPred,
      pRVsort_realize, realize_tv_last_apply]

/-! ## 1. Membership helpers for the frozen theory -/

theorem mem_ACVF_rvGroup {s : LRV.Sentence} (h : s ∈ Axioms.rvGroup) : s ∈ Axioms.ACVF := by
  simp only [Axioms.ACVF, Axioms.ACVFpaper, Set.mem_union]
  tauto

theorem mem_ACVF_kField {s : LRV.Sentence} (h : s ∈ Axioms.kField) : s ∈ Axioms.ACVF := by
  simp only [Axioms.ACVF, Axioms.ACVFpaper, Set.mem_union]
  tauto

theorem mem_ACVF_rvMulInv : Axioms.rvMulInv ∈ Axioms.ACVF :=
  mem_ACVF_rvGroup (by simp [Axioms.rvGroup, Axioms.ofList])

theorem mem_ACVF_rvMulInfty : Axioms.rvMulInfty ∈ Axioms.ACVF :=
  mem_ACVF_rvGroup (by simp [Axioms.rvGroup, Axioms.ofList])

theorem mem_ACVF_rvMulOne : Axioms.rvMulOne ∈ Axioms.ACVF :=
  mem_ACVF_rvGroup (by simp [Axioms.rvGroup, Axioms.ofList])

theorem mem_ACVF_rvMulAssoc : Axioms.rvMulAssoc ∈ Axioms.ACVF :=
  mem_ACVF_rvGroup (by simp [Axioms.rvGroup, Axioms.ofList])

theorem mem_ACVF_rvOneMem : Axioms.rvOneMem ∈ Axioms.ACVF :=
  mem_ACVF_rvGroup (by simp [Axioms.rvGroup, Axioms.ofList])

theorem mem_ACVF_rvSurj : Axioms.rvSurj ∈ Axioms.ACVF :=
  mem_ACVF_rvAxioms (by simp [Axioms.rvAxioms, Axioms.ofList])

/-- `0 ≠ 1` of the residue field `K`, as an unguarded sentence of the frozen theory. -/
theorem mem_ACVF_kZeroNeOne : (∼(pEq tRVZero tRVOne)) ∈ Axioms.ACVF :=
  mem_ACVF_kField (by simp [Axioms.kField, Axioms.ofList])

/-- `∞ = 0` of the `RV` sort lies in the `RV` sort (sort closure `sdRVZero`). -/
theorem rv_zero_mem {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) :
    iRV (iRVZero (M := M)) := by
  have h := sentence_realize hM (φ := Axioms.sdRVZero)
    (mem_ACVF_sortClosure (s := Axioms.sdRVZero) (by simp [Axioms.sortClosure, Axioms.ofList]))
  rw [Axioms.sdRVZero, Sentence.Realize] at h
  simp only [Formula.Realize] at h
  rw [pRVsort_realize, realize_tRVZero] at h
  exact h

/-- `1` of the `RV` sort lies in the `RV` sort (sort closure `sdRVOne`). -/
theorem rv_one_mem {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) :
    iRV (iRVOne (M := M)) := by
  have h := sentence_realize hM (φ := Axioms.sdRVOne)
    (mem_ACVF_sortClosure (s := Axioms.sdRVOne) (by simp [Axioms.sortClosure, Axioms.ofList]))
  rw [Axioms.sdRVOne, Sentence.Realize] at h
  simp only [Formula.Realize] at h
  rw [pRVsort_realize, realize_tRVOne] at h
  exact h

/-- `1 ∈ Kˣ` (`Axioms.rvOneMem`). -/
theorem units_rv_one {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) :
    iUnits (iRVOne (M := M)) := by
  have h := sentence_realize hM (φ := Axioms.rvOneMem) mem_ACVF_rvOneMem
  rw [Axioms.rvOneMem, Sentence.Realize] at h
  simp only [Formula.Realize] at h
  rwa [pUnits_realize, realize_tRVOne] at h

/-- `0 ≠ 1` of the `RV` sort. -/
theorem rv_zero_ne_one {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) :
    iRVZero (M := M) ≠ iRVOne := by
  have h := sentence_realize hM mem_ACVF_kZeroNeOne
  rw [Sentence.Realize] at h
  simp only [Formula.Realize, BoundedFormula.realize_not, pEq, BoundedFormula.realize_bdEqual,
    realize_tRVZero, realize_tRVOne] at h
  exact h

/-- **The absorbing law of `∞` on the `RV` sort**: `y · ∞ = ∞` for `y ∈ RV`
(`Axioms.rvMulInfty`). -/
theorem rv_mul_infty {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {y : M}
    (hy : iRV y) : iRVMul y iRVZero = iRVZero := by
  have h := allSorted_realize hM (ss := ![SortTag.rv])
    (φ := (pEq (tRVMul &0 tRVInfty) tRVInfty)) mem_ACVF_rvMulInfty ![y] (by
      intro i; fin_cases i; simpa using hy)
  simpa [pEq, BoundedFormula.realize_bdEqual, realize_tRVMul, realize_tRVZero, tRVInfty,
    realize_tv, Term.realize_var, Sum.elim_inr, Function.comp_apply,
    Matrix.cons_val_zero] using h

/-- **Inverses in `Kˣ`** (`Axioms.rvMulInv`), semantically. -/
theorem units_inv {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {x : M}
    (hx : iRV x) (hu : iUnits x) :
    ∃ y : M, iRV y ∧ iUnits y ∧ iRVMul y x = iRVOne := by
  have h := allSorted_realize hM (ss := ![SortTag.rv])
    (φ := (pUnits &0 ⟹ exSorted .rv (pUnits &1 ⊓ pEq (tRVMul &1 &0) tRVOne)))
    mem_ACVF_rvMulInv ![x] (by intro i; fin_cases i; simpa using hx)
  have h' : iUnits x → ∃ y : M, iRV y ∧ iUnits y ∧ iRVMul y x = iRVOne := by
    simpa [pUnits_realize, exSorted_realize, BoundedFormula.realize_inf, pEq,
      BoundedFormula.realize_bdEqual, realize_tRVMul, realize_tRVOne, realize_tv_last_apply,
      snoc_apply_zero_one, snoc_apply_one_one] using h
  exact h' hu

/-! ## 2. `Kˣ` does not contain `∞` — the junk case of `pUnits` -/

/-- **`Kˣ` does not contain `∞ = 0 = rv 0`.**

The frozen axioms state nothing directly about `pUnits` at `0` (`sdUnits` only says `Kˣ ⊆ RV`,
`leClassOne` is guarded by `pRV`), but `Axioms.rvMulInv` at `0` gives `y ∈ Kˣ` with `y · 0 = 1`
and `Axioms.rvMulInfty` at `y` gives `y · 0 = 0`, hence `0 = 1`, contradicting `kField`. -/
theorem not_units_zero {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) :
    ¬ iUnits (iRVZero (M := M)) := by
  intro hu
  obtain ⟨y, hy, huy, hinv⟩ := units_inv hM (rv_zero_mem hM) hu
  have hzero : iRVMul y iRVZero = iRVZero := rv_mul_infty hM hy
  exact rv_zero_ne_one hM (by rw [← hinv, hzero])

/-- `Kˣ ⊆ RV` (`Axioms.sdUnits`), semantically. -/
theorem units_mem_rv {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {x : M}
    (hu : iUnits x) : iRV x := by
  have hmem : allOne (pUnits &0 ⟹ pRVsort &0) ∈ Axioms.ACVF :=
    mem_ACVF_sortClosure (by simp [Axioms.sortClosure, Axioms.ofList, Axioms.sdUnits])
  have h := allOne_realize hM (φ := (pUnits &0 ⟹ pRVsort &0)) hmem ![x]
  simp only [BoundedFormula.realize_imp, pUnits_realize, pRVsort_realize, Term.realize_var,
    Sum.elim_inr, Function.comp_apply, Matrix.cons_val_zero] at h
  exact h hu

/-! ## 3. `Kˣ` is the class of `1`, with the guard removed -/

/-- **`Axioms.leClassOne`, semantically** (guarded, as in `.ultramath/smw14elno/m4/d4.lean`):
for `x ∈ RV`, `x ∈ Kˣ ↔ 1 ≤ x ∧ x ≤ 1`. -/
theorem iUnits_iff_le {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {x : M}
    (hx : iRV x) (hx0 : x ≠ iRVZero) :
    iUnits x ↔ (iLe (iRVOne (M := M)) x ∧ iLe x iRVOne) := by
  have hmem : Axioms.leClassOne ∈ Axioms.ACVF :=
    mem_ACVF_preorderRV (s := Axioms.leClassOne) (by simp [Axioms.preorderRV, Axioms.ofList])
  have h := allSorted_realize hM (ss := ![SortTag.rv])
    (φ := (pRV &0 ⟹ (pUnits &0 ⇔ (pLe tRVOne &0 ⊓ pLe &0 tRVOne)))) hmem ![x] (by
      intro i; fin_cases i; simpa using hx)
  have h' : x ≠ iRVZero → (iUnits x ↔ (iLe iRVOne x ∧ iLe x iRVOne)) := by
    simpa [pRV_realize, pUnits_realize, realize_pLe, realize_tRVOne] using h
  exact h' hx0

/-- **`Kˣ` is the class of `1`, unguarded.**  The `pRV` guard of `Axioms.leClassOne` can be
dropped, because at `x = ∞ = 0` both sides are false: the right-hand side by
`Transfer.le_infty_eq` and `iRVZero ≠ iRVOne`, the left-hand side by `not_units_zero`. -/
theorem iUnits_iff' {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {x : M}
    (hx : iRV x) :
    iUnits x ↔ (iLe (iRVOne (M := M)) x ∧ iLe x iRVOne) := by
  by_cases hx0 : x = iRVZero
  · subst hx0
    constructor
    · intro hu
      exact absurd hu (not_units_zero hM)
    · rintro ⟨-, h2⟩
      exact absurd (le_infty_eq hM iRVOne (rv_one_mem hM) (rv_zero_ne_one hM).symm h2).symm
        (rv_zero_ne_one hM)
  · exact iUnits_iff_le hM hx hx0
/-- `∞ ≤ 1` is false: by `Axioms.leInftyEq` it would force `1 = ∞`, against `kField`. -/
theorem not_le_infty_one {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) :
    ¬ iLe (iRVZero (M := M)) iRVOne := by
  intro h
  exact rv_zero_ne_one hM
    (le_infty_eq hM iRVOne (rv_one_mem hM) (rv_zero_ne_one hM).symm h).symm

/-- A member of `Kˣ` is not `∞ = 0`: the junk case of `pUnits`, `0 ∈ Kˣ` is false. -/
theorem units_ne_infty {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {x : M}
    (hu : iUnits x) : x ≠ iRVZero :=
  fun h => not_units_zero hM (h ▸ hu)

/-! ## 4. Terms over a `VF`-tuple, and the two atoms at `rv`-of-terms -/

section Terms

variable {M : Type} [LRV.Structure M]

/-- `valTermEval` of a term over a `VF`-tuple stays in the `VF` sort. -/
theorem valTermEval_mem (hM : M ⊨ Axioms.ACVF) {n : ℕ} {x : Fin n → M}
    (hx : ∀ i, iVF (x i)) (t : Language.val.Term (Empty ⊕ Fin n)) :
    iVF (valTermEval x t) := by
  induction t with
  | var v =>
    rcases v with e | i
    · exact e.elim
    · exact hx i
  | func f args ih =>
    cases f with
    | add => exact vf_add_mem hM (ih 0) (ih 1)
    | mul => exact vf_mul_mem hM (ih 0) (ih 1)
    | neg => exact vf_neg_mem hM (ih 0)
    | zero => exact vf_zero_mem hM
    | one => exact vf_one_mem hM

@[simp] theorem valTermEval_zero {n : ℕ} (x : Fin n → M) :
    valTermEval x (0 : Language.val.Term (Empty ⊕ Fin n)) = iVFZero := rfl

@[simp] theorem valTermEval_one {n : ℕ} (x : Fin n → M) :
    valTermEval x (1 : Language.val.Term (Empty ⊕ Fin n)) = iVFOne := rfl

/-- **The `pLe` atom at `rv` of two terms.** -/
theorem realize_pLe_tRv {k : ℕ} (a b : Tm k) (v : Empty → M) (x : Fin k → M) :
    (pLe (tRv a) (tRv b)).Realize v x ↔
      iLe (iRv (a.realize (Sum.elim v x))) (iRv (b.realize (Sum.elim v x))) := by
  rw [realize_pLe, realize_tRv, realize_tRv]

/-- **The `pLe` atom at translated `L_val`-terms.** -/
theorem pLe_valTerm_iff {n : ℕ} (s t : Language.val.Term (Empty ⊕ Fin n)) (x : Fin n → M) :
    (pLe (tRv (valTermToRV s)) (tRv (valTermToRV t))).Realize (default : Empty → M) x ↔
      iLe (iRv (valTermEval x s)) (iRv (valTermEval x t)) := by
  rw [realize_pLe_tRv, valTermToRV_realize, valTermToRV_realize]

/-- **The `L_val` atom `leF s t` (`v s ≤ v t`), read in the `L_RV`-structure**: it is `iLe` of
the two values, reversed. -/
theorem leF_valTerm_iff {n : ℕ} (s t : Language.val.Term (Empty ⊕ Fin n)) (x : Fin n → M) :
    valFormulaEval x (leF s t) ↔ iLe (iRv (valTermEval x t)) (iRv (valTermEval x s)) :=
  Iff.rfl

/-- **The order atom: `pLe (rv s) (rv t)` is exactly the `L_val`-formula `leF t s`.**  The swap
`t s` is the reversal between the `RV` order (`∞` on top) and `L_val`'s `v · ≤ v ·` (`∞` at the
bottom). -/
theorem translate_pLe {n : ℕ} (s t : Language.val.Term (Empty ⊕ Fin n)) (x : Fin n → M) :
    valFormulaEval x (leF t s) ↔
      (pLe (tRv (valTermToRV s)) (tRv (valTermToRV t))).Realize (default : Empty → M) x :=
  (leF_valTerm_iff t s x).trans (pLe_valTerm_iff s t x).symm

/-- `⊓` on `L_val`-formulas, read by `valFormulaEval`. -/
theorem valFormulaEval_inf {n : ℕ} (x : Fin n → M)
    (φ ψ : Language.val.BoundedFormula Empty n) :
    valFormulaEval x (φ ⊓ ψ) ↔ (valFormulaEval x φ ∧ valFormulaEval x ψ) := by
  have h : valFormulaEval x (φ ⊓ ψ)
      = ¬ (valFormulaEval x φ → ¬ valFormulaEval x ψ) := rfl
  rw [h]
  tauto

/-- `⊔` on `L_val`-formulas, read by `valFormulaEval`. -/
theorem valFormulaEval_sup {n : ℕ} (x : Fin n → M)
    (φ ψ : Language.val.BoundedFormula Empty n) :
    valFormulaEval x (φ ⊔ ψ) ↔ (valFormulaEval x φ ∨ valFormulaEval x ψ) := by
  have h : valFormulaEval x (φ ⊔ ψ)
      = (¬ valFormulaEval x φ → valFormulaEval x ψ) := rfl
  rw [h]
  tauto

end Terms

/-! ## 5. `rv 1 = 1` — the other canonical value, also absent from the axioms -/

/-- **`rv` is surjective on `RV ∖ {∞}`** (`Axioms.rvSurj`), semantically. -/
theorem rv_surj {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {y : M}
    (hy : iRV y) (hy0 : y ≠ iRVZero) : ∃ x : M, iVF x ∧ iRv x = y := by
  have h := allSorted_realize hM (ss := ![SortTag.rv])
    (φ := (∼(pEq &0 tRVZero) ⟹ exSorted .vf (pEq (tRv &1) &0))) mem_ACVF_rvSurj ![y] (by
      intro i; fin_cases i; simpa using hy)
  simp only [pEq, BoundedFormula.realize_bdEqual, BoundedFormula.realize_imp,
    BoundedFormula.realize_not, exSorted, BoundedFormula.realize_ex, BoundedFormula.realize_inf,
    sortPred, realize_tRVZero, realize_tRv, pVF_realize,
    realize_tv_last_apply] at h
  exact h hy0

/-- `1` is neutral on `Kˣ` (`Axioms.rvMulOne`). -/
theorem rv_mul_one {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {x : M}
    (hu : iUnits x) : iRVMul (iRVOne (M := M)) x = x := by
  have h := allSorted_realize hM (ss := ![SortTag.rv])
    (φ := (pUnits &0 ⟹ pEq (tRVMul tRVOne &0) &0)) mem_ACVF_rvMulOne ![x] (by
      intro i; fin_cases i; simpa using units_mem_rv hM hu)
  have h' : iUnits x → iRVMul iRVOne x = x := by
    simpa [pUnits_realize, pEq, BoundedFormula.realize_bdEqual, realize_tRVMul, realize_tRVOne,
      Matrix.cons_val_zero] using h
  exact h' hu

/-- Associativity of `×` on the `RV` sort (`Axioms.rvMulAssoc`). -/
theorem rv_mul_assoc {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {x y z : M}
    (hx : iRV x) (hy : iRV y) (hz : iRV z) :
    iRVMul (iRVMul x y) z = iRVMul x (iRVMul y z) := by
  have h := allSorted_realize hM (ss := ![SortTag.rv, SortTag.rv, SortTag.rv])
    (φ := (pEq (tRVMul (tRVMul &0 &1) &2) (tRVMul &0 (tRVMul &1 &2))))
    mem_ACVF_rvMulAssoc ![x, y, z] (by intro i; fin_cases i <;> simp [hx, hy, hz])
  simpa [pEq, BoundedFormula.realize_bdEqual, realize_tRVMul, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons] using h

/-- **`rv 1` is a left identity for the whole of `RV^×`**: `rv(1) · y = y` for every `y ∈ RV`.
This is not an axiom — it is `rvSurj` (every `y` is some `rv x`) plus `rvMulHom` plus the field
law `1 · x = x`. -/
theorem rv_one_mul_left {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {y : M}
    (hy : iRV y) : iRVMul (iRv (iVFOne (M := M))) y = y := by
  by_cases hy0 : y = iRVZero
  · subst hy0
    exact rv_mul_infty hM (rv_mem hM (vf_one_mem hM))
  · obtain ⟨x, hx, hxy⟩ := rv_surj hM hy hy0
    rw [← hxy, ← rv_mul_hom hM (vf_one_mem hM) hx, vf_mul_comm hM (vf_one_mem hM) hx,
      vf_mul_one hM hx]

/-- Every `RV`-element other than `∞` is left-invertible with respect to `rv 1`:
`v · rv x = rv 1`.  This is where the field inverse of `VF` (`vf_mul_inv_or_zero`) enters; it is
what makes `RV^×` a group even though the encoding only axiomatises `Kˣ` as one. -/
theorem rv_exists_left_inv {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {y : M}
    (hy : iRV y) (hy0 : y ≠ iRVZero) :
    ∃ v : M, iRV v ∧ iRVMul v y = iRv (iVFOne (M := M)) := by
  obtain ⟨a, ha, rfl⟩ := rv_surj hM hy hy0
  rcases vf_mul_inv_or_zero hM ha with ha0 | ⟨b, hb, hab⟩
  · exact absurd (by rw [ha0, rv_zero_eq hM]) hy0
  · exact ⟨iRv b, rv_mem hM hb, by rw [← rv_mul_hom hM hb ha, vf_mul_comm hM hb ha, hab]⟩

/-- **`rv 1 = 1`.**  Not an axiom of the encoding (`rvMulHom` alone does not say it).

Two ingredients, both consequences of the axioms:
* `rv 1` is a left identity for the whole of `RV^×` (`rv_one_mul_left`, from `rvSurj` + `rvMulHom`);
* `1 = iRVOne` is idempotent (`rvMulOne` at `1 ∈ Kˣ`) and has a left inverse `v` with respect to
  `rv 1` (`rv_exists_left_inv`).

Then `rv 1 = v · 1 = v · (1 · 1) = (v · 1) · 1 = (rv 1) · 1 = 1`. -/
theorem rv_one_eq {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) :
    iRv (iVFOne (M := M)) = iRVOne := by
  have hone : iRVMul (iRVOne (M := M)) iRVOne = iRVOne :=
    rv_mul_one hM (units_rv_one hM)
  obtain ⟨v, hv, hve⟩ := rv_exists_left_inv hM (rv_one_mem hM) (rv_zero_ne_one hM).symm
  calc iRv iVFOne
      = iRVMul v iRVOne := hve.symm
    _ = iRVMul v (iRVMul iRVOne iRVOne) := by rw [hone]
    _ = iRVMul (iRVMul v iRVOne) iRVOne :=
        (rv_mul_assoc hM hv (rv_one_mem hM) (rv_one_mem hM)).symm
    _ = iRVMul (iRv iVFOne) iRVOne := by rw [hve]
    _ = iRVOne := rv_one_mul_left hM (rv_one_mem hM)

/-- `rv 1 ∈ Kˣ`: the `pUnits` atom holds at `rv 1`. -/
theorem units_rv_one_eq {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) :
    iUnits (iRv (iVFOne (M := M))) := by
  rw [rv_one_eq hM]
  exact units_rv_one hM

/-- `rv 1 ≠ ∞`. -/
theorem rv_one_ne_zero {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) :
    iRv (iVFOne (M := M)) ≠ iRVZero :=
  fun h => rv_zero_ne_one hM (by rw [← h, rv_one_eq hM])


/-! ## 5b. `Kˣ` is a single `≤`-class: the order atoms cannot separate units -/

/-- Every member of `Kˣ` satisfies both inequalities against `1`. -/
theorem units_le_one {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {x : M}
    (hu : iUnits x) :
    (iLe (iRVOne (M := M)) x ∧ iLe x iRVOne) :=
  (iUnits_iff' hM (units_mem_rv hM hu)).1 hu

/-- **Any two members of `Kˣ` are `≤`-equivalent.**  So the two order atoms cannot tell two
units apart: the order on `RV` sees only `RV/Kˣ`, not `RV` itself. -/
theorem units_pairwise_le {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {x y : M}
    (hx : iUnits x) (hy : iUnits y) : (iLe x y ∧ iLe y x) := by
  have hx' := units_le_one hM hx
  have hy' := units_le_one hM hy
  refine ⟨?_, ?_⟩
  · exact le_trans hM (units_mem_rv hM hx) (rv_one_mem hM) (units_mem_rv hM hy)
      (units_ne_infty hM hx) (rv_zero_ne_one hM).symm (units_ne_infty hM hy) hx'.2 hy'.1
  · exact le_trans hM (units_mem_rv hM hy) (rv_one_mem hM) (units_mem_rv hM hx)
      (units_ne_infty hM hy) (rv_zero_ne_one hM).symm (units_ne_infty hM hx) hy'.2 hx'.1

/-- `rv`-equality implies the two order atoms (the converse fails, see below). -/
theorem rv_eq_imp_orderEq {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {s t : M}
    (ht : iVF t) (h : iRv s = iRv t) :
    (iLe (iRv s) (iRv t) ∧ iLe (iRv t) (iRv s)) := by
  rw [h]
  exact ⟨le_self hM (rv_mem hM ht), le_self hM (rv_mem hM ht)⟩

/-- **The order atoms do not translate the equality atom.**  If `Kˣ` has two distinct elements
`u ≠ v` (always the case in the intended model: `K` is an algebraically closed field, so `Kˣ` is
infinite), then the preimages of `u` and `v` under `rv` satisfy *both* order atoms
`iLe (rv s) (rv t)` and `iLe (rv t) (rv s)` while `rv s ≠ rv t`.

So `Axioms.leClassOne` makes `iLe` a genuine *preorder* whose classes are the cosets of `Kˣ`, and
`leF s t ⊓ leF t s` — the only quantifier-free `L_val` reading of "same value" — is strictly weaker
than `pEq (tRv s) (tRv t)`.  Translating the equality atom needs the residue field, i.e. a link
between `rv` and `kAdd`/`kNeg` that the frozen axioms do not state. -/
theorem order_atoms_not_iff_pEq {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {u v : M}
    (hu : iUnits u) (hv : iUnits v) (hne : u ≠ v) :
    ∃ s t : M, iVF s ∧ iVF t ∧ (iLe (iRv s) (iRv t) ∧ iLe (iRv t) (iRv s)) ∧
      iRv s ≠ iRv t := by
  obtain ⟨s, hs, hsu⟩ := rv_surj hM (units_mem_rv hM hu) (units_ne_infty hM hu)
  obtain ⟨t, ht, htv⟩ := rv_surj hM (units_mem_rv hM hv) (units_ne_infty hM hv)
  have hle := units_pairwise_le hM hu hv
  refine ⟨s, t, hs, ht, ?_, ?_⟩
  · rw [hsu, htv]; exact hle
  · simpa only [hsu, htv] using hne

/-! ## 6. `pUnits (rv s)` is `v s = v 1` — exactly, junk case included -/

section UnitsAtom

variable {M : Type} [LRV.Structure M]

/-- **The `L_val`-formula `v s = v 1`**: the preimage of the `L_RV` atom `pUnits (rv s)`. -/
def leOneF {n : ℕ} (s : Language.val.Term (Empty ⊕ Fin n)) :
    Language.val.BoundedFormula Empty n :=
  leF s 1 ⊓ leF 1 s

/-- The semantics of `leOneF s`, in terms of the `rv` of the `1` *of the `VF` sort*. -/
theorem leOneF_eval {n : ℕ} (s : Language.val.Term (Empty ⊕ Fin n)) (x : Fin n → M) :
    valFormulaEval x (leOneF s) ↔
      (iLe (iRv (iVFOne (M := M))) (iRv (valTermEval x s)) ∧
        iLe (iRv (valTermEval x s)) (iRv iVFOne)) := by
  rw [leOneF, valFormulaEval_inf, leF_valTerm_iff, leF_valTerm_iff]
  simp only [valTermEval_one]

/-- The semantics of `leOneF s`: `v s = v 1`, using `rv 1 = 1` (`rv_one_eq`). -/
theorem leOneF_eval' (hM : M ⊨ Axioms.ACVF) {n : ℕ}
    (s : Language.val.Term (Empty ⊕ Fin n)) (x : Fin n → M) :
    valFormulaEval x (leOneF s) ↔
      (iLe (iRVOne (M := M)) (iRv (valTermEval x s)) ∧
        iLe (iRv (valTermEval x s)) iRVOne) := by
  rw [leOneF_eval, rv_one_eq hM]

/-- **The `pUnits` atom at `rv` of a term is exactly the quantifier-free `L_val`-formula
`v s = v 1`, junk case `s = 0` included.** -/
theorem leOneF_iff_pUnits (hM : M ⊨ Axioms.ACVF) {n : ℕ}
    (s : Language.val.Term (Empty ⊕ Fin n)) {x : Fin n → M} (hx : ∀ i, iVF (x i)) :
    valFormulaEval x (leOneF s) ↔
      (pUnits (tRv (valTermToRV s))).Realize (default : Empty → M) x := by
  rw [leOneF_eval' hM, pUnits_realize, realize_tRv, valTermToRV_realize,
    ← iUnits_iff' hM (rv_mem hM (valTermEval_mem hM hx s))]

/-- `v s = v 1` forces `s ≠ 0` (`pUnits` is false at `∞`). -/
theorem leOneF_ne_zero (hM : M ⊨ Axioms.ACVF) {n : ℕ}
    (s : Language.val.Term (Empty ⊕ Fin n)) {x : Fin n → M}
    (h : valFormulaEval x (leOneF s)) : valTermEval x s ≠ iVFZero := by
  intro h0
  rw [leOneF_eval' hM] at h
  rw [h0, rv_zero_eq hM] at h
  exact not_le_infty_one hM h.2

/-- **The junk case `s = 0`**: `pUnits (rv 0)` is false, and so is its `L_val` preimage. -/
theorem pUnits_tRv_zero {k : ℕ} (hM : M ⊨ Axioms.ACVF) (v : Empty → M) (x : Fin k → M) :
    ¬ (pUnits (tRv (tVFZero (n := k)))).Realize v x := by
  rw [pUnits_realize, realize_tRv, realize_tVFZero]
  simpa only [rv_zero_eq hM] using not_units_zero hM

/-- `pUnits (rv 0)` is false. -/
theorem pUnits_iRv_zero (hM : M ⊨ Axioms.ACVF) :
    ¬ iUnits (iRv (iVFZero (M := M))) := by
  simpa only [rv_zero_eq hM] using not_units_zero hM

/-- The junk case of `leOneF`: at the zero term it is false, matching `pUnits_tRv_zero`. -/
theorem leOneF_zero {n : ℕ} (hM : M ⊨ Axioms.ACVF) (x : Fin n → M) :
    ¬ valFormulaEval x (leOneF (0 : Language.val.Term (Empty ⊕ Fin n))) := by
  rw [leOneF_eval' hM, valTermEval_zero, rv_zero_eq hM]
  exact fun h => not_le_infty_one hM h.2

/-- **`K = Kˣ ∪ {0}`** inside `L_val`: the preimage of `pInK (rv s)` is `v s = v 1 ∨ s = 0`. -/
def inKF {n : ℕ} (s : Language.val.Term (Empty ⊕ Fin n)) :
    Language.val.BoundedFormula Empty n :=
  leOneF s ⊔ s =' 0

/-- Equality of two `L_val`-terms, read by `valFormulaEval`. -/
theorem valFormulaEval_equal {n : ℕ} (x : Fin n → M)
    (t u : Language.val.Term (Empty ⊕ Fin n)) :
    valFormulaEval x (t =' u) ↔ valTermEval x t = valTermEval x u :=
  Iff.rfl

/-- The semantics of `inKF s`. -/
theorem inKF_eval (hM : M ⊨ Axioms.ACVF) {n : ℕ}
    (s : Language.val.Term (Empty ⊕ Fin n)) (x : Fin n → M) :
    valFormulaEval x (inKF s) ↔
      ((iLe (iRVOne (M := M)) (iRv (valTermEval x s)) ∧
        iLe (iRv (valTermEval x s)) iRVOne) ∨ valTermEval x s = iVFZero) := by
  rw [inKF, valFormulaEval_sup, leOneF_eval' hM, valFormulaEval_equal, valTermEval_zero]

/-- **`pInK (rv s)` is exactly the `L_val`-formula `v s = v 1 ∨ s = 0`.** -/
theorem inKF_iff_pInK (hM : M ⊨ Axioms.ACVF) {n : ℕ}
    (s : Language.val.Term (Empty ⊕ Fin n)) {x : Fin n → M} (hx : ∀ i, iVF (x i)) :
    valFormulaEval x (inKF s) ↔
      (pInK (tRv (valTermToRV s))).Realize (default : Empty → M) x := by
  have hmem : iVF (valTermEval x s) := valTermEval_mem hM hx s
  have hzero : (valTermEval x s = iVFZero) ↔ (iRv (valTermEval x s) = iRVZero) := by
    constructor
    · intro h; rw [h, rv_zero_eq hM]
    · exact rv_eq_infty hM hmem
  have hR : (pInK (tRv (valTermToRV s))).Realize (default : Empty → M) x ↔
      (iUnits (iRv (valTermEval x s)) ∨ iRv (valTermEval x s) = iRVZero) := by
    simp only [pInK, BoundedFormula.realize_sup, pUnits_realize, realize_tRv,
      valTermToRV_realize, pEq, BoundedFormula.realize_bdEqual, realize_tRVZero]
  rw [inKF_eval hM, hR, ← iUnits_iff' hM (rv_mem hM hmem), hzero]

end UnitsAtom

/-! ## 7. The equality atom, conditional on the repair `rvFibreIff`

`iRv s = iRv t` is not definable in `L_val` from the frozen axioms (see `REPORT.md` §3 and
`order_atoms_not_iff_pEq`).  The missing sentence is the one that makes the fibres of `rv` the
cosets of `1 + M`; with it the equality atom has a quantifier-free `L_val` preimage, and that is
what this section proves.  Nothing else in the file uses `rvFibreIff`. -/

/-- **Suggested repair axiom** (in the style of `Axioms.leMulCompatFull`): `rv x = rv y` iff the two
values agree and, unless `x = 0`, `x - y` has strictly larger value than `x`.  In the intended
model the second conjunct says `resid x = resid y`, so this is exactly the statement that the
fibres of `rv` are the cosets of `1 + M` — the part of the paper's Definition 2.1/2.2 (RV as a
quotient of `VF^×`) that the encoding never writes down.

Read with `pLe a b = iLe (rv a) (rv b)`: `pLe &0 &1 ⊓ pLe &1 &0` is `v x = v y`, and
`pLe (x - y) x ⊓ ¬ pLe x (x - y)` is `v (x - y) > v x`. -/
def rvFibreIff : LRV.Sentence :=
  allSorted ![.vf, .vf]
    (pEq (tRv &0) (tRv &1) ⇔
      ((pLe (tRv &0) (tRv &1) ⊓ pLe (tRv &1) (tRv &0)) ⊓
        (pEq &0 tVFZero ⊔ (pLe (tRv &0) (tRv (tVFAdd &0 (tVFNeg &1))) ⊓
          ∼(pLe (tRv (tVFAdd &0 (tVFNeg &1))) (tRv &0))))))

section EqAtom

variable {M : Type} [LRV.Structure M]

/-- The semantic form of `rvFibreIff`. -/
theorem rv_fibre_iff (hfib : M ⊨ ({rvFibreIff} : LRV.Theory)) {x y : M}
    (hx : iVF x) (hy : iVF y) :
    (iRv x = iRv y) ↔
      ((iLe (iRv x) (iRv y) ∧ iLe (iRv y) (iRv x)) ∧
        (x = iVFZero ∨ (iLe (iRv x) (iRv (iVFAdd x (iVFNeg y))) ∧
          ¬ iLe (iRv (iVFAdd x (iVFNeg y))) (iRv x)))) := by
  have h := allSorted_realize (T := ({rvFibreIff} : LRV.Theory)) hfib
    (ss := ![SortTag.vf, SortTag.vf])
    (φ := (pEq (tRv &0) (tRv &1) ⇔
      ((pLe (tRv &0) (tRv &1) ⊓ pLe (tRv &1) (tRv &0)) ⊓
        (pEq &0 tVFZero ⊔ (pLe (tRv &0) (tRv (tVFAdd &0 (tVFNeg &1))) ⊓
          ∼(pLe (tRv (tVFAdd &0 (tVFNeg &1))) (tRv &0))))))) (by simp [rvFibreIff]) ![x, y] (by
      intro i; fin_cases i <;> simp [hx, hy])
  simpa [pEq, BoundedFormula.realize_bdEqual, BoundedFormula.realize_iff,
    BoundedFormula.realize_inf, BoundedFormula.realize_sup, BoundedFormula.realize_not,
    realize_pLe, realize_tRv, realize_tVFZero, realize_tVFAdd, realize_tVFNeg, realize_tv,
    Term.realize_var, Sum.elim_inr, Function.comp_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons] using h

/-- **The `L_val`-formula `v s = v t` with the residue test**: the preimage of `pEq (rv s) (rv t)`
once `rvFibreIff` is assumed. -/
def leEqF {n : ℕ} (s t : Language.val.Term (Empty ⊕ Fin n)) :
    Language.val.BoundedFormula Empty n :=
  (leF s t ⊓ leF t s) ⊓ (s =' 0 ⊔ (leF (s + -t) s ⊓ ∼(leF s (s + -t))))

@[simp] theorem valTermEval_add {n : ℕ} (x : Fin n → M)
    (a b : Language.val.Term (Empty ⊕ Fin n)) :
    valTermEval x (a + b) = iVFAdd (valTermEval x a) (valTermEval x b) := rfl

@[simp] theorem valTermEval_neg {n : ℕ} (x : Fin n → M)
    (a : Language.val.Term (Empty ⊕ Fin n)) :
    valTermEval x (-a) = iVFNeg (valTermEval x a) := rfl

/-- The negation of an `L_val`-formula, read by `valFormulaEval`. -/
theorem valFormulaEval_not {n : ℕ} (x : Fin n → M)
    (φ : Language.val.BoundedFormula Empty n) :
    valFormulaEval x (∼φ) ↔ ¬ valFormulaEval x φ :=
  Iff.rfl

/-- The semantics of `leEqF s t`, in `L_val`'s own vocabulary. -/
theorem leEqF_eval {n : ℕ} (s t : Language.val.Term (Empty ⊕ Fin n)) (x : Fin n → M) :
    valFormulaEval x (leEqF s t) ↔
      ((iLe (iRv (valTermEval x s)) (iRv (valTermEval x t)) ∧
          iLe (iRv (valTermEval x t)) (iRv (valTermEval x s))) ∧
        (valTermEval x s = iVFZero ∨
          (iLe (iRv (valTermEval x s)) (iRv (iVFAdd (valTermEval x s)
              (iVFNeg (valTermEval x t)))) ∧
            ¬ iLe (iRv (iVFAdd (valTermEval x s) (iVFNeg (valTermEval x t))))
              (iRv (valTermEval x s))))) := by
  simp only [leEqF, valFormulaEval_inf, valFormulaEval_sup, valFormulaEval_equal,
    valFormulaEval_not, valTermEval_zero, leF_valTerm_iff, valTermEval_add, valTermEval_neg]
  tauto

/-- **The equality atom, once `rvFibreIff` is assumed**: `pEq (rv s) (rv t)` is exactly the
quantifier-free `L_val`-formula `leEqF s t`. -/
theorem leEqF_iff_pEq (hM : M ⊨ Axioms.ACVF) (hfib : M ⊨ ({rvFibreIff} : LRV.Theory))
    {n : ℕ} (s t : Language.val.Term (Empty ⊕ Fin n)) {x : Fin n → M}
    (hx : ∀ i, iVF (x i)) :
    valFormulaEval x (leEqF s t) ↔
      (pEq (tRv (valTermToRV s)) (tRv (valTermToRV t))).Realize (default : Empty → M) x := by
  rw [leEqF_eval, pEq, BoundedFormula.realize_bdEqual, realize_tRv, realize_tRv,
    valTermToRV_realize, valTermToRV_realize,
    ← rv_fibre_iff hfib (valTermEval_mem hM hx s) (valTermEval_mem hM hx t)]

end EqAtom

end M2
end SpecialTransformations.Milestone0.Transfer

/-! ## Axiom checks -/

#print axioms SpecialTransformations.Milestone0.Transfer.M2.not_units_zero
#print axioms SpecialTransformations.Milestone0.Transfer.M2.iUnits_iff'
#print axioms SpecialTransformations.Milestone0.Transfer.M2.rv_one_eq
#print axioms SpecialTransformations.Milestone0.Transfer.M2.units_rv_one
#print axioms SpecialTransformations.Milestone0.Transfer.M2.translate_pLe
#print axioms SpecialTransformations.Milestone0.Transfer.M2.leOneF_iff_pUnits
#print axioms SpecialTransformations.Milestone0.Transfer.M2.inKF_iff_pInK
#print axioms SpecialTransformations.Milestone0.Transfer.M2.pUnits_tRv_zero
#print axioms SpecialTransformations.Milestone0.Transfer.M2.leOneF_zero
#print axioms SpecialTransformations.Milestone0.Transfer.M2.rv_one_mul_left
#print axioms SpecialTransformations.Milestone0.Transfer.M2.rv_exists_left_inv
#print axioms SpecialTransformations.Milestone0.Transfer.M2.units_le_one
#print axioms SpecialTransformations.Milestone0.Transfer.M2.units_pairwise_le
#print axioms SpecialTransformations.Milestone0.Transfer.M2.order_atoms_not_iff_pEq
#print axioms SpecialTransformations.Milestone0.Transfer.M2.rv_eq_imp_orderEq
#print axioms SpecialTransformations.Milestone0.Transfer.M2.rv_fibre_iff
#print axioms SpecialTransformations.Milestone0.Transfer.M2.leEqF_eval
#print axioms SpecialTransformations.Milestone0.Transfer.M2.leEqF_iff_pEq

#print axioms Smw1541fr.M1.sentence_iff_of_qfSentence_iff
#print axioms Smw1541fr.M1.not_hasQE_of_qfSentence_equiv
#print axioms Smw1541fr.M1.hasQE_of_qfSeparated
#print axioms SpecialTransformations.Milestone0.Transfer.M2.translate_pLe
#print axioms SpecialTransformations.Milestone0.Transfer.M2.leOneF_iff_pUnits
#print axioms SpecialTransformations.Milestone0.Transfer.M2.rv_one_eq
#print axioms SpecialTransformations.Milestone0.Transfer.M2.not_units_zero

namespace SpecialTransformations.Milestone0.Transfer

/-- Realisation of a sort-guarded existential. -/
theorem exSorted_realize {M : Type} [LRV.Structure M] {k : ℕ} (s : SortTag) (φ : Bf (k + 1))
    (x : Fin k → M) :
    (exSorted s φ).Realize (default : Empty → M) x ↔
      ∃ a : M, (match s with | .vf => iVF a | .rv => iRV a) ∧
        φ.Realize (default : Empty → M) (Fin.snoc x a) := by
  have hterm : ∀ a : M, Term.realize (Sum.elim (default : Empty → M) (Fin.snoc x a))
      (tv k (Nat.lt_succ_self k)) = a := by
    intro a
    show Term.realize (Sum.elim (default : Empty → M) (Fin.snoc x a))
      (Term.var (Sum.inr ⟨k, Nat.lt_succ_self k⟩)) = a
    rw [Term.realize_var]
    simp only [Sum.elim_inr]
    rw [show (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1)) = Fin.last k from rfl, Fin.snoc_last]
  cases s with
  | vf => simp only [exSorted, BoundedFormula.realize_ex, BoundedFormula.realize_inf, sortPred,
      pVF_realize, hterm]
  | rv => simp only [exSorted, BoundedFormula.realize_ex, BoundedFormula.realize_inf, sortPred,
      pRVsort_realize, hterm]

/-- **Nontriviality** as an `L_RV` sentence: some nonzero `VF`-element has value strictly below the
value of `1`.  The transport of `ValPM.axNontrivial`; the frozen `ACVF` lacks it, and without it
the theory admits trivially valued fields on which the target is false. -/
def axNontrivialRV : LRV.Sentence :=
  exSorted .vf (∼(pEq &0 tVFZero) ⊓ ∼(pLe (tRv &0) (tRv tVFOne)))

/-- The theory with item 5 in full and nontriviality. -/
def ACVFplusN : LRV.Theory := ACVFplus ∪ {axNontrivialRV}

theorem axNontrivialRV_mem : axNontrivialRV ∈ ACVFplusN := Or.inr (by simp)

theorem ACVFplus_subset_ACVFplusN : ACVFplus ⊆ ACVFplusN := fun _ h => Or.inl h

/-- A model of the repaired theory with nontriviality has a nontrivial valuation. -/
theorem hasNontrivVal_of_model_ACVFplusN {M : Type} [LRV.Structure M] (hM : M ⊨ ACVFplusN) :
    HasNontrivVal M := by
  have h := hM.realize_of_mem axNontrivialRV axNontrivialRV_mem
  rw [axNontrivialRV] at h
  rw [Sentence.Realize] at h
  simp only [Formula.Realize] at h
  rw [exSorted_realize] at h
  obtain ⟨x, hxVF, hx⟩ := h
  simp only [BoundedFormula.realize_inf, BoundedFormula.realize_not, pEq,
    BoundedFormula.realize_bdEqual, realize_tVFZero, realize_tRv, realize_tVFOne, realize_tv,
    realize_pLe, Sum.elim_inr, Function.comp_apply, Matrix.cons_val_zero] at hx
  exact ⟨x, hxVF, hx.1, hx.2⟩

/-- **The extraction from the fully repaired theory**: no nontriviality hypothesis, no case split. -/
theorem model_ACVF_val_of_model_ACVFplusN {M : Type} [LRV.Structure M]
    (hM : M ⊨ ACVFplusN) :
    @Theory.Model Language.val (VFType (M := M))
      (vfValStruct (hM := model_ACVF_of_model_ACVFplus (Theory.Model.mono hM ACVFplus_subset_ACVFplusN)))
      ValPM.ACVF_val :=
  model_ACVF_val_of_model_ACVFplus (Theory.Model.mono hM ACVFplus_subset_ACVFplusN)
    (hasNontrivVal_of_model_ACVFplusN hM)
end SpecialTransformations.Milestone0.Transfer

#print axioms SpecialTransformations.Milestone0.Transfer.exSorted_realize
#print axioms SpecialTransformations.Milestone0.Transfer.hasNontrivVal_of_model_ACVFplusN
#print axioms SpecialTransformations.Milestone0.Transfer.model_ACVF_val_of_model_ACVFplusN


/-!
# The cover, I: `rv 1 = 1` and the unit atom

`SpecialTransformations.Milestone0.Transfer` has the translation `L_val → L_RV`
(`valFormulaToRVvf`, `VFRestrict`) and its realization lemma.  The transfer of quantifier
elimination needs the **converse**: every `L_RV`-formula is (modulo the axioms) the image of an
`L_val`-formula.  This file builds the pieces of that cover that can be closed.

Contents:

* `rv_one` — `iRv (iVFOne) = iRVOne`.  This is *not* an axiom of the frozen encoding and nobody
  has proved it: `rv` is multiplicative and surjective, so `rv 1` is the identity of the ambient
  `RV`-semigroup, and `iRVOne` is an idempotent, so the two agree.  The derivation below uses
  `rvSurj` twice (through `iRVOne ∈ rv '' VF` and an inverse of a preimage).  Without it the
  paper's `Kˣ` cannot be matched to `v x = v 1` in `L_val`, i.e. `pUnits` has no `L_val` image.
* `iUnits_iff` — the semantic form of `Axioms.leClassOne` (`Kˣ` is the class of `1`).  This is
  `d1`'s target; it is proved here in ten lines because the cover below consumes it.
* `VFTm`, `Frag`, `Frag.toRV`, `Frag.toVal` and `Frag.realize` — the cover on the fragment of
  `L_RV` whose atoms are `v s ≤ v t` (`pLe` on `rv`-terms) and `s ∈ Kˣ` (`pUnits` on `rv`-terms),
  with arbitrarily nested Boolean structure and `VF`-guarded quantifiers.
* `frag_QE` — quantifier elimination for that fragment, from `hasQE_ACVF_val` and the read-back
  `VFRestrict.transfer_of_isQF`, *given* that the `VF` sort of the model models `ValPM.ACVF_val`.

Not done here (and why): RV-sorted equality `rv s = rv t` needs the residue field, so it is not
covered; `Theory.Iff`-level statements at junk tuples are not covered; the hypothesis
`VFType ⊨ ValPM.ACVF_val` is exactly the gap on record (item 5 + `axNontrivial`).
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Axioms
open SpecialTransformations.Milestone0.Transfer

namespace Cover

variable {M : Type} [LRV.Structure M]

/-! ## 1. Members of the frozen theory -/

theorem mem_ACVF_paper {s : LRV.Sentence} (h : s ∈ Axioms.ACVFpaper) : s ∈ Axioms.ACVF := by
  simp only [Axioms.ACVF, Set.mem_union]
  tauto

theorem mem_ACVF_rvGroup {s : LRV.Sentence} (h : s ∈ Axioms.rvGroup) : s ∈ Axioms.ACVF :=
  mem_ACVF_paper (by
    simp only [Axioms.ACVFpaper, Set.mem_union]
    tauto)

theorem mem_ACVF_kField {s : LRV.Sentence} (h : s ∈ Axioms.kField) : s ∈ Axioms.ACVF :=
  mem_ACVF_paper (by
    simp only [Axioms.ACVFpaper, Set.mem_union]
    tauto)

/-! ## 2. The realizers of the constants -/

theorem realize_tRVOne {k : ℕ} (v : Empty ⊕ Fin k → M) : (tRVOne (n := k)).realize v = iRVOne := by
  show FirstOrder.Language.Structure.funMap (L := LRV) Fn.rvOne
      (fun i => Term.realize (L := LRV) v ((fun j : Fin 0 => j.elim0) i)) = iRVOne
  rw [show (fun i => Term.realize (L := LRV) v ((fun j : Fin 0 => j.elim0) i))
      = (fun i => i.elim0) from by funext i; exact i.elim0]
  rfl

/-- The value of the variable that `Fin.snoc` appends. -/
theorem realize_tv_last_apply {k : ℕ} (v : Empty → M) (x : Fin k → M) (a : M) (h : k < k + 1) :
    (tv k h).realize (Sum.elim v (Fin.snoc x a)) = a := by
  rw [show tv k h = tv (⟨k, h⟩ : Fin (k + 1)).1 (⟨k, h⟩ : Fin (k + 1)).2 from rfl, realize_tv]
  simp [Fin.snoc]

theorem snoc_apply_zero_one (x : Fin 1 → M) (a : M) :
    (Fin.snoc (α := fun _ : Fin 2 => M) x a) (0 : Fin 2) = x 0 := by
  simp [Fin.snoc]

theorem snoc_apply_one_one (x : Fin 1 → M) (a : M) :
    (Fin.snoc (α := fun _ : Fin 2 => M) x a) (1 : Fin 2) = a := by
  simp [Fin.snoc]

/-- **`rv` is surjective on `RV` away from `∞`** (`Axioms.rvSurj`), semantically. -/
theorem rvSurj_realize (hM : M ⊨ Axioms.ACVF) {y : M} (hy : iRV y) (hy0 : y ≠ iRVZero) :
    ∃ x : M, iVF x ∧ iRv x = y := by
  have hmem : Axioms.rvSurj ∈ Axioms.ACVF :=
    mem_ACVF_rvAxioms (by simp [Axioms.rvAxioms, Axioms.ofList])
  have h := allSorted_realize hM (ss := ![SortTag.rv])
    (φ := (∼(pEq &0 tRVZero) ⟹ exSorted .vf (pEq (tRv &1) &0))) hmem ![y] (by
      intro i; fin_cases i; simpa using hy)
  simp only [pEq, BoundedFormula.realize_bdEqual, BoundedFormula.realize_imp,
    BoundedFormula.realize_not, exSorted, BoundedFormula.realize_ex, BoundedFormula.realize_inf,
    sortPred, realize_tRVZero, realize_tRv, pVF_realize, Matrix.cons_val_zero,
    realize_tv_last_apply, snoc_apply_zero_one, snoc_apply_one_one] at h
  exact h hy0

/-- **`Kˣ` is the class of `1`** (`Axioms.leClassOne`), semantically. -/
theorem iUnits_iff (hM : M ⊨ Axioms.ACVF) {x : M} (hx : iRV x) (hx0 : x ≠ iRVZero) :
    iUnits x ↔ (iLe (iRVOne (M := M)) x ∧ iLe x iRVOne) := by
  have hmem : Axioms.leClassOne ∈ Axioms.ACVF :=
    mem_ACVF_preorderRV (s := Axioms.leClassOne) (by simp [Axioms.preorderRV, Axioms.ofList])
  have h := allSorted_realize hM (ss := ![SortTag.rv])
    (φ := (pRV &0 ⟹ (pUnits &0 ⇔ (pLe tRVOne &0 ⊓ pLe &0 tRVOne)))) hmem ![x] (by
      intro i; fin_cases i; simpa using hx)
  have h' : x ≠ iRVZero → (iUnits x ↔ (iLe iRVOne x ∧ iLe x iRVOne)) := by
    simpa [pRV_realize, pUnits_realize, realize_pLe, realize_tRVOne] using h
  exact h' hx0

/-- A nonzero `VF`-element has `rv ≠ ∞` (`Axioms.rvEqInfty` contrapositively). -/
theorem rv_ne_zero (hM : M ⊨ Axioms.ACVF) {x : M} (hx : iVF x) (h : x ≠ iVFZero) :
    iRv x ≠ iRVZero :=
  fun hh => h (rv_eq_infty hM hx hh)

/-- Every `RV`-element is `rv` of a `VF`-element (`Axioms.rvSurj`, with `rv 0 = ∞` for the
absorbing element). -/
theorem exists_vf_of_rv (hM : M ⊨ Axioms.ACVF) {a : M} (ha : iRV a) :
    ∃ x : M, iVF x ∧ iRv x = a := by
  by_cases ha0 : a = iRVZero
  · exact ⟨iVFZero, vf_zero_mem hM, by rw [rv_zero_eq hM, ha0]⟩
  · exact rvSurj_realize hM ha ha0

/-! ## 3. The sort of `1` of the `RV` sort, and `rv 1 = 1` -/

/-- `1` of the `RV` sort lies in the `RV` sort (`sdRVOne`). -/
theorem rv_one_mem (hM : M ⊨ Axioms.ACVF) : iRV (iRVOne (M := M)) := by
  have h := sentence_realize hM (φ := Axioms.sdRVOne)
    (mem_ACVF_sortClosure (s := Axioms.sdRVOne) (by simp [Axioms.sortClosure, Axioms.ofList]))
  rw [Axioms.sdRVOne, Sentence.Realize] at h
  simp only [Formula.Realize] at h
  rw [pRVsort_realize, realize_tRVOne] at h
  exact h

/-- `0 ≠ 1` on the `RV` sort (`kField` states it unguarded). -/
theorem iRVZero_ne_iRVOne (hM : M ⊨ Axioms.ACVF) : iRVZero (M := M) ≠ iRVOne := by
  have hmem : (∼(pEq tRVZero tRVOne)) ∈ Axioms.ACVF :=
    mem_ACVF_kField (s := ∼(pEq tRVZero tRVOne)) (by simp [Axioms.kField, Axioms.ofList])
  have h := sentence_realize hM hmem
  rw [Sentence.Realize] at h
  simp only [Formula.Realize, BoundedFormula.realize_not, pEq, BoundedFormula.realize_bdEqual,
    realize_tRVZero, realize_tRVOne] at h
  exact h

/-- `1 ∈ Kˣ` (`Axioms.rvOneMem`). -/
theorem units_one (hM : M ⊨ Axioms.ACVF) : iUnits (iRVOne (M := M)) := by
  have hmem : Axioms.rvOneMem ∈ Axioms.ACVF :=
    mem_ACVF_rvGroup (by simp [Axioms.rvGroup, Axioms.ofList])
  have h := sentence_realize hM hmem
  rw [Axioms.rvOneMem, Sentence.Realize] at h
  simp only [Formula.Realize] at h
  rw [pUnits_realize, realize_tRVOne] at h
  exact h

/-- `×` on the `RV` sort is associative (`Axioms.rvMulAssoc`), semantically. -/
theorem rv_mul_assoc (hM : M ⊨ Axioms.ACVF) {x y z : M} (hx : iRV x) (hy : iRV y) (hz : iRV z) :
    iRVMul (iRVMul x y) z = iRVMul x (iRVMul y z) := by
  have hmem : Axioms.rvMulAssoc ∈ Axioms.ACVF :=
    mem_ACVF_rvGroup (by simp [Axioms.rvGroup, Axioms.ofList])
  have h := allSorted_realize hM hmem ![x, y, z] (by
    intro i; fin_cases i <;> simp [hx, hy, hz])
  simpa only [pEq, BoundedFormula.realize_bdEqual, realize_tRVMul, realize_tv, Term.realize_var,
    Sum.elim_inr, Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Fin.succ_zero_eq_one, Matrix.head_cons] using h

/-- `1` is neutral for `×` on `Kˣ` (`Axioms.rvMulOne`), semantically. -/
theorem rv_mul_one (hM : M ⊨ Axioms.ACVF) {x : M} (hx : iRV x) (hu : iUnits x) :
    iRVMul iRVOne x = x := by
  have hmem : Axioms.rvMulOne ∈ Axioms.ACVF :=
    mem_ACVF_rvGroup (by simp [Axioms.rvGroup, Axioms.ofList])
  have h := allSorted_realize hM hmem ![x] (by intro i; fin_cases i; simpa using hx)
  have h' : iUnits x → iRVMul iRVOne x = x := by
    simpa only [pUnits_realize, BoundedFormula.realize_imp, pEq, BoundedFormula.realize_bdEqual,
      realize_tRVMul, realize_tRVOne, realize_tv, Term.realize_var, Sum.elim_inr,
      Function.comp_apply, Matrix.cons_val_zero] using h
  exact h' hu

/-- **`rv 1 = 1`.**  Not an axiom of the frozen encoding; derived from multiplicativity of `rv`,
`rvSurj`, and the fact that `RV ∖ {0}` is a semigroup with identity `rv 1` in which `iRVOne` is
idempotent and has an inverse.

The chain is `1 = 1·rv 1 = 1·(1·rv y) = (1·1)·rv y = 1·rv y = rv 1`, where `y` is the inverse
of a preimage `x` of `iRVOne` under `rv` (`rvSurj`), which exists because `x ∈ VF` is a field. -/
theorem rv_one (hM : M ⊨ Axioms.ACVF) : iRv (iVFOne (M := M)) = iRVOne := by
  have h1mem : iVF (iVFOne (M := M)) := vf_one_mem hM
  have hg0 : iRv (iVFOne (M := M)) ≠ iRVZero :=
    rv_ne_zero hM h1mem (vf_zero_ne_one hM).symm
  have hh_mem : iRV (iRVOne (M := M)) := rv_one_mem hM
  have hh0 : iRVOne ≠ iRVZero := fun h => iRVZero_ne_iRVOne hM h.symm
  -- a preimage of `iRVOne` under `rv`
  obtain ⟨x, hx, hxone⟩ := rvSurj_realize hM hh_mem hh0
  have hx0 : x ≠ iVFZero := by
    intro h
    rw [h, rv_zero_eq hM] at hxone
    exact hh0 hxone.symm
  obtain ⟨y, hy, hxy⟩ := (vf_mul_inv_or_zero hM hx).resolve_left hx0
  -- `h · rv y = rv 1`
  have key1 : iRv (iVFOne (M := M)) = iRVMul iRVOne (iRv y) := by
    have h := rv_mul_hom hM hx hy
    rw [hxy, hxone] at h
    exact h
  -- `h · rv 1 = h`
  have key2 : iRVOne = iRVMul iRVOne (iRv (iVFOne (M := M))) := by
    have h := rv_mul_hom hM hx h1mem
    rw [vf_mul_one hM hx, hxone] at h
    exact h
  -- `h · h = h`
  have hh : iRVMul iRVOne iRVOne = iRVOne := rv_mul_one hM hh_mem (units_one hM)
  have hyp : iRV (iRv y) := rv_mem hM hy
  have step2 : iRVMul iRVOne (iRv (iVFOne (M := M)))
      = iRVMul iRVOne (iRVMul iRVOne (iRv y)) := by rw [key1]
  have step3 : iRVMul iRVOne (iRVMul iRVOne (iRv y))
      = iRVMul (iRVMul iRVOne iRVOne) (iRv y) :=
    (rv_mul_assoc hM hh_mem hh_mem hyp).symm
  have step4 : iRVMul (iRVMul iRVOne iRVOne) (iRv y) = iRVMul iRVOne (iRv y) := by rw [hh]
  exact key1.trans (key2.trans (step2.trans (step3.trans step4))).symm


/-! ## 4. `VF`-terms and their two readings -/

/-- The `VF`-terms of `L_RV`: the terms built from the `VF`-sorted symbols and the variables.
`L_RV` has a single carrier, so this is a *sub*-term-language of `Tm n`, made into its own
inductive type so that the two translations below are structural recursions. -/
inductive VFTm (n : ℕ) : Type
  /-- the variable `i` -/
  | var : Fin n → VFTm n
  /-- `0` of the `VF` sort -/
  | zero : VFTm n
  /-- `1` of the `VF` sort -/
  | one : VFTm n
  /-- `+` of the `VF` sort -/
  | add : VFTm n → VFTm n → VFTm n
  /-- `-` of the `VF` sort -/
  | neg : VFTm n → VFTm n
  /-- `×` of the `VF` sort -/
  | mul : VFTm n → VFTm n → VFTm n

namespace VFTm

variable {n : ℕ}

/-- The `L_RV`-term underlying a `VF`-term. -/
def toLRV : VFTm n → Tm n
  | var i => tv i.1 i.2
  | zero => tVFZero
  | one => tVFOne
  | add a b => tVFAdd a.toLRV b.toLRV
  | neg a => tVFNeg a.toLRV
  | mul a b => tVFMul a.toLRV b.toLRV

/-- The `L_val`-term underlying a `VF`-term: the same shape, read in the ring language. -/
def toVal : VFTm n → Language.val.Term (Empty ⊕ Fin n)
  | var i => Term.var (Sum.inr i)
  | zero => (0 : Language.val.Term (Empty ⊕ Fin n))
  | one => (1 : Language.val.Term (Empty ⊕ Fin n))
  | add a b => Term.func ValFunc.add ![a.toVal, b.toVal]
  | neg a => Term.func ValFunc.neg ![a.toVal]
  | mul a b => Term.func ValFunc.mul ![a.toVal, b.toVal]

/-- **The term-level cover**: a `VF`-term has the same value read as an `L_RV`-term and as an
`L_val`-term.  No axiom is used. -/
theorem realize_toLRV (s : VFTm n) (x : Fin n → M) :
    (s.toLRV).realize (Sum.elim (default : Empty → M) x) = valTermEval x s.toVal := by
  induction s with
  | var i => rfl
  | zero => simp [toLRV, toVal, realize_tVFZero, valTermEval]
  | one => simp [toLRV, toVal, realize_tVFOne, valTermEval]
  | add a b iha ihb =>
    simp only [toLRV, toVal, realize_tVFAdd, iha, ihb, valTermEval, Matrix.cons_val_zero,
      Matrix.cons_val_one]
  | neg a iha =>
    simp only [toLRV, toVal, realize_tVFNeg, iha, valTermEval, Matrix.cons_val_zero]
  | mul a b iha ihb =>
    simp only [toLRV, toVal, realize_tVFMul, iha, ihb, valTermEval, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons]

/-- A `VF`-term with a tuple of `VF`-elements as parameters is a `VF`-element (the sort-closure
axioms of the encoding). -/
theorem realize_mem (hM : M ⊨ Axioms.ACVF) (s : VFTm n) (x : Fin n → M)
    (hx : ∀ i, iVF (x i)) : iVF ((s.toLRV).realize (Sum.elim (default : Empty → M) x)) := by
  induction s with
  | var i => simpa [toLRV, realize_tv] using hx i
  | zero => simpa [toLRV, realize_tVFZero] using vf_zero_mem hM
  | one => simpa [toLRV, realize_tVFOne] using vf_one_mem hM
  | add a b iha ihb =>
    simp only [toLRV, realize_tVFAdd]
    exact vf_add_mem hM iha ihb
  | neg a iha =>
    simp only [toLRV, realize_tVFNeg]
    exact vf_neg_mem hM iha
  | mul a b iha ihb =>
    simp only [toLRV, realize_tVFMul]
    exact vf_mul_mem hM iha ihb

end VFTm

/-! ## 5. The fragment and its two translations -/

/-- A fragment of `L_RV`: Boolean combinations of the atoms `v s ≤ v t` (i.e. `pLe` on `rv`-terms,
with the reversal of the order) and `s ∈ Kˣ` (i.e. `pUnits` on `rv`-terms, together with the
nonzero condition that makes it a statement about `v s = v 1`), closed under `VF`-guarded
quantification.  Every constructor has an image in `L_RV` (`Frag.toRV`) and in `L_val`
(`Frag.toVal`), and `Frag.realize_toRV_iff` says the two images agree at every `VF`-tuple. -/
inductive Frag : ℕ → Type
  /-- `⊥` -/
  | falsum (n : ℕ) : Frag n
  /-- `v s ≤ v t`, i.e. `pLe (rv t) (rv s)` -/
  | leAtm {n : ℕ} : VFTm n → VFTm n → Frag n
  /-- `s ∈ Kˣ` together with `s ≠ 0`, i.e. `pUnits (rv s)` plus its nonzero condition -/
  | unitAtm {n : ℕ} : VFTm n → Frag n
  /-- implication -/
  | imp {n : ℕ} : Frag n → Frag n → Frag n
  /-- universal quantification over the `VF` sort -/
  | all {n : ℕ} : Frag (n + 1) → Frag n

namespace Frag

/-- The image of a fragment formula in `L_RV`. -/
def toRV : {n : ℕ} → Frag n → Bf n
  | _, falsum _ => BoundedFormula.falsum
  | _, leAtm s t => pLe (tRv t.toLRV) (tRv s.toLRV)
  | _, unitAtm s => pUnits (tRv s.toLRV) ⊓ ∼(pEq s.toLRV tVFZero)
  | _, imp a b => BoundedFormula.imp a.toRV b.toRV
  | _, all φ =>
    BoundedFormula.all (pVF (tv _ (Nat.lt_succ_self _)) ⟹ φ.toRV)

/-- The image of a fragment formula in `L_val`. -/
def toVal : {n : ℕ} → Frag n → Language.val.BoundedFormula Empty n
  | _, falsum _ => BoundedFormula.falsum
  | _, leAtm s t => ValPM.leF s.toVal t.toVal
  | _, unitAtm s =>
    ∼(s.toVal =' (0 : Language.val.Term (Empty ⊕ _))) ⊓
      (ValPM.leF s.toVal (1 : Language.val.Term (Empty ⊕ _)) ⊓
        ValPM.leF (1 : Language.val.Term (Empty ⊕ _)) s.toVal)
  | _, imp a b => BoundedFormula.imp a.toVal b.toVal
  | _, all φ => BoundedFormula.all φ.toVal

end Frag

/-! ## 6. The atoms -/

variable {n : ℕ}

/-- The realisation of an `L_val`-term in `vfStruct`, as a term of the `VF` sort. -/
noncomputable def vfTermEval (hM : M ⊨ Axioms.ACVF) {n : ℕ} (x : Fin n → VFType (M := M))
    (t : Language.val.Term (Empty ⊕ Fin n)) : VFType (M := M) :=
  @Term.realize Language.val (VFType (M := M)) (VFRestrict.vfStruct hM) (Empty ⊕ Fin n)
    (Sum.elim (default : Empty → VFType (M := M)) x) t

/-- The value of an `L_val`-term in `vfStruct`, as an element of `M`. -/
theorem vfTermEval_val (hM : M ⊨ Axioms.ACVF) {n : ℕ} (x : Fin n → VFType (M := M))
    (t : Language.val.Term (Empty ⊕ Fin n)) :
    (vfTermEval hM x t).1 = valTermEval (fun i => (x i).1) t :=
  VFRestrict.realize_term_vf hM x t

/-- `leF` read in `vfStruct`: the realisation of `v a ≤ v b` is `iLe (rv b) (rv a)`, the paper's
order with the reversal. -/
theorem vfStruct_leF (hM : M ⊨ Axioms.ACVF) {n : ℕ} (x : Fin n → VFType (M := M))
    (a b : Language.val.Term (Empty ⊕ Fin n)) :
    (@BoundedFormula.Realize Language.val (VFType (M := M)) (VFRestrict.vfStruct hM) Empty n
        (ValPM.leF a b) (default : Empty → VFType (M := M)) x)
      ↔ iLe (iRv (vfTermEval hM x b).1) (iRv (vfTermEval hM x a).1) := by
  letI : Language.val.Structure (VFType (M := M)) := VFRestrict.vfStruct hM
  rw [show ValPM.leF a b = Relations.boundedFormula ValRel.le ![a, b] from rfl,
    BoundedFormula.realize_rel]
  have h2 : ∀ r : Fin 2 → VFType (M := M),
      Structure.RelMap (L := Language.val) ValRel.le r ↔ iLe (iRv (r 1).1) (iRv (r 0).1) :=
    fun r => VFRestrict.vfStruct_le hM r
  rw [h2]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one, vfTermEval]

/-- **The unit atom.**  `rv a ∈ Kˣ` together with `a ≠ 0` is `v a = v 1`.  (`leClassOne` gives
`Kˣ = ` the class of `1`, and `rv_one` identifies the `RV`-`1` with `rv 1`.) -/
theorem units_atom (hM : M ⊨ Axioms.ACVF) {a : M} (ha : iVF a) (h0 : a ≠ iVFZero) :
    iUnits (iRv a) ↔
      (iLe (iRv (iVFOne (M := M))) (iRv a) ∧
        iLe (iRv a) (iRv (iVFOne (M := M)))) := by
  exact (iUnits_iff hM (rv_mem hM ha) (rv_ne_zero hM ha h0)).trans (by rw [rv_one hM])

/-! ## 7. The cover on the fragment -/

/-- **The cover.**  On the fragment, the `L_RV`-image and the `L_val`-image of a formula are
realised by the same tuple: `L_RV` at the `VF`-elements of `M`, `L_val` in the structure
`vfStruct` on the `VF` sort.  This is the converse of
`VFRestrict.valFormulaToRVvf_realize_VF`. -/
theorem Frag.realize (hM : M ⊨ Axioms.ACVF) :
    ∀ {n : ℕ} (φ : Frag n) (x : Fin n → VFType (M := M)),
      (@BoundedFormula.Realize Language.val (VFType (M := M)) (VFRestrict.vfStruct hM) Empty n
          φ.toVal (default : Empty → VFType (M := M)) x)
        ↔ (@BoundedFormula.Realize LRV M _ Empty n
            φ.toRV (default : Empty → M) (fun i => (x i).1))
  | _, Frag.falsum _, x => Iff.rfl
  | _, Frag.leAtm s t, x => by
    letI : Language.val.Structure (VFType (M := M)) := VFRestrict.vfStruct hM
    rw [Frag.toVal, Frag.toRV, vfStruct_leF hM x]
    rw [realize_pLe, realize_tRv, realize_tRv]
    have e1 : (vfTermEval hM x t.toVal).1 = valTermEval (fun i => (x i).1) t.toVal :=
      vfTermEval_val hM x t.toVal
    have e2 : (vfTermEval hM x s.toVal).1 = valTermEval (fun i => (x i).1) s.toVal :=
      vfTermEval_val hM x s.toVal
    have e3 : (t.toLRV).realize (Sum.elim (default : Empty → M) (fun i => (x i).1))
        = valTermEval (fun i => (x i).1) t.toVal := VFTm.realize_toLRV t _
    have e4 : (s.toLRV).realize (Sum.elim (default : Empty → M) (fun i => (x i).1))
        = valTermEval (fun i => (x i).1) s.toVal := VFTm.realize_toLRV s _
    rw [e1, e2, e3, e4]
  | _, Frag.unitAtm s, x => by
    letI : Language.val.Structure (VFType (M := M)) := VFRestrict.vfStruct hM
    rw [Frag.toVal, Frag.toRV]
    simp only [BoundedFormula.realize_inf, BoundedFormula.realize_not, pUnits_realize,
      realize_tRv, pEq, BoundedFormula.realize_bdEqual, realize_tVFZero]
    rw [vfStruct_leF hM x s.toVal (1 : Language.val.Term (Empty ⊕ _)),
      vfStruct_leF hM x (1 : Language.val.Term (Empty ⊕ _)) s.toVal]
    have e1 : (vfTermEval hM x s.toVal).1 = valTermEval (fun i => (x i).1) s.toVal :=
      vfTermEval_val hM x s.toVal
    have e1' : (vfTermEval hM x (1 : Language.val.Term (Empty ⊕ _))).1 = iVFOne := by
      rw [vfTermEval_val hM x]; rfl
    have e2 : ((s.toLRV).realize (Sum.elim (default : Empty → M) (fun i => (x i).1)))
        = valTermEval (fun i => (x i).1) s.toVal := VFTm.realize_toLRV s _
    have hmem : iVF (valTermEval (fun i => (x i).1) s.toVal) := by
      rw [← e2]
      exact VFTm.realize_mem hM s _ (fun i => (x i).2)
    have es : Term.realize (Sum.elim (default : Empty → VFType (M := M)) x) s.toVal
        = vfTermEval hM x s.toVal := rfl
    have e3 : Term.realize (Sum.elim (default : Empty → VFType (M := M)) x)
        (0 : Language.val.Term (Empty ⊕ _)) = (0 : VFType (M := M)) := rfl
    have hiff : (vfTermEval hM x s.toVal = (0 : VFType (M := M)))
        ↔ (valTermEval (fun i => (x i).1) s.toVal = iVFZero) := by
      rw [Subtype.ext_iff, e1]
      exact Iff.rfl
    rw [es, e3, e1, e1', e2, hiff]
    constructor
    · rintro ⟨hne, h1, h2⟩
      exact ⟨(units_atom hM hmem hne).2 ⟨h1, h2⟩, hne⟩
    · rintro ⟨hu, hne⟩
      exact ⟨hne, (units_atom hM hmem hne).1 hu⟩
  | _, Frag.imp a b, x => by
    letI : Language.val.Structure (VFType (M := M)) := VFRestrict.vfStruct hM
    rw [Frag.toVal, Frag.toRV]
    simp only [BoundedFormula.realize_imp]
    exact ⟨fun h ha => (Frag.realize hM b x).1 (h ((Frag.realize hM a x).2 ha)),
      fun h ha => (Frag.realize hM b x).2 (h ((Frag.realize hM a x).1 ha))⟩
  | _, Frag.all φ, x => by
    letI : Language.val.Structure (VFType (M := M)) := VFRestrict.vfStruct hM
    rw [Frag.toVal, Frag.toRV]
    simp only [BoundedFormula.realize_all, BoundedFormula.realize_imp,
      VFRestrict.realize_pVF_last, Fin.snoc_last]
    constructor
    · intro h a ha
      have h1 := h (⟨a, ha⟩ : VFType (M := M))
      have h2 := (Frag.realize hM φ (Fin.snoc x (⟨a, ha⟩ : VFType (M := M)))).1 h1
      have hs := VFRestrict.val_snoc (M := M) x (⟨a, ha⟩ : VFType (M := M))
      rwa [hs] at h2
    · intro h a
      have h1 := h a.1 a.2
      have hs := VFRestrict.val_snoc (M := M) x a
      rw [← hs] at h1
      exact (Frag.realize hM φ (Fin.snoc x a)).2 h1

/-! ## 8. The cover commutes with the guarded transfer, and quantifier elimination -/

/-- **The cover commutes with `valFormulaToRVvf`**: at every tuple of `VF`-elements, the fragment
formula and the guarded `L_RV`-image of its `L_val`-image agree. -/
theorem frag_iff_valFormulaToRVvf (hM : M ⊨ Axioms.ACVF) {n : ℕ} (φ : Frag n) (x : Fin n → M)
    (hx : ∀ i, iVF (x i)) :
    (φ.toRV).Realize (default : Empty → M) x
      ↔ (VFRestrict.valFormulaToRVvf φ.toVal).Realize (default : Empty → M) x := by
  rw [VFRestrict.valFormulaToRVvf_realize,
    ← VFRestrict.realize_valFormulaVF' hM φ.toVal x hx]
  exact (Frag.realize hM φ (fun i => (⟨x i, hx i⟩ : VFType (M := M)))).symm

/-- A model of `ValPM.ACVF_val` on the `VF` sort realises its formulas as the model relation says. -/
theorem realize_of_valModel (hM : M ⊨ Axioms.ACVF)
    (hval : @Theory.Model Language.val (VFType (M := M)) (VFRestrict.vfStruct hM) ValPM.ACVF_val)
    {n : ℕ} {θ : Language.val.BoundedFormula Empty n} (h : ValPM.ACVF_val ⊨ᵇ θ)
    (x : Fin n → VFType (M := M)) :
    (@BoundedFormula.Realize Language.val (VFType (M := M)) (VFRestrict.vfStruct hM) Empty n
      θ (default : Empty → VFType (M := M)) x) := by
  letI : Language.val.Structure (VFType (M := M)) := VFRestrict.vfStruct hM
  haveI : @Theory.Model Language.val (VFType (M := M)) _ ValPM.ACVF_val := hval
  haveI : Nonempty (VFType (M := M)) := ⟨0⟩
  exact Theory.ModelsBoundedFormula.realize_boundedFormula h _ (v := (default : Empty → VFType (M := M)))
    (xs := x)

/-- **Quantifier elimination on the fragment**, from `QECriterion.HasQEb ValPM.ACVF_val` (QE in
`L_val` for bounded formulas) and the read-back `VFRestrict.transfer_of_isQF`.  At every tuple of
`VF`-elements, a fragment formula is equivalent to the `L_RV`-image of a quantifier-free
`L_val`-formula.

The hypothesis `hval` is where the gaps on record enter: `ValPM.ACVF_val` contains
`axNontrivial`, which the frozen axioms do not imply. -/
theorem frag_QE (hM : M ⊨ Axioms.ACVF)
    (hval : @Theory.Model Language.val (VFType (M := M)) (VFRestrict.vfStruct hM) ValPM.ACVF_val)
    (hQEb : QECriterion.HasQEb ValPM.ACVF_val) {n : ℕ} (φ : Frag n) :
    ∃ ψ : Language.val.BoundedFormula Empty n, ψ.IsQF ∧
      ∀ (y : Fin n → M), (∀ i, iVF (y i)) →
        ((φ.toRV).Realize (default : Empty → M) y
          ↔ (valFormulaToRV ψ).Realize (default : Empty → M) y) := by
  obtain ⟨ψ, hψ, hiff⟩ := hQEb Empty n φ.toVal
  refine ⟨ψ, hψ, fun y hy => ?_⟩
  have hpoint : ∀ x : Fin n → VFType (M := M),
      (@BoundedFormula.Realize Language.val (VFType (M := M)) (VFRestrict.vfStruct hM) Empty n
          φ.toVal (default : Empty → VFType (M := M)) x)
        ↔ (@BoundedFormula.Realize Language.val (VFType (M := M)) (VFRestrict.vfStruct hM) Empty n
          ψ (default : Empty → VFType (M := M)) x) := by
    intro x
    have h2 := realize_of_valModel hM hval hiff x
    have h3 := realize_of_valModel hM hval hiff.not x
    simpa only [BoundedFormula.realize_iff] using h2
  exact (frag_iff_valFormulaToRVvf hM φ y hy).trans
    (VFRestrict.transfer_of_isQF hM hψ hpoint y hy)

/-- **Quantifier elimination on the sentences of the fragment**, unconditional in the QE input:
`hasQE_ACVF_val` (QE in `L_val`, proved in the tree) applies directly, because a fragment formula
in no free variables is an `L_val`-sentence. -/
theorem frag_QE_sentence (hM : M ⊨ Axioms.ACVF)
    (hval : @Theory.Model Language.val (VFType (M := M)) (VFRestrict.vfStruct hM) ValPM.ACVF_val)
    (φ : Frag 0) :
    ∃ ψ : Language.val.BoundedFormula Empty 0, ψ.IsQF ∧
      ((φ.toRV).Realize (default : Empty → M) (default : Fin 0 → M)
        ↔ (valFormulaToRV ψ).Realize (default : Empty → M) (default : Fin 0 → M)) := by
  obtain ⟨ψ, hψ, hiff⟩ := hasQE_ACVF_val Empty φ.toVal
  refine ⟨ψ, hψ, ?_⟩
  have hpoint : ∀ x : Fin 0 → VFType (M := M),
      (@BoundedFormula.Realize Language.val (VFType (M := M)) (VFRestrict.vfStruct hM) Empty 0
          φ.toVal (default : Empty → VFType (M := M)) x)
        ↔ (@BoundedFormula.Realize Language.val (VFType (M := M)) (VFRestrict.vfStruct hM) Empty 0
          ψ (default : Empty → VFType (M := M)) x) := by
    intro x
    have h2 := realize_of_valModel hM hval hiff x
    simpa only [BoundedFormula.realize_iff] using h2
  exact (frag_iff_valFormulaToRVvf hM φ (default : Fin 0 → M) (fun i => i.elim0)).trans
    (VFRestrict.transfer_of_isQF hM hψ hpoint (default : Fin 0 → M) (fun i => i.elim0))

end Cover
/-! ## Axiom checks -/

#print axioms Cover.rv_one
#print axioms Cover.units_atom
#print axioms Cover.VFTm.realize_toLRV
#print axioms Cover.VFTm.realize_mem
#print axioms Cover.Frag.realize
#print axioms Cover.frag_iff_valFormulaToRVvf
#print axioms Cover.frag_QE
#print axioms Cover.frag_QE_sentence


/-!
# From the cover `L_RV → L_val` to quantifier elimination on the `VF` sort

`hasQE_ACVF_val` (`QE/Assembly_val.lean`) is quantifier elimination for `ValPM.ACVF_val` in the
one-sorted language `L_val`.  `m6/ValEvalVF.lean` (swarm `smw14elno`) has the reading of an
`L_val`-formula in the `L_val`-structure `vfStruct hM` on the `VF` sort of an `L_RV`-model, the
guarded translation `valFormulaToRVvf`, and `transfer_of_isQF`, which reads a quantifier-eliminated
`L_val` output back into `L_RV` at tuples of `VF`-elements.

This file puts the two together: **given the cover hypothesis `CoverVF` — every `L_RV`-formula is,
at `VF`-tuples of every model of `ACVF`, equivalent to the image `valFormulaToRVvf θ` of an
`L_val`-formula — every `L_RV`-formula is (uniformly in the model) equivalent at `VF`-tuples to a
quantifier-free `L_RV`-formula**, provided the `VF`-sort structure is a model of `ACVF_val`.

The uniformity matters: the quantifier-free witness `ψ = valFormulaToRV θ'` depends only on the
cover's `θ` and on `ACVF_val`, not on the model or the tuple.  Hence the two-model transfer step
follows immediately at `VF`-tuples (the last theorem).

What is **not** here: tuples with `RV`-valued coordinates.  The cover is stated with a tuple of
`VF`-elements because `L_val` has nothing to say about an `RV`-element; in the intended proof the
`RV`-coordinates are replaced by `VF`-preimages using `Axioms.rvSurj`, which costs existential
quantifiers in `L_val` and is the content of the cover proper (direction e1).  Also missing: the
model hypothesis `S ⊨ ValPM.ACVF_val`, which needs the repaired axiom `leMulCompatFull`
(`m1/Scale.lean`), `m5/VFAlgClosed.lean`, and nontriviality.
-/

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open VFRestrict

namespace CoverBridge

/-! ## 1. `valFormulaToRV` preserves quantifier-freeness

(Copied from `m3/QFTransfer.lean`, swarm `smw14elno`, where it was accepted; it is two inductions
and is reproduced here so that this file is self-contained.) -/

theorem isQF_of_isAtomic {n : ℕ} {φ : Language.val.BoundedFormula Empty n} (h : φ.IsAtomic) :
    (valFormulaToRV φ).IsQF := by
  induction h with
  | equal t₁ t₂ =>
    show BoundedFormula.IsQF ((valTermToRV t₁) =' (valTermToRV t₂))
    exact BoundedFormula.IsAtomic.equal _ _ |>.isQF
  | rel R ts =>
    cases R with
    | le =>
      show BoundedFormula.IsQF (pLe (tRv (valTermToRV (ts 1)))
        (tRv (valTermToRV (ts 0))))
      exact (BoundedFormula.IsAtomic.rel (l := 2) Rel.rvLe
        ![tRv (valTermToRV (ts 1)), tRv (valTermToRV (ts 0))]).isQF

/-- **The translation preserves quantifier-freeness.** -/
theorem isQF_valFormulaToRV {n : ℕ} {φ : Language.val.BoundedFormula Empty n} (h : φ.IsQF) :
    (valFormulaToRV φ).IsQF := by
  induction h with
  | falsum => exact BoundedFormula.IsQF.falsum
  | of_isAtomic hA => exact isQF_of_isAtomic hA
  | imp _ _ ih1 ih2 => exact ih1.imp ih2

/-! ## 2. The cover hypothesis -/

/-- **The cover**, at `VF`-tuples: every `L_RV`-formula is equivalent, in every model of `T`, at
every tuple of `VF`-elements, to the guarded `L_RV`-image of an `L_val`-formula in the same number
of variables.  (The general form must also handle `RV`-valued coordinates, by `Axioms.rvSurj`;
that is the cover proper, direction e1.) -/
def CoverVF (T : LRV.Theory) : Prop :=
  ∀ (n : ℕ) (φ : LRV.BoundedFormula Empty n), ∃ θ : Language.val.BoundedFormula Empty n,
    ∀ (M : Type) [LRV.Structure M], M ⊨ T → ∀ y : Fin n → M, (∀ i, iVF (y i)) →
      (φ.Realize (default : Empty → M) y
        ↔ (valFormulaToRVvf θ).Realize (default : Empty → M) y)

-- The hypothesis `hQEb` is not vacuous: its `n = 0` case is `hasQE_ACVF_val`, unconditionally.
example (φ : Language.val.Formula Empty) :
    ∃ ψ : Language.val.Formula Empty, ψ.IsQF ∧ Theory.Iff ValPM.ACVF_val φ ψ :=
  hasQE_ACVF_val Empty φ

/-! ## 3. The bridge: quantifier elimination at `VF`-tuples -/

/-- **The cover plus quantifier elimination in `L_val` gives a uniform quantifier-free
`L_RV`-formula at `VF`-tuples.** -/
theorem exists_qf_of_coverVF (hQEb : QECriterion.HasQEb (L := Language.val) ValPM.ACVF_val)
    (hC : CoverVF Axioms.ACVF) {n : ℕ} (φ : LRV.BoundedFormula Empty n) :
    ∃ ψ : LRV.BoundedFormula Empty n, ψ.IsQF ∧
      ∀ (M : Type) [LRV.Structure M] (hM : M ⊨ Axioms.ACVF)
        (hS : @Theory.Model Language.val (VFType (M := M)) (vfStruct hM) ValPM.ACVF_val)
        (y : Fin n → M), (∀ i, iVF (y i)) →
        (φ.Realize (default : Empty → M) y
          ↔ ψ.Realize (default : Empty → M) y) := by
  obtain ⟨θ, hθ⟩ := hC n φ
  obtain ⟨θ', hθ'QF, hθ'⟩ := hQEb Empty n θ
  refine ⟨valFormulaToRV θ', isQF_valFormulaToRV hθ'QF, ?_⟩
  intro M _ hM hS y hy
  -- the `L_val`-equivalence, read in the `L_val`-structure on the `VF` sort
  haveI : Nonempty (VFType (M := M)) := ⟨⟨iVFZero, vf_zero_mem hM⟩⟩
  letI : Language.val.Structure (VFType (M := M)) := vfStruct hM
  haveI : @Theory.Model Language.val (VFType (M := M)) inferInstance ValPM.ACVF_val := hS
  have hiff : ∀ x : Fin n → VFType (M := M),
      (@BoundedFormula.Realize Language.val (VFType (M := M)) inferInstance Empty n θ
        (default : Empty → VFType (M := M)) x)
      ↔ (@BoundedFormula.Realize Language.val (VFType (M := M)) inferInstance Empty n θ'
        (default : Empty → VFType (M := M)) x) :=
    fun x => hθ'.realize_bd_iff
  exact (hθ M hM y hy).trans (transfer_of_isQF hM hθ'QF (by
    intro x
    exact hiff x) y hy)

/-- **The two-model transfer at `VF`-tuples.**  Two models of `ACVF` whose `VF`-sort structures
model `ACVF_val`, and two `VF`-tuples with the same quantifier-free `L_RV`-type, satisfy the same
`L_RV`-formulas.  (No nontriviality or triviality enters: this is the `VF`-tuple fragment only.) -/
theorem transfer_at_vf_tuples (hQEb : QECriterion.HasQEb (L := Language.val) ValPM.ACVF_val)
    (hC : CoverVF Axioms.ACVF) {n : ℕ}
    {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF)
    (hSM : @Theory.Model Language.val (VFType (M := M)) (vfStruct hM) ValPM.ACVF_val)
    {N : Type} [LRV.Structure N] (hN : N ⊨ Axioms.ACVF)
    (hSN : @Theory.Model Language.val (VFType (M := N)) (vfStruct hN) ValPM.ACVF_val)
    {y : Fin n → M} {z : Fin n → N} (hy : ∀ i, iVF (y i)) (hz : ∀ i, iVF (z i))
    (hQF : ∀ ψ : LRV.BoundedFormula Empty n, ψ.IsQF →
      (ψ.Realize (default : Empty → M) y ↔ ψ.Realize (default : Empty → N) z))
    (φ : LRV.BoundedFormula Empty n) :
    (φ.Realize (default : Empty → M) y ↔ φ.Realize (default : Empty → N) z) := by
  obtain ⟨ψ, hψQF, hψ⟩ := exists_qf_of_coverVF hQEb hC φ
  exact (hψ M hM hSM y hy).trans ((hQF ψ hψQF).trans (hψ N hN hSN z hz).symm)

end CoverBridge

#print axioms CoverBridge.isQF_valFormulaToRV
#print axioms CoverBridge.exists_qf_of_coverVF
#print axioms CoverBridge.transfer_at_vf_tuples

#print axioms Cover.rv_one
#print axioms Cover.frag_QE_sentence
#print axioms CoverBridge.exists_qf_of_coverVF
#print axioms CoverBridge.transfer_at_vf_tuples


set_option linter.style.haveILetI false

open FirstOrder FirstOrder.Language

universe u v

namespace BCompCore

variable {L : FirstOrder.Language.{u, v}}

/-!
# The compactness argument for bounded formulas

`BoundedFormula.toFormula : BoundedFormula α n → Formula (α ⊕ Fin n)` has no converse in
Mathlib, and the formula-level compactness argument produces its output on the `Formula` side
while `QEExStep` consumes `BoundedFormula α n`. This file removes that obstruction by running
the whole argument in `BoundedFormula α n`, using `toFormula` **only on the way into**
compactness: given a finite set of `Formula`s in the image, the corresponding bounded formulas
are chosen by `Finset.attach` plus choice, and the witness is pushed forward again. No inverse
of `toFormula` is needed.

Contents, all in `BoundedFormula α n`:
* `exists_realize_bounded` — compactness for bounded formulas;
* `lifsup`/`liinf` with `isQF_lifsup`/`isQF_liinf` and `realize_lifsup`/`realize_liinf`;
* `exists_qf_imp_bounded` — isolation: under QF-type invariance for `β`, an assignment
  satisfying `β` is separated from its complement by a QF formula implying `β`.

Not yet done: the cover and the final `QEExStep` assembly, which is mechanical given
`exists_qf_imp_bounded` and `exists_realize_bounded`.
-/

/-! ## Quantifier elimination, formula level

`HasQE T` is the formula-level statement that every `L`-formula is `T`-equivalent to a
quantifier-free one.  It has the same shape as `SpecialTransformations.Milestone0.HasQE`
(`Milestone0/Encoding.lean`), only at a general language `L`. -/

/-- `T` admits quantifier elimination. -/
def HasQE (T : L.Theory) : Prop :=
  ∀ (α : Type u) (φ : L.Formula α), ∃ ψ : L.Formula α, ψ.IsQF ∧ T ⊨ᵇ (φ ⇔ ψ)

/-! ## Finite conjunctions and disjunctions -/

section Finite

variable {α : Type u} {β : Type*}

lemma isQF_listFoldr_sup (l : List β) (f : β → L.Formula α) (h : ∀ b ∈ l, (f b).IsQF) :
    (l.map f).foldr (· ⊔ ·) ⊥ |>.IsQF := by
  induction l with
  | nil => exact BoundedFormula.isQF_bot
  | cons a l ih =>
      rw [List.map_cons, List.foldr_cons]
      exact (h a (by simp)).sup (ih (fun b hb => h b (by simp [hb])))

lemma isQF_listFoldr_inf (l : List β) (f : β → L.Formula α)
    (h : ∀ b ∈ l, (f b).IsQF) : (l.map f).foldr (· ⊓ ·) ⊤ |>.IsQF := by
  induction l with
  | nil => exact BoundedFormula.IsQF.top
  | cons a l ih =>
      rw [List.map_cons, List.foldr_cons]
      exact (h a (by simp)).inf (ih (fun b hb => h b (by simp [hb])))

/-- A finite disjunction of quantifier-free formulas is quantifier-free. -/
lemma isQF_iSup {β : Type*} [Finite β] (f : β → L.Formula α) (h : ∀ b, (f b).IsQF) :
    (Formula.iSup f).IsQF := by
  classical
  rw [Formula.iSup, BoundedFormula.iSup]
  exact isQF_listFoldr_sup _ f (fun b _ => h b)

/-- A finite conjunction of quantifier-free formulas is quantifier-free. -/
lemma isQF_iInf {β : Type*} [Finite β] (f : β → L.Formula α) (h : ∀ b, (f b).IsQF) :
    (Formula.iInf f).IsQF := by
  classical
  rw [Formula.iInf, BoundedFormula.iInf]
  exact isQF_listFoldr_inf _ f (fun b _ => h b)

/-- The realization of a finite disjunction of formulas. -/
lemma realize_iSup {β : Type*} [Finite β] (f : β → L.Formula α) {M : Type*} [L.Structure M]
    (v : α → M) : (Formula.iSup f).Realize v ↔ ∃ b, (f b).Realize v :=
  BoundedFormula.realize_iSup

/-- The realization of a finite conjunction of formulas. -/
lemma realize_iInf {β : Type*} [Finite β] (f : β → L.Formula α) {M : Type*} [L.Structure M]
    (v : α → M) : (Formula.iInf f).Realize v ↔ ∀ b, (f b).Realize v :=
  BoundedFormula.realize_iInf

end Finite

/-! ## Compactness for a set of formulas with free variables -/

/-- **Compactness, realization form.** If every finite set of formulas taken from `Γ` can be
realized together with `φ` in a model of `T`, then `Γ` itself can be realized together with `φ`. -/
theorem exists_model_realize_of_finset {α : Type u} {T : L.Theory} {Γ : Set (L.Formula α)}
    {φ : L.Formula α}
    (h : ∀ Γ0 : Finset (L.Formula α), (∀ ψ ∈ Γ0, ψ ∈ Γ) →
      ∃ (M : Theory.ModelType.{u, v, max u v} T) (v : α → M.Carrier),
        (∀ ψ ∈ Γ0, ψ.Realize v) ∧ φ.Realize v) :
    ∃ (M : Theory.ModelType.{u, v, max u v} T) (v : α → M.Carrier),
      (∀ ψ ∈ Γ, ψ.Realize v) ∧ φ.Realize v := by
  classical
  set U : (L[[α]]).Theory :=
    (L.lhomWithConstants α).onTheory T ∪ Formula.equivSentence '' Γ ∪
      {Formula.equivSentence φ} with hUdef
  have hfin : U.IsFinitelySatisfiable := by
    intro U0 hU0
    -- the part of `Γ` that shows up in `U0`
    set Γ0 : Finset (L.Formula α) :=
      (U0.filter (fun s => s ∈ Formula.equivSentence '' Γ)).image
        (fun s => Formula.equivSentence.symm s) with hΓ0def
    have hΓ0 : ∀ ψ ∈ Γ0, ψ ∈ Γ := by
      intro ψ hψ
      obtain ⟨s, hs, hseq⟩ := Finset.mem_image.mp hψ
      obtain ⟨-, hs2⟩ := Finset.mem_filter.mp hs
      obtain ⟨ψ', hψ', hψ'eq⟩ := (Set.mem_image _ _ _).mp hs2
      rw [← hseq, ← hψ'eq, Equiv.symm_apply_apply]
      exact hψ'
    obtain ⟨M, v, hv, hφv⟩ := h Γ0 hΓ0
    letI : (constantsOn α).Structure M.Carrier := constantsOn.structure v
    have hmem : ∀ s ∈ U0, M.Carrier ⊨ s := by
      intro s hs
      have hsU : s ∈ U := hU0 hs
      simp only [hUdef, Set.mem_union, Set.mem_image, Set.mem_singleton_iff] at hsU
      rcases hsU with (hsT | ⟨ψ, hψ, hψs⟩) | hφs
      · exact ((LHom.onTheory_model (L.lhomWithConstants α) T).2 M.is_model).realize_of_mem s hsT
      · rw [← hψs] at hs ⊢
        refine (Formula.realize_equivSentence M.Carrier ψ).2 (hv ψ ?_)
        rw [hΓ0def]
        exact Finset.mem_image.mpr
          ⟨Formula.equivSentence ψ, Finset.mem_filter.mpr ⟨hs, ⟨ψ, hψ, rfl⟩⟩, by simp⟩
      · rw [hφs]
        exact (Formula.realize_equivSentence M.Carrier φ).2 hφv
    haveI : M.Carrier ⊨ (U0 : (L[[α]]).Theory) := ⟨fun s hs => hmem s hs⟩
    exact Theory.Model.isSatisfiable M.Carrier
  obtain ⟨N⟩ := Theory.isSatisfiable_iff_isFinitelySatisfiable.2 hfin
  have hNU : ∀ s ∈ U, N.Carrier ⊨ s := fun s hs => N.is_model.realize_of_mem s hs
  letI : L.Structure N.Carrier := (L.lhomWithConstants α).reduct N.Carrier
  have hNT : N.Carrier ⊨ T :=
    (LHom.onTheory_model (L.lhomWithConstants α) T).1
      ⟨fun s hs => hNU s (by rw [hUdef]; exact Or.inl (Or.inl hs))⟩
  refine ⟨Theory.ModelType.of T N.Carrier, fun a => (L.con a : N.Carrier), ?_, ?_⟩
  · intro ψ hψ
    refine (Formula.realize_equivSentence N.Carrier ψ).1 (hNU _ ?_)
    rw [hUdef]
    exact Or.inl (Or.inr ⟨ψ, hψ, rfl⟩)
  · refine (Formula.realize_equivSentence N.Carrier φ).1 (hNU _ ?_)
    rw [hUdef]
    exact Or.inr rfl


end BCompCore

namespace BComp

open BCompCore

variable {L : FirstOrder.Language.{u, v}}

/-- `T`-equivalence of bounded formulas with the same context. -/
def IffB (T : L.Theory) {α : Type u} {n : ℕ} (φ ψ : L.BoundedFormula α n) : Prop :=
  ∀ (M : Theory.ModelType.{u, v, max u v} T) (v : α → M.Carrier) (xs : Fin n → M.Carrier),
    (φ.Realize v xs ↔ ψ.Realize v xs)

/-- One existential quantifier in front of a quantifier-free formula can be removed. -/
def QEExStep (T : L.Theory) : Prop :=
  ∀ (α : Type u) (n : ℕ) (θ : L.BoundedFormula α (n + 1)), θ.IsQF →
    ∃ ψ : L.BoundedFormula α n, ψ.IsQF ∧ IffB T θ.ex ψ

/-- **Compactness for bounded formulas.** Only the *forward* map `toFormula` is used: finite sets
are pulled back along membership in its image by choice, which needs no inverse. -/
theorem exists_realize_bounded {α : Type u} {n : ℕ} {T : L.Theory}
    {Γ : Set (L.BoundedFormula α n)} {β : L.BoundedFormula α n}
    (h : ∀ Γ0 : Finset (L.BoundedFormula α n), (∀ ψ ∈ Γ0, ψ ∈ Γ) →
      ∃ (M : Theory.ModelType.{u, v, max u v} T) (v : α → M.Carrier) (xs : Fin n → M.Carrier),
        (∀ ψ ∈ Γ0, ψ.Realize v xs) ∧ β.Realize v xs) :
    ∃ (M : Theory.ModelType.{u, v, max u v} T) (v : α → M.Carrier) (xs : Fin n → M.Carrier),
      (∀ ψ ∈ Γ, ψ.Realize v xs) ∧ β.Realize v xs := by
  classical
  set Γ' : Set (L.Formula (α ⊕ Fin n)) := BoundedFormula.toFormula '' Γ with hΓ'def
  have hfin : ∀ Γ0 : Finset (L.Formula (α ⊕ Fin n)), (∀ ψ ∈ Γ0, ψ ∈ Γ') →
      ∃ (M : Theory.ModelType.{u, v, max u v} T) (V : α ⊕ Fin n → M.Carrier),
        (∀ ψ ∈ Γ0, ψ.Realize V) ∧ β.toFormula.Realize V := by
    intro Γ0 hΓ0
    choose f hfΓ hfeq using fun (ψ : ↥Γ0) => (Set.mem_image _ _ _).mp (hΓ0 ψ.1 ψ.2)
    set Γ0' : Finset (L.BoundedFormula α n) := Γ0.attach.image f with hΓ0'def
    have hΓ0'mem : ∀ ψ ∈ Γ0', ψ ∈ Γ := by
      intro ψ hψ
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hψ
      exact hfΓ j
    obtain ⟨M, v, xs, hall, hβ⟩ := h Γ0' hΓ0'mem
    refine ⟨M, Sum.elim v xs, ?_, ?_⟩
    · intro ψ hψ
      have hmem : f ⟨ψ, hψ⟩ ∈ Γ0' :=
        Finset.mem_image.mpr ⟨⟨ψ, hψ⟩, Finset.mem_attach _ _, rfl⟩
      have h1 := hall _ hmem
      have h2 : (f ⟨ψ, hψ⟩).toFormula = ψ := hfeq ⟨ψ, hψ⟩
      rw [← h2, BoundedFormula.realize_toFormula]
      simpa using h1
    · rw [BoundedFormula.realize_toFormula]
      simpa using hβ
  obtain ⟨M, V, hV, hβV⟩ :=
    BCompCore.exists_model_realize_of_finset (T := T) (Γ := Γ') (φ := β.toFormula) hfin
  refine ⟨M, V ∘ Sum.inl, V ∘ Sum.inr, ?_, ?_⟩
  · intro ψ hψ
    have h1 := hV _ (Set.mem_image_of_mem _ hψ)
    rwa [BoundedFormula.realize_toFormula] at h1
  · have h1 := hβV
    rwa [BoundedFormula.realize_toFormula] at h1

end BComp

namespace BComp

open BCompCore

variable {L : FirstOrder.Language.{u, v}}

/-- Finite disjunction of bounded formulas, by a list fold. -/
noncomputable def lifsup {α : Type u} {n : ℕ} (l : List (L.BoundedFormula α n)) :
    L.BoundedFormula α n :=
  l.foldr (· ⊔ ·) ⊥

/-- Finite conjunction of bounded formulas, by a list fold. -/
noncomputable def liinf {α : Type u} {n : ℕ} (l : List (L.BoundedFormula α n)) :
    L.BoundedFormula α n :=
  l.foldr (· ⊓ ·) ⊤

theorem isQF_lifsup {α : Type u} {n : ℕ} {l : List (L.BoundedFormula α n)}
    (h : ∀ ψ ∈ l, ψ.IsQF) : (lifsup l).IsQF := by
  induction l with
  | nil => exact BoundedFormula.isQF_bot
  | cons a t ih =>
    exact BoundedFormula.IsQF.sup (h a (List.mem_cons_self))
      (ih fun ψ hψ => h ψ (List.mem_cons_of_mem _ hψ))

theorem isQF_liinf {α : Type u} {n : ℕ} {l : List (L.BoundedFormula α n)}
    (h : ∀ ψ ∈ l, ψ.IsQF) : (liinf l).IsQF := by
  induction l with
  | nil => exact BoundedFormula.IsQF.top
  | cons a t ih =>
    exact BoundedFormula.IsQF.inf (h a (List.mem_cons_self))
      (ih fun ψ hψ => h ψ (List.mem_cons_of_mem _ hψ))

theorem realize_lifsup {α : Type u} {n : ℕ} {l : List (L.BoundedFormula α n)}
    {M : Type*} [L.Structure M] (v : α → M) (xs : Fin n → M) :
    (lifsup l).Realize v xs ↔ ∃ ψ ∈ l, ψ.Realize v xs := by
  induction l with
  | nil => simp [lifsup, BoundedFormula.realize_bot]
  | cons a t ih =>
    rw [show lifsup (a :: t) = a ⊔ lifsup t from rfl, BoundedFormula.realize_sup, ih]
    simp only [List.mem_cons]
    constructor
    · rintro (h | ⟨ψ, hψ, hreal⟩)
      · exact ⟨a, Or.inl rfl, h⟩
      · exact ⟨ψ, Or.inr hψ, hreal⟩
    · rintro ⟨ψ, (rfl | hψ), hreal⟩
      · exact Or.inl hreal
      · exact Or.inr ⟨ψ, hψ, hreal⟩

theorem realize_liinf {α : Type u} {n : ℕ} {l : List (L.BoundedFormula α n)}
    {M : Type*} [L.Structure M] (v : α → M) (xs : Fin n → M) :
    (liinf l).Realize v xs ↔ ∀ ψ ∈ l, ψ.Realize v xs := by
  induction l with
  | nil => simp [liinf, BoundedFormula.realize_top]
  | cons a t ih =>
    rw [show liinf (a :: t) = a ⊓ liinf t from rfl, BoundedFormula.realize_inf, ih]
    simp only [List.mem_cons]
    constructor
    · rintro ⟨h, ht⟩ ψ (rfl | hψ)
      · exact h
      · exact ht ψ hψ
    · intro h
      exact ⟨h a (Or.inl rfl), fun ψ hψ => h ψ (Or.inr hψ)⟩

/-- **Isolation**, bounded form. -/
theorem exists_qf_imp_bounded {α : Type u} {n : ℕ} {T : L.Theory} {β : L.BoundedFormula α n}
    (Hβ : ∀ (M N : Theory.ModelType.{u, v, max u v} T) (v : α → M.Carrier)
      (xs : Fin n → M.Carrier) (w : α → N.Carrier) (ys : Fin n → N.Carrier),
      (∀ ψ : L.BoundedFormula α n, ψ.IsQF → (ψ.Realize v xs ↔ ψ.Realize w ys)) →
      (β.Realize v xs ↔ β.Realize w ys))
    (M : Theory.ModelType.{u, v, max u v} T) (v : α → M.Carrier) (xs : Fin n → M.Carrier)
    (hβ : β.Realize v xs) :
    ∃ ψ : L.BoundedFormula α n, ψ.IsQF ∧ ψ.Realize v xs ∧
      ∀ (N : Theory.ModelType.{u, v, max u v} T) (w : α → N.Carrier) (ys : Fin n → N.Carrier),
        ψ.Realize w ys → β.Realize w ys := by
  classical
  by_contra hcon
  push Not at hcon
  set Γ : Set (L.BoundedFormula α n) := {ψ | ψ.IsQF ∧ ψ.Realize v xs} with hΓdef
  have hfin : ∀ Γ0 : Finset (L.BoundedFormula α n), (∀ ψ ∈ Γ0, ψ ∈ Γ) →
      ∃ (N : Theory.ModelType.{u, v, max u v} T) (w : α → N.Carrier) (ys : Fin n → N.Carrier),
        (∀ ψ ∈ Γ0, ψ.Realize w ys) ∧ β.not.Realize w ys := by
    intro Γ0 hΓ0
    have hq : ∀ ψ ∈ Γ0.val.toList, ψ.IsQF :=
      fun ψ hψ => (hΓ0 ψ (Finset.mem_val.mp (Multiset.mem_toList.mp hψ))).1
    have hr : ∀ ψ ∈ Γ0.val.toList, ψ.Realize v xs :=
      fun ψ hψ => (hΓ0 ψ (Finset.mem_val.mp (Multiset.mem_toList.mp hψ))).2
    obtain ⟨N, w, ys, h1, h2⟩ :=
      hcon _ (isQF_liinf hq) ((realize_liinf v xs).2 hr)
    exact ⟨N, w, ys,
      fun ψ hψ => (realize_liinf w ys).1 h1 ψ
        (Multiset.mem_toList.mpr (Finset.mem_val.mpr hψ)),
      (BoundedFormula.realize_not).2 h2⟩
  obtain ⟨N, w, ys, hw, hnβ⟩ := exists_realize_bounded (T := T) hfin
  have htypes : ∀ ψ : L.BoundedFormula α n, ψ.IsQF → (ψ.Realize v xs ↔ ψ.Realize w ys) := by
    intro ψ hψ
    constructor
    · intro hvψ
      exact hw ψ ⟨hψ, hvψ⟩
    · intro hwψ
      by_contra hvψ
      have hcontr := hw ψ.not ⟨hψ.not, (BoundedFormula.realize_not).2 hvψ⟩
      rw [BoundedFormula.realize_not] at hcontr
      exact hcontr hwψ
  have hiff := Hβ M N v xs w ys htypes
  rw [BoundedFormula.realize_not] at hnβ
  exact hnβ (hiff.mp hβ)

/-! ## The cover and the assembly -/

/-- **`QFExDetermined` gives `QEExStep`.** The cover is produced by contradiction: if no finite
set of quantifier-free consequences covered `θ.ex`, bounded compactness would give a tuple
satisfying `θ.ex` and falsifying every quantifier-free consequence of it, contradicting the
isolation lemma. -/
theorem qeExStep_of_qfDet {T : L.Theory}
    (H : ∀ (α : Type u) (n : ℕ) (θ : L.BoundedFormula α (n + 1)), θ.IsQF →
      ∀ (M N : Theory.ModelType.{u, v, max u v} T) (v : α → M.Carrier)
        (xs : Fin n → M.Carrier) (w : α → N.Carrier) (ys : Fin n → N.Carrier),
        (∀ ψ : L.BoundedFormula α n, ψ.IsQF → (ψ.Realize v xs ↔ ψ.Realize w ys)) →
        ((θ.ex).Realize v xs ↔ (θ.ex).Realize w ys)) :
    QEExStep (L := L) T := by
  intro α n θ hθ
  classical
  have Hβ := H α n θ hθ
  set Ψ : Set (L.BoundedFormula α n) :=
    {ψ | ψ.IsQF ∧ ∀ (M : Theory.ModelType.{u, v, max u v} T) (v : α → M.Carrier)
      (xs : Fin n → M.Carrier), ψ.Realize v xs → (θ.ex).Realize v xs} with hΨdef
  have hcov : ∃ Ψ0 : Finset (L.BoundedFormula α n), (∀ ψ ∈ Ψ0, ψ ∈ Ψ) ∧
      ∀ (M : Theory.ModelType.{u, v, max u v} T) (v : α → M.Carrier) (xs : Fin n → M.Carrier),
        (θ.ex).Realize v xs → (lifsup Ψ0.val.toList).Realize v xs := by
    by_contra hno
    push Not at hno
    set Γ : Set (L.BoundedFormula α n) := {η | ∃ ψ ∈ Ψ, ψ.not = η} with hΓdef
    have hfin : ∀ Γ0 : Finset (L.BoundedFormula α n), (∀ η ∈ Γ0, η ∈ Γ) →
        ∃ (M : Theory.ModelType.{u, v, max u v} T) (v : α → M.Carrier)
          (xs : Fin n → M.Carrier),
          (∀ η ∈ Γ0, η.Realize v xs) ∧ (θ.ex).Realize v xs := by
      intro Γ0 hΓ0
      have hchoice : ∀ η : ↥Γ0, ∃ ψ ∈ Ψ, ψ.not = η.1 := fun η => hΓ0 η.1 η.2
      choose f hfΨ hfeq using hchoice
      set Ψ0 : Finset (L.BoundedFormula α n) := Γ0.attach.image f with hΨ0def
      have hΨ0 : ∀ ψ ∈ Ψ0, ψ ∈ Ψ := by
        intro ψ hψ
        obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hψ
        exact hfΨ j
      obtain ⟨M, v, xs, hθex, hnoψ⟩ := hno Ψ0 hΨ0
      refine ⟨M, v, xs, ?_, hθex⟩
      intro η hη
      have hmem : f ⟨η, hη⟩ ∈ Ψ0 :=
        Finset.mem_image.mpr ⟨⟨η, hη⟩, Finset.mem_attach _ _, rfl⟩
      have hfalse : ¬ (f ⟨η, hη⟩).Realize v xs := by
        intro htrue
        exact hnoψ ((realize_lifsup v xs).2 ⟨_, Multiset.mem_toList.mpr hmem, htrue⟩)
      have heq : (f ⟨η, hη⟩).not = η := hfeq ⟨η, hη⟩
      rw [← heq, BoundedFormula.realize_not]
      exact hfalse
    obtain ⟨M, v, xs, hΓ0, hθex⟩ := exists_realize_bounded (T := T) hfin
    obtain ⟨ψ0, hqf0, htrue0, himp0⟩ := exists_qf_imp_bounded (T := T) Hβ M v xs hθex
    have hmemΨ : ψ0 ∈ Ψ := ⟨hqf0, himp0⟩
    have hnotmem : ψ0.not ∈ Γ := ⟨ψ0, hmemΨ, rfl⟩
    have hcontra := hΓ0 ψ0.not hnotmem
    rw [BoundedFormula.realize_not] at hcontra
    exact hcontra htrue0
  obtain ⟨Ψ0, hΨ0, hcov⟩ := hcov
  refine ⟨lifsup Ψ0.val.toList,
    isQF_lifsup (fun ψ hψ => (hΨ0 ψ (Multiset.mem_toList.mp hψ)).1), ?_⟩
  intro M v xs
  constructor
  · intro h
    exact hcov M v xs h
  · intro h
    obtain ⟨ψ, hψl, hψtrue⟩ := (realize_lifsup v xs).1 h
    exact (hΨ0 ψ (Multiset.mem_toList.mp hψl)).2 M v xs hψtrue

end BComp


#print axioms BComp.exists_realize_bounded
#print axioms BComp.exists_qf_imp_bounded
#print axioms BComp.isQF_lifsup
#print axioms BComp.realize_liinf

#print axioms BComp.qeExStep_of_qfDet


/-!
# `QFTypeDetermines ⟹ HasQE`: the compactness step

`QE/Assembly_val.lean` records this as *the* missing implication between the semantic
Shoenfield/back-and-forth machinery and the syntactic `QEExStep`:

> What is still missing is `QFExDetermined → QEExStep`, and the obstruction is concrete:
> `BoundedFormula.toFormula : BoundedFormula α n → Formula (α ⊕ Fin n)` has no converse in
> Mathlib.

`QE/Bounded_compactness.lean` (compiled here as the module `BComp`, namespaces renamed to
`BCompCore`/`BComp` to avoid a clash with the copy of `ShoenfieldQE` inside `Assembly_val`) proves
exactly that implication, at the level of bounded formulas, by running the compactness argument
through `toFormula` only on the way *into* compactness.  This file supplies the missing glue: the
`IffB` of that file is the `Theory.Iff` of Mathlib (the universes match on the nose), so
`QEExStep` transfers, and `QECriterion.HasQE_of_QEExStep` turns it into quantifier elimination.

Nothing here is specific to `L_RV`; it is the general step, and it lets the final assembly take
`QFTypeDetermines` (the two-model QF-type criterion, which is what the back-and-forth produces)
as its only model-theoretic hypothesis.
-/

open FirstOrder FirstOrder.Language

namespace QFComp

variable {L : FirstOrder.Language.{0, 0}} {T : L.Theory}

/-- `IffB` (the bounded-formula equivalence of `QE/Bounded_compactness.lean`) is `Theory.Iff`. -/
theorem iffB_iff {α : Type} {n : ℕ} {φ ψ : L.BoundedFormula α n} :
    BComp.IffB T φ ψ ↔ Theory.Iff T φ ψ where
  mp h M v xs := by
    rw [BoundedFormula.realize_iff]
    exact h M v xs
  mpr h M v xs := by
    have := h M v xs
    rwa [BoundedFormula.realize_iff] at this

/-- The universal QE step from QF-type determination. -/
theorem qeExStep_of_qfTypeDetermines (h : QECriterion.QFTypeDetermines T) :
    QECriterion.QEExStep T := by
  intro α n θ hθ
  obtain ⟨ψ, hψ, hiff⟩ :=
    BComp.qeExStep_of_qfDet (T := T)
      (fun α n θ _ M N v xs w ys hQF =>
        h α n (M : Type) (inferInstance : (M : Type) ⊨ T) (N : Type)
          (inferInstance : (N : Type) ⊨ T) v xs w ys hQF θ.ex)
      α n θ hθ
  exact ⟨ψ, hψ, (iffB_iff).1 hiff⟩

/-- **The compactness step**: QF-type determination gives quantifier elimination. -/
theorem hasQE_of_qfTypeDetermines (h : QECriterion.QFTypeDetermines T) :
    QECriterion.HasQE T :=
  QECriterion.HasQE_of_QEExStep (qeExStep_of_qfTypeDetermines h)

end QFComp

#print axioms QFComp.hasQE_of_qfTypeDetermines


/-!
# Final assembly of the `L_RV` quantifier-elimination target, with named hypotheses

The frozen target is `SpecialTransformations.Milestone0.HasQE Axioms.ACVF`
(`theorem_2_3_quantifier_elimination`).  `QE-PLAN.md` records that it cannot be reached against
the frozen axioms as they stand (two defects: item 5 transcribed as multiplication by `Kˣ`
instead of scaling, and no nontriviality axiom, so trivially valued models are models too), and
that the repair is the one sentence `leMulCompatFull` below.  This file assembles the reduction
for the repaired theory

  `ACVFplus = ACVF ∪ {leMulCompatFull}`

into three named model-theoretic hypotheses, and proves every step in between, so that what
remains missing is exactly the cover `L_RV → L_val` (direction e1), the trivial-valuation case
(direction e4), and the separation of the two cases.

Shape, in the house style of `theorem_2_3_of_hypotheses` (`QE/Reduction_assembly.lean`):

  `NontrivialTransfer` + `TrivialTransfer` + `CaseSeparation` + `CaseSplit`
      ⟹ `QECriterion.QFTypeDetermines ACVFplus`      (proved here)
      ⟹ `QECriterion.HasQE ACVFplus`                  (**proved here** from
                                                        `QFComp.hasQE_of_qfTypeDetermines`)

`QFComp.hasQE_of_qfTypeDetermines` is the compactness step that `QE/Assembly_val.lean` records as
missing (`QFExDetermined → QEExStep`); it is proved there from `QE/Bounded_compactness.lean`.

## Why the hypothesis is *not* "every model has QE"

The natural-looking *per-model* statement — "for each `M ⊨ T` and each tuple, every formula is
equivalent at that tuple to a quantifier-free formula" — does **not** imply `HasQE T`.  Take
`T = ∅` in a language with a single unary predicate `P` and the one-point model: every formula is
equivalent there to `⊤`, `⊥` or `P(x)`, but `∀ x, P x` has no quantifier-free equivalent modulo
`∅`.  What the transfer must supply is the *two-model* statement (`QFTypeDetermines`): models
with the same quantifier-free type at a tuple satisfy the same formulas there.  That is the shape
of `NontrivialTransfer`/`TrivialTransfer` below.

Everything is stated at universe `0` for the carrier, because the transfer lemmas of
`Assembly_val.lean` (`le_self`, `rv_mem`, `vf_one_mem`, …) are stated for `{M : Type}`.
-/

set_option linter.unusedVariables false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer

namespace FinalAssembly

/-! ## 1. The repaired theory -/

/-- Definition 2.2 item 5 in the form the ruling has it: the ordering on `RV/Kˣ = Γ` is
translation-invariant, i.e. scaling by *any* nonzero `RV`-element (`pRV`), both directions.  The
frozen `Axioms.leMulCompat` has `pUnits` (i.e. `Kˣ`) in place of `pRV`, which makes it a statement
about the trivial translation and forces nothing. -/
def leMulCompatFull : LRV.Sentence :=
  allSorted ![.rv, .rv, .rv]
    (pRV &2 ⟹ (pLe &0 &1 ⇔ pLe (tRVMul &0 &2) (tRVMul &1 &2)))

/-- The repaired theory. -/
def ACVFplus : LRV.Theory := Axioms.ACVF ∪ {leMulCompatFull}

theorem ACVF_subset_ACVFplus : Axioms.ACVF ⊆ ACVFplus := fun _ h => Or.inl h

theorem leMulCompatFull_mem : leMulCompatFull ∈ ACVFplus := Or.inr (Set.mem_singleton _)

/-- Models of `ACVFplus` are models of the frozen `ACVF`. -/
theorem model_ACVF_of_model_ACVFplus {M : Type} [LRV.Structure M] (hM : M ⊨ ACVFplus) :
    M ⊨ Axioms.ACVF :=
  ⟨fun φ hφ => hM.realize_of_mem φ (ACVF_subset_ACVFplus hφ)⟩

/-! ## 2. Trivial and nontrivial valuations -/

/-- The valuation is **nontrivial in the paper's sense** (the hypothesis `axNontrivial` of
`ValPM.ACVF_val`): some nonzero `x ∈ VF` has value strictly below the value of `1`. -/
def IsNontrivialVF (M : Type) [LRV.Structure M] : Prop :=
  ∃ x : M, iVF x ∧ x ≠ iVFZero ∧ ¬ iLe (iRv iVFOne) (iRv x)

/-- The valuation is **trivial**: every element of the `VF` sort is `0` or has the value of `1`. -/
def IsTrivialVF (M : Type) [LRV.Structure M] : Prop :=
  ∀ x : M, iVF x → x = iVFZero ∨ iRv x = iRv iVFOne

/-- Trivial valuations are not nontrivial. -/
theorem not_nontrivial_of_trivial {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF)
    (h : IsTrivialVF M) : ¬ IsNontrivialVF M := by
  rintro ⟨x, hxVF, hx0, hlt⟩
  rcases h x hxVF with hzero | heq
  · exact hx0 hzero
  · rw [heq] at hlt
    exact hlt (le_self hM (rv_mem hM (vf_one_mem hM)))

/-- Nontrivial valuations are not trivial (the form used below). -/
theorem not_trivial_of_nontrivial {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF)
    (h : IsNontrivialVF M) : ¬ IsTrivialVF M :=
  fun ht => not_nontrivial_of_trivial hM ht h

/-! ## 3. The named hypotheses -/

/-- **The transfer hypothesis for a class of models `P`**: two models of `T` in the class which
agree on all quantifier-free formulas at a tuple agree there on every formula. -/
def TransferAt (P : (M : Type) → [LRV.Structure M] → Prop) (T : LRV.Theory) : Prop :=
  ∀ (α : Type) (n : ℕ) (M : Type) [LRV.Structure M] [Nonempty M] (hM : M ⊨ T), P M →
  ∀ (N : Type) [LRV.Structure N] [Nonempty N] (hN : N ⊨ T), P N →
  ∀ (v : α → M) (xs : Fin n → M) (w : α → N) (ys : Fin n → N),
    (∀ ψ : LRV.BoundedFormula α n, ψ.IsQF → (ψ.Realize v xs ↔ ψ.Realize w ys)) →
    ∀ φ : LRV.BoundedFormula α n, (φ.Realize v xs ↔ φ.Realize w ys)

/-- **The nontrivial half** (directions e1-e3 + `hasQE_ACVF_val`). -/
def NontrivialTransfer (T : LRV.Theory) : Prop := TransferAt IsNontrivialVF T

/-- **The trivial half** (direction e4). -/
def TrivialTransfer (T : LRV.Theory) : Prop := TransferAt IsTrivialVF T

/-- **Separation of the two cases by quantifier-free types**: a tuple in a nontrivial model and a
tuple in a trivial model never have the same quantifier-free type.  (Without this the two
transfers do not compose: `QFTypeDetermines` compares models in the *same* class only.) -/
def CaseSeparation (T : LRV.Theory) : Prop :=
  ∀ (α : Type) (n : ℕ) (M : Type) [LRV.Structure M] [Nonempty M] (hM : M ⊨ T)
    (N : Type) [LRV.Structure N] [Nonempty N] (hN : N ⊨ T)
    (v : α → M) (xs : Fin n → M) (w : α → N) (ys : Fin n → N),
    (∀ ψ : LRV.BoundedFormula α n, ψ.IsQF → (ψ.Realize v xs ↔ ψ.Realize w ys)) →
    (IsNontrivialVF M ↔ IsNontrivialVF N)

/-- **The case split**: every model has a nontrivial or a trivial valuation. -/
def CaseSplit (T : LRV.Theory) : Prop :=
  ∀ (M : Type) [LRV.Structure M] [Nonempty M], M ⊨ T → IsNontrivialVF M ∨ IsTrivialVF M

/-! ## 4. The composition -/

/-- **The hypotheses give QF-type determination.** -/
theorem qfTypeDetermines_of_transfers {T : LRV.Theory} (hsub : Axioms.ACVF ⊆ T)
    (hnt : NontrivialTransfer T) (htr : TrivialTransfer T)
    (hsep : CaseSeparation T) (hsplit : CaseSplit T) :
    QECriterion.QFTypeDetermines T := by
  intro α n M _ _ hM N _ _ hN v xs w ys hQF φ
  rcases hsplit M hM with hMn | hMt
  · -- `M` nontrivial, so `N` is nontrivial by separation, and the nontrivial transfer applies
    have hNn : IsNontrivialVF N := (hsep α n M hM N hN v xs w ys hQF).1 hMn
    exact hnt α n M hM hMn N hN hNn v xs w ys hQF φ
  · rcases hsplit N hN with hNn | hNt
    · -- mixed: excluded by separation
      have hMn : IsNontrivialVF M := (hsep α n M hM N hN v xs w ys hQF).2 hNn
      have hACVF : M ⊨ Axioms.ACVF := ⟨fun φ hφ => hM.realize_of_mem φ (hsub hφ)⟩
      exact absurd hMn (not_nontrivial_of_trivial hACVF hMt)
    · exact htr α n M hM hMt N hN hNt v xs w ys hQF φ

/-- **The assembly**: the three named hypotheses and the case split give quantifier elimination
for the repaired theory — with the compactness step proved, not assumed. -/
theorem hasQE_of_transfers {T : LRV.Theory} (hsub : Axioms.ACVF ⊆ T)
    (hnt : NontrivialTransfer T) (htr : TrivialTransfer T)
    (hsep : CaseSeparation T) (hsplit : CaseSplit T) :
    QECriterion.HasQE T :=
  QFComp.hasQE_of_qfTypeDetermines (qfTypeDetermines_of_transfers hsub hnt htr hsep hsplit)

/-- The assembled theorem for the repaired theory, in the frozen shape
(`SpecialTransformations.Milestone0.HasQE`). -/
theorem hasQE_ACVFplus_of_transfers
    (hnt : NontrivialTransfer ACVFplus) (htr : TrivialTransfer ACVFplus)
    (hsep : CaseSeparation ACVFplus) (hsplit : CaseSplit ACVFplus) :
    SpecialTransformations.Milestone0.HasQE ACVFplus :=
  hasQE_of_transfers ACVF_subset_ACVFplus hnt htr hsep hsplit

/-! ## 5. What each hypothesis is, precisely

* `NontrivialTransfer`: given `M, N ⊨ ACVFplus` with nontrivial valuations, tuples with the same
  quantifier-free `L_RV`-type satisfy the same formulas.  Intended proof: the cover
  `L_RV → L_val` (e1, with the atoms of e2 and the residue-field symbols of e3) identifies an
  `L_RV`-formula with the image `valFormulaToRVvf θ` of an `L_val`-formula `θ`;
  `hasQE_ACVF_val` replaces `θ` by a quantifier-free `θ'` in the `L_val`-structure on the `VF`
  sort — which needs that structure to be a model of `ValPM.ACVF_val`: the repaired axiom
  `leMulCompatFull` for `IsValPred.scale` (`m1/Scale.lean`), `m5/VFAlgClosed.lean` for
  `IsAlgClosed`, and nontriviality; then `VFRestrict.transfer_of_isQF`
  (`.ultramath/smw14elno/m6/ValEvalVF.lean`) reads `θ'` back into `L_RV` at `VF`-tuples.  The
  `RV`-valued coordinates are turned into `VF`-coordinates by `Axioms.rvSurj`.

* `TrivialTransfer`: the same for trivially valued models, where `rv` is injective on
  `VF ∖ {0}` and the `L_RV`-structure is a definitional expansion of the algebraically closed
  field on `VF`; this should be a *uniform* translation, with the quantifier-free witness supplied
  by `HasQE acf`.

* `CaseSeparation`: quantifier-free `L_RV`-formulas separate the two classes.

* `CaseSplit`: `IsNontrivialVF M ∨ IsTrivialVF M`.  Genuine content: from `x ≠ 0` and
  `rv x ≠ rv 1` one must produce `y ≠ 0` with `¬ (rv 1 ≤ rv y)` — take `y = x` or `y = x⁻¹`,
  which needs antisymmetry of the `RV`-preorder (only a preorder is axiomatised) plus the repaired
  scaling law.  Not proved here.
-/

end FinalAssembly

#print axioms FinalAssembly.leMulCompatFull
#print axioms FinalAssembly.not_nontrivial_of_trivial
#print axioms FinalAssembly.qfTypeDetermines_of_transfers
#print axioms FinalAssembly.hasQE_of_transfers
#print axioms FinalAssembly.hasQE_ACVFplus_of_transfers

#print axioms QFComp.qeExStep_of_qfTypeDetermines
#print axioms QFComp.hasQE_of_qfTypeDetermines
#print axioms FinalAssembly.hasQE_ACVFplus_of_transfers

namespace SpecialTransformations.Milestone0.Transfer

open SpecialTransformations.Milestone0.Axioms

/-- A member of the repaired axiom set is an axiom of `ACVF`. -/
theorem mem_ACVF_repair {s : LRV.Sentence} (h : s ∈ Axioms.repairRV) : s ∈ Axioms.ACVF := by
  simp only [Axioms.ACVF, Axioms.ACVFpaper, Set.mem_union]
  tauto

theorem mem_ACVF_leMulCompatFull : Axioms.leMulCompatFull ∈ Axioms.ACVF :=
  mem_ACVF_repair (by simp [Axioms.repairRV, Axioms.ofList])

theorem mem_ACVF_axNontrivialRV : Axioms.axNontrivialRV ∈ Axioms.ACVF :=
  mem_ACVF_repair (by simp [Axioms.repairRV, Axioms.ofList])

/-- **The paper's item 5 follows from the repaired axioms**: the order on `RV` is invariant under
scaling by any nonzero `RV`-element. -/
theorem paperScale_of_model {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) : PaperScale M := by
  intro a b c ha hb hc h0
  have h := allSorted_realize hM mem_ACVF_leMulCompatFull ![a, b, c]
    (by intro i; fin_cases i <;> simp [ha, hb, hc])
  have h' : c ≠ iRVZero → (iLe a b ↔ iLe (iRVMul a c) (iRVMul b c)) := by
    simpa [pRV_realize, realize_pLe, realize_tRVMul] using h
  exact h' h0

/-- **Nontriviality follows from the repaired axioms.** -/
theorem hasNontrivVal_of_model {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) :
    HasNontrivVal M := by
  have h := hM.realize_of_mem Axioms.axNontrivialRV mem_ACVF_axNontrivialRV
  rw [Axioms.axNontrivialRV] at h
  rw [Sentence.Realize] at h
  simp only [Formula.Realize] at h
  rw [exSorted_realize] at h
  obtain ⟨x, hxVF, hx⟩ := h
  simp only [BoundedFormula.realize_inf, BoundedFormula.realize_not, pEq,
    BoundedFormula.realize_bdEqual, realize_tVFZero, realize_tRv, realize_tVFOne,
    realize_pLe, Function.comp_apply, Matrix.cons_val_zero] at hx
  exact ⟨x, hxVF, hx.1, hx.2⟩

/-- **The extraction, unconditionally**: the `VF` sort of any model of the repaired `ACVF` models
`ValPM.ACVF_val`.  No nontriviality hypothesis, no scaling hypothesis, no case split. -/
theorem model_ACVF_val_of_model {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) :
    @Theory.Model Language.val (VFType (M := M))
      (vfValStruct (hM := hM)) ValPM.ACVF_val :=
  model_ACVF_val_of_axioms (M := M)
    (fun x => predV_refl hM x) (fun x y z h1 h2 => predV_trans hM h1 h2)
    (fun x => predV_zero_le hM x) (fun x h => predV_zero_eq hM h)
    (fun x y => predV_ultra hM x y) (fun x y => predV_total hM x y)
    (paperScale_of_model hM) (VFAlgClosed.isAlgClosed_vfType (M := M)) (hasNontrivVal_of_model hM)

end SpecialTransformations.Milestone0.Transfer

#print axioms SpecialTransformations.Milestone0.Transfer.paperScale_of_model
#print axioms SpecialTransformations.Milestone0.Transfer.hasNontrivVal_of_model
#print axioms SpecialTransformations.Milestone0.Transfer.model_ACVF_val_of_model

namespace SpecialTransformations.Milestone0.Transfer

open SpecialTransformations.Milestone0.Axioms

/-- Realisation of the constant `1` of the `RV` sort (local copy). -/
theorem realize_tRVOne' {M : Type} [LRV.Structure M] {k : ℕ} (v : Empty ⊕ Fin k → M) :
    (tRVOne (n := k)).realize v = iRVOne := by
  show Structure.funMap (L := LRV) Fn.rvOne
      (fun i => Term.realize (L := LRV) v ((fun j : Fin 0 => j.elim0) i)) = iRVOne
  rw [show (fun i => Term.realize (L := LRV) v ((fun j : Fin 0 => j.elim0) i))
      = (fun i => i.elim0) from by funext i; exact i.elim0]
  rfl

theorem mem_ACVF_rvMulOneRV : Axioms.rvMulOneRV ∈ Axioms.ACVF :=
  mem_ACVF_repair (by simp [Axioms.repairRV, Axioms.ofList])

theorem mem_ACVF_rvMulInvRV : Axioms.rvMulInvRV ∈ Axioms.ACVF :=
  mem_ACVF_repair (by simp [Axioms.repairRV, Axioms.ofList])

/-- The neutral law for `×` on `RV^×`, from the repaired item 2. -/
theorem rv_mul_one_ne {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {a : M}
    (ha : iRV a) (ha0 : a ≠ iRVZero) : iRVMul iRVOne a = a := by
  have hu := allSorted_realize hM mem_ACVF_rvMulOneRV ![a]
    (by intro i; fin_cases i; simpa using ha)
  have hu' : a ≠ iRVZero → iRVMul iRVOne a = a := by
    simpa [pRV_realize, pEq, BoundedFormula.realize_bdEqual, realize_tRVMul, realize_tRVOne',
      realize_tv, Matrix.cons_val_zero] using hu
  exact hu' ha0

/-- Inverses in `RV^×`, from the repaired item 2. -/
theorem rv_mul_inv_ne {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {a : M}
    (ha : iRV a) (ha0 : a ≠ iRVZero) :
    ∃ b : M, iRV b ∧ b ≠ iRVZero ∧ iRVMul b a = iRVOne := by
  have hu := allSorted_realize hM mem_ACVF_rvMulInvRV ![a]
    (by intro i; fin_cases i; simpa using ha)
  have hu' : a ≠ iRVZero → ∃ b : M, iRV b ∧ b ≠ iRVZero ∧ iRVMul b a = iRVOne := by
    simpa [pRV_realize, exSorted, sortPred, sortPred_realize, pRVsort_realize,
      BoundedFormula.realize_ex, BoundedFormula.realize_inf, pEq, BoundedFormula.realize_bdEqual,
      realize_tRVMul, realize_tRVOne', realize_tv, Function.comp_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one] using hu
  exact hu' ha0

/-- **Nontriviality in the `IsNontrivialVF` form.**  `axNontrivialRV` gives `a ≠ 0` with
`¬ (v a ≤ v 1)`; an inverse of `rv a` in `RV^×` lifts to a `VF`-element by `rvSurj`, and scaling
`v 1 ≤ v x` by `v a` contradicts `¬ (v a ≤ v 1)`. -/
theorem isNontrivialVF_of_model {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) :
    ∃ x : M, iVF x ∧ x ≠ iVFZero ∧ ¬ iLe (iRv iVFOne) (iRv x) := by
  obtain ⟨a, haVF, ha0, hlt⟩ := hasNontrivVal_of_model hM
  have har : iRv a ≠ iRVZero := fun h => ha0 (rv_eq_infty hM haVF h)
  have hone : iRv iVFOne = iRVOne := Cover.rv_one hM
  have hlt' : ¬ iLe (iRv a) iRVOne := by rwa [hone] at hlt
  obtain ⟨b, hbRV, hb0, hbinv⟩ := rv_mul_inv_ne hM (rv_mem hM haVF) har
  obtain ⟨x, hxVF, hx⟩ := rv_surj (M := M) hM hbRV hb0
  refine ⟨x, hxVF, ?_, ?_⟩
  · intro hx0
    exact hb0 (by rw [← hx, hx0, rv_zero_eq hM])
  · intro hle
    have hs := (paperScale_of_model hM (iRv iVFOne) (iRv x) (iRv a)
      (rv_mem hM (vf_one_mem hM)) (rv_mem hM hxVF) (rv_mem hM haVF) har).1 hle
    rw [hone, rv_mul_one_ne hM (rv_mem hM haVF) har] at hs
    rw [hx, hbinv] at hs
    exact hlt' hs

end SpecialTransformations.Milestone0.Transfer

#print axioms SpecialTransformations.Milestone0.Transfer.rv_mul_one_ne
#print axioms SpecialTransformations.Milestone0.Transfer.rv_mul_inv_ne
#print axioms SpecialTransformations.Milestone0.Transfer.isNontrivialVF_of_model

/-
  Swarm `smw163dd5`, member m6, direction f6: **the trivial case**.

  The endgame `FinalAssembly.hasQE_ACVFplus_of_transfers` takes four hypotheses:
  `NontrivialTransfer`, `TrivialTransfer`, `CaseSeparation`, `CaseSplit`.  This file shows that
  **the trivial half is free**, and reduces the other three to a single one.

  Main content:

  * `isTrivialVF_iff_trivVal` : the `FinalAssembly.IsTrivialVF` of the endgame **is** the
    `TrivCase.TrivVal` of `TrivCase.no_coarse_triv` (same definition, so this is `Iff.rfl`-cheap);
  * `not_isTrivialVF` : **no model of `Axioms.ACVF` is trivially valued in that sense**
    (`TrivCase.no_coarse_triv`), hence `no_isTrivialVF_of_subset` for any `T ⊇ Axioms.ACVF`;
  * `trivialTransfer` : **`FinalAssembly.TrivialTransfer T` holds unconditionally** for every
    theory `T ⊇ Axioms.ACVF`.  The hypothesis class is empty, so the transfer is vacuous.  This
    discharges one of the four hypotheses of `hasQE_ACVFplus_of_transfers`
    (for `ACVFplus`, for `ACVFplus ∪ {axNontrivialRV}`, for `ACVF00`, …).
  * `caseSeparation_of_allNontrivial`, `caseSplit_of_allNontrivial` : once the trivial class is
    empty, both the case separation and the case split reduce to
    `∀ M, M ⊨ T → IsNontrivialVF M`;
  * `hasQE_of_nontrivialTransfer` and `hasQE_ACVFplus_of_nontrivialTransfer` : **the endgame with
    one nontrivial hypothesis instead of four**:
    `NontrivialTransfer T → (∀ M ⊨ T, IsNontrivialVF M) → HasQE T`.
  * `fineTriv_not_trivial` / `fineTriv_not_nontrivial` : in the *fine* trivial case
    (`TrivCase.FineTriv`, order-trivial with `rv` injective — the class `QE-PLAN.md` §10 calls
    the trivially valued model), the valuation is **neither** `IsTrivialVF` **nor**
    `IsNontrivialVF`.  Consequence, stated exactly: `CaseSplit`/`CaseSeparation` for a theory `T`
    can only be discharged through nontriviality if there is **no** `FineTriv` model of `T`; the
    two predicates of the endgame do not exhaust the models.

  Uses `import Pre` (the compiled preamble of `QE/Assembly_val.lean`).
-/

open FirstOrder FirstOrder.Language
open scoped FirstOrder
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Milestone0.LRV

namespace TrivialHalf

/-! ## 1. `FinalAssembly.IsTrivialVF` is `TrivCase.TrivVal` -/

variable {M : Type} [LRV.Structure M]

theorem isTrivialVF_iff_trivVal : FinalAssembly.IsTrivialVF M ↔ TrivCase.TrivVal M :=
  Iff.rfl

theorem isNontrivialVF_iff (hM : M ⊨ Axioms.ACVF) :
    FinalAssembly.IsNontrivialVF M ↔
      ∃ x : M, iVF x ∧ x ≠ iVFZero ∧ ¬ iLe (iRv iVFOne) (iRv x) :=
  Iff.rfl

/-! ## 2. The trivial class is empty -/

theorem not_isTrivialVF (hM : M ⊨ Axioms.ACVF) : ¬ FinalAssembly.IsTrivialVF M :=
  fun h => TrivCase.no_coarse_triv hM h

/-- **Any theory containing `Axioms.ACVF` has no trivially valued models in the sense of the
endgame.** -/
theorem not_isTrivialVF_of_subset {T : LRV.Theory} (hsub : Axioms.ACVF ⊆ T)
    (hM : M ⊨ T) : ¬ FinalAssembly.IsTrivialVF M :=
  fun h => TrivCase.no_coarse_triv ⟨fun φ hφ => hM.realize_of_mem φ (hsub hφ)⟩ h

/-- **The trivial half of the endgame, unconditionally.**  For every theory `T ⊇ Axioms.ACVF`,
`FinalAssembly.TrivialTransfer T` holds: its hypothesis `IsTrivialVF` is unsatisfiable. -/
theorem trivialTransfer (T : LRV.Theory) (hsub : Axioms.ACVF ⊆ T) :
    FinalAssembly.TrivialTransfer T := by
  intro α n M _ _ hM hPM N _ _ hN hPN v xs w ys hQF φ
  exact absurd hPM (not_isTrivialVF_of_subset (M := M) hsub hM)

theorem trivialTransfer_ACVFplus : FinalAssembly.TrivialTransfer FinalAssembly.ACVFplus :=
  trivialTransfer _ FinalAssembly.ACVF_subset_ACVFplus

theorem trivialTransfer_ACVF : FinalAssembly.TrivialTransfer Axioms.ACVF :=
  trivialTransfer _ (subset_rfl)

/-! ## 3. Separation and split from nontriviality alone -/

/-- Every model of `T` is nontrivially valued. -/
def AllNontrivial (T : LRV.Theory) : Prop :=
  ∀ (M : Type) [LRV.Structure M] [Nonempty M], M ⊨ T → FinalAssembly.IsNontrivialVF M

theorem caseSeparation_of_allNontrivial {T : LRV.Theory} (h : AllNontrivial T) :
    FinalAssembly.CaseSeparation T := by
  intro α n M _ _ hM N _ _ hN v xs w ys hQF
  exact ⟨fun _ => h N hN, fun _ => h M hM⟩

theorem caseSplit_of_allNontrivial {T : LRV.Theory} (h : AllNontrivial T) :
    FinalAssembly.CaseSplit T :=
  fun M _ _ hM => Or.inl (h M hM)

/-! ## 4. The endgame with one hypothesis instead of four -/

/-- **The assembly without the trivial hypotheses**: `NontrivialTransfer` plus "every model is
nontrivially valued" give quantifier elimination. -/
theorem hasQE_of_nontrivialTransfer {T : LRV.Theory} (hsub : Axioms.ACVF ⊆ T)
    (hnt : FinalAssembly.NontrivialTransfer T) (hn : AllNontrivial T) :
    QECriterion.HasQE T :=
  FinalAssembly.hasQE_of_transfers hsub hnt (trivialTransfer T hsub)
    (caseSeparation_of_allNontrivial hn) (caseSplit_of_allNontrivial hn)

/-- The assembled theorem for the repaired theory `ACVFplus`, with the trivial hypotheses gone. -/
theorem hasQE_ACVFplus_of_nontrivialTransfer (hnt : FinalAssembly.NontrivialTransfer
      FinalAssembly.ACVFplus) (hn : AllNontrivial FinalAssembly.ACVFplus) :
    SpecialTransformations.Milestone0.HasQE FinalAssembly.ACVFplus :=
  FinalAssembly.hasQE_ACVFplus_of_transfers hnt trivialTransfer_ACVFplus
    (caseSeparation_of_allNontrivial hn) (caseSplit_of_allNontrivial hn)

/-! ## 5. The fine trivial case is neither trivial nor nontrivial -/

/-- In a `FineTriv` model, `1 ≠ 0` on the `VF` sort. -/
theorem vf_one_ne_zero (hM : M ⊨ Axioms.ACVF) : iVFOne (M := M) ≠ iVFZero :=
  fun h => vf_zero_ne_one hM h.symm

/-- **In the fine trivial case the coarse triviality predicate fails**: `FineTriv` gives an element
whose value differs from the value of `1`. -/
theorem fineTriv_not_trivial (hM : M ⊨ Axioms.ACVF) (h : TrivCase.FineTriv M) :
    ¬ FinalAssembly.IsTrivialVF M := by
  obtain ⟨x, hxVF, hx0, hx⟩ := TrivCase.exists_rv_ne_one hM
  intro hT
  rcases isTrivialVF_iff_trivVal.mp hT x hxVF with h0 | h0
  · exact hx0 h0
  · exact hx h0

/-- **In the fine trivial case, nontriviality fails too**: with the trivial order every nonzero
element is `≤ 1`, so nothing lies strictly below `1`. -/
theorem fineTriv_not_nontrivial (hM : M ⊨ Axioms.ACVF) (h : TrivCase.FineTriv M) :
    ¬ FinalAssembly.IsNontrivialVF M := by
  rintro ⟨x, hxVF, hx0, hlt⟩
  have h1 : iLe (iRv (iVFOne (M := M))) (iRv x) := by
    rw [(h.ord (iVFOne (M := M)) x (vf_one_mem hM) hxVF)]
    exact Or.inl (vf_one_ne_zero hM)
  exact hlt h1

/-- **The two classes of the endgame do not exhaust a theory with a `FineTriv` model.** -/
theorem fineTriv_neither (hM : M ⊨ Axioms.ACVF) (h : TrivCase.FineTriv M) :
    ¬ (FinalAssembly.IsNontrivialVF M ∨ FinalAssembly.IsTrivialVF M) :=
  fun hc => hc.elim (fineTriv_not_nontrivial hM h) (fineTriv_not_trivial hM h)

/-- Consequence for the case split: any theory `T ⊇ Axioms.ACVF` that has a `FineTriv` model does
**not** satisfy `CaseSplit T`.  (So `CaseSplit` can only be reached by adding nontriviality as an
axiom, or by replacing it with a genuinely exhaustive split; and `CaseSeparation` alone does not
close the endgame either.) -/
theorem not_caseSplit_of_fineTriv {T : LRV.Theory} (hsub : Axioms.ACVF ⊆ T)
    (hM : M ⊨ T) (h : TrivCase.FineTriv M) (hne : Nonempty M) :
    ¬ FinalAssembly.CaseSplit T := by
  intro hCS
  haveI := hne
  have hACVF : M ⊨ Axioms.ACVF := ⟨fun φ hφ => hM.realize_of_mem φ (hsub hφ)⟩
  exact fineTriv_neither hACVF h (hCS M hM)

end TrivialHalf

#print axioms TrivialHalf.isTrivialVF_iff_trivVal
#print axioms TrivialHalf.not_isTrivialVF
#print axioms TrivialHalf.not_isTrivialVF_of_subset
#print axioms TrivialHalf.trivialTransfer
#print axioms TrivialHalf.trivialTransfer_ACVFplus
#print axioms TrivialHalf.caseSeparation_of_allNontrivial
#print axioms TrivialHalf.caseSplit_of_allNontrivial
#print axioms TrivialHalf.hasQE_of_nontrivialTransfer
#print axioms TrivialHalf.hasQE_ACVFplus_of_nontrivialTransfer
#print axioms TrivialHalf.fineTriv_not_trivial
#print axioms TrivialHalf.fineTriv_not_nontrivial
#print axioms TrivialHalf.fineTriv_neither
#print axioms TrivialHalf.not_caseSplit_of_fineTriv

/-
  Swarm `smw163dd5`, member m6, direction f6 — **the trivial case, quantifier elimination**.

  Setting: `M` is a model of the frozen `Axioms.ACVF` which is *trivially valued in the fine
  sense* (`TrivCase.FineTriv`: `rv` injective on `VF`, the valuation order trivial, the residue
  operations the field's own).  Then the `L_val`-structure `VFRestrict.vfStruct` on the `VF` sort
  has as its predicate the quantifier-free ring condition `y ≠ 0 ∨ x = 0`, and its ring symbols
  are the field operations.  Hence

  * the `VF` sort with its `L_val`-structure is a model of `ACFValidation.acf`, and
  * every `L_val`-formula is, at every `VF`-tuple, equivalent to a **quantifier-free** one
    (`fineTriv_val_QE`), by quantifier elimination for `acf` (`HQEDerive.HasQEb_acf`) applied to
    the quantifier-free `L_ring`-translation of the formula.

  This is the trivial case's half of the campaign: the exact analogue of `hasQE_ACVF_val`, with
  `TrivCase.FineTriv` in place of nontriviality.  Nothing here uses the cover, and nothing beyond
  `M ⊨ Axioms.ACVF` and `TrivCase.FineTriv M`.
-/

open FirstOrder FirstOrder.Language
open scoped FirstOrder
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Milestone0.LRV

namespace FineQE

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

/-! ## 1. The `VF` sort of a `FineTriv` model as an algebraically closed field -/

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- The field structure on the `VF` sort. -/
noncomputable instance instFieldVF : Field (VFType (M := M)) := vfFieldOfModel (M := M)

/-- The ring structure on the `VF` sort is the field's own. -/
noncomputable instance instCompatVF : FirstOrder.Ring.CompatibleRing (VFType (M := M)) :=
  FirstOrder.Ring.compatibleRingOfRing _

/-- The `L_val`-structure of `VFRestrict`: `VF`-sorted ring symbols, reversed `RV`-order. -/
noncomputable instance instValVF : Language.val.Structure (VFType (M := M)) :=
  VFRestrict.vfStruct hM

/-- The ring symbols of `vfStruct` are the field operations, so `valRingHom` is an expansion. -/
instance instExpVF : LHom.IsExpansionOn FirstOrder.valRingHom (VFType (M := M)) where
  map_onFunction := by
    intro n f x
    cases f <;> rfl
  map_onRelation := by
    intro n r x
    exact isEmptyElim r

instance instIsAlgClosedVF : IsAlgClosed (VFType (M := M)) :=
  VFAlgClosed.isAlgClosed_vfType (M := M) (hM := hM)

/-- **The `VF` sort of a `FineTriv` model models the theory of algebraically closed fields.** -/
noncomputable instance instAcfVF : ACFValidation.acf.Model (VFType (M := M)) :=
  ACFValidation.acfModel

instance instNonemptyVF : Nonempty (VFType (M := M)) := ⟨0⟩

/-! ## 2. The predicate is quantifier-free in the ring language -/

/-- **In the fine trivial case the `L_val`-predicate of the `VF` sort is the quantifier-free ring
condition `y ≠ 0 ∨ x = 0`.** -/
theorem vfType_eq_zero_iff (x : VFType (M := M)) : x = 0 ↔ x.1 = iVFZero := by
  constructor
  · rintro rfl
    exact vfType_zero_val (M := M)
  · intro h
    exact Subtype.ext (h.trans (vfType_zero_val (M := M)).symm)

theorem predVF_iff (h : TrivCase.FineTriv M) (x y : VFType (M := M)) :
    (@Structure.RelMap Language.val (VFType (M := M)) (VFRestrict.vfStruct hM) 2 ValRel.le
      ![x, y]) ↔ y ≠ 0 ∨ x = 0 := by
  have hord : (@Structure.RelMap Language.val (VFType (M := M)) (VFRestrict.vfStruct hM) 2
        ValRel.le ![x, y]) ↔ y.1 ≠ iVFZero ∨ x.1 = iVFZero := by
    rw [VFRestrict.vfStruct_le_apply]
    exact h.ord y.1 x.1 y.2 x.2
  rw [hord]
  constructor
  · rintro (hy | hx)
    · exact Or.inl (fun h0 => hy ((vfType_eq_zero_iff y).mp h0))
    · exact Or.inr ((vfType_eq_zero_iff x).mpr hx)
  · rintro (hy | hx)
    · exact Or.inl (fun h0 => hy ((vfType_eq_zero_iff y).mpr h0))
    · exact Or.inr ((vfType_eq_zero_iff x).mp hx)


/-! ## 3. Translation of `L_val`-terms into `L_ring`-terms -/

section Terms

variable {α : Type}

/-- Relabel `L_val`-terms as `L_ring`-terms (the function symbols agree). -/
noncomputable def toRingTerm : Language.val.Term α → Language.ring.Term α
  | .var a => .var a
  | .func f ts => .func (ValPM.valToRing f) (fun i => toRingTerm (ts i))

theorem toRingTerm_var (a : α) : toRingTerm (Term.var a : Language.val.Term α) = .var a := rfl

theorem toRingTerm_func {n : ℕ} (f : Language.val.Functions n)
    (ts : Fin n → Language.val.Term α) :
    toRingTerm (.func f ts) = .func (ValPM.valToRing f) (fun i => toRingTerm (ts i)) := rfl

/-- `L_val`-terms and their `L_ring`-images have the same value in `VFRestrict.vfStruct`. -/
theorem realize_toRingTerm (v : α → VFType (M := M)) (t : Language.val.Term α) :
    Term.realize (L := Language.val) v t = Term.realize (L := Language.ring) v (toRingTerm t) := by
  induction t with
  | var a => rfl
  | func f ts ih =>
    rw [toRingTerm_func, Term.realize_func, Term.realize_func]
    rw [show (fun i => Term.realize v (toRingTerm (ts i)))
        = (fun i => Term.realize v (ts i)) from funext fun i => (ih i).symm]
    exact ValPM.valFunMap_eq_ringVal (N := VFType (M := M)) f _

end Terms

/-! ## 4. Translation of `L_val`-formulas into `L_ring`-formulas -/

/-- The `L_val`-predicate `v x ≤ v y`, read as the ring condition `y ≠ 0 ∨ x = 0`. -/
noncomputable def leToRing {α : Type} {n : ℕ} (a b : Language.val.Term (α ⊕ Fin n)) :
    Language.ring.BoundedFormula α n :=
  (∼(toRingTerm b =' (0 : Language.ring.Term (α ⊕ Fin n)))) ⊔
    (toRingTerm a =' (0 : Language.ring.Term (α ⊕ Fin n)))

theorem realize_leToRing {α : Type} {n : ℕ}
    (a b : Language.val.Term (α ⊕ Fin n)) (v : α → VFType (M := M))
    (xs : Fin n → VFType (M := M)) :
    (leToRing a b).Realize v xs ↔
      ¬ (Term.realize (Sum.elim v xs) b = 0) ∨ Term.realize (Sum.elim v xs) a = 0 := by
  rw [leToRing, BoundedFormula.realize_sup, BoundedFormula.realize_not,
    BoundedFormula.realize_bdEqual, BoundedFormula.realize_bdEqual,
    realize_toRingTerm, realize_toRingTerm, FirstOrder.Ring.realize_zero]

/-- Relabel `L_val`-formulas as `L_ring`-formulas, sending every `v a ≤ v b` to `b ≠ 0 ∨ a = 0`. -/
noncomputable def toRingForm {α : Type} : {n : ℕ} → Language.val.BoundedFormula α n →
    Language.ring.BoundedFormula α n
  | _, .falsum => .falsum
  | _, .equal t₁ t₂ => .equal (toRingTerm t₁) (toRingTerm t₂)
  | _, .rel ValRel.le ts => leToRing (ts 0) (ts 1)
  | _, @BoundedFormula.imp _ _ n φ₁ φ₂ => .imp (toRingForm φ₁) (toRingForm φ₂)
  | _, @BoundedFormula.all _ _ n φ => .all (toRingForm φ)

theorem toRingForm_falsum {α : Type} {n : ℕ} :
    toRingForm (BoundedFormula.falsum (L := Language.val) (α := α) (n := n))
      = (BoundedFormula.falsum : Language.ring.BoundedFormula α n) := rfl

theorem toRingForm_equal {α : Type} {n : ℕ} (t₁ t₂ : Language.val.Term (α ⊕ Fin n)) :
    toRingForm (BoundedFormula.equal t₁ t₂) = (toRingTerm t₁ =' toRingTerm t₂) := rfl

theorem toRingForm_rel {α : Type} {n : ℕ} (ts : Fin 2 → Language.val.Term (α ⊕ Fin n)) :
    toRingForm (BoundedFormula.rel ValRel.le ts) = leToRing (ts 0) (ts 1) := rfl

theorem toRingForm_imp {α : Type} {n : ℕ} (φ₁ φ₂ : Language.val.BoundedFormula α n) :
    toRingForm (BoundedFormula.imp φ₁ φ₂) = (BoundedFormula.imp (toRingForm φ₁) (toRingForm φ₂)) :=
  rfl

theorem toRingForm_all {α : Type} {n : ℕ} (φ : Language.val.BoundedFormula α (n + 1)) :
    toRingForm (BoundedFormula.all φ) = (BoundedFormula.all (toRingForm φ)) := rfl

/-- **The translation preserves realization** in the `L_val`-structure on the `VF` sort. -/
theorem realize_toRingForm (h : TrivCase.FineTriv M) :
    ∀ {n : ℕ} (φ : Language.val.BoundedFormula α n) (v : α → VFType (M := M))
      (xs : Fin n → VFType (M := M)),
      (φ.Realize v xs ↔ (toRingForm φ).Realize v xs)
  | _, .falsum, v, xs => by
    rw [toRingForm_falsum]
    exact Iff.rfl
  | _, .equal t₁ t₂, v, xs => by
    rw [toRingForm_equal]
    show Term.realize (L := Language.val) (Sum.elim v xs) t₁
        = Term.realize (L := Language.val) (Sum.elim v xs) t₂ ↔ _
    rw [realize_toRingTerm, realize_toRingTerm]
    exact Iff.rfl
  | _, .rel ValRel.le ts, v, xs => by
    rw [toRingForm_rel]
    show (@Structure.RelMap Language.val (VFType (M := M)) (VFRestrict.vfStruct hM) 2 ValRel.le
      (fun i => Term.realize (Sum.elim v xs) (ts i))) ↔ (leToRing (ts 0) (ts 1)).Realize v xs
    rw [show (fun i => Term.realize (Sum.elim v xs) (ts i))
        = ![Term.realize (Sum.elim v xs) (ts 0), Term.realize (Sum.elim v xs) (ts 1)] from by
        funext i; fin_cases i <;> rfl,
      predVF_iff h, realize_leToRing, realize_toRingTerm, realize_toRingTerm]
  | _, .imp φ₁ φ₂, v, xs => by
    rw [toRingForm_imp, BoundedFormula.realize_imp, BoundedFormula.realize_imp,
      realize_toRingForm h φ₁ v xs, realize_toRingForm h φ₂ v xs]
  | _, .all φ, v, xs => by
    rw [toRingForm_all, BoundedFormula.realize_all, BoundedFormula.realize_all]
    exact forall_congr' fun a => realize_toRingForm h φ v (Fin.snoc xs a)


/-! ## 5. Quantifier elimination for `L_val` in the fine trivial case -/

section QE

variable {α : Type}

/-- `LHom.onBoundedFormula` preserves quantifier-freeness. -/
theorem isQF_onBoundedFormula_valRingHom {n : ℕ} {φ : Language.ring.BoundedFormula α n}
    (h : φ.IsQF) : (FirstOrder.valRingHom.onBoundedFormula φ).IsQF := by
  induction h with
  | falsum => exact BoundedFormula.isQF_bot
  | of_isAtomic ha =>
    cases ha with
    | equal t₁ t₂ => exact (BoundedFormula.IsAtomic.equal _ _).isQF
    | rel R ts => exact isEmptyElim R
  | imp _ _ ih₁ ih₂ => exact ih₁.imp ih₂

/-- **The quantifier-free `L_val`-formula produced by the trivial-case elimination.**  It is an
explicit function of the input (a choice from `HasQEb_acf`), hence the *same* formula in every
`FineTriv` model — which is what makes the two-model transfer below go through. -/
noncomputable def fineTriv_qf {n : ℕ} (θ : Language.val.BoundedFormula α n) :
    Language.val.BoundedFormula α n :=
  FirstOrder.valRingHom.onBoundedFormula
    (Classical.choose (HQEDerive.HasQEb_acf α n (toRingForm θ)))

theorem fineTriv_qf_isQF {n : ℕ} (θ : Language.val.BoundedFormula α n) :
    (fineTriv_qf θ).IsQF :=
  isQF_onBoundedFormula_valRingHom
    (Classical.choose_spec (HQEDerive.HasQEb_acf α n (toRingForm θ))).1

/-- The defining property: the quantifier-free formula is equivalent at every `VF`-tuple. -/
theorem fineTriv_qf_iff (h : TrivCase.FineTriv M) {n : ℕ}
    (θ : Language.val.BoundedFormula α n) (v : α → VFType (M := M))
    (xs : Fin n → VFType (M := M)) :
    (θ.Realize v xs ↔ (fineTriv_qf θ).Realize v xs) := by
  have hspec := (Classical.choose_spec (HQEDerive.HasQEb_acf α n (toRingForm θ))).2
  have h1 : (toRingForm θ).Realize v xs ↔
      (Classical.choose (HQEDerive.HasQEb_acf α n (toRingForm θ))).Realize v xs :=
    hspec.realize_bd_iff
  have h2 : (fineTriv_qf θ).Realize v xs ↔
      (Classical.choose (HQEDerive.HasQEb_acf α n (toRingForm θ))).Realize v xs :=
    LHom.realize_onBoundedFormula FirstOrder.valRingHom _
  exact (realize_toRingForm (M := M) h θ v xs).trans (h1.trans h2.symm)

/-- **Quantifier elimination for `L_val` on the `VF` sort of a `FineTriv` model.**  Every
`L_val`-formula is, at every tuple of `VF`-elements, equivalent to a quantifier-free one.  This is
the trivial-case counterpart of `hasQE_ACVF_val`, and it uses only `M ⊨ Axioms.ACVF` and
`TrivCase.FineTriv M` — no nontriviality, no cover. -/
theorem fineTriv_val_QE (h : TrivCase.FineTriv M) {n : ℕ}
    (θ : Language.val.BoundedFormula α n) :
    ∃ θ' : Language.val.BoundedFormula α n, θ'.IsQF ∧
      ∀ (v : α → VFType (M := M)) (xs : Fin n → VFType (M := M)),
        (θ.Realize v xs ↔ θ'.Realize v xs) :=
  ⟨fineTriv_qf θ, fineTriv_qf_isQF θ, fun v xs => fineTriv_qf_iff h θ v xs⟩

end QE

/-! ## 6. The trivial case of the endgame: `L_RV`-formulas at `VF`-tuples

The cover of the campaign (`CoverBridge.CoverVF`, the one open hypothesis) converts an
`L_RV`-formula at a `VF`-tuple into an `L_val`-formula; `fineTriv_val_QE` then removes the
quantifiers, and `VFRestrict.transfer_of_isQF` reads the result back in `L_RV`.  Consequently the
*trivial* transfer and the quantifier-free form of every `L_RV`-formula hold **for `FineTriv`
models, with the cover as the only hypothesis** — in particular without `HasQEb ACVF_val`, hence
without nontriviality. -/

/-- **The trivial-side cover bridge, uniformly in the model**: on every `FineTriv` model, every
`L_RV`-formula is at every `VF`-tuple equivalent to a quantifier-free `L_RV`-formula, modulo the
cover.  The witness does not depend on the model. -/
theorem exists_qf_uniform_fineTriv (hC : CoverBridge.CoverVF Axioms.ACVF) {n : ℕ}
    (φ : LRV.BoundedFormula Empty n) :
    ∃ ψ : LRV.BoundedFormula Empty n, ψ.IsQF ∧
      ∀ (M : Type) [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] (hTM : TrivCase.FineTriv M)
        (y : Fin n → M), (∀ i, iVF (y i)) →
        (φ.Realize (default : Empty → M) y
          ↔ ψ.Realize (default : Empty → M) y) := by
  obtain ⟨θ, hθ⟩ := hC n φ
  refine ⟨valFormulaToRV (fineTriv_qf θ),
    CoverBridge.isQF_valFormulaToRV (fineTriv_qf_isQF θ), ?_⟩
  intro M _ hM hTM y hy
  exact (hθ M hM y hy).trans
    (VFRestrict.transfer_of_isQF (M := M) hM (fineTriv_qf_isQF θ)
      (fun x => fineTriv_qf_iff (M := M) (hM := hM) hTM θ _ x) y hy)

/-- The per-model form of `exists_qf_uniform_fineTriv`. -/
theorem exists_qf_of_coverVF_fineTriv (h : TrivCase.FineTriv M)
    (hC : CoverBridge.CoverVF Axioms.ACVF) {n : ℕ} (φ : LRV.BoundedFormula Empty n) :
    ∃ ψ : LRV.BoundedFormula Empty n, ψ.IsQF ∧
      ∀ y : Fin n → M, (∀ i, iVF (y i)) →
        (φ.Realize (default : Empty → M) y
          ↔ ψ.Realize (default : Empty → M) y) := by
  obtain ⟨ψ, hψQF, hψ⟩ := exists_qf_uniform_fineTriv hC φ
  exact ⟨ψ, hψQF, fun y hy => hψ M h y hy⟩

/-- **The trivial half of the transfer, for `FineTriv` models, modulo the cover.**  Two `FineTriv`
models of `Axioms.ACVF` whose tuples have the same quantifier-free `L_RV`-type have the same
`L_RV`-theory at those tuples. -/
theorem transferAt_fineTriv (hC : CoverBridge.CoverVF Axioms.ACVF)
    {n : ℕ} {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
    (hTM : TrivCase.FineTriv M) {N : Type} [LRV.Structure N] [hN : N ⊨ Axioms.ACVF]
    (hTN : TrivCase.FineTriv N) {y : Fin n → M} {z : Fin n → N}
    (hy : ∀ i, iVF (y i)) (hz : ∀ i, iVF (z i))
    (hQF : ∀ ψ : LRV.BoundedFormula Empty n, ψ.IsQF →
      (ψ.Realize (default : Empty → M) y ↔ ψ.Realize (default : Empty → N) z))
    (φ : LRV.BoundedFormula Empty n) :
    (φ.Realize (default : Empty → M) y ↔ φ.Realize (default : Empty → N) z) := by
  obtain ⟨ψ, hψQF, hψ⟩ := exists_qf_uniform_fineTriv hC φ
  exact (hψ M hTM y hy).trans ((hQF ψ hψQF).trans (hψ N hTN z hz).symm)

end FineQE

#print axioms FineQE.isQF_onBoundedFormula_valRingHom
#print axioms FineQE.fineTriv_val_QE
#print axioms FineQE.fineTriv_qf_iff
#print axioms FineQE.exists_qf_uniform_fineTriv
#print axioms FineQE.exists_qf_of_coverVF_fineTriv
#print axioms FineQE.transferAt_fineTriv

namespace SpecialTransformations.Milestone0.Transfer

/-- **The frozen target, from one hypothesis.**  `NontrivialTransfer Axioms.ACVF` says that two
models with the same quantifier-free `L_RV`-type satisfy the same formulas at matching tuples; from
it, `HasQE Axioms.ACVF` — the statement of Theorem 2.3 — follows, because every model of the
repaired `ACVF` is nontrivially valued (`isNontrivialVF_of_model`) and the trivial half of the
assembly is vacuous (`TrivialHalf.trivialTransfer`). -/
theorem hasQE_ACVF_of_nontrivialTransfer
    (hnt : FinalAssembly.NontrivialTransfer Axioms.ACVF) :
    SpecialTransformations.Milestone0.HasQE Axioms.ACVF :=
  TrivialHalf.hasQE_of_nontrivialTransfer (T := Axioms.ACVF) (fun _ h => h) hnt
    (fun M _ _ hM => isNontrivialVF_of_model hM)

end SpecialTransformations.Milestone0.Transfer

#print axioms TrivialHalf.hasQE_of_nontrivialTransfer
#print axioms FineQE.fineTriv_val_QE
#print axioms SpecialTransformations.Milestone0.Transfer.hasQE_ACVF_of_nontrivialTransfer

/-
  **RV-term normal form** (swarm `smw163dd5`, member m1, direction f1).

  Every `L_RV`-term of the `RV` sort whose `VF`-arguments are `VF`-terms is, at every tuple of
  `VF`-elements of a model of `ACVF` plus the residue links, pointwise **either `0` or `rv s` for
  one of finitely many `L_val`-terms `s` that are read off the term syntactically**:

    `RVTerm.realize_normal : t.evalM x = iRVZero ∨ ∃ s ∈ t.vals, t.evalM x = iRv (valTermEval x s)`

  The set `t.vals` is computed by `RVTerm.vals`:
  `·` is product, `kAdd` is `S_a ∪ S_b ∪ (S_a + S_b)`, `kNeg` is `-S_a`, `rv s` is `{s}`,
  `0` is `∅`, `1` is `{1}`.

  **The single-candidate form is false**, and the reason is worth recording, because it is
  exactly the shape the cover direction f1 was stated in: `mul 0 b = 0` forgets the value of `b`
  (`rvMulInfty`), so the value of `kAdd (mul a b) 1` on the region where `a = 0` is `rv 1`,
  independently of the value of `b`; a single `L_val`-term `s` would have to be `≡ 1` there
  (the region is valuation-open, hence Zariski dense, so `s = 1` as a polynomial), but on the
  region where `a = rv(v0+v1)`, `b = rv v2` with `rv((v0+v1)v2) = 1` and `(v0+v1)v2 = -1` the
  term is `kAdd (rv(-1)) (rv 1) = 0`, where `rv s = rv 1 ≠ 0`. Hence no single `s` works; a finite
  set does.  See `REPORT.md`.

  Repair axioms used (all named at the use site):
  * `Axioms.rvMulHom`, `Axioms.rvMulInfty`, `Axioms.rvEqInfty`, `Axioms.kField` (zero law and
    commutativity of `kAdd` on `K`), `Axioms.sdRVMul`, `Axioms.sdKAdd`, `Axioms.sdKNeg`,
    `Axioms.sdRv` — frozen `ACVF`;
  * `kAddLink` (the residue addition at units, two cases), `kNegLink` (residue negation at units),
    `kJunkZero`, `kNegJunkZero` — the residue links, defined below because they are not in the
    `Pre` snapshot (they are `Axioms.kAddLink` etc. in the working tree).

  Only import: `Pre`.  No `sorry`, no `axiom`, no `native_decide`.
-/

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open scoped FirstOrder
open SpecialTransformations.Milestone0
open SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Axioms
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Milestone0.Transfer.M2
open Cover

namespace RVNF

variable {M : Type} [LRV.Structure M]

/-! ## 1. The residue links (copies of `Axioms.kAddLink` etc. of the working tree) -/

/-- `kAdd` is the residue addition at units: `kAdd (rv x) (rv y) = rv (x+y)` if that is a unit, and
`0` if it is not. -/
def kAddLink : LRV.Sentence :=
  allSorted ![.vf, .vf]
    (pUnits (tRv &0) ⟹ (pUnits (tRv &1) ⟹
      ((pUnits (tRv (tVFAdd &0 &1)) ⟹
          pEq (tKAdd (tRv &0) (tRv &1)) (tRv (tVFAdd &0 &1))) ⊓
        (∼(pUnits (tRv (tVFAdd &0 &1))) ⟹
          pEq (tKAdd (tRv &0) (tRv &1)) tRVZero))))

/-- `kNeg` is the residue negation at units. -/
def kNegLink : LRV.Sentence :=
  allSorted ![.vf] (pUnits (tRv &0) ⟹ pEq (tKNeg (tRv &0)) (tRv (tVFNeg &0)))

/-- The junk convention for `kAdd` off `K`. -/
def kJunkZero : LRV.Sentence :=
  allSorted ![.rv, .rv] ((∼(pInK &0) ⊔ ∼(pInK &1)) ⟹ pEq (tKAdd &0 &1) tRVZero)

/-- The junk convention for `kNeg` off `K`. -/
def kNegJunkZero : LRV.Sentence := allSorted ![.rv] (∼(pInK &0) ⟹ pEq (tKNeg &0) tRVZero)

/-- The residue links, as a theory. -/
def residueLink : LRV.Theory := ofList [kAddLink, kNegLink, kJunkZero, kNegJunkZero]

/-- **The theory this file works in**: the frozen `ACVF` plus the residue links. -/
def ACVFrep : LRV.Theory := Axioms.ACVF ∪ residueLink ∪ {Transfer.M2.rvFibreIff}

theorem acvf_of_repair (h : M ⊨ ACVFrep) : M ⊨ Axioms.ACVF :=
  Theory.Model.mono h (fun s hs => Or.inl (Or.inl hs))

theorem mem_repair_of_link {s : LRV.Sentence} (hs : s ∈ residueLink) : s ∈ ACVFrep :=
  Or.inl (Or.inr hs)

theorem mem_repair_kAddLink : kAddLink ∈ ACVFrep := mem_repair_of_link (by simp [residueLink, Axioms.ofList])

theorem mem_repair_kNegLink : kNegLink ∈ ACVFrep := mem_repair_of_link (by simp [residueLink, Axioms.ofList])

theorem mem_repair_kJunkZero : kJunkZero ∈ ACVFrep := mem_repair_of_link (by simp [residueLink, Axioms.ofList])

theorem mem_repair_kNegJunkZero : kNegJunkZero ∈ ACVFrep :=
  mem_repair_of_link (by simp [residueLink, Axioms.ofList])

theorem mem_repair_rvFibre : Transfer.M2.rvFibreIff ∈ ACVFrep := Or.inr (by simp)

end RVNF

namespace RVNF

variable {M : Type} [LRV.Structure M]

/-! ## 2. The semantic form of the residue links -/

/-- The semantic form of `kAddLink`. -/
def KAddAdditive (M : Type) [LRV.Structure M] : Prop :=
  ∀ x y : M, iVF x → iVF y → iUnits (iRv x) → iUnits (iRv y) →
    ((iUnits (iRv (iVFAdd x y)) → iKAdd (iRv x) (iRv y) = iRv (iVFAdd x y)) ∧
      (¬ iUnits (iRv (iVFAdd x y)) → iKAdd (iRv x) (iRv y) = iRVZero))

theorem kAddAdditive_of_repair (h : M ⊨ ACVFrep) : KAddAdditive M := by
  intro x y hx hy hxu hyu
  have h' := allSorted_realize (T := ACVFrep) h (ss := ![SortTag.vf, SortTag.vf])
    (φ := (pUnits (tRv &0) ⟹ (pUnits (tRv &1) ⟹
      ((pUnits (tRv (tVFAdd &0 &1)) ⟹
          pEq (tKAdd (tRv &0) (tRv &1)) (tRv (tVFAdd &0 &1))) ⊓
        (∼(pUnits (tRv (tVFAdd &0 &1))) ⟹
          pEq (tKAdd (tRv &0) (tRv &1)) tRVZero))))) mem_repair_kAddLink ![x, y]
    (by intro i; fin_cases i <;> simp [hx, hy])
  simp only [BoundedFormula.realize_imp, BoundedFormula.realize_inf, pUnits_realize,
    pEq, BoundedFormula.realize_bdEqual, BoundedFormula.realize_not, Transfer.realize_tRv,
    TrivCase.realize_tKAdd, Transfer.realize_tVFAdd, Transfer.realize_tRVZero,
    realize_tv, Term.realize_var, Sum.elim_inr, Function.comp_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons] at h'
  exact h' hxu hyu

/-- The semantic form of `kNegLink`. -/
theorem kNegLink_sem (h : M ⊨ ACVFrep) {x : M} (hx : iVF x) (hu : iUnits (iRv x)) :
    TrivCase.iKNeg (iRv x) = iRv (iVFNeg x) := by
  have h' := allSorted_realize (T := ACVFrep) h (ss := ![SortTag.vf])
    (φ := (pUnits (tRv &0) ⟹ pEq (tKNeg (tRv &0)) (tRv (tVFNeg &0)))) mem_repair_kNegLink
    ![x] (by intro i; fin_cases i; simpa using hx)
  simp only [BoundedFormula.realize_imp, pUnits_realize, pEq, BoundedFormula.realize_bdEqual,
    Transfer.realize_tRv, TrivCase.realize_tKNeg, Transfer.realize_tVFNeg, realize_tv,
    Term.realize_var, Sum.elim_inr, Function.comp_apply, Matrix.cons_val_zero] at h'
  exact h' hu

/-- The semantic form of `kJunkZero`. -/
theorem kJunkZero_sem (h : M ⊨ ACVFrep) {a b : M} (ha : iRV a) (hb : iRV b)
    (hK : ¬(iUnits a ∨ a = iRVZero) ∨ ¬(iUnits b ∨ b = iRVZero)) : iKAdd a b = iRVZero := by
  have h' := allSorted_realize (T := ACVFrep) h (ss := ![SortTag.rv, SortTag.rv])
    (φ := ((∼(pInK &0) ⊔ ∼(pInK &1)) ⟹ pEq (tKAdd &0 &1) tRVZero)) mem_repair_kJunkZero
    ![a, b] (by intro i; fin_cases i <;> simp [ha, hb])
  simp only [BoundedFormula.realize_imp, BoundedFormula.realize_sup, BoundedFormula.realize_not,
    TrivCase.pInK_realize, pEq, BoundedFormula.realize_bdEqual, TrivCase.realize_tKAdd,
    Transfer.realize_tRVZero, realize_tv, Term.realize_var, Sum.elim_inr, Function.comp_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h'
  exact h' hK

/-- The semantic form of `kNegJunkZero`. -/
theorem kNegJunkZero_sem (h : M ⊨ ACVFrep) {a : M} (ha : iRV a)
    (hK : ¬(iUnits a ∨ a = iRVZero)) : TrivCase.iKNeg a = iRVZero := by
  have h' := allSorted_realize (T := ACVFrep) h (ss := ![SortTag.rv])
    (φ := (∼(pInK &0) ⟹ pEq (tKNeg &0) tRVZero)) mem_repair_kNegJunkZero ![a]
    (by intro i; fin_cases i; simpa using ha)
  simp only [BoundedFormula.realize_imp, BoundedFormula.realize_not, TrivCase.pInK_realize,
    pEq, BoundedFormula.realize_bdEqual, TrivCase.realize_tKNeg, Transfer.realize_tRVZero,
    realize_tv, Term.realize_var, Sum.elim_inr, Function.comp_apply, Matrix.cons_val_zero] at h'
  exact h' hK

end RVNF

namespace RVNF

variable {M : Type} [LRV.Structure M]

/-! ## 3. One-step lemmas: `×`, `+`, `-` on `rv`-images -/

theorem mem_ACVF_rvMulComm : Axioms.rvMulComm ∈ Axioms.ACVF :=
  M2.mem_ACVF_rvGroup (by simp [Axioms.rvGroup, Axioms.ofList])

theorem mem_ACVF_rvMulInfty : Axioms.rvMulInfty ∈ Axioms.ACVF :=
  M2.mem_ACVF_rvGroup (by simp [Axioms.rvGroup, Axioms.ofList])

/-- `×` of `RV` is commutative, for `RV`-elements. -/
theorem iRVMul_comm (h : M ⊨ ACVFrep) {a b : M} (ha : iRV a) (hb : iRV b) :
    iRVMul a b = iRVMul b a := by
  have hA : M ⊨ Axioms.ACVF := acvf_of_repair h
  have h' := allSorted_realize hA (T := Axioms.ACVF) (ss := ![SortTag.rv, SortTag.rv])
    (φ := pEq (tRVMul &0 &1) (tRVMul &1 &0)) mem_ACVF_rvMulComm ![a, b]
    (by intro i; fin_cases i <;> simp [ha, hb])
  simpa [pEq, BoundedFormula.realize_bdEqual, Transfer.realize_tRVMul, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons] using h'

/-- `×` of `RV` stays in the `RV` sort. -/
theorem iRVMul_mem (h : M ⊨ ACVFrep) {a b : M} (ha : iRV a) (hb : iRV b) : iRV (iRVMul a b) := by
  have hA : M ⊨ Axioms.ACVF := acvf_of_repair h
  have hmem : Axioms.sdRVMul ∈ Axioms.ACVF :=
    Transfer.mem_ACVF_sortClosure (by simp [Axioms.sortClosure, Axioms.ofList])
  have h' := allSorted_realize hA (T := Axioms.ACVF) (ss := ![SortTag.rv, SortTag.rv])
    (φ := pRVsort (tRVMul &0 &1)) hmem ![a, b] (by intro i; fin_cases i <;> simp [ha, hb])
  simpa [Transfer.pRVsort_realize, Transfer.realize_tRVMul, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons] using h'

/-- `0` is absorbing for `×` on the left. -/
theorem iRVMul_zero_left (h : M ⊨ ACVFrep) {b : M} (hb : iRV b) :
    iRVMul iRVZero b = iRVZero := by
  have hA : M ⊨ Axioms.ACVF := acvf_of_repair h
  rw [iRVMul_comm h (TrivCase.iRV_rvZero hA) hb]
  exact M2.rv_mul_infty hA hb

/-- `0` is absorbing for `×` on the right. -/
theorem iRVMul_zero_right (h : M ⊨ ACVFrep) {a : M} (ha : iRV a) :
    iRVMul a iRVZero = iRVZero := by
  have hA : M ⊨ Axioms.ACVF := acvf_of_repair h
  exact M2.rv_mul_infty hA ha

/-- `×` of two `rv`-images is the `rv` of the product (`Axioms.rvMulHom`). -/
theorem iRVMul_rv (h : M ⊨ ACVFrep) {x y : M} (hx : iVF x) (hy : iVF y) :
    iRVMul (iRv x) (iRv y) = iRv (iVFMul x y) := by
  have hA : M ⊨ Axioms.ACVF := acvf_of_repair h
  exact (Transfer.rv_mul_hom hA hx hy).symm

/-- `kAdd 0 0 = 0` (`Axioms.kField`: `0` is neutral for `+` on `K`). -/
theorem iKAdd_zero_zero (h : M ⊨ ACVFrep) :
    iKAdd (iRVZero (M := M)) (iRVZero (M := M)) = iRVZero := by
  have hA : M ⊨ Axioms.ACVF := acvf_of_repair h
  exact TrivCase.kAdd_zero_right hA (Or.inr rfl)

/-- **`kAdd 0 (rv y)`** is `rv y` if `rv y ∈ K`, and `0` otherwise. -/
theorem iKAdd_zero_rv (h : M ⊨ ACVFrep) {y : M} (hy : iVF y) :
    iKAdd iRVZero (iRv y) = iRv y ∨ iKAdd iRVZero (iRv y) = iRVZero := by
  have hA : M ⊨ Axioms.ACVF := acvf_of_repair h
  by_cases hu : iUnits (iRv y)
  · exact Or.inl (TrivCase.kAdd_zero_left hA (Or.inl hu))
  · by_cases h0 : iRv y = iRVZero
    · right; rw [h0]; exact iKAdd_zero_zero h
    · right
      exact kJunkZero_sem h (TrivCase.iRV_rvZero hA) (Transfer.rv_mem hA hy)
        (Or.inr (by rintro (h' | h'); exact hu h'; exact h0 h'))

/-- **`kAdd (rv x) 0`** is `rv x` if `rv x ∈ K`, and `0` otherwise. -/
theorem iKAdd_rv_zero (h : M ⊨ ACVFrep) {x : M} (hx : iVF x) :
    iKAdd (iRv x) iRVZero = iRv x ∨ iKAdd (iRv x) iRVZero = iRVZero := by
  have hA : M ⊨ Axioms.ACVF := acvf_of_repair h
  by_cases hu : iUnits (iRv x)
  · exact Or.inl (TrivCase.kAdd_zero_right hA (Or.inl hu))
  · by_cases h0 : iRv x = iRVZero
    · left; rw [h0]; exact iKAdd_zero_zero h
    · right
      exact kJunkZero_sem h (Transfer.rv_mem hA hx) (TrivCase.iRV_rvZero hA)
        (Or.inl (by rintro (h' | h'); exact hu h'; exact h0 h'))

/-- **`kAdd (rv x) (rv y)`**: the two cases of `kAddLink`, and the junk cases of `kJunkZero`. -/
theorem iKAdd_rv_rv (h : M ⊨ ACVFrep) {x y : M} (hx : iVF x) (hy : iVF y) :
    (iUnits (iRv x) → iUnits (iRv y) → iUnits (iRv (iVFAdd x y)) →
        iKAdd (iRv x) (iRv y) = iRv (iVFAdd x y)) ∧
      (iUnits (iRv x) → iUnits (iRv y) → ¬ iUnits (iRv (iVFAdd x y)) →
        iKAdd (iRv x) (iRv y) = iRVZero) ∧
      (¬ iUnits (iRv x) → iRv x ≠ iRVZero → iKAdd (iRv x) (iRv y) = iRVZero) ∧
      (¬ iUnits (iRv y) → iRv y ≠ iRVZero → iKAdd (iRv x) (iRv y) = iRVZero) := by
  have hA : M ⊨ Axioms.ACVF := acvf_of_repair h
  refine ⟨fun hu1 hu2 hs => (kAddAdditive_of_repair h x y hx hy hu1 hu2).1 hs,
    fun hu1 hu2 hs => (kAddAdditive_of_repair h x y hx hy hu1 hu2).2 hs, ?_, ?_⟩
  · intro hu h0
    exact kJunkZero_sem h (Transfer.rv_mem hA hx) (Transfer.rv_mem hA hy)
      (Or.inl (by rintro (h' | h'); exact hu h'; exact h0 h'))
  · intro hu h0
    exact kJunkZero_sem h (Transfer.rv_mem hA hx) (Transfer.rv_mem hA hy)
      (Or.inr (by rintro (h' | h'); exact hu h'; exact h0 h'))

/-- **`kNeg (rv x)`**: the residue negation at units, and the junk convention. -/
theorem iKNeg_rv (h : M ⊨ ACVFrep) {x : M} (hx : iVF x) :
    (iUnits (iRv x) → TrivCase.iKNeg (iRv x) = iRv (iVFNeg x)) ∧
      (¬ iUnits (iRv x) → TrivCase.iKNeg (iRv x) = iRVZero) := by
  have hA : M ⊨ Axioms.ACVF := acvf_of_repair h
  refine ⟨fun hu => kNegLink_sem h hx hu, fun hu => ?_⟩
  by_cases h0 : iRv x = iRVZero
  · rw [h0]; exact TrivCase.kNeg_zero hA
  · exact kNegJunkZero_sem h (Transfer.rv_mem hA hx)
      (by rintro (h' | h'); exact hu h'; exact h0 h')

/-- `kNeg 0 = 0`. -/
theorem iKNeg_zero (h : M ⊨ ACVFrep) :
    TrivCase.iKNeg (iRVZero (M := M)) = iRVZero :=
  TrivCase.kNeg_zero (acvf_of_repair h)

/-- `rv x = 0` iff `x = 0` (`Axioms.rvEqInfty` and `Axioms.rvZeroEq`). -/
theorem iRv_eq_zero_iff (h : M ⊨ ACVFrep) {x : M} (hx : iVF x) :
    iRv x = iRVZero ↔ x = iVFZero :=
  ⟨fun h' => Transfer.rv_eq_infty (acvf_of_repair h) hx h',
    fun h' => by rw [h', Transfer.rv_zero_eq (acvf_of_repair h)]⟩

end RVNF

namespace RVNF

variable {M : Type} [LRV.Structure M]

/-! ## 4. `RV`-terms, their two readings, and their candidate lists -/

/-- `RV`-sorted terms of `L_RV` built from `VF`-terms and `rv`.  There are no `RV`-sorted
variables: the cover eliminates those (direction f3), and the class below is what the
substitution `y ↦ rv x` produces. -/
inductive RVTerm (n : ℕ) : Type
  /-- `0` of the `RV` sort (= the paper's `∞`) -/
  | zero : RVTerm n
  /-- `1` of the `RV` sort -/
  | one : RVTerm n
  /-- `×` of the `RV` sort -/
  | mul : RVTerm n → RVTerm n → RVTerm n
  /-- `+` of the residue field `K` -/
  | kadd : RVTerm n → RVTerm n → RVTerm n
  /-- `-` of the residue field `K` -/
  | kneg : RVTerm n → RVTerm n
  /-- `rv` of a `VF`-term -/
  | rv : VFTm n → RVTerm n

namespace RVTerm

variable {n : ℕ}

/-- The `L_RV`-term underlying an `RV`-term. -/
def toLRV : RVTerm n → Tm n
  | zero => tRVZero
  | one => tRVOne
  | mul a b => tRVMul a.toLRV b.toLRV
  | kadd a b => tKAdd a.toLRV b.toLRV
  | kneg a => tKNeg a.toLRV
  | rv s => tRv s.toLRV

/-- The `L_val`-term attached to an `RV`-term, read as a value. -/
def valT : RVTerm n → Language.val.Term (Empty ⊕ Fin n)
  | zero => 0
  | one => 1
  | mul a b => a.valT * b.valT
  | kadd a b => a.valT + b.valT
  | kneg a => -a.valT
  | rv s => s.toVal

/-- **The candidate list**: the `L_val`-terms whose `rv`-image covers the term pointwise.

`kAdd` needs the union `S_a ∪ S_b ∪ (S_a + S_b)`: the extra `S_a`, `S_b` are exactly the
`kAdd 0 b = b` / `kAdd a 0 = a` cases, in which the value of the zero argument is lost
(`rvMulInfty` / `kAdd` at `0`) and a single candidate `S_a + S_b` would be wrong. -/
def vals : RVTerm n → List (Language.val.Term (Empty ⊕ Fin n))
  | zero => []
  | one => [1]
  | mul a b => a.vals.flatMap (fun s => b.vals.map (fun t => s * t))
  | kadd a b => a.vals ++ b.vals ++ a.vals.flatMap (fun s => b.vals.map (fun t => s + t))
  | kneg a => a.vals.map (fun s => -s)
  | rv s => [s.toVal]

/-- The direct semantic recursion for an `RV`-term. -/
def evalM (x : Fin n → M) : RVTerm n → M
  | zero => iRVZero
  | one => iRVOne
  | mul a b => iRVMul (evalM x a) (evalM x b)
  | kadd a b => iKAdd (evalM x a) (evalM x b)
  | kneg a => TrivCase.iKNeg (evalM x a)
  | rv s => iRv (Term.realize (Sum.elim (default : Empty → M) x) s.toLRV)

/-- The realization of `toLRV` is `evalM`. -/
theorem realize_toLRV {M : Type} [LRV.Structure M] (x : Fin n → M) (t : RVTerm n) :
    Term.realize (Sum.elim (default : Empty → M) x) t.toLRV = t.evalM x := by
  induction t with
  | zero => simp [toLRV, evalM, Transfer.realize_tRVZero]
  | one => simp [toLRV, evalM, Cover.realize_tRVOne]
  | mul a b iha ihb => simp only [toLRV, evalM, Transfer.realize_tRVMul, iha, ihb]
  | kadd a b iha ihb => simp only [toLRV, evalM, TrivCase.realize_tKAdd, iha, ihb]
  | kneg a iha => simp only [toLRV, evalM, TrivCase.realize_tKNeg, iha]
  | rv s => simp only [toLRV, evalM, Transfer.realize_tRv]

end RVTerm
end RVNF

namespace RVNF

variable {M : Type} [LRV.Structure M] {n : ℕ}

@[simp] theorem valTermEval_mul (x : Fin n → M)
    (a b : Language.val.Term (Empty ⊕ Fin n)) :
    valTermEval x (a * b) = iVFMul (valTermEval x a) (valTermEval x b) := rfl

/-- **The `RV`-term normal form.**  Every `RV`-sorted `L_RV`-term built from `VF`-terms is, at
every tuple of `VF`-elements of a model of `ACVFrep`, pointwise either `0` or the `rv` of one of
the finitely many `L_val`-terms in its candidate list `vals`.

Each constructor uses exactly one link:
* `rv` — nothing;
* `one` — `Axioms.rvMulHom`-free: `rv 1 = 1` (`M2.rv_one_eq`, from `rvMulHom` + `rvSurj`);
* `mul` — `Axioms.rvMulHom` when both factors are nonzero, `Axioms.rvMulInfty` when one is `0`;
* `kadd` — `kAddLink` (both arguments units: two cases according to whether the sum is a unit),
  `kJunkZero` (an argument off `K`), `Axioms.kField`'s zero law + commutativity (`kAdd 0 b = b`
  for `b ∈ K`), and `iKAdd_zero_zero`;
* `kneg` — `kNegLink` at units, `kNegJunkZero` off `K`, `TrivCase.kNeg_zero` at `0`. -/
theorem exists_normal (h : M ⊨ ACVFrep) (x : Fin n → M) (hx : ∀ i, iVF (x i)) :
    ∀ t : RVTerm n, t.evalM x = iRVZero ∨ ∃ s ∈ t.vals, t.evalM x = iRv (valTermEval x s) := by
  have hA : M ⊨ Axioms.ACVF := acvf_of_repair h
  intro t
  induction t with
  | zero => exact Or.inl rfl
  | one =>
    refine Or.inr ⟨1, by simp [RVTerm.vals], ?_⟩
    simp only [RVTerm.evalM]
    rw [M2.valTermEval_one, M2.rv_one_eq hA]
  | rv s =>
    refine Or.inr ⟨s.toVal, by simp [RVTerm.vals], ?_⟩
    simp only [RVTerm.evalM]
    rw [VFTm.realize_toLRV]
  | mul a b iha ihb =>
    rcases iha with ha | ⟨sa, hsa, ha⟩ <;> rcases ihb with hb | ⟨sb, hsb, hb⟩
    · refine Or.inl ?_
      simp only [RVTerm.evalM]
      rw [ha, hb, iRVMul_zero_left h (TrivCase.iRV_rvZero hA)]
    · refine Or.inl ?_
      simp only [RVTerm.evalM]
      rw [ha, hb]
      exact iRVMul_zero_left h
        (Transfer.rv_mem hA (M2.valTermEval_mem hA hx sb))
    · refine Or.inl ?_
      simp only [RVTerm.evalM]
      rw [ha, hb]
      exact iRVMul_zero_right h (Transfer.rv_mem hA (M2.valTermEval_mem hA hx sa))
    · refine Or.inr ⟨sa * sb, ?_, ?_⟩
      · simp only [RVTerm.vals, List.mem_flatMap, List.mem_map]
        exact ⟨sa, hsa, sb, hsb, rfl⟩
      simp only [RVTerm.evalM]
      rw [ha, hb, iRVMul_rv h (M2.valTermEval_mem hA hx sa) (M2.valTermEval_mem hA hx sb)]
      rw [valTermEval_mul]
  | kneg a iha =>
    rcases iha with ha | ⟨sa, hsa, ha⟩
    · refine Or.inl ?_
      simp only [RVTerm.evalM]
      rw [ha, iKNeg_zero h]
    · obtain ⟨hunit, hjunk⟩ := iKNeg_rv h (M2.valTermEval_mem hA hx sa)
      by_cases hu : iUnits (iRv (valTermEval x sa))
      · refine Or.inr ⟨-sa, ?_, ?_⟩
        · simp only [RVTerm.vals, List.mem_map]
          exact ⟨sa, hsa, rfl⟩
        simp only [RVTerm.evalM]
        rw [ha, hunit hu, ← M2.valTermEval_neg]
      · by_cases h0 : iRv (valTermEval x sa) = iRVZero
        · refine Or.inl ?_
          simp only [RVTerm.evalM]
          rw [ha, h0, iKNeg_zero h]
        · refine Or.inl ?_
          simp only [RVTerm.evalM]
          rw [ha, hjunk hu]
  | kadd a b iha ihb =>
    rcases iha with ha0 | ⟨sa, hsa, ha⟩ <;> rcases ihb with hb0 | ⟨sb, hsb, hb⟩
    · -- a = 0, b = 0
      refine Or.inl ?_
      simp only [RVTerm.evalM]
      rw [ha0, hb0, iKAdd_zero_zero h]
    · -- a = 0, b = rv sb
      simp only [RVTerm.evalM]
      rw [ha0, hb]
      rcases iKAdd_zero_rv h (M2.valTermEval_mem hA hx sb) with hz | hz
      · refine Or.inr ⟨sb, ?_, hz⟩
        simp only [RVTerm.vals, List.mem_append]
        exact Or.inl (Or.inr hsb)
      · exact Or.inl hz
    · -- a = rv sa, b = 0
      simp only [RVTerm.evalM]
      rw [ha, hb0]
      rcases iKAdd_rv_zero h (M2.valTermEval_mem hA hx sa) with hz | hz
      · refine Or.inr ⟨sa, ?_, hz⟩
        simp only [RVTerm.vals, List.mem_append]
        exact Or.inl (Or.inl hsa)
      · exact Or.inl hz
    · -- a = rv sa, b = rv sb
      simp only [RVTerm.evalM]
      rw [ha, hb]
      obtain ⟨hl1, hl2, hl3, hl4⟩ :=
        iKAdd_rv_rv h (M2.valTermEval_mem hA hx sa) (M2.valTermEval_mem hA hx sb)
      by_cases hua : iUnits (iRv (valTermEval x sa))
      · by_cases hub : iUnits (iRv (valTermEval x sb))
        · by_cases hus : iUnits (iRv (iVFAdd (valTermEval x sa) (valTermEval x sb)))
          · refine Or.inr ⟨sa + sb, ?_, ?_⟩
            · simp only [RVTerm.vals, List.mem_append, List.mem_flatMap, List.mem_map]
              exact Or.inr ⟨sa, hsa, sb, hsb, rfl⟩
            rw [show valTermEval x (sa + sb)
              = iVFAdd (valTermEval x sa) (valTermEval x sb) from M2.valTermEval_add x sa sb]
            exact hl1 hua hub hus
          · exact Or.inl (hl2 hua hub hus)
        · by_cases hb0' : iRv (valTermEval x sb) = iRVZero
          · rw [hb0']
            rcases iKAdd_rv_zero h (M2.valTermEval_mem hA hx sa) with hz | hz
            · refine Or.inr ⟨sa, ?_, hz⟩
              simp only [RVTerm.vals, List.mem_append]
              exact Or.inl (Or.inl hsa)
            · exact Or.inl hz
          · exact Or.inl (hl4 hub hb0')
      · by_cases ha0' : iRv (valTermEval x sa) = iRVZero
        · rw [ha0']
          rcases iKAdd_zero_rv h (M2.valTermEval_mem hA hx sb) with hz | hz
          · refine Or.inr ⟨sb, ?_, hz⟩
            simp only [RVTerm.vals, List.mem_append]
            exact Or.inl (Or.inr hsb)
          · exact Or.inl hz
        · exact Or.inl (hl3 hua ha0')

/-- The same, read back through `Term.realize`: the realization of the `L_RV`-term `t.toLRV`. -/
theorem realize_normal (h : M ⊨ ACVFrep) (x : Fin n → M) (hx : ∀ i, iVF (x i))
    (t : RVTerm n) :
    Term.realize (Sum.elim (default : Empty → M) x) t.toLRV = iRVZero ∨
      ∃ s ∈ t.vals,
        Term.realize (Sum.elim (default : Empty → M) x) t.toLRV = iRv (valTermEval x s) := by
  rw [RVTerm.realize_toLRV]
  exact exists_normal h x hx t

end RVNF

namespace RVNF

variable {M : Type} [LRV.Structure M]

/-! ## 5. The residue operations always land in `K = Kˣ ∪ {0}`

These are the sort facts the formula-level cover needs at a *composite* `RV`-term: `kAdd` and
`kNeg` of `RV`-elements are always in `K`, so the next `kField`/`kAddLink`-guarded step applies.
`Axioms.sdKAdd`/`Axioms.sdKNeg` give the `K`-case (`TrivCase.inK_kAdd`, `TrivCase.inK_kNeg`);
`kJunkZero`/`kNegJunkZero` give the junk case. -/

/-- `kAdd` of two `RV`-elements is in `K`. -/
theorem iKAdd_mem_K (h : M ⊨ ACVFrep) {a b : M} (ha : iRV a) (hb : iRV b) :
    iUnits (iKAdd a b) ∨ iKAdd a b = iRVZero := by
  have hA : M ⊨ Axioms.ACVF := acvf_of_repair h
  by_cases haK : iUnits a ∨ a = iRVZero
  · by_cases hbK : iUnits b ∨ b = iRVZero
    · exact TrivCase.inK_kAdd hA haK hbK
    · rw [kJunkZero_sem h ha hb (Or.inr hbK)]
      exact Or.inr rfl
  · rw [kJunkZero_sem h ha hb (Or.inl haK)]
    exact Or.inr rfl

/-- `kNeg` of an `RV`-element is in `K`. -/
theorem iKNeg_mem_K (h : M ⊨ ACVFrep) {a : M} (ha : iRV a) :
    iUnits (TrivCase.iKNeg a) ∨ TrivCase.iKNeg a = iRVZero := by
  have hA : M ⊨ Axioms.ACVF := acvf_of_repair h
  by_cases haK : iUnits a ∨ a = iRVZero
  · exact TrivCase.inK_kNeg hA haK
  · rw [kNegJunkZero_sem h ha haK]
    exact Or.inr rfl

/-- `kAdd` of two `RV`-elements is an `RV`-element. -/
theorem iRV_iKAdd (h : M ⊨ ACVFrep) {a b : M} (ha : iRV a) (hb : iRV b) : iRV (iKAdd a b) :=
  TrivCase.iRV_of_inK (acvf_of_repair h) (iKAdd_mem_K h ha hb)

/-- `kNeg` of an `RV`-element is an `RV`-element. -/
theorem iRV_iKNeg (h : M ⊨ ACVFrep) {a : M} (ha : iRV a) : iRV (TrivCase.iKNeg a) :=
  TrivCase.iRV_of_inK (acvf_of_repair h) (iKNeg_mem_K h ha)

/-- `kAdd` is commutative on `K` (`Axioms.kField`). -/
theorem iKAdd_comm_K (h : M ⊨ ACVFrep) {a b : M} (haK : iUnits a ∨ a = iRVZero)
    (hbK : iUnits b ∨ b = iRVZero) : iKAdd a b = iKAdd b a :=
  TrivCase.kAdd_comm (acvf_of_repair h) haK hbK

/-- `0` is neutral for `kAdd` on the left, on `K` (`Axioms.kField`). -/
theorem iKAdd_zero_left_K (h : M ⊨ ACVFrep) {a : M} (haK : iUnits a ∨ a = iRVZero) :
    iKAdd iRVZero a = a :=
  TrivCase.kAdd_zero_left (acvf_of_repair h) haK

end RVNF

/-! ## Axiom checks -/

#print axioms RVNF.kAddAdditive_of_repair
#print axioms RVNF.kNegLink_sem
#print axioms RVNF.kJunkZero_sem
#print axioms RVNF.kNegJunkZero_sem
#print axioms RVNF.iRVMul_comm
#print axioms RVNF.iRVMul_mem
#print axioms RVNF.iRVMul_zero_left
#print axioms RVNF.iRVMul_rv
#print axioms RVNF.iKAdd_zero_rv
#print axioms RVNF.iKAdd_rv_zero
#print axioms RVNF.iKAdd_rv_rv
#print axioms RVNF.iKNeg_rv
#print axioms RVNF.iRv_eq_zero_iff
#print axioms RVNF.RVTerm.realize_toLRV
#print axioms RVNF.exists_normal
#print axioms RVNF.realize_normal
#print axioms RVNF.iKAdd_mem_K
#print axioms RVNF.iKNeg_mem_K
#print axioms RVNF.iKAdd_comm_K

namespace RVNF

variable {M : Type} [LRV.Structure M] {n : ℕ}

/-! ## 6. The multiplicative fragment: an *exact* normal form, and its atom translations

For terms built from `0`, `1`, `×` and `rv` (no `kAdd`/`kNeg`) the disjunction of
`RVTerm.exists_normal` collapses: the term *is* `rv (valT)` at every tuple, with no case split.
Consequently the atoms `pLe`, `pEq`, `pUnits` at such terms are single quantifier-free `L_val`
formulas (`leF`, `leEqF`, `leOneF`).  This is the part of the cover that needs no guards; the
guards enter only with `kAdd`/`kNeg` (see `REPORT.md` §3). -/

/-- `RV`-terms in the multiplicative fragment: `0`, `1`, `×`, `rv` of a `VF`-term. -/
inductive MulTerm (n : ℕ) : Type
  | zero : MulTerm n
  | one : MulTerm n
  | mul : MulTerm n → MulTerm n → MulTerm n
  | rv : VFTm n → MulTerm n

namespace MulTerm

/-- The `L_RV`-term underlying a multiplicative `RV`-term. -/
def toLRV : MulTerm n → Tm n
  | zero => tRVZero
  | one => tRVOne
  | mul a b => tRVMul a.toLRV b.toLRV
  | rv s => tRv s.toLRV

/-- The `L_val`-term: the product of the `VF`-witnesses of the factors. -/
def valT : MulTerm n → Language.val.Term (Empty ⊕ Fin n)
  | zero => 0
  | one => 1
  | mul a b => a.valT * b.valT
  | rv s => s.toVal

/-- The semantic recursion. -/
def evalM (x : Fin n → M) : MulTerm n → M
  | zero => iRVZero
  | one => iRVOne
  | mul a b => iRVMul (evalM x a) (evalM x b)
  | rv s => iRv (Term.realize (Sum.elim (default : Empty → M) x) s.toLRV)

/-- **The exact normal form of the multiplicative fragment**: no disjunction, no case split. -/
theorem exact_normal (h : M ⊨ ACVFrep) (x : Fin n → M) (hx : ∀ i, iVF (x i)) (t : MulTerm n) :
    t.evalM x = iRv (valTermEval x t.valT) := by
  have hA : M ⊨ Axioms.ACVF := acvf_of_repair h
  induction t with
  | zero =>
    simp only [evalM, valT, M2.valTermEval_zero]
    exact (Transfer.rv_zero_eq hA).symm
  | one =>
    simp only [evalM, valT, M2.valTermEval_one]
    exact (M2.rv_one_eq hA).symm
  | mul a b iha ihb =>
    simp only [evalM, valT, valTermEval_mul]
    rw [iha, ihb,
      iRVMul_rv h (M2.valTermEval_mem hA hx a.valT) (M2.valTermEval_mem hA hx b.valT)]
  | rv s => simp only [evalM, valT, VFTm.realize_toLRV]

/-- The `L_RV`-realization version. -/
theorem exact_normal_realize (h : M ⊨ ACVFrep) (x : Fin n → M) (hx : ∀ i, iVF (x i))
    (t : MulTerm n) :
    Term.realize (Sum.elim (default : Empty → M) x) t.toLRV = iRv (valTermEval x t.valT) := by
  have hA : M ⊨ Axioms.ACVF := acvf_of_repair h
  induction t with
  | zero => simp only [toLRV, Transfer.realize_tRVZero, valT, M2.valTermEval_zero]
            exact (Transfer.rv_zero_eq hA).symm
  | one => simp only [toLRV, Cover.realize_tRVOne, valT, M2.valTermEval_one]
           exact (M2.rv_one_eq hA).symm
  | mul a b iha ihb =>
    simp only [toLRV, Transfer.realize_tRVMul, valT, valTermEval_mul]
    rw [iha, ihb,
      iRVMul_rv h (M2.valTermEval_mem hA hx a.valT) (M2.valTermEval_mem hA hx b.valT)]
  | rv s => simp only [toLRV, Transfer.realize_tRv, valT, VFTm.realize_toLRV]

/-- **The order atom** at multiplicative terms is the single `L_val` atom `leF`. -/
theorem le_atom (h : M ⊨ ACVFrep) (x : Fin n → M) (hx : ∀ i, iVF (x i))
    (t u : MulTerm n) :
    iLe (t.evalM x) (u.evalM x) ↔ valFormulaEval x (ValPM.leF u.valT t.valT) := by
  rw [exact_normal h x hx t, exact_normal h x hx u, M2.leF_valTerm_iff]

/-- **The equality atom** at multiplicative terms is the single quantifier-free `L_val` formula
`leEqF` (this uses `rvFibreIff`). -/
theorem eq_atom (h : M ⊨ ACVFrep) (x : Fin n → M) (hx : ∀ i, iVF (x i))
    (t u : MulTerm n) :
    t.evalM x = u.evalM x ↔ valFormulaEval x (M2.leEqF t.valT u.valT) := by
  have hA : M ⊨ Axioms.ACVF := acvf_of_repair h
  have hfib : M ⊨ ({M2.rvFibreIff} : LRV.Theory) :=
    Theory.Model.mono h (by
      intro s hs
      rw [Set.mem_singleton_iff] at hs
      subst hs
      exact mem_repair_rvFibre)
  rw [exact_normal h x hx t, exact_normal h x hx u]
  rw [M2.leEqF_iff_pEq hA hfib t.valT u.valT hx]
  simp only [pEq, BoundedFormula.realize_bdEqual, Transfer.realize_tRv,
    Transfer.valTermToRV_realize]

/-- **The `Kˣ` atom** at multiplicative terms is the single quantifier-free `L_val` formula
`leOneF`. -/
theorem units_atom (h : M ⊨ ACVFrep) (x : Fin n → M) (hx : ∀ i, iVF (x i)) (t : MulTerm n) :
    iUnits (t.evalM x) ↔ valFormulaEval x (M2.leOneF t.valT) := by
  have hA : M ⊨ Axioms.ACVF := acvf_of_repair h
  rw [exact_normal h x hx t, M2.leOneF_iff_pUnits hA t.valT hx, Transfer.pUnits_realize,
    Transfer.realize_tRv, Transfer.valTermToRV_realize]

end MulTerm

/-! ## Axiom checks for §6 -/

#print axioms RVNF.MulTerm.exact_normal
#print axioms RVNF.MulTerm.exact_normal_realize
#print axioms RVNF.MulTerm.le_atom
#print axioms RVNF.MulTerm.eq_atom
#print axioms RVNF.MulTerm.units_atom

end RVNF

#print axioms RVNF.exists_normal
#print axioms RVNF.realize_normal
#print axioms RVNF.realize_normal
