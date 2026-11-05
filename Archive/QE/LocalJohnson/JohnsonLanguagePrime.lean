/-
Johnson's Chapter 2 proof: valued-field language, theory, and prime models.
Extracted from the existing QE/Assembly_val.lean (sections 1–13).
Proofs are preserved; this module shares its definitions with the other
LocalJohnson modules instead of repeating standalone snapshots.
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

/-- Enlarging the target theory preserves the prime model property: fewer models
can witness that a substructure embeds in a model of the target theory. -/
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

/-- The valuation is nontrivial: some **nonzero** element lies in the maximal ideal,
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

/-- The nontriviality sentence asserts a nonzero element in the maximal ideal.
It is phrased with the value of the constant `1` rather than `(1 : M)`, because an
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

