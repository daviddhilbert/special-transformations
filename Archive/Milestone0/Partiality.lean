module

public import Mathlib

@[expose] public section

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.constructorNameAsVariable false

/-!
# Partial function symbols in Mathlib's `FirstOrder.Language`

Mathlib's first-order languages have **total** function symbols only:
`FirstOrder.Language.Structure.funMap : ∀ {n}, L.Functions n → (Fin n → M) → M`.

The language `L_RV` of Yin, *Special transformations in algebraically closed valued fields*
(APAL 2010, arXiv:1006.2467), Definition 2.1, is not of this shape: its RV-sort carries
`+ : K² → K` and `− : K → K` with `K = Kˣ ∪ {0}`, and the paper says so itself — the sentence
after Definition 2.1 of the source it quotes ([16] = arXiv:1006.1393, identical Def. 2.1):
"Technically speaking, the constant 0 and the functions +, − in the RV-sort should all be
relations."

This file settles the encoding question for such symbols, once and abstractly:

* `PartStruct L M` — an interpretation of the symbols of `L` in `M` in which function symbols
  are **partial** (`Option`-valued; `none` = undefined);
* `PEval P v t a` — the partial evaluation relation for `L`-terms;
* `PEval.toTotal P junk` — the **junk-value totalisation** of `P`, a genuine Mathlib
  `L.Structure M`;
* `PartStruct.ofTotal N dom` — the **read-back** of a partial structure from a total one.

Results (no `sorry`):

* `PEval.realize` — partial values are totalised values, for any junk value.
* `PEval.det` — partial values are unique.
* `PEval.ne_junk` — under `JunkFresh` and a junk-avoiding assignment no value is the junk value.
* `PartStruct.ofTotal_toTotal` — reading back the totalisation returns `P` **exactly**, so
  totalisation loses no structure at all.
* `PartStruct.toTotal_ofTotal_apply` — totalising the read-back of `N` returns `N` off the
  junk set.
* `PartStruct.exists_iff_realize_ne_junk` — under `JunkFresh` and `JunkProp`, for a
  junk-avoiding assignment a term has a partial value iff its totalised value is not junk.
* `PartStruct.iff_realize` — with `a ≠ junk` in addition: `PEval P v t a ↔ t.realize v = a`.
-/

namespace PartialFO

open FirstOrder FirstOrder.Language

universe u v w u'

variable {L : FirstOrder.Language.{u, v}} {M : Type w} {α : Type u'}

/-! ### Totalising an optional value -/

/-- Totalise an optional value with a junk value: `none` becomes `junk`. -/
def totalizeOpt {M : Type w} (junk : M) : Option M → M
  | some a => a
  | none => junk

@[simp]
theorem totalizeOpt_some {M : Type w} (junk : M) (a : M) : totalizeOpt junk (some a) = a := rfl

@[simp]
theorem totalizeOpt_none {M : Type w} (junk : M) : totalizeOpt junk (none : Option M) = junk := rfl

/-- If the totalised value is not the junk value then the value was defined. -/
theorem exists_of_totalizeOpt_ne {M : Type w} {junk : M} {o : Option M}
    (h : totalizeOpt junk o ≠ junk) : ∃ b, o = some b := by
  cases o with
  | none => exact absurd rfl h
  | some b => exact ⟨b, rfl⟩

/-- A **partial** `L`-structure: relation symbols as usual, function symbols as partial maps,
coded as `Option`-valued maps (`none` = undefined). -/
structure PartStruct (L : FirstOrder.Language.{u, v}) (M : Type w) where
  /-- Interpretation of a function symbol: `none` means "undefined at this tuple". -/
  funMap : ∀ {n}, L.Functions n → (Fin n → M) → Option M
  /-- Interpretation of a relation symbol. -/
  relMap : ∀ {n}, L.Relations n → (Fin n → M) → Prop

namespace PartStruct

@[ext]
theorem ext {P Q : PartStruct L M}
    (h₁ : ∀ {n} (f : L.Functions n) (xs : Fin n → M), P.funMap f xs = Q.funMap f xs)
    (h₂ : ∀ {n} (R : L.Relations n) (xs : Fin n → M), P.relMap R xs ↔ Q.relMap R xs) :
    P = Q := by
  obtain ⟨fm, rm⟩ := P
  obtain ⟨fm', rm'⟩ := Q
  have hfm : @fm = @fm' := by
    funext n f xs
    exact h₁ f xs
  have hrm : @rm = @rm' := by
    funext n R xs
    exact propext (h₂ R xs)
  rw [hfm, hrm]

/-- **Read-back.** From a total `L`-structure `N` and a domain predicate `dom`, recover a partial
structure: a symbol is defined at a tuple exactly when `dom` holds. -/
noncomputable def ofTotal (N : L.Structure M)
    (dom : ∀ {n}, L.Functions n → (Fin n → M) → Prop) : PartStruct L M := by
  classical
  exact
    { funMap := fun {_n} f xs => if dom f xs then some (N.funMap f xs) else none
      relMap := fun {_n} R xs => N.RelMap R xs }

/-- The junk value is **fresh** for `P`: no function symbol of `L` ever takes it as a value.
For `L_RV` with `junk = ∞` this is exactly the statement that `+` and `−` take values in
`K = RV0 \ {∞}`, so `∞ ∉ K`. -/
def JunkFresh (P : PartStruct L M) (junk : M) : Prop :=
  ∀ {n} (f : L.Functions n) (xs : Fin n → M), P.funMap f xs ≠ some junk

/-- The junk value **propagates** for `P`: a partial function symbol is undefined as soon as one
of its arguments is the junk value. For `L_RV` with `junk = ∞` this says `+` and `−` are
undefined whenever an argument is `∞`. -/
def JunkProp (P : PartStruct L M) (junk : M) : Prop :=
  ∀ {n} (f : L.Functions n) (xs : Fin n → M) (i : Fin n), xs i = junk → P.funMap f xs = none

end PartStruct

/-- Partial evaluation of an `L`-term in a partial `L`-structure: `PEval P v t a` says that `t`
evaluates to `a`. -/
inductive PEval (P : PartStruct L M) (v : α → M) : L.Term α → M → Prop
  | var (a : α) : PEval P v (.var a) (v a)
  | func {n : ℕ} (f : L.Functions n) (ts : Fin n → L.Term α) (xs : Fin n → M) (a : M)
      (hxs : ∀ i, PEval P v (ts i) (xs i)) (hdef : P.funMap f xs = some a) :
      PEval P v (.func f ts) a

namespace PEval

variable {P : PartStruct L M} {v : α → M} {t : L.Term α} {a : M}

/-- **Junk-value totalisation.** Choose `junk : M` and replace every partial map by the total map
returning `junk` where the partial map was undefined. This is Mathlib's `L.Structure M`. -/
@[instance_reducible]
def toTotal (P : PartStruct L M) (junk : M) : L.Structure M where
  funMap {_n} f xs := totalizeOpt junk (P.funMap f xs)
  RelMap {_n} R xs := P.relMap R xs

@[simp]
theorem toTotal_funMap (P : PartStruct L M) (junk : M) {n : ℕ} (f : L.Functions n)
    (xs : Fin n → M) : (toTotal P junk).funMap f xs = totalizeOpt junk (P.funMap f xs) := rfl

@[simp]
theorem toTotal_RelMap (P : PartStruct L M) (junk : M) {n : ℕ} (R : L.Relations n)
    (xs : Fin n → M) : (toTotal P junk).RelMap R xs = P.relMap R xs := rfl

/-- **Partial values are totalised values**, for any junk value. -/
theorem realize (junk : M) (h : PEval P v t a) :
    @Term.realize L M (toTotal P junk) α v t = a := by
  letI : L.Structure M := toTotal P junk
  induction h with
  | var a => rfl
  | func f ts xs a hxs hdef ih =>
    have hxs' : (fun i => Term.realize v (ts i)) = xs := funext ih
    rw [Term.realize_func, hxs']
    show totalizeOpt junk (P.funMap f xs) = a
    rw [hdef]
    rfl

/-- Partial values are unique. -/
theorem det (h : PEval P v t a) : ∀ {b : M}, PEval P v t b → a = b := by
  induction h with
  | var a =>
    intro b hb
    cases hb
    rfl
  | func f ts xs a hxs hdef ih =>
    intro b hb
    cases hb with
    | func f' ts' ys b' hys hdef' =>
      have hxy : xs = ys := by
        funext i
        exact ih i (hys i)
      subst hxy
      rw [hdef] at hdef'
      injection hdef' with hab

/-- A partial value is never the junk value, provided the assignment avoids the junk value and
the junk value is fresh. -/
theorem ne_junk (junk : M) (hfresh : P.JunkFresh junk) {v : α → M} (hv : ∀ a : α, v a ≠ junk)
    (h : PEval P v t a) : a ≠ junk := by
  induction h with
  | var a => exact hv a
  | func f ts xs a hxs hdef ih => exact fun hc => hfresh f xs (by rw [hdef, hc])

end PEval

namespace PartStruct

variable {P : PartStruct L M}

/-- **Totalisation loses nothing.** Reading back the totalisation of `P` along the domain of `P`
returns `P` exactly — for *any* junk value. -/
theorem ofTotal_toTotal (P : PartStruct L M) (junk : M) :
    ofTotal (PEval.toTotal P junk) (fun {_n} f xs => P.funMap f xs ≠ none) = P := by
  apply PartStruct.ext
  · intro n f xs
    simp only [ofTotal, PEval.toTotal_funMap]
    by_cases h : P.funMap f xs = none
    · simp [h]
    · obtain ⟨a, ha⟩ : ∃ a, P.funMap f xs = some a := by
        cases hh : P.funMap f xs with
        | none => exact absurd hh h
        | some b => exact ⟨b, rfl⟩
      simp [ha]
  · intro n R xs
    exact Iff.rfl

/-- **Read-back agrees off the junk set.** -/
theorem toTotal_ofTotal_apply (N : L.Structure M) (junk : M) {n : ℕ} (f : L.Functions n)
    (xs : Fin n → M) (h : N.funMap f xs ≠ junk) :
    (PEval.toTotal (ofTotal N (fun {_n} f xs => N.funMap f xs ≠ junk)) junk).funMap f xs =
      N.funMap f xs := by
  simp only [PEval.toTotal_funMap, ofTotal, if_pos h, totalizeOpt_some]

/-- Under `JunkFresh` and `JunkProp`, for a junk-avoiding assignment: a term has a partial value
iff its totalised value is not junk. -/
theorem exists_iff_realize_ne_junk (P : PartStruct L M) (junk : M) (hfresh : P.JunkFresh junk)
    (hprop : P.JunkProp junk) {v : α → M} (hv : ∀ a : α, v a ≠ junk) (t : L.Term α) :
    (∃ a, PEval P v t a) ↔ @Term.realize L M (PEval.toTotal P junk) α v t ≠ junk := by
  letI : L.Structure M := PEval.toTotal P junk
  induction t with
  | var a => exact ⟨fun _ => hv a, fun _ => ⟨v a, PEval.var a⟩⟩
  | @func n f ts ih =>
    constructor
    · rintro ⟨a, ha⟩
      have hne : a ≠ junk := PEval.ne_junk junk hfresh hv ha
      cases ha with
      | func _ _ xs _ hxs hdef =>
        have hxs' : (fun i => Term.realize v (ts i)) = xs := funext fun i =>
          PEval.realize junk (hxs i)
        rw [Term.realize_func, PEval.toTotal_funMap, hxs', hdef, totalizeOpt_some]
        exact hne
    · intro hval
      have hall : ∀ i, ∃ b, PEval P v (ts i) b := by
        intro i
        by_contra hcon
        have hz : Term.realize v (ts i) = junk := by
          by_contra hne
          exact hcon ((ih i).mpr hne)
        have hnone : P.funMap f (fun j => Term.realize v (ts j)) = none :=
          hprop f (fun j => Term.realize v (ts j)) i hz
        rw [Term.realize_func, PEval.toTotal_funMap, hnone, totalizeOpt_none] at hval
        exact hval rfl
      choose xs hxs using hall
      have harg : ∀ i, PEval P v (ts i) (Term.realize v (ts i)) := by
        intro i
        have h1 : Term.realize v (ts i) = xs i := PEval.realize junk (hxs i)
        rw [h1]
        exact hxs i
      have hsome : ∃ b, P.funMap f (fun i => Term.realize v (ts i)) = some b := by
        apply exists_of_totalizeOpt_ne
        rw [← PEval.toTotal_funMap, ← Term.realize_func]
        exact hval
      obtain ⟨b, hb⟩ := hsome
      exact ⟨b, PEval.func f ts (fun i => Term.realize v (ts i)) b harg hb⟩

/-- Under `JunkFresh` and `JunkProp`, for a junk-avoiding assignment and a non-junk value `a`:
`t` evaluates partially to `a` iff its totalised value is `a`. -/
theorem iff_realize (P : PartStruct L M) (junk : M) (hfresh : P.JunkFresh junk)
    (hprop : P.JunkProp junk) {v : α → M} (hv : ∀ a : α, v a ≠ junk) (t : L.Term α) (a : M)
    (ha : a ≠ junk) :
    PEval P v t a ↔ @Term.realize L M (PEval.toTotal P junk) α v t = a := by
  letI : L.Structure M := PEval.toTotal P junk
  constructor
  · intro h
    exact PEval.realize junk h
  · intro h
    have hne : Term.realize v t ≠ junk := by rw [h]; exact ha
    obtain ⟨b, hb⟩ := (exists_iff_realize_ne_junk P junk hfresh hprop hv t).mpr hne
    have h2 : Term.realize v t = b := PEval.realize junk hb
    rw [h] at h2
    exact h2 ▸ hb

/-! ### Formulas -/

/-- **Partial satisfaction**, strict in function symbols: an atomic formula is satisfied only when
all of its terms are defined. -/
def pSat (P : PartStruct L M) : ∀ {l : ℕ}, L.BoundedFormula α l → (α → M) → (Fin l → M) → Prop
  | _, .falsum, _, _ => False
  | _, .equal t₁ t₂, v, xs => ∃ a, PEval P (Sum.elim v xs) t₁ a ∧ PEval P (Sum.elim v xs) t₂ a
  | _, .rel R ts, v, xs =>
      ∃ ys : Fin _ → M, (∀ i, PEval P (Sum.elim v xs) (ts i) (ys i)) ∧ P.relMap R ys
  | _, .imp φ ψ, v, xs => pSat P φ v xs → pSat P ψ v xs
  | _, .all φ, v, xs => ∀ a : M, pSat P φ v (Fin.snoc xs a)

/-- Every term occurring in the formula has a partial value at the assignment. -/
def DefinedAt (P : PartStruct L M) :
    ∀ {l : ℕ}, L.BoundedFormula α l → (α → M) → (Fin l → M) → Prop
  | _, .falsum, _, _ => True
  | _, .equal t₁ t₂, v, xs =>
      (∃ a, PEval P (Sum.elim v xs) t₁ a) ∧ (∃ a, PEval P (Sum.elim v xs) t₂ a)
  | _, .rel _ ts, v, xs => ∀ i, ∃ a, PEval P (Sum.elim v xs) (ts i) a
  | _, .imp φ ψ, v, xs => DefinedAt P φ v xs ∧ DefinedAt P ψ v xs
  | _, .all φ, v, xs => ∀ a : M, DefinedAt P φ v (Fin.snoc xs a)

/-- Atomic formulas: partial and totalised satisfaction agree at an assignment where all terms are
defined. -/
theorem atomic_sat_iff {P : PartStruct L M} {junk : M} {l : ℕ} {v : α → M} {xs : Fin l → M} :
    ∀ {φ : L.BoundedFormula α l}, φ.IsAtomic → P.DefinedAt φ v xs →
      (P.pSat φ v xs ↔ @BoundedFormula.Realize L M (PEval.toTotal P junk) α l φ v xs) := by
  letI : L.Structure M := PEval.toTotal P junk
  intro φ h
  induction h with
  | equal t₁ t₂ =>
    intro hd
    simp only [pSat, Term.bdEqual, BoundedFormula.Realize]
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hd
    constructor
    · rintro ⟨c, hc, hc'⟩
      rw [PEval.realize junk hc, PEval.realize junk hc']
    · intro heq
      have hba : b = a := by
        rw [← PEval.realize junk hb, ← heq, PEval.realize junk ha]
      exact ⟨a, ha, hba ▸ hb⟩
  | rel R ts =>
    intro hd
    simp only [pSat, Relations.boundedFormula, BoundedFormula.Realize, PEval.toTotal_RelMap]
    constructor
    · rintro ⟨ys, hys, hR⟩
      have hys' : (fun i => Term.realize (Sum.elim v xs) (ts i)) = ys := by
        funext i
        exact PEval.realize junk (hys i)
      rw [hys']
      exact hR
    · intro hR
      refine ⟨fun i => Term.realize (Sum.elim v xs) (ts i), ?_, hR⟩
      intro i
      obtain ⟨a, ha⟩ := hd i
      have h1 : Term.realize (Sum.elim v xs) (ts i) = a := PEval.realize junk ha
      show PEval P (Sum.elim v xs) (ts i) (Term.realize (Sum.elim v xs) (ts i))
      rw [h1]
      exact ha

/-- **Quantifier-free formulas**: partial and totalised satisfaction agree at an assignment where
all terms are defined. (`IsQF` is exactly the fragment with no quantifiers; a quantifier would
need its bound variable to avoid the junk value, which is not expressible in general.) -/
theorem qf_sat_iff {P : PartStruct L M} {junk : M} {l : ℕ} {v : α → M} {xs : Fin l → M} :
    ∀ {φ : L.BoundedFormula α l}, φ.IsQF → P.DefinedAt φ v xs →
      (P.pSat φ v xs ↔ @BoundedFormula.Realize L M (PEval.toTotal P junk) α l φ v xs) := by
  letI : L.Structure M := PEval.toTotal P junk
  intro φ h
  induction h with
  | falsum =>
    intro _
    simp only [pSat, BoundedFormula.Realize]
  | of_isAtomic h => exact atomic_sat_iff h
  | imp φ ψ ih1 ih2 =>
    intro hd
    constructor
    · intro h hb
      exact (ih2 hd.2).mp (h ((ih1 hd.1).mpr hb))
    · intro h ha
      exact (ih2 hd.2).mpr (h ((ih1 hd.1).mp ha))

end PartStruct

/-! ### Necessity of the two hypotheses, and non-vacuity

`JunkFresh` and `JunkProp` are not decoration: each is needed for
`PartStruct.exists_iff_realize_ne_junk`. The two counterexamples below are machine-checked, so
the price of the junk-value encoding of a partial symbol is *exactly* these two conditions on the
structure — for `L_RV`'s `+` and `−` with `junk = ∞` they say that `+`, `−` take values in
`K = RV0 \ {∞}` and are undefined on `∞`.

A third structure meets both conditions, so the theorems are not vacuous. -/

/-- A toy one-sorted language with a constant `c` and a unary symbol `f`. -/
inductive ToyFn : ℕ → Type
  | c : ToyFn 0
  | f : ToyFn 1

/-- The toy language, with no relation symbols. -/
def ToyLang : FirstOrder.Language where
  Functions := ToyFn
  Relations := fun _ => Empty

/-- A partial structure that returns the junk value `true`: `JunkFresh` fails. -/
def pdFresh : PartStruct ToyLang Bool where
  funMap := fun {n} f =>
    match n, f with
    | _, ToyFn.c => fun _ => some true
    | _, ToyFn.f => fun _ => none
  relMap := fun {n} R _ => nomatch R

/-- A partial structure whose unary symbol is defined on the junk argument `true`:
`JunkProp` fails. -/
def pdProp : PartStruct ToyLang Bool where
  funMap := fun {n} f =>
    match n, f with
    | _, ToyFn.c => fun _ => none
    | _, ToyFn.f => fun xs => if xs 0 = true then some false else none
  relMap := fun {n} R _ => nomatch R

/-- A partial structure satisfying `JunkFresh` and `JunkProp`: undefined except `f 0 = 0`. -/
def pdGood : PartStruct ToyLang Bool where
  funMap := fun {n} f =>
    match n, f with
    | _, ToyFn.c => fun _ => none
    | _, ToyFn.f => fun xs => if xs 0 = false then some false else none
  relMap := fun {n} R _ => nomatch R

/-- The constant `c` as a term. -/
def tc : ToyLang.Term Empty := .func ToyFn.c fun i => i.elim0

/-- The term `f c`. -/
def tfc : ToyLang.Term Empty := .func ToyFn.f fun _ => tc

/-- In `pdFresh` the constant `c` evaluates to the junk value. -/
theorem pdFresh_eval : PEval pdFresh (fun e : Empty => e.elim) tc true :=
  PEval.func (P := pdFresh) (v := fun e : Empty => e.elim) (n := 0) (f := ToyFn.c)
    (ts := fun i => i.elim0) (xs := fun i => i.elim0) (a := true)
    (hxs := fun i => i.elim0) (hdef := rfl)

/-- Without `JunkFresh` the conclusion of `exists_iff_realize_ne_junk` is false. -/
theorem exists_iff_realize_ne_junk_needs_fresh :
    ¬ ((∃ a, PEval pdFresh (fun e : Empty => e.elim) tc a) ↔
        @Term.realize ToyLang Bool (PEval.toTotal pdFresh true) Empty (fun e : Empty => e.elim)
          tc ≠ true) := by
  intro h
  have hleft : ∃ a, PEval pdFresh (fun e : Empty => e.elim) tc a := ⟨true, pdFresh_eval⟩
  have hright : @Term.realize ToyLang Bool (PEval.toTotal pdFresh true) Empty
      (fun e : Empty => e.elim) tc = true := rfl
  exact (h.mp hleft) hright

/-- Without `JunkProp` the conclusion of `exists_iff_realize_ne_junk` is false. -/
theorem exists_iff_realize_ne_junk_needs_prop :
    ¬ ((∃ a, PEval pdProp (fun e : Empty => e.elim) tfc a) ↔
        @Term.realize ToyLang Bool (PEval.toTotal pdProp true) Empty (fun e : Empty => e.elim)
          tfc ≠ true) := by
  intro h
  have hright : @Term.realize ToyLang Bool (PEval.toTotal pdProp true) Empty
      (fun e : Empty => e.elim) tfc = false := rfl
  have hne : @Term.realize ToyLang Bool (PEval.toTotal pdProp true) Empty
      (fun e : Empty => e.elim) tfc ≠ true := by rw [hright]; simp
  obtain ⟨a, ha⟩ := h.mpr hne
  cases ha with
  | func _ _ xs _ hxs hdef =>
    have h0 : PEval pdProp (fun e : Empty => e.elim) tc (xs 0) := hxs 0
    cases h0 with
    | func _ _ _ _ _ hgc => simp [pdProp] at hgc

/-- `pdGood` satisfies both hypotheses of the totalisation theorems. -/
theorem pdGood_junk : pdGood.JunkFresh true ∧ pdGood.JunkProp true := by
  constructor
  · intro n f xs
    match n, f with
    | _, ToyFn.c => simp [pdGood]
    | _, ToyFn.f => simp [pdGood]
  · intro n f xs i hi
    match n, f with
    | _, ToyFn.c => exact i.elim0
    | _, ToyFn.f =>
      have hi0 : xs 0 = true := by
        have h1 : i = 0 := Fin.eq_zero i
        rw [h1] at hi
        exact hi
      simp [pdGood, hi0]

/-- In `pdGood` the term `f c` has no partial value and its totalised value is the junk value: the
hypotheses are satisfiable, so the theorems above are not vacuous. -/
theorem pdGood_tfc :
    (¬ ∃ a, PEval pdGood (fun e : Empty => e.elim) tfc a) ∧
      @Term.realize ToyLang Bool (PEval.toTotal pdGood true) Empty (fun e : Empty => e.elim)
        tfc = true := by
  obtain ⟨hfresh, hprop⟩ := pdGood_junk
  have hiff := PartStruct.exists_iff_realize_ne_junk pdGood true hfresh hprop
    (v := fun e : Empty => e.elim) (hv := fun e => e.elim) tfc
  have hright : @Term.realize ToyLang Bool (PEval.toTotal pdGood true) Empty
      (fun e : Empty => e.elim) tfc = true := rfl
  exact ⟨fun hex => (hiff.mp hex) hright, hright⟩

end PartialFO

/-! ### Axiom check

Running `lean PartialSemantics.lean` prints the axiom dependencies below: no `sorryAx` appears, so
every definition and theorem in this file is complete. -/

#print axioms PartialFO.PEval.realize
#print axioms PartialFO.PEval.det
#print axioms PartialFO.PEval.ne_junk
#print axioms PartialFO.PartStruct.ofTotal_toTotal
#print axioms PartialFO.PartStruct.toTotal_ofTotal_apply
#print axioms PartialFO.PartStruct.exists_iff_realize_ne_junk
#print axioms PartialFO.PartStruct.iff_realize
#print axioms PartialFO.PartStruct.atomic_sat_iff
#print axioms PartialFO.PartStruct.qf_sat_iff
#print axioms PartialFO.exists_iff_realize_ne_junk_needs_fresh
#print axioms PartialFO.exists_iff_realize_ne_junk_needs_prop
#print axioms PartialFO.pdGood_tfc
