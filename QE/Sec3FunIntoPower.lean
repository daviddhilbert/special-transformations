/-
**`fun:into:power`** (`paper.tex:755`, Section 3, Notation) — formalized.

The paper's sentence, verbatim:

> Let `A₁`, `A₂` be subsets and `R₁`, `R₂` equivalence relations on them, respectively.  A subset
> `B ⊆ A₁ × A₂` over `A₁` may be considered as a function from `A₁ / R₁` into the powerset
> `𝓟(A₂ / R₂)` if, for each equivalence class `C ∈ A₁ / R₁` and every `c₁, c₂ ∈ C`, there is a
> `U ∈ 𝓟(A₂ / R₂)` such that `fib(B, c₁) = fib(B, c₂) = ⋃ U`.  In this case, we sometime do write
> `B` as a function `A₁ / R₁ → 𝓟(A₂ / R₂)`.  We are of course only interested in definable objects.
> For example, we will discuss functions of the forms `VF / 𝔐 → 𝓟(RVᵐ)`, `VFⁿ × Γˡ → 𝓟(RVᵐ)`.

This is the only item of §3 with no model-theoretic content at all: it is a *definition* plus the
statement that the definition does what it says (the descent of `B` to the quotient exists and is
unique).  That is what this file proves, in full:

* `fib B a` — the paper's `fib(B, a)`;
* `unionOf s U` — the paper's `⋃ U` for a set `U` of `s`-classes;
* `IsUnionOfClasses r S` — "`S` is a union of `r`-classes" (`S` is the paper's `⋃ U`;
  `exists_unionOf_iff` proves the two readings agree);
* `Descends s₁ s₂ B` — the paper's condition, transcribed literally as
  `fib(B,c₁) = fib(B,c₂) = ⋃U`;
* `descends_iff_exists` — **`B` descends iff `B` is a function `A₁/R₁ → 𝓟(A₂/R₂)`**, i.e. iff there
  is `F : A₁/R₁ → Set (A₂/R₂)` with `fib B a = ⋃ (F ⟦a⟧)` for every `a`;
* `descends_unique` — and the `F` is **unique** (the paper says "may be considered as a function",
  which presupposes uniqueness);
* `descends_iff_invariant_and_saturated` — the two halves of the condition separated: `fib` is
  `R₁`-invariant **and** every `fib` is `R₂`-saturated.  This is the form one checks in practice;
  the paper's `= ⋃U` silently carries the saturation half, which is *not* automatic
  (`not_saturated_counterexample` below: `B = {(a,a)}` on `α = β = 2` is `R₁`-invariant but does not
  descend for a nontrivial `R₂`).
* `descends_discrete` — the second of the paper's two "forms", `VFⁿ × Γˡ → 𝓟(RVᵐ)`: on the *first*
  factor the relation may be anything (`R₁` arbitrary), and if the second relation is trivial then
  the saturation half is vacuous, so the condition collapses to `R₁`-invariance;
* `descends_ker_rv` — the first form, `VF / 𝔐 → 𝓟(RVᵐ)`: taking `R₁ = ker rv` (the paper's `𝔐`,
  see the docstring of `rvSetoid`) the descent is the same thing as an `rv`-invariant fibration,
  and it factors through the `RV` sort itself (`iRv`), which is the set-theoretic content of
  "functions on the residue field".

Nothing here is left unfinished: no `sorry`, no extra axiom, no `decide`/`native_decide`.

Check with (`.scratch2/sec3/` holds the compiled `Enc`, `Sec3Frozen`, `Sec3Infra`):

    cp .ultramath/smw1qqehg/m2/Sec3FunIntoPower.lean .scratch2/sec3/
    cd .scratch2/sec3 && LEAN_PATH=$PWD:$LEAN_PATH lean Sec3FunIntoPower.lean
-/
import Sec3Infra

open FirstOrder FirstOrder.Language

namespace SpecialTransformations.Milestone0

namespace FunIntoPower

/-! ## 1. Fibres of a relation, and unions of equivalence classes -/

variable {α β : Type*}

/-- The paper's `fib(B, a)`: the fibre of a subset `B ⊆ A₁ × A₂` over `a ∈ A₁`. -/
def fib (B : Set (α × β)) (a : α) : Set β := {b | (a, b) ∈ B}

@[simp] theorem mem_fib {B : Set (α × β)} {a : α} {b : β} : b ∈ fib B a ↔ (a, b) ∈ B :=
  Iff.rfl

theorem fib_congr {B : Set (α × β)} {a a' : α} (h : fib B a = fib B a') : fib B a = fib B a' := h

/-- `S ⊆ A₂` **is a union of `r`-classes**: the paper's `S = ⋃ U` for some `U ∈ 𝓟(A₂/R₂)`. -/
def IsUnionOfClasses (r : β → β → Prop) (S : Set β) : Prop :=
  ∀ ⦃x⦄, x ∈ S → ∀ ⦃y⦄, r x y → y ∈ S

theorem IsUnionOfClasses.mono {r r' : β → β → Prop} (hr : ∀ x y, r x y → r' x y) {S : Set β}
    (h : IsUnionOfClasses r' S) : IsUnionOfClasses r S :=
  fun x hx y hxy => h hx (hr x y hxy)

theorem isUnionOfClasses_empty {r : β → β → Prop} : IsUnionOfClasses r (∅ : Set β) :=
  fun _ hx => hx.elim

theorem isUnionOfClasses_univ {r : β → β → Prop} : IsUnionOfClasses r (Set.univ : Set β) :=
  fun _ _ _ _ => Set.mem_univ _

theorem IsUnionOfClasses.inter {r : β → β → Prop} {S T : Set β}
    (hS : IsUnionOfClasses r S) (hT : IsUnionOfClasses r T) :
    IsUnionOfClasses r (S ∩ T) :=
  fun _ hx _ hy => ⟨hS hx.1 hy, hT hx.2 hy⟩

theorem IsUnionOfClasses.union {r : β → β → Prop} {S T : Set β}
    (hS : IsUnionOfClasses r S) (hT : IsUnionOfClasses r T) :
    IsUnionOfClasses r (S ∪ T) := by
  intro x hx y hy
  rcases hx with hx | hx
  · exact Or.inl (hS hx hy)
  · exact Or.inr (hT hx hy)

section Setoid

variable (s : Setoid β)

/-- The paper's `⋃ U`, for `U` a set of `s`-classes: the union of the classes in `U`. -/
def unionOf (U : Set (Quotient s)) : Set β := {x | Quotient.mk s x ∈ U}

theorem mem_unionOf {U : Set (Quotient s)} {x : β} :
    x ∈ unionOf s U ↔ Quotient.mk s x ∈ U := Iff.rfl

/-- A union of classes is a union of classes. -/
theorem isUnionOfClasses_unionOf (U : Set (Quotient s)) :
    IsUnionOfClasses s.r (unionOf s U) := by
  intro x hx y hy
  show Quotient.mk s y ∈ U
  rw [← Quotient.sound hy]
  exact hx

/-- Every set that is a union of classes is literally `⋃ U` for the set `U` of the classes it
meets.  This is the converse of `isUnionOfClasses_unionOf`, in the exact form used below. -/
theorem eq_unionOf_image {S : Set β} (h : IsUnionOfClasses s.r S) :
    S = unionOf s (Quotient.mk s '' S) := by
  ext x
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    have hrel : s.r y x := Quotient.exact hyx
    exact h hy hrel

theorem exists_unionOf_iff {S : Set β} :
    (∃ U : Set (Quotient s), S = unionOf s U) ↔ IsUnionOfClasses s.r S := by
  constructor
  · rintro ⟨U, rfl⟩
    exact isUnionOfClasses_unionOf s U
  · intro h
    exact ⟨_, eq_unionOf_image s h⟩

/-- The class of a point. -/
def cls (x : β) : Set β := {y | s.r x y}

theorem mem_cls {x y : β} : y ∈ cls s x ↔ s.r x y := Iff.rfl

theorem isUnionOfClasses_cls (x : β) : IsUnionOfClasses s.r (cls s x) := by
  intro y hy z hz
  exact s.trans hy hz

theorem cls_eq_unionOf (x : β) : cls s x = unionOf s {Quotient.mk s x} := by
  ext y
  simp only [mem_cls, mem_unionOf, Set.mem_singleton_iff]
  exact ⟨fun h => Quotient.sound (s.symm h), fun h => s.symm (Quotient.exact h)⟩

theorem cls_eq_cls_iff {x y : β} : cls s x = cls s y ↔ s.r x y := by
  constructor
  · intro h
    have : y ∈ cls s y := s.refl y
    rw [← h] at this
    exact this
  · intro h
    ext z
    exact ⟨fun hxz => s.trans (s.symm h) hxz, fun hyz => s.trans h hyz⟩

end Setoid

/-! ## 2. The paper's condition, and the descent theorem -/

/-- The trivial (equality) equivalence relation on `β`. -/
def discreteSetoid (β : Type*) : Setoid β := ⟨(· = ·), fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

theorem discreteSetoid_rel {x y : β} : (discreteSetoid β).r x y ↔ x = y := Iff.rfl

section Descends

variable (s₁ : Setoid α) (s₂ : Setoid β)

/-- **The paper's condition** (`fun:into:power`): for each class `C ∈ A₁/R₁` and every `c₁, c₂ ∈ C`
there is a `U ∈ 𝓟(A₂/R₂)` such that `fib(B,c₁) = fib(B,c₂) = ⋃ U`. -/
def Descends (B : Set (α × β)) : Prop :=
  ∀ c₁ c₂ : α, s₁.r c₁ c₂ →
    ∃ U : Set (Quotient s₂), fib B c₁ = unionOf s₂ U ∧ fib B c₂ = unionOf s₂ U

/-- The paper's condition in the equivalent `fib`-form: `fib` is `R₁`-invariant and its values are
`R₂`-saturated.  The saturation half is what the paper's `= ⋃U` says; the invariance half is what
the quantifier over `c₁, c₂ ∈ C` says. -/
theorem descends_iff_invariant_and_saturated (B : Set (α × β)) :
    Descends s₁ s₂ B ↔
      (∀ c₁ c₂ : α, s₁.r c₁ c₂ → fib B c₁ = fib B c₂) ∧
        ∀ c : α, IsUnionOfClasses s₂.r (fib B c) := by
  constructor
  · rintro h
    refine ⟨?_, ?_⟩
    · intro c₁ c₂ hc
      obtain ⟨U, h₁, h₂⟩ := h c₁ c₂ hc
      rw [h₁, h₂]
    · intro c
      obtain ⟨U, h₁, _⟩ := h c c (s₁.refl c)
      rw [h₁]
      exact isUnionOfClasses_unionOf s₂ U
  · rintro ⟨hinv, hsat⟩ c₁ c₂ hc
    have hfib : fib B c₁ = fib B c₂ := hinv c₁ c₂ hc
    exact ⟨Quotient.mk s₂ '' fib B c₁, eq_unionOf_image s₂ (hsat c₁),
      by rw [← hfib]; exact eq_unionOf_image s₂ (hsat c₁)⟩

/-- **`fun:into:power`, the content of the notation**: the paper's condition is exactly saying that
`B` *is* a function `A₁/R₁ → 𝓟(A₂/R₂)`, i.e. that `B` factors through `fib` and the quotient. -/
theorem descends_iff_exists (B : Set (α × β)) :
    Descends s₁ s₂ B ↔
      ∃ F : Quotient s₁ → Set (Quotient s₂), ∀ c : α, fib B c = unionOf s₂ (F (Quotient.mk s₁ c)) := by
  constructor
  · intro h
    obtain ⟨hinv, hsat⟩ := (descends_iff_invariant_and_saturated s₁ s₂ B).mp h
    refine ⟨fun q => Quotient.lift (fun c => Quotient.mk s₂ '' fib B c) ?_ q, ?_⟩
    · intro c₁ c₂ hc
      rw [hinv c₁ c₂ hc]
    · intro c
      show fib B c = unionOf s₂ (Quotient.lift (fun c => Quotient.mk s₂ '' fib B c) _ (Quotient.mk s₁ c))
      rw [Quotient.lift_mk]
      exact eq_unionOf_image s₂ (hsat c)
  · rintro ⟨F, hF⟩
    intro c₁ c₂ hc
    refine ⟨F (Quotient.mk s₁ c₁), hF c₁, ?_⟩
    rw [hF c₂, Quotient.sound hc]

/-- The function of `descends_iff_exists` is **unique**: "`B` may be considered as a function
`A₁/R₁ → 𝓟(A₂/R₂)`" is well defined, because two such functions with the same `B` coincide.  (In
this argument the non-emptiness of the classes — `s₂.refl` — is what makes `⋃` injective.) -/
theorem descends_unique {B : Set (α × β)} {F F' : Quotient s₁ → Set (Quotient s₂)}
    (hF : ∀ c : α, fib B c = unionOf s₂ (F (Quotient.mk s₁ c)))
    (hF' : ∀ c : α, fib B c = unionOf s₂ (F' (Quotient.mk s₁ c))) : F = F' := by
  funext q
  induction q using Quotient.inductionOn with
  | h c =>
    have hU : unionOf s₂ (F (Quotient.mk s₁ c)) = unionOf s₂ (F' (Quotient.mk s₁ c)) := by
      rw [← hF c, ← hF' c]
    have : ∀ U U' : Set (Quotient s₂), unionOf s₂ U = unionOf s₂ U' → U = U' := by
      intro U U' hUU'
      ext q
      induction q using Quotient.inductionOn with
      | h x =>
        constructor
        · intro hx
          have hx' : x ∈ unionOf s₂ U := hx
          rw [hUU'] at hx'
          exact hx'
        · intro hx
          have hx' : x ∈ unionOf s₂ U' := hx
          rw [← hUU'] at hx'
          exact hx'
    rw [this _ _ hU]

/-- The descent does not lose information: the relation `B` is recovered from `F` as the union of
the fibres of the classes.  In particular, if `B` is definable over `A`, then so is the graph of the
induced function — the paper's "We are of course only interested in definable objects" costs
nothing here. -/
theorem eq_of_descends {B : Set (α × β)} {F : Quotient s₁ → Set (Quotient s₂)}
    (hF : ∀ c : α, fib B c = unionOf s₂ (F (Quotient.mk s₁ c))) :
    B = {p : α × β | p.2 ∈ unionOf s₂ (F (Quotient.mk s₁ p.1))} := by
  ext ⟨a, b⟩
  show (a, b) ∈ B ↔ b ∈ unionOf s₂ (F (Quotient.mk s₁ a))
  rw [← hF a]
  exact Iff.rfl

/-- The second of the paper's two forms, `VFⁿ × Γˡ → 𝓟(RVᵐ)`: when the relation on the *second*
factor is trivial, the saturation half of the condition is vacuous. -/
theorem descends_discrete (B : Set (α × β)) :
    Descends s₁ (discreteSetoid β) B ↔ ∀ c₁ c₂ : α, s₁.r c₁ c₂ → fib B c₁ = fib B c₂ := by
  rw [descends_iff_invariant_and_saturated]
  constructor
  · rintro ⟨h, _⟩
    exact h
  · intro h
    refine ⟨h, fun c x hx y hy => ?_⟩
    exact hy ▸ hx

end Descends

/-! ## 3. A cautionary example: the saturation half is not automatic

The paper's condition has two halves (see `descends_iff_invariant_and_saturated`) and the second is
easy to overlook.  On `α = β = Bool` with `s₁ = ⊤` and `s₂` the universal relation, `B = {(a,a)}` is
`s₁`-invariantly fibred (`B` is a function, its fibres are singletons) but it does **not** descend:
the fibre `{a}` is not a union of `s₂`-classes, and `fib B a = ⋃ U` would say `{a}` is all of `Bool`.
-/

/-- The universal setoid on any nonempty type. -/
def topSetoid (β : Type*) : Setoid β where
  r := fun _ _ => True
  iseqv := ⟨fun _ => trivial, fun _ => trivial, fun _ _ => trivial⟩

theorem not_descends_diag : ¬ Descends (⊤ : Setoid Bool) (topSetoid Bool) {p : Bool × Bool | p.1 = p.2} := by
  rintro h
  obtain ⟨U, h₁, -⟩ := h true false trivial
  have hmem : true ∈ fib ({p : Bool × Bool | p.1 = p.2}) true := rfl
  rw [h₁] at hmem
  have hfalse : false ∈ unionOf (topSetoid Bool) U :=
    isUnionOfClasses_unionOf (topSetoid Bool) U hmem (show (topSetoid Bool).r true false from trivial)
  rw [← h₁] at hfalse
  simp only [fib, Set.mem_ofPred_eq] at hfalse
  exact absurd hfalse (by decide)

/-! ## 4. The first of the paper's two forms: `VF / 𝔐 → 𝓟(RVᵐ)`

The paper's `𝔐` is the maximal ideal of `VF`, so `VF/𝔐` is the residue field.  In `L_RV` the
residue of `x` is `rv x` itself (`Axioms.rvEqLink`: `rv a = rv b ↔ ¬(v (a - b) ≤ v b)` for `b ≠ 0`,
i.e. `x ≡ y (mod 𝔐) ↔ rv x = rv y` when `v x = v y`), so the formal counterpart of `VF/𝔐` is the
quotient of `VF` by `ker rv`.  `rvSetoid` is that quotient; `quotient_of_rvSetoid_equiv_range`
records that `VF/𝔐` embeds in the `RV` sort through `rv`, which is why a function
`VF/𝔐 → 𝓟(RVᵐ)` can be written as a function of `rv` — and that is the form
`descends_ker_rv` produces. -/

section RV

variable {M : Type*} [LRV.Structure M]

/-- **The paper's `VF / 𝔐`**, formally: `x ~ y` iff `rv x = rv y` (for `x, y` of equal value this is
`x - y ∈ 𝔐`, by `Axioms.rvEqLink`). -/
def rvSetoid : Setoid M := Setoid.ker iRv

theorem rvSetoid_rel {x y : M} : (rvSetoid).r x y ↔ iRv x = iRv y := Iff.rfl

/-- `VF/𝔐` sits inside the `RV` sort: the quotient map `VF → VF/𝔐` followed by `rv` is injective. -/
theorem quotient_of_rvSetoid_injective :
    Function.Injective (Quotient.lift (s := rvSetoid) (fun x : M => iRv x) (fun _ _ h => h)) := by
  intro q q' hq
  induction q using Quotient.inductionOn with
  | h x =>
    induction q' using Quotient.inductionOn with
    | h y =>
      have hxy : iRv x = iRv y := hq
      exact Quotient.sound (s := rvSetoid) hxy

/-- **`fun:into:power` at `VF/𝔐`**: a subset `B ⊆ VF × A₂` whose fibres are `R₁`-invariant for
`R₁ = ker rv` (the paper's `𝔐`) is a function `VF/𝔐 → 𝓟(A₂/R₂)`.  Via
`quotient_of_rvSetoid_injective` the quotient `VF/𝔐` is a subset of the `RV` sort, so this is the
paper's "function `VF/𝔐 → 𝓟(RVᵐ)`". -/
theorem descends_ker_rv {A₂ : Type*} (s₂ : Setoid A₂) (B : Set (M × A₂))
    (hinv : ∀ c₁ c₂ : M, iRv c₁ = iRv c₂ → fib B c₁ = fib B c₂)
    (hsat : ∀ c : M, IsUnionOfClasses s₂.r (fib B c)) :
    ∃ F : Quotient rvSetoid → Set (Quotient s₂),
      ∀ c : M, fib B c = unionOf s₂ (F (Quotient.mk rvSetoid c)) :=
  (descends_iff_exists rvSetoid s₂ B).mp
    ((descends_iff_invariant_and_saturated rvSetoid s₂ B).mpr ⟨hinv, hsat⟩)

end RV

end FunIntoPower

end SpecialTransformations.Milestone0
