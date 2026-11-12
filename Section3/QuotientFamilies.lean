module

/-
Notation 3.16: quotient-to-powerset descent, adapted from the generic part
of Sec3FunIntoPower.lean. No identification of ker(rv) with an additive
maximal-ideal quotient is made.
-/
public import Section3.Parameters

@[expose] public section

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0

namespace SpecialTransformations.Section3

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

end FunIntoPower

namespace QuotientFamilies

open FunIntoPower

variable {M : Type} [LRV.Structure M] {n m : ℕ}

/-- Pull a relation on two definable domains back to the original Cartesian
power. This is where definability of a quotient-valued family is tested. -/
def liftedGraph {A₁ : Set (Fin n → M)} {A₂ : Set (Fin m → M)}
    (B : Set (A₁ × A₂)) : Set (Fin (n + m) → M) :=
  {x | ∃ a : A₁, ∃ b : A₂, x = Fin.append a.val b.val ∧ (a, b) ∈ B}

/-- The graph of a quotient-to-powerset map, expressed on representatives. -/
def representativeGraph {A₁ : Set (Fin n → M)} {A₂ : Set (Fin m → M)}
    (r₁ : Setoid A₁) (r₂ : Setoid A₂) (F : Quotient r₁ → Set (Quotient r₂)) :
    Set (A₁ × A₂) := {p | Quotient.mk r₂ p.2 ∈ F (Quotient.mk r₁ p.1)}

/-- Definability of the family is definability of the pulled-back relation
over the *same* base. This definition adds no representatives as parameters. -/
def DefinableFamilyOver (S : Set M) (sn : Fin n → SortTag) (sm : Fin m → SortTag)
    {A₁ : Set (Fin n → M)} {A₂ : Set (Fin m → M)}
    (r₁ : Setoid A₁) (r₂ : Setoid A₂) (F : Quotient r₁ → Set (Quotient r₂)) : Prop :=
  DefinableOver S (Fin.append sn sm) (liftedGraph (representativeGraph r₁ r₂ F))

/-- The phrase "over A₁" before Notation 3.16 means surjectivity of the
projection; equivalently every relation fibre is nonempty. -/
def OverDomain {α β : Type} (B : Set (α × β)) : Prop :=
  ∀ a, ∃ b, (a, b) ∈ B

theorem overDomain_iff_fibres_nonempty {α β : Type} (B : Set (α × β)) :
    OverDomain B ↔ ∀ a, (fib B a).Nonempty := Iff.rfl

/-- Notation 3.16 with definability retained. Descent is exactly invariance
in the first quotient and saturation in the second; the induced map is
unique and definable over the original base S. -/
theorem notation_3_16 (S : Set M) (sn : Fin n → SortTag) (sm : Fin m → SortTag)
    {A₁ : Set (Fin n → M)} {A₂ : Set (Fin m → M)}
    (r₁ : Setoid A₁) (r₂ : Setoid A₂) (B : Set (A₁ × A₂))
    (hdef : DefinableOver S (Fin.append sn sm) (liftedGraph B))
    (hdesc : Descends r₁ r₂ B) :
    ∃! F : Quotient r₁ → Set (Quotient r₂),
      (∀ a : A₁, fib B a = unionOf r₂ (F (Quotient.mk r₁ a))) ∧
      DefinableFamilyOver S sn sm r₁ r₂ F := by
  obtain ⟨F, hF⟩ := (descends_iff_exists r₁ r₂ B).mp hdesc
  refine ⟨F, ⟨hF, ?_⟩, ?_⟩
  · have heq : B = representativeGraph r₁ r₂ F := eq_of_descends r₁ r₂ hF
    unfold DefinableFamilyOver
    rw [← heq]
    exact hdef
  · intro F' hF'
    exact descends_unique r₁ r₂ hF'.1 hF

theorem overDomain_iff_nonempty_values {α β : Type} (r₁ : Setoid α) (r₂ : Setoid β)
    {B : Set (α × β)} {F : Quotient r₁ → Set (Quotient r₂)}
    (hF : ∀ a, fib B a = unionOf r₂ (F (Quotient.mk r₁ a))) :
    OverDomain B ↔ ∀ q, (F q).Nonempty := by
  constructor
  · intro h q
    induction q using Quotient.inductionOn with
    | h a =>
      obtain ⟨b, hb⟩ := h a
      refine ⟨Quotient.mk r₂ b, ?_⟩
      change b ∈ unionOf r₂ (F (Quotient.mk r₁ a))
      rw [← hF a]
      exact hb
  · intro h a
    obtain ⟨q, hq⟩ := h (Quotient.mk r₁ a)
    induction q using Quotient.inductionOn with
    | h b =>
      change b ∈ unionOf r₂ (F (Quotient.mk r₁ a)) at hq
      rw [← hF a] at hq
      exact ⟨b, hq⟩

end QuotientFamilies
end SpecialTransformations.Section3
