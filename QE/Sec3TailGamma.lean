/-
**`fun:bounded:cons` in the language that has `Γ`** (`paper.tex:764`).

`fun:into:power` (`paper.tex:755`) and `fun:bounded:cons` are about `RV`- and `Γ`-valued objects:
`Sec3Tail.lean` states them in `L_RV`, which has no sort for `Γ`, so "bounded in `Γ`" is written
there in the preorder `≤` of `RV` (of which `vrv` is the quotient map onto `Γ`).  This file states
the same lemma *literally* — `vrv(⋃ f(VF^×)) ⊆ Γ` bounded above and below, and `δ ∈ Γ` — in the
three-sorted expansion `L_RV^Γ` of `Milestone0/Encoding.lean` Part 4, whose `Γ`-vocabulary
(`Gamma.iMemGamma`, `Gamma.iVrv`, the order `RelΓ.le`) is read on the carrier here.

The `L_RV` symbols are read in `L_RV^Γ` through the summand inclusion (`instLRV` below, a *local*
instance: it is only used inside this file, so it does not pollute the instance space of anything
that imports it).  Hence `puncturedOmega`, `IsSetValuedFun`, `imageSet`, `vfZero` are exactly the
`Sec3Tail` ones, now interpreted in the expansion.

What is here: the frozen statement `FunBoundedConsΓ` (the paper's sentence, verbatim, in the
language where it can be said), `vrvImage` = the paper's `vrv(⋃ f(VF^×)) ⊆ Γ`, and the one provable
case `funBoundedConsΓ_of_const`.  No `sorry`, no `axiom`.

    cp .ultramath/smw1qqehg/m2/Sec3TailGamma.lean .scratch2/sec3/
    cd .scratch2/sec3 && LEAN_PATH=$PWD:$LEAN_PATH lean Sec3TailGamma.lean
-/
import Sec3Tail

open FirstOrder FirstOrder.Language

namespace SpecialTransformations.Milestone0

namespace Sec3TailGamma

open FunIntoPower

variable {M : Type*} [Gamma.LRVΓ.Structure M]

/-- The `L_RV`-structure read inside `L_RV^Γ` through the left summand.  Local to this file. -/
local instance instLRV : LRV.Structure M where
  funMap g xs := Structure.funMap (L := Gamma.LRVΓ) (Sum.inl g) xs
  RelMap r xs := Structure.RelMap (L := Gamma.LRVΓ) (Sum.inl r) xs

/-- **The order of `Γ`** (`RelΓ.le`) of `L_RV^Γ`, semantically. -/
def leGamma (x y : M) : Prop :=
  Structure.RelMap (L := Gamma.LRVΓ) (Sum.inr Gamma.RelΓ.le) ![x, y]

/-- **The paper's `vrv(⋃ f(VF^×))`**, as a subset of `Γ`: the set of values `vrv(ȳ_i)` for `ȳ` in the
union of the values of `f` at the nonzero `VF`-elements.  (The `Γ`-sort predicate is part of the
set, so this is literally a subset of `Γ`, as in the source.) -/
def vrvImage (m : ℕ) (f : M → Set (Fin m → M)) : Set M :=
  {γ | Gamma.iMemGamma γ ∧ ∃ Y ∈ Sec3Tail.imageSet m f, ∃ i : Fin m, Gamma.iVrv (Y i) = γ}

theorem mem_vrvImage {m : ℕ} {f : M → Set (Fin m → M)} {γ : M} :
    γ ∈ vrvImage m f ↔
      Gamma.iMemGamma γ ∧ ∃ Y ∈ Sec3Tail.imageSet m f, ∃ i : Fin m, Gamma.iVrv (Y i) = γ :=
  Iff.rfl

/-- `vrv(⋃ f(VF^×))` is a subset of `Γ`. -/
theorem vrvImage_subset_gamma {m : ℕ} (f : M → Set (Fin m → M)) :
    vrvImage m f ⊆ {γ | Gamma.iMemGamma γ} :=
  fun _ h => h.1

/-- **"The subset `vrv(⋃ f(VF^×))` is bounded from both above and below"**, the hypothesis of
`fun:bounded:cons`, stated on `Γ`: there are `γ₁, γ₂ ∈ Γ` with `γ₁ ≤ γ ≤ γ₂` for every
`γ ∈ vrv(⋃ f(VF^×))`.  This is the paper's hypothesis verbatim; `Sec3Tail.VrvBounded` is its
`L_RV`-form. -/
def VrvBoundedΓ (m : ℕ) (f : M → Set (Fin m → M)) : Prop :=
  ∃ γ₁ γ₂ : M, Gamma.iMemGamma γ₁ ∧ Gamma.iMemGamma γ₂ ∧
    ∀ γ ∈ vrvImage m f, leGamma γ₁ γ ∧ leGamma γ γ₂

/-- **`fun:bounded:cons`** (`paper.tex:764`), frozen, in `L_RV^Γ`.  The paper's sentence, verbatim:

> Let `f : VF^× -> 𝓟(RV^m)` be a definable function such that the subset `vrv(⋃ f(VF^×))` is bounded
> from both above and below.  Then for any sufficiently large `δ ∈ Γ` the restriction
> `f ↾ ω(0,δ) ∖ {0}` is constant.

Every ingredient is the paper's: `IsSetValuedFun` is definability of the graph in `L_RV ⊆ L_RV^Γ`,
`VrvBoundedΓ` is the boundedness of the `vrv`-image *in `Γ`*, `δ ∈ Γ` is `Gamma.iMemGamma δ`, and
`ω(0,δ) ∖ {0}` is `puncturedOmega δ` (the set of `x` with `vv x > δ`, i.e. `¬ (rv x ≤ δ)`). -/
def FunBoundedConsΓ (S : Set M) (m : ℕ) (f : M → Set (Fin m → M)) : Prop :=
  Sec3Tail.IsSetValuedFun S m f → VrvBoundedΓ m f →
    ∃ δ : M, Gamma.iMemGamma δ ∧
      ∀ a a' : M, a ∈ Sec3Tail.puncturedOmega δ → a' ∈ Sec3Tail.puncturedOmega δ → f a = f a'

/-- The provable case of `fun:bounded:cons`: if `f` is constant on the nonzero `VF`-elements then
its restriction to any punctured ball is constant, and the boundedness hypothesis is not needed.
(Here `δ` may be taken to be `0`, which is a `Γ`-element only if the model's value group is
trivial; for the statement as frozen the choice of `δ` is left to the proof of the general case,
which is the paper's normal-form argument.  This lemma is recorded to show that the frozen
statement's conclusion is not vacuous.) -/
theorem funBoundedConsΓ_conclusion_of_const {m : ℕ} {f : M → Set (Fin m → M)}
    (h : ∃ c : Set (Fin m → M), ∀ a : M, iVF a → a ≠ Sec3Tail.vfZero (M := M) → f a = c)
    (δ : M) :
    ∀ a a' : M,
      a ∈ Sec3Tail.puncturedOmega δ → a' ∈ Sec3Tail.puncturedOmega δ → f a = f a' := by
  obtain ⟨c, hc⟩ := h
  exact fun a a' ha ha' => by rw [hc a ha.1 ha.2.1, hc a' ha'.1 ha'.2.1]

/-- **`fun:bounded:cons` holds for constant `f`**, in the `Γ`-form, with `δ` any `Γ`-element. -/
theorem funBoundedConsΓ_of_const {S : Set M} {m : ℕ} {f : M → Set (Fin m → M)}
    (h : ∃ c : Set (Fin m → M), ∀ a : M, iVF a → a ≠ Sec3Tail.vfZero (M := M) → f a = c)
    (γ : M) (hγ : Gamma.iMemGamma γ) : FunBoundedConsΓ S m f :=
  fun _ _ => ⟨γ, hγ, funBoundedConsΓ_conclusion_of_const h γ⟩

end Sec3TailGamma

end SpecialTransformations.Milestone0
