/-
Copyright: none.  Ultramath swarm smw2ngn1z, member m2 (direction d3).

# The value-group step of Lemma 3.6 (`lift:transcendental`): rational rank 0 + divisibility

The proof of Lemma 3.6 of `refs/qe.tex` (l. 732, `lift:transcendental`) contains the inference
(l. 740)

> By the dimension inequality of valuation theory (see [EP, Theorem 3.4.3]), the rational rank
> of `Γ(⟨Ŝ,e⟩)/Γ(Ŝ)` is 0.  Since `Γ(Ŝ)` is divisible, we actually have
> `Γ(⟨Ŝ,e⟩) = Γ(Ŝ)`.

This file isolates that inference as **ordered abelian group theory**.  There are no valued
fields, no models of `ACVF` and no quoted inequality here: the result is about any
`H ≤ K ≤ G` with `G` an ordered commutative group, so it can be consumed both at the tree's
`GammaOf M` (multiplicative, see `GammaInstantiation.lean`) and at any additive value group.

## What is proved

* §1 `eq_one_of_pow_eq_one` — **ordered commutative groups are torsion-free**.  This is the only
  order-theoretic input of the step.
* §2 `divHull H` — the **root closure** `{x | ∃ n > 0, xⁿ ∈ H}` of a subgroup: a subgroup
  (`CommGroup` is needed for `mul_mem'`), containing `H` (`le_divHull`), monotone
  (`divHull_mono`), and *the* largest subgroup of `G` in which `H` has torsion quotient
  (`ratRankZero_iff_le_divHull`).
* §2 `RatRankZero H K` — the paper's "the rational rank of `K/H` is 0", in the elementary form
  *"every element of `K` has a positive power in `H`"*, i.e. `K/H` is a torsion group.
  `RatRankTensor.lean` identifies this with `Module.rank ℚ (ℚ ⊗ (K/H)) = 0`.
* §3 `eq_of_divisible_of_ratRankZero` — **the paper's step**: `H` divisible, `H ≤ K`,
  `RatRankZero H K` ⟹ `K = H`.
* §3 `maximal_extension_iff` — the *converse*: in a divisible `G`, the implication holds for
  every `K ⊇ H` exactly when `H` is divisible.  So the paper's divisibility hypothesis is
  equivalent to the inference it is used for, not merely sufficient for the paper's proof.
* §5 `DivisibleSubgroup ↔ RootableBy H ℕ` (Mathlib's `Mathlib.GroupTheory.Divisible`), so the
  tree's `RootableBy`-form divisibility (as recorded by `QE/GammaDiv.lean`) plugs into §3.

The two sharpness examples (`RatRankSharp.lean`) show both hypotheses are necessary.

## Hypothesis audit

Every theorem is quantified over its subgroup data; nothing is assumed beyond
`[CommGroup G] [LinearOrder G] [IsOrderedMonoid G]`, which is *exactly* the instance set that
`QE/GammaGroup.lean` installs on the tree's `GammaOf M` (`gammaOfCommGroup`,
`gammaOfLinearOrder`, `gammaIsOrderedMonoid`) and that `QE/GammaDiv.lean`'s
`RootableBy (GammaOf M) ℕ` inhabits.  `GammaInstantiation.lean` checks the instantiation.
-/
import Mathlib

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Ultramath.M2RR

variable {G : Type*} [CommGroup G] [LinearOrder G] [IsOrderedMonoid G]

/-! ## §1 Ordered commutative groups are torsion-free -/

/-- **An ordered commutative group is torsion-free**: the only element of finite order is `1`.
This is the whole of the order theory needed by the paper's step
`rational rank 0 + Γ(Ŝ) divisible ⟹ Γ(⟨Ŝ,e⟩) = Γ(Ŝ)`. -/
@[to_additive eq_zero_of_nsmul_eq_zero
  /-- **An ordered commutative group is torsion-free** (additive form). -/]
theorem eq_one_of_pow_eq_one {x : G} {n : ℕ} (hn : n ≠ 0) (h : x ^ n = 1) : x = 1 := by
  rcases lt_trichotomy x 1 with hlt | heq | hgt
  · have h1 : x ^ n < 1 := (pow_lt_one_iff hn).mpr hlt
    rw [h] at h1
    exact absurd h1 (lt_irrefl 1)
  · exact heq
  · have h1 : 1 < x ^ n := (one_lt_pow_iff hn).mpr hgt
    rw [h] at h1
    exact absurd h1 (lt_irrefl 1)

/-- Powers are injective: `xⁿ = yⁿ` with `n ≠ 0` forces `x = y`.  Used for the *uniqueness* of
`n`-th roots, which is what makes divisibility of `Γ(Ŝ)` usable at all. -/
@[to_additive nsmul_right_injective
  /-- Multiples are injective (additive form). -/]
theorem pow_right_injective {x y : G} {n : ℕ} (hn : n ≠ 0) (h : x ^ n = y ^ n) : x = y := by
  have h' : (x / y) ^ n = 1 := by
    rw [div_pow, h, div_eq_one]
  have h1 : x / y = 1 := eq_one_of_pow_eq_one hn h'
  rwa [div_eq_one] at h1

/-- `n`-th roots in an ordered commutative group are unique. -/
@[to_additive nsmul_right_injective_iff
  /-- `n`-th roots in an ordered commutative group are unique (additive form). -/]
theorem pow_right_injective_iff {x y : G} {n : ℕ} (hn : n ≠ 0) : x ^ n = y ^ n ↔ x = y :=
  ⟨pow_right_injective hn, fun h => by rw [h]⟩

/-! ## §2 The root closure of a subgroup, and `RatRankZero` -/

/-- A subgroup is **divisible** if every element of it has `n`-th roots in it, for every `n ≥ 1`.
This is the paper's hypothesis "`Γ(Ŝ)` is divisible" in subgroup form. -/
@[to_additive DivisibleAddSubgroup
  /-- An additive subgroup is **divisible** if every element of it has `n`-th multiples in it. -/]
def DivisibleSubgroup (H : Subgroup G) : Prop :=
  ∀ x ∈ H, ∀ n : ℕ, 1 ≤ n → ∃ y ∈ H, y ^ n = x

/-- The **root closure** of `H`: the elements of `G` a positive power of which lies in `H`.
It is the largest subgroup of `G` containing `H` with torsion quotient, and the paper's `Γ(Ŝ)` is
divisible exactly when it equals its own root closure (`divHull_eq_self_iff`). -/
@[to_additive divHullAdd
  /-- The **root closure** of an additive subgroup. -/]
def divHull (H : Subgroup G) : Subgroup G where
  carrier := {x | ∃ n : ℕ, 1 ≤ n ∧ x ^ n ∈ H}
  one_mem' := ⟨1, le_rfl, by simpa using H.one_mem⟩
  mul_mem' := by
    rintro x y ⟨m, hm, hxm⟩ ⟨n, hn, hyn⟩
    refine ⟨m * n, Nat.mul_pos (by omega) (by omega), ?_⟩
    have h2 : (y ^ m) ^ n = (y ^ n) ^ m := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    have h1 : (x * y) ^ (m * n) = (x ^ m) ^ n * (y ^ m) ^ n := by
      rw [mul_pow, pow_mul, pow_mul]
    rw [h1, h2]
    exact H.mul_mem (H.pow_mem hxm n) (H.pow_mem hyn m)
  inv_mem' := by
    rintro x ⟨n, hn, hxn⟩
    exact ⟨n, hn, by rw [inv_pow]; exact H.inv_mem hxn⟩

/-- **Rational rank zero**, elementwise: every element of `K` has a positive power in `H`, i.e.
the quotient group `K/H` is a torsion group.  This is the paper's "the rational rank of
`Γ(⟨Ŝ,e⟩)/Γ(Ŝ)` is 0". -/
@[to_additive RatRankZeroAdd
  /-- **Rational rank zero** for additive subgroups: `K/H` is a torsion group. -/]
def RatRankZero (H K : Subgroup G) : Prop := ∀ x ∈ K, ∃ n : ℕ, 1 ≤ n ∧ x ^ n ∈ H

/-- `RatRankZero H K` *is* the statement `K ≤ divHull H`: the root closure is exactly the
subgroup cut out by "rational rank 0 over `H`". -/
@[to_additive ratRankZeroAdd_iff_le_divHullAdd
  /-- The additive form of `ratRankZero_iff_le_divHull`. -/]
theorem ratRankZero_iff_le_divHull {H K : Subgroup G} : RatRankZero H K ↔ K ≤ divHull H :=
  Iff.rfl

/-- `H` is contained in its root closure. -/
@[to_additive le_divHullAdd]
theorem le_divHull (H : Subgroup G) : H ≤ divHull H :=
  fun _ hx => ⟨1, le_rfl, by simpa using hx⟩

/-- The root closure is closed under the relation "positive power lies in `H`": adjoining roots
of elements of the root closure does not enlarge it. -/
@[to_additive ratRankZeroAdd_divHullAdd]
theorem ratRankZero_divHull (H : Subgroup G) : RatRankZero H (divHull H) := fun _ hx => hx

/-- The root closure is monotone. -/
@[to_additive divHullAdd_mono]
theorem divHull_mono {H H' : Subgroup G} (h : H ≤ H') : divHull H ≤ divHull H' := by
  rintro x ⟨n, hn, hx⟩
  exact ⟨n, hn, h hx⟩

/-- The root closure of `⊤` is `⊤`. -/
@[to_additive divHullAdd_top]
theorem divHull_top : divHull (⊤ : Subgroup G) = ⊤ :=
  le_antisymm le_top (le_divHull ⊤)

/-- **A divisible subgroup is root-closed**: `H` divisible ⟹ `divHull H = H`.  Divisibility is
used exactly here: `xⁿ ∈ H` has a root *inside* `H`, and roots are unique by torsion-freeness. -/
@[to_additive divHullAdd_eq_self_of_divisible]
theorem divHull_eq_self_of_divisible {H : Subgroup G} (hdiv : DivisibleSubgroup H) :
    divHull H = H := by
  refine le_antisymm ?_ (le_divHull H)
  rintro x ⟨n, hn, hxn⟩
  obtain ⟨y, hyH, hy⟩ := hdiv (x ^ n) hxn n hn
  have hxy : x = y := pow_right_injective (by omega : n ≠ 0) hy.symm
  rwa [hxy]

/-! ## §3 The paper's step and its converse -/

/-- **The value-group step of Lemma 3.6** (`lift:transcendental`, qe.tex l. 740): if `Γ(Ŝ) = H`
is divisible, `Γ(Ŝ) ≤ Γ(⟨Ŝ,e⟩) = K`, and the rational rank of `K/H` is `0`, then the value group
does not grow: `K = H`.

This is the paper's one-liner: `K/H` torsion gives `xⁿ ∈ H`; divisibility of `H` gives an `n`-th
root `y ∈ H` of `xⁿ`; torsion-freeness of an ordered group gives `x = y ∈ H`. -/
@[to_additive eq_of_divisible_of_ratRankZeroAdd
  /-- **The value-group step of Lemma 3.6** in additive form. -/]
theorem eq_of_divisible_of_ratRankZero {H K : Subgroup G} (hHK : H ≤ K)
    (hdiv : DivisibleSubgroup H) (hrank : RatRankZero H K) : K = H := by
  refine le_antisymm ?_ hHK
  intro x hx
  obtain ⟨n, hn, hxn⟩ := hrank x hx
  obtain ⟨y, hyH, hy⟩ := hdiv (x ^ n) hxn n hn
  have hxy : x = y := pow_right_injective (by omega : n ≠ 0) hy.symm
  rwa [hxy]

/-- The `K = ⊤` form: a divisible `Γ(Ŝ)` with `Γ(M)/Γ(Ŝ)` of rational rank `0` is all of
`Γ(M)`. -/
@[to_additive eq_top_of_divisible_of_ratRankZeroAdd_top]
theorem eq_top_of_divisible_of_ratRankZero_top {H : Subgroup G} (hdiv : DivisibleSubgroup H)
    (hrank : RatRankZero H ⊤) : H = ⊤ :=
  (eq_of_divisible_of_ratRankZero le_top hdiv hrank).symm

/-- **Divisibility is the same as root-closure collapsing**, in a group where roots exist. -/
@[to_additive divHullAdd_eq_self_iff]
theorem divHull_eq_self_iff {H : Subgroup G}
    (hG : ∀ x : G, ∀ n : ℕ, 1 ≤ n → ∃ y : G, y ^ n = x) :
    divHull H = H ↔ DivisibleSubgroup H := by
  refine ⟨fun hH => ?_, divHull_eq_self_of_divisible⟩
  intro x hx n hn
  obtain ⟨y, hy⟩ := hG x n hn
  refine ⟨y, ?_, hy⟩
  have hy' : y ∈ divHull H := ⟨n, hn, by rw [hy]; exact hx⟩
  rwa [hH] at hy'

/-- **Converse of the paper's step.**  In a group `G` in which every element has `n`-th roots,
the implication "`K/H` of rational rank `0` ⟹ `K = H`" holds for *every* `K ≥ H` exactly when
`H` is divisible.  So Lemma 3.6's divisibility hypothesis is equivalent to the inference it feeds,
not merely sufficient for the paper's particular proof route. -/
@[to_additive maximal_extension_iff_add
  /-- Converse of the paper's step, additive. -/]
theorem maximal_extension_iff {H : Subgroup G}
    (hG : ∀ x : G, ∀ n : ℕ, 1 ≤ n → ∃ y : G, y ^ n = x) :
    (∀ K : Subgroup G, H ≤ K → RatRankZero H K → K = H) ↔ DivisibleSubgroup H := by
  refine ⟨fun h => ?_, fun hdiv K hK hrank => eq_of_divisible_of_ratRankZero hK hdiv hrank⟩
  have hroot : divHull H = H := h (divHull H) (le_divHull H) (ratRankZero_divHull H)
  rw [← divHull_eq_self_iff hG]
  exact hroot

/-! ## §5 Bridge to Mathlib's `RootableBy`

`QE/GammaDiv.lean` records the divisibility of `Γ(M)` as `RootableBy (GammaOf M) ℕ` (Mathlib's
`Mathlib.GroupTheory.Divisible`).  The two lemmas below identify that class with
`DivisibleSubgroup`, so `eq_of_divisible_of_ratRankZero` accepts it unchanged. -/

/-- `RootableBy H ℕ` (Mathlib) gives divisibility in the elementwise form used here. -/
@[to_additive divisibleAddSubgroup_of_divisibleBy
  /-- `DivisibleBy H ℕ` (Mathlib) gives divisibility in the elementwise form used here. -/]
theorem divisibleSubgroup_of_rootableBy {H : Subgroup G} [RootableBy H ℕ] :
    DivisibleSubgroup H := by
  intro x hx n hn
  have hn0 : n ≠ 0 := by omega
  obtain ⟨y, hy⟩ := RootableBy.surjective_pow (A := H) (α := ℕ) (n := n) hn0 ⟨x, hx⟩
  refine ⟨y.1, y.2, ?_⟩
  have := congrArg Subtype.val hy
  simpa using this

/-- Conversely, elementwise divisibility is Mathlib's `RootableBy H ℕ`. -/
@[to_additive divisibleBy_of_divisibleAddSubgroup
  /-- Conversely, elementwise divisibility is Mathlib's `DivisibleBy H ℕ`. -/]
noncomputable def rootableBy_of_divisibleSubgroup {H : Subgroup G} (hdiv : DivisibleSubgroup H) :
    RootableBy H ℕ :=
  rootableByOfPowLeftSurj (A := H) (α := ℕ) fun {n} hn => by
    intro x
    obtain ⟨y, hy, hyn⟩ := hdiv x.1 x.2 n (by omega)
    exact ⟨⟨y, hy⟩, Subtype.ext (by simpa using hyn)⟩

/-! ## §4 The divisible-hull characterisation of `divHull`

In a group where `n`-th roots exist (in the application: `Γ(M)`, `QE/GammaDiv.lean`),
`divHull H` is exactly the *internal divisible hull* of `H`: it is divisible, contains `H`, and is
contained in every divisible subgroup containing `H`. -/

/-- `divHull H` is contained in every root-closed subgroup containing `H`; together with
`le_divHull` and `ratRankZero_divHull` this says `divHull H` is the *least* root-closed subgroup
containing `H`. -/
@[to_additive divHullAdd_le_of_rootClosed]
theorem divHull_le_of_rootClosed {H K : Subgroup G} (hHK : H ≤ K) (hK : divHull K = K) :
    divHull H ≤ K :=
  (divHull_mono hHK).trans (le_of_eq hK)

/-- `divHull H` is contained in every divisible subgroup containing `H`. -/
@[to_additive divHullAdd_le_of_divisible]
theorem divHull_le_of_divisible {H K : Subgroup G} (hHK : H ≤ K) (hdiv : DivisibleSubgroup K) :
    divHull H ≤ K :=
  divHull_le_of_rootClosed hHK (divHull_eq_self_of_divisible hdiv)

/-- **The internal divisible hull**: if every element of `G` has `n`-th roots, then `divHull H` is
divisible.  (Adjoining a root `y` of `x` keeps `y` inside `divHull H`, since a positive power of
`y` is a positive power of `x`.) -/
@[to_additive divHullAdd_divisible]
theorem divisibleSubgroup_divHull {H : Subgroup G}
    (hG : ∀ x : G, ∀ n : ℕ, 1 ≤ n → ∃ y : G, y ^ n = x) : DivisibleSubgroup (divHull H) := by
  rintro x ⟨n, hn, hxn⟩ m hm
  obtain ⟨y, hy⟩ := hG x m hm
  refine ⟨y, ⟨m * n, Nat.mul_pos (by omega) (by omega), ?_⟩, hy⟩
  rw [pow_mul, hy]
  exact hxn

end Ultramath.M2RR

/-! ## Axiom check -/

#print axioms Ultramath.M2RR.eq_one_of_pow_eq_one
#print axioms Ultramath.M2RR.pow_right_injective
#print axioms Ultramath.M2RR.divHull_eq_self_of_divisible
#print axioms Ultramath.M2RR.eq_of_divisible_of_ratRankZero
#print axioms Ultramath.M2RR.eq_top_of_divisible_of_ratRankZero_top
#print axioms Ultramath.M2RR.divHull_eq_self_iff
#print axioms Ultramath.M2RR.maximal_extension_iff
#print axioms Ultramath.M2RR.divisibleSubgroup_of_rootableBy
#print axioms Ultramath.M2RR.rootableBy_of_divisibleSubgroup
#print axioms Ultramath.M2RR.divHull_le_of_rootClosed
#print axioms Ultramath.M2RR.divHull_le_of_divisible
#print axioms Ultramath.M2RR.divisibleSubgroup_divHull
