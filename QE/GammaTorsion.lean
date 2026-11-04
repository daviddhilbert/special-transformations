/-
**The `Γ`-side of Lemma 3.6: rational rank 0 + `Γ(Ŝ)` divisible ⇒ `Γ` unchanged.**

Direction `d4` of swarm `smw2ngn1z` (member `m3`).  Audit frame: this file is the part of
the paper's Lemma 3.6 `lift:transcendental` (`qe.tex:732`) that is **pure ordered-group
algebra**, i.e. the part Mathlib already has the vocabulary for; the transcendental input
(EP Thm 3.4.3, "the rational rank of `Γ(⟨Ŝ,e⟩)/Γ(Ŝ)` is 0") is *not* proved here — it enters
as the named hypothesis `RatRankZeroSet`, exactly in the tree's own class form
(`GammaDiv.GammaHullInitialQ`, `gammaHullInitialQ_iff_image`).

## What the paper does at this step

`qe.tex:744-747`: *"By the dimension inequality of valuation theory (EP Thm 3.4.3), the
rational rank of `Γ(⟨Ŝ,e⟩)/Γ(Ŝ)` is 0. Since `Γ(Ŝ)` is divisible, we actually have
`Γ(⟨Ŝ,e⟩) = Γ(Ŝ)`. So for every `b ∈ VF(⟨Ŝ,e⟩)` there is an `a ∈ VF(Ŝ)` such that
`vv(b/a) = 0`."*

The algebraic content of that sentence is:

* rational rank 0 of `L/K` means `L/K` is a **torsion** group;
* a torsion extension of a **divisible** subgroup of a torsion-free ordered abelian group is
  trivial: if `q^n ∈ K` with `n > 0` and `r^n = q^n` with `r ∈ K`, then `r = q` (the power
  map of an ordered abelian group is injective), so `q ∈ K` already.

That is `subset_of_divisible_of_ratRankZero` (§1) and its instantiation at the encoding's
`Γ(M)` in §3 (`gammaImage_subset_of_divisible_of_hullInitial`).  §2 records the same step in
the shape `q3` needs, over `ℚ`: a submodule of a `ℚ`-vector space that receives a positive
multiple of every vector is everything (`submodule_eq_top_of_forall_smul_mem`) — this is what
"rational rank 0" means once the divisibility has been used, and it is the Mathlib-side form a
future `Module.rank`-based statement of EP 3.4.3 would plug into.

## Stress tests (§4)

* `exists_ratRankZero_not_subset`: the divisibility hypothesis is **not** redundant.  A pair
  `(K, L)` with `RatRankZeroSet K L` and `L ⊄ K` exists (concretely `G = Multiplicative ℤ`,
  `K = ⟨2⟩`, `L = ⊤`): "torsion over `Γ(Ŝ)`" alone does not give the paper's `Γ`-unchanged
  conclusion, so the paper's "since `Γ(Ŝ)` is divisible" is load-bearing.
* `RatRankZeroSet` requires a positive exponent (`0 < n`): with `n = 0` allowed the predicate
  would be vacuous at any `K` containing `1`, i.e. Lemma 3.6's group step would be contentless.

No `sorry`, no `axiom`; axioms are printed at the end of the file.
-/
import GammaDiv
import M5Ledger

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
open SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.GammaGroup
open SpecialTransformations.Milestone0.GammaDiv

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace SpecialTransformations.Milestone0.GammaTorsion

/-! ## §1 The abstract ordered-group core -/

section Abstract

variable {G : Type*} [CommGroup G] [LinearOrder G] [IsOrderedMonoid G]

/-- **Powers are injective in a linearly ordered commutative group.**  Used by the paper's
"`Γ(Ŝ)` divisible" step: a root of `q ^ n` (for `n > 0`) is `q` itself. -/
theorem pow_inj_of_pos {n : ℕ} (hn : 0 < n) {a b : G} (h : a ^ n = b ^ n) : a = b := by
  rcases lt_trichotomy a b with hlt | heq | hgt
  · exact absurd h (ne_of_lt (pow_lt_pow_left' hn.ne' hlt))
  · exact heq
  · exact absurd h.symm (ne_of_lt (pow_lt_pow_left' hn.ne' hgt))

/-- **Rational rank zero, in class form.**  `L / K` is a torsion group: every class of `L` has a
positive power in `K`.  This is the paper's `ratrank(Γ(⟨Ŝ,e⟩)/Γ(Ŝ)) = 0` written without ever
mentioning `⊗ ℚ` (over a finitely generated `Γ(⟨Ŝ,e⟩)/Γ(Ŝ)` the two readings agree; the
`ℚ`-reading is §2).

The exponent is required to be positive: with `n = 0` the predicate would be vacuous. -/
def RatRankZeroSet (K L : Set G) : Prop := ∀ q ∈ L, ∃ n : ℕ, 0 < n ∧ q ^ n ∈ K

/-- **Divisibility of a subset of an ordered abelian group** (`Γ(Ŝ)` divisible): every element
has an `n`-th root inside the subset, for every `n > 0`. -/
def DivisibleSet (K : Set G) : Prop := ∀ a ∈ K, ∀ n : ℕ, 0 < n → ∃ b ∈ K, b ^ n = a

/-- **The paper's group step** (`qe.tex:745-747`): if `K` is divisible and `L/K` is torsion, then
`L ⊆ K`. -/
theorem subset_of_divisible_of_ratRankZero {K L : Set G}
    (hdiv : DivisibleSet K) (h0 : RatRankZeroSet (G := G) K L) : L ⊆ K := by
  intro q hq
  obtain ⟨n, hn, hqn⟩ := h0 q hq
  obtain ⟨b, hb, hbn⟩ := hdiv (q ^ n) hqn n hn
  have hbq : b = q := pow_inj_of_pos hn hbn
  rwa [hbq] at hb

/-- The same for subgroups, with the hypotheses in `Subgroup` form. -/
theorem subgroup_le_of_divisible_of_ratRankZero {K L : Subgroup G}
    (hdiv : ∀ a ∈ K, ∀ n : ℕ, 0 < n → ∃ b ∈ K, b ^ n = a)
    (h0 : ∀ x ∈ L, ∃ n : ℕ, 0 < n ∧ x ^ n ∈ K) : L ≤ K := by
  intro q hq
  obtain ⟨n, hn, hqn⟩ := h0 q hq
  obtain ⟨b, hb, hbn⟩ := hdiv (q ^ n) hqn n hn
  have hbq : b = q := pow_inj_of_pos hn hbn
  rwa [hbq] at hb

/-- Divisibility is *not* redundant: `RatRankZeroSet` alone does not force `L ⊆ K`.
Concrete witness: `G = Multiplicative ℤ`, `K = ⟨2⟩` (the even integers), `L = ⊤`; every integer
has its square in `2ℤ`-in-multiplicative-form... in additive notation `2m` has `2m` itself, and
`x ^ 2 = ofAdd (2x) ∈ K`, while `ofAdd 1 ∉ K`. -/
theorem exists_ratRankZero_not_subset :
    ∃ (G : Type) (_ : CommGroup G) (_ : LinearOrder G) (_ : IsOrderedMonoid G)
      (K L : Set G), RatRankZeroSet K L ∧ ¬ L ⊆ K := by
  refine ⟨Multiplicative ℤ, inferInstance, inferInstance, inferInstance,
    Set.range (fun m : ℤ => Multiplicative.ofAdd (m + m)), Set.univ, ?_, ?_⟩
  · intro q _
    refine ⟨2, two_pos, ⟨q.toAdd, ?_⟩⟩
    show Multiplicative.ofAdd (q.toAdd + q.toAdd) = q ^ 2
    rw [pow_two, ← ofAdd_toAdd q]
    exact ofAdd_add q.toAdd q.toAdd
  · intro h
    obtain ⟨m, hm⟩ := h (Set.mem_univ (Multiplicative.ofAdd (1 : ℤ)))
    have h3 : m + m = 1 := by
      have := congrArg Multiplicative.toAdd hm
      simpa using this
    omega

/-- **`RatRankZeroSet` has content**: it is not satisfied by a *proper* pair in a group with an
element of infinite order.  With `G = Multiplicative ℤ`, `K = {1}` and `L = ⊤`, the class of `1`
has no positive power in `K`, so the hypothesis `RatRankZeroSet K L` genuinely constrains `L`
(contrast: with `K = ⊤` it is automatic, `ratRankZeroSet_top`). -/
theorem not_ratRankZeroSet_bot :
    ¬ RatRankZeroSet (G := Multiplicative ℤ) {1} Set.univ := by
  intro h
  obtain ⟨n, hn, hyp⟩ := h (Multiplicative.ofAdd (1 : ℤ)) (Set.mem_univ _)
  have h1 : (Multiplicative.ofAdd (1 : ℤ)) ^ n = 1 := hyp
  have h2 : (n : ℤ) = 0 := by
    have := congrArg Multiplicative.toAdd h1
    simpa using this
  omega

/-- The trivial case: `L = K` satisfies the hypothesis (so it is satisfiable at every group). -/
theorem ratRankZeroSet_self (K : Set G) : RatRankZeroSet K K := by
  intro q hq
  exact ⟨1, one_pos, by simpa using hq⟩

end Abstract

/-! ## §2 The `ℚ`-form: rational rank 0 over a `ℚ`-vector space -/

section Rational

/-- **Mathlib-side form of "rational rank 0".**  In a `ℚ`-vector space a submodule that receives
a positive multiple of every vector is everything.  This is the step `n⁻¹ • (n • v)` of
`subset_of_divisible_of_ratRankZero`, exposed in the vocabulary (`Module`, `Submodule`, `ℚ`-scalars)
in which a `Module.rank`-based transcription of EP Thm 3.4.3 would state its conclusion. -/
theorem submodule_eq_top_of_forall_smul_mem {V : Type*} [AddCommGroup V] [Module ℚ V]
    {W : Submodule ℚ V} (h : ∀ v : V, ∃ n : ℕ, 0 < n ∧ (n : ℚ) • v ∈ W) : W = ⊤ := by
  refine top_unique fun v _ => ?_
  obtain ⟨n, hn, hnv⟩ := h v
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have hv : v = (n : ℚ)⁻¹ • ((n : ℚ) • v) := by
    rw [smul_smul, inv_mul_cancel₀ hnq, one_smul]
  rw [hv]
  exact W.smul_mem _ hnv

end Rational

/-! ## §3 Instantiation at the encoding's `Γ(M) = GammaOf M` -/

section Model

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- **Divisibility of `Γ(S)` in the quotient form** (`Γ(S)` as the image `GammaImage S` of the
encoding's value map).  This is the paper's hypothesis "`Γ(Ŝ)` is divisible"
(`qe.tex:733`), stated on `GammaDiv.GammaImage` rather than on the encoding's representative
form `Assembly.GammaDivisible S`. -/
def GammaImageDivisible (S : LRV.Substructure M) : Prop :=
  ∀ q ∈ GammaImage S (M := M), ∀ n : ℕ, 0 < n → ∃ r ∈ GammaImage S (M := M), r ^ n = q

/-- **`GammaHullInitialQ` *is* rational rank 0** in class form: every class of `Γ(T)` has a
positive power in `Γ(S)` (`GammaDiv.gammaHullInitialQ_iff_image`). -/
theorem ratRankZeroSet_gammaImage {S T : LRV.Substructure M}
    (h : GammaHullInitialQ (M := M) S T) :
    RatRankZeroSet (GammaImage S (M := M)) (GammaImage T (M := M)) :=
  (gammaHullInitialQ_iff_image (M := M) (S := S) (T := T)).mp h

/-- **Lemma 3.6, `Γ`-step** (`qe.tex:745-747`), at the encoding's `Γ(M)`:

`Γ(Ŝ)` divisible + `ratrank(Γ(T)/Γ(Ŝ)) = 0` ⇒ `Γ(T) ⊆ Γ(Ŝ)`.

All the transcendental input is in the second hypothesis; nothing about `e`, `rv(e)` or
`VF` occurs here. -/
theorem gammaImage_subset_of_divisible_of_hullInitial {S T : LRV.Substructure M}
    (hdiv : GammaImageDivisible (M := M) S)
    (hhull : GammaHullInitialQ (M := M) S T) :
    GammaImage T (M := M) ⊆ GammaImage S (M := M) :=
  subset_of_divisible_of_ratRankZero (G := GammaOf M) hdiv
    (ratRankZeroSet_gammaImage hhull)

/-- The paper's conclusion `Γ(⟨Ŝ,e⟩) = Γ(Ŝ)` as an equality of the two images. -/
theorem gammaImage_eq_of_divisible_of_hullInitial {S T : LRV.Substructure M}
    (hST : S ≤ T) (hdiv : GammaImageDivisible (M := M) S)
    (hhull : GammaHullInitialQ (M := M) S T) :
    GammaImage T (M := M) = GammaImage S (M := M) := by
  refine Set.Subset.antisymm (gammaImage_subset_of_divisible_of_hullInitial hdiv hhull) ?_
  intro q hq
  obtain ⟨s, hs, hsrv, hs0, rfl⟩ := hq
  exact ⟨s, hST hs, hsrv, hs0, rfl⟩

/-- **The consumer-shaped form** (`GammaDiv.GammaEqQ`): from the two hypotheses of Lemma 3.6's
group step, every nonzero value class of `T` is the class of a nonzero element of `S`.  This is
the paper's "for every `b ∈ VF(⟨Ŝ,e⟩)` there is an `a ∈ VF(Ŝ)` such that `vv(b/a) = 0`" at the
level of value classes. -/
theorem gammaEqQ_of_divisible_of_hullInitial {S T : LRV.Substructure M}
    (hdiv : GammaImageDivisible (M := M) S)
    (hhull : GammaHullInitialQ (M := M) S T) :
    GammaEqQ (M := M) S T := by
  intro t ht hrv ht0
  have hmem : gammaMk (mkR t hrv ht0) ∈ GammaImage T (M := M) := ⟨t, ht, hrv, ht0, rfl⟩
  obtain ⟨s, hs, hsrv, hs0, hsq⟩ := gammaImage_subset_of_divisible_of_hullInitial hdiv hhull hmem
  exact ⟨s, hs, hsrv, hs0, hsq⟩

/-- **The converter**: the encoding's representative form `Assembly.GammaDivisible S`
("`rvPow u n = t · c` with `c` a unit of `S`") implies the quotient form
`GammaImageDivisible S` used above.  Same transport as
`GammaDiv.exists_gamma_root_of_gammaDivisible_top`, with `⊤` replaced by an arbitrary `S`
(the residue factor `c` is a unit, hence `1` in `Γ`). -/
theorem gammaImageDivisible_of_gammaDivisible {S : LRV.Substructure M}
    (hdiv : Assembly.GammaDivisible S) : GammaImageDivisible (M := M) S := by
  rintro q ⟨t, ht, hrv, ht0, rfl⟩ n hn
  obtain ⟨u, c, huS, hu, hu0, _hcS, hcu, heq⟩ := hdiv t ht hrv ht0 n hn
  have hcrv : iRV c := Jm2.iRV_of_inK (Or.inl hcu)
  have hc0 : c ≠ iRVZero := units_ne_zero hcu
  refine ⟨gammaMk (mkR u hu hu0), ⟨u, huS, hu, hu0, rfl⟩, ?_⟩
  rw [gammaMk_rvPow]
  rw [gammaMk_congr (rvPow_mem hu n) (rvPow_ne_zero hu hu0 n)
    (Transfer.rv_mul_mem hM hrv hcrv) (rvStar_mul_nonzero ⟨hrv, ht0⟩ ⟨hcrv, hc0⟩) heq]
  have hprod : (mkR (iRVMul t c) (Transfer.rv_mul_mem hM hrv hcrv)
      (rvStar_mul_nonzero ⟨hrv, ht0⟩ ⟨hcrv, hc0⟩) : RVStar M)
      = mkR t hrv ht0 * rvStarOfUnit hcu := Subtype.ext rfl
  have hone : gammaMk (rvStarOfUnit hcu) = 1 := (gammaMk_eq_one_iff_units).mpr hcu
  rw [hprod, gammaMk_mul, hone, mul_one]

/-- **Lemma 3.6's `Γ`-step from the encoding's own divisibility predicate**: if
`Assembly.GammaDivisible S` holds (the tree's form of "`Γ(Ŝ)` is divisible", produced e.g. by
`M5Ledger.DivisibilityStep`) and `Γ(T)` lies in the divisible hull of `Γ(S)`
(`GammaHullInitialQ`, the tree's class form of EP 3.4.3's rational-rank-0 conclusion), then
every value class of `T` is a value class of `S`. -/
theorem gammaEqQ_of_gammaDivisible_of_hullInitial {S T : LRV.Substructure M}
    (hdiv : Assembly.GammaDivisible S) (hhull : GammaHullInitialQ (M := M) S T) :
    GammaEqQ (M := M) S T :=
  gammaEqQ_of_divisible_of_hullInitial (gammaImageDivisible_of_gammaDivisible hdiv) hhull

/-- **The paper's `VF`-sorted form of the value normalization.**  Lemma 3.6's conclusion is used
in the shape "for every `b ∈ VF(⟨Ŝ,e⟩)` there is an `a ∈ VF(Ŝ)` with `vv(b/a) = 0`" — that is,
with the *witness a in the `VF` sort* of `S`.  `gammaEqQ` gives a witness in the `RV` sort of `S`;
`Assembly.IsVFGen S` (the tree's `rv(VF(S)) = RV(S)`) upgrades it, and the resulting statement is
what the polynomial induction on `Σ bᵢ eⁱ` consumes.

`iRv a` is the residue of the `VF`-sorted witness; the two proof arguments of the class
constructor are quantified over so that no `rv`-membership lemma is needed at the call site. -/
theorem exists_vf_class_witness {S T : LRV.Substructure M}
    (hgen : Assembly.IsVFGen S) (hdiv : Assembly.GammaDivisible S)
    (hhull : GammaHullInitialQ (M := M) S T) :
    ∀ (t : M) (ht : t ∈ T) (hrv : iRV t) (ht0 : t ≠ iRVZero),
      ∃ (a : M), a ∈ S ∧ iVF a ∧ iRv a ∈ S ∧ iRv a ≠ iRVZero ∧
        ∀ (hrv' : iRV (iRv a)) (h0' : iRv a ≠ iRVZero),
          gammaMk (mkR t hrv ht0) = gammaMk (mkR (iRv a) hrv' h0') := by
  intro t ht hrv ht0
  obtain ⟨s, hs, hsrv, hs0, heq⟩ :=
    gammaEqQ_of_gammaDivisible_of_hullInitial hdiv hhull t ht hrv ht0
  rcases hgen s hs hsrv with ⟨a, haS, haVF, hrvEq⟩ | hzero
  · refine ⟨a, haS, haVF, ?_, ?_, ?_⟩
    · rwa [hrvEq]
    · rw [hrvEq]; exact hs0
    · intro hrv' h0'
      exact heq.trans (gammaMk_congr hsrv hs0 hrv' h0' hrvEq.symm)
  · exact absurd hzero hs0

end Model

#print axioms SpecialTransformations.Milestone0.GammaTorsion.pow_inj_of_pos
#print axioms SpecialTransformations.Milestone0.GammaTorsion.subset_of_divisible_of_ratRankZero
#print axioms SpecialTransformations.Milestone0.GammaTorsion.exists_ratRankZero_not_subset
#print axioms SpecialTransformations.Milestone0.GammaTorsion.not_ratRankZeroSet_bot
#print axioms SpecialTransformations.Milestone0.GammaTorsion.ratRankZeroSet_self
#print axioms SpecialTransformations.Milestone0.GammaTorsion.submodule_eq_top_of_forall_smul_mem
#print axioms SpecialTransformations.Milestone0.GammaTorsion.gammaImage_subset_of_divisible_of_hullInitial
#print axioms SpecialTransformations.Milestone0.GammaTorsion.gammaEqQ_of_divisible_of_hullInitial
#print axioms SpecialTransformations.Milestone0.GammaTorsion.gammaImageDivisible_of_gammaDivisible
#print axioms SpecialTransformations.Milestone0.GammaTorsion.gammaEqQ_of_gammaDivisible_of_hullInitial
#print axioms SpecialTransformations.Milestone0.GammaTorsion.exists_vf_class_witness

end SpecialTransformations.Milestone0.GammaTorsion
