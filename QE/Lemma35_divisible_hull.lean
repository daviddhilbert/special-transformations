/-
Evidence artifact for the ACVF quantifier-elimination campaign: the value-theoretic core of
Yin's Lemma 3.5, `lift:divisible:hull` (`qe.tex`, §3).

## Setting

`K` is a valued field inside the extension `L` (valued by `v : Valuation L Γ₀`), `e ∈ L`
satisfies `e ^ n = a` with `a ∈ K^×`, and `IsSeparated v e n` records Yin's hypothesis
`vv (e ^ i) ∉ Γ (K)` for `0 < i < n` in elementwise form:

  `IsSeparated v e n := ∀ c : K, c ≠ 0 → ∀ i, 0 < i → i < n → v (algebraMap K L c) ≠ (v e) ^ i`.

## What is proved here

1. `exists_leading_term` — the value computation: a nonzero `∑_{i<n} b i · e ^ i` has the value
   of exactly one of its terms, all other terms having strictly smaller value, because the
   terms have pairwise distinct values (`val_term_ne`, by cancelling in the value group).
2. `sum_ne_zero` — `1, e, …, e ^ (n-1)` are `K`-linearly independent.
3. `same_rv_class` — the sum lies in the `rv`-class of its leading term, which is what
   `RV (K (e)) = ⟨RV (K), rv (e)⟩` says concretely.
4. `natDegree_le_of_eval₂_eq_zero`, `irreducible_X_pow_sub_C` — the degree count and the
   irreducibility of `X ^ n - a` asserted in the source's proof.
5. `value_eq_of_map_eq`, `sum_eq_zero_iff` — the embedding half on expansions: if `d ^ n = a`,
   `v e = u d`, and the two valuations agree on `K`, then `e ↦ d` preserves values.
6. `exists_reduce`, `exists_expansion_div`, `exists_valued_image` — every element of `K⟮e⟯` is a
   quotient of expansions (reduction modulo `X ^ n - a`), so the value computation applies to
   all of `K⟮e⟯`: each `x` has an image in `N` with the same value, vanishing iff `x` does.
   This is Claim (⋆) of `lift:divisible:hull` in value form.

## What is *not* proved here (the honest boundary)

* Existence of `d` with `d ^ n = a` and `rv d = rv e`: Yin's Lemma 3.2 plus henselianity —
  in this project `QE/RV_henselian.lean` (`exists_root_rv_eq`).
* Extension of the valuation of `K` to `L`: Chevalley's lemma, Johnson §2.2.
* Both valuations here take values in the *same* ordered group `Γ₀`; Yin's situation allows an
  embedding `Γ(K) → Γ(N)`.  The RV-sort half of Claim (⋆) needs `rv d = rv e`, strictly more
  than `v d = v e`, and is again Lemma 3.2's job.
* The correspondence is not assembled into an actual `L_v`- or `L_RV`-monomorphism (that needs
  the two items above plus the RV bookkeeping).

Only `Mathlib` is imported; there is no unproved step and no new axiom.  The `#print axioms`
outputs at the end of the file are `[propext, Classical.choice, Quot.sound]` for every theorem.
-/
import Mathlib

set_option linter.unusedVariables false

namespace LiftDivHull

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-! ### The separation hypothesis -/

/-- Yin's hypothesis `v (e ^ i) ∉ Γ(K)` for `0 < i < n`, in elementwise form: no positive
power `e ^ i` with `i < n` has the value of an element of `K`. -/
def IsSeparated (v : Valuation L Γ₀) (e : L) (n : ℕ) : Prop :=
  ∀ (c : K) (i : ℕ), 0 < i → i < n → c ≠ 0 → v (algebraMap K L c) ≠ v e ^ i

section Basics

variable {v : Valuation L Γ₀} {e : L} {n : ℕ} {a : K}

lemma algebraMap_ne_zero {c : K} (hc : c ≠ 0) : algebraMap K L c ≠ 0 :=
  fun h => hc (FaithfulSMul.algebraMap_injective K L (by simpa using h))

lemma val_algebraMap_ne_zero (hc : c ≠ 0) : v (algebraMap K L c) ≠ 0 :=
  (Valuation.ne_zero_iff v).2 (algebraMap_ne_zero hc)

lemma ne_zero_of_pow_eq (hn : 0 < n) (hae : e ^ n = algebraMap K L a) (ha : a ≠ 0) : e ≠ 0 := by
  rintro rfl
  rw [zero_pow hn.ne'] at hae
  exact algebraMap_ne_zero ha hae.symm

/-- The value of a single term of the expansion. -/
lemma val_term (b : K) (i : ℕ) :
    v (algebraMap K L b * e ^ i) = v (algebraMap K L b) * v e ^ i := by
  rw [map_mul, map_pow]

/-- Dividing an equality in the value group by a power. -/
lemma pow_sub_eq_div {x : Γ₀} (hx : x ≠ 0) {b c : Γ₀} (hc : c ≠ 0) {i j : ℕ} (hij : i ≤ j)
    (h : b * x ^ i = c * x ^ j) : x ^ (j - i) = b / c := by
  have hxi : x ^ i ≠ 0 := pow_ne_zero i hx
  have h' : b * x ^ i = (c * x ^ (j - i)) * x ^ i := by
    rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hij, ← h]
  have hb : b = c * x ^ (j - i) := mul_right_cancel₀ hxi h'
  rw [hb, eq_div_iff hc, mul_comm]

/-- Under the separation hypothesis, two terms with *distinct* exponents have distinct values
(as soon as both coefficients are nonzero).  This is the only place where the hypothesis is
used. -/
lemma val_term_ne (hs : IsSeparated (K := K) v e n) (he : e ≠ 0) {b : Fin n → K} {i j : Fin n}
    (hij : i < j) (hbi : b i ≠ 0) (hbj : b j ≠ 0) :
    v (algebraMap K L (b i) * e ^ (i : ℕ)) ≠ v (algebraMap K L (b j) * e ^ (j : ℕ)) := by
  intro hEq
  have hwe : v e ≠ 0 := (Valuation.ne_zero_iff v).2 he
  have hbj0 : v (algebraMap K L (b j)) ≠ 0 := val_algebraMap_ne_zero hbj
  have h : v e ^ ((j : ℕ) - (i : ℕ))
      = v (algebraMap K L (b i)) / v (algebraMap K L (b j)) := by
    refine pow_sub_eq_div hwe hbj0 (by omega) ?_
    simpa only [map_mul, map_pow] using hEq
  have hdiv : v (algebraMap K L (b i / b j))
      = v (algebraMap K L (b i)) / v (algebraMap K L (b j)) := by
    rw [map_div₀, map_div₀]
  exact hs (b i / b j) ((j : ℕ) - (i : ℕ)) (by omega) (by omega)
    (div_ne_zero hbi hbj) (hdiv.trans h.symm)

end Basics

/-! ### The leading term of `∑_{i<n} b i * e ^ i` -/

section Main

variable {v : Valuation L Γ₀} {e : L} {n : ℕ} {a : K}

/-- **The value computation of `lift:divisible:hull`.**  If `e ^ n = a ∈ K^×` and `e` is
separated over `K`, then any nonzero element `∑_{i<n} b i * e ^ i` has the value of exactly one
of its terms, and every other term has strictly smaller value.  (In the additive notation of the
source, where `≤` is the opposite order, this is "`v (∑) = min`", the terms having distinct
values.) -/
theorem exists_leading_term (hs : IsSeparated (K := K) v e n) (hn : 0 < n) (hae : e ^ n = algebraMap K L a)
    (ha : a ≠ 0) {b : Fin n → K} (hb : ∃ i : Fin n, b i ≠ 0) :
    ∃ j : Fin n, b j ≠ 0 ∧
      v (∑ i : Fin n, algebraMap K L (b i) * e ^ (i : ℕ))
          = v (algebraMap K L (b j) * e ^ (j : ℕ)) ∧
      ∀ i : Fin n, i ≠ j →
        v (algebraMap K L (b i) * e ^ (i : ℕ))
          < v (algebraMap K L (b j) * e ^ (j : ℕ)) := by
  classical
  have he : e ≠ 0 := ne_zero_of_pow_eq hn hae ha
  obtain ⟨i₀, hi₀⟩ := hb
  have hS : (Finset.univ.filter fun i : Fin n => b i ≠ 0).Nonempty :=
    ⟨i₀, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi₀⟩⟩
  obtain ⟨j, hjS, hjmax⟩ :=
    Finset.exists_max_image (Finset.univ.filter fun i : Fin n => b i ≠ 0)
      (fun i : Fin n => v (algebraMap K L (b i) * e ^ (i : ℕ))) hS
  have hbj : b j ≠ 0 := (Finset.mem_filter.1 hjS).2
  have hvalj : v (algebraMap K L (b j) * e ^ (j : ℕ)) ≠ 0 := by
    rw [val_term]
    exact mul_ne_zero (val_algebraMap_ne_zero hbj) (pow_ne_zero _ ((Valuation.ne_zero_iff v).2 he))
  have hlt : ∀ i ∈ (Finset.univ : Finset (Fin n)) \ {j},
      v (algebraMap K L (b i) * e ^ (i : ℕ)) < v (algebraMap K L (b j) * e ^ (j : ℕ)) := by
    intro i hi
    have hne : i ≠ j := by simpa using (Finset.mem_sdiff.1 hi).2
    rcases eq_or_ne (b i) 0 with h0 | h0
    · rw [h0, map_zero, zero_mul, map_zero]
      exact zero_lt_iff.2 hvalj
    · have hiS : i ∈ Finset.univ.filter fun i : Fin n => b i ≠ 0 :=
        Finset.mem_filter.2 ⟨Finset.mem_univ _, h0⟩
      have hle := hjmax i hiS
      refine lt_of_le_of_ne hle ?_
      rcases lt_or_gt_of_ne (by omega : i ≠ j) with hij | hij
      · exact val_term_ne hs he hij h0 hbj
      · exact (val_term_ne hs he hij hbj h0).symm
  refine ⟨j, hbj, ?_, ?_⟩
  · exact Valuation.map_sum_eq_of_lt v (Finset.mem_univ j) hlt
  · intro i hi
    exact hlt i (Finset.mem_sdiff.2 ⟨Finset.mem_univ _, by simpa using hi⟩)

/-- The expansion `∑_{i<n} b i * e ^ i` is nonzero as soon as one coefficient is nonzero:
`1, e, …, e ^ (n-1)` are `K`-linearly independent.  (This is the degree count in
`lift:divisible:hull`; it also shows that `X ^ n - a` is the minimal polynomial of `e`.) -/
theorem sum_ne_zero (hs : IsSeparated (K := K) v e n) (hn : 0 < n) (hae : e ^ n = algebraMap K L a)
    (ha : a ≠ 0) {b : Fin n → K} (hb : ∃ i : Fin n, b i ≠ 0) :
    (∑ i : Fin n, algebraMap K L (b i) * e ^ (i : ℕ)) ≠ 0 := by
  obtain ⟨j, hbj, hval, -⟩ := exists_leading_term hs hn hae ha hb
  have he : e ≠ 0 := ne_zero_of_pow_eq hn hae ha
  intro h0
  rw [h0, map_zero, val_term] at hval
  exact (mul_ne_zero (val_algebraMap_ne_zero hbj)
    (pow_ne_zero _ ((Valuation.ne_zero_iff v).2 he))) hval.symm

/-- The same linear independence in Mathlib's canonical form: `1, e, …, e ^ (n-1)` are linearly
independent over `K`. -/
theorem linearIndependent_pow (hs : IsSeparated (K := K) v e n) (hn : 0 < n)
    (hae : e ^ n = algebraMap K L a) (ha : a ≠ 0) :
    LinearIndependent K (fun i : Fin n => (e ^ (i : ℕ) : L)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  by_contra hg0
  push Not at hg0
  obtain ⟨i, hi⟩ := hg0
  exact sum_ne_zero hs hn hae ha ⟨i, hi⟩ (by simpa [Algebra.smul_def] using hg)

/-- `rv`-form of the value computation: the sum lies in the same `rv`-class as its leading term
`b j * e ^ j`, which is what `RV (K[e]) = ⟨RV K, rv e⟩` means concretely. -/
theorem same_rv_class (hs : IsSeparated (K := K) v e n) (hn : 0 < n) (hae : e ^ n = algebraMap K L a)
    (ha : a ≠ 0) {b : Fin n → K} (hb : ∃ i : Fin n, b i ≠ 0) :
    ∃ j : Fin n, b j ≠ 0 ∧
      v ((∑ i : Fin n, algebraMap K L (b i) * e ^ (i : ℕ))
            - algebraMap K L (b j) * e ^ (j : ℕ))
        < v (algebraMap K L (b j) * e ^ (j : ℕ)) := by
  classical
  obtain ⟨j, hbj, -, hlt⟩ := exists_leading_term hs hn hae ha hb
  refine ⟨j, hbj, ?_⟩
  have he : e ≠ 0 := ne_zero_of_pow_eq hn hae ha
  have hvalj : v (algebraMap K L (b j) * e ^ (j : ℕ)) ≠ 0 := by
    rw [val_term]
    exact mul_ne_zero (val_algebraMap_ne_zero hbj) (pow_ne_zero _ ((Valuation.ne_zero_iff v).2 he))
  have hsum : (∑ i : Fin n, algebraMap K L (b i) * e ^ (i : ℕ))
      - algebraMap K L (b j) * e ^ (j : ℕ)
      = ∑ i ∈ (Finset.univ : Finset (Fin n)) \ {j}, algebraMap K L (b i) * e ^ (i : ℕ) := by
    rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem (f := fun i : Fin n =>
      algebraMap K L (b i) * e ^ (i : ℕ)) (Finset.mem_univ j)]
    abel
  rw [hsum]
  exact Valuation.map_sum_lt v hvalj (fun i hi => hlt i (by simpa using (Finset.mem_sdiff.1 hi).2))

/-- The hypothesis of `lift:divisible:hull` includes `v e ∉ Γ(K)`: this is its `i = 1` case. -/
theorem val_e_not_mem (hs : IsSeparated (K := K) v e n) (hn : 1 < n) {c : K} (hc : c ≠ 0) :
    v (algebraMap K L c) ≠ v e := by
  have h := hs c 1 one_pos hn hc
  simpa using h

/-- The separation hypothesis is not satisfiable inside `K`: it forces `e` to lie in a genuine
field extension.  (So `lift:divisible:hull` is a statement about extensions, not a vacuous
one.) -/
theorem algebraMap_ne (hs : IsSeparated (K := K) v e n) (hn : 1 < n)
    (hae : e ^ n = algebraMap K L a) (ha : a ≠ 0) {c : K} : algebraMap K L c ≠ e := by
  intro h
  have he : e ≠ 0 := ne_zero_of_pow_eq (by omega) hae ha
  have hc : c ≠ 0 := fun h0 => he (by rw [← h]; simp [h0])
  exact val_e_not_mem hs hn hc (by rw [h])

end Main


/-! ### The degree count and the irreducibility of `X ^ n - a`

Both are used in the proof of `lift:divisible:hull`: "since the roots of the polynomial
`X ^ n - a` are all of the same value, by the assumption on `vv (e)`, `F (X)` is irreducible
over `VF (Ŝ)`", and the degree count `[K (⟨Ŝ, e⟩) : K (Ŝ)] = n` that follows from it.
They are corollaries of the value computation above: a vanishing polynomial of degree `< n`
would be a nontrivial relation between `1, e, …, e ^ (n-1)`. -/

section Degree

variable {v : Valuation L Γ₀} {e : L} {n : ℕ} {a : K}

/-- The value computation, indexed by `Finset.range n` instead of `Fin n` (the form in which
`Polynomial.eval₂_eq_sum_range'` produces it). -/
theorem sum_range_ne_zero (hs : IsSeparated (K := K) v e n) (hn : 0 < n)
    (hae : e ^ n = algebraMap K L a) (ha : a ≠ 0) {b : ℕ → K}
    (hb : ∃ i ∈ Finset.range n, b i ≠ 0) :
    (∑ i ∈ Finset.range n, algebraMap K L (b i) * e ^ i) ≠ 0 := by
  classical
  obtain ⟨i, hi, hbi⟩ := hb
  have h := sum_ne_zero hs hn hae ha (b := fun j : Fin n => b (j : ℕ))
    ⟨⟨i, Finset.mem_range.1 hi⟩, hbi⟩
  rw [show (∑ i : Fin n, algebraMap K L (b ↑i) * e ^ (i : ℕ))
      = ∑ i ∈ Finset.range n, algebraMap K L (b i) * e ^ i from
      Fin.sum_univ_eq_sum_range (fun k : ℕ => algebraMap K L (b k) * e ^ k) n] at h
  exact h

/-- **The degree count.**  Under the separation hypothesis no nonzero polynomial over `K` of
degree `< n` vanishes at `e`; i.e. `X ^ n - a` is the minimal polynomial of `e`, so
`[K (e) : K] = n`. -/
theorem natDegree_le_of_eval₂_eq_zero (hs : IsSeparated (K := K) v e n) (hn : 0 < n)
    (hae : e ^ n = algebraMap K L a) (ha : a ≠ 0) {p : Polynomial K} (hp : p ≠ 0)
    (hroot : p.eval₂ (algebraMap K L) e = 0) : n ≤ p.natDegree := by
  classical
  by_contra hlt
  push Not at hlt
  have hz := sum_range_ne_zero hs hn hae ha (b := fun i => p.coeff i)
    ⟨p.natDegree, Finset.mem_range.2 hlt, by
      rw [Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.2 hp⟩
  refine hz ?_
  rw [← hroot]
  exact (Polynomial.eval₂_eq_sum_range' (algebraMap K L) hlt e).symm

/-- **The irreducibility of `X ^ n - a`** asserted in the proof of `lift:divisible:hull`. -/
theorem irreducible_X_pow_sub_C (hs : IsSeparated (K := K) v e n) (hn : 1 < n)
    (hae : e ^ n = algebraMap K L a) (ha : a ≠ 0) :
    Irreducible (Polynomial.X ^ n - Polynomial.C a) := by
  have hroot : Polynomial.aeval e (Polynomial.X ^ n - Polynomial.C a) = 0 := by
    simp [Polynomial.aeval_def, hae]
  have hint : IsIntegral K e :=
    ⟨_, Polynomial.monic_X_pow_sub_C a (by omega : n ≠ 0), hroot⟩
  have hmin : minpoly K e = Polynomial.X ^ n - Polynomial.C a := by
    refine (minpoly.unique K e (Polynomial.monic_X_pow_sub_C a (by omega : n ≠ 0)) hroot ?_).symm
    intro q hqmonic hqroot
    have hq0 : q ≠ 0 := hqmonic.ne_zero
    rw [Polynomial.degree_X_pow_sub_C (by omega : 0 < n) a,
      Polynomial.degree_eq_natDegree hq0]
    exact_mod_cast natDegree_le_of_eval₂_eq_zero hs (by omega : 0 < n) hae ha hq0
      (by simpa [Polynomial.aeval_def] using hqroot)
  rw [← hmin]
  exact minpoly.irreducible hint

end Degree


/-! ### Every element of `K⟮e⟯` is a quotient of expansions

This is the bookkeeping that turns the value computation on expansions into a statement about
all of `K (e)`, i.e. Claim (⋆) of `lift:divisible:hull`: `RV (K (e))` is generated over
`RV (K)` by `rv (e)`. -/

section Adjoin

variable {v : Valuation L Γ₀} {e : L} {n : ℕ} {a : K}

/-- Reduction modulo `X ^ n - a`: every value at `e` of a polynomial over `K` is the value at `e`
of a polynomial of degree `< n`.  (No irreducibility is needed: `e ^ n = a` makes the residue
of any polynomial equivalent.) -/
theorem exists_reduce (hn : 0 < n) (hae : e ^ n = algebraMap K L a) (r : Polynomial K) :
    ∃ r' : Polynomial K, r'.natDegree < n ∧ Polynomial.aeval e r' = Polynomial.aeval e r := by
  classical
  have hmonic : (Polynomial.X ^ n - Polynomial.C a).Monic :=
    Polynomial.monic_X_pow_sub_C a hn.ne'
  have hne1 : (Polynomial.X ^ n - Polynomial.C a) ≠ 1 := by
    intro hcon
    have hdeg := Polynomial.natDegree_X_pow_sub_C (R := K) (n := n) (r := a)
    rw [hcon, Polynomial.natDegree_one] at hdeg
    omega
  have hroot : Polynomial.aeval e (Polynomial.X ^ n - Polynomial.C a) = 0 := by
    simp [Polynomial.aeval_def, hae]
  have key := Polynomial.modByMonic_add_div r (Polynomial.X ^ n - Polynomial.C a)
  refine ⟨r %ₘ (Polynomial.X ^ n - Polynomial.C a), ?_, ?_⟩
  · have hlt := Polynomial.natDegree_modByMonic_lt r hmonic hne1
    rwa [Polynomial.natDegree_X_pow_sub_C] at hlt
  · have key2 : Polynomial.aeval e r
        = Polynomial.aeval e (r %ₘ (Polynomial.X ^ n - Polynomial.C a)) := by
      conv_lhs => rw [← key]
      rw [map_add, map_mul, hroot, zero_mul, add_zero]
    exact key2.symm

/-- Every element of the simple extension `K⟮e⟯` is a quotient of expansions
`∑_{i<n} b i · e ^ i`. -/
theorem exists_expansion_div (hn : 0 < n) (hae : e ^ n = algebraMap K L a) {x : L}
    (hx : x ∈ IntermediateField.adjoin K ({e} : Set L)) :
    ∃ b b' : ℕ → K,
      (∑ i ∈ Finset.range n, algebraMap K L (b' i) * e ^ i) ≠ 0 ∧
        x * (∑ i ∈ Finset.range n, algebraMap K L (b' i) * e ^ i)
          = ∑ i ∈ Finset.range n, algebraMap K L (b i) * e ^ i := by
  classical
  obtain ⟨r, s, hrs⟩ := (IntermediateField.mem_adjoin_simple_iff K x).1 hx
  obtain ⟨r', hr'deg, hr'⟩ := exists_reduce hn hae r
  obtain ⟨s', hs'deg, hs'⟩ := exists_reduce hn hae s
  have hr'eq : Polynomial.aeval e r = ∑ i ∈ Finset.range n, algebraMap K L (r'.coeff i) * e ^ i := by
    rw [← hr', Polynomial.aeval_def,
      Polynomial.eval₂_eq_sum_range' (algebraMap K L) hr'deg]
  have hs'eq : Polynomial.aeval e s = ∑ i ∈ Finset.range n, algebraMap K L (s'.coeff i) * e ^ i := by
    rw [← hs', Polynomial.aeval_def,
      Polynomial.eval₂_eq_sum_range' (algebraMap K L) hs'deg]
  have hone : (∑ i ∈ Finset.range n, algebraMap K L (if i = 0 then 1 else 0) * e ^ i) = 1 := by
    refine (Finset.sum_eq_single 0 ?_ ?_).trans ?_
    · intro i _ hi0
      simp [hi0]
    · intro hnot
      exact absurd (Finset.mem_range.2 hn) hnot
    · simp
  by_cases hs0 : Polynomial.aeval e s = 0
  · have hx0 : x = 0 := by rw [hrs, hs0, div_zero]
    refine ⟨fun _ => 0, fun i => if i = 0 then 1 else 0, ?_, ?_⟩
    · rw [hone]
      exact one_ne_zero
    · rw [hx0, zero_mul]
      simp
  · have hden : (∑ i ∈ Finset.range n, algebraMap K L (s'.coeff i) * e ^ i) ≠ 0 := by
      rw [← hs'eq]
      exact hs0
    refine ⟨r'.coeff, s'.coeff, hden, ?_⟩
    rw [hrs, hr'eq, hs'eq, div_mul_cancel₀ _ hden]

end Adjoin

/-! ### The embedding half: `e ↦ d` preserves the valuation -/

section Embedding

variable {N : Type*} [Field N] [Algebra K N]
  {v : Valuation L Γ₀} {u : Valuation N Γ₀} {e : L} {d : N} {n : ℕ} {a : K}

/-- The separation hypothesis transports across an identification of the two valued fields on
`K` together with `v e = u d`. -/
lemma isSeparated_of_eq (hs : IsSeparated (K := K) v e n)
    (h : ∀ c : K, v (algebraMap K L c) = u (algebraMap K N c)) (hval : v e = u d) :
    IsSeparated (K := K) u d n := by
  intro c i hi hin hc
  rw [← h c, ← hval]
  exact hs c i hi hin hc

/-- **The embedding half of `lift:divisible:hull`.**  If `e ^ n = a` in `L`, `d ^ n = a` in `N`,
`e` is separated over `K`, the two valuations agree on `K` and `v e = u d`, then `e ↦ d`
preserves values on the whole expansion `∑_{i<n} b i * X ^ i`.  Note that the hypothesis
`hv : v e = u d` is *weaker* than `rv d = rv e`; the latter is what supplies it in
`lift:divisible:hull` (via Lemma 3.2, `exists_root_rv_eq`). -/
theorem value_eq_of_map_eq (hs : IsSeparated (K := K) v e n) (hn : 0 < n)
    (hae : e ^ n = algebraMap K L a) (had : d ^ n = algebraMap K N a) (ha : a ≠ 0)
    (h : ∀ c : K, v (algebraMap K L c) = u (algebraMap K N c)) (hval : v e = u d)
    (b : Fin n → K) :
    u (∑ i : Fin n, algebraMap K N (b i) * d ^ (i : ℕ))
      = v (∑ i : Fin n, algebraMap K L (b i) * e ^ (i : ℕ)) := by
  classical
  by_cases hb : ∃ i : Fin n, b i ≠ 0
  · obtain ⟨j, hbj, hvalL, hltL⟩ := exists_leading_term hs hn hae ha hb
    have hterm : ∀ i : Fin n,
        u (algebraMap K N (b i) * d ^ (i : ℕ)) = v (algebraMap K L (b i) * e ^ (i : ℕ)) := by
      intro i
      rw [val_term, val_term, h (b i), hval]
    have hvalj : u (algebraMap K N (b j) * d ^ (j : ℕ)) ≠ 0 := by
      rw [hterm j, val_term]
      exact mul_ne_zero (val_algebraMap_ne_zero hbj)
        (pow_ne_zero _ ((Valuation.ne_zero_iff v).2 (ne_zero_of_pow_eq hn hae ha)))
    have hltN : ∀ i ∈ (Finset.univ : Finset (Fin n)) \ {j},
        u (algebraMap K N (b i) * d ^ (i : ℕ)) < u (algebraMap K N (b j) * d ^ (j : ℕ)) := by
      intro i hi
      rw [hterm i, hterm j]
      exact hltL i (by simpa using (Finset.mem_sdiff.1 hi).2)
    rw [Valuation.map_sum_eq_of_lt u (Finset.mem_univ j) hltN, hterm j]
    exact hvalL.symm
  · push Not at hb
    simp [hb]

/-- Injectivity of `e ↦ d` on the expansions: `∑ f (b i) * d ^ i = 0` iff all `b i = 0`.
Together with `value_eq_of_map_eq` this is exactly "`e ↦ d` is a *valued* field embedding of
`K(e)` into `N`" once one passes to quotients of expansions. -/
theorem sum_eq_zero_iff (hs : IsSeparated (K := K) v e n) (hn : 0 < n)
    (hae : e ^ n = algebraMap K L a) (had : d ^ n = algebraMap K N a) (ha : a ≠ 0)
    (h : ∀ c : K, v (algebraMap K L c) = u (algebraMap K N c)) (hval : v e = u d)
    (b : Fin n → K) :
    (∑ i : Fin n, algebraMap K L (b i) * e ^ (i : ℕ)) = 0
      ↔ (∑ i : Fin n, algebraMap K N (b i) * d ^ (i : ℕ)) = 0 := by
  constructor
  · intro hL
    have hu : u (∑ i : Fin n, algebraMap K N (b i) * d ^ (i : ℕ)) = 0 := by
      rw [value_eq_of_map_eq hs hn hae had ha h hval b, hL, map_zero]
    exact (Valuation.zero_iff u).1 hu
  · intro hN
    have hv : v (∑ i : Fin n, algebraMap K L (b i) * e ^ (i : ℕ)) = 0 := by
      rw [← value_eq_of_map_eq hs hn hae had ha h hval b, hN, map_zero]
    exact (Valuation.zero_iff v).1 hv

end Embedding


/-! ### Claim (⋆) of `lift:divisible:hull` for the whole simple extension -/

section AdjoinValue

variable {N : Type*} [Field N] [Algebra K N]
  {v : Valuation L Γ₀} {u : Valuation N Γ₀} {e : L} {d : N} {n : ℕ} {a : K}

/-- `value_eq_of_map_eq` in the `Finset.range` indexing used by `exists_expansion_div`. -/
theorem value_eq_of_map_eq_range (hs : IsSeparated (K := K) v e n) (hn : 0 < n)
    (hae : e ^ n = algebraMap K L a) (had : d ^ n = algebraMap K N a) (ha : a ≠ 0)
    (h : ∀ c : K, v (algebraMap K L c) = u (algebraMap K N c)) (hval : v e = u d)
    (b : ℕ → K) :
    u (∑ i ∈ Finset.range n, algebraMap K N (b i) * d ^ i)
      = v (∑ i ∈ Finset.range n, algebraMap K L (b i) * e ^ i) := by
  have hfin := value_eq_of_map_eq hs hn hae had ha h hval (b := fun i : Fin n => b (i : ℕ))
  rw [show (∑ i : Fin n, algebraMap K L (b ↑i) * e ^ (i : ℕ))
        = ∑ i ∈ Finset.range n, algebraMap K L (b i) * e ^ i from
        Fin.sum_univ_eq_sum_range (fun k : ℕ => algebraMap K L (b k) * e ^ k) n,
      show (∑ i : Fin n, algebraMap K N (b ↑i) * d ^ (i : ℕ))
        = ∑ i ∈ Finset.range n, algebraMap K N (b i) * d ^ i from
        Fin.sum_univ_eq_sum_range (fun k : ℕ => algebraMap K N (b k) * d ^ k) n] at hfin
  exact hfin

/-- **Claim (⋆) of `lift:divisible:hull`, value form.**  Every element `x` of the simple valued
field extension `K⟮e⟯` has an image `y` in `N` — namely `num (d) / den (d)` where
`x = num (e) / den (e)` is a quotient of expansions — which has the same value and vanishes
exactly when `x` does.  Together with the multiplicativity of this correspondence, this is
"the monomorphism `f` extends to `⟨Ŝ, e⟩`. -/
theorem exists_valued_image (hs : IsSeparated (K := K) v e n) (hn : 0 < n)
    (hae : e ^ n = algebraMap K L a) (had : d ^ n = algebraMap K N a) (ha : a ≠ 0)
    (h : ∀ c : K, v (algebraMap K L c) = u (algebraMap K N c)) (hval : v e = u d)
    {x : L} (hx : x ∈ IntermediateField.adjoin K ({e} : Set L)) :
    ∃ y : N, (y = 0 ↔ x = 0) ∧ u y = v x := by
  classical
  obtain ⟨b, b', hden, hnum⟩ := exists_expansion_div hn hae hx
  have hvalNum := value_eq_of_map_eq_range hs hn hae had ha h hval b
  have hvalD := value_eq_of_map_eq_range hs hn hae had ha h hval b'
  have hDne : (∑ i ∈ Finset.range n, algebraMap K N (b' i) * d ^ i) ≠ 0 := by
    intro h0
    refine hden ((Valuation.zero_iff v).1 ?_)
    rw [← hvalD, h0, map_zero]
  refine ⟨(∑ i ∈ Finset.range n, algebraMap K N (b i) * d ^ i)
    / (∑ i ∈ Finset.range n, algebraMap K N (b' i) * d ^ i), ?_, ?_⟩
  · constructor
    · intro hy
      have hNum0 : (∑ i ∈ Finset.range n, algebraMap K N (b i) * d ^ i) = 0 := by
        rcases div_eq_zero_iff.1 hy with h' | h'
        · exact h'
        · exact absurd h' hDne
      have hNumL0 : (∑ i ∈ Finset.range n, algebraMap K L (b i) * e ^ i) = 0 := by
        refine (Valuation.zero_iff v).1 ?_
        rw [← hvalNum, hNum0, map_zero]
      rw [← hnum] at hNumL0
      exact (mul_eq_zero.1 hNumL0).resolve_right hden
    · intro hx0
      have hNumL0 : (∑ i ∈ Finset.range n, algebraMap K L (b i) * e ^ i) = 0 := by
        rw [← hnum, hx0, zero_mul]
      have hNum0 : (∑ i ∈ Finset.range n, algebraMap K N (b i) * d ^ i) = 0 := by
        refine (Valuation.zero_iff u).1 ?_
        rw [hvalNum, hNumL0, map_zero]
      rw [hNum0, zero_div]
  · rw [map_div₀, hvalNum, hvalD]
    have hvD : v (∑ i ∈ Finset.range n, algebraMap K L (b' i) * e ^ i) ≠ 0 :=
      (Valuation.ne_zero_iff v).2 hden
    rw [← hnum, map_mul, mul_div_assoc, div_self hvD, mul_one]

end AdjoinValue

/-! ### Axiom check -/

#print axioms LiftDivHull.exists_leading_term
#print axioms LiftDivHull.sum_ne_zero
#print axioms LiftDivHull.linearIndependent_pow
#print axioms LiftDivHull.same_rv_class
#print axioms LiftDivHull.value_eq_of_map_eq
#print axioms LiftDivHull.sum_eq_zero_iff
#print axioms LiftDivHull.algebraMap_ne
#print axioms LiftDivHull.sum_range_ne_zero
#print axioms LiftDivHull.natDegree_le_of_eval₂_eq_zero
#print axioms LiftDivHull.irreducible_X_pow_sub_C
#print axioms LiftDivHull.exists_reduce
#print axioms LiftDivHull.exists_expansion_div
#print axioms LiftDivHull.value_eq_of_map_eq_range
#print axioms LiftDivHull.exists_valued_image

end LiftDivHull
