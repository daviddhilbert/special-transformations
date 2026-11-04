/-
A transcendence-degree model for Yin, "Special transformations in algebraically closed valued
fields", §4.1 "Dimensions" (`paper.tex` 803-966) -- swarm `smw1qqem3`, member m4 (direction d7).

**What this file is.**  `paper.tex:841-843` introduces, for a definable `A ⊆ VF^n × RV^m`,

> For any `(ā,t̄) ∈ A` let `td(ā,t̄)` be the transcendental degree of `VF(ā)` over `VF(S)`.
> Let `td(A) = max { td(ā,t̄) : (ā,t̄) ∈ A }`.

and Lemma `VF:dim:tran:deg` (`paper.tex:853`) proves `dim_VF(A) = td(A)`.  So the *intended
model* of the §4.1 dimension function is transcendence degree over the parameter field.  This
file builds that model over an arbitrary field extension `k → K` (read `k = VF(S)`, `K` a big
algebraically closed valued field, `A` a subset of the affine space `VF^n = Fin n → K`) and
checks the §4.1 assertions *in* it.  Consequence: the §4.1 dimension statements are jointly
consistent and non-vacuous -- they are not a bundle of hypotheses that only the trivial
`dim ≡ 0` satisfies.

**The definition used.**  `tdPt a` is *not* literally `Algebra.trdeg k (k(a))`: it is the
equivalent combinatorial form "largest size of an algebraically independent subfamily of the
tuple `a`".  The equivalence of the two for a finite tuple is the standard characterisation of
transcendence degree ("trdeg = the size of a maximal algebraically independent subfamily").
Mathlib has `Algebra.trdeg` and the bound `AlgebraicIndependent.cardinalMk_le_trdeg`, but not
the bound of `trdeg` by the *number of generators* of a field extension, which is what the
equivalence needs; so the comparison with `Algebra.trdeg` is left open here (nothing below
depends on it).  Defining `tdPt` combinatorially keeps every statement below an honest theorem
rather than a hypothesis.  `VF:dim:tran:deg`
itself (the identification of the paper's `dim_VF`, defined by *definable finite-to-one maps*,
with `td`) is **not** proved here and is not claimed.

**What is proved** (all with `#print axioms` ⊆ {propext, Classical.choice, Quot.sound}):

* `tdPt_le_pred_of_aeval_eq_zero`, `hypersurface_dim_le` -- a point of a hypersurface
  `{x | f(x) = 0}`, `f ≠ 0`, has `td ≤ n - 1`: the algebraic content of "a proper Zariski closed
  subset of `VF^n` has dimension `< n`", i.e. the `≤` half of `dim:vf:same:zar` (`paper.tex:893`)
  and the only-if direction of `full:dim:open:poly` (`paper.tex:868`) in the model.
* `dim_univ_eq_card`, `dim_open_eq_card` -- `dim VF^n = n` (the normalisation behind
  `VF:dim:tran:deg`) and: a Zariski open set `{q ≠ 0}`, `q ≠ 0`, has full dimension `n`
  (the if direction of `full:dim:open:poly`).
* `dim_eq_card_of_mem_generic` -- a set containing a generic point has full dimension `n`.
* `dim_coord_hyperplane_eq` / `dim_coord_hyperplane_model` -- the coordinate hyperplane
  `{x₀ = 0} ⊆ VF^{m+1}` has dimension *exactly* `m` (so the drop in `hypersurface_dim_le` is
  sharp, not merely an inequality), the `dim:vf:same:zar` (`paper.tex:893`) computation for a
  hyperplane.
* `dim_mono`, `dim_union`, `dim_empty`, `dim_singleton`, `dim_singleton_zero`, `tdPt_zero_tuple`
  -- `dim` is monotone (`VF:dim:mono`, `paper.tex:864`, in its trivial monotonicity form), the
  dimension of a finite union is the max, `dim ∅ = 0`, `dim` of a point is `0`.
* `section41_model` -- all of the above simultaneously, in the concrete model
  `k ⊆ k(t₁,…,t_n) = FractionRing k[X₁,…,X_n]`.
* `dim_univ_model` at `p + q`, under the identification `VF^{p+q} = VF^p × VF^q`, is additivity
  of the dimension over products: `dim (VF^p × VF^q) = p + q = dim VF^p + dim VF^q`.

**What is NOT proved here** (named gaps, per the project rules; nothing below is smuggled in as
a hypothesis):

1. `VF:dim:tran:deg` (`paper.tex:853`) itself.  The paper's `dim_VF` is defined by *definable
   finite-to-one maps into `VF^k × RV_Γ^l`*; the tree's `Sec4Dim.dimVF` is exactly that
   syntactic object.  This file models the *right-hand side* of Lemma 853 (`td`), not the
   tree's `dimVF`, and the identification of the two is not proved.  What this file
   establishes is the consistency/non-vacuity of the §4.1 dimension statements as statements
   about `td`, and the truth of their combinatorial content -- not the bridge from the
   syntactic `dimVF`.
2. The comparison `tdPt = Algebra.trdeg k (k(ā))`: the missing direction is "transcendence
   degree is bounded by the number of generators of a *field* extension", which Mathlib does
   not have.  Nothing below depends on it (see the paragraph on the definition above).
3. The `RV` sort.  The definitions here are parametric in the base field, so the paper's
   `dim_RV` (`paper.tex:888`: the least `k` with a definable finite-to-one map `B → RV^k`) is
   modelled by `tdPt`/`dim` at the residue field -- but the *identification* with the paper's
   `dim_RV` is the same Mathlib gap as (2), and it is not carried out; Lemmas
   `VF:dim:rv:polydisc` (885), `dim:rv:same:zar` (912), `rv:dim:gamma:coset` (923) and
   `RV:fiber:dim:same` (946) are therefore not modelled either.
4. `dim:VF:pullback` (832) -- the fibrewise statement `dim_VF(A) = max dim_VF(f^{-1}(t̄))` --
   is not addressed; nothing here is a pullback computation.
5. §4.2 (`defn:VF:cat` … `RV:isomorphism:weaker:condition`) and §4.3 (Grothendieck groups) are
   out of scope for this file.

Compile: `LEAN_PATH=$LEAN_PATH lean Sec4DimACFModel.lean` (exit 0, no `sorry`, `#print axioms`
⊆ {propext, Classical.choice, Quot.sound}).
-/
import Mathlib

open MvPolynomial

namespace Sec4DimModel

section Basic
variable (k : Type*) [Field k]
variable {K : Type*} [Field K] [Algebra k K]

/-- `Indep a m`: the tuple `a` has an algebraically independent subfamily of size `m`. -/
def Indep {n : ℕ} (a : Fin n → K) (m : ℕ) : Prop :=
  ∃ s : Fin m ↪ Fin n, AlgebraicIndependent k (fun j => a (s j))

/-- `tdPt a`: the paper's `td(ā)` (`paper.tex:841`), the transcendence degree of `VF(ā)` over
`VF(S)`, in the equivalent form "largest size of an algebraically independent subfamily". -/
noncomputable def tdPt {n : ℕ} (a : Fin n → K) : ℕ := by
  classical
  exact (Finset.range (n + 1)).sup (fun m => if Indep k a m then m else 0)

/-- `dim A`: the paper's `td(A)` (`paper.tex:843`), `max { td(ā) : ā ∈ A }`. -/
noncomputable def dim {n : ℕ} (A : Set (Fin n → K)) : ℕ := by
  classical
  exact (Finset.range (n + 1)).sup (fun m => if ∃ a ∈ A, Indep k a m then m else 0)

theorem le_tdPt {n : ℕ} {a : Fin n → K} {m : ℕ} (hm : m ≤ n) (h : Indep k a m) :
    m ≤ tdPt k a := by
  classical
  have hmem : m ∈ Finset.range (n + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hm)
  have hle : (if Indep k a m then m else 0) ≤ tdPt k a := by
    rw [tdPt]
    exact Finset.le_sup (f := fun m => if Indep k a m then m else 0) hmem
  rwa [if_pos h] at hle

theorem tdPt_le {n : ℕ} {a : Fin n → K} {r : ℕ} (h : ∀ m, Indep k a m → m ≤ r) :
    tdPt k a ≤ r := by
  classical
  rw [tdPt]
  refine Finset.sup_le (fun m _ => ?_)
  by_cases hm : Indep k a m
  · simpa [hm] using h m hm
  · simp [hm]

theorem le_dim {n : ℕ} {A : Set (Fin n → K)} {m : ℕ} (hm : m ≤ n)
    (h : ∃ a ∈ A, Indep k a m) : m ≤ dim k A := by
  classical
  have hmem : m ∈ Finset.range (n + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hm)
  have hle : (if ∃ a ∈ A, Indep k a m then m else 0) ≤ dim k A := by
    rw [dim]
    exact Finset.le_sup (f := fun m => if ∃ a ∈ A, Indep k a m then m else 0) hmem
  rwa [if_pos h] at hle

theorem dim_le {n : ℕ} {A : Set (Fin n → K)} {r : ℕ}
    (h : ∀ m, (∃ a ∈ A, Indep k a m) → m ≤ r) : dim k A ≤ r := by
  classical
  rw [dim]
  refine Finset.sup_le (fun m _ => ?_)
  by_cases hm : ∃ a ∈ A, Indep k a m
  · simpa [hm] using h m hm
  · simp [hm]

/-- An algebraically independent subfamily cannot be longer than the tuple. -/
theorem indep_le_card {n m : ℕ} {a : Fin n → K} (h : Indep k a m) : m ≤ n := by
  obtain ⟨s, -⟩ := h
  simpa using Fintype.card_le_of_injective (⇑s) s.injective

/-- `td(ā) ≤ n` for `ā ∈ VF^n`. -/
theorem tdPt_le_card {n : ℕ} (a : Fin n → K) : tdPt k a ≤ n :=
  tdPt_le k (fun _ h => indep_le_card k h)

theorem dim_mono {n : ℕ} {A B : Set (Fin n → K)} (h : A ⊆ B) : dim k A ≤ dim k B := by
  refine dim_le k (fun m hm => ?_)
  obtain ⟨a, ha, hind⟩ := hm
  exact le_dim k (indep_le_card k hind) ⟨a, h ha, hind⟩

theorem dim_empty {n : ℕ} : dim k (∅ : Set (Fin n → K)) = 0 := by
  refine le_antisymm (dim_le k (fun m hm => ?_)) (Nat.zero_le _)
  obtain ⟨a, ha, -⟩ := hm
  exact absurd ha (Set.notMem_empty a)

theorem dim_singleton {n : ℕ} (a : Fin n → K) : dim k ({a} : Set (Fin n → K)) = tdPt k a := by
  classical
  have hfun : (fun m => if (∃ b ∈ ({a} : Set (Fin n → K)), Indep k b m) then m else 0)
      = (fun m => if Indep k a m then m else 0) := by
    funext m
    simp only [Set.mem_singleton_iff, exists_eq_left]
  simp only [dim, tdPt, hfun]

theorem dim_union_le {n : ℕ} (A B : Set (Fin n → K)) :
    dim k (A ∪ B) ≤ max (dim k A) (dim k B) := by
  refine dim_le k (fun m hm => ?_)
  obtain ⟨a, ha, hind⟩ := hm
  rcases ha with ha | ha
  · exact le_trans (le_dim k (indep_le_card k hind) ⟨a, ha, hind⟩) (le_max_left _ _)
  · exact le_trans (le_dim k (indep_le_card k hind) ⟨a, ha, hind⟩) (le_max_right _ _)

/-- The dimension of a finite union is the maximum (`paper.tex:843`, `dim` as a maximum). -/
theorem dim_union {n : ℕ} (A B : Set (Fin n → K)) :
    dim k (A ∪ B) = max (dim k A) (dim k B) :=
  le_antisymm (dim_union_le k A B)
    (max_le (dim_mono k (Set.subset_union_left)) (dim_mono k (Set.subset_union_right)))

/-! ### Dependence from a vanishing polynomial: a hypersurface drops dimension -/

theorem not_algIndep_of_aeval_eq_zero {n : ℕ} {f : MvPolynomial (Fin n) k} (hf : f ≠ 0)
    {a : Fin n → K} (ha : aeval a f = 0) : ¬ AlgebraicIndependent k a := by
  rw [algebraicIndependent_iff_injective_aeval]
  intro hinj
  exact hf (hinj (by rw [ha, map_zero]))

/-- If the whole tuple is algebraically dependent, no independent subfamily has full length. -/
theorem indep_lt_of_not_algIndep {n m : ℕ} {a : Fin n → K}
    (hdep : ¬ AlgebraicIndependent k a) (h : Indep k a m) : m < n := by
  obtain ⟨s, hs⟩ := h
  rcases lt_or_eq_of_le (indep_le_card k ⟨s, hs⟩) with hlt | heq
  · exact hlt
  · exfalso
    have hbij : Function.Bijective (⇑s) := by
      rw [Fintype.bijective_iff_injective_and_card]
      exact ⟨s.injective, by simp [heq]⟩
    have h1 : AlgebraicIndependent k (a ∘ ⇑(Equiv.ofBijective (⇑s) hbij)) := hs
    exact hdep ((algebraicIndependent_equiv (Equiv.ofBijective (⇑s) hbij) (f := a)).mp h1)

/-- **`dim:vf:same:zar` (`paper.tex:893`), pointwise form.** A point satisfying a nontrivial
polynomial equation has transcendence degree at most `n - 1`. -/
theorem tdPt_le_pred_of_aeval_eq_zero {n : ℕ} {f : MvPolynomial (Fin n) k} (hf : f ≠ 0)
    {a : Fin n → K} (ha : aeval a f = 0) : tdPt k a ≤ n - 1 := by
  have hdep := not_algIndep_of_aeval_eq_zero k hf ha
  have h := tdPt_le k (a := a) (r := n - 1) (fun m hm => by
    have := indep_lt_of_not_algIndep k hdep hm
    omega)
  omega

/-- **`full:dim:open:poly` (`paper.tex:868`), only-if side, in the model.** Every subset of a
hypersurface `{x | f(x) = 0}`, `f ≠ 0`, has dimension at most `n - 1`: a full-dimensional
definable set satisfies no nontrivial polynomial equation. -/
theorem hypersurface_dim_le {n : ℕ} {f : MvPolynomial (Fin n) k} (hf : f ≠ 0) :
    dim k {x : Fin n → K | aeval x f = 0} ≤ n - 1 := by
  refine dim_le k (fun m hm => ?_)
  obtain ⟨a, ha, hind⟩ := hm
  have hdep := not_algIndep_of_aeval_eq_zero k hf (by simpa using ha)
  have := indep_lt_of_not_algIndep k hdep hind
  omega

end Basic

section Model
variable (k : Type*) [Field k]
variable {K : Type*} [Field K] [Algebra k K]

/-- **`VF:dim:tran:deg` (`paper.tex:853`) normalisation, in the model.** An algebraically
independent `n`-tuple has `td = n`. -/
theorem tdPt_eq_card_of_algIndep {n : ℕ} {t : Fin n → K} (ht : AlgebraicIndependent k t) :
    tdPt k t = n := by
  refine le_antisymm (tdPt_le_card k t) ?_
  refine le_tdPt k (le_refl n) ⟨Function.Embedding.refl (Fin n), ?_⟩
  simpa using ht

/-- `dim VF^n = n` in the model, in the presence of a generic point. -/
theorem dim_univ_eq_card {n : ℕ} {t : Fin n → K} (ht : AlgebraicIndependent k t) :
    dim k (Set.univ : Set (Fin n → K)) = n := by
  refine le_antisymm ?_ ?_
  · refine dim_le k (fun m hm => ?_)
    obtain ⟨a, -, hind⟩ := hm
    exact indep_le_card k hind
  · exact le_dim k (le_refl n)
      ⟨t, Set.mem_univ t, ⟨Function.Embedding.refl (Fin n), by simpa using ht⟩⟩

set_option maxHeartbeats 2000000 in
/-- **`dim:vf:same:zar` (`paper.tex:893`) at a coordinate hyperplane.**  In `VF^{m+1}` the
Zariski closed set `{x | x₀ = 0}` has dimension exactly `m`: the dimension drops by one, so the
bound of `hypersurface_dim_le` is sharp.  The generic point of the hyperplane is
`(0, t₁, …, t_m)` for an algebraically independent `m`-tuple `t`. -/
theorem dim_coord_hyperplane_eq {m : ℕ} {t : Fin m → K} (ht : AlgebraicIndependent k t) :
    dim k {x : Fin (m + 1) → K | x ⟨0, Nat.succ_pos m⟩ = 0} = m := by
  obtain ⟨f, hf, hset⟩ :
      ∃ f : MvPolynomial (Fin (m + 1)) k, f ≠ 0 ∧
        {x : Fin (m + 1) → K | aeval x f = 0}
          = {x : Fin (m + 1) → K | x ⟨0, Nat.succ_pos m⟩ = 0} :=
    ⟨MvPolynomial.X ⟨0, Nat.succ_pos m⟩, by simp, by ext x; simp⟩
  rw [← hset]
  refine le_antisymm ?_ ?_
  · simpa using hypersurface_dim_le k (K := K) hf
  · have hy : (Fin.cons (0 : K) t : Fin (m + 1) → K) ∈ {x : Fin (m + 1) → K | aeval x f = 0} := by
      rw [hset]
      simp
    have hs : Indep k (Fin.cons (0 : K) t : Fin (m + 1) → K) m := by
      refine ⟨Fin.succEmb m, ?_⟩
      show AlgebraicIndependent k
        (fun j : Fin m => (Fin.cons (0 : K) t : Fin (m + 1) → K) (Fin.succEmb m j))
      simpa using ht
    exact le_dim k (Nat.le_succ m) ⟨_, hy, hs⟩

/-- **`full:dim:open:poly` (`paper.tex:868`), if side, in the model.** A Zariski open set
`{x | q(x) ≠ 0}`, `q ≠ 0`, contains the generic point, hence has full dimension `n`. -/
theorem dim_open_eq_card {n : ℕ} {q : MvPolynomial (Fin n) k} (hq : q ≠ 0)
    {t : Fin n → K} (ht : AlgebraicIndependent k t) :
    dim k {x : Fin n → K | aeval x q ≠ 0} = n := by
  have hmem : t ∈ {x : Fin n → K | aeval x q ≠ 0} := by
    simp only [Set.mem_ofPred_eq]
    intro h
    exact hq (ht.eq_zero_of_aeval_eq_zero q h)
  refine le_antisymm ?_ ?_
  · refine dim_le k (fun m hm => ?_)
    obtain ⟨a, -, hind⟩ := hm
    exact indep_le_card k hind
  · exact le_dim k (le_refl n)
      ⟨t, hmem, ⟨Function.Embedding.refl (Fin n), by simpa using ht⟩⟩

/-- **Full dimension from a generic point.**  If the set contains a point all of whose `n`
coordinates are algebraically independent over `VF(S)`, its dimension is `n`: the "contains an
open polydisc" side of `full:dim:open:poly` (`paper.tex:868`) in the ACF model, in the general
form (the point need not be the `X`-tuple of `dim_open_eq_card`). -/
theorem dim_eq_card_of_mem_generic {n : ℕ} {A : Set (Fin n → K)} {t : Fin n → K}
    (ht : AlgebraicIndependent k t) (hmem : t ∈ A) : dim k A = n := by
  refine le_antisymm (dim_le k (fun m hm => by
    obtain ⟨a, -, hind⟩ := hm
    exact indep_le_card k hind)) ?_
  exact le_dim k (le_refl n) ⟨t, hmem, ⟨Function.Embedding.refl (Fin n), by simpa using ht⟩⟩

/-- `dim` of a point is `0` (the point `0` is `VF(S)`-rational). -/
theorem tdPt_zero_tuple {n : ℕ} : tdPt k (0 : Fin n → K) = 0 := by
  refine le_antisymm (tdPt_le k (fun m hm => ?_)) (Nat.zero_le _)
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · omega
  · obtain ⟨s, hs⟩ := hm
    exfalso
    have hzero : (fun j : Fin m => ((0 : Fin n → K) (s j) : K)) = fun _ => (0 : K) := by
      funext j; simp
    rw [hzero] at hs
    have hi : Fin m := ⟨0, hpos⟩
    have hX : (MvPolynomial.X hi : MvPolynomial (Fin m) k) ≠ 0 := by simp
    refine hX (hs.eq_zero_of_aeval_eq_zero (MvPolynomial.X hi) ?_)
    simp

theorem dim_singleton_zero {n : ℕ} :
    dim k ({(0 : Fin n → K)} : Set (Fin n → K)) = 0 := by
  rw [dim_singleton k, tdPt_zero_tuple k]

end Model

section FunctionField
variable (k : Type*) [Field k]

/-- The model field `VF(S)(t₁,…,t_n)` of rational functions: the fraction field of `k[X₁,…,X_n]`. -/
abbrev Kmodel (n : ℕ) := FractionRing (MvPolynomial (Fin n) k)

/-- The generic point `(t₁,…,t_n) = (X₁,…,X_n)` of `VF^n` is algebraically independent over the
parameter field: the non-vacuity input. -/
theorem algIndep_model (n : ℕ) :
    AlgebraicIndependent k (fun i =>
      IsScalarTower.toAlgHom k (MvPolynomial (Fin n) k) (Kmodel k n) (MvPolynomial.X i)) :=
  AlgebraicIndependent.map' (MvPolynomial.algebraicIndependent_X (Fin n) k)
    (f := IsScalarTower.toAlgHom k (MvPolynomial (Fin n) k) (Kmodel k n))
    (IsFractionRing.injective _ _)

/-- `dim VF^n = n` in the concrete model `k ⊆ k(t₁,…,t_n)`. -/
theorem dim_univ_model (n : ℕ) :
    dim k (Set.univ : Set (Fin n → Kmodel k n)) = n :=
  dim_univ_eq_card k (algIndep_model k n)

/-- A nonempty Zariski open subset of `VF^n` has dimension `n` in the concrete model. -/
theorem dim_open_model (n : ℕ) {q : MvPolynomial (Fin n) k} (hq : q ≠ 0) :
    dim k {x : Fin n → Kmodel k n | aeval x q ≠ 0} = n :=
  dim_open_eq_card k hq (algIndep_model k n)

/-- The hyperplane `{x₀ = 0} ⊆ VF^{m+1}` has dimension exactly `m` in the concrete model
`k ⊆ k(t₁,…,t_m)`. -/
theorem dim_coord_hyperplane_model (m : ℕ) :
    dim k {x : Fin (m + 1) → Kmodel k m | x ⟨0, Nat.succ_pos m⟩ = 0} = m :=
  dim_coord_hyperplane_eq k (K := Kmodel k m) (algIndep_model k m)

/-- **Summary (non-vacuity of the §4.1 dimension axioms).** In the model
`k ⊆ k(t₁,…,t_n)`, the paper's §4.1 assertions hold *simultaneously*:
`dim VF^n = n` (`VF:dim:tran:deg` normalisation), `dim` of a point `= 0`, `dim ≤ n`,
`dim` monotone in the set (`VF:dim:mono`), `dim` of a union is the max, every subset of a
hypersurface has dimension `≤ n - 1` (`dim:vf:same:zar`, `full:dim:open:poly` only-if), and a
Zariski open set has full dimension `n` (`full:dim:open:poly` if).  Hence those statements are
jointly consistent and are not satisfied only by the degenerate `dim ≡ 0`. -/
theorem section41_model (n : ℕ) :
    dim k (Set.univ : Set (Fin n → Kmodel k n)) = n ∧
    dim k ({(0 : Fin n → Kmodel k n)} : Set (Fin n → Kmodel k n)) = 0 ∧
    (∀ A : Set (Fin n → Kmodel k n), dim k A ≤ n) ∧
    (∀ A B : Set (Fin n → Kmodel k n), A ⊆ B → dim k A ≤ dim k B) ∧
    (∀ A B : Set (Fin n → Kmodel k n), dim k (A ∪ B) = max (dim k A) (dim k B)) ∧
    (∀ f : MvPolynomial (Fin n) k, f ≠ 0 →
      dim k {x : Fin n → Kmodel k n | aeval x f = 0} ≤ n - 1) ∧
    (∀ q : MvPolynomial (Fin n) k, q ≠ 0 →
      dim k {x : Fin n → Kmodel k n | aeval x q ≠ 0} = n) :=
  ⟨dim_univ_model k n, dim_singleton_zero k,
   fun A => dim_le k (fun m hm => by
     obtain ⟨a, -, hind⟩ := hm
     exact indep_le_card k hind),
   fun _ _ h => dim_mono k h, fun _ _ => dim_union k _ _,
   fun f hf => hypersurface_dim_le k hf, fun q hq => dim_open_model k n hq⟩

end FunctionField

end Sec4DimModel

#print axioms Sec4DimModel.tdPt_le_pred_of_aeval_eq_zero
#print axioms Sec4DimModel.hypersurface_dim_le
#print axioms Sec4DimModel.dim_open_eq_card
#print axioms Sec4DimModel.dim_univ_eq_card
#print axioms Sec4DimModel.tdPt_zero_tuple
#print axioms Sec4DimModel.dim_coord_hyperplane_eq
#print axioms Sec4DimModel.section41_model
