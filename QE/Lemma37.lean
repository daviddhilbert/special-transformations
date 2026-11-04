import RVCalc

/-!
# Lemma 3.7 (`e:transc`, arXiv:1006.2467) in the frozen tagged encoding — full proof

Member m5, swarm `smw1rx5g2` (frozen-theorem swarm, direction 5).  Self-contained over
`QE/RVCalc.lean` (frozen encoding `Milestone0/Encoding.lean` + its `RV`/`Γ` calculus).

`Transc.e_transc` (member m3 of swarm `smw1kqpdp`, `TranscFrozen.lean`) states Lemma 3.7 in the
tagged encoding with three hypotheses `hbe`, `hdis`, `hvnz`.  This file **discharges two of them**,
so that what remains are exactly the paper's hypotheses.

Paper (Lemma \label{e:transc}): *suppose `e` is transcendental over `VF(Ŝ)` and `vv(e)` is of
infinite order modulo `Γ(Ŝ)`; for any `b = ∑_{0 ≤ i ≤ m} b_i e^i` with `b_i ∈ VF(Ŝ)`, if `b ≠ 0`
then `vv(b) = min {vv(b_i e^i) : 0 ≤ i ≤ m}`.*

Contents, in order.

§0 (inlined verbatim from m3's `TranscFrozen.lean`, credited there): `Cls` (the paper's
`vv u = vv v`), `vpow`, `vsum`, their sort closure, `cls_rv_add_of_dominated`, the no-cancellation
induction `cls_vsum_of_pairwise_distinct`, and `e_transc`.

§1–§2 (`hvnz` discharged).  New `RV` algebra: `rvpow`, `iRV_rvpow`, `rv_vpow` (`iRv (vpow e n) =
rvpow (iRv e) n`), `rvpow_add`, `rvpow_ne_zero`, `rv_mul_ne_zero` (`RV∖{0}` is a monoid),
`cls_mul_iff` (the class order is cancellable — `leMulCompatFull`, both directions), `cls_add_of_not_cls`
(strict triangle: different classes ⇒ sum ≠ 0).  Then `vsum_exists_min`: if the terms are nonzero
and their classes pairwise distinct, every nonempty partial sum has the class of a *minimal* term —
which yields `vsum_ne_zero_of_pairwise_distinct`, i.e. `hvnz`.  Hence `e_transc'`: `hvnz` replaced
by the primitive `∀ i, b i * e ^ i ≠ 0`.

§3–§4 (`hdis` discharged).  `Γ(Ŝ)` is not term-definable in the tagged language (`S ∩ VF` is only a
ring: there is no inverse symbol), so it is represented the way the proof uses it — by the set `G`
of `RV`-classes closed under multiplication (`hGmul`) and under class-inverse (`hGinv`) and
containing the classes of the coefficients (`hGb`); `hpow` is the paper's hypothesis verbatim,
`∀ k ≠ 0, ∀ x ∈ G, ¬ Cls (ε^k) x`.  `hdis_of_lt` is the paper's cancellation argument
(`vv(b_i e^i) = vv(b_j e^j)`, `i < j` ⇒ `vv(e^{j-i}) = vv(b_i/b_j) ∈ Γ(Ŝ)`, contradiction), and
`hdis_of_gamma` removes the case distinction.  Finally `e_transc_of_gamma` is Lemma 3.7 with only
the paper's hypotheses: `e ≠ 0`, `vv(e)` of infinite order mod `G`, nonzero coefficients in `G`,
and `b = ∑_{i ≤ m} b_i e^i ≠ 0`.

Not formalized here (outside the tagged language, they need the subfield structure):
the paper's `` `e` transcendental over `VF(Ŝ)` `` (not needed for this conclusion) and the second
half of Lemma 3.7 (`Γ(⟨Ŝ,e⟩) = Γ(Ŝ) ⊕ ℤ·vv(e)`).  Coefficients are required nonzero (`hb0`),
i.e. the sum is indexed over the support, as in the paper; a zero coefficient has no class in `RV`.
-/

set_option linter.unusedSectionVars false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0

namespace SpecialTransformations.Milestone0
namespace Transc

open RVCalc
open SpecialTransformations.Milestone0.Transfer

variable {M : Type} [LRV.Structure M]

/-! ## 0. The existing port (member m3, swarm `smw1kqpdp`): `Cls`, `vpow`, `vsum`, `e_transc` -/

/-! ## The class relation and the `VF`-side order -/

/-- `Cls u v`: the paper's `vv u = vv v` on the `RV` sort (same class modulo `Kˣ`). -/
def Cls (u v : M) : Prop := iLe u v ∧ iLe v u

/-- `VLe x y`: the paper's `vv x ≤ vv y` on the `VF` sort. -/
def VLe (x y : M) : Prop := iLe (iRv x) (iRv y)

theorem cls_refl (hM : M ⊨ Axioms.ACVF) {a : M} (ha : iRV a) : Cls a a :=
  ⟨le_refl_rv hM ha, le_refl_rv hM ha⟩

theorem cls_symm {a b : M} (h : Cls a b) : Cls b a := ⟨h.2, h.1⟩

theorem cls_trans (hM : M ⊨ Axioms.ACVF) {a b c : M} (ha : iRV a) (hb : iRV b) (hc : iRV c)
    (hab : Cls a b) (hbc : Cls b c) : Cls a c :=
  ⟨le_trans_rv hM ha hb hc hab.1 hbc.1, le_trans_rv hM hc hb ha hbc.2 hab.2⟩

theorem not_le_of_not_cls {a b : M} (h1 : iLe a b) (h : ¬ Cls a b) : ¬ iLe b a :=
  fun h2 => h ⟨h1, h2⟩

/-! ## Powers and finite sums in the `VF` sort -/

/-- `e ^ n` in the `VF` sort. -/
noncomputable def vpow (e : M) : ℕ → M
  | 0 => iVFOne
  | (n + 1) => iVFMul (vpow e n) e

theorem iVF_vpow (hM : M ⊨ Axioms.ACVF) {e : M} (he : iVF e) : ∀ n, iVF (vpow e n)
  | 0 => vf_one_mem (M := M) hM
  | (n + 1) => vf_mul_mem (M := M) hM (iVF_vpow hM he n) he

/-- The `n`-fold sum `f 0 + f 1 + ⋯ + f (n-1)`. -/
noncomputable def vsum (f : ℕ → M) : ℕ → M
  | 0 => iVFZero
  | (n + 1) => iVFAdd (vsum f n) (f n)

theorem iVF_vsum (hM : M ⊨ Axioms.ACVF) {f : ℕ → M} (hf : ∀ i, iVF (f i)) :
    ∀ n, iVF (vsum f n)
  | 0 => vf_zero_mem (M := M) hM
  | (n + 1) => vf_add_mem (M := M) hM (iVF_vsum hM hf n) (hf n)

/-! ## No cancellation -/

/-- The no-cancellation step (`e:transc`'s inductive heart), read off `RVCalc.rv_add_of_lt`:
if `vv x < vv y` then `x + y` has the same value as `x`. -/
theorem cls_rv_add_of_dominated (hM : M ⊨ Axioms.ACVF) {x y : M} (hx : iVF x) (hy : iVF y)
    (hxy : VLe x y) (hlt : ¬ VLe y x) : Cls (iRv (iVFAdd x y)) (iRv x) :=
  rv_add_of_lt hM hx hy hxy hlt

/-- **Lemma 3.7 (`e:transc`), no cancellation, in the frozen tagged encoding.**  If the terms
`f 0, …, f (n-1)` have values in pairwise distinct classes — which is what "`vv(e)` is of infinite
order modulo `Γ(Ŝ)`" supplies for `f i = b i * e ^ i` — and the sum is nonzero, then the sum has
the same value as one of the terms, and that term's value is the smallest:
`vv(∑_{i<n} f i) = min_{i<n} vv(f i)`. -/
theorem cls_vsum_of_pairwise_distinct (hM : M ⊨ Axioms.ACVF) {f : ℕ → M}
    (hf : ∀ i, iVF (f i))
    (hdis : ∀ i j, i ≠ j → ¬ Cls (iRv (f i)) (iRv (f j)))
    (hvnz : ∀ k, 0 < k → vsum f k ≠ iVFZero) :
    ∀ n, vsum f n ≠ iVFZero →
      ∃ j, j < n ∧ Cls (iRv (vsum f n)) (iRv (f j)) ∧
        ∀ i, i < n → iLe (iRv (f j)) (iRv (f i)) := by
  intro n
  induction n with
  | zero => intro h; exact absurd rfl h
  | succ n ih =>
    intro hsum0
    have hfn : iRV (iRv (f n)) := rv_mem hM (hf n)
    by_cases hS : vsum f n = iVFZero
    · have hn0 : n = 0 := Nat.eq_zero_of_not_pos (fun hpos => hvnz n hpos hS)
      have hf0 : iRV (iRv (f 0)) := rv_mem hM (hf 0)
      refine ⟨0, ?_, ?_, ?_⟩
      · rw [hn0]; exact Nat.lt_succ_self 0
      · have hvn : vsum f (n + 1) = f n := by
          show iVFAdd (vsum f n) (f n) = f n
          rw [hS, vf_zero_add hM (hf n)]
        rw [hvn, hn0]
        exact cls_refl hM hf0
      · intro i hi
        rw [hn0] at hi
        have hi0 : i = 0 := by omega
        rw [hi0]
        exact le_refl_rv hM hf0
    · obtain ⟨j, hjn, hcls, hdom⟩ := ih hS
      have hSv : iVF (vsum f n) := iVF_vsum hM hf n
      have hfj : iRV (iRv (f j)) := rv_mem hM (hf j)
      have hrvS : iRV (iRv (vsum f n)) := rv_mem hM hSv
      have hrvN : iRV (iRv (vsum f (n + 1))) := rv_mem hM (iVF_vsum hM hf (n + 1))
      rcases le_total_rv hM hrvS hfn with h1 | h1
      · have hnc : ¬ Cls (iRv (vsum f n)) (iRv (f n)) := by
          intro hc
          exact hdis j n (Nat.ne_of_lt hjn)
            ⟨le_trans_rv hM hfj hrvS hfn hcls.2 hc.1,
             le_trans_rv hM hfn hrvS hfj hc.2 hcls.1⟩
        have hsum : Cls (iRv (vsum f (n + 1))) (iRv (vsum f n)) :=
          cls_rv_add_of_dominated hM hSv (hf n) h1 (not_le_of_not_cls h1 hnc)
        refine ⟨j, Nat.lt_succ_of_lt hjn, ?_, ?_⟩
        · exact cls_trans hM hrvN hrvS hfj hsum hcls
        · intro i hi
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | hieq
          · exact hdom i hi'
          · rw [hieq]
            exact le_trans_rv hM hfj hrvS hfn hcls.2 h1
      · have hnc : ¬ Cls (iRv (f n)) (iRv (vsum f n)) := by
          intro hc
          exact hdis j n (Nat.ne_of_lt hjn)
            ⟨le_trans_rv hM hfj hrvS hfn hcls.2 hc.2,
             le_trans_rv hM hfn hrvS hfj hc.1 hcls.1⟩
        have hsum : Cls (iRv (vsum f (n + 1))) (iRv (f n)) := by
          have h := cls_rv_add_of_dominated hM (hf n) hSv h1 (not_le_of_not_cls h1 hnc)
          have hc : iVFAdd (vsum f n) (f n) = iVFAdd (f n) (vsum f n) :=
            vf_add_comm hM hSv (hf n)
          show Cls (iRv (iVFAdd (vsum f n) (f n))) (iRv (f n))
          rw [hc]
          exact h
        refine ⟨n, Nat.lt_succ_self n, hsum, ?_⟩
        intro i hi
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | hieq
        · refine le_trans_rv hM hfn hfj (rv_mem hM (hf i)) ?_ (hdom i hi')
          exact le_trans_rv hM hfn hrvS hfj h1 hcls.1
        · rw [hieq]
          exact le_refl_rv hM hfn

/-- **Lemma 3.7 (`e:transc`) of arXiv:1006.2467 in the frozen tagged encoding.**  For
`b = ∑_{0 ≤ i ≤ m} b_i e^i` whose nonzero terms have values in pairwise distinct classes — the
paper's hypothesis "`vv(e)` is of infinite order modulo `Γ(Ŝ)`" for coefficients in `K(Ŝ)^×`
(see `YinLemma37.v_mul_pow_ne` for the derivation in the Mathlib setting) — and with `b ≠ 0`, the
value of `b` is the value of one of the terms `b_j e^j`, and that term's value is the smallest:
`vv(b) = min { vv(b_i e^i) : 0 ≤ i ≤ m }`, i.e. `∀ i ≤ m, vv(b_j e^j) ≤ vv(b_i e^i)`. -/
theorem e_transc (hM : M ⊨ Axioms.ACVF) {e : M} {b : ℕ → M}
    (hbe : ∀ i, iVF (iVFMul (b i) (vpow e i)))
    (hdis : ∀ i j, i ≠ j →
      ¬ Cls (iRv (iVFMul (b i) (vpow e i))) (iRv (iVFMul (b j) (vpow e j))))
    (hvnz : ∀ k, 0 < k → vsum (fun i => iVFMul (b i) (vpow e i)) k ≠ iVFZero)
    {m : ℕ}
    (hne : vsum (fun i => iVFMul (b i) (vpow e i)) (m + 1) ≠ iVFZero) :
    ∃ j, j ≤ m ∧
      Cls (iRv (vsum (fun i => iVFMul (b i) (vpow e i)) (m + 1)))
        (iRv (iVFMul (b j) (vpow e j))) ∧
      ∀ i, i ≤ m →
        iLe (iRv (iVFMul (b j) (vpow e j))) (iRv (iVFMul (b i) (vpow e i))) := by
  obtain ⟨j, hj, hcls, hdom⟩ :=
    cls_vsum_of_pairwise_distinct hM hbe hdis hvnz (m + 1) hne
  exact ⟨j, Nat.lt_succ_iff.mp hj, hcls, fun i hi => hdom i (Nat.lt_succ_iff.mpr hi)⟩


/-! ## 1-2. `hvnz` discharged -/

/-! ## 1. Powers in the `RV` sort -/

/-- `ε ^ n` in the `RV` sort (`ε ^ 0 = 1`). -/
noncomputable def rvpow (ε : M) : ℕ → M
  | 0 => iRVOne
  | (n + 1) => iRVMul (rvpow ε n) ε

theorem iRV_rvpow (hM : M ⊨ Axioms.ACVF) {ε : M} (hε : iRV ε) : ∀ n, iRV (rvpow ε n)
  | 0 => rv_one_mem (M := M) hM
  | (n + 1) => rv_mul_mem (M := M) hM (iRV_rvpow hM hε n) hε

/-- `iRv` of a `VF`-power is the corresponding `RV`-power (`rvMulHom`, by induction). -/
theorem rv_vpow (hM : M ⊨ Axioms.ACVF) {e : M} (he : iVF e) :
    ∀ n, iRv (vpow e n) = rvpow (iRv e) n
  | 0 => rv_one hM
  | (n + 1) => by
      show iRv (iVFMul (vpow e n) e) = iRVMul (rvpow (iRv e) n) (iRv e)
      rw [rv_mul_hom_of_model hM (iVF_vpow hM he n) he, rv_vpow hM he n]

/-- `ε^(m+n) = ε^m · ε^n`. -/
theorem rvpow_add (hM : M ⊨ Axioms.ACVF) {ε : M} (hε : iRV ε) (m : ℕ) :
    ∀ n, rvpow ε (m + n) = iRVMul (rvpow ε m) (rvpow ε n)
  | 0 => by
      show rvpow ε m = iRVMul (rvpow ε m) iRVOne
      exact (rv_mul_one_any_right hM (iRV_rvpow hM hε m)).symm
  | (n + 1) => by
      rw [Nat.add_succ]
      show iRVMul (rvpow ε (m + n)) ε = iRVMul (rvpow ε m) (iRVMul (rvpow ε n) ε)
      rw [rvpow_add hM hε m n,
        rv_mul_assoc_of_model hM (iRV_rvpow hM hε m) (iRV_rvpow hM hε n) hε]

/-! ## 2. `RV ∖ {0}` is a multiplicative monoid -/

/-- A product of nonzero `RV`-elements is nonzero (`rvMulInvRV`). -/
theorem rv_mul_ne_zero (hM : M ⊨ Axioms.ACVF) {a b : M} (ha : iRV a) (hb : iRV b)
    (ha0 : a ≠ iRVZero) (hb0 : b ≠ iRVZero) : iRVMul a b ≠ iRVZero := by
  intro h
  obtain ⟨d, hd, _hd0, hdab⟩ := rv_mul_inv_exists_of_model hM hb hb0
  have hcomm : iRVMul d b = iRVOne := hdab
  have haeq : a = iRVZero := by
    calc a = iRVMul a iRVOne := (rv_mul_one_any_right hM ha).symm
      _ = iRVMul a (iRVMul d b) := by rw [hcomm]
      _ = iRVMul (iRVMul a b) d := by
            rw [rv_mul_assoc_of_model hM ha hb hd, rv_mul_comm_of_model hM hb hd]
      _ = iRVMul iRVZero d := by rw [h]
      _ = iRVZero := rv_mul_zero_left_of_model hM hd
  exact ha0 haeq

/-- A nonzero `RV`-element has nonzero powers. -/
theorem rvpow_ne_zero (hM : M ⊨ Axioms.ACVF) {ε : M} (hε : iRV ε) (hε0 : ε ≠ iRVZero) :
    ∀ n, rvpow ε n ≠ iRVZero
  | 0 => rv_one_ne_zero hM
  | (n + 1) =>
      rv_mul_ne_zero hM (iRV_rvpow hM hε n) hε (rvpow_ne_zero hM hε hε0 n) hε0

/-! ## 3. The class relation is scale invariant in both directions -/

/-- `Cls (a c) (b c) ↔ Cls a b` for `c ≠ 0`: the cancellation law for the `Γ`-class order
(`leMulCompatFull`). -/
theorem cls_mul_iff (hM : M ⊨ Axioms.ACVF) {a b c : M} (ha : iRV a) (hb : iRV b) (hc : iRV c)
    (hc0 : c ≠ iRVZero) : (Cls (iRVMul a c) (iRVMul b c) ↔ Cls a b) :=
  ⟨fun h => ⟨(le_mul_iff hM ha hb hc hc0).mpr h.1, (le_mul_iff hM hb ha hc hc0).mpr h.2⟩,
   fun h => ⟨(le_mul_iff hM ha hb hc hc0).mp h.1, (le_mul_iff hM hb ha hc hc0).mp h.2⟩⟩

/-- One direction of scale invariance, with **no** nonvanishing hypothesis on `c` (at `c = 0`
both sides are `0 ≤ 0`). -/
theorem le_mul_right_of_le (hM : M ⊨ Axioms.ACVF) {a b c : M} (ha : iRV a) (hb : iRV b)
    (hc : iRV c) (h : iLe a b) : iLe (iRVMul a c) (iRVMul b c) := by
  by_cases hc0 : c = iRVZero
  · subst hc0
    rw [rv_mul_zero_right_of_model hM ha, rv_mul_zero_right_of_model hM hb]
    exact le_refl_rv hM (rv_zero_mem hM)
  · exact (le_mul_iff hM ha hb hc hc0).mp h

theorem cls_mul_right (hM : M ⊨ Axioms.ACVF) {a b c : M} (ha : iRV a) (hb : iRV b) (hc : iRV c)
    (h : Cls a b) : Cls (iRVMul a c) (iRVMul b c) :=
  ⟨le_mul_right_of_le hM ha hb hc h.1, le_mul_right_of_le hM hb ha hc h.2⟩

theorem cls_mul_left (hM : M ⊨ Axioms.ACVF) {a b c : M} (ha : iRV a) (hb : iRV b) (hc : iRV c)
    (h : Cls a b) : Cls (iRVMul c a) (iRVMul c b) := by
  rw [rv_mul_comm_of_model hM hc ha, rv_mul_comm_of_model hM hc hb]
  exact cls_mul_right hM ha hb hc h

/-! ## 4. The additive step: `x + y ≠ 0` when the classes differ -/

/-- If `x, y ≠ 0` have **different** `Γ`-classes then `x + y ≠ 0`.  (The strict triangle
`rv_add_of_lt`: the sum has the class of the smaller of the two terms.) -/
theorem cls_add_of_not_cls (hM : M ⊨ Axioms.ACVF) {x y : M} (hx : iVF x) (hy : iVF y)
    (hx0 : x ≠ iVFZero) (hy0 : y ≠ iVFZero) (h : ¬ Cls (iRv x) (iRv y)) :
    iVFAdd x y ≠ iVFZero := by
  have hxr : iRV (iRv x) := rv_mem hM hx
  have hyr : iRV (iRv y) := rv_mem hM hy
  have hcls : Cls (iRv (iVFAdd x y)) (iRv x) ∨ Cls (iRv (iVFAdd x y)) (iRv y) := by
    rcases le_total_rv hM hxr hyr with h1 | h1
    · have h2 : ¬ iLe (iRv y) (iRv x) := fun h2 => h ⟨h1, h2⟩
      exact Or.inl (rv_add_of_lt hM hx hy h1 h2)
    · have h2 : ¬ iLe (iRv x) (iRv y) := fun h2 => h ⟨h2, h1⟩
      have hc := rv_add_of_lt hM hy hx h1 h2
      rw [← vf_add_comm hM hx hy] at hc
      exact Or.inr hc
  intro heq
  have hz : iRv (iVFAdd x y) = iRVZero := by rw [heq, rv_zero_eq hM]
  rcases hcls with hc | hc
  · rw [hz] at hc
    exact hx0 (vf_eq_zero_of_rv_eq_zero hM hx (le_infty_eq hM hxr hc.1))
  · rw [hz] at hc
    exact hy0 (vf_eq_zero_of_rv_eq_zero hM hy (le_infty_eq hM hyr hc.1))

/-! ## 5. Partial sums of pairwise-distinct classes never vanish -/

/-- **The zero-free partial sums, with the minimal term.**  If every term of `f` is nonzero
(`hfne`) and the terms have pairwise distinct `Γ`-classes (`hdis`), then for every `n > 0` the
partial sum `f 0 + ⋯ + f (n-1)` has the class of some term `f j` that is minimal among
`f 0, …, f (n-1)`; in particular the partial sum is nonzero. -/
theorem vsum_exists_min (hM : M ⊨ Axioms.ACVF) {f : ℕ → M}
    (hf : ∀ i, iVF (f i)) (hfne : ∀ i, f i ≠ iVFZero)
    (hdis : ∀ i j, i ≠ j → ¬ Cls (iRv (f i)) (iRv (f j))) :
    ∀ n, 0 < n → ∃ j, j < n ∧ Cls (iRv (vsum f n)) (iRv (f j)) ∧
      ∀ i, i < n → iLe (iRv (f j)) (iRv (f i)) := by
  intro n
  induction n with
  | zero => intro h; exact absurd h (Nat.lt_irrefl 0)
  | succ k ih =>
    rcases k with _ | k
    · intro _
      refine ⟨0, by omega, ?_, ?_⟩
      · have h1 : vsum f 1 = f 0 := by
          show iVFAdd (iVFZero (M := M)) (f 0) = f 0
          exact vf_zero_add hM (hf 0)
        rw [h1]
        exact cls_refl hM (rv_mem hM (hf 0))
      · intro i hi
        have hi0 : i = 0 := by omega
        subst hi0
        exact le_refl_rv hM (rv_mem hM (hf 0))
    · intro _
      obtain ⟨j, hjk, hcls, hmin⟩ := ih (Nat.succ_pos k)
      have hsv : iVF (vsum f (k + 1)) := iVF_vsum hM hf (k + 1)
      have hb : iVF (f (k + 1)) := hf (k + 1)
      have hsvr : iRV (iRv (vsum f (k + 1))) := rv_mem hM hsv
      have hbr : iRV (iRv (f (k + 1))) := rv_mem hM hb
      have hjr : iRV (iRv (f j)) := rv_mem hM (hf j)
      -- the sum of the first `k+1` terms is nonzero
      have hs0 : vsum f (k + 1) ≠ iVFZero := by
        intro heq
        have hrv : iRv (vsum f (k + 1)) = iRVZero := by rw [heq, rv_zero_eq hM]
        rw [hrv] at hcls
        exact hfne j (vf_eq_zero_of_rv_eq_zero hM (hf j) (le_infty_eq hM hjr hcls.1))
      -- so its class differs from the class of the next term
      have hnc : ¬ Cls (iRv (vsum f (k + 1))) (iRv (f (k + 1))) := by
        intro hc
        exact hdis j (k + 1) (by omega)
          (cls_trans hM hjr hsvr hbr ⟨hcls.2, hcls.1⟩ hc)
      have hstep : vsum f (k + 2) = iVFAdd (vsum f (k + 1)) (f (k + 1)) := rfl
      rcases le_total_rv hM hsvr hbr with h1 | h1
      · have hlt : ¬ iLe (iRv (f (k + 1))) (iRv (vsum f (k + 1))) := fun h2 => hnc ⟨h1, h2⟩
        have hcr := rv_add_of_lt hM hsv hb h1 hlt
        refine ⟨j, by omega, ?_, ?_⟩
        · exact cls_trans hM (rv_mem hM (iVF_vsum hM hf (k + 2))) hsvr hjr hcr hcls
        · intro i hi
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | hieq
          · exact hmin i hi'
          · rw [hieq]
            exact le_trans_rv hM hjr hsvr hbr hcls.2 h1
      · have hlt : ¬ iLe (iRv (vsum f (k + 1))) (iRv (f (k + 1))) := fun h2 => hnc ⟨h2, h1⟩
        have hcr := rv_add_of_lt hM hb hsv h1 hlt
        have hclsb : Cls (iRv (vsum f (k + 2))) (iRv (f (k + 1))) := by
          rw [hstep, vf_add_comm hM hsv hb]
          exact hcr
        refine ⟨k + 1, by omega, hclsb, ?_⟩
        · intro i hi
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | hieq
          · exact le_trans_rv hM hbr hsvr (rv_mem hM (hf i)) h1
              (le_trans_rv hM hsvr hjr (rv_mem hM (hf i)) hcls.1 (hmin i hi'))
          · rw [hieq]
            exact le_refl_rv hM hbr

/-- **`hvnz` discharged**: under pairwise distinct classes of *nonzero* terms, every nonempty
partial sum is nonzero. -/
theorem vsum_ne_zero_of_pairwise_distinct (hM : M ⊨ Axioms.ACVF) {f : ℕ → M}
    (hf : ∀ i, iVF (f i)) (hfne : ∀ i, f i ≠ iVFZero)
    (hdis : ∀ i j, i ≠ j → ¬ Cls (iRv (f i)) (iRv (f j))) :
    ∀ k, 0 < k → vsum f k ≠ iVFZero := by
  intro k hk heq
  obtain ⟨j, _hjk, hcls, _hmin⟩ := vsum_exists_min hM hf hfne hdis k hk
  have hrv : iRv (vsum f k) = iRVZero := by rw [heq, rv_zero_eq hM]
  rw [hrv] at hcls
  exact hfne j (vf_eq_zero_of_rv_eq_zero hM (hf j)
    (le_infty_eq hM (rv_mem hM (hf j)) hcls.1))

/-! ## 6. Lemma 3.7 without `hvnz` -/

/-- **Lemma 3.7 (`e:transc`) of arXiv:1006.2467 in the frozen tagged encoding, `hvnz` removed.**
Compared with `Transc.e_transc`, the awkward hypothesis "every partial sum is nonzero" is replaced
by the primitive "every term is nonzero". -/
theorem e_transc' (hM : M ⊨ Axioms.ACVF) {e : M} {b : ℕ → M}
    (hbe : ∀ i, iVF (iVFMul (b i) (vpow e i)))
    (hdis : ∀ i j, i ≠ j →
      ¬ Cls (iRv (iVFMul (b i) (vpow e i))) (iRv (iVFMul (b j) (vpow e j))))
    (hfne : ∀ i, iVFMul (b i) (vpow e i) ≠ iVFZero)
    {m : ℕ}
    (hne : vsum (fun i => iVFMul (b i) (vpow e i)) (m + 1) ≠ iVFZero) :
    ∃ j, j ≤ m ∧
      Cls (iRv (vsum (fun i => iVFMul (b i) (vpow e i)) (m + 1)))
        (iRv (iVFMul (b j) (vpow e j))) ∧
      ∀ i, i ≤ m →
        iLe (iRv (iVFMul (b j) (vpow e j))) (iRv (iVFMul (b i) (vpow e i))) :=
  e_transc hM hbe hdis (vsum_ne_zero_of_pairwise_distinct hM hbe hfne hdis) hne


/-! ## 3-4. `hdis` from the `\u0393(Ŝ)`-hypothesis -/

/-! ## 1. `iRv` of a monomial -/

theorem rv_monomial (hM : M ⊨ Axioms.ACVF) {e : M} (he : iVF e) {b : ℕ → M}
    (hb : ∀ i, iVF (b i)) (i : ℕ) :
    iRv (iVFMul (b i) (vpow e i)) = iRVMul (iRv (b i)) (rvpow (iRv e) i) := by
  rw [rv_mul_hom_of_model hM (hb i) (iVF_vpow hM he i), rv_vpow hM he i]

/-! ## 2. `VF` is a domain and powers of a nonzero element are nonzero -/

/-- `VF` has no zero divisors. -/
theorem vf_mul_ne_zero (hM : M ⊨ Axioms.ACVF) {x y : M} (hx : iVF x) (hy : iVF y)
    (hx0 : x ≠ iVFZero) (hy0 : y ≠ iVFZero) : iVFMul x y ≠ iVFZero := by
  intro h
  have hxr : iRv x ≠ iRVZero := fun h0 => hx0 (vf_eq_zero_of_rv_eq_zero hM hx h0)
  have hyr : iRv y ≠ iRVZero := fun h0 => hy0 (vf_eq_zero_of_rv_eq_zero hM hy h0)
  have h1 : iRVMul (iRv x) (iRv y) = iRVZero := by
    rw [← rv_mul_hom_of_model hM hx hy, h, rv_zero_eq hM]
  exact rv_mul_ne_zero hM (rv_mem hM hx) (rv_mem hM hy) hxr hyr h1

/-- Powers of a nonzero `VF`-element are nonzero. -/
theorem vpow_ne_zero (hM : M ⊨ Axioms.ACVF) {e : M} (he : iVF e) (he0 : e ≠ iVFZero) :
    ∀ n, vpow e n ≠ iVFZero
  | 0 => fun h => vf_zero_ne_one hM h.symm
  | (n + 1) => vf_mul_ne_zero hM (iVF_vpow hM he n) he (vpow_ne_zero hM he he0 n) he0

/-! ## 3. `hdis` from the `Γ(Ŝ)`-hypothesis -/

/-- **The cancellation core.**  If `i < j` and `vv(e)` has no positive power in `G`, then the terms
`b i * e ^ i` and `b j * e ^ j` have different `Γ`-classes. -/
theorem hdis_of_lt (hM : M ⊨ Axioms.ACVF) {e : M} (he : iVF e) (he0 : iRv e ≠ iRVZero)
    {b : ℕ → M} (hb : ∀ i, iVF (b i)) {G : M → Prop}
    (hGmem : ∀ x, G x → iRV x)
    (hGmul : ∀ x y, G x → G y → G (iRVMul x y))
    (hGinv : ∀ x, G x → ∃ y, G y ∧ Cls (iRVMul x y) iRVOne)
    (hGb : ∀ i, G (iRv (b i)))
    (hpow : ∀ k, 0 < k → ∀ x, G x → ¬ Cls (rvpow (iRv e) k) x)
    {i j : ℕ} (hij : i < j) :
    ¬ Cls (iRVMul (iRv (b i)) (rvpow (iRv e) i))
        (iRVMul (iRv (b j)) (rvpow (iRv e) j)) := by
  intro hc
  have hε : iRV (iRv e) := rv_mem hM he
  have hγ : ∀ n, iRV (iRv (b n)) := fun n => rv_mem hM (hb n)
  have hεi : iRV (rvpow (iRv e) i) := iRV_rvpow hM hε i
  have hεk0 : ∀ k, iRV (rvpow (iRv e) k) := fun k => iRV_rvpow hM hε k
  obtain ⟨k, hk⟩ : ∃ k, j = i + k := ⟨j - i, by omega⟩
  have hkpos : 0 < k := by omega
  rw [hk, rvpow_add hM hε i k] at hc
  -- move the `e^i` factor to the right on the second term
  have hswap : iRVMul (iRv (b (i + k))) (iRVMul (rvpow (iRv e) i) (rvpow (iRv e) k))
      = iRVMul (iRVMul (iRv (b (i + k))) (rvpow (iRv e) k)) (rvpow (iRv e) i) := by
    rw [rv_mul_comm_of_model hM hεi (hεk0 k),
      ← rv_mul_assoc_of_model hM (hγ (i + k)) (hεk0 k) hεi]
  rw [hswap] at hc
  -- cancel `e^i`
  have hck : iRV (iRVMul (iRv (b (i + k))) (rvpow (iRv e) k)) :=
    rv_mul_mem hM (hγ (i + k)) (hεk0 k)
  have hc' : Cls (iRv (b i)) (iRVMul (iRv (b (i + k))) (rvpow (iRv e) k)) :=
    (cls_mul_iff hM (hγ i) hck hεi (rvpow_ne_zero hM hε he0 i)).mp hc
  -- multiply by a class-inverse of `rv (b i)`
  obtain ⟨δ, hδG, hδ⟩ := hGinv (iRv (b i)) (hGb i)
  have hδm : iRV δ := hGmem δ hδG
  have h1 : Cls (iRVMul (iRv (b i)) δ)
      (iRVMul (iRVMul (iRv (b (i + k))) (rvpow (iRv e) k)) δ) :=
    cls_mul_right hM (hγ i) hck hδm hc'
  have h2 : Cls (iRVMul (iRVMul (iRv (b (i + k))) (rvpow (iRv e) k)) δ) iRVOne :=
    cls_trans hM (rv_mul_mem hM hck hδm) (rv_mul_mem hM (hγ i) hδm) (rv_one_mem hM)
      (cls_symm h1) hδ
  -- regroup: `(rv b_{i+k} * e^k) * δ = e^k * g` with `g = rv b_{i+k} * δ ∈ G`
  have hgg : iRVMul (iRVMul (iRv (b (i + k))) (rvpow (iRv e) k)) δ
      = iRVMul (rvpow (iRv e) k) (iRVMul (iRv (b (i + k))) δ) := by
    rw [rv_mul_assoc_of_model hM (hγ (i + k)) (hεk0 k) hδm,
      rv_mul_comm_of_model hM (hεk0 k) hδm,
      ← rv_mul_assoc_of_model hM (hγ (i + k)) hδm (hεk0 k),
      rv_mul_comm_of_model hM (rv_mul_mem hM (hγ (i + k)) hδm) (hεk0 k)]
  have h3 : Cls (iRVMul (rvpow (iRv e) k) (iRVMul (iRv (b (i + k))) δ)) iRVOne := by
    rw [← hgg]; exact h2
  -- the class-inverse `g'` of `g`
  have hgG : G (iRVMul (iRv (b (i + k))) δ) := hGmul _ _ (hGb (i + k)) hδG
  have hgm : iRV (iRVMul (iRv (b (i + k))) δ) := hGmem _ hgG
  obtain ⟨g', hg'G, hgg'⟩ := hGinv (iRVMul (iRv (b (i + k))) δ) hgG
  have hg'm : iRV g' := hGmem g' hg'G
  -- multiply `h3` by `g'`
  have h4 : Cls (iRVMul (iRVMul (rvpow (iRv e) k) (iRVMul (iRv (b (i + k))) δ)) g')
      (iRVMul iRVOne g') :=
    cls_mul_right hM (rv_mul_mem hM (hεk0 k) hgm) (rv_one_mem hM) hg'm h3
  rw [rv_mul_one_any hM hg'm] at h4
  -- multiply `g * g' ~ 1` by `e^k`
  have h5 : Cls (iRVMul (iRVMul (iRVMul (iRv (b (i + k))) δ) g') (rvpow (iRv e) k))
      (iRVMul iRVOne (rvpow (iRv e) k)) :=
    cls_mul_right hM (rv_mul_mem hM hgm hg'm) (rv_one_mem hM) (hεk0 k) hgg'
  rw [rv_mul_one_any hM (hεk0 k)] at h5
  -- the two products are the same element
  have h6 : iRVMul (iRVMul (rvpow (iRv e) k) (iRVMul (iRv (b (i + k))) δ)) g'
      = iRVMul (iRVMul (iRVMul (iRv (b (i + k))) δ) g') (rvpow (iRv e) k) := by
    rw [rv_mul_assoc_of_model hM (hεk0 k) hgm hg'm,
      rv_mul_comm_of_model hM (hεk0 k) (rv_mul_mem hM hgm hg'm)]
  have h5X : Cls (iRVMul (iRVMul (rvpow (iRv e) k) (iRVMul (iRv (b (i + k))) δ)) g')
      (rvpow (iRv e) k) := by
    rw [h6]; exact h5
  exact hpow k hkpos g' hg'G
    (cls_trans hM (hεk0 k) (rv_mul_mem hM (rv_mul_mem hM (hεk0 k) hgm) hg'm) hg'm
      (cls_symm h5X) h4)

/-- **`hdis` from the paper's `Γ(Ŝ)`-hypothesis**: the monomials `b i * e ^ i` have pairwise
distinct `Γ`-classes. -/
theorem hdis_of_gamma (hM : M ⊨ Axioms.ACVF) {e : M} (he : iVF e) (he0 : iRv e ≠ iRVZero)
    {b : ℕ → M} (hb : ∀ i, iVF (b i)) {G : M → Prop}
    (hGmem : ∀ x, G x → iRV x)
    (hGmul : ∀ x y, G x → G y → G (iRVMul x y))
    (hGinv : ∀ x, G x → ∃ y, G y ∧ Cls (iRVMul x y) iRVOne)
    (hGb : ∀ i, G (iRv (b i)))
    (hpow : ∀ k, 0 < k → ∀ x, G x → ¬ Cls (rvpow (iRv e) k) x) :
    ∀ i j, i ≠ j →
      ¬ Cls (iRv (iVFMul (b i) (vpow e i))) (iRv (iVFMul (b j) (vpow e j))) := by
  intro i j hij hc
  rw [rv_monomial hM he hb i, rv_monomial hM he hb j] at hc
  rcases Nat.lt_or_gt_of_ne hij with hlt | hgt
  · exact hdis_of_lt hM he he0 hb hGmem hGmul hGinv hGb hpow hlt hc
  · exact hdis_of_lt hM he he0 hb hGmem hGmul hGinv hGb hpow hgt (cls_symm hc)

/-! ## 4. Lemma 3.7 with the paper's hypotheses -/

/-- **Lemma 3.7 (`e:transc`) of arXiv:1006.2467 in the frozen tagged encoding, with the paper's
hypotheses only**: `e ≠ 0` with `vv(e)` of infinite order modulo the class set `G` of `Γ(Ŝ)`
(`hpow`), nonzero coefficients `b i` in `G` (`hb0`, `hGb`), and `b = ∑ b i e^i ≠ 0` (`hne`).
No `hdis`, no `hvnz`: both are derived. -/
theorem e_transc_of_gamma (hM : M ⊨ Axioms.ACVF) {e : M} (he : iVF e) (he0 : e ≠ iVFZero)
    {b : ℕ → M} (hb : ∀ i, iVF (b i)) (hb0 : ∀ i, b i ≠ iVFZero) {G : M → Prop}
    (hGmem : ∀ x, G x → iRV x)
    (hGmul : ∀ x y, G x → G y → G (iRVMul x y))
    (hGinv : ∀ x, G x → ∃ y, G y ∧ Cls (iRVMul x y) iRVOne)
    (hGb : ∀ i, G (iRv (b i)))
    (hpow : ∀ k, 0 < k → ∀ x, G x → ¬ Cls (rvpow (iRv e) k) x)
    {m : ℕ}
    (hne : vsum (fun i => iVFMul (b i) (vpow e i)) (m + 1) ≠ iVFZero) :
    ∃ j, j ≤ m ∧
      Cls (iRv (vsum (fun i => iVFMul (b i) (vpow e i)) (m + 1)))
        (iRv (iVFMul (b j) (vpow e j))) ∧
      ∀ i, i ≤ m →
        iLe (iRv (iVFMul (b j) (vpow e j))) (iRv (iVFMul (b i) (vpow e i))) := by
  have he' : iRv e ≠ iRVZero := fun h => he0 (vf_eq_zero_of_rv_eq_zero hM he h)
  exact e_transc' hM (fun i => vf_mul_mem (M := M) hM (hb i) (iVF_vpow hM he i))
    (hdis_of_gamma hM he he' hb hGmem hGmul hGinv hGb hpow)
    (fun i => vf_mul_ne_zero hM (hb i) (iVF_vpow hM he i) (hb0 i) (vpow_ne_zero hM he he0 i))
    hne

/-! ## 5. Axiom audit -/

end Transc
end SpecialTransformations.Milestone0

#print axioms SpecialTransformations.Milestone0.Transc.e_transc
#print axioms SpecialTransformations.Milestone0.Transc.vsum_ne_zero_of_pairwise_distinct
#print axioms SpecialTransformations.Milestone0.Transc.e_transc'
#print axioms SpecialTransformations.Milestone0.Transc.hdis_of_lt
#print axioms SpecialTransformations.Milestone0.Transc.hdis_of_gamma
#print axioms SpecialTransformations.Milestone0.Transc.e_transc_of_gamma
