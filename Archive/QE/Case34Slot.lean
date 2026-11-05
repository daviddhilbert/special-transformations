/-
# p1 — the exact slot statement of Lemma 3.4 (`lift:all:root`), and where it belongs

Member `m1`, swarm `smw2mluv7`.  Paper: Yin, *Special transformations in ACVF*, `qe.tex`;
`lift:all:root` is the lemma at `qe.tex:613-631`.

    Let `F(X) = X^n + Σ_{0 ≤ i < n} a_i X^i ∈ O(Ŝ)[X]` such that its projection `F̄(X)` to
    `K(Ŝ)[X]` is irreducible.  Suppose that `e ∈ U(M)` and is a root of `F(X)`.  If the valued
    field `(VF(Ŝ), O(Ŝ))` is henselian, then Claim (⋆) holds.

Claim (⋆) (`qe.tex:606-611`) is: `RV(⟨Ŝ,e⟩) = ⟨RV(Ŝ), rv(e)⟩ ⊆ RV(S)` **and** the monomorphism
`f ↾ Ŝ` extends to `f^* : ⟨Ŝ,e⟩ → N` with `f^*(rv e) = f(rv e)`.

## What this file establishes

**§1 — a correction to the case bookkeeping (machine-checked).**  `QE/OneStepCases.lean` attributes
Lemma 3.4 to the `CaseSeparated` slot ("`vv(m^k) ∉ Γ(Ŝ)` for `k > 0` — Lemma 3.4 / Lemma 3.6").  That
attribution is **false**: `e ∈ U(M)` means `v(e) = 0`, so `vv(e^k) = 0 ∈ Γ(Ŝ)` for every `k > 0`, and
with `x = y = 1` in `M5L.Separated S e` the clause at `k = 1` fails outright.  Machine-checked:

* `separated_imp_pow_not_cls_one` — `Separated S m` forces *every* positive power of `rv m` to have
  a class different from `1` (i.e. `vv(m)` has infinite order modulo the units, exactly the paper's
  `vv(e^k) ∉ Γ(Ŝ)`);
* `not_separated_of_units` — hence a unit of the valuation ring is **never** separated;
* `not_separated_top` — `Separated ⊤ m` fails at *every* nonzero `VF` element.

Consequence for the ledger: Lemma 3.4's case is a case of `M4Cases.CaseNotSeparated`, and the
not-separated slot has to cover the *unit* case — `M5L34_36`'s `m^n = a` analysis (and
`QE/OneStepCases.lean`'s description of `CaseNotSeparated` as "Lemma 3.5") does not.

**§2 — the exact slot statement.**  `LiftAllRoot S f a n m` is Lemma 3.4's hypothesis list at a fixed
pair `M, N ⊨ ACVF`, with `F` given by its coefficient function `a : ℕ → M` (`MonicO`), `e = m` a
root of `F` (`IsRootOf`, via `M7Hens.vfEval`), `e ∈ U(M)` (`iUnits (iRv m)`), `(VF(Ŝ),O(Ŝ))`
henselian (`M7Hens.IsHenselianVF S`), plus the three facts the paper's *proof* derives and the
tagged encoding cannot derive itself (`root_lift`, `embed`, `class_control` — see the docstring for
why each is irreducible here).

**§3 — the reduction.**  `slot_of_liftAllRoot`: the paper's Claim (⋆) at `e` gives the slot
conclusion `∃ T g, S ≤ T ∧ g ↾ S = f ∧ m ∈ T ∧ Standing T` — with `T = ⟨Ŝ,e⟩` the encoding's
closure and `Standing T` supplied by `M5L.standing_of_ClassControl` (so the *only* `Standing`
content is the class computation, i.e. the paper's `RV(⟨Ŝ,e⟩) ⊆ RV(S)`).

**§4 — stress tests.**  (a) `MonicO`/`IsRootOf` are inhabited (`F = X - 1`, `e = 1`) and that
instance is not separated, so §1 bites at the simplest 3.4 datum; (b) the slot conclusion is
satisfiable at every point where the monomorphism extends to `M ↪[LRV] N` (`T = ⊤`), so the
statement is not contradictory and carries no cardinality conjunct of its own.

No `sorry`, no `axiom`, no `native_decide`; axiom audit at the end.
-/
import M5L34_36
import Lemma32_at_model
import M7Hensel
import OneStepCases
import GammaGroup

set_option autoImplicit false
set_option linter.unusedSectionVars false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
open SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transc
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Milestone0.RVCalc

namespace SpecialTransformations.Milestone0
namespace M5P1

variable {M N : Type} [LRV.Structure M] [LRV.Structure N]
variable [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]

/-! ## 0. Two bookkeeping lemmas -/

/-- `1` of the `VF` sort lies in every substructure (it is a constant symbol). -/
theorem vfOne_mem_sub (S : LRV.Substructure M) : iVFOne (M := M) ∈ S :=
  S.fun_mem Fn.vfOne (fun i => i.elim0) (fun i => i.elim0)

/-- The first `RV` power of `ε` is `1 · ε`, definitionally. -/
theorem rvpow_one (ε : M) : rvpow ε 1 = iRVMul iRVOne ε := rfl

/-! ## 1. `U(M)` and the separation hypothesis are disjoint

`e ∈ U(M)` is, in the encoding's vocabulary, `iVF e ∧ iUnits (iRv e)`: `rv` of a unit of the
valuation ring lies in the residue field's unit group `Kˣ`, i.e. in the class of `1`
(`RVCalc.units_iff_le_one`).  The paper's separation hypothesis is `vv(e^k) ∉ Γ(Ŝ)` for `k > 0`;
for a unit every `vv(e^k)` is `0 = vv(1) ∈ Γ(Ŝ)`.  Lemma 3.4 is therefore *not* a separated case. -/

/-- **Necessary condition for `M5L.Separated`, read off `x = y = 1`**: no positive power of `rv m`
may have the class of `1`, i.e. `vv(m)` must have infinite order modulo the units of `Ŝ` — the
paper's `vv(e^k) ∉ Γ(Ŝ)` (`qe.tex:633`, `741`), with `Γ(Ŝ)` read as the classes of `S ∩ VF^×`. -/
theorem separated_imp_pow_not_cls_one {S : LRV.Substructure M} {m : M} (hmVF : iVF m)
    (hsep : M5L.Separated S m) :
    ∀ k : ℕ, 0 < k → ¬ Transc.Cls (rvpow (iRv m) k) iRVOne := by
  intro k hk hc
  have h1S : iVFOne (M := M) ∈ S := vfOne_mem_sub S
  have h1VF : iVF (iVFOne (M := M)) := vf_one_mem (M := M) hM
  have h10 : iVFOne (M := M) ≠ iVFZero (M := M) := (RVCalc.vf_zero_ne_one (M := M) hM).symm
  have h := hsep k hk (iVFOne (M := M)) (iVFOne (M := M)) h1VF h1VF h1S h1S h10 h10
  apply h
  rw [rv_one hM, rv_mul_one_any_right hM (iRV_rvpow hM (rv_mem hM hmVF) k)]
  exact hc

/-- **Lemma 3.4's hypothesis `e ∈ U(M)` refutes `M5L.Separated`** (see the module docstring).  In the
paper's notation: `e ∈ U(M)` gives `vv(e) = 0`, and `0 = vv(1) ∈ Γ(Ŝ)` because `1 ∈ Ŝ`, so the
separation hypothesis of Lemmas 3.5/3.6 fails at `k = 1`. -/
theorem not_separated_of_units {S : LRV.Substructure M} {m : M} (hmVF : iVF m)
    (hmU : iUnits (iRv m)) : ¬ M5L.Separated S m := by
  intro hsep
  have hrv : iRV (iRv m) := rv_mem hM hmVF
  have hrv0 : iRv m ≠ iRVZero := GammaGroup.units_ne_zero hmU
  have hunit : iLe iRVOne (iRv m) ∧ iLe (iRv m) iRVOne :=
    (units_iff_le_one hM hrv hrv0).mp hmU
  refine separated_imp_pow_not_cls_one hmVF hsep 1 (by norm_num) ?_
  rw [rvpow_one, rv_mul_one_any hM hrv]
  exact ⟨hunit.2, hunit.1⟩

/-- `e ∈ U(M)` also puts `rv e` in every `KEqTop` substructure — the paper's `K(S) = K(M)` — so
Lemma 3.4's data does satisfy the slot's own hypothesis `iRv m ∈ S`. -/
theorem rv_mem_of_units {S : LRV.Substructure M} (hK : Assembly.KEqTop S) {m : M}
    (hmU : iUnits (iRv m)) : iRv m ∈ S :=
  hK _ hmU

/-- **The paper's separation condition implies `M5L.Separated`, given `VFInvClosedOn`.**  The
paper's hypothesis (`qe.tex:633, 741`) is `vv(m^k) ∉ Γ(Ŝ)`, i.e. *no* class of an element of
`S ∩ VF^×` equals `vv(m^k)` — the hypothesis of `h` below.  The tree's `M5L.Separated` is the *ratio*
form (the encoding has no class-inverse, so it compares `(rv m)^k · rv x` against `rv y`); the
implication is exactly where `M5L.VFInvClosedOn S` — the paper's `VF(S)` being a field — is consumed:
it supplies the class of `x⁻¹`, which cancels `rv x` from the ratio.  Together with
`separated_imp_pow_not_cls_one` (the converse, which needs nothing) this pins the tree's hypothesis
as the paper's condition. -/
theorem separated_of_pow_notin {S : LRV.Substructure M} {m : M} (hmVF : iVF m)
    (hfinv : M5L.VFInvClosedOn S)
    (h : ∀ k : ℕ, 0 < k → ∀ s : M, s ∈ S → iRV s → ¬ Transc.Cls (rvpow (iRv m) k) s) :
    M5L.Separated S m := by
  intro k hk x y hxVF hyVF hxS hyS hx0 hy0 hcls
  have hxrv : iRv x ∈ S := M5L.rv_mem_sub S hxS
  obtain ⟨x', hx'VF, hx'RV, hxx'⟩ := hfinv x hxVF hxrv hx0
  have hxrv0 : iRv x ≠ iRVZero := fun hz => hx0 (vf_eq_zero_of_rv_eq_zero hM hxVF hz)
  have hε : iRV (rvpow (iRv m) k) := iRV_rvpow hM (rv_mem hM hmVF) k
  have hxRV : iRV (iRv x) := rv_mem hM hxVF
  have hyRV : iRV (iRv y) := rv_mem hM hyVF
  have hx'RVr : iRV (iRv x') := rv_mem hM hx'VF
  have hx'inv : iRVMul (iRv x) (iRv x') = iRVOne := by
    rw [← rv_mul_hom_of_model hM hxVF hx'VF, hxx', rv_one hM]
  have hy_eq : iRv y = iRVMul (iRVMul (iRv y) (iRv x')) (iRv x) := by
    rw [rv_mul_assoc_of_model hM hyRV hx'RVr hxRV,
      rv_mul_comm_of_model hM hx'RVr hxRV, hx'inv, rv_mul_one_any_right hM hyRV]
  have hcls' : Transc.Cls (iRVMul (rvpow (iRv m) k) (iRv x))
      (iRVMul (iRVMul (iRv y) (iRv x')) (iRv x)) := by
    rw [← hy_eq]
    exact hcls
  exact h k hk (iRVMul (iRv y) (iRv x')) (M5L.rvMul_mem_sub S (M5L.rv_mem_sub S hyS) hx'RV)
    (rv_mul_mem hM hyRV hx'RVr)
    ((Transc.cls_mul_iff hM hε (rv_mul_mem hM hyRV hx'RVr) hxRV hxrv0).mp hcls')

/-- **`Separated` fails even at `S = ⊤`**: with `x = 1` and `y = m`, the class of `m^1 · 1` is the
class of `rv m` itself.  So `CaseSeparated` can only ever fire at proper substructures, and the
separated hypothesis is a genuine restriction on `vv(m)` rather than a bookkeeping device. -/
theorem not_separated_top {m : M} (hmVF : iVF m) (hm0 : m ≠ iVFZero) :
    ¬ M5L.Separated (⊤ : LRV.Substructure M) m := by
  intro hsep
  have hrv : iRV (iRv m) := rv_mem hM hmVF
  have h1VF : iVF (iVFOne (M := M)) := vf_one_mem (M := M) hM
  have h := hsep 1 (by norm_num) (iVFOne (M := M)) m h1VF hmVF (by trivial) (by trivial)
    ((RVCalc.vf_zero_ne_one (M := M) hM).symm) hm0
  apply h
  rw [rvpow_one, rv_one hM, rv_mul_one_any hM hrv, rv_mul_one_any_right hM hrv]
  exact Transc.cls_refl hM hrv

/-! ### 1b. The corrected attribution of the paper's case lemmas

The paper's four case lemmas at `rv e ∈ RV(S) \ RV(Ŝ)` (`qe.tex` labels; the tree's numbering of the
first three is 3.4/3.5/3.6) have these hypotheses:

* `lift:all:root`      (l. 613) — `e ∈ U(M)`, `e` a root of a monic `F` over `O(Ŝ)`;
* `lift:divisible:hull` (l. 633) — `e ∉ U(M)`, `e^n = a ∈ VF(Ŝ)`, `vv(e^i) ∉ Γ(Ŝ)` for `0<i<n`;
* `lift:transcendental` (l. 732) — `e ∈ U(M)`, `rv e` transcendental over `K(Ŝ)`;
* `e:transc`           (l. 790) — `e` transcendental over `VF(Ŝ)`, `vv(e)` of infinite order mod `Γ(Ŝ)`.

`not_separated_of_units` kills the separation hypothesis for the first **and third**: both have
`e ∈ U(M)`.  The fourth is the only one whose hypothesis *is* the tree's `M5L.Separated S e`
(up to the `VFInvClosedOn`-form of `Γ(Ŝ)`).  So the ledger's slots correspond as

    `M4Cases.CaseSeparated`    ⟷  `e:transc` (Lemma 3.7 of the tree's numbering)
    `M4Cases.CaseNotSeparated` ⟷  `lift:all:root` ∪ `lift:divisible:hull` ∪ `lift:transcendental`

and `QE/OneStepCases.lean`'s "separated — Lemmas 3.4/3.6", "not separated — Lemma 3.5" is rotated.
`lift:transcendental`'s hypotheses are `iVF e ∧ iUnits (iRv e)` plus transcendence, so: -/

/-- **Lemma 3.6 (`lift:transcendental`) is a `¬ Separated` case**: its hypothesis `e ∈ U(M)` already
refutes `M5L.Separated` (`not_separated_of_units`); the transcendence of `rv e` is not needed for
this, only for the `RV`-computation inside the proof. -/
theorem liftTranscendental_not_separated {S : LRV.Substructure M} {m : M} (hmVF : iVF m)
    (hmU : iUnits (iRv m)) : ¬ M5L.Separated S m :=
  not_separated_of_units hmVF hmU

/-- **`CaseNotSeparated` is the union of the unit half (Lemmas 3.4/3.6) and the non-unit half
(Lemma 3.5)** — machine-checked splitting of the slot, so that a proof covering only the non-unit
configurations (the `m^n = a` analysis) is visibly incomplete. -/
theorem caseNotSeparated_iff_unit_and_nonunit :
    M4Cases.CaseNotSeparated (M := M) (N := N) ↔
      ((∀ (S : LRV.Substructure M) (f : S ↪[LRV] N), Assembly.Standing S → ∀ m : M, iVF m →
          iRv m ∈ S → iUnits (iRv m) → ¬ M5L.Separated S m →
          ∃ (T : LRV.Substructure M) (g : T ↪[LRV] N) (hST : S ≤ T),
            (∀ x : S, g ⟨(x : M), hST x.2⟩ = f x) ∧ m ∈ T ∧ Assembly.Standing T) ∧
       (∀ (S : LRV.Substructure M) (f : S ↪[LRV] N), Assembly.Standing S → ∀ m : M, iVF m →
          iRv m ∈ S → ¬ iUnits (iRv m) → ¬ M5L.Separated S m →
          ∃ (T : LRV.Substructure M) (g : T ↪[LRV] N) (hST : S ≤ T),
            (∀ x : S, g ⟨(x : M), hST x.2⟩ = f x) ∧ m ∈ T ∧ Assembly.Standing T)) := by
  constructor
  · intro h
    constructor
    · intro S f hS m hmVF hmrv hunit hns; exact h S f hS m hmVF hmrv hns
    · intro S f hS m hmVF hmrv hunit hns; exact h S f hS m hmVF hmrv hns
  · intro ⟨hu, hnu⟩ S f hS m hmVF hmrv hns
    by_cases hunit : iUnits (iRv m)
    · exact hu S f hS m hmVF hmrv hunit hns
    · exact hnu S f hS m hmVF hmrv hunit hns

/-- **In the unit case `m`'s `Γ`-class is already a class of `S`** — `1` is a constant, hence in `S`,
and `iUnits` says the two are class-equal.  This is the precise sense in which Lemma 3.4 needs no
`Γ`-hull (contrast `M5.OneStepRVNew`): the `Γ`-side of 3.4 is not where the work is. -/
theorem unit_class_in_S {S : LRV.Substructure M} {m : M} (hmVF : iVF m) (hmU : iUnits (iRv m)) :
    ∃ s : M, s ∈ S ∧ iRV s ∧ Transc.Cls (iRv m) s := by
  have hrv : iRV (iRv m) := rv_mem hM hmVF
  have hunit : iLe iRVOne (iRv m) ∧ iLe (iRv m) iRVOne :=
    (units_iff_le_one hM hrv (GammaGroup.units_ne_zero hmU)).mp hmU
  exact ⟨iRVOne, M5L.rvOne_mem_sub S, rv_one_mem (M := M) hM, ⟨hunit.2, hunit.1⟩⟩

/-! ## 2. The exact statement of Lemma 3.4's hypotheses at a fixed pair -/

/-- **`F(X) = Σ_{i≤n} a_i X^i ∈ O(Ŝ)[X]`, monic of degree `n ≥ 1`** — the polynomial of Lemma 3.4.
`O(Ŝ)` is the paper's valuation ring: coefficients lie in `S ∩ VF` and are integral
(`iLe 1 (rv (a i))`, i.e. `vv(a_i) ≥ 0`). -/
structure MonicO (S : LRV.Substructure M) (a : ℕ → M) (n : ℕ) : Prop where
  /-- the degree is positive (`X^n + …`) -/
  one_le : 1 ≤ n
  /-- all coefficients lie in `Ŝ` -/
  coeff_mem : ∀ i, i ≤ n → a i ∈ S
  /-- all coefficients lie in the `VF` sort -/
  coeff_vf : ∀ i, iVF (a i)
  /-- all coefficients are integral: they lie in `O(Ŝ)` -/
  coeff_int : ∀ i, i ≤ n → iLe iRVOne (iRv (a i))
  /-- `F` is monic -/
  monic : a n = iVFOne (M := M)
  /-- `F` has degree `n` -/
  deg_le : ∀ i, n < i → a i = iVFZero (M := M)

/-- **`m` is a root of `F = Σ_{i≤n} a_i X^i`**, in the `VF` sort (`M7Hens.vfEval`). -/
def IsRootOf (a : ℕ → M) (n : ℕ) (m : M) : Prop :=
  M7Hens.vfEval a n m = iVFZero (M := M)

/-- **Lemma 3.4's hypothesis list at a fixed pair, with the three facts its *proof* derives isolated
as named fields.**  The paper's hypotheses are `monic`, `unit`, `root`, `hensel`; the last three
fields are what the proof obtains from them, and each is irreducible in this repository:

* `root_lift` — the conclusion of Lemma 3.2 (`rv:root:lift:vf`) at the pair: `f(rv e)` is a root of
  `f(F̄)` because `rv e` is a root of `F̄` and `F̄` is irreducible, hence lifts to `d ∈ VF(N)` with
  `rv d = f(rv e)`.  Available at a *model* as `M5AtModel.rv_root_lift_at_model` (which is
  `YinRV.rv_root_lift_rv`, proved in `QE/Lemma32_root_lifting.lean`) once the encoding's `rv`-class
  hypothesis is translated into Lemma 3.2's `huniv`/`hred` pair; the translation is *not* done here.
* `embed` — the paper's second use of "`F̄` irreducible": `F` is irreducible over `VF(Ŝ)`, so with
  `(VF(Ŝ),O(Ŝ))` henselian the field isomorphism `VF(Ŝ)[X]/(F) → VF(Ŝ)(e)` sends `e ↦ d`, and
  henselianity makes the image valuation agree, giving a **valued** field embedding
  `⟨Ŝ,e⟩ → N` with `f^*(e) = d`; `qe.tex:622` then converts it to an `L_RV`-monomorphism.  Stated
  here directly as the `L_RV`-monomorphism of the encoding's closure `⟨Ŝ,e⟩`.
* `class_control` — Claim (⋆)'s `RV(⟨Ŝ,e⟩) = ⟨RV(Ŝ), rv e⟩ ⊆ RV(S)`, in the class form the frozen
  encoding consumes (`M5L.ResidualClasses`, cf. `M5L.ResidualClasses_of_VFGen`).  The paper gets it
  from the fundamental inequality `[K(⟨Ŝ,e⟩):K(Ŝ)] = [VF(⟨Ŝ,e⟩):VF(Ŝ)]`, which is not in Mathlib.

`e ∉ U(M)`-type hypotheses do not appear: Lemma 3.4 is the *unit* case (§1). -/
structure LiftAllRoot (S : LRV.Substructure M) (f : S ↪[LRV] N) (a : ℕ → M) (n : ℕ) (m : M) :
    Prop where
  /-- `F = X^n + Σ_{i<n} a_i X^i ∈ O(Ŝ)[X]` -/
  monic : MonicO S a n
  /-- `e ∈ U(M) ⊆ VF(M)`: a unit of the valuation ring -/
  vf : iVF m
  /-- `e ∈ U(M)`: its `rv`-class is a unit of the residue field -/
  unit : iUnits (iRv m)
  /-- `e` is a root of `F` -/
  root : IsRootOf a n m
  /-- `(VF(Ŝ), O(Ŝ))` is henselian -/
  hensel : M7Hens.IsHenselianVF S
  /-- `rv e ∈ S` — free in the paper's setting (`rv e ∈ Kˣ(M) ⊆ S` by `K(S) = K(M)`,
  `rv_mem_of_units`); recorded so that `f (rv e)` is meaningful -/
  rv_mem : iRv m ∈ S
  /-- **Lemma 3.2 at the pair**: the root of the projection lifts to `N` -/
  root_lift : ∃ (b : ℕ → N) (d : N), iVF d ∧ iRv d = f ⟨iRv m, rv_mem⟩ ∧
    (∀ (i : ℕ) (hi : i ≤ n), b i = f ⟨a i, monic.coeff_mem i hi⟩) ∧
    M7Hens.vfEval b n d = iVFZero (M := N)
  /-- **the henselianity step**: the valued field embedding `⟨Ŝ,e⟩ → N` with `e ↦ d`, as an
  `L_RV`-monomorphism of the encoding's `⟨Ŝ,e⟩ = closure (S ∪ {m})` -/
  embed : ∃ g : (Substructure.closure LRV ((S : Set M) ∪ {m})) ↪[LRV] N,
    ∀ x : S, g ⟨(x : M), Substructure.subset_closure (Or.inl x.2)⟩ = f x
  /-- **Claim (⋆)'s `RV` half** — `RV(⟨Ŝ,e⟩) ⊆ RV(S)` in class form -/
  class_control : M5L.ResidualClasses S (Substructure.closure LRV ((S : Set M) ∪ {m}))

/-! ## 3. Claim (⋆) ⟹ the slot conclusion

The only `Standing` content of the conclusion is `class_control`: `Standing T` is
`M5L.standing_of_ClassControl`, because `KEqTop` is monotone in the substructure and `Γ`'s
divisibility transfers along the class computation. -/

/-- **`Standing` of the paper's `⟨Ŝ,e⟩` from Claim (⋆)'s `RV` half.** -/
theorem standing_closure_of_classControl {S : LRV.Substructure M} {m : M}
    (hS : Assembly.Standing S) (hcc : M5L.ResidualClasses S (Substructure.closure LRV ((S : Set M) ∪ {m}))) :
    Assembly.Standing (Substructure.closure LRV ((S : Set M) ∪ {m})) :=
  M5L.standing_of_ClassControl
    (fun _ hx => Substructure.subset_closure (Or.inl hx)) hS hcc

/-- **Lemma 3.4 at a fixed pair `(M, N)`: Claim (⋆) gives the ledger's one-step conclusion.**
The extension is `T = ⟨Ŝ,e⟩ = closure (S ∪ {e})`, `m = e`; the monomorphism is `embed`, and
`Standing T` is `standing_closure_of_classControl`.  Note the *absence* of any `Separated`
hypothesis: by §1 there can be none at a unit `e`. -/
theorem slot_of_liftAllRoot (S : LRV.Substructure M) (f : S ↪[LRV] N) (a : ℕ → M) (n : ℕ) (m : M)
    (hS : Assembly.Standing S) (h : LiftAllRoot S f a n m) :
    ∃ (T : LRV.Substructure M) (g : T ↪[LRV] N) (hST : S ≤ T),
      (∀ x : S, g ⟨(x : M), hST x.2⟩ = f x) ∧ m ∈ T ∧ Assembly.Standing T := by
  obtain ⟨g, hagree⟩ := h.embed
  refine ⟨Substructure.closure LRV ((S : Set M) ∪ {m}), g,
    fun _ hx => Substructure.subset_closure (Or.inl hx), hagree,
    Substructure.subset_closure (Or.inr rfl), ?_⟩
  exact standing_closure_of_classControl hS h.class_control

/-- **The 3.4 slot, stated with `CaseNotSeparated`'s hypothesis shape** (i.e. `¬ Separated`, which
the 3.4 data proves for free by `liftAllRoot_not_separated`).  This is the slot at which Lemma 3.4
belongs; `M4Cases.CaseSeparated`'s `Separated` hypothesis is refuted by `unit` (§1). -/
def Slot34 : Prop :=
  ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N), Assembly.Standing S → ∀ (a : ℕ → M) (n : ℕ) (m : M),
    LiftAllRoot S f a n m → ¬ M5L.Separated S m →
      ∃ (T : LRV.Substructure M) (g : T ↪[LRV] N) (hST : S ≤ T),
        (∀ x : S, g ⟨(x : M), hST x.2⟩ = f x) ∧ m ∈ T ∧ Assembly.Standing T

/-- **The 3.4 data is never a `CaseSeparated` configuration.**  This is the sharp form of §1 for the
slot statement: at every configuration satisfying Lemma 3.4's hypotheses (`Standing S`, `F` monic
over `O(Ŝ)` with `e ∈ U(M)` a root of `F`), the hypothesis `M5L.Separated S m` of
`M4Cases.CaseSeparated` is *false*, so the separated slot cannot be where 3.4 is proved. -/
theorem liftAllRoot_not_separated {S : LRV.Substructure M} {f : S ↪[LRV] N} {a : ℕ → M} {n : ℕ}
    {m : M} (h : LiftAllRoot S f a n m) : ¬ M5L.Separated S m :=
  not_separated_of_units h.vf h.unit

/-- **The same, at `M4Cases.CaseNotSeparated`**: the 3.4 data satisfies the not-separated slot's
hypotheses (`Standing S`, `iVF m`, `iRv m ∈ S`, `¬ Separated S m`), so `M4Cases.CaseNotSeparated`
must be strong enough to cover Lemma 3.4 — the attribution of that slot to Lemma 3.5 alone
(`QE/OneStepCases.lean`) is incomplete. -/
theorem liftAllRoot_caseNotSeparated_hypotheses {S : LRV.Substructure M} {f : S ↪[LRV] N}
    {a : ℕ → M} {n : ℕ} {m : M} (h : LiftAllRoot S f a n m) :
    iVF m ∧ iRv m ∈ S ∧ ¬ M5L.Separated S m :=
  ⟨h.vf, h.rv_mem, liftAllRoot_not_separated h⟩

/-! ## 4. Stress tests -/

section Stress

/-- **(0) The literal reading "Lemma 3.4 at `CaseSeparated`'s hypotheses" is vacuous.**  Carrying
`M5L.Separated S m` *alongside* Lemma 3.4's data makes the hypothesis set inconsistent
(`liftAllRoot_not_separated`), so the implication holds for the wrong reason and proves nothing
about 3.4.  Recorded as the stress test that forces the slot to be `Slot34` (with `¬ Separated`). -/
theorem slot34_at_caseSeparated_hypotheses_vacuous (S : LRV.Substructure M) (f : S ↪[LRV] N)
    (a : ℕ → M) (n : ℕ) (m : M) (h : LiftAllRoot S f a n m) (hsep : M5L.Separated S m) :
    ∃ (T : LRV.Substructure M) (g : T ↪[LRV] N) (hST : S ≤ T),
      (∀ x : S, g ⟨(x : M), hST x.2⟩ = f x) ∧ m ∈ T ∧ Assembly.Standing T :=
  absurd hsep (liftAllRoot_not_separated h)


/-- **(a) `MonicO` and `IsRootOf` are inhabited**: `F = X - 1`, `e = 1`.  The coefficient function
is `a 0 = -1`, `a 1 = 1`, `a i = 0` for `i > 1`.  (This is the simplest instance of Lemma 3.4's
hypotheses; it shows the hypothesis package is not vacuous.) -/
noncomputable def xMinusOneCoeff : ℕ → M :=
  fun i => if i = 0 then iVFNeg (iVFOne (M := M)) else if i = 1 then iVFOne (M := M)
    else iVFZero (M := M)

theorem xMinusOneCoeff_zero :
    xMinusOneCoeff (M := M) 0 = iVFNeg (iVFOne (M := M)) := by
  unfold xMinusOneCoeff
  rw [if_pos rfl]

theorem xMinusOneCoeff_one : xMinusOneCoeff (M := M) 1 = iVFOne (M := M) := by
  unfold xMinusOneCoeff
  rw [if_neg (by norm_num), if_pos rfl]

theorem xMinusOneCoeff_other {i : ℕ} (h0 : i ≠ 0) (h1 : i ≠ 1) :
    xMinusOneCoeff (M := M) i = iVFZero (M := M) := by
  unfold xMinusOneCoeff
  rw [if_neg h0, if_neg h1]

theorem monicO_xMinusOne (S : LRV.Substructure M) : MonicO S (xMinusOneCoeff (M := M)) 1 := by
  have h1VF : iVF (iVFOne (M := M)) := vf_one_mem (M := M) hM
  have hnegS : iVFNeg (iVFOne (M := M)) ∈ S :=
    S.fun_mem Fn.vfNeg ![iVFOne (M := M)] (by intro j; fin_cases j; exact vfOne_mem_sub S)
  refine ⟨by norm_num, ?_, ?_, ?_, xMinusOneCoeff_one, ?_⟩
  · intro i hi
    rcases (by omega : i = 0 ∨ i = 1) with h0 | h1
    · rw [h0, xMinusOneCoeff_zero]; exact hnegS
    · rw [h1, xMinusOneCoeff_one]; exact vfOne_mem_sub S
  · intro i
    rcases (by omega : i = 0 ∨ i = 1 ∨ 1 < i) with h0 | h1 | h2
    · rw [h0, xMinusOneCoeff_zero]; exact vf_neg_mem (M := M) hM h1VF
    · rw [h1, xMinusOneCoeff_one]; exact h1VF
    · rw [xMinusOneCoeff_other (by omega) (by omega)]; exact vf_zero_mem (M := M) hM
  · intro i hi
    rcases (by omega : i = 0 ∨ i = 1) with h0 | h1
    · rw [h0, xMinusOneCoeff_zero]
      have h := (rv_neg_class (M := M) hM h1VF).2
      rwa [rv_one hM] at h
    · rw [h1, xMinusOneCoeff_one, rv_one hM]
      exact le_refl_rv hM (rv_one_mem (M := M) hM)
  · intro i hi
    exact xMinusOneCoeff_other (by omega) (by omega)

/-- **(a₁) `IsRootOf` is inhabited**: `1` is a root of `X - 1`. -/
theorem isRootOf_xMinusOne :
    IsRootOf (xMinusOneCoeff (M := M)) 1 (iVFOne (M := M)) := by
  have h1VF : iVF (iVFOne (M := M)) := vf_one_mem (M := M) hM
  have hnegVF : iVF (iVFNeg (iVFOne (M := M))) := vf_neg_mem (M := M) hM h1VF
  have hp0 : StandingTree.vfPow (M := M) (iVFOne (M := M)) 0 = iVFOne (M := M) := rfl
  have hp1 : StandingTree.vfPow (M := M) (iVFOne (M := M)) 1 = iVFOne (M := M) := by
    show iVFMul (iVFOne (M := M)) (iVFOne (M := M)) = iVFOne (M := M)
    exact RVCalc.vf_mul_one (M := M) hM h1VF
  have hm0 : iVFMul (xMinusOneCoeff (M := M) 0)
      (StandingTree.vfPow (M := M) (iVFOne (M := M)) 0) = iVFNeg (iVFOne (M := M)) := by
    rw [xMinusOneCoeff_zero, hp0]
    exact RVCalc.vf_mul_one (M := M) hM hnegVF
  have hm1 : iVFMul (xMinusOneCoeff (M := M) 1)
      (StandingTree.vfPow (M := M) (iVFOne (M := M)) 1) = iVFOne (M := M) := by
    rw [xMinusOneCoeff_one, hp1]
    exact RVCalc.vf_mul_one (M := M) hM h1VF
  unfold IsRootOf M7Hens.vfEval
  have hstep : M7Hens.vfSum (M := M)
      (fun i => iVFMul (xMinusOneCoeff (M := M) i)
        (StandingTree.vfPow (M := M) (iVFOne (M := M)) i)) 1
      = iVFAdd (iVFMul (xMinusOneCoeff (M := M) 0)
          (StandingTree.vfPow (M := M) (iVFOne (M := M)) 0))
        (iVFMul (xMinusOneCoeff (M := M) 1)
          (StandingTree.vfPow (M := M) (iVFOne (M := M)) 1)) := rfl
  rw [hstep, hm0, hm1, RVCalc.vf_add_comm (M := M) hM hnegVF h1VF]
  exact RVCalc.vf_add_neg (M := M) hM h1VF

/-- **(a′) The simplest 3.4 datum is not separated** — the concrete instance of §1: `1` is a unit of
the valuation ring, so no substructure has it as a `Separated` element. -/
theorem not_separated_one (S : LRV.Substructure M) :
    ¬ M5L.Separated S (iVFOne (M := M)) := by
  refine not_separated_of_units (S := S) (vf_one_mem (M := M) hM) ?_
  rw [rv_one hM]
  exact StandingTree.rv_one_units

/-- **(b) The slot conclusion is satisfiable** wherever the monomorphism extends to a total
`M ↪[LRV] N`: then `T = ⊤` works, since `Standing ⊤` holds (`StandingTree.standing_top`) and an
`RV`-class computation is not needed.  So the statement of the slot is not contradictory, and it
carries no cardinality conjunct beyond what `Standing S` plus an embedding already forces
(`M4Cases.standing_forces_units_size`). -/
theorem slot_of_global_extension (S : LRV.Substructure M) (f : S ↪[LRV] N) {m : M}
    (hglob : ∃ g : M ↪[LRV] N, ∀ x : S, g (x : M) = f x) :
    ∃ (T : LRV.Substructure M) (g : T ↪[LRV] N) (hST : S ≤ T),
      (∀ x : S, g ⟨(x : M), hST x.2⟩ = f x) ∧ m ∈ T ∧ Assembly.Standing T := by
  obtain ⟨g, hg⟩ := hglob
  exact ⟨⊤, g.domRestrict ⊤, fun _ _ => trivial, fun x => hg x, trivial,
    StandingTree.standing_top⟩

end Stress

/-! ## 6. Why a `¬ Separated ⇒ configuration` cover cannot hold: the unit points

`QE/OneStepCases.lean`'s not-separated slot is *complement*-based (`¬ M5L.Separated S m`), while the
paper's Lemma 3.5 (`lift:divisible:hull`) is *configuration*-based (`m^n = a ∈ S`, `n > 1`,
`vv(m^i) ∉ Γ(Ŝ)` for `0 < i < n`).  Member `m4` (same swarm, `.ultramath/smw2mluv7/m4/
LiftDivHull.lean`) bridges them by the exhaustion statement `DivHullCover`: every not-separated
point carries the configuration.  That cover is **false**: at a unit point `vv(m^k) = 0` for every
`k`, so the configuration's separation conjunct fails already at `k = 1 < n` (for `n > 1`).  The
definitions below are m4's, restated verbatim so that the refutation is against the real statement. -/

/-- m4's `SeparatedBelow`: the paper's truncation `vv(m^k) ∉ Γ(Ŝ)` for `0 < k < n`. -/
def SeparatedBelow (S : LRV.Substructure M) (m : M) (n : ℕ) : Prop :=
  ∀ k, 0 < k → k < n → ∀ x y : M, iVF x → iVF y → x ∈ S → y ∈ S →
    x ≠ iVFZero → y ≠ iVFZero →
      ¬ Transc.Cls (iRVMul (rvpow (iRv m) k) (iRv x)) (iRv y)

/-- m4's `HasDivHullConfig`: the `lift:divisible:hull` configuration as a `Prop`. -/
def HasDivHullConfig (S : LRV.Substructure M) (m : M) : Prop :=
  ∃ (n : ℕ) (a : M),
    1 < n ∧ iVF m ∧ m ≠ iVFZero ∧ iRv m ∈ S ∧
      iVF a ∧ a ∈ S ∧ a ≠ iVFZero ∧ Transc.vpow m n = a ∧ SeparatedBelow S m n

/-- **A unit has no truncated separation**: for `n > 1` the conjunct `SeparatedBelow S m n` fails at
`k = 1`, `x = y = 1`. -/
theorem not_separatedBelow_of_units {S : LRV.Substructure M} {m : M} (hmVF : iVF m)
    (hmU : iUnits (iRv m)) {n : ℕ} (hn : 1 < n) : ¬ SeparatedBelow S m n := by
  intro hb
  have hrv : iRV (iRv m) := rv_mem hM hmVF
  have hunit : iLe iRVOne (iRv m) ∧ iLe (iRv m) iRVOne :=
    (units_iff_le_one hM hrv (GammaGroup.units_ne_zero hmU)).mp hmU
  have h1S : iVFOne (M := M) ∈ S := vfOne_mem_sub S
  have h1VF : iVF (iVFOne (M := M)) := vf_one_mem (M := M) hM
  have h10 : iVFOne (M := M) ≠ iVFZero (M := M) := (RVCalc.vf_zero_ne_one (M := M) hM).symm
  refine hb 1 (by norm_num) hn (iVFOne (M := M)) (iVFOne (M := M)) h1VF h1VF h1S h1S h10 h10 ?_
  rw [rvpow_one, rv_one hM, rv_mul_one_any hM hrv, rv_mul_one_any_right hM hrv]
  exact ⟨hunit.2, hunit.1⟩

/-- **`HasDivHullConfig` is false at every unit.** -/
theorem not_hasDivHullConfig_of_units {S : LRV.Substructure M} {m : M} (hmVF : iVF m)
    (hmU : iUnits (iRv m)) : ¬ HasDivHullConfig S m := by
  rintro ⟨n, a, hn, hmVF', _hm0, _hmRV, _haVF, _haS, _ha0, _hpow, hbelow⟩
  exact not_separatedBelow_of_units hmVF' hmU hn hbelow

/-- `VFInvClosedOn ⊤` is just invertibility in the `VF` sort, which `ACVF` gives. -/
theorem vfInvClosedOn_top : M5L.VFInvClosedOn (⊤ : LRV.Substructure M) := by
  intro x hx _ hx0
  rcases Transfer.vf_mul_inv_or_zero (M := M) hM hx with h | ⟨y, hy, hxy⟩
  · exact absurd h hx0
  · exact ⟨y, hy, trivial, hxy⟩

/-- **The `lift:divisible:hull` cover (`DivHullCover`) is refuted** at `S = ⊤`, at any pair `(M, N)`
that admits an embedding `⊤ ↪[LRV] N`.  So the exhaustion step must be restricted to the non-unit
points; at a unit point the paper's Lemma 3.5 supplies nothing, and the unit case is Lemmas 3.4/3.6. -/
theorem divHullCover_refuted
    (hcover : ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N), Assembly.Standing S →
      M5L.VFInvClosedOn S → ∀ m : M, iVF m → iRv m ∈ S → ¬ M5L.Separated S m →
        HasDivHullConfig S m)
    (_f : (⊤ : LRV.Substructure M) ↪[LRV] N) : False := by
  have h1VF : iVF (iVFOne (M := M)) := vf_one_mem (M := M) hM
  have h1U : iUnits (iRv (iVFOne (M := M))) := by
    rw [rv_one hM]
    exact StandingTree.rv_one_units
  have h10 : iVFOne (M := M) ≠ iVFZero (M := M) := (RVCalc.vf_zero_ne_one (M := M) hM).symm
  exact not_hasDivHullConfig_of_units h1VF h1U
    (hcover ⊤ _f StandingTree.standing_top vfInvClosedOn_top (iVFOne (M := M)) h1VF (by trivial)
      (not_separated_top h1VF h10))

end M5P1
end SpecialTransformations.Milestone0

/-! ## Axiom audit -/

#print axioms SpecialTransformations.Milestone0.M5P1.vfOne_mem_sub
#print axioms SpecialTransformations.Milestone0.M5P1.separated_imp_pow_not_cls_one
#print axioms SpecialTransformations.Milestone0.M5P1.not_separated_of_units
#print axioms SpecialTransformations.Milestone0.M5P1.rv_mem_of_units
#print axioms SpecialTransformations.Milestone0.M5P1.separated_of_pow_notin
#print axioms SpecialTransformations.Milestone0.M5P1.not_separated_top
#print axioms SpecialTransformations.Milestone0.M5P1.liftTranscendental_not_separated
#print axioms SpecialTransformations.Milestone0.M5P1.caseNotSeparated_iff_unit_and_nonunit
#print axioms SpecialTransformations.Milestone0.M5P1.unit_class_in_S
#print axioms SpecialTransformations.Milestone0.M5P1.slot34_at_caseSeparated_hypotheses_vacuous
#print axioms SpecialTransformations.Milestone0.M5P1.standing_closure_of_classControl
#print axioms SpecialTransformations.Milestone0.M5P1.slot_of_liftAllRoot
#print axioms SpecialTransformations.Milestone0.M5P1.liftAllRoot_not_separated
#print axioms SpecialTransformations.Milestone0.M5P1.liftAllRoot_caseNotSeparated_hypotheses
#print axioms SpecialTransformations.Milestone0.M5P1.monicO_xMinusOne
#print axioms SpecialTransformations.Milestone0.M5P1.isRootOf_xMinusOne
#print axioms SpecialTransformations.Milestone0.M5P1.not_separated_one
#print axioms SpecialTransformations.Milestone0.M5P1.slot_of_global_extension
#print axioms SpecialTransformations.Milestone0.M5P1.not_separatedBelow_of_units
#print axioms SpecialTransformations.Milestone0.M5P1.not_hasDivHullConfig_of_units
#print axioms SpecialTransformations.Milestone0.M5P1.vfInvClosedOn_top
#print axioms SpecialTransformations.Milestone0.M5P1.divHullCover_refuted
