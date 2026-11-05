/-
# Direction p5: the not-separated slot (`M4Cases.CaseNotSeparated`) — exact statement, fragments,
# and the obstruction to the paper's `m^n = a` shape

Member `m5`, swarm `smw2mluv7`.

The frozen slot (`QE/OneStepCases.lean`) is

    CaseNotSeparated := ∀ S f, Standing S → ∀ m, iVF m → iRv m ∈ S → ¬ M5L.Separated S m →
      ∃ T g hST, (∀ x : S, g ⟨x, hST x.2⟩ = f x) ∧ m ∈ T ∧ Standing T

— the `rv`-old case of `Assembly.OneStepVFP` in which the new element `m` is *not* separated from
`S`.  The paper's branch for it is `lift:divisible:hull` (`qe.tex:633`), i.e. the divisible-hull
step of the `S*` construction (`qe.tex:582-612`): `e^n = a ∈ VF(Ŝ)` for some `n > 1`,
`vv(e^i) ∉ Γ(Ŝ)` for `0 < i < n`, `(VF(Ŝ), O(Ŝ))` henselian.

## Contents and verdict

**§1** the paper's finite-range separation hypothesis `SeparatedBelow S m n`, its monotonicity,
`M5L.Separated S m ↔ ∀ n, SeparatedBelow S m n`, and the minimal violation exponent
(`exists_minimal_violation`): the paper's `n` is a well-defined function of the data.

**§2 (main fragment).**  `Assembly.Standing S` contains `Assembly.GammaDivisible S`: every value
class in `S` has an `n`-th root in `S` up to a unit.  With torsion-freeness of
`Γ(M) = RV^×/K^×` (`GammaDiv.gamma_pow_inj`; ordered groups are torsion-free) this forces the
minimal violation exponent to be **one**:

  `notSeparated_class_form` — `Standing S`, `iVF m`, `m ≠ 0`, `iRv m ∈ S`, `¬ Separated S m` give
  `u, u' ∈ RV(S) ∖ {0}` with `Cls (rv m · u) u'`, i.e. `[m] = [u'] - [u]` in `Γ(M)`.

That is the `n = 1` instance of the paper's `t^n ∈ S₁`: the class of `m` is a *quotient* of two old
classes.  Consequence: `rv m · u ∈ S` (`notSeparated_mul_mem`); with the paper's VF-generation
property (`Assembly.IsVFGen S`, Remark 3.1 for `Ŝ = ⟨VF(S)⟩`) the witnesses are `rv` of VF-elements
of `S` (`notSeparated_vf_form`).

**§3c (perturbation obstruction).**  The frozen slot's hypothesis `iRv m ∈ S` is weaker than the
paper's `rv(e) ∈ RV(S) ∖ RV(Ŝ)`: it also admits `m = y + ε` with `y ∈ S ∩ VF` old and `ε` of a *new*
value class.  There the paper's Claim (⋆) conclusion is **false**: the closure of `S ∪ {m}` contains
`ε`, whose class is not an old class, so no `T ⊇ S` containing `m` satisfies `M5L.ResidualClasses S T`
(`not_residualClasses_of_perturbation`).  Hence `ResidualClasses`/`RV`-control interfaces are
*sufficient only* and cannot be derived from the slot's hypotheses; the slot itself can only be
reached by realisation (total extension: `Input5R` at relGate pairs).  The paper's missing conjunct
is `RVNewOverVF S m` (the class of `m` is not the class of a VF-element of `S`), which `Separated`
*does* imply (`separated_imp_RVNewOverVF`) — so the two cases are genuinely asymmetric.

**§3 (obstruction).**  At the slot's hypotheses *together with* `Assembly.IsVFGen S` the paper's
shape with `n ≥ 2` is **inconsistent**: `not_separatedBelow_of_notSeparated` gives
`¬ SeparatedBelow S m n` for every `n ≥ 2`, hence no `RootStepHyp` (`m^n = a ∈ S` plus
separation-below-`n`, `n ≥ 2`) holds at `CaseNotSeparated`.  This is not an accident: the
`m^n = a` shape is the one-element step of the *divisible hull*, where `Γ(Ŝ)` is by construction
*not* divisible (`qe.tex:820`), whereas `Standing S` — the frozen slot's hypothesis — is exactly the
regime in which it cannot occur.  So the paper's Lemma-3.6 hypothesis cannot be *stated* at the
slot; §2's `k = 1` form is the normal form the slot actually has.

**§4 the exact branch statement and the implication chain into the slot.**
`RVOldClass S m` is §2's normal form; `NotSeparatedBranch` is the slot with `¬ Separated S m`
replaced by `RVOldClass S m` and with the tree's `M5L.ResidualClasses S T` as conclusion (the class
control that `M5L.standing_of_ClassControl` converts into `Standing T`).
`caseNotSeparated_of_branch` is the machine-checked chain; `caseNotSeparated_of_ResidualClasses`
and `caseNotSeparated_of_RVControl` are the slot-shaped interfaces mirroring the merged
`caseSeparated_of_ResidualClasses` / `caseSeparated_of_RVControl`.

**§4c what the `Γ`-machinery gives inside the branch**: `cls_rvpow_mul` (`[m]^j + [u]^j = [u']^j`)
and `monomial_class_control` — for every monomial `b · m^j` with `b ∈ S ∩ VF`, the class of
`rv (b · m^j)` times the *fixed* old factor `(rv u)^j` is the class of an element of `S`.  Removing
that factor is exactly the point where the missing inverse of an old class bites; this is the same
`L_RV`-has-no-`VF`-inverse defect that makes `M5L.VFInvClosedOn` underivable from `Standing`.

**The exact residual.**  What the slot still owes after this file is *not* a statement about `Γ`:
it is (a) `M5L.ResidualClasses S T` for a `T ⊇ ⟨S,m⟩` (the class control of the *quotient/junk*
part of the closure, i.e. the paper's "quotient of expansions" step for the `k = 1` branch, where
the paper's separation-based distinctness of monomial classes is unavailable), and (b) the
`L_RV`-monomorphism `g : T ↪ N` extending `f` (the paper's saturation/atomic-realisation half, the
same input every slot uses).  `NotSeparatedBranch` is the branch with (a) isolated and
`caseNotSeparated_of_branch` the machine-checked chain from it to `M4Cases.CaseNotSeparated`.

**§4d `cases_of_branch`**: the frozen `M4Cases.Cases` from `CaseSeparated`,
`NotSeparatedBranch`, `CaseNewRV` — the integration point with `M4Cases.oneStepVFP_of_cases`.

**§5 stress tests.**  `not_separated_of_vpow`: the paper's `m^n = a` hypothesis *forces*
`¬ Separated`, so the branch hypothesis is not vacuous (and the *unrestricted* `Separated` is
incompatible with the paper's shape — the finite range `0 < i < n` is forced).
`separated_imp_not_mem`: `Separated S m` implies `m ∉ S`, so the case split is consistent.
`notSeparated_class_form_concl_witness`: §2's conclusion is inhabited (at `u = 1`, `u' = rv m`).
`notSeparated_top`, `caseNotSeparated_hyp_satisfiable`: at `S = ⊤` the slot's hypotheses hold for
every `m ≠ 0`, so `CaseNotSeparated` is not a vacuous implication; `Standing ⊤` is
`StandingTree.standing_top`.

No `sorry`, no `axiom`, no `native_decide`; the axiom audit is at the end of the file.
-/
import OneStepCases
import GammaDiv

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
open SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Milestone0.RVCalc
open SpecialTransformations.Milestone0.Transc

namespace SpecialTransformations.Milestone0.Case35

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {N : Type} [LRV.Structure N] [hN : N ⊨ Axioms.ACVF]

/-! ## 0. Closure of a substructure -/

theorem vfOne_mem_sub (S : LRV.Substructure M) : iVFOne (M := M) ∈ S :=
  S.fun_mem Fn.vfOne (fun i => i.elim0) (fun i => i.elim0)

theorem vfMul_mem_sub (S : LRV.Substructure M) {x y : M} (hx : x ∈ S) (hy : y ∈ S) :
    iVFMul x y ∈ S :=
  S.fun_mem Fn.vfMul ![x, y] (by
    intro i
    fin_cases i
    · simpa using hx
    · simpa using hy)

/-! ## 1. The paper's finite-range separation hypothesis, and the minimal violation -/

/-- **Lemma 3.6's separation hypothesis, transcribed** (`qe.tex:633`: `vv(e^i) ∉ Γ(Ŝ)` for
`0 < i < n`), in the tree's `Γ`-class vocabulary.  `M5L.Separated S e` is the `n = ∞` form
(`separated_iff_forall_separatedBelow`). -/
def SeparatedBelow (S : LRV.Substructure M) (e : M) (n : ℕ) : Prop :=
  ∀ k, 0 < k → k < n → ∀ x y : M, iVF x → iVF y → x ∈ S → y ∈ S →
    x ≠ iVFZero → y ≠ iVFZero →
      ¬ Transc.Cls (iRVMul (Transc.rvpow (iRv e) k) (iRv x)) (iRv y)

/-- `SeparatedBelow` is anti-monotone in the degree bound. -/
theorem separatedBelow_mono {S : LRV.Substructure M} {e : M} {n n' : ℕ} (hn : n ≤ n')
    (h : SeparatedBelow S e n') : SeparatedBelow S e n :=
  fun k hk hk' => h k hk (lt_of_lt_of_le hk' hn)

/-- **The paper's separation hypothesis is the `n = ∞` case.** -/
theorem separated_iff_forall_separatedBelow (S : LRV.Substructure M) (e : M) :
    M5L.Separated S e ↔ ∀ n, SeparatedBelow S e n := by
  constructor
  · intro h n k hk _ x y hx hy hxS hyS hx0 hy0
    exact h k hk x y hx hy hxS hyS hx0 hy0
  · intro h k hk x y hx hy hxS hyS hx0 hy0
    exact h (k + 1) k hk (Nat.lt_succ_self k) x y hx hy hxS hyS hx0 hy0

/-- A violation of separation at exponent `k`: a class of `(rv e)^k · rv x` that is the class of an
element of `S`. -/
def Violates (S : LRV.Substructure M) (e : M) (k : ℕ) : Prop :=
  0 < k ∧ ∃ x y : M, iVF x ∧ iVF y ∧ x ∈ S ∧ y ∈ S ∧ x ≠ iVFZero ∧ y ≠ iVFZero ∧
    Transc.Cls (iRVMul (Transc.rvpow (iRv e) k) (iRv x)) (iRv y)

/-- `¬ Separated` is the existence of a violation. -/
theorem not_separated_iff_exists_violates (S : LRV.Substructure M) (e : M) :
    ¬ M5L.Separated S e ↔ ∃ k, Violates S e k := by
  constructor
  · intro h
    by_contra hcon
    apply h
    intro k hk x y hx hy hxS hyS hx0 hy0 hcls
    exact hcon ⟨k, hk, x, y, hx, hy, hxS, hyS, hx0, hy0, hcls⟩
  · rintro ⟨k, hk, x, y, hx, hy, hxS, hyS, hx0, hy0, hcls⟩ hsep
    exact hsep k hk x y hx hy hxS hyS hx0 hy0 hcls

/-- **The paper's minimal exponent exists**: some exponent violates separation, and every smaller
positive exponent is separated.  (This is the `n` of `lift:divisible:hull`.) -/
theorem exists_minimal_violation (S : LRV.Substructure M) (e : M)
    (h : ¬ M5L.Separated S e) :
    ∃ n : ℕ, Violates S e n ∧ ∀ k, k < n → ¬ Violates S e k := by
  classical
  have hex : ∃ k, Violates S e k := (not_separated_iff_exists_violates S e).mp h
  exact ⟨Nat.find hex, Nat.find_spec hex, fun k hk => Nat.find_min hex hk⟩

/-- The minimal violation gives the paper's finite-range separation hypothesis. -/
theorem separatedBelow_of_minimal {S : LRV.Substructure M} {e : M} {n : ℕ}
    (hmin : ∀ k, k < n → ¬ Violates S e k) : SeparatedBelow S e n := by
  intro k hk hkn x y hx hy hxS hyS hx0 hy0 hcls
  exact hmin k hkn ⟨hk, x, y, hx, hy, hxS, hyS, hx0, hy0, hcls⟩

/-- **`rv e` raised to the first power is `rv e`.** -/
theorem transc_rvpow_one {u : M} (hu : iRV u) : Transc.rvpow u 1 = u := by
  show iRVMul (Transc.rvpow u 0) u = u
  rw [show Transc.rvpow u 0 = iRVOne from rfl]
  exact MulNormalForm.rv_mul_one_all hM hu

/-! ## 2. The normal form of `¬ Separated` under `Standing S`: exponent one -/

/-- `rv` of a nonzero `VF`-element is a nonzero `RV`-element. -/
theorem rv_mem_ne {x : M} (hx : iVF x) (hx0 : x ≠ iVFZero) : iRv x ≠ iRVZero :=
  fun h => hx0 (vf_eq_zero_of_rv_eq_zero hM hx h)

/-- The two `rvPow`s of the tree agree (`Transc.rvpow` is the one in `M5L.Separated`,
`Assembly.rvPow` the one in `Assembly.GammaDivisible`). -/
theorem transc_rvpow_eq_rvPow (u : M) : ∀ k : ℕ, Transc.rvpow u k = Assembly.rvPow u k
  | 0 => rfl
  | (k + 1) => by
      show iRVMul (Transc.rvpow u k) u = iRVMul (Assembly.rvPow u k) u
      rw [transc_rvpow_eq_rvPow u k]

/-- `Γ`-class of a nonzero `VF`-element (the tree's `GammaGroup.gammaVal`). -/
noncomputable def gv (x : M) (hx : iVF x) (hx0 : x ≠ iVFZero) : GammaGroup.GammaOf M :=
  GammaGroup.gammaVal hx hx0

theorem gv_eq_mkR {x : M} (hx : iVF x) (hx0 : x ≠ iVFZero) :
    gv x hx hx0
      = GammaGroup.gammaMk (GammaDiv.mkR (iRv x) (rv_mem hM hx) (rv_mem_ne hx hx0)) := rfl

/-- `gv` is multiplicative. -/
theorem gv_mul {x y : M} (hx : iVF x) (hy : iVF y) (hx0 : x ≠ iVFZero) (hy0 : y ≠ iVFZero) :
    gv x hx hx0 * gv y hy hy0
      = gv (iVFMul x y) (Transfer.vf_mul_mem hM hx hy) (GammaDiv.vf_mul_ne_zero hx hy hx0 hy0) :=
  GammaDiv.gammaVal_mul hx hy hx0 hy0

/-- `gv` of a class-`1` element is `1`. -/
theorem gv_of_rv_one {x : M} (hx : iVF x) (hx0 : x ≠ iVFZero) (h : iRv x = iRVOne) :
    gv x hx hx0 = 1 := by
  have h1 : (GammaGroup.rvStarOf hx hx0).1 = iRVOne := h
  have hu : iUnits (GammaGroup.rvStarOf hx hx0).1 := h1 ▸ StandingTree.rv_one_units
  show GammaGroup.gammaMk (GammaGroup.rvStarOf hx hx0) = 1
  exact (GammaGroup.gammaMk_eq_one_iff_units).mpr hu

/-- `gv 1 = 1`. -/
theorem gv_one :
    gv (iVFOne : M) (Transfer.vf_one_mem (M := M) hM)
      (fun h => RVCalc.vf_zero_ne_one hM h.symm) = 1 :=
  gv_of_rv_one _ _ (rv_one hM)

/-- **`gv` of a `VF`-power is the power of `gv`.** -/
theorem gv_pow (x : M) (hx : iVF x) (hx0 : x ≠ iVFZero) :
    ∀ k : ℕ, gv (Transc.vpow x k) (Transc.iVF_vpow hM hx k)
        (Transc.vpow_ne_zero hM hx hx0 k) = gv x hx hx0 ^ k
  | 0 => by
      rw [pow_zero]
      exact gv_one
  | (k + 1) => by
      have hfac : gv (Transc.vpow x k) (Transc.iVF_vpow hM hx k)
            (Transc.vpow_ne_zero hM hx hx0 k) * gv x hx hx0
          = gv (iVFMul (Transc.vpow x k) x) (Transfer.vf_mul_mem hM (Transc.iVF_vpow hM hx k) hx)
              (GammaDiv.vf_mul_ne_zero (Transc.iVF_vpow hM hx k) hx
                (Transc.vpow_ne_zero hM hx hx0 k) hx0) :=
        gv_mul (Transc.iVF_vpow hM hx k) hx (Transc.vpow_ne_zero hM hx hx0 k) hx0
      have hstep : gv (iVFMul (Transc.vpow x k) x)
          (Transfer.vf_mul_mem hM (Transc.iVF_vpow hM hx k) hx)
          (GammaDiv.vf_mul_ne_zero (Transc.iVF_vpow hM hx k) hx
            (Transc.vpow_ne_zero hM hx hx0 k) hx0) = gv x hx hx0 ^ (k + 1) := by
        rw [← hfac, gv_pow x hx hx0 k, pow_succ]
      exact hstep

/-- Equality of `Γ`-classes is equality of `gammaMk`'s. -/
theorem gammaMk_eq_of_cls {a b : M} (ha : iRV a) (ha0 : a ≠ iRVZero) (hb : iRV b)
    (hb0 : b ≠ iRVZero) (h : Transc.Cls a b) :
    GammaGroup.gammaMk (GammaDiv.mkR a ha ha0) = GammaGroup.gammaMk (GammaDiv.mkR b hb hb0) :=
  GammaGroup.gammaMk_eq_iff_le.mpr h

/-- The converse: `Γ`-classes from an equality in `Γ(M)`. -/
theorem cls_of_gammaMk_eq {a b : M} (ha : iRV a) (ha0 : a ≠ iRVZero) (hb : iRV b)
    (hb0 : b ≠ iRVZero)
    (h : GammaGroup.gammaMk (GammaDiv.mkR a ha ha0) = GammaGroup.gammaMk (GammaDiv.mkR b hb hb0)) :
    Transc.Cls a b :=
  GammaGroup.gammaMk_eq_iff_le.mp h

/-- Product rule on `mkR`-classes. -/
theorem gammaMk_mul_mkR {a b : M} (ha : iRV a) (ha0 : a ≠ iRVZero) (hb : iRV b)
    (hb0 : b ≠ iRVZero) :
    GammaGroup.gammaMk
        (GammaDiv.mkR (iRVMul a b) (Transfer.rv_mul_mem hM ha hb)
          (GammaGroup.rvStar_mul_nonzero ⟨ha, ha0⟩ ⟨hb, hb0⟩))
      = GammaGroup.gammaMk (GammaDiv.mkR a ha ha0) *
        GammaGroup.gammaMk (GammaDiv.mkR b hb hb0) := by
  rw [GammaDiv.mkR_mul_eq a b ha ha0 hb hb0, GammaGroup.gammaMk_mul]

/-- The class of an `n`-th root, given the frozen form of divisibility `rvPow u n = t · c` with
`c` a unit. -/
theorem gammaMk_pow_of_rvPow_eq_mul_unit {u t c : M} {k : ℕ}
    (hu : iRV u) (hu0 : u ≠ iRVZero) (ht : iRV t) (ht0 : t ≠ iRVZero)
    (hc : iRV c) (hcU : iUnits c) (hpow : Assembly.rvPow u k = iRVMul t c) :
    GammaGroup.gammaMk (GammaDiv.mkR u hu hu0) ^ k
      = GammaGroup.gammaMk (GammaDiv.mkR t ht ht0) := by
  rw [GammaDiv.gammaMk_rvPow, GammaDiv.rvStarPow_mkR]
  refine (gammaMk_eq_of_cls (GammaDiv.rvPow_mem hu k) (GammaDiv.rvPow_ne_zero hu hu0 k)
    (Transfer.rv_mul_mem hM ht hc)
    (GammaGroup.rvStar_mul_nonzero ⟨ht, ht0⟩ ⟨hc, GammaGroup.units_ne_zero hcU⟩) ?_).trans
    ?_
  · rw [hpow]
    exact Transc.cls_refl hM (Transfer.rv_mul_mem hM ht hc)
  · rw [GammaDiv.mkR_mul_eq t c ht ht0 hc (GammaGroup.units_ne_zero hcU), GammaGroup.gammaMk_mul,
      show GammaGroup.gammaMk (GammaDiv.mkR c hc (GammaGroup.units_ne_zero hcU)) = 1
        from (GammaGroup.gammaMk_eq_one_iff_units).mpr hcU, mul_one]

/-- **The normal form of `¬ Separated` at the slot**: under `Standing S` (i.e. `Γ(S)` divisible and
all units in `S`) the minimal violation exponent is *one*: the class of `m` is a quotient of two old
classes.  This is the `n = 1` instance of the paper's `t^n ∈ S₁`. -/
theorem notSeparated_class_form {S : LRV.Substructure M} (hS : Assembly.Standing S) {m : M}
    (hmVF : iVF m) (hm0 : m ≠ iVFZero) (hmrv : iRv m ∈ S) (hnot : ¬ M5L.Separated S m) :
    ∃ u u' : M, u ∈ S ∧ u' ∈ S ∧ iRV u ∧ iRV u' ∧ u ≠ iRVZero ∧ u' ≠ iRVZero ∧
      Transc.Cls (iRVMul (iRv m) u) u' := by
  obtain ⟨k, hkpos, x, y, hxVF, hyVF, hxS, hyS, hx0, hy0, hcls⟩ :=
    (not_separated_iff_exists_violates S m).mp hnot
  have hk1 : 1 ≤ k := hkpos
  -- the violation, with `rvpow (rv m) k` written as `rv (m ^ k)`
  have hcls' : Transc.Cls (iRVMul (iRv (Transc.vpow m k)) (iRv x)) (iRv y) := by
    rw [Transc.rv_vpow hM hmVF k]
    exact hcls
  -- the product rule for `gv`
  have hprod : gv (iVFMul (Transc.vpow m k) x)
      (Transfer.vf_mul_mem hM (Transc.iVF_vpow hM hmVF k) hxVF)
      (GammaDiv.vf_mul_ne_zero (Transc.iVF_vpow hM hmVF k) hxVF
        (Transc.vpow_ne_zero hM hmVF hm0 k) hx0) = gv y hyVF hy0 := by
    rw [gv_eq_mkR, gv_eq_mkR]
    refine gammaMk_eq_of_cls (rv_mem hM (Transfer.vf_mul_mem hM (Transc.iVF_vpow hM hmVF k) hxVF))
      (rv_mem_ne (Transfer.vf_mul_mem hM (Transc.iVF_vpow hM hmVF k) hxVF)
        (GammaDiv.vf_mul_ne_zero (Transc.iVF_vpow hM hmVF k) hxVF
          (Transc.vpow_ne_zero hM hmVF hm0 k) hx0))
      (rv_mem hM hyVF) (rv_mem_ne hyVF hy0) ?_
    rw [Transfer.rv_mul_hom_of_model hM (Transc.iVF_vpow hM hmVF k) hxVF]
    exact hcls'
  -- the divisibility roots of the two old classes
  obtain ⟨u, c, huS, huRV, hu0, hcS, hcU, hpow⟩ :=
    hS.2 (iRv x) (M5L.rv_mem_sub S hxS) (rv_mem hM hxVF) (rv_mem_ne hxVF hx0) k hk1
  obtain ⟨v, d, hvS, hvRV, hv0, hdS, hdU, hpow'⟩ :=
    hS.2 (iRv y) (M5L.rv_mem_sub S hyS) (rv_mem hM hyVF) (rv_mem_ne hyVF hy0) k hk1
  have hpx : GammaGroup.gammaMk (GammaDiv.mkR u huRV hu0) ^ k = gv x hxVF hx0 := by
    rw [gv_eq_mkR]
    exact gammaMk_pow_of_rvPow_eq_mul_unit huRV hu0 (rv_mem hM hxVF) (rv_mem_ne hxVF hx0)
      (Jm2.iRV_of_inK (Or.inl hcU)) hcU hpow
  have hpy : GammaGroup.gammaMk (GammaDiv.mkR v hvRV hv0) ^ k = gv y hyVF hy0 := by
    rw [gv_eq_mkR]
    exact gammaMk_pow_of_rvPow_eq_mul_unit hvRV hv0 (rv_mem hM hyVF) (rv_mem_ne hyVF hy0)
      (Jm2.iRV_of_inK (Or.inl hdU)) hdU hpow'
  -- cancel the `k`-th powers in the ordered group `Γ(M)`
  have hkey : gv m hmVF hm0 ^ k * GammaGroup.gammaMk (GammaDiv.mkR u huRV hu0) ^ k
      = GammaGroup.gammaMk (GammaDiv.mkR v hvRV hv0) ^ k := by
    rw [← gv_pow m hmVF hm0 k, hpx,
      gv_mul (x := Transc.vpow m k) (y := x) (hx := Transc.iVF_vpow hM hmVF k) (hy := hxVF)
        (hx0 := Transc.vpow_ne_zero hM hmVF hm0 k) (hy0 := hx0), hprod, ← hpy]
  have hfinal : gv m hmVF hm0 * GammaGroup.gammaMk (GammaDiv.mkR u huRV hu0)
      = GammaGroup.gammaMk (GammaDiv.mkR v hvRV hv0) := by
    apply GammaDiv.gamma_pow_inj (n := k) hk1
    rw [mul_pow]
    exact hkey
  refine ⟨u, v, huS, hvS, huRV, hvRV, hu0, hv0, ?_⟩
  have h1 : gv m hmVF hm0 * GammaGroup.gammaMk (GammaDiv.mkR u huRV hu0)
      = GammaGroup.gammaMk (GammaDiv.mkR (iRVMul (iRv m) u)
          (Transfer.rv_mul_mem hM (rv_mem hM hmVF) huRV)
          (GammaGroup.rvStar_mul_nonzero ⟨rv_mem hM hmVF, rv_mem_ne hmVF hm0⟩ ⟨huRV, hu0⟩)) := by
    rw [gv_eq_mkR]
    exact gammaMk_mul_mkR (rv_mem hM hmVF) (rv_mem_ne hmVF hm0) huRV hu0
  rw [h1] at hfinal
  exact cls_of_gammaMk_eq _ _ _ _ hfinal

/-- **Consequence**: some old class times the class of `m` is *literally* an element of `S`. -/
theorem notSeparated_mul_mem {S : LRV.Substructure M} (hS : Assembly.Standing S) {m : M}
    (hmVF : iVF m) (hm0 : m ≠ iVFZero) (hmrv : iRv m ∈ S) (hnot : ¬ M5L.Separated S m) :
    ∃ u : M, u ∈ S ∧ iRV u ∧ u ≠ iRVZero ∧ iRVMul (iRv m) u ∈ S := by
  obtain ⟨u, u', huS, hu'S, hu, hu', hu0, hu'0, hcls⟩ :=
    notSeparated_class_form hS hmVF hm0 hmrv hnot
  exact ⟨u, huS, hu, hu0,
    M5L.mem_of_cls_mem hM hS.1 (Transfer.rv_mul_mem hM (rv_mem hM hmVF) hu) hu' hcls hu'S⟩

/-! ## 3. The `m^n = a` shape is *not* the normal form at the slot: the obstruction -/

/-- **The paper's VF-generation property** (`Assembly.IsVFGen`) turns §2's `RV`-witnesses into
`VF`-witnesses: `¬ Separated` is a violation at exponent **one**. -/
theorem notSeparated_vf_form {S : LRV.Substructure M} (hS : Assembly.Standing S)
    (hgen : Assembly.IsVFGen S) {m : M} (hmVF : iVF m) (hm0 : m ≠ iVFZero) (hmrv : iRv m ∈ S)
    (hnot : ¬ M5L.Separated S m) :
    ∃ x y : M, iVF x ∧ iVF y ∧ x ∈ S ∧ y ∈ S ∧ x ≠ iVFZero ∧ y ≠ iVFZero ∧
      Transc.Cls (iRVMul (iRv m) (iRv x)) (iRv y) := by
  obtain ⟨u, u', huS, hu'S, hu, hu', hu0, hu'0, hcls⟩ :=
    notSeparated_class_form hS hmVF hm0 hmrv hnot
  obtain ⟨x, hxS, hxVF, hxr⟩ | huz := hgen u huS hu
  · obtain ⟨y, hyS, hyVF, hyr⟩ | hu'z := hgen u' hu'S hu'
    · refine ⟨x, y, hxVF, hyVF, hxS, hyS, ?_, ?_, ?_⟩
      · intro hx0
        exact hu0 (by rw [← hxr, hx0, rv_zero_eq hM])
      · intro hy0
        exact hu'0 (by rw [← hyr, hy0, rv_zero_eq hM])
      · rw [← hxr, ← hyr] at hcls
        exact hcls
    · exact absurd hu'z hu'0
  · exact absurd huz hu0

/-- **The obstruction**: at the slot's hypotheses plus VF-generation, separation *fails* at every
degree `≥ 2` — so the paper's shape (`m^n = a` together with `vv(m^i) ∉ Γ(Ŝ)` for `0 < i < n`,
`n ≥ 2`) cannot be satisfied at `CaseNotSeparated`. -/
theorem not_separatedBelow_of_notSeparated {S : LRV.Substructure M} (hS : Assembly.Standing S)
    (hgen : Assembly.IsVFGen S) {m : M} (hmVF : iVF m) (hm0 : m ≠ iVFZero) (hmrv : iRv m ∈ S)
    (hnot : ¬ M5L.Separated S m) {n : ℕ} (hn : 2 ≤ n) :
    ¬ SeparatedBelow S m n := by
  intro hbelow
  obtain ⟨x, y, hxVF, hyVF, hxS, hyS, hx0, hy0, hcls⟩ :=
    notSeparated_vf_form hS hgen hmVF hm0 hmrv hnot
  refine hbelow 1 (by norm_num) (by omega) x y hxVF hyVF hxS hyS hx0 hy0 ?_
  rwa [transc_rvpow_one (rv_mem hM hmVF)]

/-- **The paper's `m^n = a` hypothesis shape**, exactly (`lift:divisible:hull`, `qe.tex:633`, with
the degree bound restricted to `n ≥ 2`): `m^n = a` is a nonzero `VF`-element of `S`, and
`vv(m^i) ∉ Γ(Ŝ)` for all `0 < i < n`.  (The paper's `e ∉ U(M)` conjunct is not needed for the
statement of the branch in the frozen encoding, where the slot's conclusion is uniform.) -/
def RootStepHyp (S : LRV.Substructure M) (m : M) : Prop :=
  ∃ n : ℕ, 2 ≤ n ∧ SeparatedBelow S m n ∧
    ∃ a : M, iVF a ∧ a ∈ S ∧ a ≠ iVFZero ∧ Transc.vpow m n = a

/-- **No `m^n = a` branch at the slot.**  The paper's Lemma-3.6 hypothesis is inconsistent with the
slot's own hypothesis under `Standing S` and VF-generation. -/
theorem not_rootStepHyp_of_notSeparated {S : LRV.Substructure M} (hS : Assembly.Standing S)
    (hgen : Assembly.IsVFGen S) {m : M} (hmVF : iVF m) (hm0 : m ≠ iVFZero) (hmrv : iRv m ∈ S)
    (hnot : ¬ M5L.Separated S m) : ¬ RootStepHyp S m := by
  rintro ⟨n, hn, hbelow, -⟩
  exact not_separatedBelow_of_notSeparated hS hgen hmVF hm0 hmrv hnot hn hbelow

/-- **The paper's `m^n = a` hypothesis forces the not-separated branch** (so the branch's
hypothesis is not vacuous, and — with §3 — the *unrestricted* `Separated` is incompatible with the
paper's own shape: the finite range `0 < i < n` is forced). -/
theorem not_separated_of_vpow {S : LRV.Substructure M} {m a : M} (hmVF : iVF m) (haVF : iVF a)
    (haS : a ∈ S) (ha0 : a ≠ iVFZero) {n : ℕ} (hn : 0 < n) (hpow : Transc.vpow m n = a) :
    ¬ M5L.Separated S m := by
  intro hsep
  have hrel : Transc.Cls (iRVMul (Transc.rvpow (iRv m) n) (iRv a)) (iRv (iVFMul a a)) := by
    rw [← Transc.rv_vpow hM hmVF n, hpow, ← Transfer.rv_mul_hom_of_model hM haVF haVF]
    exact Transc.cls_refl hM (rv_mem hM (Transfer.vf_mul_mem hM haVF haVF))
  have haaS : iVFMul a a ∈ S := vfMul_mem_sub S haS haS
  exact hsep n hn a (iVFMul a a) haVF (Transfer.vf_mul_mem hM haVF haVF) haS haaS ha0
    (GammaDiv.vf_mul_ne_zero haVF haVF ha0 ha0) hrel

/-- **No `m^n = a` branch at *any* `Standing` VF-generated `S`**: combining
`not_separated_of_vpow` (the shape forces `¬ Separated`) with the obstruction above gives that the
paper's `lift:divisible:hull` hypotheses are *internally inconsistent* with `Standing S` once `S` is
VF-generated — no slot hypothesis is needed.  This is the sharp form of the statement that the
divisible-hull step is not available in the regime `Γ(S)` divisible. -/
theorem not_rootStepHyp_of_standing {S : LRV.Substructure M} (hS : Assembly.Standing S)
    (hgen : Assembly.IsVFGen S) {m : M} (hmVF : iVF m) (hmrv : iRv m ∈ S) :
    ¬ RootStepHyp S m := by
  rintro ⟨n, hn, hbelow, a, haVF, haS, ha0, hpow⟩
  have hm0 : m ≠ iVFZero := by
    intro hm0
    have hzero : Transc.vpow m n = iVFZero := by
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      rw [hm0]
      show iVFMul (Transc.vpow (iVFZero : M) k) iVFZero = iVFZero
      exact RVCalc.vf_mul_zero hM
        (Transc.iVF_vpow hM (Transfer.vf_zero_mem (M := M) hM) k)
    rw [hzero] at hpow
    exact ha0 hpow.symm
  exact not_separatedBelow_of_notSeparated hS hgen hmVF hm0 hmrv
    (not_separated_of_vpow hmVF haVF haS ha0 (by omega) hpow) hn hbelow

/-- **The unit half of the obstruction** (`e ∈ U(M)` is Lemmas 3.4/3.6).  For a *unit* `m`,
separation fails at degree one (`x = y = 1`, both in `S` as constants), so no
`SeparatedBelow S m n` with `n ≥ 2` — with **no** hypothesis on `S`.  Together with
`not_rootStepHyp_of_standing` this excludes the `m^n = a` shape at every point of
`CaseNotSeparated` (units unconditionally, non-units at VF-generated `Standing S`). -/
theorem not_separatedBelow_of_units {S : LRV.Substructure M} {m : M} (hmVF : iVF m)
    (hu : iUnits (iRv m)) {n : ℕ} (hn : 1 < n) : ¬ SeparatedBelow S m n := by
  intro hbelow
  have hm0 : iRv m ≠ iRVZero := GammaGroup.units_ne_zero hu
  have hcls : Transc.Cls (iRVMul (Transc.rvpow (iRv m) 1) (iRv (iVFOne : M)))
      (iRv (iVFOne : M)) := by
    rw [transc_rvpow_one (rv_mem hM hmVF), rv_one hM,
      MulNormalForm.rv_mul_one_right hM (rv_mem hM hmVF)]
    obtain ⟨h1, h2⟩ := (RVCalc.units_iff_le_one hM (rv_mem hM hmVF) hm0).mp hu
    exact ⟨h2, h1⟩
  exact hbelow 1 (by norm_num) (by omega) iVFOne iVFOne
    (Transfer.vf_one_mem (M := M) hM) (Transfer.vf_one_mem (M := M) hM)
    (vfOne_mem_sub S) (vfOne_mem_sub S)
    (fun h => RVCalc.vf_zero_ne_one hM h.symm) (fun h => RVCalc.vf_zero_ne_one hM h.symm) hcls

/-- **The `m^n = a` shape is absent at the unit points of `CaseNotSeparated`.** -/
theorem not_rootStepHyp_of_unit {S : LRV.Substructure M} {m : M} (hmVF : iVF m)
    (hu : iUnits (iRv m)) : ¬ RootStepHyp S m := by
  rintro ⟨n, hn, hbelow, -⟩
  exact not_separatedBelow_of_units hmVF hu (by omega) hbelow

/-! ## 3c. The perturbation obstruction: `ResidualClasses` is *not* derivable at the slot

The paper's one-element step is applied to `e` with `rv(e) ∈ RV(S) ∖ RV(Ŝ)`, i.e. the *class* of `e`
is not the class of any `VF`-element of `S` (`RVNewOverVF` below).  The frozen slot only assumes
`iRv m ∈ S`, which also admits `m = y + ε` with `y ∈ S ∩ VF` and `ε` of a value class that is *new*:
then `rv m = rv y` is old, `m ∉ S`, but the closure of `S ∪ {m}` contains `ε`, whose class is not an
old class.  So the paper's Claim (⋆) (`ResidualClasses` / `RV`-control) is *false* on that
sub-regime — no per-element class-control interface can close `CaseNotSeparated`; the slot can only
be reached by realisation (a total extension, `Input5R`). -/

/-- The paper's `rv(e) ∈ RV(S) ∖ RV(Ŝ)`: the class of `m` is not the class of any `VF`-element of
`S`.  (`Separated S m` implies it — `separated_imp_RVNewOverVF` below — but `CaseNotSeparated` does
not.) -/
def RVNewOverVF (S : LRV.Substructure M) (m : M) : Prop :=
  ∀ y : M, y ∈ S → iVF y → ¬ Transc.Cls (iRv m) (iRv y)

/-- The paper's setting (`RVNewOverVF`) is a consequence of separation. -/
theorem separated_imp_RVNewOverVF {S : LRV.Substructure M} {m : M} (hmVF : iVF m)
    (hm0 : m ≠ iVFZero) (hsep : M5L.Separated S m) : RVNewOverVF S m := by
  intro y hyS hyVF hcls
  by_cases hy0 : y = iVFZero
  · -- `rv y = 0` cannot be class-equal to a nonzero `rv m`
    have hmrn : iRv m ≠ iRVZero := rv_mem_ne hmVF hm0
    refine hmrn ?_
    rw [hy0, rv_zero_eq hM] at hcls
    exact le_infty_eq hM (rv_mem hM hmVF) hcls.2
  · have h1 : Transc.rvpow (iRv m) 1 = iRv m := transc_rvpow_one (rv_mem hM hmVF)
    exact hsep 1 (by norm_num) iVFOne y (Transfer.vf_one_mem (M := M) hM) hyVF
      (vfOne_mem_sub S) hyS (fun h => RVCalc.vf_zero_ne_one hM h.symm) hy0
      (by rw [h1, rv_one hM, MulNormalForm.rv_mul_one_right hM (rv_mem hM hmVF)]; exact hcls)

/-- **The perturbation obstruction**: if `m` differs from an old `VF`-element `y ∈ S` by an element
whose class is not an old class, then **no** `T ⊇ S` containing `m` satisfies
`M5L.ResidualClasses S T` (the difference `m - y` is in `T`, and its class is new).  So
`caseNotSeparated_of_ResidualClasses`'s antecedent, and `NotSeparatedBranch`, are *sufficient
interfaces only*: they cannot be derived from the slot's hypotheses in this sub-regime. -/
theorem not_residualClasses_of_perturbation {S T : LRV.Substructure M} {m y : M}
    (hST : S ≤ T) (hmT : m ∈ T) (hyS : y ∈ S) (hmVF : iVF m) (hyVF : iVF y)
    (heps0 : iVFAdd m (iVFNeg y) ≠ iVFZero)
    (hnew : ∀ s : M, s ∈ S → iRV s → ¬ Transc.Cls (iRv (iVFAdd m (iVFNeg y))) s) :
    ¬ M5L.ResidualClasses S T := by
  intro hres
  have hyT : y ∈ T := hST hyS
  have hneg : iVFNeg y ∈ T := T.fun_mem Fn.vfNeg ![y] (by
    intro i; fin_cases i; simpa using hyT)
  have hepsT : iVFAdd m (iVFNeg y) ∈ T := T.fun_mem Fn.vfAdd ![m, iVFNeg y] (by
    intro i
    fin_cases i
    · simpa using hmT
    · simpa using hneg)
  have hepsVF : iVF (iVFAdd m (iVFNeg y)) :=
    Transfer.vf_add_mem hM hmVF (Transfer.vf_neg_mem hM hyVF)
  have hrvT : iRv (iVFAdd m (iVFNeg y)) ∈ T := M5L.rv_mem_sub T hepsT
  obtain ⟨s, hsS, hsRV, hcls⟩ := hres _ hrvT (rv_mem hM hepsVF)
  exact hnew s hsS hsRV hcls

/-- **The perturbation point satisfies the slot's `rv` hypothesis.**  If `y ∈ S ∩ VF` strictly
dominates `ε` (`vv y < vv ε`), then `rv (y + ε)` is class-equal to `rv y`, hence `iRv (y + ε) ∈ S`
under `KEqTop S`.  So the points where `not_residualClasses_of_perturbation` bites are genuine
instances of `CaseNotSeparated`'s hypothesis `iRv m ∈ S` (with `m = y + ε`, `m - y = ε` the new
class). -/
theorem perturbation_rv_mem {S : LRV.Substructure M} (hK : Assembly.KEqTop S) {y ε : M}
    (hyS : y ∈ S) (hyVF : iVF y) (heVF : iVF ε) (hle : Transc.VLe y ε)
    (hnle : ¬ Transc.VLe ε y) : iRv (iVFAdd y ε) ∈ S := by
  have hcls : Transc.Cls (iRv (iVFAdd y ε)) (iRv y) :=
    Transc.cls_rv_add_of_dominated hM hyVF heVF hle hnle
  exact M5L.mem_of_cls_mem hM hK (rv_mem hM (Transfer.vf_add_mem hM hyVF heVF))
    (rv_mem hM hyVF) hcls (M5L.rv_mem_sub S hyS)

/-! ## 4. The exact branch statement at the slot, and the chain into `CaseNotSeparated` -/

/-- **The normal form of `¬ Separated S m`** (§2): a class of `rv m` times an old class is an old
class — the `n = 1` instance of the paper's `t^n ∈ S₁`. -/
def RVOldClass (S : LRV.Substructure M) (m : M) : Prop :=
  ∃ u u' : M, u ∈ S ∧ u' ∈ S ∧ iRV u ∧ iRV u' ∧ u ≠ iRVZero ∧ u' ≠ iRVZero ∧
    Transc.Cls (iRVMul (iRv m) u) u'

/-- **The not-separated branch at the slot, exact statement.**  Hypothesis: §2's normal form of
`¬ Separated S m` (provably implied by it under `Standing S`; and *strictly* the shape the slot
has — §3).  Conclusion: the extension with the tree's `Γ`-class control `M5L.ResidualClasses S T`,
which is what `M5L.standing_of_ClassControl` turns into `Standing T`. -/
def NotSeparatedBranch : Prop :=
  ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N), Assembly.Standing S → ∀ m : M, iVF m → iRv m ∈ S →
    RVOldClass S m →
      ∃ (T : LRV.Substructure M) (g : T ↪[LRV] N) (hST : S ≤ T),
        (∀ x : S, g ⟨(x : M), hST x.2⟩ = f x) ∧ m ∈ T ∧ M5L.ResidualClasses S T

/-- **The slot from its exact branch statement.** -/
theorem caseNotSeparated_of_branch (hb : NotSeparatedBranch (M := M) (N := N)) :
    M4Cases.CaseNotSeparated (M := M) (N := N) := by
  intro S f hS m hmVF hmrv hnot
  by_cases hm0 : m = iVFZero
  · refine ⟨S, f, le_rfl, fun _ => rfl, ?_, hS⟩
    rw [hm0]
    exact S.fun_mem Fn.vfZero (fun i => i.elim0) (fun i => i.elim0)
  · obtain ⟨T, g, hST, hagree, hmT, hcc⟩ :=
      hb S f hS m hmVF hmrv (notSeparated_class_form hS hmVF hm0 hmrv hnot)
    exact ⟨T, g, hST, hagree, hmT, M5L.standing_of_ClassControl hST hS hcc⟩

/-- **The not-separated slot in `Γ`-class form** — the exact mirror of the merged
`M4Cases.caseSeparated_of_ResidualClasses` for `CaseNotSeparated`. -/
theorem caseNotSeparated_of_ResidualClasses
    (h : ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N), Assembly.Standing S → ∀ m : M, iVF m →
      iRv m ∈ S → ¬ M5L.Separated S m →
      ∃ (T : LRV.Substructure M) (g : T ↪[LRV] N) (hST : S ≤ T),
        (∀ x : S, g ⟨(x : M), hST x.2⟩ = f x) ∧ m ∈ T ∧ M5L.ResidualClasses S T) :
    M4Cases.CaseNotSeparated (M := M) (N := N) := by
  intro S f hS m hmVF hmrv hnot
  obtain ⟨T, g, hST, hagree, hmT, hcc⟩ := h S f hS m hmVF hmrv hnot
  exact ⟨T, g, hST, hagree, hmT, M5L.standing_of_ClassControl hST hS hcc⟩

/-- **The not-separated slot in `RV`-control form** — the exact mirror of the merged
`M4Cases.caseSeparated_of_RVControl` for `CaseNotSeparated`. -/
theorem caseNotSeparated_of_RVControl
    (h : ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N), Assembly.Standing S → ∀ m : M, iVF m →
      iRv m ∈ S → ¬ M5L.Separated S m →
      ∃ (T : LRV.Substructure M) (g : T ↪[LRV] N) (hST : S ≤ T),
        (∀ x : S, g ⟨(x : M), hST x.2⟩ = f x) ∧ m ∈ T ∧
          (∀ y : M, y ∈ T → iRV y → y ∈ S)) :
    M4Cases.CaseNotSeparated (M := M) (N := N) := by
  intro S f hS m hmVF hmrv hnot
  obtain ⟨T, g, hST, hagree, hmT, hRV⟩ := h S f hS m hmVF hmrv hnot
  exact ⟨T, g, hST, hagree, hmT, M5.standing_of_RV_le hST hS hRV⟩

/-! ## 4b. The exponent-one form is *exactly* the slot's hypothesis -/

/-- **The slot's hypothesis in equality form**: multiplying `rv m` by an old class gives an old
class times a unit — the paper's `t^n ∈ S₁` shape at `n = 1` (`S₁ = ⟨K(M), RV(S)⟩`, and `K(M) ⊆ S`
is `KEqTop`). -/
theorem notSeparated_eq_form {S : LRV.Substructure M} (hS : Assembly.Standing S) {m : M}
    (hmVF : iVF m) (hm0 : m ≠ iVFZero) (hmrv : iRv m ∈ S) (hnot : ¬ M5L.Separated S m) :
    ∃ u u' c : M, u ∈ S ∧ u' ∈ S ∧ iRV u ∧ iRV u' ∧ iRV c ∧ iUnits c ∧
      iRVMul (iRv m) u = iRVMul u' c := by
  obtain ⟨u, u', huS, hu'S, hu, hu', hu0, hu'0, hcls⟩ :=
    notSeparated_class_form hS hmVF hm0 hmrv hnot
  obtain ⟨c, hc, hcU, heq⟩ :=
    M5L.cls_ratio_units hM (Transfer.rv_mul_mem hM (rv_mem hM hmVF) hu) hu' hcls hu'0
  exact ⟨u, u', c, huS, hu'S, hu, hu', hc, hcU, heq⟩

/-- **`RVOldClass` implies `¬ Separated`** (with VF-generation): §2's normal form is a violation at
exponent one. -/
theorem notSeparated_of_RVOldClass {S : LRV.Substructure M} (hgen : Assembly.IsVFGen S) {m : M}
    (hmVF : iVF m) (h : RVOldClass S m) : ¬ M5L.Separated S m := by
  obtain ⟨u, u', huS, hu'S, hu, hu', hu0, hu'0, hcls⟩ := h
  obtain ⟨x, hxS, hxVF, hxr⟩ | huz := hgen u huS hu
  · obtain ⟨y, hyS, hyVF, hyr⟩ | hu'z := hgen u' hu'S hu'
    · have hx0 : x ≠ iVFZero := by
        intro hx0
        exact hu0 (by rw [← hxr, hx0, rv_zero_eq hM])
      have hy0 : y ≠ iVFZero := by
        intro hy0
        exact hu'0 (by rw [← hyr, hy0, rv_zero_eq hM])
      have hcls' : Transc.Cls (iRVMul (iRv m) (iRv x)) (iRv y) := by
        rw [← hxr, ← hyr] at hcls
        exact hcls
      rw [not_separated_iff_exists_violates S m]
      refine ⟨1, by norm_num, x, y, hxVF, hyVF, hxS, hyS, hx0, hy0, ?_⟩
      rwa [transc_rvpow_one (rv_mem hM hmVF)]
    · exact absurd hu'z hu'0
  · exact absurd huz hu0

/-- **Exact characterization**: under `Standing S` and VF-generation, the slot's hypothesis
`¬ Separated S m` is *equivalent* to the exponent-one class form — so `NotSeparatedBranch`'s
hypothesis is the slot's own, and §3's obstruction says the `m^n = a` shape is not. -/
theorem notSeparated_iff_RVOldClass {S : LRV.Substructure M} (hS : Assembly.Standing S)
    (hgen : Assembly.IsVFGen S) {m : M} (hmVF : iVF m) (hm0 : m ≠ iVFZero) (hmrv : iRv m ∈ S) :
    ¬ M5L.Separated S m ↔ RVOldClass S m :=
  ⟨notSeparated_class_form hS hmVF hm0 hmrv, notSeparated_of_RVOldClass hgen hmVF⟩

/-! ## 4c. What the `Γ`-class machinery gives *inside* the branch: the monomial fragment -/

/-- `Cls` is a congruence for `iRVMul`. -/
theorem cls_mul {a b c d : M} (ha : iRV a) (hb : iRV b) (hc : iRV c) (hd : iRV d)
    (hab : Transc.Cls a b) (hcd : Transc.Cls c d) :
    Transc.Cls (iRVMul a c) (iRVMul b d) :=
  Transc.cls_trans hM (rv_mul_mem hM ha hc) (rv_mul_mem hM hb hc) (rv_mul_mem hM hb hd)
    (Transc.cls_mul_right hM ha hb hc hab) (Transc.cls_mul_left hM hc hd hb hcd)

/-- `(a b)(c d) = (a c)(b d)` in `RV^×` — the exchange law used to regroup powers. -/
theorem rv_mul_swap {a b c d : M} (ha : iRV a) (hb : iRV b) (hc : iRV c) (hd : iRV d) :
    iRVMul (iRVMul a b) (iRVMul c d) = iRVMul (iRVMul a c) (iRVMul b d) := by
  have hab : iRV (iRVMul a b) := rv_mul_mem hM ha hb
  have hac : iRV (iRVMul a c) := rv_mul_mem hM ha hc
  calc iRVMul (iRVMul a b) (iRVMul c d)
      = iRVMul (iRVMul (iRVMul a b) c) d := (rv_mul_assoc_of_model hM hab hc hd).symm
    _ = iRVMul (iRVMul (iRVMul a c) b) d := by
          rw [rv_mul_assoc_of_model hM ha hb hc, rv_mul_comm_of_model hM hb hc,
            ← rv_mul_assoc_of_model hM ha hc hb]
    _ = iRVMul (iRVMul a c) (iRVMul b d) := rv_mul_assoc_of_model hM hac hb hd

/-- **The class identity of the exponent-one branch**: `[m]^j + [u]^j = [u']^j` for every `j`. -/
theorem cls_rvpow_mul {m u u' : M} (hm : iRV (iRv m)) (hu : iRV u) (hu' : iRV u')
    (hcls : Transc.Cls (iRVMul (iRv m) u) u') (j : ℕ) :
    Transc.Cls (iRVMul (Transc.rvpow (iRv m) j) (Transc.rvpow u j)) (Transc.rvpow u' j) := by
  induction j with
  | zero =>
      show Transc.Cls (iRVMul iRVOne iRVOne) iRVOne
      rw [MulNormalForm.rv_mul_one_all hM (Transfer.rv_one_mem (M := M) hM)]
      exact Transc.cls_refl hM (Transfer.rv_one_mem (M := M) hM)
  | succ j ih =>
      have hL : iRVMul (Transc.rvpow (iRv m) (j + 1)) (Transc.rvpow u (j + 1))
          = iRVMul (iRVMul (Transc.rvpow (iRv m) j) (Transc.rvpow u j))
              (iRVMul (iRv m) u) := by
        show iRVMul (iRVMul (Transc.rvpow (iRv m) j) (iRv m)) (iRVMul (Transc.rvpow u j) u)
          = iRVMul (iRVMul (Transc.rvpow (iRv m) j) (Transc.rvpow u j)) (iRVMul (iRv m) u)
        exact rv_mul_swap (Transc.iRV_rvpow hM hm j) hm (Transc.iRV_rvpow hM hu j) hu
      rw [hL]
      exact cls_mul (rv_mul_mem hM (Transc.iRV_rvpow hM hm j) (Transc.iRV_rvpow hM hu j))
        (Transc.iRV_rvpow hM hu' j) (rv_mul_mem hM hm hu) hu' ih hcls

/-- `rvpow` of an `RV`-element of `S` stays in `S`. -/
theorem rvpow_mem_sub_of_mem (S : LRV.Substructure M) {e : M} (heS : e ∈ S) (j : ℕ) :
    Transc.rvpow e j ∈ S := by
  induction j with
  | zero => exact M5L.rvOne_mem_sub S
  | succ k ih =>
      show iRVMul (Transc.rvpow e k) e ∈ S
      exact M5L.rvMul_mem_sub S ih heS

/-- **The monomial fragment of the class control in the exponent-one branch.**  For every monomial
`b · m^j` (`b ∈ S ∩ VF`) the class of `rv (b · m^j)` *times the fixed old factor* `(rv u)^j` is the
class of an element of `S`.  The factor `(rv u)^j` is exactly the obstruction to
`M5L.ResidualClasses`: removing it needs an inverse of an old class, which `L_RV` has no symbol for
(`QE/M5L34_36.lean`'s documented residual). -/
theorem monomial_class_control {S : LRV.Substructure M} {m u u' : M} (hmVF : iVF m)
    (huS : u ∈ S) (hu'S : u' ∈ S) (hu : iRV u) (hu' : iRV u') (hu0 : u ≠ iRVZero)
    (hu'0 : u' ≠ iRVZero) (hcls : Transc.Cls (iRVMul (iRv m) u) u') {b : M} (hbVF : iVF b)
    (hbS : b ∈ S) (hb0 : b ≠ iVFZero) (j : ℕ) :
    ∃ s : M, s ∈ S ∧ iRV s ∧ s ≠ iRVZero ∧
      Transc.Cls (iRVMul (iRv (iVFMul b (Transc.vpow m j))) (Transc.rvpow u j)) s := by
  have hm : iRV (iRv m) := rv_mem hM hmVF
  have h1 := cls_rvpow_mul (m := m) hm hu hu' hcls j
  have h2 : Transc.Cls
      (iRVMul (iRv b) (iRVMul (Transc.rvpow (iRv m) j) (Transc.rvpow u j)))
      (iRVMul (iRv b) (Transc.rvpow u' j)) :=
    Transc.cls_mul_left hM (rv_mul_mem hM (Transc.iRV_rvpow hM hm j) (Transc.iRV_rvpow hM hu j))
      (Transc.iRV_rvpow hM hu' j) (rv_mem hM hbVF) h1
  have h3 : iRVMul (iRv b) (iRVMul (Transc.rvpow (iRv m) j) (Transc.rvpow u j))
      = iRVMul (iRv (iVFMul b (Transc.vpow m j))) (Transc.rvpow u j) := by
    rw [← rv_mul_assoc_of_model hM (rv_mem hM hbVF) (Transc.iRV_rvpow hM hm j)
      (Transc.iRV_rvpow hM hu j)]
    congr 1
    rw [← Transc.rv_vpow hM hmVF j]
    exact (Transfer.rv_mul_hom_of_model hM hbVF (Transc.iVF_vpow hM hmVF j)).symm
  refine ⟨iRVMul (iRv b) (Transc.rvpow u' j), ?_, ?_, ?_, ?_⟩
  · exact M5L.rvMul_mem_sub S (M5L.rv_mem_sub S hbS) (rvpow_mem_sub_of_mem S hu'S j)
  · exact Transfer.rv_mul_mem hM (rv_mem hM hbVF) (Transc.iRV_rvpow hM hu' j)
  · exact Transc.rv_mul_ne_zero hM (rv_mem hM hbVF) (Transc.iRV_rvpow hM hu' j)
      (rv_mem_ne hbVF hb0) (Transc.rvpow_ne_zero hM hu' hu'0 j)
  · rw [h3] at h2
    exact h2

/-- **Integration point**: the frozen `M4Cases.Cases` from the separated slot, the not-separated
branch in its exact (`k = 1`) form, and the new-`rv` slot.  With `M4Cases.oneStepVFP_of_cases` this
is the one-step `Assembly.OneStepVFP` at the pair. -/
theorem cases_of_branch (hsep : M4Cases.CaseSeparated (M := M) (N := N))
    (hnot : NotSeparatedBranch (M := M) (N := N))
    (hnew : M4Cases.CaseNewRV (M := M) (N := N)) : M4Cases.Cases (M := M) (N := N) where
  separated := hsep
  notSeparated := caseNotSeparated_of_branch hnot
  newRV := hnew

/-- **The two routes, combined.**  The paper-shaped branch (with the paper's `RVNewOverVF` conjunct,
i.e. `rv m ∉ rv(VF(S))`, which `Separated` implies) closes the paper's setting; the points *outside*
it (perturbations of old elements, where `ResidualClasses` is impossible by
`not_residualClasses_of_perturbation`) can only be closed by realising a **total** extension.  So
`CaseNotSeparated` follows from these two inputs — and this is the sharp form of the slot's
decomposition. -/
theorem caseNotSeparated_of_paper_branch_and_global
    (hbranch : ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N), Assembly.Standing S → ∀ m : M, iVF m →
      iRv m ∈ S → ¬ M5L.Separated S m → RVNewOverVF S m →
      ∃ (T : LRV.Substructure M) (g : T ↪[LRV] N) (hST : S ≤ T),
        (∀ x : S, g ⟨(x : M), hST x.2⟩ = f x) ∧ m ∈ T ∧ M5L.ResidualClasses S T)
    (hglob : ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N), ∃ g : M ↪[LRV] N,
      ∀ x : S, g (x : M) = f x) :
    M4Cases.CaseNotSeparated (M := M) (N := N) := by
  intro S f hS m hmVF hmrv hnot
  by_cases hnew : RVNewOverVF S m
  · obtain ⟨T, g, hST, hagree, hmT, hcc⟩ := hbranch S f hS m hmVF hmrv hnot hnew
    exact ⟨T, g, hST, hagree, hmT, M5L.standing_of_ClassControl hST hS hcc⟩
  · obtain ⟨g, hg⟩ := hglob S f
    exact ⟨⊤, g.domRestrict ⊤, fun _ _ => trivial, fun x => hg x, trivial,
      StandingTree.standing_top⟩

/-! ## 5. Stress tests -/

/-- **Non-degeneracy of §2's conclusion**: it is inhabited at `u = 1`, `u' = rv m` — the conclusion
is not a hidden `False`, and the extra hypothesis `RVOldClass S m` of `NotSeparatedBranch` is
satisfiable at every slot instance with `m ≠ 0` and `iRv m ∈ S`. -/
theorem notSeparated_class_form_concl_witness {S : LRV.Substructure M} {m : M} (hmVF : iVF m)
    (hm0 : m ≠ iVFZero) (hmrv : iRv m ∈ S) :
    ∃ u u' : M, u ∈ S ∧ u' ∈ S ∧ iRV u ∧ iRV u' ∧ u ≠ iRVZero ∧ u' ≠ iRVZero ∧
      Transc.Cls (iRVMul (iRv m) u) u' := by
  refine ⟨iRVOne, iRv m, M5L.rvOne_mem_sub S, hmrv, Transfer.rv_one_mem (M := M) hM,
    rv_mem hM hmVF, RVCalc.rv_one_ne_zero hM, rv_mem_ne hmVF hm0, ?_⟩
  rw [MulNormalForm.rv_mul_one_right hM (rv_mem hM hmVF)]
  exact Transc.cls_refl hM (rv_mem hM hmVF)

/-- **`Separated` implies `m ∉ S`**: taking the witnesses `x = 1`, `y = m` gives a violation at
degree one.  So the separated slot only ever applies to genuinely new elements, and the case split's
first branch (`m ∈ S`) is disjoint from both case hypotheses. -/
theorem separated_imp_not_mem {S : LRV.Substructure M} {m : M} (hmVF : iVF m) (hm0 : m ≠ iVFZero)
    (hsep : M5L.Separated S m) : m ∉ S := by
  intro hmS
  have h1 : Transc.rvpow (iRv m) 1 = iRv m := transc_rvpow_one (rv_mem hM hmVF)
  have hrel : Transc.Cls (iRVMul (Transc.rvpow (iRv m) 1) (iRv (iVFOne : M))) (iRv m) := by
    rw [h1, rv_one hM, MulNormalForm.rv_mul_one_right hM (rv_mem hM hmVF)]
    exact Transc.cls_refl hM (rv_mem hM hmVF)
  exact hsep 1 (by norm_num) iVFOne m (Transfer.vf_one_mem (M := M) hM) hmVF
    (vfOne_mem_sub S) hmS (fun h => RVCalc.vf_zero_ne_one hM h.symm) hm0 hrel

/-- **The slot's hypothesis is satisfiable**: at `S = ⊤` every nonzero element is *not* separated
(`x = 1`, `y = m`).  So `CaseNotSeparated` is not a vacuous implication. -/
theorem notSeparated_top {m : M} (hmVF : iVF m) (hm0 : m ≠ iVFZero) :
    ¬ M5L.Separated (⊤ : LRV.Substructure M) m :=
  fun hsep => separated_imp_not_mem hmVF hm0 hsep trivial

/-- **The slot is non-vacuous**: at `S = ⊤` all the slot's hypotheses (`Standing`, `iVF m`,
`iRv m ∈ S`, `¬ Separated`) hold simultaneously, for every `m ≠ 0` — and `Standing ⊤` is a theorem
of the tree (`StandingTree.standing_top`). -/
theorem caseNotSeparated_hyp_satisfiable {m : M} (hmVF : iVF m) (hm0 : m ≠ iVFZero) :
    Assembly.Standing (⊤ : LRV.Substructure M) ∧ iVF m ∧ iRv m ∈ (⊤ : LRV.Substructure M) ∧
      ¬ M5L.Separated (⊤ : LRV.Substructure M) m :=
  ⟨StandingTree.standing_top, hmVF, trivial, notSeparated_top hmVF hm0⟩

end SpecialTransformations.Milestone0.Case35

/-! ## Axiom audit -/

#print axioms SpecialTransformations.Milestone0.Case35.separated_iff_forall_separatedBelow
#print axioms SpecialTransformations.Milestone0.Case35.exists_minimal_violation
#print axioms SpecialTransformations.Milestone0.Case35.transc_rvpow_one
#print axioms SpecialTransformations.Milestone0.Case35.transc_rvpow_eq_rvPow
#print axioms SpecialTransformations.Milestone0.Case35.gv_pow
#print axioms SpecialTransformations.Milestone0.Case35.gammaMk_pow_of_rvPow_eq_mul_unit
#print axioms SpecialTransformations.Milestone0.Case35.notSeparated_class_form
#print axioms SpecialTransformations.Milestone0.Case35.notSeparated_mul_mem
#print axioms SpecialTransformations.Milestone0.Case35.notSeparated_vf_form
#print axioms SpecialTransformations.Milestone0.Case35.not_separatedBelow_of_notSeparated
#print axioms SpecialTransformations.Milestone0.Case35.not_rootStepHyp_of_notSeparated
#print axioms SpecialTransformations.Milestone0.Case35.not_rootStepHyp_of_standing
#print axioms SpecialTransformations.Milestone0.Case35.not_separatedBelow_of_units
#print axioms SpecialTransformations.Milestone0.Case35.not_rootStepHyp_of_unit
#print axioms SpecialTransformations.Milestone0.Case35.separated_imp_RVNewOverVF
#print axioms SpecialTransformations.Milestone0.Case35.not_residualClasses_of_perturbation
#print axioms SpecialTransformations.Milestone0.Case35.perturbation_rv_mem
#print axioms SpecialTransformations.Milestone0.Case35.caseNotSeparated_of_branch
#print axioms SpecialTransformations.Milestone0.Case35.caseNotSeparated_of_ResidualClasses
#print axioms SpecialTransformations.Milestone0.Case35.caseNotSeparated_of_RVControl
#print axioms SpecialTransformations.Milestone0.Case35.cases_of_branch
#print axioms SpecialTransformations.Milestone0.Case35.caseNotSeparated_of_paper_branch_and_global
#print axioms SpecialTransformations.Milestone0.Case35.notSeparated_class_form_concl_witness
#print axioms SpecialTransformations.Milestone0.Case35.not_separated_of_vpow
#print axioms SpecialTransformations.Milestone0.Case35.separated_imp_not_mem
#print axioms SpecialTransformations.Milestone0.Case35.notSeparated_eq_form
#print axioms SpecialTransformations.Milestone0.Case35.notSeparated_of_RVOldClass
#print axioms SpecialTransformations.Milestone0.Case35.notSeparated_iff_RVOldClass
#print axioms SpecialTransformations.Milestone0.Case35.cls_rvpow_mul
#print axioms SpecialTransformations.Milestone0.Case35.monomial_class_control
#print axioms SpecialTransformations.Milestone0.Case35.notSeparated_top
#print axioms SpecialTransformations.Milestone0.Case35.caseNotSeparated_hyp_satisfiable
