/-
**Γ-divisibility API (direction f3).**

`Γ(M) = RV(M)^× / K^×(M)` is the value group of a model of `Axioms.ACVF`
(`QE/GammaGroup.lean`: `GammaOf M` with `CommGroup` + `LinearOrder` + `IsOrderedMonoid`).
This file proves that it is **divisible as an ordered abelian group**, hypothesis-free.

The frozen tree has divisibility only in the *substructure* form `Assembly.GammaDivisible S`
(a statement about `rvPow u n = t · c` with `c ∈ K^×`), proved at `S = ⊤` by
`StandingTree.gammaDivisible_top`.  The work here is the transport:

* §1  powers in `RV ∖ {0}` compute as `Assembly.rvPow`, and `gammaMk` is a monoid map;
* §2  `Assembly.GammaDivisible ⊤` ⟹ Γ is `RootableBy ℕ` (= divisible);
* §3  the converse, so that the frozen sentence *is* the abstract divisibility statement;
* §4  the hypothesis-free theorem plus the `ℤ`- and order-strengthened forms;
* §5  the bridge from `M5Ledger.GammaEq`/`GammaHullInitial` to the `GammaOf` quotient.

Stress tests are in §6 (`n = 0` refutation, reflexivity of the hull clamp, …).
-/
import GammaGroup
import StandingHull
import M5Ledger

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
open SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.GammaGroup

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace SpecialTransformations.Milestone0.GammaDiv

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-! ### §0 A named constructor

`RVStar M` is a `def` of `Subtype`, so a `⟨·, proof, proof⟩` literal inside a statement
elaborates with the proof components visible, and rewriting *inside* such a literal then
fails (`motive is not type correct`) because the two proof components differ by proof
irrelevance only.  Naming the constructor and the identity `mkR a.1 a.2.1 a.2.2 = a`
avoids every such rewrite. -/

/-- `u` as an element of `RV ∖ {0}`. -/
abbrev mkR (u : M) (hu : iRV u) (hu0 : u ≠ iRVZero) : RVStar M := ⟨u, hu, hu0⟩

/-- Its value. -/
@[simp] theorem mkR_val (u : M) (hu : iRV u) (hu0 : u ≠ iRVZero) : (mkR u hu hu0).1 = u := rfl

/-- Every `RV ∖ {0}` element is `mkR` of its own data. -/
@[simp] theorem mkR_self (a : RVStar M) : mkR a.1 a.2.1 a.2.2 = a := Subtype.ext rfl

/-- `gammaMk` only sees the value, so equal values give equal classes. -/
theorem gammaMk_congr {x y : M} (hx : iRV x) (hx0 : x ≠ iRVZero) (hy : iRV y)
    (hy0 : y ≠ iRVZero) (h : x = y) : gammaMk (mkR x hx hx0) = gammaMk (mkR y hy hy0) := by
  subst h
  rfl

/-! ### §1 Powers in `RV ∖ {0}` and the monoid map `gammaMk` -/

/-- `Assembly.rvPow` keeps `RV`-elements in the `RV` sort. -/
theorem rvPow_mem {x : M} (hx : iRV x) (n : ℕ) : iRV (Assembly.rvPow x n) := by
  rw [M8Hull.rvPow_bridge]
  exact MulNormalForm.rvPow_mem hM hx n

/-- `Assembly.rvPow` of a nonzero element stays nonzero. -/
theorem rvPow_ne_zero {x : M} (hx : iRV x) (hx0 : x ≠ iRVZero) (n : ℕ) :
    Assembly.rvPow x n ≠ iRVZero := by
  rw [M8Hull.rvPow_bridge]
  exact M8Hull.rvPow_ne_zero hx hx0 n

/-- **Powers in `RV ∖ {0}` compute as `Assembly.rvPow`.**  This is the only computation
rule needed to move between the frozen `rvPow` vocabulary and `Γ`'s group structure. -/
theorem rvStar_pow_val (a : RVStar M) (n : ℕ) : (a ^ n).1 = Assembly.rvPow a.1 n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ]
    show iRVMul (a ^ k).1 a.1 = Assembly.rvPow a.1 (k + 1)
    rw [ih]
    rfl

/-- The value of `u ^ n` in `RV ∖ {0}`, packaged as an element. -/
abbrev rvStarPow (a : RVStar M) (n : ℕ) : RVStar M :=
  mkR (Assembly.rvPow a.1 n) (rvPow_mem a.2.1 n) (rvPow_ne_zero a.2.1 a.2.2 n)

/-- `a ^ n` is `rvPow` on values. -/
theorem rvStar_pow_eq (a : RVStar M) (n : ℕ) : a ^ n = rvStarPow a n :=
  Subtype.ext (rvStar_pow_val a n)

/-- **`gammaMk` is a monoid map**: the quotient map `RV ∖ {0} → Γ` sends powers to powers.
(The `ℕ`-power form of `gammaMk_mul` / `gammaMk_one_eq`.) -/
theorem gammaMk_pow (a : RVStar M) (n : ℕ) : gammaMk a ^ n = gammaMk (a ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero, gammaMk_one_eq]
  | succ k ih => rw [pow_succ, pow_succ, ih, gammaMk_mul]

/-- **The class of `u ^ n` in `Γ`, written through the frozen `rvPow`.** -/
theorem gammaMk_rvPow (a : RVStar M) (n : ℕ) :
    gammaMk a ^ n = gammaMk (rvStarPow a n) := by
  rw [gammaMk_pow, rvStar_pow_eq]

/-! ### §2 `Assembly.GammaDivisible ⊤` gives divisibility of `Γ` -/

/-- A unit, as an element of `RV ∖ {0}`. -/
abbrev rvStarOfUnit {c : M} (hc : iUnits c) : RVStar M :=
  mkR c (Jm2.iRV_of_inK (Or.inl hc)) (units_ne_zero hc)

/-- **The transport `Γ`-divisibility ⟸ frozen `Γ`-divisibility at `⊤`.**  The residue factor
`c` with `rvPow u n = t · c` is a unit, hence is `1` in `Γ`. -/
theorem exists_gamma_root_of_gammaDivisible_top
    (hdiv : Assembly.GammaDivisible (⊤ : LRV.Substructure M)) (a : GammaOf M) {n : ℕ}
    (hn : 1 ≤ n) : ∃ b : GammaOf M, b ^ n = a := by
  obtain ⟨t, rfl⟩ := gammaMk_surjective a
  obtain ⟨u, c, -, hu, hu0, -, hcu, heq⟩ := hdiv t.1 (trivial) t.2.1 t.2.2 n hn
  have hcrv : iRV c := Jm2.iRV_of_inK (Or.inl hcu)
  have hc0 : c ≠ iRVZero := units_ne_zero hcu
  refine ⟨gammaMk (mkR u hu hu0), ?_⟩
  rw [gammaMk_rvPow]
  -- the value `rvPow u n` is `iRVMul t c`
  rw [gammaMk_congr (rvPow_mem hu n) (rvPow_ne_zero hu hu0 n)
    (Transfer.rv_mul_mem hM t.2.1 hcrv) (rvStar_mul_nonzero t.2 ⟨hcrv, hc0⟩) heq]
  -- and `t · c` is `t` in `Γ`, because `c` is a unit
  have hprod : (mkR (iRVMul t.1 c) (Transfer.rv_mul_mem hM t.2.1 hcrv)
      (rvStar_mul_nonzero t.2 ⟨hcrv, hc0⟩) : RVStar M) = t * rvStarOfUnit hcu :=
    Subtype.ext rfl
  have hone : gammaMk (rvStarOfUnit hcu) = 1 := (gammaMk_eq_one_iff_units).mpr hcu
  rw [hprod, gammaMk_mul, hone, mul_one]

/-! ### §3 The converse: divisibility of `Γ` gives `Assembly.GammaDivisible ⊤` -/

/-- **The converse transport.**  If every element of `Γ` has an `n`-th root then the frozen
divisibility sentence holds at `⊤`: a root `[u]` of `[t]` differs from `t`'s own class by a
unit, and that unit is the residue factor `c` of `Assembly.GammaDivisible`. -/
theorem gammaDivisible_top_of_forall_root
    (h : ∀ (n : ℕ), 1 ≤ n → ∀ a : GammaOf M, ∃ b : GammaOf M, b ^ n = a) :
    Assembly.GammaDivisible (⊤ : LRV.Substructure M) := by
  intro t _ hrv ht0 n hn
  obtain ⟨b, hb⟩ := h n hn (gammaMk (mkR t hrv ht0))
  obtain ⟨u, rfl⟩ := gammaMk_surjective b
  -- `[u]^n = [t]`, so `uⁿ · t⁻¹` is a unit
  have hpow : gammaMk (rvStarPow u n) = gammaMk (mkR t hrv ht0) := by
    rw [← gammaMk_rvPow, hb]
  -- the residue factor
  set w : M := iRVMul (Assembly.rvPow u.1 n) (Transfer.iRVInv hM t) with hwdef
  have hwrv : iRV w :=
    Transfer.rv_mul_mem hM (rvPow_mem u.2.1 n) (Transfer.iRVInv_mem hM hrv)
  have hw0 : w ≠ iRVZero :=
    rvStar_mul_nonzero ⟨rvPow_mem u.2.1 n, rvPow_ne_zero u.2.1 u.2.2 n⟩
      ⟨Transfer.iRVInv_mem hM hrv, rvStar_inv_nonzero ⟨hrv, ht0⟩⟩
  have hunit : iUnits w := by
    have hkey : gammaMk (mkR w hwrv hw0) = 1 := by
      have hsplit : (mkR w hwrv hw0 : RVStar M) =
          rvStarPow u n * (mkR t hrv ht0 : RVStar M)⁻¹ := Subtype.ext rfl
      rw [hsplit, gammaMk_mul, gammaMk_inv, hpow, mul_inv_cancel]
    exact (gammaMk_eq_one_iff_units).mp hkey
  refine ⟨u.1, w, trivial, u.2.1, u.2.2, trivial, hunit, ?_⟩
  -- `t · (uⁿ · t⁻¹) = uⁿ`
  show Assembly.rvPow u.1 n = iRVMul t w
  rw [hwdef, Transfer.rv_mul_comm_of_model hM hrv (Transfer.rv_mul_mem hM
      (rvPow_mem u.2.1 n) (Transfer.iRVInv_mem hM hrv)),
    Transfer.rv_mul_assoc_of_model hM (rvPow_mem u.2.1 n)
      (Transfer.iRVInv_mem hM hrv) hrv,
    Transfer.iRVInv_mul_cancel hM hrv ht0,
    Transfer.rv_mul_one_any_right (M := M) hM (rvPow_mem u.2.1 n)]

/-- **The frozen sentence is exactly the abstract divisibility statement.** -/
theorem gammaDivisible_top_iff_forall_root :
    Assembly.GammaDivisible (⊤ : LRV.Substructure M)
      ↔ ∀ (n : ℕ), 1 ≤ n → ∀ a : GammaOf M, ∃ b : GammaOf M, b ^ n = a :=
  ⟨fun hdiv n hn a => exists_gamma_root_of_gammaDivisible_top hdiv a (n := n) hn,
   gammaDivisible_top_of_forall_root⟩

/-! ### §4 The hypothesis-free theorem -/

/-- **`Γ(M)` is divisible**, for every model of `Axioms.ACVF`, with no named hypothesis:
`Assembly.GammaDivisible ⊤` is `StandingTree.gammaDivisible_top`, proved from the frozen
`rvPow`/divisibility side of `Axioms.ACVF` (`VF` is algebraically closed, `rv` is surjective
and multiplicative). -/
theorem gamma_divisible (n : ℕ) (hn : 1 ≤ n) (a : GammaOf M) : ∃ b : GammaOf M, b ^ n = a :=
  exists_gamma_root_of_gammaDivisible_top (StandingTree.gammaDivisible_top) a hn

/-- The textbook surjectivity form: `· ^ n` is onto `Γ` for every `n ≠ 0`. -/
theorem gamma_pow_surjective {n : ℕ} (hn : n ≠ 0) :
    Function.Surjective (fun a : GammaOf M => a ^ n) :=
  fun a => gamma_divisible n (Nat.one_le_iff_ne_zero.mpr hn) a


/-- **`Γ(M)` is rootable.**  Mathlib's `RootableBy` (the constructive form of divisibility);
recorded so that the group-theoretic API (`Group.rootableByIntOfRootableByNat`, …) applies. -/
noncomputable instance gammaOfRootableBy : RootableBy (GammaOf M) ℕ :=
  rootableByOfPowLeftSurj _ _ fun {n} hn => gamma_pow_surjective (n := n) hn

/-- **`Γ(M)` is `ℤ`-divisible** — the strictly stronger integral form: negative powers are
covered by inverting the root. -/
noncomputable instance gammaOfRootableByInt : RootableBy (GammaOf M) ℤ :=
  Group.rootableByIntOfRootableByNat (GammaOf M)

end SpecialTransformations.Milestone0.GammaDiv

namespace SpecialTransformations.Milestone0.GammaDiv

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-! ### §5 The bridge from `M5Ledger.GammaEq` / `GammaHullInitial` to the `GammaOf` quotient

`M5Ledger.GammaEq` and `M5Ledger.GammaHullInitial` (`QE/M5Ledger.lean` §2) are written in the
encoding's *representative* form: "`t` is `s · c` with `c` a unit" and "`tⁿ` is `s · c` with
`c` a unit".  Both `c`'s are exactly the statement `[t] = [s]` resp. `[t]ⁿ = [s]` in `Γ`, by
`gammaMk_eq_one_iff_units`; that is what the two `_iff_` theorems below record.  The quotient
forms are named `GammaEqQ` / `GammaHullInitialQ` so that downstream work can use them without
carrying the representative data. -/

/-- **`GammaEq` in the quotient.**  `Γ(T) ⊆ Γ(S)`: every value class of `T` is the class of an
element of `S`. -/
def GammaEqQ (S T : LRV.Substructure M) : Prop :=
  ∀ (t : M) (_ : t ∈ T) (hrv : iRV t) (ht0 : t ≠ iRVZero),
    ∃ (s : M) (_ : s ∈ S) (hsrv : iRV s) (hs0 : s ≠ iRVZero),
      gammaMk (mkR t hrv ht0) = gammaMk (mkR s hsrv hs0)

/-- **`GammaHullInitial` in the quotient.**  Every value class of `T` has a positive power in
(the image of) `Γ(S)` — "`Γ(T)` lies in the divisible hull of `Γ(S)`". -/
def GammaHullInitialQ (S T : LRV.Substructure M) : Prop :=
  ∀ (t : M) (_ : t ∈ T) (hrv : iRV t) (ht0 : t ≠ iRVZero),
    ∃ n : ℕ, 0 < n ∧ ∃ (s : M) (_ : s ∈ S) (hsrv : iRV s) (hs0 : s ≠ iRVZero),
      gammaMk (mkR t hrv ht0) ^ n = gammaMk (mkR s hsrv hs0)

/-- The residue factor times an `RV`-element, as a group element. -/
theorem mkR_mul_eq (s c : M) (hsrv : iRV s) (hs0 : s ≠ iRVZero) (hcrv : iRV c)
    (hc0 : c ≠ iRVZero) :
    (mkR (iRVMul s c) (Transfer.rv_mul_mem hM hsrv hcrv)
        (rvStar_mul_nonzero ⟨hsrv, hs0⟩ ⟨hcrv, hc0⟩) : RVStar M)
      = mkR s hsrv hs0 * mkR c hcrv hc0 :=
  Subtype.ext rfl

/-- The class of a unit is `1`. -/
theorem gammaMk_unit_eq_one {c : M} (hcu : iUnits c) : gammaMk (rvStarOfUnit hcu) = 1 :=
  (gammaMk_eq_one_iff_units).mpr hcu

/-- `rvStarPow` on `mkR` is `mkR` of `rvPow`. -/
theorem rvStarPow_mkR (t : M) (ht : iRV t) (ht0 : t ≠ iRVZero) (n : ℕ) :
    rvStarPow (mkR t ht ht0) n
      = mkR (Assembly.rvPow t n) (rvPow_mem ht n) (rvPow_ne_zero ht ht0 n) := rfl

/-- **`M5Ledger.GammaEq` is `Γ(T) ⊆ Γ(S)`.** -/
theorem gammaEq_iff_gammaMk (S T : LRV.Substructure M) :
    M5Ledger.GammaEq S T ↔ GammaEqQ (M := M) S T := by
  constructor
  · intro h t ht hrv ht0
    obtain ⟨s, c, hs, hsrv, hs0, hcu, heq⟩ := h t ht hrv ht0
    have hcrv : iRV c := Jm2.iRV_of_inK (Or.inl hcu)
    have hc0 : c ≠ iRVZero := units_ne_zero hcu
    refine ⟨s, hs, hsrv, hs0, ?_⟩
    rw [gammaMk_congr (hx := hrv) (hx0 := ht0) (hy := Transfer.rv_mul_mem hM hsrv hcrv)
      (hy0 := rvStar_mul_nonzero ⟨hsrv, hs0⟩ ⟨hcrv, hc0⟩) (h := heq.symm),
      mkR_mul_eq s c hsrv hs0 hcrv hc0, gammaMk_mul, gammaMk_unit_eq_one hcu, mul_one]
  · intro h t ht hrv ht0
    obtain ⟨s, hs, hsrv, hs0, heq⟩ := h t ht hrv ht0
    have hsrvinv : iRV (Transfer.iRVInv hM s) := Transfer.iRVInv_mem hM hsrv
    have hs0' : Transfer.iRVInv hM s ≠ iRVZero := rvStar_inv_nonzero ⟨hsrv, hs0⟩
    -- the residue factor `c = t · s⁻¹`
    have hcrv : iRV (iRVMul t (Transfer.iRVInv hM s)) :=
      Transfer.rv_mul_mem hM hrv hsrvinv
    have hc0 : iRVMul t (Transfer.iRVInv hM s) ≠ iRVZero :=
      rvStar_mul_nonzero ⟨hrv, ht0⟩ ⟨hsrvinv, hs0'⟩
    have hunit : iUnits (iRVMul t (Transfer.iRVInv hM s)) := by
      have hkey : gammaMk (mkR (iRVMul t (Transfer.iRVInv hM s)) hcrv hc0) = 1 := by
        have hsplit : (mkR (iRVMul t (Transfer.iRVInv hM s)) hcrv hc0 : RVStar M)
            = mkR t hrv ht0 * (mkR s hsrv hs0)⁻¹ := Subtype.ext rfl
        rw [hsplit, gammaMk_mul, gammaMk_inv, heq, mul_inv_cancel]
      exact (gammaMk_eq_one_iff_units).mp hkey
    refine ⟨s, iRVMul t (Transfer.iRVInv hM s), hs, hsrv, hs0, hunit, ?_⟩
    show iRVMul s (iRVMul t (Transfer.iRVInv hM s)) = t
    rw [Transfer.rv_mul_comm_of_model hM hrv hsrvinv,
      ← Transfer.rv_mul_assoc_of_model hM hsrv hsrvinv hrv,
      Transfer.rv_mul_inv_cancel_right hM hsrv hs0,
      Transfer.rv_mul_one_any (M := M) hM hrv]

/-- **`M5Ledger.GammaHullInitial` is "`Γ(T)` lies in the divisible hull of `Γ(S)`"**: every
value class of `T` has a positive power in `Γ(S)`. -/
theorem gammaHullInitial_iff_gammaMk_pow (S T : LRV.Substructure M) :
    M5Ledger.GammaHullInitial S T ↔ GammaHullInitialQ (M := M) S T := by
  constructor
  · intro h t ht hrv ht0
    obtain ⟨n, s, c, hn, hs, hsrv, hs0, hcu, heq⟩ := h t ht hrv ht0
    have hcrv : iRV c := Jm2.iRV_of_inK (Or.inl hcu)
    have hc0 : c ≠ iRVZero := units_ne_zero hcu
    refine ⟨n, hn, s, hs, hsrv, hs0, ?_⟩
    rw [gammaMk_rvPow, rvStarPow_mkR,
      gammaMk_congr (hx := rvPow_mem hrv n) (hx0 := rvPow_ne_zero hrv ht0 n)
        (hy := Transfer.rv_mul_mem hM hsrv hcrv)
        (hy0 := rvStar_mul_nonzero ⟨hsrv, hs0⟩ ⟨hcrv, hc0⟩) (h := heq),
      mkR_mul_eq s c hsrv hs0 hcrv hc0, gammaMk_mul, gammaMk_unit_eq_one hcu, mul_one]
  · intro h t ht hrv ht0
    obtain ⟨n, hn, s, hs, hsrv, hs0, heq⟩ := h t ht hrv ht0
    have hsrvinv : iRV (Transfer.iRVInv hM s) := Transfer.iRVInv_mem hM hsrv
    have hs0' : Transfer.iRVInv hM s ≠ iRVZero := rvStar_inv_nonzero ⟨hsrv, hs0⟩
    -- the residue factor `c = tⁿ · s⁻¹`
    have hcrv : iRV (iRVMul (Assembly.rvPow t n) (Transfer.iRVInv hM s)) :=
      Transfer.rv_mul_mem hM (rvPow_mem hrv n) hsrvinv
    have hc0 : iRVMul (Assembly.rvPow t n) (Transfer.iRVInv hM s) ≠ iRVZero :=
      rvStar_mul_nonzero ⟨rvPow_mem hrv n, rvPow_ne_zero hrv ht0 n⟩ ⟨hsrvinv, hs0'⟩
    have hunit : iUnits (iRVMul (Assembly.rvPow t n) (Transfer.iRVInv hM s)) := by
      have hkey : gammaMk (mkR (iRVMul (Assembly.rvPow t n) (Transfer.iRVInv hM s)) hcrv hc0)
          = 1 := by
        have hsplit : (mkR (iRVMul (Assembly.rvPow t n) (Transfer.iRVInv hM s)) hcrv hc0 :
            RVStar M) = rvStarPow (mkR t hrv ht0) n * (mkR s hsrv hs0)⁻¹ := Subtype.ext rfl
        rw [hsplit, gammaMk_mul, gammaMk_inv, ← gammaMk_rvPow, heq, mul_inv_cancel]
      exact (gammaMk_eq_one_iff_units).mp hkey
    refine ⟨n, s, iRVMul (Assembly.rvPow t n) (Transfer.iRVInv hM s), hn, hs, hsrv, hs0,
      hunit, ?_⟩
    show Assembly.rvPow t n = iRVMul s (iRVMul (Assembly.rvPow t n) (Transfer.iRVInv hM s))
    rw [Transfer.rv_mul_comm_of_model hM (rvPow_mem hrv n) hsrvinv,
      ← Transfer.rv_mul_assoc_of_model hM hsrv hsrvinv (rvPow_mem hrv n),
      Transfer.rv_mul_inv_cancel_right hM hsrv hs0,
      Transfer.rv_mul_one_any (M := M) hM (rvPow_mem hrv n)]

/-- **`GammaEq` implies `GammaHullInitial`** (the `n = 1` case): the hull clamp is genuinely the
weaker of the two, so `M5Ledger.DivisibilityStep`'s clamp does not duplicate `ResidueStep`'s
conclusion. -/
theorem gammaHullInitial_of_gammaEq {S T : LRV.Substructure M} (h : M5Ledger.GammaEq S T) :
    M5Ledger.GammaHullInitial S T := by
  intro t ht hrv ht0
  obtain ⟨s, c, hs, hsrv, hs0, hcu, heq⟩ := h t ht hrv ht0
  refine ⟨1, s, c, one_pos, hs, hsrv, hs0, hcu, ?_⟩
  show iRVMul (Assembly.rvPow t 0) t = iRVMul s c
  rw [show Assembly.rvPow t 0 = iRVOne from rfl,
    Transfer.rv_mul_one_any (M := M) hM hrv]
  exact heq.symm

/-- The quotient form of `gammaHullInitial_of_gammaEq`. -/
theorem gammaHullInitialQ_of_gammaEqQ {S T : LRV.Substructure M} (h : GammaEqQ S T) :
    GammaHullInitialQ S T := by
  intro t ht hrv ht0
  obtain ⟨s, hs, hsrv, hs0, heq⟩ := h t ht hrv ht0
  exact ⟨1, one_pos, s, hs, hsrv, hs0, by rw [pow_one, heq]⟩

/-! ### §6 Stress tests

The shipped statement is hypothesis-free, so the risks are (i) that the exponent side condition
`n ≥ 1` is doing real work, and (ii) that the statement has hidden size content.  Both are
settled below, together with the degenerate-witness checks for the §5 bridges. -/

/-- **Stress test (i): the side condition `n ≥ 1` cannot be dropped.**  If every element of `Γ`
had an `n`-th root for *every* `n : ℕ`, including `n = 0`, then `Γ` would be trivial — because
`b ^ 0 = 1` for every `b`.  So `1 ≤ n` in `gamma_divisible` is not removable. -/
theorem forall_root_including_zero_subsingleton
    (h : ∀ (n : ℕ) (a : GammaOf M), ∃ b : GammaOf M, b ^ n = a) :
    Subsingleton (GammaOf M) := by
  refine ⟨fun a b => ?_⟩
  obtain ⟨x, hx⟩ := h 0 a
  obtain ⟨y, hy⟩ := h 0 b
  rw [pow_zero] at hx hy
  rw [← hx, ← hy]

/-- **Stress test (i′): the same for the `0`-exponent of the frozen sentence.** -/
theorem gammaDivisible_top_no_zero (h : ∀ a : GammaOf M, ∃ b : GammaOf M, b ^ 0 = a) :
    Subsingleton (GammaOf M) :=
  forall_root_including_zero_subsingleton (M := M) fun n a => by
    cases n with
    | zero => exact h a
    | succ k => exact gamma_divisible (k + 1) (Nat.succ_le_succ (Nat.zero_le k)) a

/-- **Stress test (ii): no cardinality content.**  `Γ`'s divisibility holds at a model of
`Axioms.ACVF` of *every* cardinality `κ`, so it cannot force a size condition.  (Contrast
`M5Ledger.saturationRealization_forces_size`, where the size content `#M ≤ #N` is real.) -/
theorem gamma_divisible_at_any_cardinality (κ : Cardinal) (_hκ : Cardinal.mk M = κ) (n : ℕ)
    (hn : 1 ≤ n) (a : GammaOf M) : ∃ b : GammaOf M, b ^ n = a :=
  gamma_divisible n hn a

/-- **Stress test (ii′): the universal form**, with `M ⊨ Axioms.ACVF` the *only* hypothesis —
no saturation, no `#M ≤ #N`. -/
theorem gamma_divisible_universal (M' : Type) [LRV.Structure M'] [M' ⊨ Axioms.ACVF] :
    ∀ (n : ℕ), 1 ≤ n → ∀ a : GammaGroup.GammaOf M', ∃ b : GammaGroup.GammaOf M', b ^ n = a := by
  intro n hn a
  exact gamma_divisible n hn a

/-- **Stress test (iii): the hull clamp is satisfiable by a degenerate choice.**  `GammaEq S S`
holds trivially (residue `1`), and so `GammaHullInitial S S`.  The clamp alone therefore never
forbids anything; what forbids `T = ⊤` is its *conjunction* with `Assembly.GammaDivisible T`
(this is the mirror image of `M5Ledger`'s `bare_gammaDivisible_trivial`). -/
theorem gammaEq_self (S : LRV.Substructure M) : M5Ledger.GammaEq S S := by
  intro t ht hrv ht0
  exact ⟨t, iRVOne, ht, hrv, ht0, StandingTree.rv_one_units,
    Transfer.rv_mul_one_any_right (M := M) hM hrv⟩

/-- `GammaHullInitial S S` holds trivially: exponent `1`, residue `1`. -/
theorem gammaHullInitial_self (S : LRV.Substructure M) : M5Ledger.GammaHullInitial S S :=
  gammaHullInitial_of_gammaEq (gammaEq_self S)

/-- The quotient form: `Γ(S) ⊆ Γ(S)`. -/
theorem gammaEqQ_self (S : LRV.Substructure M) : GammaEqQ (M := M) S S :=
  (gammaEq_iff_gammaMk S S).mp (gammaEq_self S)

/-- The quotient form of the degenerate hull clamp at `T = S`. -/
theorem gammaHullInitialQ_self (S : LRV.Substructure M) : GammaHullInitialQ (M := M) S S :=
  (gammaHullInitial_iff_gammaMk_pow S S).mp (gammaHullInitial_self S)

/-! ### §7 Order addenda: the roots are canonical

Divisibility alone allows arbitrary root choices; in an *ordered* group the root is determined
by its sign, and in fact uniquely.  Both are proved here, so a downstream user can write
`a ^ (1/n)` as a definite element. -/

/-- `1 ≤ [u]` is `1 ≤ u` on representatives. -/
theorem one_le_gammaMk_iff {a : RVStar M} : (1 : GammaOf M) ≤ gammaMk a ↔ iLe iRVOne a.1 := by
  rw [show (1 : GammaOf M) = gammaMk (1 : RVStar M) from gammaMk_one_eq.symm, gammaMk_le_iff]
  rfl

/-- **The sign of the root.**  `1 ≤ a ^ n ↔ 1 ≤ a` for `n ≥ 1`: no positive power of an element
below `1` is above `1`.  This uses the frozen order calculus (`M8Hull.one_le_pow`,
`M8Hull.pow_le_self`) on representatives. -/
theorem one_le_pow_iff {a : GammaOf M} {n : ℕ} (hn : 1 ≤ n) :
    (1 : GammaOf M) ≤ a ^ n ↔ 1 ≤ a := by
  obtain ⟨u, rfl⟩ := gammaMk_surjective a
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have key : (1 : GammaOf M) ≤ gammaMk u ^ (k + 1)
      ↔ iLe iRVOne (Assembly.rvPow u.1 (k + 1)) := by
    rw [gammaMk_rvPow]
    exact one_le_gammaMk_iff
  have hkey' : (1 : GammaOf M) ≤ gammaMk u ↔ iLe iRVOne u.1 := one_le_gammaMk_iff
  rw [key, hkey']
  constructor
  · intro h
    by_contra hc
    have hle : iLe u.1 iRVOne := by
      rcases RVCalc.le_total_rv hM u.2.1 (Transfer.rv_one_mem (M := M) hM) with h' | h'
      · exact h'
      · exact absurd h' hc
    have hps : iLe (Assembly.rvPow u.1 (k + 1)) u.1 := by
      rw [M8Hull.rvPow_bridge]
      exact M8Hull.pow_le_self u.2.1 u.2.2 hle k
    exact hc (RVCalc.le_trans_rv hM (Transfer.rv_one_mem (M := M) hM)
      (rvPow_mem u.2.1 (k + 1)) u.2.1 h hps)
  · intro h
    rw [M8Hull.rvPow_bridge]
    exact M8Hull.one_le_pow u.2.1 u.2.2 h (k + 1)

/-- **`1` is the only element whose positive power is `1`** — the torsion-freeness an ordered
group has and a plain divisible group does not. -/
theorem pow_eq_one_iff {a : GammaOf M} {n : ℕ} (hn : 1 ≤ n) : a ^ n = 1 ↔ a = 1 := by
  constructor
  · intro h
    have h1 : (1 : GammaOf M) ≤ a := (one_le_pow_iff hn).mp (le_of_eq h.symm)
    have h2 : (1 : GammaOf M) ≤ a⁻¹ := by
      rw [← one_le_pow_iff (a := a⁻¹) hn, inv_pow, h, inv_one]
    have h3 : a ≤ 1 := by
      have hstep := gamma_mul_le_mul_left (1 : GammaOf M) a⁻¹ a h2
      rwa [mul_one, mul_inv_cancel] at hstep
    exact le_antisymm h3 h1
  · intro h
    rw [h, one_pow]

/-- `1 ≤ b · c⁻¹` gives `c ≤ b`. -/
theorem le_of_one_le_mul_inv {b c : GammaOf M} (h : (1 : GammaOf M) ≤ b * c⁻¹) : c ≤ b := by
  have hsimp : c * (b * c⁻¹) = b := by
    rw [← mul_assoc, mul_comm c b, mul_assoc, mul_inv_cancel, mul_one]
  have hstep := gamma_mul_le_mul_left (1 : GammaOf M) (b * c⁻¹) c h
  rwa [mul_one, hsimp] at hstep

/-- **Roots are unique**: `· ^ n` is injective on `Γ` for `n ≥ 1`.  Divisibility supplies
existence and the order supplies uniqueness. -/
theorem gamma_pow_inj {n : ℕ} (hn : 1 ≤ n) {b c : GammaOf M} (h : b ^ n = c ^ n) : b = c := by
  have hx : (b * c⁻¹) ^ n = 1 := by
    rw [mul_pow, inv_pow, ← h, mul_inv_cancel]
  have hx' : (c * b⁻¹) ^ n = 1 := by
    rw [mul_pow, inv_pow, ← h, mul_inv_cancel]
  have h1 : (1 : GammaOf M) ≤ b * c⁻¹ := (one_le_pow_iff hn).mp (le_of_eq hx.symm)
  have h2 : (1 : GammaOf M) ≤ c * b⁻¹ := (one_le_pow_iff hn).mp (le_of_eq hx'.symm)
  exact le_antisymm (le_of_one_le_mul_inv h2) (le_of_one_le_mul_inv h1)

/-- **The `n`-th root exists and is unique**: `Γ` carries a canonical root function. -/
theorem existsUnique_gamma_root (a : GammaOf M) {n : ℕ} (hn : 1 ≤ n) :
    ∃! b : GammaOf M, b ^ n = a := by
  obtain ⟨b, hb⟩ := gamma_divisible n hn a
  exact ⟨b, hb, fun c hc => gamma_pow_inj (M := M) hn (by rw [hc, hb])⟩

end SpecialTransformations.Milestone0.GammaDiv

/-! ## Axiom audit -/

#print axioms SpecialTransformations.Milestone0.GammaDiv.gamma_divisible
#print axioms SpecialTransformations.Milestone0.GammaDiv.gamma_pow_surjective
#print axioms SpecialTransformations.Milestone0.GammaDiv.gammaDivisible_top_iff_forall_root
#print axioms SpecialTransformations.Milestone0.GammaDiv.gammaOfRootableBy
#print axioms SpecialTransformations.Milestone0.GammaDiv.gammaOfRootableByInt
#print axioms SpecialTransformations.Milestone0.GammaDiv.gammaEq_iff_gammaMk
#print axioms SpecialTransformations.Milestone0.GammaDiv.gammaHullInitial_iff_gammaMk_pow
#print axioms SpecialTransformations.Milestone0.GammaDiv.gammaHullInitial_of_gammaEq
#print axioms SpecialTransformations.Milestone0.GammaDiv.gammaEq_self
#print axioms SpecialTransformations.Milestone0.GammaDiv.gamma_divisible_universal
#print axioms SpecialTransformations.Milestone0.GammaDiv.gamma_divisible_at_any_cardinality
#print axioms SpecialTransformations.Milestone0.GammaDiv.one_le_pow_iff
#print axioms SpecialTransformations.Milestone0.GammaDiv.pow_eq_one_iff
#print axioms SpecialTransformations.Milestone0.GammaDiv.gamma_pow_inj
#print axioms SpecialTransformations.Milestone0.GammaDiv.existsUnique_gamma_root
#print axioms SpecialTransformations.Milestone0.GammaDiv.forall_root_including_zero_subsingleton

namespace SpecialTransformations.Milestone0.GammaDiv

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-! ### §8 The additive form

`M5Ledger.GammaHullInitial`'s source `ClassicalProps.DivisibleHullExists` and
`Lifting_transcendental.divHull` speak additively (`n • h = j g`), so the divisibility of `Γ`
is also recorded for `Additive (GammaOf M)`. -/

/-- **`Γ` in additive notation is `ℕ`-divisible.** -/
noncomputable instance gammaAdditiveDivisibleByNat : DivisibleBy (Additive (GammaOf M)) ℕ :=
  divisibleByOfSMulRightSurj _ _ fun {n} hn => by
    intro a
    obtain ⟨b, hb⟩ := gamma_pow_surjective hn a.toMul
    have hb' : b ^ n = a.toMul := hb
    refine ⟨Additive.ofMul b, ?_⟩
    show n • Additive.ofMul b = a
    have h2 : n • Additive.ofMul b = Additive.ofMul (b ^ n) := by simp
    rw [h2, hb']
    simp

/-- **`Γ` in additive notation is `ℤ`-divisible.** -/
noncomputable instance gammaAdditiveDivisibleByInt : DivisibleBy (Additive (GammaOf M)) ℤ :=
  AddGroup.divisibleByIntOfDivisibleByNat _

/-- The additive surjectivity form: `n • ·` is onto `Γ` for every `n ≠ 0`. -/
theorem gamma_nsmul_surjective {n : ℕ} (hn : n ≠ 0) :
    Function.Surjective (fun a : Additive (GammaOf M) => n • a) :=
  DivisibleBy.surjective_smul (A := Additive (GammaOf M)) (α := ℕ) hn

/-- The additive root is unique as well, so `Γ` is a `ℚ`-divisible ordered abelian group in the
strong sense: `n • ·` is a bijection. -/
theorem gamma_nsmul_bijective {n : ℕ} (hn : n ≠ 0) :
    Function.Bijective (fun a : Additive (GammaOf M) => n • a) := by
  refine ⟨fun a b h => ?_, gamma_nsmul_surjective hn⟩
  have h' : a.toMul ^ n = b.toMul ^ n := by
    have h2 := congrArg Additive.toMul h
    simpa using h2
  exact Additive.toMul.injective (gamma_pow_inj (Nat.one_le_iff_ne_zero.mpr hn) h')

end SpecialTransformations.Milestone0.GammaDiv

#print axioms SpecialTransformations.Milestone0.GammaDiv.gammaAdditiveDivisibleByNat
#print axioms SpecialTransformations.Milestone0.GammaDiv.gammaAdditiveDivisibleByInt
#print axioms SpecialTransformations.Milestone0.GammaDiv.gamma_nsmul_surjective
#print axioms SpecialTransformations.Milestone0.GammaDiv.gamma_nsmul_bijective
#print axioms SpecialTransformations.Milestone0.GammaDiv.gammaHullInitial_self
#print axioms SpecialTransformations.Milestone0.GammaDiv.gammaHullInitialQ_of_gammaEqQ
#print axioms SpecialTransformations.Milestone0.GammaDiv.gammaDivisible_top_no_zero

namespace SpecialTransformations.Milestone0.GammaDiv

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-! ### §9 `Γ(S)` as a subset of `Γ(M)`

The paper writes `Γ(S) ⊆ Γ(T) ⊆ Γ(M)`.  In the encoding, `Γ(S)` is the image of the nonzero
`RV`-elements of `S` under `gammaMk`; §9 records that this image is a submonoid of `Γ(M)` (it is
*not* known to be a subgroup: `Transfer.iRVInv` is a choice function, not a term symbol, so
substructures are not closed under it — see the remark in `REPORT.md`), and restates the hull
clamp as "`Γ(T)` is contained in the root-closure of `Γ(S)`". -/

/-- `1` of the `RV` sort lies in every substructure (it is the constant `Fn.rvOne`). -/
theorem rvOne_mem_sub (S : LRV.Substructure M) : iRVOne (M := M) ∈ S :=
  S.fun_mem Fn.rvOne (fun i : Fin 0 => i.elim0) (fun i => i.elim0)

/-- **`Γ(S)`**: the image in `Γ(M)` of the nonzero `RV`-elements of `S`. -/
def GammaImage (S : LRV.Substructure M) : Set (GammaOf M) :=
  {q | ∃ (s : M) (_ : s ∈ S) (hsrv : iRV s) (hs0 : s ≠ iRVZero), q = gammaMk (mkR s hsrv hs0)}

/-- `1 ∈ Γ(S)`. -/
theorem gammaImage_one (S : LRV.Substructure M) : (1 : GammaOf M) ∈ GammaImage S (M := M) :=
  ⟨iRVOne, rvOne_mem_sub S, Transfer.rv_one_mem (M := M) hM, RVCalc.rv_one_ne_zero hM,
    gammaMk_one_eq.symm⟩

/-- **`Γ(S)` is closed under multiplication**: `rvMul` is a function symbol, so `S` is closed
under it (`M8Hull.rvMul_mem_sub`). -/
theorem gammaImage_mul {S : LRV.Substructure M} {q q' : GammaOf M}
    (hq : q ∈ GammaImage S (M := M)) (hq' : q' ∈ GammaImage S (M := M)) :
    q * q' ∈ GammaImage S (M := M) := by
  obtain ⟨s, hs, hsrv, hs0, rfl⟩ := hq
  obtain ⟨s', hs', hsrv', hs0', rfl⟩ := hq'
  refine ⟨iRVMul s s', M8Hull.rvMul_mem_sub S hs hs', Transfer.rv_mul_mem hM hsrv hsrv',
    rvStar_mul_nonzero ⟨hsrv, hs0⟩ ⟨hsrv', hs0'⟩, ?_⟩
  rw [mkR_mul_eq s s' hsrv hs0 hsrv' hs0', ← gammaMk_mul]

/-- **The hull clamp is root-closure of the image**: `GammaHullInitial S T` says exactly that
every class in `Γ(T)` has a positive power in `Γ(S)`.  This is the form in which the paper's
"`Γ(T)` lies in the divisible hull of `Γ(S)`" is used. -/
theorem gammaHullInitialQ_iff_image {S T : LRV.Substructure M} :
    GammaHullInitialQ (M := M) S T
      ↔ ∀ q ∈ GammaImage T (M := M), ∃ n : ℕ, 0 < n ∧ q ^ n ∈ GammaImage S (M := M) := by
  constructor
  · rintro h q ⟨t, ht, hrv, ht0, rfl⟩
    obtain ⟨n, hn, s, hs, hsrv, hs0, heq⟩ := h t ht hrv ht0
    exact ⟨n, hn, s, hs, hsrv, hs0, heq⟩
  · intro h t ht hrv ht0
    obtain ⟨n, hn, s, hs, hsrv, hs0, heq⟩ := h (gammaMk (mkR t hrv ht0)) ⟨t, ht, hrv, ht0, rfl⟩
    exact ⟨n, hn, s, hs, hsrv, hs0, heq⟩

end SpecialTransformations.Milestone0.GammaDiv

#print axioms SpecialTransformations.Milestone0.GammaDiv.gammaImage_one
#print axioms SpecialTransformations.Milestone0.GammaDiv.rvOne_mem_sub
#print axioms SpecialTransformations.Milestone0.GammaDiv.gammaImage_mul
#print axioms SpecialTransformations.Milestone0.GammaDiv.gammaHullInitialQ_iff_image


namespace SpecialTransformations.Milestone0.GammaDiv

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-! ### §10 `gammaVal`: the valuation-side reading

`GammaGroup.gammaVal hx hx0` is `[rv x]` for a nonzero `VF`-element.  Downstream work phrased
in `v(x)` rather than in `rv` (Prestel–Engler instantiations) needs that it is order-preserving
and multiplicative; both follow from the representatives. -/

/-- A product of nonzero `VF`-elements is nonzero.  Proved through `rv`, so that no `Field`
instance on `Transfer.VFType` is needed: `rv` is multiplicative and has no zero divisors. -/
theorem vf_mul_ne_zero {x y : M} (hx : iVF x) (hy : iVF y) (hx0 : x ≠ Transfer.iVFZero)
    (hy0 : y ≠ Transfer.iVFZero) : iVFMul x y ≠ Transfer.iVFZero := by
  intro h
  have hxr : iRV (iRv x) := Transfer.rv_mem hM hx
  have hyr : iRV (iRv y) := Transfer.rv_mem hM hy
  have hxr0 : iRv x ≠ iRVZero := fun h' => hx0 (RVCalc.vf_eq_zero_of_rv_eq_zero hM hx h')
  have hyr0 : iRv y ≠ iRVZero := fun h' => hy0 (RVCalc.vf_eq_zero_of_rv_eq_zero hM hy h')
  have h1 : iRv (iVFMul x y) = iRVZero := by rw [h, RVCalc.rv_zero_eq hM]
  rw [Transfer.rv_mul_hom_of_model hM hx hy] at h1
  exact rvStar_mul_nonzero ⟨hxr, hxr0⟩ ⟨hyr, hyr0⟩ h1

/-- **`gammaVal` is order-preserving and order-reflecting** on nonzero `VF`-elements. -/
theorem gammaVal_le_iff_le {x y : M} (hx : iVF x) (hy : iVF y) (hx0 : x ≠ Transfer.iVFZero)
    (hy0 : y ≠ Transfer.iVFZero) :
    gammaVal hx hx0 ≤ gammaVal hy hy0 ↔ iLe (iRv x) (iRv y) :=
  gammaMk_le_iff

/-- **`gammaVal` is multiplicative**: `v(x · y) = v(x) · v(y)` in `Γ(M)`. -/
theorem gammaVal_mul {x y : M} (hx : iVF x) (hy : iVF y) (hx0 : x ≠ Transfer.iVFZero)
    (hy0 : y ≠ Transfer.iVFZero) :
    gammaVal hx hx0 * gammaVal hy hy0
      = gammaVal (Transfer.vf_mul_mem hM hx hy) (vf_mul_ne_zero hx hy hx0 hy0) := by
  have hkey : (rvStarOf (Transfer.vf_mul_mem hM hx hy) (vf_mul_ne_zero hx hy hx0 hy0) :
      RVStar M) = rvStarOf hx hx0 * rvStarOf hy hy0 := by
    refine Subtype.ext ?_
    show iRv (iVFMul x y) = iRVMul (iRv x) (iRv y)
    exact Transfer.rv_mul_hom_of_model hM hx hy
  show gammaMk (rvStarOf hx hx0) * gammaMk (rvStarOf hy hy0)
      = gammaMk (rvStarOf (Transfer.vf_mul_mem hM hx hy) (vf_mul_ne_zero hx hy hx0 hy0))
  rw [hkey, gammaMk_mul]

/-- **`Γ`-divisibility in valuation form**: `v(x)` is `n`-divisible in `Γ(M)` for every nonzero
`VF`-element `x` and every `n ≥ 1`. -/
theorem gammaVal_root {x : M} (hx : iVF x) (hx0 : x ≠ Transfer.iVFZero) {n : ℕ}
    (hn : 1 ≤ n) : ∃ b : GammaOf M, b ^ n = gammaVal hx hx0 :=
  gamma_divisible n hn _

end SpecialTransformations.Milestone0.GammaDiv

#print axioms SpecialTransformations.Milestone0.GammaDiv.vf_mul_ne_zero
#print axioms SpecialTransformations.Milestone0.GammaDiv.gammaVal_le_iff_le
#print axioms SpecialTransformations.Milestone0.GammaDiv.gammaVal_mul
#print axioms SpecialTransformations.Milestone0.GammaDiv.gammaVal_root
