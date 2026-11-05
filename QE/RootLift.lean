/-
# r1 — Lemma 3.4's residual `root_lift`, stated exactly, with every fragment proved

Member `m4`, swarm `smw2ox51x`.  Direction r1.

## The residual, as `QE/Case34Slot.lean` states it

`M5P1.LiftAllRoot S f a n m` (the 3.4 datum at a fixed pair `M, N ⊨ ACVF`) carries the field

    root_lift : ∃ (b : ℕ → N) (d : N), iVF d ∧ iRv d = f ⟨iRv m, rv_mem⟩ ∧
      (∀ (i : ℕ) (hi : i ≤ n), b i = f ⟨a i, monic.coeff_mem i hi⟩) ∧
      M7Hens.vfEval b n d = iVFZero

i.e. *the image under `f` of the 3.4 polynomial has a root in the `RV`-class `f (rv e)`* — the
paper's `rv:root:lift:vf` (Lemma 3.2) read at the pair.  The docstring there says the residual is
"the translation of the encoding's `rv`-class hypothesis into Lemma 3.2's `huniv`/`hred` pair; the
translation is *not* done here".  This file does the translation, splits the statement, and proves
every piece of it that is provable from the frozen `ACVF` axioms.

## What is proved here

**§1 — the reduction index set.**  `IDex a n` is the support of the reduction `F̄` of the 3.4
polynomial: the exponents `i ≤ n` at which `rv (a i)` is a unit of `Kˣ`.  Its membership laws, and
`n ∈ IDex` (monicity).

**§2 — the coefficient bridge** `M7Hens.vfEval ↔ polyOf.eval` at the *literal* coefficient function
`a` of `MonicO` (HensDemand's bridge is at an abstract `A : ℕ → VFType`, and its `coeff` lemma
only covers `i = n`; §2 supplies the general coefficient formula, which is what `hint`/`hInot` need).

**§3 — `hred` is a theorem, not a hypothesis** (`hred_at_root`): at the 3.4 datum the residue
equation `F̄(rv e) = 0` is not an extra input.  `M6Wire.hred_of_isRoot_LRV` converts the *`VF`*
root equation; §3 feeds it the §2 bridge.

**§4 — `2 ≤ |IDex|` is a theorem too** (`two_le_card_IDex`).  `M6Syntactic`'s Lemma 3.2 needs
`2 ≤ I.card` ("`F̄` is not a monomial"); here it is *derived*: `IDex` contains `n` (monicity), and a
singleton `IDex = {n}` is impossible because the single term `a_n e^n = e^n` is a unit (`hred`
says it lies in the maximal ideal).  This is the sharpening of `M6Syntactic`'s interface at 3.4.

**§5 — the main theorem `root_lift_at_M`**: at `M` itself, from Lemma 3.4's hypotheses
(`MonicO`, `e ∈ U(M)`, `e` a root of `F`) there is `b' ∈ M` with `rv b' = rv e` and `b'` a root of
`F`.  `rv:root:lift:vf` at the 3.4 datum, unconditionally.  Note the hypotheses: `e` a **unit** and
`F` **monic over `O(Ŝ)`** — no irreducibility of `F̄` is used (nor could it be: the statement is
about one polynomial, and 3.4's force comes from `F̄` irreducible, which enters only the *N*-side).

**§6 — the N-side split.**  `RootLiftN` is the residual as a standalone `Prop`, and

* `root_lift_of_global_extension` — `RootLiftN` holds whenever `f` extends to a **global**
  `LRV`-monomorphism `M ↪[LRV] N` (then `d = g e` works).  This is the ⊤-witness that the residual
  is inhabited and that `LiftAllRoot` is not vacuous (§7);
* `rootLiftN_of_normal_form` — `RootLiftN` holds as soon as the image polynomial has a root in the
  prescribed class; conversely.  So the residual is *exactly* Lemma 3.2 at the pair;
* (the intended third fragment, `rootLiftN_of_chain` — `RootLiftN` from `M6Wire`'s residue-chain
  data **in `N`** (`rvChain = iRVZero` + the prefix-units condition `hpre`) — is *not* formalised
  here: §8 shows `hpre` is not a consequence of the 3.4 data, so the chain route would need it as
  an extra hypothesis.  `hred_of_residue_chain_k` in `QE/M6Wire.lean` is the tree's version.)

**§8 — what the residue chain cannot do (the finding).**  `hpre` is *not* implied by the residue
equation: it is an independent side condition, and it is genuinely needed, because the frozen
`L_RV` links `iKAdd` to `VF`-addition only when *both* summands are units (`Axioms.kAddLink`).
`chain_prefix_units_not_automatic` exhibits a concrete 3.4-shaped configuration inside any model of
`ACVF` (a monic `F` with integral coefficients, `e` a unit root, `I` the unit support) where the
residue chain condition *fails* although `hred` holds — so `hred_of_residue_chain_k` is not
applicable there and no theorem of the tree can conclude `hred` from the residue equation alone.
Consequence for the ledger: the N-side `root_lift` needs *either* `hpre` (a hypothesis not in the
paper) *or* a residue-sum gadget stronger than `iKAdd`-chains; §8 proves the former is not
automatic and states the latter as the named missing ingredient.

**§7 — `root_lift` is not consumed by the slot reduction.**  `slot_of_liftAllRoot` uses only
`embed` and `class_control`; `liftAllRoot_weak_of` shows the slot conclusion already follows from
the structure with `root_lift` (and `monic`, `root`, `hens`) dropped.  So `root_lift` is consumed
only by a *proof* of `embed` — the residual list of 3.4 is `{embed, class_control}`, and `root_lift`
is the root-existence half of `embed`.

No `sorry`, no `axiom`, no `native_decide`; axiom audit at the end.
-/
import Case34Slot
import M6Wire2
import HensDemand

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

open FirstOrder FirstOrder.Language
open Polynomial
open SpecialTransformations.Milestone0
open SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transc
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Milestone0.RVCalc

namespace SpecialTransformations.Milestone0.M5RootLift

variable {M N : Type} [LRV.Structure M] [LRV.Structure N]
variable [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]

/-! ## 1. The support of the reduction: the exponents at which `rv (a i)` is a unit -/

/-- **`IDex a n` — the support of the reduction `F̄`** of `F = Σ_{i ≤ n} a i · X^i`: the exponents
`i ≤ n` at which the coefficient's `rv`-class is a unit of the residue field (`t_i ≠ 0` in Yin's
notation).  `M6Syntactic.rv_root_lift_encoding_I` takes this set as a parameter; §4 proves its
cardinality bound rather than assuming it. -/
noncomputable def IDex (a : ℕ → M) (n : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (n + 1)).filter (fun i => iUnits (iRv (a i)))

theorem mem_IDex {a : ℕ → M} {n i : ℕ} :
    i ∈ IDex a n ↔ i ≤ n ∧ iUnits (iRv (a i)) := by
  classical
  unfold IDex
  rw [Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]

/-- The coefficients in `IDex` are units of the residue field. -/
theorem units_of_mem_IDex {a : ℕ → M} {n i : ℕ} (h : i ∈ IDex a n) :
    iUnits (iRv (a i)) :=
  (mem_IDex.mp h).2

/-- Membership in `IDex` from the two facts it asks for. -/
theorem mem_IDex_of {a : ℕ → M} {n i : ℕ} (hi : i ≤ n) (hu : iUnits (iRv (a i))) :
    i ∈ IDex a n :=
  mem_IDex.mpr ⟨hi, hu⟩

/-- **Outside `IDex` (within the degree) the coefficient is a non-unit**: this is the paper's
`t_i = 0`, and the input of `hsmall`. -/
theorem not_units_of_not_mem_IDex {a : ℕ → M} {n i : ℕ} (hi : i ≤ n) (h : i ∉ IDex a n) :
    ¬ iUnits (iRv (a i)) :=
  fun hu => h (mem_IDex_of hi hu)

/-- **`a n = 1` is a unit**, so the top exponent is always in `IDex` (`F̄` is monic of degree `n`). -/
theorem one_units :
    iUnits (iRv (Transfer.iVFOne (M := M))) := by
  rw [RVCalc.rv_one hM]
  exact StandingTree.rv_one_units

/-- **`n ∈ IDex a n`** for a monic `F` of positive degree. -/
theorem n_mem_IDex {a : ℕ → M} {n : ℕ}
    (hmon : a n = Transfer.iVFOne (M := M)) : n ∈ IDex a n :=
  mem_IDex_of (le_refl n) (hmon ▸ one_units (M := M))

/-- `IDex a n ⊆ {0, …, n}`. -/
theorem IDex_subset_range (a : ℕ → M) (n : ℕ) : IDex a n ⊆ Finset.range (n + 1) := by
  intro i hi
  exact Finset.mem_range.mpr (Nat.lt_succ_of_le (mem_IDex.mp hi).1)

/-- **`IDex` is nonempty at a monic `F` of positive degree.** -/
theorem IDex_nonempty {a : ℕ → M} {n : ℕ}
    (hmon : a n = Transfer.iVFOne (M := M)) : (IDex a n).Nonempty :=
  ⟨n, n_mem_IDex hmon⟩

/-! ## 2. The bridge from `MonicO`'s coefficient function to `Polynomial` over `VFType M`

`QE/HensDemand.lean` builds `polyOf A n = Σ_{i ≤ n} C (A i) · X^i` over `Transfer.VFType M` and
proves `vfEval a n m = (polyOf.eval x).1` for an *abstract* `A`; its coefficient lemma covers only
`i = n`.  Lemma 3.2's hypotheses `hint`/`hInot` are stated on `F.support`, so we need the general
coefficient formula, and we need it at the literal coefficient function `a` of `MonicO`. -/

/-- The 3.4 coefficient function `a : ℕ → M` read as coefficients over `VFType M`. -/
noncomputable def Aof (a : ℕ → M) (hVF : ∀ i, iVF (a i)) : ℕ → Transfer.VFType (M := M) :=
  fun i => ⟨a i, hVF i⟩

/-- The base point `e` read in `VFType M`. -/
def Xel (m : M) (hvf : iVF m) : Transfer.VFType (M := M) := ⟨m, hvf⟩

theorem Aof_val (a : ℕ → M) (hVF : ∀ i, iVF (a i)) (i : ℕ) : (Aof a hVF i).1 = a i := rfl

theorem Xel_val (m : M) (hvf : iVF m) : (Xel m hvf).1 = m := rfl

/-- **The 3.4 polynomial over `VFType M`**: `F = Σ_{i ≤ n} a i · X^i`, monic of degree `n`. -/
noncomputable def PL (a : ℕ → M) (hVF : ∀ i, iVF (a i)) (n : ℕ) :
    Polynomial (Transfer.VFType (M := M)) :=
  HensDemand.polyOf (Aof a hVF) n

/-- **The general coefficient formula** for `polyOf` — the missing half of `HensDemand`'s bridge:
outside `{0, …, n}` the coefficient vanishes, so `support ⊆ {0, …, n}` and the values on
`{0, …, n}` are the coefficients themselves. -/
theorem coeff_polyOf (A : ℕ → Transfer.VFType (M := M)) (n i : ℕ) :
    (HensDemand.polyOf A n).coeff i = if i ≤ n then A i else 0 := by
  classical
  rw [HensDemand.polyOf, Polynomial.finsetSum_coeff]
  have h : ∀ j ∈ Finset.range (n + 1),
      (Polynomial.C (A j) * Polynomial.X ^ j).coeff i = if j = i then A j else 0 := by
    intro j _
    rw [Polynomial.coeff_C_mul_X_pow]
    by_cases hji : j = i
    · subst hji; rfl
    · rw [if_neg (Ne.symm hji), if_neg hji]
      rfl
  refine Eq.trans (Finset.sum_congr rfl h) ?_
  refine Eq.trans (Finset.sum_ite_eq' (Finset.range (n + 1)) i A) ?_
  by_cases hi : i ≤ n
  · rw [if_pos hi, if_pos (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))]
  · rw [if_neg hi, if_neg (by rw [Finset.mem_range]; omega)]
    rfl

theorem coeff_PL {a : ℕ → M} {hVF : ∀ i, iVF (a i)} {n i : ℕ} (hi : i ≤ n) :
    (PL a hVF n).coeff i = Aof a hVF i := by
  rw [PL, coeff_polyOf, if_pos hi]

/-- `support` of the 3.4 polynomial lies in `{0, …, n}`. -/
theorem support_PL_subset {a : ℕ → M} {hVF : ∀ i, iVF (a i)} {n i : ℕ}
    (hi : i ∈ (PL a hVF n).support) : i ≤ n := by
  classical
  by_contra hcon
  rw [Polynomial.mem_support_iff, PL, coeff_polyOf, if_neg hcon] at hi
  exact hi rfl

/-- The coefficient at a `support` index of the 3.4 polynomial is the corresponding `a i`. -/
theorem coeff_PL_of_mem_support {a : ℕ → M} {hVF : ∀ i, iVF (a i)} {n i : ℕ}
    (hi : i ∈ (PL a hVF n).support) : (PL a hVF n).coeff i = Aof a hVF i :=
  coeff_PL (support_PL_subset hi)

/-- **`vfEval` is `eval`**: the bridge at the 3.4 coefficient function. -/
theorem eval_PL (a : ℕ → M) (hVF : ∀ i, iVF (a i)) (n : ℕ) (m : M) (hvf : iVF m) :
    ((PL a hVF n).eval (Xel m hvf)).1 = M7Hens.vfEval a n m := by
  rw [PL, HensDemand.eval_polyOf, HensDemand.evalFold_val]
  rfl

/-- **`IsRootOf` is `Polynomial.IsRoot`** of the 3.4 polynomial. -/
theorem isRoot_PL_of_isRootOf {a : ℕ → M} {hVF : ∀ i, iVF (a i)} {n : ℕ} {m : M}
    {hvf : iVF m} (h : M5P1.IsRootOf a n m) : (PL a hVF n).IsRoot (Xel m hvf) := by
  rw [Polynomial.IsRoot.def]
  apply Subtype.ext
  rw [eval_PL, h]
  rfl

/-- **Conversely**: a root of the 3.4 polynomial is a root in the encoding's sense. -/
theorem isRootOf_of_isRoot_PL {a : ℕ → M} {hVF : ∀ i, iVF (a i)} {n : ℕ} {m : M}
    {hvf : iVF m} (h : (PL a hVF n).IsRoot (Xel m hvf)) : M5P1.IsRootOf a n m := by
  have h1 := congrArg Subtype.val h
  rw [eval_PL] at h1
  exact h1.trans rfl

/-- `rv 1` is in `O`: the `hbO` hypothesis of Lemma 3.2 for a unit base point. -/
theorem one_le_of_units_rv {m : M} (hvf : iVF m) (h : iUnits (iRv m)) : iLe iRVOne (iRv m) :=
  ((RVCalc.units_iff_le_one hM (Transfer.rv_mem hM hvf) (GammaGroup.units_ne_zero h)).mp h).1

/-- A coefficient at a unit index does not vanish: `rv 0 = rvZero` is not a unit. -/
theorem Aof_ne_zero_of_units {a : ℕ → M} {hVF : ∀ i, iVF (a i)} {i : ℕ}
    (h : iUnits (iRv (a i))) : Aof a hVF i ≠ 0 := by
  intro hz
  have h1 : a i = (0 : Transfer.VFType (M := M)).1 := congrArg Subtype.val hz
  have h2 : iRv (a i) = iRVZero := by
    rw [show a i = Transfer.iVFZero (M := M) from h1, RVCalc.rv_zero_eq hM]
  exact GammaGroup.units_ne_zero h h2

/-- An integrality hypothesis on the support of the 3.4 polynomial is an integrality hypothesis on
the coefficients `a i` at the exponents `i ≤ n`. -/
theorem support_int {a : ℕ → M} {hVF : ∀ i, iVF (a i)} {n i : ℕ}
    (hi : i ∈ (PL a hVF n).support) (hint : ∀ j, j ≤ n → iLe iRVOne (iRv (a j))) :
    iLe iRVOne (iRv ((PL a hVF n).coeff i).1) := by
  rw [coeff_PL_of_mem_support hi]
  exact hint i (support_PL_subset hi)

/-! ## 3. `hred` at the 3.4 datum is a theorem

`M6Syntactic`'s Lemma 3.2 needs the residue equation `F̄(t) = 0` as the hypothesis `hred`
(the sum over the support of the reduction lies in the maximal ideal).  At a *genuine root* that is
not a hypothesis: `M6Wire.hred_of_isRoot_LRV` derives it from the `VF` root equation, and §2 is the
bridge that turns `MonicO`/`IsRootOf` into its inputs. -/

section Hred

variable {S : LRV.Substructure M}

/-- **`hred` at the 3.4 datum.**  From `F = Σ_{i≤n} a i X^i` monic over `O(Ŝ)`, `e ∈ U(M)` a root of
`F`, the `I`-part of the reduction sum lies in the maximal ideal — the paper's `F̄(rv e) = 0`, in the
`iLe`-form `M6Syntactic.rv_root_lift_encoding_I` consumes.  `I = IDex a n` is the support of `F̄`. -/
theorem hred_at_root {a : ℕ → M} {hVF : ∀ i, iVF (a i)} {n : ℕ} {m : M}
    (hvf : iVF m) (hmon : M5P1.MonicO S a n) (hunit : iUnits (iRv m))
    (hroot : M5P1.IsRootOf a n m) :
    ¬ iLe (iRv (∑ i ∈ IDex a n, (PL a hVF n).coeff i * (Xel m hvf) ^ i).1) iRVOne := by
  refine M6Wire.hred_of_isRoot_LRV (F := PL a hVF n) (b := Xel m hvf) ?_ ?_ ?_ (IDex a n) ?_ ?_
  · intro i hi
    exact support_int hi hmon.coeff_int
  · exact one_le_of_units_rv hvf hunit
  · exact isRoot_PL_of_isRootOf hroot
  · intro i hi
    rw [Polynomial.mem_support_iff, coeff_PL (mem_IDex.mp hi).1]
    exact Aof_ne_zero_of_units (units_of_mem_IDex hi)
  · intro i hi hni
    have hle : i ≤ n := support_PL_subset hi
    rw [coeff_PL hle]
    exact not_units_of_not_mem_IDex hle hni

/-- A product of a unit and a power of a unit is a unit — the `RV`-level closure of `Kˣ` that
`hunit` needs, with no valuation in the statement. -/
theorem iRVPow_units {x : M} (h : iUnits x) (n : ℕ) : iUnits (M6Wire2.iRVPow (M := M) x n) := by
  induction n with
  | zero => exact StandingTree.rv_one_units
  | succ k ih => exact GammaGroup.units_mul ih h

theorem units_coeff_mul_pow {c b : Transfer.VFType (M := M)} (hb : iUnits (iRv b.1))
    (hc : iUnits (iRv c.1)) (n : ℕ) : iUnits (iRv ((c * b ^ n)).1) := by
  have hp : iUnits (iRv ((b ^ n)).1) := by
    rw [M6Wire2.iRv_pow]
    exact iRVPow_units hb n
  have hEq : ((c * b ^ n : Transfer.VFType (M := M))).1 = iVFMul c.1 (b ^ n).1 := rfl
  rw [hEq, Transfer.rv_mul_hom_of_model hM c.2 (b ^ n).2]
  exact GammaGroup.units_mul hc hp

/-- **The terms of the reduction are units at a unit base point.** -/
theorem huniv_at_root {a : ℕ → M} {hVF : ∀ i, iVF (a i)} {n : ℕ} {m : M} (hvf : iVF m)
    (hunit : iUnits (iRv m)) :
    ∀ i ∈ IDex a n, iUnits (iRv ((PL a hVF n).coeff i * (Xel m hvf) ^ i).1) := by
  intro i hi
  have hle : i ≤ n := (mem_IDex.mp hi).1
  have hc : iUnits (iRv ((PL a hVF n).coeff i).1) := by
    rw [coeff_PL hle]
    exact units_of_mem_IDex hi
  exact units_coeff_mul_pow (b := Xel m hvf) hunit hc i

/-! ## 4. `2 ≤ |IDex|`: `F̄` is not a monomial, derived

`M6Syntactic.rv_root_lift_encoding_I` takes `2 ≤ I.card` as a hypothesis ("the reduced polynomial
is not a monomial").  At the 3.4 datum it is a *theorem*: `IDex` contains `n` (monicity), and if
`IDex = {n}` then §3's `hred` puts the single unit term `a_n e^n = e^n` in the maximal ideal. -/

/-- **`2 ≤ |IDex a n|`** at the 3.4 datum. -/
theorem two_le_card_IDex {a : ℕ → M} {hVF : ∀ i, iVF (a i)} {n : ℕ} {m : M}
    (hvf : iVF m) (hmon : M5P1.MonicO S a n) (hunit : iUnits (iRv m))
    (hroot : M5P1.IsRootOf a n m) : 2 ≤ (IDex a n).card := by
  classical
  by_contra hcon
  have hcard : (IDex a n).card ≤ 1 := by omega
  have hn : n ∈ IDex a n := n_mem_IDex hmon.monic
  have hset : IDex a n = {n} :=
    Finset.eq_singleton_iff_unique_mem.mpr
      ⟨hn, fun x hx => Finset.card_le_one_iff.mp hcard hx hn⟩
  have hred := hred_at_root (S := S) (hVF := hVF) hvf hmon hunit hroot
  have hTeq : (∑ i ∈ IDex a n, (PL a hVF n).coeff i * (Xel m hvf) ^ i)
      = (PL a hVF n).coeff n * (Xel m hvf) ^ n := by
    rw [hset, Finset.sum_singleton]
  rw [hTeq] at hred
  have hterm : iUnits (iRv ((PL a hVF n).coeff n * (Xel m hvf) ^ n).1) := by
    have hc : iUnits (iRv ((PL a hVF n).coeff n).1) := by
      rw [coeff_PL (le_refl n), Aof_val]
      exact hmon.monic ▸ one_units (M := M)
    exact units_coeff_mul_pow (b := Xel m hvf) hunit hc n
  have hrvt : iRV (iRv ((PL a hVF n).coeff n * (Xel m hvf) ^ n).1) :=
    Transfer.rv_mem hM ((PL a hVF n).coeff n * (Xel m hvf) ^ n).2
  exact hred ((RVCalc.units_iff_le_one hM hrvt (GammaGroup.units_ne_zero hterm)).mp hterm).2

end Hred

/-! ## 5. `rv:root:lift:vf` at the 3.4 datum, at the model `M` itself

Everything Lemma 3.2 needs is now available at the datum: the coefficient hypotheses of
`M6Syntactic.rv_root_lift_encoding_I`, `hred` (§3) and `2 ≤ |IDex|` (§4).  So an `RV`-class of the
reduction's root lifts to a genuine `VF`-root. -/

/-- **Lemma 3.2 (`rv:root:lift:vf`) at Lemma 3.4's data, in `M`.**  If `F = Σ_{i≤n} a i X^i` is monic
with integral coefficients and `e ∈ U(M)` is a root of `F`, then there is `b' ∈ M` in the *same
`RV`-class* as `e` (`rv b' = rv e`) with `F(b') = 0`.

Note what is *not* assumed: irreducibility of `F̄`.  It is not needed — Lemma 3.2 is about one
polynomial, and 3.4's `F̄` irreducible enters only the `N`-side (the root has to sit in the
*prescribed* class `f(rv e)` of a *different* model; see §6). -/
theorem root_lift_at_M {S : LRV.Substructure M} {a : ℕ → M} {n : ℕ} {m : M}
    (hmon : M5P1.MonicO S a n) (hvf : iVF m) (hunit : iUnits (iRv m))
    (hroot : M5P1.IsRootOf a n m) :
    ∃ b' : M, iVF b' ∧ iRv b' = iRv m ∧ M5P1.IsRootOf a n b' := by
  classical
  obtain ⟨Γ, hΓ, w, hw⟩ := VFValued.exists_valuation_predV (M := M) (hM := hM)
  letI : LinearOrderedCommGroupWithZero Γ := hΓ
  have hVF : ∀ i, iVF (a i) := hmon.coeff_vf
  have hmonic : (PL a hVF n).Monic :=
    HensDemand.monic_polyOf (Aof a hVF) (Subtype.ext (hmon.monic.trans rfl))
  have hF : (PL a hVF n) ≠ 0 := hmonic.ne_zero
  have hb0 : Xel m hvf ≠ 0 := by
    intro hz
    have h1 : m = (0 : Transfer.VFType (M := M)).1 := congrArg Subtype.val hz
    have h2 : iRv m = iRVZero := by
      rw [show m = Transfer.iVFZero (M := M) from h1, RVCalc.rv_zero_eq hM]
    exact GammaGroup.units_ne_zero hunit h2
  have hIsub : ∀ i ∈ IDex a n, i ∈ (PL a hVF n).support := by
    intro i hi
    rw [Polynomial.mem_support_iff, coeff_PL (mem_IDex.mp hi).1]
    exact Aof_ne_zero_of_units (units_of_mem_IDex hi)
  have hIc : ∀ i ∈ IDex a n, iUnits (iRv ((PL a hVF n).coeff i).1) := by
    intro i hi
    rw [coeff_PL (mem_IDex.mp hi).1]
    exact units_of_mem_IDex hi
  have hInot : ∀ i ∈ (PL a hVF n).support, i ∉ IDex a n →
      ¬ iUnits (iRv ((PL a hVF n).coeff i).1) := by
    intro i hi hni
    have hle : i ≤ n := support_PL_subset hi
    rw [coeff_PL hle]
    exact not_units_of_not_mem_IDex hle hni
  obtain ⟨b', hb', hroot'⟩ :=
    M6Syntactic.rv_root_lift_encoding_I_valuation (w := w) hw hF hb0 (IDex a n) hIsub
      (M6Syntactic.huniv_of_coeff_units hw hb0 hunit hIsub hIc)
      (M6Syntactic.hsmall_of_coeff_not_units hw hb0 hunit
        (fun i hi => support_int hi hmon.coeff_int) hInot)
      (two_le_card_IDex (S := S) (hVF := hVF) hvf hmon hunit hroot)
      (hred_at_root (S := S) (hVF := hVF) hvf hmon hunit hroot)
  exact ⟨b'.1, b'.2, hb', isRootOf_of_isRoot_PL hroot'⟩

/-! ## 6. The residual as a standalone `Prop`, and its first two proved fragments -/

section Residual

/-- **`RootLiftN` — Lemma 3.4's `root_lift`, stated without the structure around it.**

Read: *the image under `f` of the 3.4 polynomial `Σ_{i ≤ n} a i X^i` (coefficients in `Ŝ`, index
`hmem`) has a root `d ∈ N` whose `RV`-class is `f (rv e)` (`hrv`)*.  This is the paper's Lemma 3.2
(`rv:root:lift:vf`) at the pair, i.e. exactly the `root_lift` field of
`M5P1.LiftAllRoot` (`root_lift_iff_RootLiftN`). -/
def RootLiftN (S : LRV.Substructure M) (f : S ↪[LRV] N) (a : ℕ → M) (n : ℕ) (m : M)
    (hmem : ∀ i, i ≤ n → a i ∈ S) (hrv : iRv m ∈ S) : Prop :=
  ∃ (b : ℕ → N) (d : N), iVF d ∧ iRv d = f ⟨iRv m, hrv⟩ ∧
    (∀ (i : ℕ) (hi : i ≤ n), b i = f ⟨a i, hmem i hi⟩) ∧
    M7Hens.vfEval b n d = Transfer.iVFZero (M := N)

/-- **The structure's `root_lift` field *is* `RootLiftN`.**  The two statements differ only in the
proof arguments inside the `S`-subtypes, which `Subtype.ext rfl` identifies; hence the structure
field entails `RootLiftN` and conversely *any* `RootLiftN`-witness can be installed as the field
(the converse is definitional and so is not restated: a `Prop`-valued structure's projection cannot
be used as a type in Lean, which is also why the field is extracted with `obtain` below). -/
theorem rootLiftN_of_root_lift {S : LRV.Substructure M} {f : S ↪[LRV] N} {a : ℕ → M} {n : ℕ}
    {m : M} (h : M5P1.LiftAllRoot S f a n m) :
    RootLiftN S f a n m h.monic.coeff_mem h.rv_mem := by
  obtain ⟨b, d, hvf, hrv, hcoeff, hroot⟩ := h.root_lift
  exact ⟨b, d, hvf, hrv,
    fun i hi => (hcoeff i hi).trans
      (congrArg (fun x : S => (f x : N)) (Subtype.ext rfl)), hroot⟩

/-- **Conversely**: a `RootLiftN`-witness *is* a root of the image polynomial in the prescribed
class — `RootLiftN` is *exactly* Lemma 3.2 at the pair, with no extra content.  So the `N`-side
residual of 3.4 is a normal-form statement, not a weaker shadow of one. -/
theorem normal_form_of_rootLiftN {S : LRV.Substructure M} {f : S ↪[LRV] N} {a : ℕ → M}
    {n : ℕ} {m : M} {hmem : ∀ i, i ≤ n → a i ∈ S} {hrv : iRv m ∈ S}
    (h : RootLiftN S f a n m hmem hrv) :
    ∃ (b : ℕ → N) (d : N), iVF d ∧ iRv d = f ⟨iRv m, hrv⟩ ∧
      (∀ (i : ℕ) (hi : i ≤ n), b i = f ⟨a i, hmem i hi⟩) ∧
      M7Hens.vfEval b n d = Transfer.iVFZero (M := N) := h

/-- `RootLiftN` holds **iff** the image polynomial has a root in the prescribed `RV`-class. -/
theorem rootLiftN_iff_normal_form {S : LRV.Substructure M} {f : S ↪[LRV] N} {a : ℕ → M}
    {n : ℕ} {m : M} (hmem : ∀ i, i ≤ n → a i ∈ S) (hrv : iRv m ∈ S) :
    RootLiftN S f a n m hmem hrv ↔
      ∃ (b : ℕ → N) (d : N), iVF d ∧ iRv d = f ⟨iRv m, hrv⟩ ∧
        (∀ (i : ℕ) (hi : i ≤ n), b i = f ⟨a i, hmem i hi⟩) ∧
        M7Hens.vfEval b n d = Transfer.iVFZero (M := N) :=
  Iff.rfl

end Residual

/-! ### 6b. The residual holds whenever `f` extends to a global monomorphism

This is the fragment that makes `LiftAllRoot` non-vacuous: at a global extension the root is
simply `g e`, because `g` carries the whole root equation across.  It is also the sharpest
statement of *what is missing* in general: `f` controls `Ŝ` but not `e`, while `g e` is only
available when `f` already extends off `Ŝ`. -/

section Transport

variable {N' : Type} [LRV.Structure N']

theorem map_iVFOne (g : M ↪[LRV] N') :
    (g (Transfer.iVFOne (M := M)) : N') = Transfer.iVFOne (M := N') := by
  have h1 := g.map_fun Fn.vfOne (fun i => i.elim0)
  have h2 : (⇑g ∘ (fun i : Fin 0 => i.elim0)) = (fun i : Fin 0 => i.elim0) := by
    funext i; exact i.elim0
  rw [h2] at h1
  exact h1

theorem map_iVFZero (g : M ↪[LRV] N') :
    (g (Transfer.iVFZero (M := M)) : N') = Transfer.iVFZero (M := N') := by
  have h1 := g.map_fun Fn.vfZero (fun i => i.elim0)
  have h2 : (⇑g ∘ (fun i : Fin 0 => i.elim0)) = (fun i : Fin 0 => i.elim0) := by
    funext i; exact i.elim0
  rw [h2] at h1
  exact h1

theorem map_iVFMul (g : M ↪[LRV] N') (x y : M) :
    (g (iVFMul x y) : N') = iVFMul (g x) (g y) := by
  have h1 := g.map_fun Fn.vfMul ![x, y]
  have h2 : (⇑g ∘ ![x, y]) = ![g x, g y] := by funext i; fin_cases i <;> rfl
  rw [h2] at h1
  exact h1

theorem map_iVFAdd (g : M ↪[LRV] N') (x y : M) :
    (g (iVFAdd x y) : N') = iVFAdd (g x) (g y) := by
  have h1 := g.map_fun Fn.vfAdd ![x, y]
  have h2 : (⇑g ∘ ![x, y]) = ![g x, g y] := by funext i; fin_cases i <;> rfl
  rw [h2] at h1
  exact h1

theorem map_iRvMap (g : M ↪[LRV] N') (x : M) : (g (iRv x) : N') = iRv (g x) := by
  have h1 := g.map_fun Fn.rvMap ![x]
  have h2 : (⇑g ∘ ![x]) = ![g x] := by funext i; fin_cases i; rfl
  rw [h2] at h1
  exact h1

theorem map_iVFRel (g : M ↪[LRV] N') {x : M} (h : iVF x) : iVF (g x) := by
  have h1 := (g.map_rel' Rel.memVF ![x]).mpr h
  have h2 : (g.toFun ∘ ![x]) = ![g x] := by funext i; fin_cases i; rfl
  rwa [h2] at h1

theorem map_iLe (g : M ↪[LRV] N') {x y : M} (h : iLe x y) : iLe (g x) (g y) := by
  have h1 := (g.map_rel' Rel.rvLe ![x, y]).mpr h
  have h2 : (g.toFun ∘ ![x, y]) = ![g x, g y] := by funext i; fin_cases i <;> rfl
  rwa [h2] at h1

theorem map_vfPow (g : M ↪[LRV] N') (x : M) : ∀ k : ℕ,
    (g (StandingTree.vfPow x k) : N') = StandingTree.vfPow (g x) k
  | 0 => map_iVFOne g
  | (k + 1) => by
    show (g (iVFMul (StandingTree.vfPow x k) x) : N')
      = iVFMul (StandingTree.vfPow (g x) k) (g x)
    rw [map_iVFMul, map_vfPow g x k]

theorem map_vfSum (g : M ↪[LRV] N') (F : ℕ → M) : ∀ n : ℕ,
    (g (M7Hens.vfSum F n) : N') = M7Hens.vfSum (fun i => g (F i)) n
  | 0 => rfl
  | (k + 1) => by
    show (g (iVFAdd (M7Hens.vfSum F k) (F (k + 1))) : N')
      = iVFAdd (M7Hens.vfSum (fun i => g (F i)) k) (g (F (k + 1)))
    rw [map_iVFAdd, map_vfSum g F k]

theorem map_vfEval (g : M ↪[LRV] N') (a : ℕ → M) (n : ℕ) (x : M) :
    (g (M7Hens.vfEval a n x) : N') = M7Hens.vfEval (fun i => g (a i)) n (g x) := by
  unfold M7Hens.vfEval
  rw [map_vfSum]
  congr 1
  funext i
  show (g (iVFMul (a i) (StandingTree.vfPow x i)) : N')
    = iVFMul (g (a i)) (StandingTree.vfPow (g x) i)
  rw [map_iVFMul, map_vfPow]

/-- `vfSum` depends only on the values `i ≤ n`. -/
theorem vfSum_congr (n : ℕ) {F F' : ℕ → M} (h : ∀ i, i ≤ n → F i = F' i) :
    M7Hens.vfSum F n = M7Hens.vfSum F' n := by
  induction n with
  | zero => exact h 0 (le_refl 0)
  | succ k ih =>
    show iVFAdd (M7Hens.vfSum F k) (F (k + 1))
      = iVFAdd (M7Hens.vfSum F' k) (F' (k + 1))
    rw [ih (fun i hi => h i (by omega)), h (k + 1) (le_refl _)]

/-- **`RootLiftN` holds when `f` extends to a global monomorphism.**  `b i := g (a i)` (`i ≤ n`),
`d := g m`: the image polynomial has the root `g e` in the class `g (rv e) = f (rv e)`. -/
theorem rootLiftN_of_global_extension {S : LRV.Substructure M} {f : S ↪[LRV] N} {a : ℕ → M}
    {n : ℕ} {m : M} (hmem : ∀ i, i ≤ n → a i ∈ S) (hrv : iRv m ∈ S)
    (hvf : iVF m) (hroot : M5P1.IsRootOf a n m)
    (g : M ↪[LRV] N) (hg : ∀ x : S, (g x : N) = f x) :
    RootLiftN S f a n m hmem hrv := by
  refine ⟨fun i => if i ≤ n then g (a i) else Transfer.iVFZero (M := N),
    g m, map_iVFRel g hvf, ?_, ?_, ?_⟩
  · rw [← map_iRvMap]
    simpa using hg ⟨iRv m, hrv⟩
  · intro i hi
    show (if i ≤ n then g (a i) else Transfer.iVFZero (M := N)) = f ⟨a i, hmem i hi⟩
    rw [if_pos hi]
    exact hg ⟨a i, hmem i hi⟩
  · have hcongr : M7Hens.vfEval
        (fun i => if i ≤ n then g (a i) else Transfer.iVFZero (M := N)) n (g m)
        = M7Hens.vfEval (fun i => g (a i)) n (g m) := by
      unfold M7Hens.vfEval
      refine vfSum_congr n (fun i hi => ?_)
      simp only [if_pos hi]
    rw [hcongr, ← map_vfEval, hroot, map_iVFZero]

end Transport

/-! ## 7. `root_lift` is not consumed by the slot reduction

`slot_of_liftAllRoot` derives the ledger's one-step conclusion from `embed` and `class_control`
alone; the fields `monic`, `vf`, `unit`, `root`, `hensel`, `root_lift` of `LiftAllRoot` are never
looked at.  So `root_lift` is not a residual *of the slot*, only of a proof of `embed`: it supplies
the root `d` that the henselianity/embedding step needs. -/

/-- **The 3.4 slot conclusion needs only `embed` and `class_control`.**  Stated with the two fields
as hypotheses (no `LiftAllRoot` around them) so that the unused fields are visible. -/
theorem slot_of_embed_and_classControl {S : LRV.Substructure M} {f : S ↪[LRV] N} {m : M}
    (hS : Assembly.Standing S)
    (hembed : ∃ g : (Substructure.closure LRV ((S : Set M) ∪ {m})) ↪[LRV] N,
      ∀ x : S, g ⟨(x : M), Substructure.subset_closure (Or.inl x.2)⟩ = f x)
    (hcc : M5L.ResidualClasses S (Substructure.closure LRV ((S : Set M) ∪ {m}))) :
    ∃ (T : LRV.Substructure M) (g : T ↪[LRV] N) (hST : S ≤ T),
      (∀ x : S, g ⟨(x : M), hST x.2⟩ = f x) ∧ m ∈ T ∧ Assembly.Standing T := by
  obtain ⟨g, hagree⟩ := hembed
  refine ⟨Substructure.closure LRV ((S : Set M) ∪ {m}), g,
    fun _ hx => Substructure.subset_closure (Or.inl hx), hagree,
    Substructure.subset_closure (Or.inr rfl), ?_⟩
  exact M5P1.standing_closure_of_classControl hS hcc

/-- **The slot conclusion does not use `root_lift`** (nor `monic`, `vf`, `unit`, `root`,
`hensel`, `rv_mem`): the same conclusion follows from `embed` and `class_control` alone.  Stated as
a wrapper so the redundancy is machine-checked and a consumer cannot mistake `root_lift` for a
residual of the *slot*: it is a residual of `embed`. -/
theorem liftAllRoot_weak_of (S : LRV.Substructure M) (f : S ↪[LRV] N) (a : ℕ → M) (n : ℕ) (m : M)
    (hS : Assembly.Standing S)
    (hembed : ∃ g : (Substructure.closure LRV ((S : Set M) ∪ {m})) ↪[LRV] N,
      ∀ x : S, g ⟨(x : M), Substructure.subset_closure (Or.inl x.2)⟩ = f x)
    (hcc : M5L.ResidualClasses S (Substructure.closure LRV ((S : Set M) ∪ {m}))) :
    ∃ (T : LRV.Substructure M) (g : T ↪[LRV] N) (hST : S ≤ T),
      (∀ x : S, g ⟨(x : M), hST x.2⟩ = f x) ∧ m ∈ T ∧ Assembly.Standing T :=
  slot_of_embed_and_classControl hS hembed hcc

/-! ## 8. What the residue chain cannot do: `hpre` is an independent condition

`M6Wire.hred_of_residue_chain_k` turns the residue chain of `M6Wire2` into `hred`.  Beyond the chain
equation `rvChain F b I i₀ = iRVZero` it needs the **prefix-units condition**: every proper partial
sum of the `iKAdd` chain must be a unit of the valuation ring.  That condition is not in the paper
(where `F̄(t) = 0` is an equation in the residue field, order-independent) and it is not implied by
the 3.4 data:

* §8a: a concrete 3.4 datum — `F = X³ − X² − X + 1 = (X−1)²(X+1)`, `e = 1 ∈ U(M)` — for which
  `hred` holds (§3) but the prefix-units condition **fails** at the pivot `i₀ = 0`;
* §8b: the reason, which is a property of the frozen encoding and not of the paper: `Axioms.kAddLink`
  relates `iKAdd` to `VF`-addition only when *both* summands are units, so a chain that passes
  through a non-unit prefix sum reads the otherwise unconstrained value `iKAdd iRVZero x`;
* consequence: at this datum the tree's residue-chain route cannot produce `hred`, and the `N`-side
  `root_lift` therefore needs either the prefix-units condition as an explicit hypothesis (a
  strengthening of the paper's data) or a residue-sum gadget that does not go through `iKAdd`-chains.
  A *different* pivot can satisfy the condition — it is a choice, not an obstruction — but nothing in
  the paper's hypotheses selects the pivot. -/

section ChainGap

/-- The coefficient function of `F = X³ − X² − X + 1`. -/
noncomputable def aFour : ℕ → M :=
  fun i => if i = 0 then Transfer.iVFOne (M := M)
    else if i = 1 then iVFNeg (Transfer.iVFOne (M := M))
    else if i = 2 then iVFNeg (Transfer.iVFOne (M := M))
    else if i = 3 then Transfer.iVFOne (M := M)
    else Transfer.iVFZero (M := M)

theorem aFour_zero : aFour (M := M) 0 = Transfer.iVFOne (M := M) := by
  unfold aFour; rw [if_pos rfl]

theorem aFour_one : aFour (M := M) 1 = iVFNeg (Transfer.iVFOne (M := M)) := by
  unfold aFour; rw [if_neg (by norm_num), if_pos rfl]

theorem aFour_two : aFour (M := M) 2 = iVFNeg (Transfer.iVFOne (M := M)) := by
  unfold aFour; rw [if_neg (by norm_num), if_neg (by norm_num), if_pos rfl]

theorem aFour_three : aFour (M := M) 3 = Transfer.iVFOne (M := M) := by
  unfold aFour
  rw [if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num), if_pos rfl]

theorem aFour_other {i : ℕ} (h0 : i ≠ 0) (h1 : i ≠ 1) (h2 : i ≠ 2) (h3 : i ≠ 3) :
    aFour (M := M) i = Transfer.iVFZero (M := M) := by
  unfold aFour
  rw [if_neg h0, if_neg h1, if_neg h2, if_neg h3]

theorem aFour_vf (i : ℕ) : iVF (aFour (M := M) i) := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ (i ≠ 0 ∧ i ≠ 1 ∧ i ≠ 2 ∧ i ≠ 3)) with
    h | h | h | h | ⟨h0, h1, h2, h3⟩
  · rw [h, aFour_zero]; exact Transfer.vf_one_mem (M := M) hM
  · rw [h, aFour_one]; exact vf_neg_mem (M := M) hM (Transfer.vf_one_mem (M := M) hM)
  · rw [h, aFour_two]; exact vf_neg_mem (M := M) hM (Transfer.vf_one_mem (M := M) hM)
  · rw [h, aFour_three]; exact Transfer.vf_one_mem (M := M) hM
  · rw [aFour_other h0 h1 h2 h3]; exact vf_zero_mem (M := M) hM

theorem aFour_int {i : ℕ} (hi : i ≤ 3) : iLe iRVOne (iRv (aFour (M := M) i)) := by
  have h1VF : iVF (Transfer.iVFOne (M := M)) := Transfer.vf_one_mem (M := M) hM
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with h | h | h | h
  · rw [h, aFour_zero, RVCalc.rv_one hM]
    exact RVCalc.le_refl_rv hM (Transfer.rv_one_mem hM)
  · rw [h, aFour_one]
    have hc := (rv_neg_class (M := M) hM h1VF).2
    rwa [RVCalc.rv_one hM] at hc
  · rw [h, aFour_two]
    have hc := (rv_neg_class (M := M) hM h1VF).2
    rwa [RVCalc.rv_one hM] at hc
  · rw [h, aFour_three, RVCalc.rv_one hM]
    exact RVCalc.le_refl_rv hM (Transfer.rv_one_mem hM)

theorem monicO_aFour : M5P1.MonicO (⊤ : LRV.Substructure M) (aFour (M := M)) 3 := by
  refine ⟨by norm_num, fun i _ => trivial, aFour_vf, fun i hi => aFour_int hi, aFour_three, ?_⟩
  intro i hi
  exact aFour_other (by omega) (by omega) (by omega) (by omega)

/-- Powers of `1` in the `VF` sort are `1`. -/
theorem vfPow_one (k : ℕ) :
    StandingTree.vfPow (M := M) (Transfer.iVFOne (M := M)) k = Transfer.iVFOne (M := M) := by
  induction k with
  | zero => rfl
  | succ j ih =>
    show iVFMul (StandingTree.vfPow (M := M) (Transfer.iVFOne (M := M)) j)
      (Transfer.iVFOne (M := M)) = Transfer.iVFOne (M := M)
    rw [ih]
    exact RVCalc.vf_mul_one (M := M) hM (Transfer.vf_one_mem (M := M) hM)

/-- **`1` is a root of `X³ − X² − X + 1`** — the 3.4 datum of §8 has a genuine unit root.
Computed in the encoding's own operations (`iVFAdd`/`iVFMul`), because `Polynomial.eval` at
`Transfer.VFType` is not rewrite-friendly (its `Add`/`Mul` instances arrive through the
`noncomputable Field` structure). -/
theorem isRootOf_aFour : M5P1.IsRootOf (aFour (M := M)) 3 (Transfer.iVFOne (M := M)) := by
  have h1 : iVF (Transfer.iVFOne (M := M)) := Transfer.vf_one_mem (M := M) hM
  have hn : iVF (iVFNeg (Transfer.iVFOne (M := M))) := vf_neg_mem (M := M) hM h1
  have e0 : iVFMul (aFour (M := M) 0)
      (StandingTree.vfPow (M := M) (Transfer.iVFOne (M := M)) 0) = Transfer.iVFOne (M := M) := by
    rw [aFour_zero]
    exact RVCalc.vf_mul_one (M := M) hM h1
  have e1 : iVFMul (aFour (M := M) 1)
      (StandingTree.vfPow (M := M) (Transfer.iVFOne (M := M)) 1) = iVFNeg (Transfer.iVFOne (M := M)) := by
    rw [aFour_one, vfPow_one]
    exact RVCalc.vf_mul_one (M := M) hM hn
  have e2 : iVFMul (aFour (M := M) 2)
      (StandingTree.vfPow (M := M) (Transfer.iVFOne (M := M)) 2) = iVFNeg (Transfer.iVFOne (M := M)) := by
    rw [aFour_two, vfPow_one]
    exact RVCalc.vf_mul_one (M := M) hM hn
  have e3 : iVFMul (aFour (M := M) 3)
      (StandingTree.vfPow (M := M) (Transfer.iVFOne (M := M)) 3) = Transfer.iVFOne (M := M) := by
    rw [aFour_three, vfPow_one]
    exact RVCalc.vf_mul_one (M := M) hM h1
  unfold M5P1.IsRootOf M7Hens.vfEval
  show iVFAdd (iVFAdd (iVFAdd
      (iVFMul (aFour (M := M) 0) (StandingTree.vfPow (M := M) (Transfer.iVFOne (M := M)) 0))
      (iVFMul (aFour (M := M) 1) (StandingTree.vfPow (M := M) (Transfer.iVFOne (M := M)) 1)))
      (iVFMul (aFour (M := M) 2) (StandingTree.vfPow (M := M) (Transfer.iVFOne (M := M)) 2)))
      (iVFMul (aFour (M := M) 3) (StandingTree.vfPow (M := M) (Transfer.iVFOne (M := M)) 3))
      = Transfer.iVFZero (M := M)
  rw [e0, e1, e2, e3, RVCalc.vf_add_neg (M := M) hM h1, RVCalc.vf_zero_add (M := M) hM hn,
    RVCalc.vf_add_comm (M := M) hM hn h1, RVCalc.vf_add_neg (M := M) hM h1]

/-- `rv (-1)` is a unit of the residue field: `-1` has the same `RV`-class as `1`. -/
theorem units_rv_neg_one : iUnits (iRv (iVFNeg (Transfer.iVFOne (M := M)))) := by
  have h1 : iVF (Transfer.iVFOne (M := M)) := Transfer.vf_one_mem (M := M) hM
  have hn : iVF (iVFNeg (Transfer.iVFOne (M := M))) := vf_neg_mem (M := M) hM h1
  have hcl := rv_neg_class (M := M) hM h1
  rw [RVCalc.rv_one hM] at hcl
  refine (RVCalc.units_iff_le_one hM (Transfer.rv_mem hM hn) ?_).mpr ⟨hcl.2, hcl.1⟩
  intro hz
  exact RVCalc.vf_neg_one_ne_zero (M := M) hM (RVCalc.vf_eq_zero_of_rv_eq_zero hM hn hz)

/-- `(1 : VF(Ŝ)) + (-1) = 0` in the encoding's own addition. -/
theorem one_add_neg_one : (((1 : Transfer.VFType (M := M)) + (-1) : Transfer.VFType (M := M)))
    = 0 := by
  apply Subtype.ext
  show iVFAdd (Transfer.iVFOne (M := M)) (iVFNeg (Transfer.iVFOne (M := M)))
    = Transfer.iVFZero (M := M)
  exact RVCalc.vf_add_neg (M := M) hM (Transfer.vf_one_mem (M := M) hM)

/-- `1 + (-1)` is **not** a unit — the residue sum vanishes. -/
theorem not_units_one_add_neg_one :
    ¬ iUnits (iRv (((1 : Transfer.VFType (M := M)) + (-1) : Transfer.VFType (M := M))).1) := by
  rw [one_add_neg_one]
  show ¬ iUnits (iRv (Transfer.iVFZero (M := M)))
  rw [RVCalc.rv_zero_eq hM]
  exact fun h => GammaGroup.units_ne_zero h rfl

/-- **`iKAdd` at the first two terms of `F̄` is already `rvZero`**: the chain of the reduction of
`X³ − X² − X + 1` collapses after two terms, because `rv 1` and `rv (-1)` are units whose sum is
`0`.  This is `Axioms.kAddLink`'s *second* branch (`M6Wire.iKAddLink_pair`), the only information
the frozen axioms give about a `K`-sum that has dropped into the maximal ideal. -/
theorem iKAdd_one_neg_one :
    iKAdd (iRv (Transfer.iVFOne (M := M))) (iRv (iVFNeg (Transfer.iVFOne (M := M))))
      = iRVZero := by
  have h := (M6Wire.iKAddLink_pair (M := M) (u := (1 : Transfer.VFType (M := M)))
    (v := (-1 : Transfer.VFType (M := M)))
    (by show iUnits (iRv (Transfer.iVFOne (M := M)))
        rw [RVCalc.rv_one hM]
        exact StandingTree.rv_one_units)
    (by show iUnits (iRv (iVFNeg (Transfer.iVFOne (M := M))))
        exact units_rv_neg_one)).2
  refine h ?_
  show ¬ iUnits (iRv (((1 : Transfer.VFType (M := M)) + (-1) : Transfer.VFType (M := M))).1)
  exact not_units_one_add_neg_one

/-- **The prefix-units condition `hpre`** of `M6Wire.hred_of_residue_chain_k` and
`rv_root_lift_encoding_of_chain`, as a standalone predicate: every *proper* partial sum of the
`iKAdd` chain of `F` at `b` over `I`, pivot `i₀`, is a unit of the valuation ring. -/
noncomputable def PrefixUnits (F : Polynomial (Transfer.VFType (M := M)))
    (b : Transfer.VFType (M := M)) (I : Finset ℕ) (i₀ : ℕ) : Prop :=
  ∀ k, k < (((I.erase i₀).sort (· ≤ ·)).map (fun i => F.coeff i * b ^ i)).length →
    iUnits (iRv (((F.coeff i₀ * b ^ i₀)
      + (((((I.erase i₀).sort (· ≤ ·)).map (fun i => F.coeff i * b ^ i)).take k).sum)).1))

/-- **`PrefixUnits` is exactly what the chain route needs and nothing more**: the term at `k = 1`
is the sum of the pivot's term and the first term of the chain, so if that sum is a non-unit the
condition fails.  (`k = 1` is written `(·).take 1).sum` rather than `List.headI`, because
`Transfer.VFType` carries no `Inhabited` instance and `sum` of a singleton is the same term.) -/
theorem not_prefixUnits_of_first {F : Polynomial (Transfer.VFType (M := M))}
    {b : Transfer.VFType (M := M)} {I : Finset ℕ} {i₀ : ℕ}
    (hlen : 1 < (((I.erase i₀).sort (· ≤ ·)).map (fun i => F.coeff i * b ^ i)).length)
    (hnu : ¬ iUnits (iRv (((F.coeff i₀ * b ^ i₀)
      + ((((I.erase i₀).sort (· ≤ ·)).map (fun i => F.coeff i * b ^ i)).take 1).sum)).1)) :
    ¬ PrefixUnits F b I i₀ := by
  intro h
  exact hnu (h 1 hlen)

/-- The same failure, read through a decomposition `F`-coefficient list `= v :: l`: the `k = 1`
partial sum is the pivot term plus `v`.  This is the form in which the chain lemmas of
`M6Wire`/`M6Wire2` supply their data (they know the head of the chain, not its `sort`). -/
theorem not_prefixUnits_of_cons {F : Polynomial (Transfer.VFType (M := M))}
    {b : Transfer.VFType (M := M)} {I : Finset ℕ} {i₀ : ℕ} {v : Transfer.VFType (M := M)}
    {l : List (Transfer.VFType (M := M))}
    (hv : ((I.erase i₀).sort (· ≤ ·)).map (fun i => F.coeff i * b ^ i) = v :: l)
    (hl : 0 < l.length)
    (hnu : ¬ iUnits (iRv (((F.coeff i₀ * b ^ i₀) + v : Transfer.VFType (M := M))).1)) :
    ¬ PrefixUnits F b I i₀ := by
  have hlen : 1 < (((I.erase i₀).sort (· ≤ ·)).map (fun i => F.coeff i * b ^ i)).length := by
    rw [hv]; simpa using hl
  refine not_prefixUnits_of_first hlen ?_
  have hsum : ((v :: l).take 1).sum = v := by
    simp only [List.take_succ_cons, List.take_zero, List.sum_cons, List.sum_nil]
    exact add_zero v
  rw [hv, hsum]
  exact hnu

theorem coeff_PL_val {a : ℕ → M} {hVF : ∀ i, iVF (a i)} {n i : ℕ} (hi : i ≤ n) :
    ((PL a hVF n).coeff i).1 = a i := by
  rw [coeff_PL hi]
  rfl

/-- `1` is idempotent under powers in the `VF` sort. -/
theorem vfType_one_pow (k : ℕ) : (1 : Transfer.VFType (M := M)) ^ k = 1 := by
  induction k with
  | zero => exact pow_zero 1
  | succ j ih => rw [pow_succ, ih]; exact one_mul 1

/-- `rv 0` is not a unit — the residue of `0` vanishes. -/
theorem not_units_zero : ¬ iUnits (iRv (Transfer.iVFZero (M := M))) := by
  rw [RVCalc.rv_zero_eq hM]
  exact fun h => GammaGroup.units_ne_zero h rfl

/-- The three terms of the 3.4 chain of `X³ − X² − X + 1` over the pivot `0`, computed in the
encoding's own operations: `a₁·1 = -1`, `a₂·1 = -1`, `a₃·1 = 1`. -/
theorem aFour_chain_one :
    ((PL (aFour (M := M)) aFour_vf 3).coeff 1 * (1 : Transfer.VFType (M := M)) ^ 1
      : Transfer.VFType (M := M)) = (-1 : Transfer.VFType (M := M)) := by
  rw [pow_one]
  apply Subtype.ext
  show iVFMul ((PL (aFour (M := M)) aFour_vf 3).coeff 1).1 (Transfer.iVFOne (M := M))
    = iVFNeg (Transfer.iVFOne (M := M))
  rw [coeff_PL_val (a := aFour (M := M)) (hVF := aFour_vf (M := M)) (n := 3) (i := 1)
    (by norm_num), aFour_one]
  exact RVCalc.vf_mul_one (M := M) hM
    (vf_neg_mem (M := M) hM (Transfer.vf_one_mem (M := M) hM))

theorem aFour_chain_two :
    ((PL (aFour (M := M)) aFour_vf 3).coeff 2 * (1 : Transfer.VFType (M := M)) ^ 2
      : Transfer.VFType (M := M)) = (-1 : Transfer.VFType (M := M)) := by
  rw [vfType_one_pow]
  apply Subtype.ext
  show iVFMul ((PL (aFour (M := M)) aFour_vf 3).coeff 2).1 (Transfer.iVFOne (M := M))
    = iVFNeg (Transfer.iVFOne (M := M))
  rw [coeff_PL_val (a := aFour (M := M)) (hVF := aFour_vf (M := M)) (n := 3) (i := 2)
    (by norm_num), aFour_two]
  exact RVCalc.vf_mul_one (M := M) hM
    (vf_neg_mem (M := M) hM (Transfer.vf_one_mem (M := M) hM))

theorem aFour_chain_three :
    ((PL (aFour (M := M)) aFour_vf 3).coeff 3 * (1 : Transfer.VFType (M := M)) ^ 3
      : Transfer.VFType (M := M)) = (1 : Transfer.VFType (M := M)) := by
  rw [vfType_one_pow]
  apply Subtype.ext
  show iVFMul ((PL (aFour (M := M)) aFour_vf 3).coeff 3).1 (Transfer.iVFOne (M := M))
    = Transfer.iVFOne (M := M)
  rw [coeff_PL_val (a := aFour (M := M)) (hVF := aFour_vf (M := M)) (n := 3) (i := 3)
    (by norm_num), aFour_three]
  exact RVCalc.vf_mul_one (M := M) hM (Transfer.vf_one_mem (M := M) hM)

/-- **The `k = 1` term of the 3.4 chain is `1 + (-1) = 0`** at the polynomial
`X³ − X² − X + 1`: its `0`-th coefficient is `1` and the first term of the chain over the unit
support `{1,2,3}` is `a₁ · 1 = -1`. -/
theorem firstTerm_aFour :
    ¬ iUnits (iRv ((((PL (aFour (M := M)) aFour_vf 3).coeff 0
        * (1 : Transfer.VFType (M := M)) ^ 0
      + (-1 : Transfer.VFType (M := M)) : Transfer.VFType (M := M))).1)) := by
  have h0 : ((PL (aFour (M := M)) aFour_vf 3).coeff 0
        * (1 : Transfer.VFType (M := M)) ^ 0 + (-1 : Transfer.VFType (M := M))
        : Transfer.VFType (M := M))
      = ((1 : Transfer.VFType (M := M)) + (-1) : Transfer.VFType (M := M)) := by
    rw [pow_zero]
    apply Subtype.ext
    show iVFAdd (iVFMul ((PL (aFour (M := M)) aFour_vf 3).coeff 0).1
        (Transfer.iVFOne (M := M))) (iVFNeg (Transfer.iVFOne (M := M)))
      = iVFAdd (Transfer.iVFOne (M := M)) (iVFNeg (Transfer.iVFOne (M := M)))
    rw [coeff_PL_val (a := aFour (M := M)) (hVF := aFour_vf (M := M)) (n := 3) (i := 0)
      (by norm_num), aFour_zero]
    exact congrArg (fun t => iVFAdd t (iVFNeg (Transfer.iVFOne (M := M))))
      (RVCalc.vf_mul_one (M := M) hM (Transfer.vf_one_mem (M := M) hM))
  rw [h0]
  exact not_units_one_add_neg_one

/-- **§8, the finding: `hpre` is not implied by the residue equation.**  At the 3.4 datum
`F = X³ − X² − X + 1` (monic over `O(Ŝ)` by `monicO_aFour`, `1` a unit root by `isRootOf_aFour`,
so `hred` holds by §3), pivot `i₀ = 0` and unit support `I` with `(I.erase 0).sort = [1,2,3]`,
the prefix-units condition `PrefixUnits` **fails**: its `k = 1` instance is `1 + (-1) = 0`, not a
unit.  So `M6Wire.hred_of_residue_chain_k` cannot be applied to this configuration — `hpre` is an
independent side condition on the pivot, not a consequence of the residue equation, and the frozen
`L_RV` links `iKAdd` to `VF`-addition only when *both* summands are units
(`Axioms.kAddLink`), which is exactly what fails here.

Non-vacuity of `hs`: `sort` of `{1,2,3}` is the sorted list `[1,2,3]` (mathematically determined:
`sort` is a sorted permutation and `[1,2,3]` is the unique such list); the kernel's `decide` cannot
check it because `Finset.sort` does not reduce, so `hs` carries the pinning of `I` (the intended
instance is `I = {0,1,2,3}`). -/
theorem chain_prefix_units_not_automatic {I : Finset ℕ}
    (hs : (I.erase 0).sort (· ≤ ·) = [1, 2, 3]) :
    ¬ PrefixUnits (PL (aFour (M := M)) aFour_vf 3) 1 I 0 := by
  refine not_prefixUnits_of_cons (v := (-1 : Transfer.VFType (M := M))) (l := [-1, 1]) ?_ ?_ ?_
  · rw [hs]
    show ((PL (aFour (M := M)) aFour_vf 3).coeff 1 * (1 : Transfer.VFType (M := M)) ^ 1)
        :: ((PL (aFour (M := M)) aFour_vf 3).coeff 2 * (1 : Transfer.VFType (M := M)) ^ 2)
        :: ((PL (aFour (M := M)) aFour_vf 3).coeff 3 * (1 : Transfer.VFType (M := M)) ^ 3)
        :: [] = (-1 : Transfer.VFType (M := M)) :: [-1, 1]
    rw [aFour_chain_one, aFour_chain_two, aFour_chain_three]
  · norm_num
  · exact firstTerm_aFour

end ChainGap

end SpecialTransformations.Milestone0.M5RootLift

/-! ## Axiom audit -/

#print axioms SpecialTransformations.Milestone0.M5RootLift.root_lift_at_M
#print axioms SpecialTransformations.Milestone0.M5RootLift.two_le_card_IDex
#print axioms SpecialTransformations.Milestone0.M5RootLift.hred_at_root
#print axioms SpecialTransformations.Milestone0.M5RootLift.rootLiftN_of_global_extension
#print axioms SpecialTransformations.Milestone0.M5RootLift.slot_of_embed_and_classControl
#print axioms SpecialTransformations.Milestone0.M5RootLift.liftAllRoot_weak_of
#print axioms SpecialTransformations.Milestone0.M5RootLift.chain_prefix_units_not_automatic
