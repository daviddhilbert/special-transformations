/-
**Lemma 3.2 wired into its consumption site.**

`M6Syntactic.lean` proves Lemma 3.2 (`rv:root:lift:vf`) with `hred` as a *hypothesis*:
`¬ iLe (iRv (∑ i ∈ I, F.coeff i * b ^ i)).1 iRVOne`, i.e. the partial sum over the support of the
reduction lies in the maximal ideal.  In the paper `hred` is never a hypothesis: it is the residue
equation `F̄(t) = 0`, and turning one into the other is the only place where the two sides of `rv`
have to be related.  This file supplies that step in the two situations in which it occurs.

* **`hred_of_isRoot`** — the `M`-side situation of Lemma 3.4 (`e ∈ U(M)` is a root of
  `F ∈ Ô(S)[X]`).  There `hred` is automatic: the coefficients outside the support `I` of the
  reduction are non-units, hence in `M`, and `F(b) = 0` makes the `I`-part minus their sum.  No
  residue calculus is involved, because `F(b) = 0` is already a `VF`-equation.

* **`rvFold`** — the `N`-side situation.  `F̄(t) = 0` is an equation in the residue field, whose
  addition is the encoding's `iKAdd`.  The frozen axiom `kAddLink` relates `iKAdd` to `VF`-addition
  only when *both* summands are units (value `1`), so a residue sum is **not** a `Finset`-sum: it
  is a chain, and only its intermediate values being units makes it mean anything.  `rvFold` is
  that chain, and `rvFold_cases` is `kAddLink` iterated along it.

* **`hred_of_residue_chain`** and **`rv_root_lift_encoding_of_chain`** — Lemma 3.2 with `hred`
  replaced by the chain condition, i.e. in the shape the residue case of Lemmas 3.4/3.5/3.6
  consumes.

`#print axioms` of every headline theorem is `{propext, Classical.choice, Quot.sound}`.
-/
import M6Syntactic

open FirstOrder FirstOrder.Language
open Polynomial
open SpecialTransformations.Milestone0
open SpecialTransformations.Milestone0.LRV

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace SpecialTransformations.Milestone0.M6Wire

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-! ## 0. An integral non-unit lies in the maximal ideal -/

/-- **`iLe`-form of "integral but not a unit".**  If `rv c` is `≥ 1` (i.e. `c` lies in the
valuation ring) and is not a unit of the residue field, then `rv c` is not `≤ 1` either, i.e. `c`
lies in the maximal ideal.  This is the step that reads the paper's `vrv(rv(b_i) t^i) > 0` for
`t_i = 0` off the hypothesis that `b_i` is a non-unit of `O`. -/
theorem not_le_one_of_integral_not_units {c : Transfer.VFType (M := M)}
    (hO : iLe iRVOne (iRv c.1)) (hU : ¬ iUnits (iRv c.1)) :
    ¬ iLe (iRv c.1) iRVOne := by
  intro h
  have hne : iRv c.1 ≠ iRVZero := by
    intro hz
    exact M6Syntactic.not_le_zero_one (M := M) (hM := hM) (hz ▸ h)
  exact hU ((RVCalc.units_iff_le_one hM (Transfer.rv_mem hM c.2) hne).mpr ⟨hO, h⟩)

/-! ## 1. `O` is closed under powers -/

variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
variable {w : Valuation (Transfer.VFType (M := M)) Γ}

/-- `O` is closed under powers. -/
theorem one_le_pow (hw : ∀ x y : Transfer.VFType (M := M), VFValued.predV x y ↔ w x ≤ w y)
    {b : Transfer.VFType (M := M)} (hb : iLe iRVOne (iRv b.1)) (n : ℕ) :
    iLe iRVOne (iRv ((b ^ n)).1) := by
  induction n with
  | zero =>
      have h1 : iRv ((b ^ 0 : Transfer.VFType (M := M))).1 = iRVOne := by
        rw [pow_zero]
        exact RVCalc.rv_one hM
      exact h1.symm ▸ RVCalc.le_refl_rv hM (Transfer.rv_one_mem hM)
  | succ n ih =>
      have h1 : (b ^ (n + 1) : Transfer.VFType (M := M)) = b ^ n * b := pow_succ b n
      have h2 : iRv ((b ^ (n + 1) : Transfer.VFType (M := M))).1
          = iRv ((b ^ n * b : Transfer.VFType (M := M))).1 :=
        congrArg (fun t : Transfer.VFType (M := M) => iRv t.1) h1
      exact h2.symm ▸ M6Syntactic.one_le_mul hw ih hb

/-- A sum of integral elements is integral, in `List` form (the shape the chain proof needs). -/
theorem one_le_list_sum (hw : ∀ x y : Transfer.VFType (M := M), VFValued.predV x y ↔ w x ≤ w y)
    (x : Transfer.VFType (M := M)) (l : List (Transfer.VFType (M := M)))
    (hx : iLe iRVOne (iRv x.1)) (h : ∀ u ∈ l, iLe iRVOne (iRv u.1)) :
    iLe iRVOne (iRv ((x + l.sum)).1) := by
  induction l generalizing x with
  | nil =>
      have hsumz : (x + ([] : List (Transfer.VFType (M := M))).sum)
          = x := by
        rw [List.sum_nil]
        exact add_zero x
      exact hsumz.symm ▸ hx
  | cons u t ih =>
      have hu : iLe iRVOne (iRv u.1) := h u (by simp)
      have ht : ∀ z ∈ t, iLe iRVOne (iRv z.1) := fun z hz => h z (by simp [hz])
      have hsum : (u :: t).sum = u + t.sum := List.sum_cons
      have hassoc : x + (u + t.sum) = (x + u) + t.sum := (add_assoc x u t.sum).symm
      rw [hsum, hassoc]
      exact ih (x + u) (M6Syntactic.one_le_add hw hx hu) ht

/-! ## 2. `hred` from a genuine root

Lemma 3.4 works in `M`: `e ∈ U(M)` is a root of `F ∈ Ô(S)[X]`.  There `hred` is not an input, it
follows from the root equation and the integrality of the coefficients. -/

/-- **`hred` is automatic at a root.**  If every coefficient of `F` is integral, `b` is integral,
`I` is a set of indices at which the coefficients are units, and every *other* coefficient of the
support is a non-unit, then `F(b) = 0` forces `∑ i ∈ I, F.coeff i * b ^ i` into the maximal ideal.

This is the paper's `F̄(t) = 0` step with `t = rv b` **at a root**, where no residue-field addition
is needed because `0 = F(b)` is already a `VF`-equation. -/
theorem hred_of_isRoot (hw : ∀ x y : Transfer.VFType (M := M), VFValued.predV x y ↔ w x ≤ w y)
    {F : (Transfer.VFType (M := M))[X]} {b : Transfer.VFType (M := M)}
    (hint : ∀ i ∈ F.support, iLe iRVOne (iRv (F.coeff i).1))
    (hbO : iLe iRVOne (iRv b.1)) (hroot : F.IsRoot b)
    (I : Finset ℕ) (hIsub : ∀ i ∈ I, i ∈ F.support)
    (hInot : ∀ i ∈ F.support, i ∉ I → ¬ iUnits (iRv (F.coeff i).1)) :
    ¬ iLe (iRv (∑ i ∈ I, F.coeff i * b ^ i).1) iRVOne := by
  have h0 : (∑ i ∈ F.support, F.coeff i * b ^ i) = 0 := by
    have h1 := hroot
    rw [Polynomial.IsRoot.def, Polynomial.eval_eq_sum, Polynomial.sum_def] at h1
    exact h1
  have hsdiff := Finset.sum_sdiff (f := fun i => F.coeff i * b ^ i) hIsub
  rw [h0] at hsdiff
  have hcompl : ¬ iLe (iRv (∑ i ∈ F.support \ I, F.coeff i * b ^ i).1) iRVOne := by
    refine M6Syntactic.lt_one_sum hw _ _ (fun i hi => ?_)
    obtain ⟨hi', hiI⟩ := Finset.mem_sdiff.mp hi
    have hcM : ¬ iLe (iRv (F.coeff i).1) iRVOne :=
      not_le_one_of_integral_not_units (hint i hi') (hInot i hi' hiI)
    have hbpow : iLe iRVOne (iRv ((b ^ i)).1) := one_le_pow hw hbO i
    exact M6Syntactic.lt_one_mul hw hcM hbpow
  have heq : (∑ i ∈ I, F.coeff i * b ^ i)
      = -(∑ i ∈ F.support \ I, F.coeff i * b ^ i) :=
    eq_neg_of_add_eq_zero_right hsdiff
  rw [heq]
  exact M6Syntactic.lt_one_neg hw hcompl

/-- `hred_of_isRoot` in `L_RV`, with no valuation in the statement. -/
theorem hred_of_isRoot_LRV
    {F : (Transfer.VFType (M := M))[X]} {b : Transfer.VFType (M := M)}
    (hint : ∀ i ∈ F.support, iLe iRVOne (iRv (F.coeff i).1))
    (hbO : iLe iRVOne (iRv b.1)) (hroot : F.IsRoot b)
    (I : Finset ℕ) (hIsub : ∀ i ∈ I, i ∈ F.support)
    (hInot : ∀ i ∈ F.support, i ∉ I → ¬ iUnits (iRv (F.coeff i).1)) :
    ¬ iLe (iRv (∑ i ∈ I, F.coeff i * b ^ i).1) iRVOne := by
  obtain ⟨Γ, hΓ, w, hw⟩ := VFValued.exists_valuation_predV (M := M) (hM := hM)
  letI : LinearOrderedCommGroupWithZero Γ := hΓ
  exact hred_of_isRoot hw hint hbO hroot I hIsub hInot


/-! ## 3. The residue chain

`F̄(t) = 0` lives in the residue field, whose addition is the encoding's `iKAdd`.
`Axioms.kAddLink` compares `iKAdd` with `VF`-addition only when both summands are units, so the
residue evaluation of `F̄` at `t` is a **chain** `iKAdd (iKAdd … ) …`, and it means what the paper
means only while its intermediate values are units. -/

/-- **`Axioms.kAddLink`, as the pair of implications the chain proof needs.**  For two units `u`,
`v`: `iKAdd (rv u) (rv v)` is `rv (u + v)` when `u + v` is a unit and the residue zero otherwise. -/
theorem iKAddLink_pair {u v : Transfer.VFType (M := M)} (hu : iUnits (iRv u.1))
    (hv : iUnits (iRv v.1)) :
    (iUnits (iRv (u + v).1) → iKAdd (iRv u.1) (iRv v.1) = iRv (u + v).1) ∧
      (¬ iUnits (iRv (u + v).1) → iKAdd (iRv u.1) (iRv v.1) = iRVZero) := by
  have hlink := Transfer.allSorted_realize hM (ss := ![SortTag.vf, SortTag.vf])
    (φ := (pUnits (tRv &0) ⟹ (pUnits (tRv &1) ⟹
      ((pUnits (tRv (tVFAdd &0 &1)) ⟹
          pEq (tKAdd (tRv &0) (tRv &1)) (tRv (tVFAdd &0 &1))) ⊓
        (∼(pUnits (tRv (tVFAdd &0 &1))) ⟹
          pEq (tKAdd (tRv &0) (tRv &1)) tRVZero)))))
    M6Syntactic.mem_ACVF_kAddLink ![u.1, v.1] (by intro i; fin_cases i <;> simp [u.2, v.2])
  have h2 : iUnits (iRv u.1) → iUnits (iRv v.1) →
      ((iUnits (iRv (iVFAdd u.1 v.1)) → iKAdd (iRv u.1) (iRv v.1) = iRv (iVFAdd u.1 v.1)) ∧
       (¬ iUnits (iRv (iVFAdd u.1 v.1)) → iKAdd (iRv u.1) (iRv v.1) = iRVZero)) := by
    simpa [BoundedFormula.realize_imp, BoundedFormula.realize_inf, Transfer.pUnits_realize,
      pEq, BoundedFormula.realize_bdEqual, Transfer.realize_tRv, TrivCase.realize_tKAdd,
      Transfer.realize_tVFAdd, Transfer.realize_tRVZero, RVCalc.realize_var_inr,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] using hlink
  exact h2 hu hv

/-- **The `RV`-valued chain.**  Same fold as `rvFold`, on bare `RV`-elements; this is the form in
which a chain is pushed along an `LRV`-monomorphism (`map_kFold`), because it mentions `iKAdd` and
nothing else. -/
def kFold (acc : M) : List M → M
  | [] => acc
  | v :: l => kFold (iKAdd acc v) l

/-- **The chain pushes along an `LRV`-monomorphism.**  `kFold` is built from `iKAdd` alone, which is
a function symbol, so an `LRV`-embedding of substructures carries it across verbatim.  This is the
step by which the `M`-side residue equation `F̄(t) = 0` becomes its `N`-side counterpart, which
`iLe`/`iUnits` could not do (relations only transfer forward). -/
theorem map_kFold {N : Type} [LRV.Structure N] (S : LRV.Substructure M) (f : S ↪[LRV] N)
    (a : S) (l : List S) :
    (f (kFold a l) : N) = kFold (f a) (l.map f) := by
  induction l generalizing a with
  | nil => rfl
  | cons v t ih =>
      have hstep : kFold a (v :: t) = kFold (iKAdd a v) t := rfl
      rw [hstep]
      have hmap : (v :: t).map f = f v :: t.map f := rfl
      rw [hmap]
      have hstep2 : kFold (f a) (f v :: t.map f) = kFold (iKAdd (f a) (f v)) (t.map f) := rfl
      rw [hstep2]
      have e : (f (iKAdd a v) : N) = iKAdd (f a) (f v) := by
        have h1 := f.map_fun Fn.kAdd ![a, v]
        have h2 : (⇑f ∘ ![a, v]) = ![f a, f v] := by
          funext i; fin_cases i <;> rfl
        rw [h2] at h1
        exact h1
      rw [← e]
      exact ih (iKAdd a v)

/-- Rewriting `iUnits` along an equation of `VFType` (the `Subtype` coercion makes `rw` unusable
under `iRv ↑(…)`, so the ports are term-mode). -/
theorem iUnits_of_eq {a b : Transfer.VFType (M := M)} (h : a = b)
    (ha : iUnits (iRv a.1)) : iUnits (iRv b.1) :=
  (congrArg (fun t : Transfer.VFType (M := M) => iRv t.1) h) ▸ ha

theorem not_iUnits_of_eq {a b : Transfer.VFType (M := M)} (h : a = b)
    (ha : ¬ iUnits (iRv a.1)) : ¬ iUnits (iRv b.1) :=
  (congrArg (fun t : Transfer.VFType (M := M) => iRv t.1) h) ▸ ha

theorem iRv_of_eq {a b : Transfer.VFType (M := M)} (h : a = b) :
    iRv a.1 = iRv b.1 :=
  congrArg (fun t : Transfer.VFType (M := M) => iRv t.1) h

theorem cons_sum_eq (x u : Transfer.VFType (M := M))
    (t : List (Transfer.VFType (M := M))) :
    x + (u :: t).sum = (x + u) + t.sum := by
  rw [List.sum_cons]
  exact (add_assoc x u t.sum).symm

theorem take_cons_sum_eq (x u : Transfer.VFType (M := M))
    (t : List (Transfer.VFType (M := M))) (k : ℕ) :
    x + ((u :: t).take (k + 1)).sum = (x + u) + (t.take k).sum := by
  rw [List.take_succ_cons, List.sum_cons]
  exact (add_assoc x u (t.take k).sum).symm

/-- **The residue chain.**  `iKAdd` folded along `l`, starting from the accumulated residue `acc`. -/
def rvFold (acc : M) : List (Transfer.VFType (M := M)) → M
  | [] => acc
  | u :: l => rvFold (iKAdd acc (iRv u.1)) l

/-- **`kAddLink` iterated along the chain.**  If `x` and every element of `l` are integral units,
and every *proper* partial sum `x + (l.take k).sum` (`k < l.length`) is a unit, then the chain
either ends at `rv` of the genuine `VF` partial sum (when that last one is a unit) or at the
residue zero.

The second branch is the paper's `F̄(t) = 0`: the last partial sum is then not a unit, and being
also integral it lies in the maximal ideal. -/
theorem rvFold_cases (hw : ∀ x y : Transfer.VFType (M := M), VFValued.predV x y ↔ w x ≤ w y)
    (x : Transfer.VFType (M := M)) (l : List (Transfer.VFType (M := M)))
    (hxO : iLe iRVOne (iRv x.1)) (hxU : iUnits (iRv x.1))
    (hO : ∀ u ∈ l, iLe iRVOne (iRv u.1))
    (hU : ∀ u ∈ l, iUnits (iRv u.1))
    (hpre : ∀ k, k < l.length → iUnits (iRv ((x + (l.take k).sum).1))) :
    (iUnits (iRv ((x + l.sum).1)) → rvFold (iRv x.1) l = iRv ((x + l.sum).1)) ∧
      (¬ iUnits (iRv ((x + l.sum).1)) → rvFold (iRv x.1) l = iRVZero) := by
  induction l generalizing x with
  | nil =>
      have hsumz : (x + ([] : List (Transfer.VFType (M := M))).sum) = x := by
        rw [List.sum_nil]
        exact add_zero x
      have hnil : rvFold (iRv x.1) ([] : List (Transfer.VFType (M := M))) = iRv x.1 := rfl
      constructor
      · intro _
        exact hnil.trans (iRv_of_eq hsumz).symm
      · intro hn
        exact absurd (iUnits_of_eq hsumz.symm hxU) hn
  | cons u t ih =>
      have hO' : iLe iRVOne (iRv u.1) := hO u (by simp)
      have hU' : iUnits (iRv u.1) := hU u (by simp)
      have hkey := iKAddLink_pair (u := x) (v := u) hxU hU'
      rcases t with _ | ⟨v, t'⟩
      · have hsum1 : (u :: ([] : List (Transfer.VFType (M := M)))).sum = u := by
          rw [List.sum_cons, List.sum_nil]
          exact add_zero u
        have hx' : x + (u :: ([] : List (Transfer.VFType (M := M)))).sum = x + u := by
          rw [hsum1]
        have hfold : rvFold (iRv x.1) (u :: ([] : List (Transfer.VFType (M := M))))
            = iKAdd (iRv x.1) (iRv u.1) := rfl
        constructor
        · intro hunit
          have hu' : iUnits (iRv ((x + u).1)) := iUnits_of_eq hx' hunit
          exact (iRv_of_eq hx').symm ▸ (hfold.trans (hkey.1 hu'))
        · intro hn
          exact hfold.trans (hkey.2 (not_iUnits_of_eq hx' hn))
      · have hu1 : iUnits (iRv ((x + u).1)) := by
          have h1 := hpre 1 (by simp)
          have htk : (u :: v :: t').take 1 = [u] := by
            rw [List.take_succ_cons, List.take_zero]
          have h2 : ([u] : List (Transfer.VFType (M := M))).sum = u := by
            rw [List.sum_cons, List.sum_nil]
            exact add_zero u
          have heq : x + ((u :: v :: t').take 1).sum = x + u := by
            rw [htk]
            exact congrArg (fun s : Transfer.VFType (M := M) => x + s) h2
          exact iUnits_of_eq heq h1
        have hx'O : iLe iRVOne (iRv ((x + u).1)) := M6Syntactic.one_le_add hw hxO hO'
        have hkeyEq : iKAdd (iRv x.1) (iRv u.1) = iRv ((x + u).1) := hkey.1 hu1
        have hfold : rvFold (iRv x.1) (u :: v :: t') = rvFold (iRv ((x + u).1)) (v :: t') := by
          show rvFold (iKAdd (iRv x.1) (iRv u.1)) (v :: t') = _
          rw [hkeyEq]
        have hO'' : ∀ z ∈ (v :: t'), iLe iRVOne (iRv z.1) := fun z hz => hO z (by simp [hz])
        have hU'' : ∀ z ∈ (v :: t'), iUnits (iRv z.1) := fun z hz => hU z (by simp [hz])
        have hstep : ∀ k, k < (v :: t').length →
            iUnits (iRv (((x + u) + ((v :: t').take k).sum).1)) := by
          intro k hk
          have h1 := hpre (k + 1) (by simpa [List.length_cons] using hk)
          exact iUnits_of_eq (take_cons_sum_eq x u (v :: t') k) h1
        have hIH := ih (x + u) hx'O hu1 hO'' hU'' hstep
        have hcons : x + (u :: v :: t').sum = (x + u) + (v :: t').sum :=
          cons_sum_eq x u (v :: t')
        constructor
        · intro hunit
          have hunit' : iUnits (iRv (((x + u) + (v :: t').sum).1)) :=
            iUnits_of_eq hcons hunit
          exact (iRv_of_eq hcons).symm ▸ (hfold.trans (hIH.1 hunit'))
        · intro hn
          have hn' : ¬ iUnits (iRv (((x + u) + (v :: t').sum).1)) :=
            not_iUnits_of_eq hcons hn
          exact hfold.trans (hIH.2 hn')

/-- `rvFold` is the `RV`-valued chain of the `rv`-values. -/
theorem rvFold_eq_kFold (acc : M) (l : List (Transfer.VFType (M := M))) :
    rvFold acc l = kFold acc (l.map (fun u => iRv u.1)) := by
  induction l generalizing acc with
  | nil => rfl
  | cons u t ih =>
      show rvFold (iKAdd acc (iRv u.1)) t
        = kFold (iKAdd acc (iRv u.1)) (t.map (fun v => iRv v.1))
      exact ih (iKAdd acc (iRv u.1))

/-! ## 4. A `Finset` sum as a list sum -/

/-- `∑ i ∈ I, f i` is the sum of `f` along `I.sort`, the enumeration the chain runs on. -/
theorem sum_map_sort (I : Finset ℕ) (f : ℕ → Transfer.VFType (M := M)) :
    ((I.sort (· ≤ ·)).map f).sum = ∑ i ∈ I, f i :=
  (List.sum_toFinset f (Finset.sort_nodup I (· ≤ ·))).symm.trans
    (congrArg (fun s => ∑ i ∈ s, f i) (Finset.sort_toFinset I (· ≤ ·)))


/-- `iUnits` at a nonzero element gives `iLe iRVOne (rv c)`: `c` lies in the valuation ring. -/
theorem one_le_of_units {c : Transfer.VFType (M := M)} (hc0 : c ≠ 0)
    (h : iUnits (iRv c.1)) : iLe iRVOne (iRv c.1) := by
  have hne : iRv c.1 ≠ iRVZero :=
    VFValued.rv_ne_zero_of_ne_zero c.2 (fun hh => hc0 (Subtype.ext hh))
  exact ((RVCalc.units_iff_le_one hM (Transfer.rv_mem hM c.2) hne).mp h).1

/-- Transporting `¬ iLe (rv ·) iRVOne` along an equation of `VFType`. -/
theorem not_iLe_of_eq {a b : Transfer.VFType (M := M)} (h : a = b) :
    (¬ iLe (iRv a.1) iRVOne) = (¬ iLe (iRv b.1) iRVOne) :=
  congrArg (fun t : Transfer.VFType (M := M) => ¬ iLe (iRv t.1) iRVOne) h

/-! ## 5. `hred` from the residue chain, and Lemma 3.2 in the chain form -/

/-- **The residue chain gives `hred`.**  This is the paper's `F̄(t) = 0` turned into the hypothesis
`M6Syntactic`'s Lemma 3.2 needs, in the frozen vocabulary.  `i₀` is the index the chain starts at;
the chain runs along `(I.erase i₀).sort`, i.e. in increasing exponent order, and its proper
partial sums must be units — the condition `kAddLink` needs.

The last hypothesis is exactly what remains of the paper's "`t` is a root of `F̄`" after the
`iKAdd` chain is made explicit. -/
theorem hred_of_residue_chain (hw : ∀ x y : Transfer.VFType (M := M), VFValued.predV x y ↔ w x ≤ w y)
    {F : (Transfer.VFType (M := M))[X]} {b : Transfer.VFType (M := M)}
    (hb0 : b ≠ 0) (hbU : iUnits (iRv b.1))
    (hint : ∀ i ∈ F.support, iLe iRVOne (iRv (F.coeff i).1))
    (I : Finset ℕ) (hIsub : ∀ i ∈ I, i ∈ F.support)
    (hIc : ∀ i ∈ I, iUnits (iRv (F.coeff i).1))
    (i₀ : ℕ) (hi₀ : i₀ ∈ I)
    (hchain : rvFold (iRv ((F.coeff i₀ * b ^ i₀)).1)
        (((I.erase i₀).sort (· ≤ ·)).map (fun i => F.coeff i * b ^ i)) = iRVZero)
    (hpre : ∀ k, k < (((I.erase i₀).sort (· ≤ ·)).map
        (fun i => F.coeff i * b ^ i)).length →
        iUnits (iRv (((F.coeff i₀ * b ^ i₀)
          + (((((I.erase i₀).sort (· ≤ ·)).map (fun i => F.coeff i * b ^ i)).take k).sum)).1))) :
    ¬ iLe (iRv (∑ i ∈ I, F.coeff i * b ^ i).1) iRVOne := by
  let l : List (Transfer.VFType (M := M)) :=
    ((I.erase i₀).sort (· ≤ ·)).map (fun i => F.coeff i * b ^ i)
  have hchain' : rvFold (iRv ((F.coeff i₀ * b ^ i₀)).1) l = iRVZero := hchain
  have hpre' : ∀ k, k < l.length →
      iUnits (iRv (((F.coeff i₀ * b ^ i₀) + (l.take k).sum).1)) := hpre
  have hbO : iLe iRVOne (iRv b.1) := one_le_of_units hb0 hbU
  have hxO : iLe iRVOne (iRv ((F.coeff i₀ * b ^ i₀)).1) :=
    M6Syntactic.one_le_mul hw (hint i₀ (hIsub i₀ hi₀)) (one_le_pow hw hbO i₀)
  have hxU : iUnits (iRv ((F.coeff i₀ * b ^ i₀)).1) :=
    M6Syntactic.units_mul hw (Polynomial.mem_support_iff.mp (hIsub i₀ hi₀))
      (pow_ne_zero i₀ hb0) (hIc i₀ hi₀) (M6Syntactic.units_pow hw hb0 hbU i₀)
  have hO : ∀ u ∈ l, iLe iRVOne (iRv u.1) := by
    intro u hu
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hu
    have hi' : i ∈ I.erase i₀ := (Finset.mem_sort (· ≤ ·)).mp hi
    exact M6Syntactic.one_le_mul hw (hint i (hIsub i (Finset.mem_of_mem_erase hi')))
      (one_le_pow hw hbO i)
  have hU : ∀ u ∈ l, iUnits (iRv u.1) := by
    intro u hu
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hu
    have hiI : i ∈ I := Finset.mem_of_mem_erase ((Finset.mem_sort (· ≤ ·)).mp hi)
    exact M6Syntactic.units_mul hw (Polynomial.mem_support_iff.mp (hIsub i hiI))
      (pow_ne_zero i hb0) (hIc i hiI) (M6Syntactic.units_pow hw hb0 hbU i)
  have hcases := rvFold_cases hw (F.coeff i₀ * b ^ i₀) l hxO hxU hO hU hpre'
  have hfin : ¬ iLe (iRv (((F.coeff i₀ * b ^ i₀) + l.sum)).1) iRVOne := by
    by_cases hunit : iUnits (iRv (((F.coeff i₀ * b ^ i₀) + l.sum)).1)
    · have hz : iRv (((F.coeff i₀ * b ^ i₀) + l.sum)).1 = iRVZero :=
        (hcases.1 hunit).symm.trans hchain'
      exact hz.symm ▸ M6Syntactic.not_le_zero_one (M := M) (hM := hM)
    · exact not_le_one_of_integral_not_units (one_le_list_sum hw _ l hxO hO) hunit
  have hlsum : l.sum = ∑ i ∈ I.erase i₀, F.coeff i * b ^ i := sum_map_sort (I.erase i₀) _
  have hsplit : (∑ i ∈ I.erase i₀, F.coeff i * b ^ i) + (F.coeff i₀ * b ^ i₀)
      = ∑ i ∈ I, F.coeff i * b ^ i :=
    Finset.sum_erase_add I (fun i => F.coeff i * b ^ i) hi₀
  have heqsum : (F.coeff i₀ * b ^ i₀) + l.sum = ∑ i ∈ I, F.coeff i * b ^ i := by
    rw [hlsum]
    exact (add_comm _ _).trans hsplit
  exact Eq.mp (not_iLe_of_eq heqsum) hfin

/-- `hred_of_residue_chain` in `L_RV`, with no valuation in the statement. -/
theorem hred_of_residue_chain_LRV
    {F : (Transfer.VFType (M := M))[X]} {b : Transfer.VFType (M := M)}
    (hb0 : b ≠ 0) (hbU : iUnits (iRv b.1))
    (hint : ∀ i ∈ F.support, iLe iRVOne (iRv (F.coeff i).1))
    (I : Finset ℕ) (hIsub : ∀ i ∈ I, i ∈ F.support)
    (hIc : ∀ i ∈ I, iUnits (iRv (F.coeff i).1))
    (i₀ : ℕ) (hi₀ : i₀ ∈ I)
    (hchain : rvFold (iRv ((F.coeff i₀ * b ^ i₀)).1)
        (((I.erase i₀).sort (· ≤ ·)).map (fun i => F.coeff i * b ^ i)) = iRVZero)
    (hpre : ∀ k, k < (((I.erase i₀).sort (· ≤ ·)).map
        (fun i => F.coeff i * b ^ i)).length →
        iUnits (iRv (((F.coeff i₀ * b ^ i₀)
          + (((((I.erase i₀).sort (· ≤ ·)).map (fun i => F.coeff i * b ^ i)).take k).sum)).1))) :
    ¬ iLe (iRv (∑ i ∈ I, F.coeff i * b ^ i).1) iRVOne := by
  obtain ⟨Γ, hΓ, w, hw⟩ := VFValued.exists_valuation_predV (M := M) (hM := hM)
  letI : LinearOrderedCommGroupWithZero Γ := hΓ
  exact hred_of_residue_chain hw hb0 hbU hint I hIsub hIc i₀ hi₀ hchain hpre

/-- The residue chain of `F` at `b` over `I`, started at `i₀`, computed on the `rv`-values: the
short form of the hypothesis of `hred_of_residue_chain`, and the form that `map_kFold` pushes along
an embedding. -/
noncomputable def rvChain (F : (Transfer.VFType (M := M))[X]) (b : Transfer.VFType (M := M)) (I : Finset ℕ)
    (i₀ : ℕ) : M :=
  kFold (iRv ((F.coeff i₀ * b ^ i₀)).1)
    (((I.erase i₀).sort (· ≤ ·)).map (fun i => iRv ((F.coeff i * b ^ i)).1))

/-- `rvFold` at the terms of `F` is `rvChain`. -/
theorem rvFold_eq_rvChain (F : (Transfer.VFType (M := M))[X]) (b : Transfer.VFType (M := M))
    (I : Finset ℕ) (i₀ : ℕ) :
    rvFold (iRv ((F.coeff i₀ * b ^ i₀)).1)
      (((I.erase i₀).sort (· ≤ ·)).map (fun i => F.coeff i * b ^ i)) = rvChain F b I i₀ := by
  rw [rvFold_eq_kFold, List.map_map]
  rfl

/-- **`hred` from the short-form chain.**  Same as `hred_of_residue_chain_LRV` with the chain
hypothesis written as `rvChain F b I i₀ = iRVZero`, the form that transfers. -/
theorem hred_of_residue_chain_k
    {F : (Transfer.VFType (M := M))[X]} {b : Transfer.VFType (M := M)}
    (hb0 : b ≠ 0) (hbU : iUnits (iRv b.1))
    (hint : ∀ i ∈ F.support, iLe iRVOne (iRv (F.coeff i).1))
    (I : Finset ℕ) (hIsub : ∀ i ∈ I, i ∈ F.support)
    (hIc : ∀ i ∈ I, iUnits (iRv (F.coeff i).1))
    (i₀ : ℕ) (hi₀ : i₀ ∈ I)
    (hchain : rvChain F b I i₀ = iRVZero)
    (hpre : ∀ k, k < (((I.erase i₀).sort (· ≤ ·)).map
        (fun i => F.coeff i * b ^ i)).length →
        iUnits (iRv (((F.coeff i₀ * b ^ i₀)
          + (((((I.erase i₀).sort (· ≤ ·)).map (fun i => F.coeff i * b ^ i)).take k).sum)).1))) :
    ¬ iLe (iRv (∑ i ∈ I, F.coeff i * b ^ i).1) iRVOne :=
  hred_of_residue_chain_LRV hb0 hbU hint I hIsub hIc i₀ hi₀
    ((rvFold_eq_rvChain F b I i₀).trans hchain) hpre

/-- **Lemma 3.2 in the shape the residue case of Lemmas 3.4/3.5/3.6 consumes**, with `hred`
replaced by the residue chain: `I` is the support of the reduction, `F̄` is not a monomial
(`2 ≤ I.card`), `b` is a unit whose residue satisfies `F̄` along the chain, and the conclusion is a
root of `F` in the class of `b`. -/
theorem rv_root_lift_encoding_of_chain
    {F : (Transfer.VFType (M := M))[X]} (hF : F ≠ 0) {b : Transfer.VFType (M := M)}
    (hb0 : b ≠ 0) (hbU : iUnits (iRv b.1))
    (hint : ∀ i ∈ F.support, iLe iRVOne (iRv (F.coeff i).1))
    (I : Finset ℕ) (hIsub : ∀ i ∈ I, i ∈ F.support)
    (hIc : ∀ i ∈ I, iUnits (iRv (F.coeff i).1))
    (hInot : ∀ i ∈ F.support, i ∉ I → ¬ iUnits (iRv (F.coeff i).1))
    (hI : 2 ≤ I.card) (i₀ : ℕ) (hi₀ : i₀ ∈ I)
    (hchain : rvFold (iRv ((F.coeff i₀ * b ^ i₀)).1)
        (((I.erase i₀).sort (· ≤ ·)).map (fun i => F.coeff i * b ^ i)) = iRVZero)
    (hpre : ∀ k, k < (((I.erase i₀).sort (· ≤ ·)).map
        (fun i => F.coeff i * b ^ i)).length →
        iUnits (iRv (((F.coeff i₀ * b ^ i₀)
          + (((((I.erase i₀).sort (· ≤ ·)).map (fun i => F.coeff i * b ^ i)).take k).sum)).1))) :
    ∃ b' : Transfer.VFType (M := M), iRv b'.1 = iRv b.1 ∧ F.IsRoot b' :=
  M6Syntactic.rv_root_lift_encoding_reduction_LRV hF hb0 hbU I hIsub hIc hint hInot hI
    (hred_of_residue_chain_LRV hb0 hbU hint I hIsub hIc i₀ hi₀ hchain hpre)


/-! ## 6. The chain residual holds at a genuine root

Conversely to Lemma 3.2: at a genuine root the chain condition is *implied* by the root equation,
so it is exactly the paper's `F̄(t) = 0` and not an extra assumption.  This is the `M`-side data of
Lemma 3.4 written in the form that transfers along an `LRV`-monomorphism. -/

/-- `f i₀` followed by the sum along `(I.erase i₀).sort` is the whole sum. -/
theorem erase_add_sort_sum (I : Finset ℕ) (f : ℕ → Transfer.VFType (M := M)) (i₀ : ℕ)
    (hi₀ : i₀ ∈ I) :
    f i₀ + (((I.erase i₀).sort (· ≤ ·)).map f).sum = ∑ i ∈ I, f i := by
  have hlsum : (((I.erase i₀).sort (· ≤ ·)).map f).sum = ∑ i ∈ I.erase i₀, f i :=
    sum_map_sort (I.erase i₀) f
  have hsplit : (∑ i ∈ I.erase i₀, f i) + f i₀ = ∑ i ∈ I, f i :=
    Finset.sum_erase_add I f hi₀
  rw [hlsum]
  exact (add_comm _ _).trans hsplit

/-- **At a genuine root the residue chain ends at `iRVZero`.**  Given the root equation, the very
same hypothesis `rvFold … = iRVZero` that `rv_root_lift_encoding_of_chain` asks for is a theorem, so
the residual of that lemma is the paper's `F̄(t) = 0` and nothing more. -/
theorem rvFold_zero_of_isRoot
    (hw : ∀ x y : Transfer.VFType (M := M), VFValued.predV x y ↔ w x ≤ w y)
    {F : (Transfer.VFType (M := M))[X]} {b : Transfer.VFType (M := M)}
    (hint : ∀ i ∈ F.support, iLe iRVOne (iRv (F.coeff i).1))
    (hb0 : b ≠ 0) (hbU : iUnits (iRv b.1)) (hroot : F.IsRoot b)
    (I : Finset ℕ) (hIsub : ∀ i ∈ I, i ∈ F.support)
    (hIc : ∀ i ∈ I, iUnits (iRv (F.coeff i).1))
    (hInot : ∀ i ∈ F.support, i ∉ I → ¬ iUnits (iRv (F.coeff i).1))
    (i₀ : ℕ) (hi₀ : i₀ ∈ I)
    (hpre : ∀ k, k < (((I.erase i₀).sort (· ≤ ·)).map
        (fun i => F.coeff i * b ^ i)).length →
        iUnits (iRv (((F.coeff i₀ * b ^ i₀)
          + (((((I.erase i₀).sort (· ≤ ·)).map (fun i => F.coeff i * b ^ i)).take k).sum)).1))) :
    rvFold (iRv ((F.coeff i₀ * b ^ i₀)).1)
      (((I.erase i₀).sort (· ≤ ·)).map (fun i => F.coeff i * b ^ i)) = iRVZero := by
  let l : List (Transfer.VFType (M := M)) :=
    ((I.erase i₀).sort (· ≤ ·)).map (fun i => F.coeff i * b ^ i)
  have hpre' : ∀ k, k < l.length →
      iUnits (iRv (((F.coeff i₀ * b ^ i₀) + (l.take k).sum).1)) := hpre
  have hbO : iLe iRVOne (iRv b.1) := one_le_of_units hb0 hbU
  have hxO : iLe iRVOne (iRv ((F.coeff i₀ * b ^ i₀)).1) :=
    M6Syntactic.one_le_mul hw (hint i₀ (hIsub i₀ hi₀)) (one_le_pow hw hbO i₀)
  have hxU : iUnits (iRv ((F.coeff i₀ * b ^ i₀)).1) :=
    M6Syntactic.units_mul hw (Polynomial.mem_support_iff.mp (hIsub i₀ hi₀))
      (pow_ne_zero i₀ hb0) (hIc i₀ hi₀) (M6Syntactic.units_pow hw hb0 hbU i₀)
  have hO : ∀ u ∈ l, iLe iRVOne (iRv u.1) := by
    intro u hu
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hu
    have hi' : i ∈ I.erase i₀ := (Finset.mem_sort (· ≤ ·)).mp hi
    exact M6Syntactic.one_le_mul hw (hint i (hIsub i (Finset.mem_of_mem_erase hi')))
      (one_le_pow hw hbO i)
  have hU : ∀ u ∈ l, iUnits (iRv u.1) := by
    intro u hu
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hu
    have hiI : i ∈ I := Finset.mem_of_mem_erase ((Finset.mem_sort (· ≤ ·)).mp hi)
    exact M6Syntactic.units_mul hw (Polynomial.mem_support_iff.mp (hIsub i hiI))
      (pow_ne_zero i hb0) (hIc i hiI) (M6Syntactic.units_pow hw hb0 hbU i)
  have hcases := rvFold_cases hw (F.coeff i₀ * b ^ i₀) l hxO hxU hO hU hpre'
  have heq : (F.coeff i₀ * b ^ i₀) + l.sum = ∑ i ∈ I, F.coeff i * b ^ i :=
    erase_add_sort_sum I (fun i => F.coeff i * b ^ i) i₀ hi₀
  have hred : ¬ iLe (iRv (∑ i ∈ I, F.coeff i * b ^ i).1) iRVOne :=
    hred_of_isRoot hw hint hbO hroot I hIsub hInot
  have hred' : ¬ iLe (iRv (((F.coeff i₀ * b ^ i₀) + l.sum)).1) iRVOne :=
    Eq.mpr (not_iLe_of_eq heq) hred
  by_cases hz : iRv (((F.coeff i₀ * b ^ i₀) + l.sum)).1 = iRVZero
  · by_cases hunit : iUnits (iRv (((F.coeff i₀ * b ^ i₀) + l.sum)).1)
    · exact (hcases.1 hunit).trans hz
    · exact hcases.2 hunit
  · have hnu : ¬ iUnits (iRv (((F.coeff i₀ * b ^ i₀) + l.sum)).1) := fun hunit =>
      hred' (((RVCalc.units_iff_le_one hM
        (Transfer.rv_mem hM ((F.coeff i₀ * b ^ i₀) + l.sum).2) hz).mp hunit).2)
    exact hcases.2 hnu

end SpecialTransformations.Milestone0.M6Wire

/-! ## 6. Axiom audit -/

#print axioms SpecialTransformations.Milestone0.M6Wire.not_le_one_of_integral_not_units
#print axioms SpecialTransformations.Milestone0.M6Wire.one_le_pow
#print axioms SpecialTransformations.Milestone0.M6Wire.one_le_list_sum
#print axioms SpecialTransformations.Milestone0.M6Wire.hred_of_isRoot
#print axioms SpecialTransformations.Milestone0.M6Wire.hred_of_isRoot_LRV
#print axioms SpecialTransformations.Milestone0.M6Wire.iKAddLink_pair
#print axioms SpecialTransformations.Milestone0.M6Wire.rvFold_cases
#print axioms SpecialTransformations.Milestone0.M6Wire.hred_of_residue_chain
#print axioms SpecialTransformations.Milestone0.M6Wire.hred_of_residue_chain_LRV
#print axioms SpecialTransformations.Milestone0.M6Wire.rv_root_lift_encoding_of_chain
#print axioms SpecialTransformations.Milestone0.M6Wire.rvFold_zero_of_isRoot
#print axioms SpecialTransformations.Milestone0.M6Wire.map_kFold
#print axioms SpecialTransformations.Milestone0.M6Wire.hred_of_residue_chain_k
