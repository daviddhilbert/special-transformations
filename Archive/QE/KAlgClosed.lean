/-
**d4 (merged from swarm smw2ioy2w m4) — the residue field `K(M) = Kˣ ∪ {0}` of a model of the frozen `ACVF` is algebraically closed.**

`QE/StandingField.lean` builds `Field (KOf M)` from the `kField` axiom list (the field axioms of
Yin's Definition 2.2 item 3, relativised to `K = Kˣ ∪ {0}` inside the `RV` sort).  This file adds
the matching half: `IsAlgClosed (KOf M)`, from the axiom list `Axioms.kAlgClosed` — which is
*already* a member of the frozen `Axioms.ACVF`:

    kAlgClosed = { acfSchemeK k | 1 ≤ k },   acfSchemeK k = ∀ a ∈ K^k, ∃ x ∈ K, hornerPoly a x = 0.

So no new mathematics and **no new hypothesis** is needed at the level of the encoding: the
algebraic closedness of `K` is an axiom (Yin's Definition 2.2 item 3 as repaired; it is also a
theorem about genuine models, but the frozen theory states it).  The work is the extraction:
realise the `allSortedK`-guarded sentence `acfSchemeK k` at a tuple of `K`-elements
(`Jm2.allSortedK_realize`), read the `exSortedK` existential (`exSortedK_realize` below), and
identify the realised Horner fold with `Polynomial.eval` of a monic polynomial
(`VFAlgClosed.eval_monic_eq`, `VFAlgClosed.horner_fold_eq` — both generic over `CommRing`, hence
reusable at `KOf M`).

This is the exact `VF`-sort argument of `QE/VFAlgClosed.lean` (`isAlgClosed_vfType`) transported
from `tVFAdd`/`tVFMul`/`iVFZero` to `tKAdd`/`tRVMul`/`tRVZero`; the `KOf`-level operation
instances are literally the frozen symbols (`kAdd`, `rvMul`), so the transport is definitional.

**Why this is what Lemma 3.3 consumes.**  `QE/ClassicalProps.lean`'s
`ACFExtendsAlgebraicEmbeddings` (Marker, quoted) has `[IsAlgClosed F]` among its hypotheses, and
`QE/PaperRoute.lean` needs it to extend a field embedding `K(M) → K(N)` of residue fields along an
algebraic extension.  `isAlgClosed_kOf` below supplies exactly that instance at `F = KOf N`, so the
quote instantiates at the frozen `Field (KOf N)` with no extra input — `acfExtends_residue` at the
end of this file is the instantiation, shown to typecheck so the discharge is consumable.

**Hypotheses introduced: none.**  The only hypotheses of every theorem below are
`[LRV.Structure M]` and `[M ⊨ Axioms.ACVF]` — the model hypothesis of the whole project — so there
is no vacuity/cardinality stress test to run: nothing is assumed and nothing is concluded that the
axioms do not already state.  (In particular the direction's fallback — "isolate one missing
model-theoretic input" — is not needed: `kAlgClosed` is in `Axioms.ACVF`.)

## Results

* `isAlgClosed_kOf : @IsAlgClosed (KOf M) (fieldKOf ..)` — the deliverable;
* `instIsAlgClosedKOf` — the same as a typeclass instance, so that every quotation stated for
  `[Field F] [IsAlgClosed F]` fires at `KOf M` with no further work;
* `acfSchemeK_realize`, `hornerPoly_realize_K`, `exSortedK_realize`, `kOf_fold_val_eq` — the
  extraction lemmas (reusable: the last one relates `KOf`-valued polynomial folds to folds of the
  frozen symbols);
* `exists_root_kOf`, `exists_pow_kOf` — the two standard corollaries (`K(M)` is root-closed, and
  `K(M)^×` is divisible), in the shape downstream files consume them;
* `acfExtends_residue` (this file, quotation restated) and, in `Quote.lean`, `acfExtends_residueK`
  against the *actual* `ClassicalProps.ACFExtendsAlgebraicEmbeddings` quote.

Verification (from the repository root `$R`; both commands exit 0 with no `error` lines):

    LEAN_PATH=$R/.scratch2/sec3:$LEAN_PATH lean $R/QE/KAlgClosed.lean

    # Quote.lean needs the frozen `ClassicalProps` module, which has no olean in `.scratch2/sec3`:
    LEAN_PATH=$R/.scratch2/sec3:$LEAN_PATH \
      lean -o $R/.scratch2/sec3/ClassicalProps.olean \
        $R/QE/ClassicalProps.lean
    LEAN_PATH=$R/.scratch2/sec3:$LEAN_PATH \
      lean -o $R/.scratch2/sec3/KAlgClosed.olean \
        $R/QE/KAlgClosed.lean
    LEAN_PATH=$R/.scratch2/sec3:$LEAN_PATH lean $R/QE/KAlgClosedQuote.lean

No `sorry`, no `admit`, no `native_decide`, no new `axiom`; `#print axioms` of every head theorem
is `[propext, Classical.choice, Quot.sound]` (the outputs are at the end of both files).
-/
import StandingField
import VFAlgClosed

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
open SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.StandingField

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace KAlgClosed

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-! ## 1. `kAlgClosed` is an axiom of `ACVF`, and `exSortedK` read semantically -/

/-- Membership of the algebraic-closedness scheme of `K` in `ACVF`. -/
theorem mem_ACVF_kAlgClosed {s : LRV.Sentence} (h : s ∈ Axioms.kAlgClosed) : s ∈ Axioms.ACVF := by
  simp only [Axioms.ACVF, Axioms.ACVFpaper, Set.mem_union] at *
  tauto

/-- The `acfSchemeK k` instance, as a member of `ACVF`, for a definite `k`. -/
theorem mem_ACVF_acfSchemeK {k : ℕ} (hk : 1 ≤ k) : Axioms.acfSchemeK k ∈ Axioms.ACVF :=
  mem_ACVF_kAlgClosed (show Axioms.acfSchemeK k ∈ Axioms.kAlgClosed from ⟨k, hk, rfl⟩)

/-- **`exSortedK .rv` realised**: `∃ x ∈ K, φ` is an existential over `K`-elements. -/
theorem exSortedK_realize {k : ℕ} (φ : LRV.Bf (k + 1)) (x : Fin k → M) :
    (LRV.exSortedK .rv φ).Realize (default : Empty → M) x ↔
      ∃ a : M, iRV a ∧ pInKof a ∧ φ.Realize (default : Empty → M) (Fin.snoc x a) := by
  have hterm : ∀ a : M, (LRV.tv k (Nat.lt_succ_self k) : LRV.Tm (k + 1)).realize
      (Sum.elim (default : Empty → M) (Fin.snoc x a)) = a := by
    intro a
    show (Fin.snoc x a : Fin (k + 1) → M) ⟨k, Nat.lt_succ_self k⟩ = a
    exact VFAlgClosed.snoc_last_apply x a
  simp only [LRV.exSortedK, BoundedFormula.realize_ex, BoundedFormula.realize_inf,
    Transfer.sortPred_realize, TrivCase.pInK_realize, hterm, pInKof]
  constructor
  · rintro ⟨a, ⟨h1, h2⟩, h3⟩
    exact ⟨a, h1, h2, h3⟩
  · rintro ⟨a, h1, h2, h3⟩
    exact ⟨a, ⟨h1, h2⟩, h3⟩

/-! ## 2. The frozen Horner term, at the residue-field symbols

Same shape as `VFAlgClosed.hornerPoly_realize`, with `tKAdd`/`tRVMul`/`iRVZero` in place of
`tVFAdd`/`tVFMul`/`iVFZero`.  (`Fin.snoc` evaluation lemmas are reused from `VFAlgClosed`, which
states them for an arbitrary `LRV.Structure`.) -/

/-- **The value of the frozen Horner term of `K`** at a coefficient tuple `a` and a candidate
root `x`: `((x + a_m) * x + ⋯ ) * x + a_0`, in `iKAdd`/`iRVMul`. -/
theorem hornerPoly_realize_K {m : ℕ} (a : Fin (m + 1) → M) (x : M) :
    (LRV.hornerPoly (k := m + 1) LRV.tKAdd LRV.tRVMul).realize
        (Sum.elim (default : Empty → M) (Fin.snoc a x : Fin (m + 1 + 1) → M))
      = (List.finRange m).reverse.foldl
          (fun acc (i : Fin m) => iKAdd (iRVMul acc x) (a i.castSucc))
          (iKAdd x (a (Fin.last m))) := by
  rw [LRV.hornerPoly]
  have hstep : ∀ (acc : LRV.Tm (m + 1 + 1)) (i : Fin m),
      (LRV.tKAdd (LRV.tRVMul acc (LRV.tv (m + 1) (by omega)))
        (LRV.tv i.val (by omega))).realize
          (Sum.elim (default : Empty → M) (Fin.snoc a x : Fin (m + 1 + 1) → M))
        = iKAdd (iRVMul ((acc).realize
            (Sum.elim (default : Empty → M) (Fin.snoc a x : Fin (m + 1 + 1) → M))) x)
            (a i.castSucc) := by
    intro acc i
    rw [TrivCase.realize_tKAdd, Transfer.realize_tRVMul,
      show (LRV.tv (m + 1) (by omega) : LRV.Tm (m + 1 + 1)).realize
          (Sum.elim (default : Empty → M) (Fin.snoc a x : Fin (m + 1 + 1) → M))
          = (Fin.snoc a x : Fin (m + 1 + 1) → M) ⟨m + 1, by omega⟩ from rfl,
      show (LRV.tv i.val (by omega) : LRV.Tm (m + 1 + 1)).realize
          (Sum.elim (default : Empty → M) (Fin.snoc a x : Fin (m + 1 + 1) → M))
          = (Fin.snoc a x : Fin (m + 1 + 1) → M) ⟨i.val, by omega⟩ from rfl,
      VFAlgClosed.snoc_root a x, VFAlgClosed.snoc_castSucc_castSucc a x i]
  have hinit : (LRV.tKAdd (LRV.tv (m + 1) (by omega)) (LRV.tv m (by omega))).realize
      (Sum.elim (default : Empty → M) (Fin.snoc a x : Fin (m + 1 + 1) → M))
      = iKAdd x (a (Fin.last m)) := by
    rw [TrivCase.realize_tKAdd,
      show (LRV.tv (m + 1) (by omega) : LRV.Tm (m + 1 + 1)).realize
          (Sum.elim (default : Empty → M) (Fin.snoc a x : Fin (m + 1 + 1) → M))
          = (Fin.snoc a x : Fin (m + 1 + 1) → M) ⟨m + 1, by omega⟩ from rfl,
      show (LRV.tv m (by omega) : LRV.Tm (m + 1 + 1)).realize
          (Sum.elim (default : Empty → M) (Fin.snoc a x : Fin (m + 1 + 1) → M))
          = (Fin.snoc a x : Fin (m + 1 + 1) → M) ⟨m, by omega⟩ from rfl,
      VFAlgClosed.snoc_root a x, VFAlgClosed.snoc_last_coeff a x]
  have h := List.foldl_hom
    (fun t : LRV.Tm (m + 1 + 1) => t.realize
      (Sum.elim (default : Empty → M) (Fin.snoc a x : Fin (m + 1 + 1) → M)))
    (g₁ := fun (acc : LRV.Tm (m + 1 + 1)) (i : Fin m) =>
      LRV.tKAdd (LRV.tRVMul acc (LRV.tv (m + 1) (by omega))) (LRV.tv i.val (by omega)))
    (g₂ := fun (acc : M) (i : Fin m) => iKAdd (iRVMul acc x) (a i.castSucc))
    (l := (List.finRange m).reverse)
    (init := LRV.tKAdd (LRV.tv (m + 1) (by omega)) (LRV.tv m (by omega)))
    (fun acc i => (hstep acc i).symm)
  rw [hinit] at h
  exact h.symm

/-- **`acfSchemeK k`, semantically**: for `1 ≤ k` and coefficients in `K`, the monic polynomial
`x^k + a_{k-1}x^{k-1} + ⋯ + a_0` has a root in `K`. -/
theorem acfSchemeK_realize {k : ℕ} (hk : 1 ≤ k) (a : Fin k → M) (ha : ∀ i, pInKof (a i)) :
    ∃ x : M, iRV x ∧ pInKof x ∧
      (LRV.hornerPoly (k := k) LRV.tKAdd LRV.tRVMul).realize
        (Sum.elim (default : Empty → M) (Fin.snoc a x)) = iRVZero := by
  have hmem : LRV.allSortedK (fun _ : Fin k => SortTag.rv)
      (LRV.exSortedK .rv (LRV.pEq (LRV.hornerPoly LRV.tKAdd LRV.tRVMul) LRV.tRVZero))
      ∈ Axioms.ACVF := mem_ACVF_acfSchemeK hk
  have h := Jm2.allSortedK_realize (T := Axioms.ACVF) hM
    (ss := (fun _ : Fin k => SortTag.rv))
    (φ := LRV.exSortedK .rv (LRV.pEq (LRV.hornerPoly LRV.tKAdd LRV.tRVMul) LRV.tRVZero))
    hmem a (fun i => Jm2.iRV_of_inK (ha i)) ha
  obtain ⟨x, hxRV, hxK, hxeq⟩ := (exSortedK_realize _ a).mp h
  refine ⟨x, hxRV, hxK, ?_⟩
  simpa only [LRV.pEq, BoundedFormula.realize_bdEqual, Transfer.realize_tRVZero] using hxeq

/-! ## 3. The fold computed on `KOf M` agrees with the fold computed on `M` -/

/-- `KOf`'s `+` is `iKAdd` and `KOf`'s `*` is `iRVMul`, definitionally. -/
theorem kOf_fold_val_eq {m : ℕ} (a : Fin (m + 1) → KOf M) (x : KOf M) :
    ((List.finRange m).reverse.foldl
        (fun acc (i : Fin m) => acc * x + a i.castSucc) (x + a (Fin.last m))).1
      = (List.finRange m).reverse.foldl
          (fun acc (i : Fin m) => iKAdd (iRVMul acc x.1) (a i.castSucc).1)
          (iKAdd x.1 (a (Fin.last m)).1) := by
  refine Eq.trans ?_ (List.foldl_hom (Subtype.val)
    (g₁ := fun (acc : KOf M) (i : Fin m) => acc * x + a i.castSucc)
    (g₂ := fun (acc : M) (i : Fin m) => iKAdd (iRVMul acc x.1) (a i.castSucc).1)
    (l := (List.finRange m).reverse)
    (init := x + a (Fin.last m)) (fun acc i => rfl)).symm
  rfl

/-! ## 4. `IsAlgClosed (KOf M)` -/

/-- **The residue field of a model of the frozen `ACVF` is algebraically closed.** -/
theorem isAlgClosed_kOf :
    @IsAlgClosed (KOf M) (fieldKOf (M := M) (hM := hM)) := by
  letI : Field (KOf M) := fieldKOf (M := M)
  refine IsAlgClosed.of_exists_root _ ?_
  intro p hpm hpi
  have hdeg : 0 < p.natDegree :=
    Polynomial.natDegree_pos_iff_degree_pos.2 (Polynomial.degree_pos_of_irreducible hpi)
  obtain ⟨m, hm⟩ : ∃ m, p.natDegree = m + 1 := ⟨p.natDegree - 1, by omega⟩
  -- a root in the `M`-level residue symbols, for the coefficient tuple of `p`
  obtain ⟨x, _hxRV, hxK, hxeq⟩ := acfSchemeK_realize (M := M) (k := m + 1) (by omega)
    (fun i => (p.coeff (i : ℕ)).1) (fun i => (p.coeff (i : ℕ)).2)
  set x' : KOf M := ⟨x, hxK⟩ with hx'def
  have hxeq' : (List.finRange m).reverse.foldl
      (fun acc (i : Fin m) => iKAdd (iRVMul acc x) ((p.coeff (i.castSucc : ℕ)).1))
      (iKAdd x ((p.coeff (Fin.last m : ℕ)).1)) = iRVZero :=
    (hornerPoly_realize_K (fun i => (p.coeff (i : ℕ)).1) x).symm.trans hxeq
  refine ⟨x', ?_⟩
  have hfold : (List.finRange m).reverse.foldl
      (fun acc (i : Fin m) => acc * x' + p.coeff (i.castSucc : ℕ)) (x' + p.coeff m) = 0 := by
    apply Subtype.ext
    exact (kOf_fold_val_eq (a := fun i => p.coeff (i : ℕ)) (x := x')).trans hxeq'
  refine Eq.trans (VFAlgClosed.eval_monic_eq hpm hm x') ?_
  refine Eq.trans (VFAlgClosed.horner_fold_eq (fun i => p.coeff i) x' m).symm ?_
  exact hfold

/-- Instance form of `isAlgClosed_kOf`: what the typeclass search of a quotation stated for
`[Field F] [IsAlgClosed F]` needs in order to fire at `F = KOf M`. -/
noncomputable instance instIsAlgClosedKOf : IsAlgClosed (KOf M) :=
  isAlgClosed_kOf (M := M) (hM := hM)

/-! ## 4b. Corollaries in the shape downstream files consume them -/

/-- **`K(M)` is root-closed**: every nonconstant polynomial over the residue field has a root.
(`f.degree ≠ 0` is the Mathlib form of `f` nonconstant.) -/
theorem exists_root_kOf (f : Polynomial (KOf M)) (hf : f.degree ≠ 0) :
    ∃ x : KOf M, f.IsRoot x :=
  IsAlgClosed.exists_root f hf

/-- **`K(M)^×` is divisible**: every element of the residue field has an `n`-th root, `n > 0`.
This is the field-level form of `Axioms.rvDivisible` at the units. -/
theorem exists_pow_kOf (x : KOf M) {n : ℕ} (hn : 0 < n) : ∃ z : KOf M, z ^ n = x :=
  IsAlgClosed.exists_pow_nat_eq x hn

/-! ## 5. The quote consumes it: `ACFExtendsAlgebraicEmbeddings` at the residue fields

`QE/ClassicalProps.lean`'s quotation is `Prop`-valued and lives in a separate module; the point of
this section is only that `isAlgClosed_kOf` discharges the `[IsAlgClosed F]` side condition at the
frozen residue field, *without* changing the shape of the quotation.  It is checked here
syntactically (`ClassicalProps` is not on the frozen `LEAN_PATH`, so its statement is restated in
the same form rather than imported; the two statements are character-for-character the same). -/

section QuoteShape

/-- The residue field of a model of `ACVF`, as a field: the `Field` instance used below is the
frozen `StandingField.fieldKOf`, and it is algebraically closed by `isAlgClosed_kOf`. -/
noncomputable example : Field (KOf M) := fieldKOf (M := M)

end QuoteShape

end KAlgClosed

/-- `ACFExtendsAlgebraicEmbeddings` (Marker, as transcribed in `QE/ClassicalProps.lean`), applied at
the residue fields of two models of the frozen `ACVF`: an algebraic extension of `K(M)` receives
every embedding `K(M) → K(N)`.  This is the exact use `QE/PaperRoute.lean`'s Lemma 3.3 makes of the
quote; it typechecks only because `K(N)` is algebraically closed (`isAlgClosed_kOf`). -/
theorem acfExtends_residue {M N : Type} [LRV.Structure M] [LRV.Structure N]
    [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]
    (hacf : ∀ {K E F : Type} [Field K] [Field E] [Field F] [Algebra K E] [IsAlgClosed F]
      (_ : Algebra.IsAlgebraic K E) (j : K →+* F), ∃ l : E →+* F, ∀ x : K, l (algebraMap K E x) = j x)
    {E : Type} [Field E] [Algebra (SpecialTransformations.Milestone0.StandingField.KOf M) E] [Algebra.IsAlgebraic (SpecialTransformations.Milestone0.StandingField.KOf M) E]
    (j : SpecialTransformations.Milestone0.StandingField.KOf M →+* SpecialTransformations.Milestone0.StandingField.KOf N) :
    ∃ l : E →+* SpecialTransformations.Milestone0.StandingField.KOf N, ∀ x : SpecialTransformations.Milestone0.StandingField.KOf M, l (algebraMap _ E x) = j x :=
  hacf (K := SpecialTransformations.Milestone0.StandingField.KOf M) (F := SpecialTransformations.Milestone0.StandingField.KOf N) (E := E)
    (inferInstance : Algebra.IsAlgebraic (SpecialTransformations.Milestone0.StandingField.KOf M) E) j

#print axioms KAlgClosed.mem_ACVF_kAlgClosed
#print axioms KAlgClosed.mem_ACVF_acfSchemeK
#print axioms KAlgClosed.exSortedK_realize
#print axioms KAlgClosed.hornerPoly_realize_K
#print axioms KAlgClosed.acfSchemeK_realize
#print axioms KAlgClosed.kOf_fold_val_eq
#print axioms KAlgClosed.isAlgClosed_kOf
#print axioms KAlgClosed.exists_root_kOf
#print axioms KAlgClosed.exists_pow_kOf
#print axioms KAlgClosed.instIsAlgClosedKOf
#print axioms acfExtends_residue
