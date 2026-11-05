/-
**`qf2_cover`**: a well-sorted quantifier-free formula over a sorted context is, at sorted tuples,
equivalent to the image of a `QF2` term of `QE/QF2Fragment.lean`.

Why this is the right target and why it is not the audit's `MixedContextCover`: that statement
(`.ultramath/smw1b0thh/m3/AvAudit.lean:158`) asks for a *parameter-free* formula `φ'` and an all-`VF`
tuple `y` with `φ.Realize v x ↔ φ'.Realize default y`.  Since `y` may depend on `(v, x)` and `φ'` is
fixed, the only thing it can require of `φ'` is that it be neither valid nor unsatisfiable, so it is
essentially true for any `φ'` with a true and a false instance, independently of `φ`.  It is therefore
not the content, and it is not what this file proves.

This file proves the content: with the fragment `RVT2` carrying an `RV`-sorted *variable*
(`RVT2.rvar`), every well-sorted quantifier-free formula over a sorted context is the image of a
`QF2` term, so the atom layer of the elimination can be done inside the fragment.  The term
extraction is where `QE/MulNormalForm.lean` belongs: an `RV`-term built out of `rvMul`/`kAdd` has to
be flattened into `RVT2`, and off `Kˣ` that is cancellation.

Build (`.scratch2/sec3/` holds the oleans):

    LEAN_PATH=$PWD:$LEAN_PATH lean QF2Cover.lean        # with QF2Fragment.olean present
-/
import QF2Fragment
set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open scoped FirstOrder
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Milestone0.Transfer
namespace QFRes2

/-- The sort assignment of the empty parameter type. -/
abbrev sE : Empty → SortTag := fun e => e.elim

section Extract

variable {n : ℕ} {sn : Fin n → SortTag}

/-! ## The cover, stated

The extraction is a *proof-free* recursion (`Option`-valued), because the proof-carrying version
(`(t : Tm n) → TmSort sE sn t = some .vf → VFT2 sn`) does not pass Lean's structural-recursion
check when the sort hypothesis is consumed inside a `cases f` block: the offending goal is
`sizeOf (ts 0) < 1 + l`, where `l` is the arity and not a size.  The `Option` version descends on `t`
alone and its soundness is a separate induction on `t`, which is the standard way round.

`vfOpt`/`rvOpt` mirror `TmSort` symbol by symbol.  **Proved here** (no `sorry`, axioms within
{propext, Classical.choice, Quot.sound}): `vfOpt_sound` and `rvOpt_sound` — a term of sort `VF`
(resp. `RV`) is extracted, and the extracted fragment term has the same value at every tuple.  The
computation uses the fragment's own `val_*` lemmas (`QF2Fragment`) plus one point that cost a round:
the encoding writes its atoms as `rel R ts` for a general `ts`, while `pVF`/`pRVsort`/`pUnits`/`pLe`
are the `![…]`-shaped abbreviations, so every atom case needs `ts` rewritten to the matrix
(`hts : ts = ![ts 0, ts 1]`) before the realization lemma applies; and `rvMap`'s argument is a *VF*
term, so the `RV` extraction has to call `vfOpt_sound` rather than its own induction hypothesis.

**Proved, no `sorry`:** `qf2_cover` itself (`qf2_cover_eval` in `QF2.Eval` form, `qf2_cover` in the
`toRV`/`Realize` form), axioms within {propext, Classical.choice, Quot.sound}.  The formula induction:
atoms via the extraction, connectives via `QF2.imp`/`QF2.falsum`, and the `all` case is excluded by
`IsQF` (`BoundedFormula.not_all_isQF`) — the fragment needs no quantifier case, which is the whole
point of stating the cover over the *quantifier-free* fragment.

Four things cost a round each; they are recorded here because they are the kind of detail that is
invisible until it bites:
1. the encoding writes atoms as `rel R ts` for a general `ts`, while `pVF`/`pRVsort`/`pUnits`/`pLe`
   are the `![…]` abbreviations — so each atom needs a realization lemma at general `ts`
   (`realize_rel_memVF` and companions), proved by `Iff.rfl` to the `RelMap` form and then rewriting
   the assignment function to the matrix with `funext`/`fin_cases`;
2. `QF2.Eval` is a pattern-matching `def`, so its constructor equations are separate `Iff.rfl`
   lemmas (`eval_inVF`, …) rather than `show`-able;
3. `IsQF` is an inductive with an `of_isAtomic` case that is impossible at an implication, so the
   `imp` case needs the destructor `isQF_imp_inv`;
4. `vfOpt_sound` is stated at a fixed model, and a section variable that a statement does not
   mention is *not* in scope for its proof — so the model-free existence of the extracted term needs
   `vfOpt_exists`, proved by instantiating the soundness theorem at a junk `LRV.Structure PUnit`
   (declared here for that purpose), with `vfOpt_val` carrying the model inside its conclusion.
   Without that split the atom cases cannot produce the `QF2` witness before the statement's `∀ M`.

-/

/-- Extract a fragment `VF`-term, undoing `TmSort` symbol by symbol.  Proof-free, so that the
recursion is structural on the term; the sort hypothesis is used only in `vfOpt_sound`. -/
noncomputable def vfOpt (sn : Fin n → SortTag) : Tm n → Option (VFT2 sn)
  | .var (Sum.inl e) => Empty.elim e
  | .var (Sum.inr i) => if h : sn i = .vf then some (.var i h) else none
  | .func f ts => match f with
      | .vfZero => some .zero
      | .vfOne => some .one
      | .vfAdd => (vfOpt sn (ts 0)).bind (fun a => (vfOpt sn (ts 1)).map (fun b => .add a b))
      | .vfNeg => (vfOpt sn (ts 0)).map (fun a => .neg a)
      | .vfMul => (vfOpt sn (ts 0)).bind (fun a => (vfOpt sn (ts 1)).map (fun b => .mul a b))
      | .rvOne => none
      | .rvZero => none
      | .rvMul => none
      | .kAdd => none
      | .kNeg => none
      | .rvMap => none

/-- Extract a fragment `RV`-term, dually. -/
noncomputable def rvOpt (sn : Fin n → SortTag) : Tm n → Option (RVT2 sn)
  | .var (Sum.inl e) => Empty.elim e
  | .var (Sum.inr i) => if h : sn i = .rv then some (.rvar i h) else none
  | .func f ts => match f with
      | .rvOne => some .one
      | .rvZero => some .zero
      | .rvMul => (rvOpt sn (ts 0)).bind (fun a => (rvOpt sn (ts 1)).map (fun b => .mul a b))
      | .kAdd => (rvOpt sn (ts 0)).bind (fun a => (rvOpt sn (ts 1)).map (fun b => .kAdd a b))
      | .kNeg => (rvOpt sn (ts 0)).map (fun a => .kNeg a)
      | .rvMap => (vfOpt sn (ts 0)).map (fun s => .rv s)
      | .vfZero => none
      | .vfOne => none
      | .vfAdd => none
      | .vfNeg => none
      | .vfMul => none

/-- **Soundness of the `VF` extraction**: a term of `VF` sort is extracted, and the extracted
fragment term has the same value. -/
theorem vfOpt_sound {M : Type} [LRV.Structure M] :
    ∀ (t : Tm n), TmSort sE sn t = some .vf →
      ∃ s : VFT2 sn, vfOpt sn t = some s ∧
        ∀ x : Fin n → M, s.Val x = t.realize (Sum.elim (default : Empty → M) x) := by
  intro t
  induction t with
  | var a =>
    rcases a with e | i
    · intro h; exact Empty.elim e
    · intro h
      simp only [TmSort, Option.some.injEq] at h
      exact ⟨.var i h, by simp only [vfOpt, h, dif_pos], fun x => rfl⟩
  | @func l f ts ih =>
    intro h
    obtain ⟨hargs, hres⟩ := (tmSort_func_iff sE sn f ts).1 h
    cases f with
    | vfZero =>
      refine ⟨.zero, rfl, fun x => ?_⟩
      rw [VFT2.val_zero]
      have hts : ts = (fun i : Fin 0 => i.elim0) := funext (fun i => i.elim0)
      rw [hts]
      exact (realize_tVFZero (M := M) (n := n) (Sum.elim (default : Empty → M) x)).symm
    | vfOne =>
      refine ⟨.one, rfl, fun x => ?_⟩
      rw [VFT2.val_one]
      have hts : ts = (fun i : Fin 0 => i.elim0) := funext (fun i => i.elim0)
      rw [hts]
      exact (realize_tVFOne (M := M) (n := n) (Sum.elim (default : Empty → M) x)).symm
    | vfAdd =>
      obtain ⟨a, ha, hva⟩ := ih 0 (hargs 0)
      obtain ⟨b, hb, hvb⟩ := ih 1 (hargs 1)
      refine ⟨.add a b, by simp only [vfOpt, ha, hb, Option.bind_some, Option.map_some], fun x => ?_⟩
      rw [VFT2.val_add, hva, hvb]
      have hts : ts = ![ts 0, ts 1] := funext (fun i => by fin_cases i <;> rfl)
      rw [hts]
      exact (realize_tVFAdd _ _ _).symm
    | vfNeg =>
      obtain ⟨a, ha, hva⟩ := ih 0 (hargs 0)
      refine ⟨.neg a, by simp only [vfOpt, ha, Option.map_some], fun x => ?_⟩
      rw [VFT2.val_neg, hva]
      have hts : ts = ![ts 0] := funext (fun i => by fin_cases i; rfl)
      rw [hts]
      exact (realize_tVFNeg _ _).symm
    | vfMul =>
      obtain ⟨a, ha, hva⟩ := ih 0 (hargs 0)
      obtain ⟨b, hb, hvb⟩ := ih 1 (hargs 1)
      refine ⟨.mul a b, by simp only [vfOpt, ha, hb, Option.bind_some, Option.map_some], fun x => ?_⟩
      rw [VFT2.val_mul, hva, hvb]
      have hts : ts = ![ts 0, ts 1] := funext (fun i => by fin_cases i <;> rfl)
      rw [hts]
      exact (realize_tVFMul _ _ _).symm
    | rvOne => exact absurd hres (by decide)
    | rvZero => exact absurd hres (by decide)
    | rvMul => exact absurd hres (by decide)
    | kAdd => exact absurd hres (by decide)
    | kNeg => exact absurd hres (by decide)
    | rvMap => exact absurd hres (by decide)

/-- **Soundness of the `RV` extraction**. -/
theorem rvOpt_sound {M : Type} [LRV.Structure M] :
    ∀ (t : Tm n), TmSort sE sn t = some .rv →
      ∃ u : RVT2 sn, rvOpt sn t = some u ∧
        ∀ x : Fin n → M, u.Val x = t.realize (Sum.elim (default : Empty → M) x) := by
  intro t
  induction t with
  | var a =>
    rcases a with e | i
    · intro h; exact Empty.elim e
    · intro h
      simp only [TmSort, Option.some.injEq] at h
      exact ⟨.rvar i h, by simp only [rvOpt, h, dif_pos], fun x => rfl⟩
  | @func l f ts ih =>
    intro h
    obtain ⟨hargs, hres⟩ := (tmSort_func_iff sE sn f ts).1 h
    cases f with
    | rvOne =>
      refine ⟨.one, rfl, fun x => ?_⟩
      rw [RVT2.val_one]
      have hts : ts = (fun i : Fin 0 => i.elim0) := funext (fun i => i.elim0)
      rw [hts]
      exact (TrivCase.realize_tRVOne (M := M) (n := n) (Sum.elim (default : Empty → M) x)).symm
    | rvZero =>
      refine ⟨.zero, rfl, fun x => ?_⟩
      rw [RVT2.val_zero]
      have hts : ts = (fun i : Fin 0 => i.elim0) := funext (fun i => i.elim0)
      rw [hts]
      exact (realize_tRVZero (M := M) (k := n) (Sum.elim (default : Empty → M) x)).symm
    | rvMul =>
      obtain ⟨a, ha, hva⟩ := ih 0 (hargs 0)
      obtain ⟨b, hb, hvb⟩ := ih 1 (hargs 1)
      refine ⟨.mul a b, by simp only [rvOpt, ha, hb, Option.bind_some, Option.map_some], fun x => ?_⟩
      rw [RVT2.val_mul, hva, hvb]
      have hts : ts = ![ts 0, ts 1] := funext (fun i => by fin_cases i <;> rfl)
      rw [hts]
      exact (realize_tRVMul _ _ _).symm
    | kAdd =>
      obtain ⟨a, ha, hva⟩ := ih 0 (hargs 0)
      obtain ⟨b, hb, hvb⟩ := ih 1 (hargs 1)
      refine ⟨.kAdd a b, by simp only [rvOpt, ha, hb, Option.bind_some, Option.map_some], fun x => ?_⟩
      rw [RVT2.val_kAdd, hva, hvb]
      have hts : ts = ![ts 0, ts 1] := funext (fun i => by fin_cases i <;> rfl)
      rw [hts]
      exact (TrivCase.realize_tKAdd _ _ _).symm
    | kNeg =>
      obtain ⟨a, ha, hva⟩ := ih 0 (hargs 0)
      refine ⟨.kNeg a, by simp only [rvOpt, ha, Option.map_some], fun x => ?_⟩
      rw [RVT2.val_kNeg, hva]
      have hts : ts = ![ts 0] := funext (fun i => by fin_cases i; rfl)
      rw [hts]
      exact (TrivCase.realize_tKNeg _ _).symm
    | rvMap =>
      -- `rvMap`'s argument is a *VF* term, so this branch calls `vfOpt_sound`, not the `RV` IH
      obtain ⟨s, hs, hvs⟩ := vfOpt_sound (M := M) (sn := sn) (ts 0) (hargs 0)
      refine ⟨.rv s, by simp only [rvOpt, hs, Option.map_some], fun x => ?_⟩
      rw [RVT2.val_rv, hvs]
      have hts : ts = ![ts 0] := funext (fun i => by fin_cases i; rfl)
      rw [hts]
      exact (realize_tRv _ _).symm
    | vfZero => exact absurd hres (by decide)
    | vfOne => exact absurd hres (by decide)
    | vfAdd => exact absurd hres (by decide)
    | vfNeg => exact absurd hres (by decide)
    | vfMul => exact absurd hres (by decide)

/-! ## The model-free part of the extraction

`vfOpt_sound`/`rvOpt_sound` are stated at a fixed model (the value equation lives there), but the
*term* they produce does not depend on the model.  The two accessors below split that:
`vfOpt_exists` is model-free (its statement mentions neither the model nor the structure, so the
section variables do not become parameters), and `vfOpt_val` carries the model inside its
conclusion.  Without the split, the cover's atom cases cannot produce the `QF2` witness before the
model is introduced by the statement's `∀`. -/

/-- A junk `L_RV`-structure on `PUnit`.  It is *not* a model of `ACVF` and is used for one purpose
only: the extraction and its value equation depend on the model, but the extracted *term* does not,
so the model-free existence statement below is proved by instantiating the soundness theorem here
(a section variable that the statement does not mention is not in scope for its proof, and a
`∀ M`-free statement cannot otherwise be obtained from a model-indexed one). -/
instance : LRV.Structure PUnit where
  RelMap := fun _ _ => True
  funMap := fun _ _ => ⟨⟩

theorem vfOpt_exists (t : Tm n) (h : TmSort sE sn t = some .vf) :
    ∃ s : VFT2 sn, vfOpt sn t = some s := by
  obtain ⟨s, hs, -⟩ := vfOpt_sound (M := PUnit) t h
  exact ⟨s, hs⟩

theorem rvOpt_exists (t : Tm n) (h : TmSort sE sn t = some .rv) :
    ∃ u : RVT2 sn, rvOpt sn t = some u := by
  obtain ⟨u, hu, -⟩ := rvOpt_sound (M := PUnit) t h
  exact ⟨u, hu⟩

theorem vfOpt_val (t : Tm n) (h : TmSort sE sn t = some .vf) {s : VFT2 sn}
    (hs : vfOpt sn t = some s) :
    ∀ (M : Type) [LRV.Structure M] (x : Fin n → M),
      s.Val x = t.realize (Sum.elim (default : Empty → M) x) := by
  intro M inst x
  obtain ⟨s', hs', hv⟩ := vfOpt_sound (M := M) t h
  rw [hs] at hs'
  cases hs'
  exact hv x

theorem rvOpt_val (t : Tm n) (h : TmSort sE sn t = some .rv) {u : RVT2 sn}
    (hu : rvOpt sn t = some u) :
    ∀ (M : Type) [LRV.Structure M] (x : Fin n → M),
      u.Val x = t.realize (Sum.elim (default : Empty → M) x) := by
  intro M inst x
  obtain ⟨u', hu', hv⟩ := rvOpt_sound (M := M) t h
  rw [hu] at hu'
  cases hu'
  exact hv x

/-! ## `qf2_cover`

Everything is at the assignment `(default : Empty → M)`, which is what `VFT2.Val` and
`QF2.realize_toRV` use; the frozen target's `(fun e : Empty => e.elim)` is the same function,
converted once in `qf2_cover`. -/

section AtomRealize

variable {M : Type} [LRV.Structure M] {x : Fin n → M}

@[simp] theorem eval_inVF (a : VFT2 sn) : QF2.Eval x (.inVF a) ↔ iVF (VFT2.Val a x) := Iff.rfl
@[simp] theorem eval_inRV (a : RVT2 sn) : QF2.Eval x (.inRV a) ↔ iRV (RVT2.Val a x) := Iff.rfl
@[simp] theorem eval_unitRV (a : RVT2 sn) :
    QF2.Eval x (.unitRV a) ↔ iUnits (RVT2.Val a x) := Iff.rfl
@[simp] theorem eval_leRV (a b : RVT2 sn) :
    QF2.Eval x (.leRV a b) ↔ iLe (RVT2.Val a x) (RVT2.Val b x) := Iff.rfl
@[simp] theorem eval_eqVF (a b : VFT2 sn) :
    QF2.Eval x (.eqVF a b) ↔ VFT2.Val a x = VFT2.Val b x := Iff.rfl
@[simp] theorem eval_eqRV (a b : RVT2 sn) :
    QF2.Eval x (.eqRV a b) ↔ RVT2.Val a x = RVT2.Val b x := Iff.rfl
@[simp] theorem eval_imp (a b : QF2 sn) :
    QF2.Eval x (.imp a b) ↔ (QF2.Eval x a → QF2.Eval x b) := Iff.rfl

/-- The destructor of `IsQF` at an implication (the inductive has an `of_isAtomic` case too, which
is impossible at an implication). -/
theorem isQF_imp_inv {k : ℕ} {φ ψ : Bf k} (h : (φ.imp ψ).IsQF) : φ.IsQF ∧ ψ.IsQF := by
  cases h with
  | imp h1 h2 => exact ⟨h1, h2⟩
  | of_isAtomic h1 => cases h1

/-- `t ∈ VF` at a general `ts` (the encoding's atoms are `rel R ts`, not the `![…]` forms). -/
theorem realize_rel_memVF (ts : Fin 1 → Tm n) (v : Empty → M) (x : Fin n → M) :
    (BoundedFormula.rel (L := LRV) Rel.memVF ts).Realize v x ↔
      iVF ((ts 0).realize (Sum.elim v x)) := by
  have h : (BoundedFormula.rel (L := LRV) Rel.memVF ts).Realize v x
      ↔ Structure.RelMap (L := LRV) Rel.memVF (fun i => (ts i).realize (Sum.elim v x)) := Iff.rfl
  rw [h]
  have h2 : (fun i => (ts i).realize (Sum.elim v x))
      = (fun i => ![(ts 0).realize (Sum.elim v x)] i) := by funext i; fin_cases i; rfl
  rw [h2]; exact Iff.rfl

theorem realize_rel_memRV (ts : Fin 1 → Tm n) (v : Empty → M) (x : Fin n → M) :
    (BoundedFormula.rel (L := LRV) Rel.memRV ts).Realize v x ↔
      iRV ((ts 0).realize (Sum.elim v x)) := by
  have h : (BoundedFormula.rel (L := LRV) Rel.memRV ts).Realize v x
      ↔ Structure.RelMap (L := LRV) Rel.memRV (fun i => (ts i).realize (Sum.elim v x)) := Iff.rfl
  rw [h]
  have h2 : (fun i => (ts i).realize (Sum.elim v x))
      = (fun i => ![(ts 0).realize (Sum.elim v x)] i) := by funext i; fin_cases i; rfl
  rw [h2]; exact Iff.rfl

theorem realize_rel_memUnits (ts : Fin 1 → Tm n) (v : Empty → M) (x : Fin n → M) :
    (BoundedFormula.rel (L := LRV) Rel.memUnits ts).Realize v x ↔
      iUnits ((ts 0).realize (Sum.elim v x)) := by
  have h : (BoundedFormula.rel (L := LRV) Rel.memUnits ts).Realize v x
      ↔ Structure.RelMap (L := LRV) Rel.memUnits (fun i => (ts i).realize (Sum.elim v x)) := Iff.rfl
  rw [h]
  have h2 : (fun i => (ts i).realize (Sum.elim v x))
      = (fun i => ![(ts 0).realize (Sum.elim v x)] i) := by funext i; fin_cases i; rfl
  rw [h2]; exact Iff.rfl

theorem realize_rel_rvLe (ts : Fin 2 → Tm n) (v : Empty → M) (x : Fin n → M) :
    (BoundedFormula.rel (L := LRV) Rel.rvLe ts).Realize v x ↔
      iLe ((ts 0).realize (Sum.elim v x)) ((ts 1).realize (Sum.elim v x)) := by
  have h : (BoundedFormula.rel (L := LRV) Rel.rvLe ts).Realize v x
      ↔ Structure.RelMap (L := LRV) Rel.rvLe (fun i => (ts i).realize (Sum.elim v x)) := Iff.rfl
  rw [h]
  have h2 : (fun i => (ts i).realize (Sum.elim v x))
      = (fun i => ![(ts 0).realize (Sum.elim v x), (ts 1).realize (Sum.elim v x)] i) := by
    funext i; fin_cases i <;> rfl
  rw [h2]; exact Iff.rfl

end AtomRealize

/-- **The cover, in `Eval` form.** -/
theorem qf2_cover_eval {n : ℕ} {sn : Fin n → SortTag} :
    ∀ (φ : Bf n), WellSorted sE sn φ → φ.IsQF →
      ∃ q : QF2 sn, ∀ (M : Type) [LRV.Structure M], M ⊨ Axioms.ACVF → ∀ x : Fin n → M,
        (∀ i, sortEval (sn i) (x i)) →
        (φ.Realize (default : Empty → M) x ↔ q.Eval x) := by
  intro φ
  induction φ with
  | falsum =>
    intro _ _
    exact ⟨.falsum, fun M _ _ x _ => Iff.rfl⟩
  | equal t u =>
    intro hws _
    cases hws with
    | equal sn' ht hu =>
      rcases hs : TmSort sE sn t with _ | s
      · rw [hs] at ht; exact absurd ht (by simp)
      · rcases hu' : TmSort sE sn u with _ | s'
        · rw [hu'] at hu; exact absurd hu (by simp)
        · have hss : s = s' := by
            rw [hs] at ht; rw [hu'] at hu
            exact (Option.some.inj ht).trans (Option.some.inj hu).symm
          subst hss
          cases s with
          | vf =>
            obtain ⟨a, ha⟩ := vfOpt_exists t hs
            obtain ⟨b, hb⟩ := vfOpt_exists u hu'
            refine ⟨.eqVF a b, fun M _ _ x _ => ?_⟩
            rw [eval_eqVF]
            change (Term.realize (Sum.elim (default : Empty → M) x) t =
              Term.realize (Sum.elim (default : Empty → M) x) u ↔
              VFT2.Val a x = VFT2.Val b x)
            rw [vfOpt_val t hs ha, vfOpt_val u hu' hb]
          | rv =>
            obtain ⟨a, ha⟩ := rvOpt_exists t hs
            obtain ⟨b, hb⟩ := rvOpt_exists u hu'
            refine ⟨.eqRV a b, fun M _ _ x _ => ?_⟩
            rw [eval_eqRV]
            change (Term.realize (Sum.elim (default : Empty → M) x) t =
              Term.realize (Sum.elim (default : Empty → M) x) u ↔
              RVT2.Val a x = RVT2.Val b x)
            rw [rvOpt_val t hs ha, rvOpt_val u hu' hb]
  | rel R ts =>
    intro hws _
    cases hws with
    | rel sn' R' ts' h =>
      cases R with
      | memVF =>
        obtain ⟨a, ha⟩ := vfOpt_exists (ts 0) (h 0)
        refine ⟨.inVF a, fun M _ _ x _ => ?_⟩
        rw [eval_inVF, realize_rel_memVF (v := default), vfOpt_val (ts 0) (h 0) ha]
      | memRV =>
        obtain ⟨u, hu⟩ := rvOpt_exists (ts 0) (h 0)
        refine ⟨.inRV u, fun M _ _ x _ => ?_⟩
        rw [eval_inRV, realize_rel_memRV (v := default), rvOpt_val (ts 0) (h 0) hu]
      | memUnits =>
        obtain ⟨u, hu⟩ := rvOpt_exists (ts 0) (h 0)
        refine ⟨.unitRV u, fun M _ _ x _ => ?_⟩
        rw [eval_unitRV, realize_rel_memUnits (v := default), rvOpt_val (ts 0) (h 0) hu]
      | rvLe =>
        obtain ⟨u, hu⟩ := rvOpt_exists (ts 0) (h 0)
        obtain ⟨w, hw⟩ := rvOpt_exists (ts 1) (h 1)
        refine ⟨.leRV u w, fun M _ _ x _ => ?_⟩
        rw [eval_leRV, realize_rel_rvLe (v := default), rvOpt_val (ts 0) (h 0) hu,
          rvOpt_val (ts 1) (h 1) hw]
  | imp a b iha ihb =>
    intro hws hqf
    cases hws with
    | imp sn' ha hb =>
      obtain ⟨hqa, hqb⟩ := isQF_imp_inv hqf
      obtain ⟨qa, hva⟩ := iha ha hqa
      obtain ⟨qb, hvb⟩ := ihb hb hqb
      refine ⟨.imp qa qb, fun M inst hM x hx => ?_⟩
      rw [eval_imp, BoundedFormula.realize_imp]
      exact ⟨fun h h1 => (hvb M hM x hx).mp (h ((hva M hM x hx).mpr h1)),
        fun h h1 => (hvb M hM x hx).mpr (h ((hva M hM x hx).mp h1))⟩
  | all χ ih =>
    intro _ hqf
    exact absurd hqf (BoundedFormula.not_all_isQF χ)

/-- **`qf2_cover`**: a well-sorted quantifier-free formula over a sorted context is, at sorted
tuples in every model of `ACVF`, the image `q.toRV` of a `QF2` term. -/
theorem qf2_cover {n : ℕ} (sn : Fin n → SortTag) (φ : Bf n) (hws : WellSorted sE sn φ)
    (hqf : φ.IsQF) :
    ∃ q : QF2 sn, ∀ (M : Type) [LRV.Structure M], M ⊨ Axioms.ACVF → ∀ x : Fin n → M,
      (∀ i, sortEval (sn i) (x i)) →
      (φ.Realize (fun e : Empty => e.elim) x ↔
        (q.toRV).Realize (fun e : Empty => e.elim) x) := by
  obtain ⟨q, hq⟩ := qf2_cover_eval (sn := sn) φ hws hqf
  refine ⟨q, fun M _ hM x hx => ?_⟩
  have hv : (fun e : Empty => e.elim) = (default : Empty → M) := funext (fun e => e.elim)
  rw [hv]
  exact (hq M hM x hx).trans (QF2.realize_toRV q x).symm

end Extract

end QFRes2
end SpecialTransformations.Milestone0.Transfer
