/-
**The Mathlib-valued-field bridge for a model of the frozen `ACVF`** — the shortcut for the paper's
valuation-theoretic lemmas (`rv:root:lift:vf` / Lemma 3.2, `lift:divisible:hull` / 3.5,
`lift:transcendental` / 3.7, `e:transc`, `lift:value:full`).

`QE/Assembly_val.lean` already proves the two facts that make those lemmas *applicable at a model of
the tagged encoding* instead of needing a hand port:

* `M4ValueOnly.exists_valuation_predV` (`QE/Assembly_val.lean:21033`) — the `VF`-sort of a model of
  `Axioms.ACVF` carries a genuine Mathlib `Valuation`, with `iLe (iRv y) (iRv x) ↔ w x ≤ w y`;
* `VFAlgClosed.isAlgClosed_vfType` (`:11575`) — that field is algebraically closed.

Every one of those paper lemmas is stated in `QE/Lemma32_root_lifting.lean`,
`QE/Lemma35_divisible_hull.lean`, `QE/Lemma37_transcendental.lean`, `QE/Lifting_transcendental.lean`,
`QE/RV_henselian.lean` for `(K, v)` with `[Field K]`, `[IsAlgClosed K]`,
`v : Valuation K Γ₀` and nothing else. So the "port to the tagged encoding" is **an instantiation at
`K := VFType M` plus the dictionary between the encoding's `iRv`/`iLe` and the valuation**, not a
re-proof. That is what this file packages.

Nothing here is new mathematics. What it adds is the two ingredients in one place, in the direction a
proof consumes them, and the packaging `ValuedModel` so that a caller can write
`let V := valuedModel hM; letI := V.instΓ` and then use `V.w` with `V.le_iff`.

Build (needs current oleans for `Assembly_val` and `Lemma32_root_lifting`; see
`QE/HANDOFF.md`, "Porting Lemma 3.2/3.5/3.7"):

    cd .scratch2 && cp ../QE/ValBridge.lean . && cp ../QE/Lemma32_root_lifting.lean sec3/ \
      && (cd sec3 && lean Lemma32_root_lifting.lean) \
      && LEAN_PATH=$PWD:$PWD/sec3:$LEAN_PATH lean ValBridge.lean
-/
import Assembly_val
import Lemma32_root_lifting

open FirstOrder FirstOrder.Language
open scoped FirstOrder
open Polynomial

set_option linter.style.haveILetI false

open SpecialTransformations.Milestone0
open SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Milestone0.M5

variable {M : Type} [LRV.Structure M]

/-- **A model of the frozen `ACVF` has a genuine Mathlib valued field as its `VF`-sort.**

`w` is a Mathlib `Valuation`, and the encoding's `iLe` on `RV` is `w`'s order read backwards —
`iLe (rv y) (rv x) ↔ w x ≤ w y` — which is the convention of `Milestone0/DECISION.md`: Mathlib's
`Valuation` is the absolute-value order, the paper's `v` is the value-group order. -/
theorem exists_valued_vfType (hM : M ⊨ Axioms.ACVF) :
    ∃ (Γ : Type) (_ : LinearOrderedCommGroupWithZero Γ)
      (w : Valuation (Transfer.VFType (M := M)) Γ),
      ∀ x y : Transfer.VFType (M := M), iLe (iRv y.1) (iRv x.1) ↔ w x ≤ w y :=
  M4ValueOnly.exists_valuation_predV (M := M) (hM := hM)

/-- **The `VF`-sort of a model of `ACVF` is an algebraically closed field** — the hypothesis
`[IsAlgClosed K]` that Lemmas 3.2, 3.5 and 3.7 all carry. -/
theorem isAlgClosed_vfType (hM : M ⊨ Axioms.ACVF) :
    @IsAlgClosed (Transfer.VFType (M := M)) (Transfer.vfFieldOfModel (M := M) (hM := hM)) :=
  VFAlgClosed.isAlgClosed_vfType (M := M) (hM := hM)

/-- The two ingredients together, in the shape a `YinRV.*` lemma wants: a field, an algebraically
closed one, and a valuation whose order is the encoding's `iLe` backwards. -/
structure ValuedModel (hM : M ⊨ Axioms.ACVF) where
  /-- the value group -/
  Γ : Type
  /-- its ordered-commutative-group-with-zero structure -/
  instΓ : LinearOrderedCommGroupWithZero Γ
  /-- the valuation on the `VF`-sort -/
  w : Valuation (Transfer.VFType (M := M)) Γ
  /-- `iLe` on `RV` is the valuation order, reversed -/
  le_iff : ∀ x y : Transfer.VFType (M := M), iLe (iRv y.1) (iRv x.1) ↔ w x ≤ w y

/-- The packaged form: every model of `ACVF` is a valued field in Mathlib's sense.  Use it as
`let V := valuedModel hM; letI := V.instΓ`, and then `V.w` is the valuation and `V.le_iff` is the
dictionary back into the encoding.  (`ValuedModel` bundles a *type*, so it cannot be eliminated out
of an `Exists` directly; `valuedModel_nonempty` does the elimination into `Prop` first.) -/
theorem valuedModel_nonempty (hM : M ⊨ Axioms.ACVF) : Nonempty (ValuedModel (M := M) hM) :=
  let ⟨Γ, hΓ, w, hw⟩ := exists_valued_vfType (M := M) hM
  ⟨⟨Γ, hΓ, w, hw⟩⟩

/-- See `valuedModel_nonempty`. -/
noncomputable def valuedModel (hM : M ⊨ Axioms.ACVF) : ValuedModel (M := M) hM :=
  Classical.choice (valuedModel_nonempty (M := M) hM)

/-- **Lemma 3.2 (`rv:root:lift:vf`) holds at every model of the frozen `ACVF`, with no port.**

This is `YinRV.rv_root_lift_rv` — a theorem about valued fields, already proved unconditionally in
`QE/Lemma32_root_lifting.lean` — instantiated at the `VF`-sort.  It is here as the demonstration that
the transport is an instantiation: what a real port still owes is only the translation of the
*encoding's* hypotheses (an `RV`-polynomial root, in the syntax of `Milestone0/Encoding.lean`) into
`huniv`/`hred` below, which is where the `iRv`/`rv` dictionary is needed. -/
theorem rv_root_lift_at_model (hM : M ⊨ Axioms.ACVF) {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation (Transfer.VFType (M := M)) Γ)
    {F : (Transfer.VFType (M := M))[X]} (hF : F ≠ 0) {b : Transfer.VFType (M := M)}
    {t : YinRV.RV w} (ht : t ≠ YinRV.rvZero w) (hb : YinRV.rv w b = t)
    (huniv : ∀ i ∈ F.support, w (F.coeff i * b ^ i) = 1)
    (hred : w (∑ i ∈ F.support, F.coeff i * b ^ i) < 1) :
    ∃ b' : Transfer.VFType (M := M), YinRV.rv w b' = t ∧ F.IsRoot b' := by
  letI : Field (Transfer.VFType (M := M)) := Transfer.vfFieldOfModel (M := M) (hM := hM)
  letI : IsAlgClosed (Transfer.VFType (M := M)) := isAlgClosed_vfType (M := M) hM
  exact YinRV.rv_root_lift_rv w hF ht hb huniv hred

end SpecialTransformations.Milestone0.M5
