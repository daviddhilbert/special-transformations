/-
# Lemma 3.6 (`lift:transcendental`): the exact pair-level statement, its wiring, and its residuals

Member `m8`, swarm `smw2ngn1z`.  Reference: Yin, `qe.tex:732`:

> **Lemma 3.6.** Suppose that `e ∈ U(M)` and `rv(e)` is transcendental over `K(Ŝ)`.  If `Γ(Ŝ)` is
> divisible, then Claim (⋆) holds.

Claim (⋆) (`qe.tex:600`): `RV(⟨Ŝ,e⟩) = ⟨RV(Ŝ), rv(e)⟩ ⊆ RV(S)`, and `f ↾ Ŝ` extends to
`f* : ⟨Ŝ,e⟩ → N` with `f*(rv(e)) = f(rv(e))`.

## What is proved here, and what is a named residual

**Proved** (`lemma36_claim_star`): the pair-level statement of Lemma 3.6 at a **fixed** model `M`
(no `∀ M ∀ N` gate), with the hypotheses named in `Lemma36Hyp`, and with the paper's dimension
inequality (EP 3.4.3) taken as the quotation `EPDimensionInequality` of `PEQuotes.lean` — exactly
the author ruling.  The conclusion is `ClaimStar`, i.e. the frozen encoding's form of Claim (⋆):

* `M5L.ResidualClasses S ⟨Ŝ,e⟩` — every `RV`-element of `⟨Ŝ,e⟩` is `Γ`-class-equal to an element of
  `S`: the paper's `RV(⟨Ŝ,e⟩) ⊆ ⟨RV(Ŝ), rv(e)⟩` read in `Γ = RV/Kˣ` (the only reading the frozen
  one-sorted encoding has, since `Γ` is not a sort there — `Milestone0/DECISION.md`);
* `Assembly.Standing ⟨Ŝ,e⟩` — the two standing properties are preserved.

**The `Γ`-route is the paper's own**, and no residue-field induction is needed for this half:
EP 3.4.3 gives `M5Ledger.GammaHullInitial S ⟨Ŝ,e⟩` (rational rank `0`), `Γ(Ŝ)`-divisibility
(`Assembly.Standing S`) turns that into `M5Ledger.GammaEq S ⟨Ŝ,e⟩`, and a `Γ`-equality is the class
statement.  That chain is `QE/Lemma36Gamma.lean`, proved with no residual.

**Named residuals** (machine-checked statements, *not* assumed by anything in this file):

* `TranscendenceDescent` — the paper's "Clearly `rv(e)` does not contain any element that is
  algebraic over `VF(Ŝ)`; in particular, `e` is transcendental over `VF(Ŝ)`" (q1(a)): if `e` is
  algebraic over `VF(Ŝ)` then a nonzero residue polynomial over `K(Ŝ)` vanishes at `rv e`, so
  `RVTrans` forces `e` transcendental.  The proof is the leading-term argument used in the paper's
  induction: normalise `Σ b_i e^i = 0` by a term of maximal value, divide, and take residues; the
  frozen encoding needs `M5L.VFInvClosedOn S` to represent `rv(b_i/b_j)` inside `S` (the `VF` sort
  of a substructure is a ring, not a field), which is why that hypothesis appears here and not in
  the paper.  Not used below: the `Γ`-route does not need it.
* `RVTransImpliesSeparated` — Lemma 3.6's hypothesis implies the tree's `M5L.Separated S e` (the
  hypothesis `QE/OneStepCases.lean`'s `CaseSeparated` slot carries).  Proof: a `Cls`-equality
  `rv(e^k)·rv(x) = rv(y)·c` with `c` a unit (`M5L.cls_ratio_units`) exhibits a *nonzero* residue
  polynomial `X^k·rv x − rv y·c` vanishing at `rv e`.  Again not used below; it is the bridge a
  consumer that wants `CaseSeparated` would use.
* q1(b) (the symmetric statement on the `N`-side, `f(rv e)` transcendental over `f(VF(Ŝ))`) needs
  the transport of `RVTrans` along the monomorphism, i.e. preservation of the *atomic* formulas
  defining `iUnits`/`iRV` — this is not in the tree; recorded as not done.

## The "`f*(rv(e)) = f(rv(e))`" half of Claim (⋆)

Not formalised here: it is the map-construction half (a valued field embedding
`VF(⟨Ŝ,e⟩) → VF(N)` given by `e ↦ d`, converted to an `L_RV`-monomorphism by Remark 3.1, i.e.
`QE/Jm2T1.lean`'s machinery).  Its ingredient `d ∈ VF(N)` with `rv(d) = f(rv(e))` **is** proved
here: `exists_vf_of_rv_map`, from `Assembly.RVeqRvVF_of_model`.

## Stress tests (§4)

* `standing_top_instance` — the headline theorem instantiated at `S = ⊤`: the conclusion is
  `Assembly.Standing ⊤`, which is a theorem of the tree (`StandingTree`), so the wiring's conclusion
  is satisfiable and the theorem is not `False → False`.
* `claimStar_self` — at `T = S` the class form holds for every `S` (`M5L.ResidualClasses S S`),
  so `ClaimStar`'s first component is not an unsatisfiable predicate.
-/
import M5L34_36
import Lemma36Gamma
import PEQuotes
import OneStepCases

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
open SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Milestone0.M8

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {N : Type} [LRV.Structure N] [hN : N ⊨ Axioms.ACVF]

/-! ## 1. Lemma 3.6's hypotheses, named

The paper's hypotheses (`qe.tex:732`), in the frozen vocabulary, at a fixed model `M`:

* `rv(e) ∈ RV(S) \ RV(Ŝ)` is what the Lemma-3.3 reduction hands Lemma 3.6 (`he : iRv e ∈ S`), so
  that `f(rv e)` is defined;
* `e ∈ U(M)` — `iUnits (iRv e)`;
* `rv(e)` transcendental over `K(Ŝ)` — `RVTrans S e`;
* `Γ(Ŝ)` divisible and `K(Ŝ) = K(M)` — packaged as `Assembly.Standing S`, which is exactly the
  standing assumption after Lemma 3.3 (`QE/Assembly_frozen.lean`). -/

/-- **The hypotheses of Lemma 3.6**, pair-level and named. -/
structure Lemma36Hyp (S : LRV.Substructure M) (e : M) : Prop where
  /-- the paper's standing assumptions after Lemma 3.3: `K(Ŝ) = K(M)`, `Γ(Ŝ)` divisible -/
  standing : Assembly.Standing S
  /-- `e` is an element of the valued field -/
  vf : iVF e
  /-- `e ∈ U(M)`: its value is `0` -/
  unit : iUnits (iRv e)
  /-- `rv(e)` is not the root of any nonzero residue polynomial over `K(Ŝ)` -/
  transc : RVTrans S e unit
  /-- `rv(e) ∈ RV(S)`, as the Lemma-3.3 reduction supplies (so that `f(rv e)` is defined) -/
  rv_mem : iRv e ∈ S

/-- **Claim (⋆) in the frozen encoding.**  The paper's `RV(⟨Ŝ,e⟩) = ⟨RV(Ŝ), rv(e)⟩ ⊆ RV(S)`,
stated as the class computation `M5L.ResidualClasses` (the encoding's `Γ`-form of it), together
with preservation of the standing properties. -/
def ClaimStar (S : LRV.Substructure M) (e : M) : Prop :=
  M5L.ResidualClasses S (Substructure.closure LRV ((S : Set M) ∪ {e})) ∧
    Assembly.Standing (Substructure.closure LRV ((S : Set M) ∪ {e}))

/-! ## 2. Lemma 3.6, proved from the quoted dimension inequality -/

/-- **Lemma 3.6 (`lift:transcendental`), pair-level, with EP 3.4.3 as the only quotation.**

Hypotheses: `Lemma36Hyp S e` (in particular `Γ(Ŝ)` divisible — the paper's hypothesis — and `rv(e)`
transcendental over `K(Ŝ)`).  Conclusion: Claim (⋆), i.e. `RV(⟨Ŝ,e⟩) ⊆ Γ(Ŝ)` in class form, and
`⟨Ŝ,e⟩` is `Standing`.

Nothing else is assumed: no `VFInvClosedOn`, no `QuotExpansions`, no `IsVFGen`, no separation
hypothesis, no henselianity, and no gate over `M`/`N` — the statement is about this pair. -/
theorem lemma36_claim_star (hq : EPDimensionInequality) {S : LRV.Substructure M} {e : M}
    (h : Lemma36Hyp S e) : ClaimStar S e := by
  have hT : Assembly.Standing (Substructure.closure LRV ((S : Set M) ∪ {e})) :=
    standing_of_EPDimensionInequality hq h.standing h.unit h.vf h.transc
  exact ⟨residualClasses_of_gammaEq (gammaEq_of_gammaHullInitial h.standing.2
    (gammaHullInitial_of_EPDimensionInequality hq h.unit h.vf h.transc)), hT⟩

/-- Lemma 3.6's *conclusion* as the paper states it first: `RV(⟨Ŝ,e⟩)`'s classes are already
classes of `S`. -/
theorem lemma36_rv_classes (hq : EPDimensionInequality) {S : LRV.Substructure M} {e : M}
    (h : Lemma36Hyp S e) :
    M5L.ResidualClasses S (Substructure.closure LRV ((S : Set M) ∪ {e})) :=
  (lemma36_claim_star hq h).1

/-- And the extension is `Standing`, i.e. the one-step's requirement. -/
theorem lemma36_standing (hq : EPDimensionInequality) {S : LRV.Substructure M} {e : M}
    (h : Lemma36Hyp S e) :
    Assembly.Standing (Substructure.closure LRV ((S : Set M) ∪ {e})) :=
  (lemma36_claim_star hq h).2

/-! ## 3. The `d ∈ VF(N)` with `rv(d) = f(rv(e))` (the paper's "Choose a `d`") -/

/-- **`rv` is surjective onto the nonzero `RV` sort, at a model** — restated from
`Assembly.RVeqRvVF_of_model` in the form Lemma 3.6 uses: for every `RV`-element `y` of `N` there is
`d ∈ VF(N)` with `rv(d) = y`, unless `y = rv 0` (which is `rv` of `0` anyway). -/
theorem exists_vf_of_rv {y : N} (hy : iRV y) : ∃ d : N, iVF d ∧ iRv d = y := by
  rcases Assembly.RVeqRvVF_of_model (M := N) y hy with ⟨d, hdVF, hd⟩ | h0
  · exact ⟨d, hdVF, hd⟩
  · refine ⟨Transfer.iVFZero, Transfer.vf_zero_mem hN, ?_⟩
    rw [h0, RVCalc.rv_zero_eq hN]

/-- **The paper's "Choose a `d ∈ VF(N)` with `rv(d) = f(rv(e))"**, reduced to the sort-preservation
of `f` on the single element `rv e` (`hfrv : iRV (f ⟨rv e, _⟩)`), which the `L_RV` embedding
supplies and which the tree does not state as an API lemma. -/
theorem exists_vf_of_rv_map {S : LRV.Substructure M} {f : S ↪[LRV] N} {e : M}
    (he : iRv e ∈ S) (hfrv : iRV (f ⟨iRv e, he⟩)) :
    ∃ d : N, iVF d ∧ iRv d = f ⟨iRv e, he⟩ :=
  exists_vf_of_rv (N := N) hfrv

/-! ## 4. The named residuals (machine-checked statements; assumed by nothing here) -/

/-- **Residual q1(a) — the paper's "Clearly ...".**  If `rv(e)` is transcendental over `K(Ŝ)` then
`e` is not algebraic over `VF(Ŝ)`: the contrapositive "`e` algebraic ⇒ `rv(e)` algebraic" is the
leading-term argument of the paper's induction on `m`.  `M5L.VFInvClosedOn S` appears because the
normalisation divides by a coefficient, and the frozen `VF` sort of `S` has no inverse symbol.

Nothing in this file uses this statement; it is here so the remaining obligation is machine-checked
text rather than prose. -/
def TranscendenceDescent (S : LRV.Substructure M) (e : M) (hunit : iUnits (iRv e)) : Prop :=
  M5L.VFInvClosedOn S → RVTrans S e hunit → ∀ n : ℕ, 1 ≤ n → ¬ AlgebraicOverVF S e n

/-- **Residual, bridging to the tree's `Separated`.**  Lemma 3.6's hypothesis is *stronger* than
the hypothesis `QE/OneStepCases.lean`'s `CaseSeparated` slot carries: a `Cls`-equality
`rv(e^k)·rv(x) ~ rv(y)` with `x, y ∈ S ∩ VF` exhibits the nonzero residue polynomial
`X^k·rv(x) − rv(y)` (times a unit) vanishing at `rv e` (`M5L.cls_ratio_units` supplies the unit).

So `Lemma36Hyp` discharges the separated slot's hypothesis; the slot's remaining content (the
extension `T` with its monomorphism `g`) is the model-theoretic realisation, not Lemma 3.6. -/
def RVTransImpliesSeparated (S : LRV.Substructure M) (e : M) (hunit : iUnits (iRv e)) : Prop :=
  RVTrans S e hunit → M5L.Separated S e

/-! ## 5. Stress tests -/

/-- **`⊤`-witness**: at `S = ⊤` the headline theorem's conclusion is `Assembly.Standing ⊤`, which
holds in every model (`StandingTree`), so `ClaimStar`'s second component is satisfiable and the
wiring is not vacuous at the top element. -/
theorem standing_top_instance : Assembly.Standing (⊤ : LRV.Substructure M) :=
  ⟨fun _ _ => trivial, StandingTree.gammaDivisible_top⟩

/-- **`T = S`**: Claim (⋆)'s class component holds at `T = S` for every `S`, so it is not an
unsatisfiable predicate. -/
theorem claimStar_self_residual (S : LRV.Substructure M) : M5L.ResidualClasses S S :=
  residualClasses_self S

/-- The residual statements are consistent with the proved chain (they are *not* used by it): the
`Γ`-route needs no residue-field input at all. -/
theorem lemma36_needs_no_residual (hq : EPDimensionInequality) {S : LRV.Substructure M} {e : M}
    (h : Lemma36Hyp S e) : ClaimStar S e :=
  lemma36_claim_star hq h

end SpecialTransformations.Milestone0.M8

/-! ## Axiom audit -/

#print axioms SpecialTransformations.Milestone0.M8.lemma36_claim_star
#print axioms SpecialTransformations.Milestone0.M8.lemma36_rv_classes
#print axioms SpecialTransformations.Milestone0.M8.lemma36_standing
#print axioms SpecialTransformations.Milestone0.M8.exists_vf_of_rv
#print axioms SpecialTransformations.Milestone0.M8.exists_vf_of_rv_map
#print axioms SpecialTransformations.Milestone0.M8.standing_top_instance
#print axioms SpecialTransformations.Milestone0.M8.claimStar_self_residual
