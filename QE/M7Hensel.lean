/-
# Lemma 3.3, step (ii): the henselization of `VF(Ŝ)`, its residue/value data, and the
# `OneStepVFP` reduction

`qe.tex` §3.1 (l. 578 onward) fixes `M, N ⊨ ACVF` with `N` `‖M‖⁺`-saturated, a substructure
`S ⊆ M` and a monomorphism `f : S → N`.  Lemma 3.3 (l. 580) produces `S*` with `VF(S*) = VF(S)`,
`K(S*) = K(M)` and `Γ(S*)` the divisible hull of `Γ(S)`.  The *structural* input of the section is
not in that lemma, but in Proposition 3.9's proof (l. 815):

> First of all, since the henselization `Š^h` of `Š` in `M` is an immediate extension (in the sense
> of valuation theory), we have `RV(⟨Š^h, Š⟩) = RV(Š)`.  So we may assume that `(VF(Š), O(Š))` is
> henselian.

The tree has no henselianity predicate and no henselization existence statement: `QE/HANDOFF.md`
records `3.3 PrepStepSize | open (henselization + get Standing; ...)`, and the stopped swarm's base
(`.ultramath/smw1v42vv/m6/Lemma33.lean`, taken over here as `M7L33base.lean` and **compiled green
in the current tree**) notes at `HenselizationStep`: "The tree has no henselization existence
proof, so `OneStepVFP` is *literally* weaker than Lemmas 3.4/3.5, which are stated at henselian
`Š`."  This file supplies that input in the shape the frozen encoding can consume, and wires it in.

## Named inputs (transcribed from valuation theory — *not* Marker, so real work, not quoted)

* `HenselizationExists M` — every substructure has an **immediate henselian** extension: the
  paper's "the henselization `Š^h` of `Š` in `M` is an immediate extension", existence form.
  Classical: Engler–Prestel, *Valued Fields*, Ch. 5 (the henselization is immediate); Drinking,
  *Limit theorems*.  Not proved here.
* `ImmediateLift` — the **universal property of the henselization** at the encoding: an embedding
  `f : S ↪ N` extends along an immediate henselian extension `S ≤ T`, `N` henselian (every model of
  `ACVF` is).  Engler–Prestel Thm 5.1.2.  This is the honest replacement for the paper's
  "we may assume that `(VF(Š), O(Š))` is henselian": the paper only justifies the
  `Standing`-invariance of the step, which is `M6L33.standing_of_immediate` and is used below.
  Caveat recorded for the residual: in the *tagged one-sorted* encoding the lift also forces the
  junk values of the new `VF` elements to match (the encoding's ill-sorted terms such as
  `rv (rv x)` are unconstrained by `ACVF`, see `QE/SortCover.lean`), so this named input is
  stronger than its valuation-theoretic reading.  That is a property of the frozen encoding, not of
  the paper's argument.

## What is *defined* (so that the inputs are statements, not placeholders)

* `Ovf S` / `Mvf S` — the valuation ring `O(Š) = {x ∈ VF(Š) : v(x) ≥ 0}` and the maximal ideal
  `m(Š) = {x ∈ VF(Š) : v(x) > 0}`, read off the encoding's preorder `iLe` on `RV`.  As in the
  paper, `O` is *defined* from `rv` and carries no symbol.
* `vfEval` — polynomial evaluation `Σ_{i ≤ n} aᵢ xⁱ` in the `VF` sort.
* `IsHenselianVF S` — **`(VF(S), O(S))` is henselian**, in the "simple root lifts" form of the
  Hensel lemma: a monic `F` over `O(S)` with `F(0) ∈ m(S)` and `F'(0) = a₁` a unit of `VF` has a
  root in `m(S)` (Engler–Prestel Thm 4.1.3 and corollaries).

## What is *proved* here (no `sorry`, no `axiom`, no `native_decide`)

* `Immediate` is reflexive and transitive; `IsVFGen` is preserved by it (`vfGen_of_immediate`) —
  the paper's use of `RV(⟨Š^h, Š⟩) = RV(Š)`: henselizing does not destroy `VF`-generatedness, so
  Remark 3.1 keeps applying afterwards;
* `henselian_congr`: henselianity is a property of the *valued field* (the `VF`-part), not of the
  substructure — which is why the henselization's data is stated as `RV`-invariance (`Immediate`);
* `rv_eq_of_henselization`: the henselization adds no `RV` element, i.e. `K(T) = K(S)` and
  `Γ(T) = Γ(S)`: the residue/value data;
* `standing_hens`: every `Standing` substructure has an immediate henselian extension that is still
  `Standing` — the paper's reduction, with invariance supplied by the base;
* `henselizationStep_of_exists`, `oneStepVFP_of_hens`: existence + lift + the one-element step at
  henselian domains give the frozen `Assembly.OneStepVFP` (Lemmas 3.4–3.8), hence
  `M7Paper.OneStepSizeFree`;
* `paper_theorem_2_3_sat_of_hens`: Theorem 2.3 from `ShoenfieldTestSat` (Marker content, quoted by
  the author ruling), `PrepStepSize` (Lemma 3.3 at `SizeHyp`) and the two henselization inputs.

## Residuals, named exactly

`HenselizationExists`, `ImmediateLift`, and the one-element step at henselian domains (the paper's
Lemmas 3.4–3.8, in the form stated as the hypothesis of `oneStepVFP_of_hens`), plus
`M7Paper.PrepStepSize` itself.  None of them restates another: `IsHenselianVF` is a statement about
roots of polynomials in the valuation ring, `Immediate` is `RV`-invariance, `ImmediateLift` is
about embeddings of the extended substructure.  In particular `HenselizationExists` is *not*
"take `T = ⊤`": `Immediate` forbids adding `RV`-elements at all, and `⊤` is not immediate over a
proper `S` (see `henselian_self_immediate` for the non-vacuity witness).
-/
import Lemma33

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
open SpecialTransformations.Milestone0.LRV

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace SpecialTransformations
namespace Milestone0
namespace M7Hens

variable {M N : Type} [LRV.Structure M] [LRV.Structure N]

/-! ### The valuation ring and maximal ideal of a substructure -/

section Ring

variable [hM : M ⊨ Axioms.ACVF]

/-- `O(Š)`, the valuation ring of the `VF`-part of `Š`: `x ∈ VF(Š)` with `v(x) ≥ 0`, i.e.
`rv 1 ≤ rv x`.  As in the paper, `O` is defined from `rv` and needs no symbol of its own. -/
def Ovf (S : LRV.Substructure M) : Set M :=
  {x | x ∈ S ∧ iVF x ∧ iLe (iRv (Transfer.iVFOne (M := M))) (iRv x)}

/-- `m(Š)`, the maximal ideal of `O(Š)`: `x ∈ VF(Š)` with `v(x) > 0`, i.e. `¬ (rv x ≤ rv 1)`. -/
def Mvf (S : LRV.Substructure M) : Set M :=
  {x | x ∈ S ∧ iVF x ∧ ¬ iLe (iRv x) (iRv (Transfer.iVFOne (M := M)))}

theorem mem_Ovf {S : LRV.Substructure M} {x : M} :
    x ∈ Ovf S ↔ x ∈ S ∧ iVF x ∧ iLe (iRv (Transfer.iVFOne (M := M))) (iRv x) := Iff.rfl

theorem mem_Mvf {S : LRV.Substructure M} {x : M} :
    x ∈ Mvf S ↔ x ∈ S ∧ iVF x ∧ ¬ iLe (iRv x) (iRv (Transfer.iVFOne (M := M))) := Iff.rfl

/-- `1` lies in the valuation ring of every substructure containing it. -/
theorem one_mem_Ovf {S : LRV.Substructure M} (h : Transfer.iVFOne (M := M) ∈ S) :
    Transfer.iVFOne (M := M) ∈ Ovf S := by
  have hVF : iVF (Transfer.iVFOne (M := M)) := Transfer.vf_one_mem (M := M) hM
  exact mem_Ovf.mpr ⟨h, hVF, RVCalc.le_refl_rv hM (Transfer.rv_mem hM hVF)⟩

/-- `m(Š) ⊆ O(Š)`: a strictly positive value is a nonnegative one. -/
theorem Mvf_subset_Ovf {S : LRV.Substructure M} {x : M} (hx : x ∈ Mvf S) : x ∈ Ovf S := by
  obtain ⟨hxS, hxVF, hxpos⟩ := mem_Mvf.mp hx
  have hxrv : iRV (iRv x) := Transfer.rv_mem hM hxVF
  have h1rv : iRV (iRv (Transfer.iVFOne (M := M))) :=
    Transfer.rv_mem hM (Transfer.vf_one_mem (M := M) hM)
  refine mem_Ovf.mpr ⟨hxS, hxVF, ?_⟩
  by_contra hcon
  exact hxpos (Or.resolve_left (RVCalc.le_total_rv hM h1rv hxrv) hcon)

end Ring

/-! ### Polynomial evaluation in the `VF` sort -/

section Poly

/-- `Σ_{i ≤ n} f i` in the `VF` sort.  (A fold, because the tree carries no `AddCommMonoid`
instance for the encoding's one-sorted carrier.) -/
def vfSum (f : ℕ → M) : ℕ → M
  | 0 => f 0
  | (k + 1) => iVFAdd (vfSum f k) (f (k + 1))

/-- Evaluation of the polynomial `Σ_{i ≤ n} (a i) · xⁱ` in the `VF` sort. -/
def vfEval (a : ℕ → M) (n : ℕ) (x : M) : M :=
  vfSum (fun i => iVFMul (a i) (StandingTree.vfPow (M := M) x i)) n

/-- A finite sum of `VF`-sorted elements is `VF`-sorted. -/
theorem vfSum_mem [hM : M ⊨ Axioms.ACVF] {f : ℕ → M} (hf : ∀ i, iVF (f i)) (n : ℕ) :
    iVF (vfSum f n) := by
  induction n with
  | zero => exact hf 0
  | succ k ih => exact Transfer.vf_add_mem (M := M) hM ih (hf (k + 1))

/-- Evaluation at `x` of a polynomial all of whose coefficients lie in the `VF` sort lies in the
`VF` sort. -/
theorem vfEval_mem [hM : M ⊨ Axioms.ACVF] {a : ℕ → M} {x : M} (ha : ∀ i, iVF (a i))
    (hx : iVF x) (n : ℕ) : iVF (vfEval (M := M) a n x) :=
  vfSum_mem (M := M)
    (fun i => Transfer.vf_mul_mem (M := M) hM (ha i) (StandingTree.vf_pow_mem (M := M) hx i)) n

end Poly

/-! ### `(VF(S), O(S))` is henselian -/

/-- **`(VF(S), O(S))` is henselian**, in the "simple root lifts" form of the Hensel lemma: if
`F = Σ_{i ≤ n} aᵢ Xⁱ` is monic of degree `n ≥ 1` over the valuation ring `O(S)`, its constant
coefficient lies in `m(S)` and its linear coefficient `a₁ = F'(0)` is a unit of `VF`, then `F` has a
root in `m(S)`.

Equivalence with henselianity of the valued field `(VF(S), O(S))` is Engler–Prestel, *Valued
Fields*, Theorem 4.1.3 and its corollaries.  This is valuation theory (not Marker), so it is
*defined* here and only used, never assumed.

**The constant-term clause**, i.e. the second `iLe`-disjunct: the intended "a₀ has strictly negative
value" is `¬iLe (rv (a 0)) (rv 1)`.  ERRATUM (swarm smw2jkpn4 m1's `HenselDefect`, 2026-11-04):
this used to read `¬iLe (rv 1) (rv (a 0))`, which contradicts the coefficient clause at `i = 0` and
made the whole predicate vacuous (`IsHenselianVF S` held of *every* substructure — so everything
consuming the predicate, notably `HenselizationExists`, was trivially satisfiable).  The clause was
restored to the intended argument order; every consumption of `IsHenselianVF` is unaffected. -/
def IsHenselianVF (S : LRV.Substructure M) : Prop :=
  ∀ (n : ℕ) (a : ℕ → M),
    1 ≤ n →
      (∀ i, a i ∈ S) →
      (∀ i, iVF (a i)) →
      (∀ i, n < i → a i = Transfer.iVFZero (M := M)) →
      a n = Transfer.iVFOne (M := M) →
      (∀ i, i ≤ n → iLe (iRv (Transfer.iVFOne (M := M))) (iRv (a i))) →
      (¬ iLe (iRv (a 0)) (iRv (Transfer.iVFOne (M := M)))) →
      iUnits (iRv (a 1)) →
      ∃ b : M, b ∈ S ∧ iVF b ∧ vfEval (M := M) a n b = Transfer.iVFZero (M := M) ∧
        ¬ iLe (iRv b) (iRv (Transfer.iVFOne (M := M)))

/-- **Henselianity is a property of the valued field, not of the substructure**: two substructures
with the same `VF`-part have the same henselianity.  (This is why the henselization's data below is
stated as `RV`-invariance: `Immediate` says `RV(T) = RV(S)`, and the `VF`-part is what carries
henselianity.) -/
theorem henselian_congr {S T : LRV.Substructure M}
    (hvf : ∀ x : M, iVF x → (x ∈ S ↔ x ∈ T)) :
    IsHenselianVF S ↔ IsHenselianVF T := by
  constructor
  · intro hS n a hn hmem hVF hdeg hmon hle h0 h1
    obtain ⟨b, hbS, hbVF, heval, hbpos⟩ :=
      hS n a hn (fun i => (hvf (a i) (hVF i)).mpr (hmem i)) hVF hdeg hmon hle h0 h1
    exact ⟨b, (hvf b hbVF).mp hbS, hbVF, heval, hbpos⟩
  · intro hT n a hn hmem hVF hdeg hmon hle h0 h1
    obtain ⟨b, hbT, hbVF, heval, hbpos⟩ :=
      hT n a hn (fun i => (hvf (a i) (hVF i)).mp (hmem i)) hVF hdeg hmon hle h0 h1
    exact ⟨b, (hvf b hbVF).mpr hbT, hbVF, heval, hbpos⟩

/-! ### The henselization, existence form, and its residue/value data -/

/-- **The henselization exists and is immediate.**  Every substructure `S ⊆ M` (a model of `ACVF`)
has a substructure `T ⊇ S` henselian at its `VF`-part and *immediate* over `S`
(`M6L33.Immediate`: no new `RV`-elements, hence `K(T) = K(S)` and `Γ(T) = Γ(S)`).

This is the paper's sentence "the henselization `Š^h` of `Š` in `M` is an immediate extension", and
it is the named input the tree lacks (`QE/HANDOFF.md`; `M6L33.HenselizationStep`).  It is classical
valuation theory — Engler–Prestel, *Valued Fields*, Chapter 5; Drinking, *Limit theorems* — hence
real work and not Marker content, and it is transcribed here, not proved. -/
def HenselizationExists (M : Type) [LRV.Structure M] : Prop :=
  ∀ S : LRV.Substructure M, ∃ T : LRV.Substructure M, M6L33.Immediate S T ∧ IsHenselianVF T

section Existence

variable [hM : M ⊨ Axioms.ACVF]

/-- The henselization adds no value-group or residue-field element: `RV(T) = RV(S)`.  This is the
residue/value data of the henselization, and the only property of it that the paper uses. -/
theorem rv_eq_of_henselization {S T : LRV.Substructure M} (h : M6L33.Immediate S T) :
    ∀ x : M, iRV x → (x ∈ T ↔ x ∈ S) :=
  fun x hx => ⟨fun hT => h.2 x hT hx, fun hS => h.1 hS⟩

/-- **Every `Standing` substructure can be henselized without losing `Standing`.**  This is the
paper's "so we may assume that `(VF(Š), O(Š))` is henselian": the henselization is immediate, so
`KEqTop` and `GammaDivisible` are unaffected (`M6L33.standing_of_immediate`). -/
theorem standing_hens (hE : HenselizationExists M) (S : LRV.Substructure M)
    (hS : Assembly.Standing S) :
    ∃ T : LRV.Substructure M, S ≤ T ∧ IsHenselianVF T ∧ Assembly.Standing T := by
  obtain ⟨T, himm, hhen⟩ := hE S
  exact ⟨T, himm.1, hhen, M6L33.standing_of_immediate himm hS⟩

/-- **Henselizing does not destroy `VF`-generatedness** — the paper's use of
`RV(⟨Š^h, Š⟩) = RV(Š)`: Remark 3.1 ("if `K'` is `VF`-generated then `f'` may also be treated as an
`lan{v}`-isomorphism") keeps applying after passing to the henselization. -/
theorem vfGen_of_immediate {S T : LRV.Substructure M} (hgen : Assembly.IsVFGen S)
    (h : M6L33.Immediate S T) : Assembly.IsVFGen T := by
  intro x hxT hxrv
  rcases hgen x (h.2 x hxT hxrv) hxrv with ⟨y, hyS, hyVF, hyr⟩ | hz
  · exact Or.inl ⟨y, h.1 hyS, hyVF, hyr⟩
  · exact Or.inr hz

/-- **Non-vacuity of the henselian predicate**: a substructure that is already henselian is its own
immediate henselian extension.  (So `HenselizationExists` is not the trivial statement "some
`T ⊇ S` exists", because `Immediate` forbids adding `RV`-elements: `⊤` is not immediate over a
proper `S`.) -/
theorem henselian_self_immediate {S : LRV.Substructure M} (h : IsHenselianVF S) :
    ∃ T : LRV.Substructure M, M6L33.Immediate S T ∧ IsHenselianVF T :=
  ⟨S, ⟨le_rfl, fun _ hx _ => hx⟩, h⟩

/-- `Immediate` is transitive. -/
theorem immediate_trans {S T U : LRV.Substructure M} (hST : M6L33.Immediate S T)
    (hTU : M6L33.Immediate T U) : M6L33.Immediate S U :=
  ⟨hST.1.trans hTU.1, fun x hx hxrv => hST.2 x (hTU.2 x hx hxrv) hxrv⟩

end Existence

/-! ### The universal property of the henselization, at the frozen encoding -/

/-- **Lifting an embedding along the henselization** (the universal property of the henselization):
if `T ⊇ S` is an immediate henselian extension and `f : S ↪ N` is a monomorphism into a model `N`
of `ACVF` (every model of `ACVF` is henselian), then `f` extends to a monomorphism `T ↪ N`.

In valuation theory this is uniqueness of the henselization inside the henselian field `N`
(Engler–Prestel, *Valued Fields*, Theorem 5.1.2: `Ş^h` is the minimal henselian extension and embeds
uniquely into every henselian extension).  It is exactly what the paper obtains without comment in
"so we may assume that `(VF(Š), O(Š))` is henselian"; the paper's own justification covers only the
`Standing`-invariance, which is `M6L33.standing_of_immediate`.  Stated as a named input: valuation
theory, not Marker. -/
def ImmediateLift : Prop :=
  ∀ (P : Type) [LRV.Structure P] [P ⊨ Axioms.ACVF]
    (Q : Type) [LRV.Structure Q] [Q ⊨ Axioms.ACVF]
    (S T : LRV.Substructure P) (f : S ↪[LRV] Q)
    (himm : M6L33.Immediate S T), IsHenselianVF T →
      ∃ g : T ↪[LRV] Q, ∀ x : S, g ⟨(x : P), himm.1 x.2⟩ = f x

/-! ### Assembly: `OneStepVFP` and Theorem 2.3 -/

/-- **The henselization step of Proposition 3.9's proof**, from the two named inputs: existence of
the henselization (`HenselizationExists`) and its universal property (`ImmediateLift`).  The
conclusion is `M6L33.HenselizationStep` at `P := IsHenselianVF`. -/
theorem henselizationStep_of_exists
    (hE : ∀ (P : Type) [LRV.Structure P] [P ⊨ Axioms.ACVF], HenselizationExists P)
    (hL : ImmediateLift) :
    ∀ (P Q : Type) [LRV.Structure P] [LRV.Structure Q] [P ⊨ Axioms.ACVF] [Q ⊨ Axioms.ACVF],
      M6L33.HenselizationStep (M := P) (N := Q) (fun S => IsHenselianVF S) := by
  intro P Q _instP _instQ _hP _hQ S f
  obtain ⟨T, himm, hhen⟩ := hE P S
  obtain ⟨g, hg⟩ := hL P Q S T f himm hhen
  exact ⟨T, g, himm.1, hg, himm, hhen⟩

/-- **The frozen one-step `Assembly.OneStepVFP` (Lemmas 3.4–3.8) from the henselization inputs and
the one-element step at henselian domains.**  The hypothesis `hOne` is the paper's Lemmas 3.4–3.8 in
the form they are stated in (`(VF(Š), O(Š))` henselian); this theorem removes the henselianity from
the statement of the frozen obligation. -/
theorem oneStepVFP_of_hens
    (hE : ∀ (P : Type) [LRV.Structure P] [P ⊨ Axioms.ACVF], HenselizationExists P)
    (hL : ImmediateLift)
    (hOne : ∀ (P Q : Type) [LRV.Structure P] [LRV.Structure Q] [P ⊨ Axioms.ACVF] [Q ⊨ Axioms.ACVF]
      (S : LRV.Substructure P) (f : S ↪[LRV] Q), Assembly.Standing S → IsHenselianVF S →
      ∀ m : P, iVF m →
        ∃ (T : LRV.Substructure P) (g : T ↪[LRV] Q) (hST : S ≤ T),
          (∀ x : S, g ⟨(x : P), hST x.2⟩ = f x) ∧ m ∈ T ∧ Assembly.Standing T) :
    M7Paper.OneStepSizeFree := by
  intro P Q _instP _instQ _hP _hQ
  exact M6L33.oneStepVFP_of_hensel
    (P := fun S => IsHenselianVF (M := P) S)
    (fun S f hStand hhen m hm => hOne P Q S f hStand hhen m hm)
    (henselizationStep_of_exists hE hL P Q)

/-- **Theorem 2.3 (`qe:acvf`) with the henselization inputs supplying the one-step.**  The three
remaining hypotheses are the paper's: Shoenfield's test at the paper's pairs (Marker content, quoted
by the author ruling), `M7Paper.PrepStepSize` (Lemma 3.3 at the size hypothesis), and the two
henselization inputs together with Lemmas 3.4–3.8 at henselian domains. -/
theorem paper_theorem_2_3_sat_of_hens
    (hShoen : M7Paper.ShoenfieldTestSat) (hPrep : M7Paper.PrepStepSize)
    (hE : ∀ (P : Type) [LRV.Structure P] [P ⊨ Axioms.ACVF], HenselizationExists P)
    (hL : ImmediateLift)
    (hOne : ∀ (P Q : Type) [LRV.Structure P] [LRV.Structure Q] [P ⊨ Axioms.ACVF] [Q ⊨ Axioms.ACVF]
      (S : LRV.Substructure P) (f : S ↪[LRV] Q), Assembly.Standing S → IsHenselianVF S →
      ∀ m : P, iVF m →
        ∃ (T : LRV.Substructure P) (g : T ↪[LRV] Q) (hST : S ≤ T),
          (∀ x : S, g ⟨(x : P), hST x.2⟩ = f x) ∧ m ∈ T ∧ Assembly.Standing T) :
    HasQE Axioms.ACVF :=
  M7Paper.paper_theorem_2_3_sat hShoen hPrep (oneStepVFP_of_hens hE hL hOne)

/-! ### The sort discipline the henselianization argument needs

`Immediate` is stated on `RV`-elements, and `KEqTop` on units (`Kˣ`).  To pass between the two one
needs the encoding's axiom `sdUnits` (`Kˣ ⊆ RV`); the tree did not have it as a lemma. -/

section SortDisc

variable [hM : M ⊨ Axioms.ACVF]

theorem mem_ACVF_sdUnits : Axioms.sdUnits ∈ Axioms.ACVF :=
  Transfer.mem_ACVF_sortClosure (by simp [Axioms.sortClosure, Axioms.ofList])

/-- `Kˣ ⊆ RV` — the axiom `sdUnits` of the encoding read off a model. -/
theorem units_rv_mem {x : M} (hx : iUnits x) : iRV x := by
  have hreal : M ⊨ Axioms.sdUnits :=
    Theory.realize_sentence_of_mem (T := Axioms.ACVF) mem_ACVF_sdUnits
  have h1 : (M ⊨ Axioms.sdUnits) ↔ ∀ xs : Fin 1 → M,
      (LRV.pUnits (LRV.tv 0 (by decide)) ⟹ LRV.pRVsort (LRV.tv 0 (by decide))).Realize
        (default : Empty → M) xs := by
    simp only [Axioms.sdUnits, LRV.allOne]
    exact FirstOrder.Language.BoundedFormula.realize_alls
  have h := (h1.mp hreal) ![x]
  rw [FirstOrder.Language.BoundedFormula.realize_imp] at h
  refine (SortCover.pRVsort_realize_at x).mp (h ?_)
  rw [Transfer.pUnits_realize]
  have hval : Term.realize (Sum.elim (default : Empty → M) ![x])
      (LRV.tv 0 (by decide) : LRV.Tm 1) = x := by
    simp [LRV.tv]
  rw [hval]
  exact hx

/-- `K = Kˣ ∪ {0} ⊆ RV`. -/
theorem inK_rv_mem {x : M} (hx : iUnits x ∨ x = iRVZero) : iRV x := by
  rcases hx with hx | hx
  · exact units_rv_mem hx
  · rw [hx]; exact Transfer.rv_zero_mem (M := M) hM

/-- `Immediate` extensions preserve the units in both directions (a unit is an `RV`-element). -/
theorem units_mem_iff_of_immediate {S T : LRV.Substructure M} (h : M6L33.Immediate S T)
    {x : M} (hx : iUnits x) : x ∈ S ↔ x ∈ T :=
  ⟨fun hS => h.1 hS, fun hT => h.2 x hT (units_rv_mem hx)⟩

/-- **`KEqTop` is `Immediate`-invariant in both directions** — so the henselization preserves the
`K(T) = K(M)` half of `Standing` exactly (the base's `standing_of_immediate` gives one direction
through `GammaDivisible`; this is the unit-level statement). -/
theorem KEqTop_iff_of_immediate {S T : LRV.Substructure M} (h : M6L33.Immediate S T) :
    Assembly.KEqTop S ↔ Assembly.KEqTop T := by
  constructor
  · intro hS x hx
    exact h.1 (hS x hx)
  · intro hT x hx
    exact (units_mem_iff_of_immediate h hx).mpr (hT x hx)

/-- **`Γ(N)` is divisible, in the shape `GammaDivisible` consumes** — the usable form of
`StandingTree.standing_top`'s second component, for the directions that need the divisibility of the
value group of a model (the Γ-room / Hahn input, the one-step's hull): for every `t ∈ RV(N)`,
`t ≠ 0`, and `n ≥ 1` there are `u ∈ RV(N)`, `u ≠ 0` and a unit `c` with `uⁿ = t · c`. -/
theorem gamma_divisible_model {t : M} (ht : iRV t) (ht0 : t ≠ iRVZero) (n : ℕ) (hn : 1 ≤ n) :
    ∃ u c : M, iRV u ∧ u ≠ iRVZero ∧ iUnits c ∧
      Assembly.rvPow u n = iRVMul t c := by
  obtain ⟨u, c, -, hu, hu0, -, hc, heq⟩ :=
    (StandingTree.standing_top (M := M)).2 t trivial ht ht0 n hn
  exact ⟨u, c, hu, hu0, hc, heq⟩

/-- **The henselization preserves `VF`-generatedness and `Standing` at once** (the paper's reduction
of Proposition 3.9 to the henselian case, in the frozen encoding). -/
theorem vfGen_standing_hens (hE : HenselizationExists M) (S : LRV.Substructure M)
    (hgen : Assembly.IsVFGen S) (hStand : Assembly.Standing S) :
    ∃ T : LRV.Substructure M, S ≤ T ∧ IsHenselianVF T ∧ Assembly.IsVFGen T ∧
      Assembly.Standing T := by
  obtain ⟨T, himm, hhen⟩ := hE S
  exact ⟨T, himm.1, hhen, vfGen_of_immediate hgen himm,
    M6L33.standing_of_immediate himm hStand⟩

end SortDisc

end M7Hens

end Milestone0
end SpecialTransformations

#print axioms SpecialTransformations.Milestone0.M7Hens.Mvf_subset_Ovf
#print axioms SpecialTransformations.Milestone0.M7Hens.vfEval_mem
#print axioms SpecialTransformations.Milestone0.M7Hens.henselian_congr
#print axioms SpecialTransformations.Milestone0.M7Hens.rv_eq_of_henselization
#print axioms SpecialTransformations.Milestone0.M7Hens.standing_hens
#print axioms SpecialTransformations.Milestone0.M7Hens.vfGen_of_immediate
#print axioms SpecialTransformations.Milestone0.M7Hens.henselian_self_immediate
#print axioms SpecialTransformations.Milestone0.M7Hens.immediate_trans
#print axioms SpecialTransformations.Milestone0.M7Hens.henselizationStep_of_exists
#print axioms SpecialTransformations.Milestone0.M7Hens.oneStepVFP_of_hens
#print axioms SpecialTransformations.Milestone0.M7Hens.paper_theorem_2_3_sat_of_hens
#print axioms SpecialTransformations.Milestone0.M7Hens.units_rv_mem
#print axioms SpecialTransformations.Milestone0.M7Hens.inK_rv_mem
#print axioms SpecialTransformations.Milestone0.M7Hens.KEqTop_iff_of_immediate
#print axioms SpecialTransformations.Milestone0.M7Hens.gamma_divisible_model
#print axioms SpecialTransformations.Milestone0.M7Hens.vfGen_standing_hens
