module

/-
Section 3 of the paper over a **monster model**: the statements that need saturation, frozen.

`QE/Sec3_frozen.lean` freezes the parameter discipline (`SP`, a sorted pair of tuples), `acl`,
`dcl` and five of §3's statements, over an arbitrary model `M ⊨ ACVF`.  The remaining items of
§3 are arguments about the monster model (realize the type of a conjugate, move it by an
automorphism, ...), so they are stated here over `Sat.MonsterACVF` of
`Milestone0/Saturation.lean`, in the shape the author ruled for (`κ`-saturation and strong
`κ`-homogeneity as genuine notions, `Milestone0/DECISION.md`).

Stated and frozen here:

* `swl_alg_ind_image`  — paper `alg:ind:imag`;
* `swl_average_zero_rv_not_constant` — paper `average:0:rv:not:constant`
  (Yin, QE:ACVF:min, Lemma 4.9);
* `swl_ball_proper_sub_center` — paper `ball:proper:sub:center`
  (whose proof the paper cites from Yin, QE:ACVF:min, Lemma 4.16);
* `swl_dcl_to_ac` — paper `dcl:to:ac`, with `Sec3.VFGen` for `VF(S)(ā)` and `IsAlgebraic` for
  membership in `VF(S)(ā)^{alg}`;
* `swl_effectiveness` — paper `effectiveness` (QE:ACVF:min 4.15), with `Sec3.HasCenters`;
* `swl_algebraic_balls_definable_centers` — paper `algebraic:balls:definable:centers`
  (QE:ACVF:min 4.17), with centres definable over `S`;
* `swl_rv_effectiveness` — Yin, QE:ACVF:min Lemma 4.16 (the fact behind the paper's
  `ball:proper:sub:center`): an `rv`-ball with a definable proper subset has a definable point.

Still not stated, with the exact missing development:

* `inf:RV:def:gam` — needs the `Γ`-sort and `vrv`, i.e. the three-sorted expansion `LRVΓ` of
  `Encoding.lean` Part 4, and a monster model *of the expansion* (`Sat.MonsterModel LRVΓ
  Axioms.ACVF00Γ` is available in principle, but the `Γ`-side vocabulary — `pMemGamma`, the
  interpretation of `gVrv`, `Γ(S)`, `vrv^{-1}(γ)` — is not built, and the statement is about
  definable subsets of `RV` together with their `Γ`-fibres).
* `aclS:model` — needs `Γ(acl(S))` nontrivial and the modelhood of the substructure `acl(S)` in
  `ACVF_S(0,0)`: `Encoding.lean` Part 5 has the theory `SubstructureTheory.ACVF_S` and the atomic
  diagram, but there is no interpretation of a definable-closure set as an `LRV.Substructure`, and
  no relativized satisfaction for it.

Check this file with (`.scratch2/sec3/` holds the oleans):

    cp Milestone0/Encoding.lean .scratch2/sec3/Enc.lean   # once
    cd .scratch2/sec3 && LEAN_PATH=$PWD:$LEAN_PATH lean -o Enc.olean Enc.lean
    cp ../../Milestone0/Saturation.lean Sat.lean && LEAN_PATH=$PWD:$LEAN_PATH lean -o Sat.olean Sat.lean
    cp ../../QE/Sec3_frozen.lean Sec3Frozen.lean && LEAN_PATH=$PWD:$LEAN_PATH lean -o Sec3Frozen.olean Sec3Frozen.lean
    cp ../../QE/Sec3_sat.lean Sec3Sat.lean && LEAN_PATH=$PWD:$LEAN_PATH lean Sec3Sat.lean

The `sorry`s are deliberate: these are *frozen targets*.  The paper cites `average:…` from
QE:ACVF:min 4.9 and `ball:proper:sub:center` from 4.16, so their proofs are external unless
re-proved here; `alg:ind:imag` has a printed proof (from exchange) and should be proved.
-/
public import Sat
public import Sec3Frozen

@[expose] public section

open FirstOrder FirstOrder.Language
open scoped FirstOrder

namespace SpecialTransformations.Milestone0
open LRV

namespace SP

variable {M : Type*} [LRV.Structure M]

/-- The interpretation of `0` of the `VF`-sort.  (`Milestone0/Encoding.lean` names the two `RV`
constants `iRVOne`/`iRVZero` but has no name for this one.) -/
def iVFZero : M := FirstOrder.Language.Structure.funMap (L := LRV) Fn.vfZero fun i => i.elim0

/-- The sum of a list of `VF`-elements, in the ring of the `VF`-sort.  (The `Field` structure on
`{x // iVF x}` is built in `QE/Assembly_val.lean`, not in `Encoding.lean`, so the average lemma
below is stated with this explicit fold rather than with `Finset.sum`.) -/
def sumVF : List M → M
  | [] => iVFZero
  | a :: l => iVFAdd a (sumVF l)

variable (𝕄 : Sat.MonsterACVF)

/-- **`alg:ind:imag`** (paper §3, corollary of `exchange`): if `a ∈ VF` is not algebraic over the
empty set, then `a` is not algebraic over any single `RV`-element.  The paper's proof: if
`a ∈ acl(t)`, then `a ∈ acl(b)` for every `b` in the `rv`-fibre of `t`; exchange then gives
`b ∈ acl(a)` for all of them, which is impossible.  Stated here for the monster model, because
the proof moves a conjugate of `b` by an automorphism. -/
theorem swl_alg_ind_image (a t : 𝕄.M) (ha : iVF a) (ht : iRV t)
    (h : ¬ acl (base (M := 𝕄.M)) a) : ¬ acl (singleRV t ht) a := by
  sorry

/-- The conclusion the first transcription of `average:0:rv:not:constant` froze is *unsatisfiable*
given its own hypothesis: it asked, in addition to `vv(c_i - c_j) = α`, that `rv (c i) ≠ rv (c j)`,
while the legacy `hsame` transcription says all `rv (c i)` agree. This is a
transcription error: Lemma 3.8 assumes equal valuations, not equal RV classes.
Its conclusion is correct; see the checked port in `Section3/Average.lean`.
-/
theorem swl_average_conclusion_unsat {k : ℕ} (hk0 : 0 < k) (c : Fin k → 𝕄.M)
    (hsame : ∀ i, iRv (c i) = iRv (c ⟨0, hk0⟩)) :
    ¬ ∃ i j : Fin k, i ≠ j ∧
      iRv (iVFAdd (c i) (iVFNeg (c j))) = iRv (c ⟨0, hk0⟩) ∧ iRv (c i) ≠ iRv (c j) := by
  rintro ⟨i, j, -, -, hij⟩
  exact hij (by rw [hsame i, hsame j])

/-- **`exchange`** (Yin, QE:ACVF:min, Lemma 4.3), `VF` half, over the monster model: *"For any
`a, b ∈ VF`, if `a ∈ acl(b) ∖ acl(0)` then `b ∈ acl(a)`."*

Stated here rather than in `QE/Sec3_frozen.lean` because exchange is a property of `acl` in a
**saturated** model — it is what makes `acl` a pregeometry — and the paper's §3 is over the monster
model `𝕄` (see `Milestone0/Saturation.lean`).  The frozen version in `Sec3_frozen` quantified over an
arbitrary `M ⊨ ACVF`, which is the wrong setting for this particular statement.  (The `RV` half of the
paper's lemma is not expressible in this encoding: `acl` is `VF`-sorted.) -/
theorem swl_exchange (𝕄 : Sat.MonsterACVF) (S : SP 𝕄.M) (a b : 𝕄.M)
    (ha : iVF a) (hb : iVF b) (hsmall : 𝕄.Small ↥(SP.paramSet S)) (hsmall' : 𝕄.Small ↥(SP.paramSet S ∪ {a}))
    (h : acl (S.extendVFParam b hb) a) (hne : ¬ acl S a) :
    acl (S.extendVFParam a ha) b := by
  sorry

/-- **`average:0:rv:not:constant`** (Yin, QE:ACVF:min, Lemma 4.9): if `c₁, …, c_k` (`k ≥ 2`) are
distinct elements of `VF` with the same value `α`, and their average is `0`, then two of them
satisfy `vv(c_i - c_j) = α`.  Stated as the two halves of that equality, because the encoding
axiomatises a *preorder* on `RV` and not a partial order, so `= α` is "equivalent to `α`" here:
`iLe (vv (c_i - c_j)) α` is the half the paper's proof produces, `iLe α (vv (c_i - c_j))` is the
ultrametric lower bound. -/
theorem swl_average_zero_rv_not_constant {k : ℕ} (hk : 1 < k) (hk0 : 0 < k) (c : Fin k → 𝕄.M)
    (hVF : ∀ i, iVF (c i)) (hinj : Function.Injective c)
    (hsame : ∀ i, iRv (c i) = iRv (c ⟨0, hk0⟩))
    (havg : sumVF (List.ofFn c) = iVFZero) :
    ∃ i j : Fin k, i ≠ j ∧
      iLe (iRv (iVFAdd (c i) (iVFNeg (c j)))) (iRv (c ⟨0, hk0⟩)) ∧
        iLe (iRv (c ⟨0, hk0⟩)) (iRv (iVFAdd (c i) (iVFNeg (c j)))) := by
  sorry

/-- **`ball:proper:sub:center`** (paper §3; the paper cites Yin, QE:ACVF:min, Lemma 4.16 for the
proof): a ball that contains a definable proper subset contains a definable point — a point
definable over the parameters, i.e. in the definable closure of `S`. -/
theorem swl_ball_proper_sub_center (S : SP 𝕄.M) (b D : Set 𝕄.M) (hb : IsBall b)
    (hD : SP.DefinableVF S D) (hne0 : D.Nonempty) (hsub : D ⊆ b) (hne : D ≠ b) :
    ∃ x : 𝕄.M, x ∈ b ∧ dcl S x := by
  sorry

end SP

end SpecialTransformations.Milestone0

/-! ## The remaining §3 items over the monster model

`dcl:to:ac`, `effectiveness` and `algebraic:balls:definable:centers` need vocabulary that
`Milestone0/Encoding.lean` does not have, and the way each is supplied is recorded in the
docstring of the statement:

* the `VF`-sort as a `Field`: `Sec3.VFType` below only names the type.  The `Field` instance is
  `QE/Assembly_val.lean`'s `vfFieldOfModel`, which is proved from the same axioms but in that
  file's copy of the encoding, so it cannot be imported here; the statements that need it carry
  `[Field (Sec3.VFType M)]` as an **instance argument**, to be supplied by the copy of
  `vfFieldOfModel` when the two copies of the encoding are unified.  The field laws are
  determined by `Axioms` (`vfAddAssoc`, `vfMulComm`, …), so this adds no hypothesis about the
  mathematics, only about the file layout.
* "algebraic set of balls" is quoted by the paper from Yin, QE:ACVF:min Definition 4.14.  That
  definition is now formalized here, from the quoted text in `.ultramath/refs/qe.tex`:
  `Sec3.IsAlgebraicSetOfBalls` (finitely many balls), `Sec3.IsAlgebraicBall`,
  `Sec3.AlgebraicUnion`, `Sec3.IsDefinableSetOfBalls` (the definability half),
  `Sec3.IsSetOfCenters` and `Sec3.HasCenters` (a definable choice `f : 𝓑 → VF` with
  `f b ∈ b` — the quoted definition asks only that the point lies in the ball, not that it is a
  geometric centre), and `Sec3.rvBall` for the paper's use of an `RV`-element as a ball.
* "`S` is `(VF, Γ)`-generated" is not formulable without the `Γ`-sort, so
  `swl_algebraic_balls_definable_centers` is frozen with the conclusion (centres definable over
  `S`) and the hypothesis recorded in its docstring; the `Γ`-side of `S` is only used to reduce
  `RV(S)` to `rv(VF(S))`.
-/

namespace SpecialTransformations
namespace Milestone0
open LRV

namespace Sec3

variable {M : Type*} [LRV.Structure M]

/-- The `VF`-sort as a type. -/
def VFType (M : Type*) [LRV.Structure M] : Type _ := {x : M // iVF x}

/-- A `VF`-element as an element of the `VF`-sort. -/
def vfOf (a : M) (ha : iVF a) : VFType M := ⟨a, ha⟩

variable [Field (VFType M)]

/-- **`VF(S)(ā)`**: the subfield of the `VF`-sort generated by the `VF`-part of the parameters
`ā` (the paper's `VF(S)(ā)`; `VF(S)` itself is the `n = 0` case, and is not needed separately
because the paper's statements only use the extension). -/
def VFGen (S : SP M) : Subfield (VFType M) :=
  Subfield.closure (Set.range (fun i : Fin S.n => vfOf (S.vf i) (S.vf_sorted i)))

/-- `a` is a **centre** of the closed ball `b`: `b = C(a, γ)` for a radius `γ ≠ 0`. -/
def IsCentreOf (b : Set M) (a : M) : Prop :=
  iVF a ∧ ∃ t : M, iRV t ∧ t ≠ iRVZero ∧
    b = {x | iVF x ∧ iLe t (iRv (iVFAdd x (iVFNeg a)))}

/-- An **algebraic ball** (Yin, QE:ACVF:min, Definition 4.14, quoted by the paper): a ball that is
a member of an algebraic set of balls.  "Algebraic" is the word for *finite* here, in the classical
sense of roots of polynomials: a nonzero polynomial has finitely many roots, so a set cut out by a
formula that defines a finite set is "algebraic".  This is the same finiteness that `SP.acl` uses
in its definition (`x ∈ acl S` is witnessed by a well-sorted formula with a finite solution set),
so the vocabulary is consistent across §3. -/
def IsAlgebraicBall (b : Set M) : Prop := IsBall b

/-- **Algebraic set of balls** — Yin, QE:ACVF:min, Definition 4.14, quoted verbatim by the paper
just before Lemma 4.15: *"Let `𝓑` be a definable set of balls.  If `𝓑` contains finitely many
(open, closed, rv-) balls, then `𝓑` is an algebraic set of balls."*  The definability half of the
quote is `IsDefinableSetOfBalls` below; this predicate is the finite-family-and-balls half, which
is all that the two lemmas use.

"Algebraic" is *finiteness*, generalizing the roots of a polynomial: a nonzero polynomial has
finitely many roots, so a definable set whose formula cuts out a finite set is called algebraic
(the same finiteness `SP.acl` uses; an "algebraic ball" is thus a ball in a finite definable
family, and the naming carries no closure-under-subballs claim). -/
def IsAlgebraicSetOfBalls (𝓑 : Set (Set M)) : Prop :=
  𝓑.Finite ∧ ∀ b ∈ 𝓑, IsBall b

/-- The **algebraic union of balls** `⋃ 𝓑`. -/
def AlgebraicUnion (𝓑 : Set (Set M)) : Set M := ⋃₀ 𝓑

/-- The `rv`-ball of `t`, `rv⁻¹(t) ∩ VF` — the paper's `rv`-ball, written `t` when `t ∈ RV` is
used as a ball. -/
def rvBall (t : M) : Set M := {x | iVF x ∧ iRv x = t}

/-- The family `𝓑` is **definable over** the parameters `S` (the definability half of
Definition 4.14): finitely many members, each `S`-definable as a set. -/
def IsDefinableSetOfBalls (S : SP M) (𝓑 : Set (Set M)) : Prop :=
  𝓑.Finite ∧ ∀ b ∈ 𝓑, SP.DefinableVF S b

/-- `C` is a **set of centers** for `𝓑` (Yin, QE:ACVF:min, Definition 4.14, verbatim): *"if there
is a definable function `f : 𝓑 → VF` such that `f(𝔟ᵢ) ∈ 𝔟ᵢ` for every `𝔟ᵢ` then we say that `𝓑`
has centers and `f(𝓑)` is a set of centers of `𝓑`"*.  `C` codes `f(𝓑)`: exactly one point of `C`
lies in each ball of `𝓑`, so `b ↦` that point is a function.  Note that the point need **not** be
a centre of the ball in the geometric sense — the quoted definition only asks `f(𝔟ᵢ) ∈ 𝔟ᵢ`. -/
def IsSetOfCenters (𝓑 : Set (Set M)) (C : Set M) : Prop :=
  ∀ b ∈ 𝓑, ∃! c : M, c ∈ C ∧ c ∈ b

/-- **`𝓑` has centers**: it has a set of centers. -/
def HasCenters (𝓑 : Set (Set M)) : Prop := ∃ C : Set M, IsSetOfCenters 𝓑 C

end Sec3

open Sec3 in
/-- **`dcl:to:ac`** (paper §3): if `b ∈ VF` is algebraic over the parameters `ā`, `t̄`, then `b` is
algebraic (in the field sense) over the field `VF(S)(ā)` generated by the `VF`-parameters.  The
paper's proof: a polynomial `F(X, ā)` occurring in a formula defining a finite set containing `b`
does not vanish at `b`, and `rv(F(d, ā)) = rv(F(b, ā))` for all `d` close enough to `b`, so the
formula would hold at infinitely many `d`.

`[Field (VFType M)]` is `vfFieldOfModel` of `QE/Assembly_val.lean` — see the section comment. -/
theorem SP.swl_dcl_to_ac (𝕄 : Sat.MonsterACVF) [Field (Sec3.VFType 𝕄.M)] (S : SP 𝕄.M)
    (b : 𝕄.M) (hb : iVF b) (h : acl S b) :
    IsAlgebraic ↥(VFGen S) (vfOf b hb) := by
  sorry

namespace SP

variable (𝕄 : Sat.MonsterACVF)

/-- **`effectiveness`** (paper §3; Yin, QE:ACVF:min, Lemma 4.15): an algebraic set of closed balls
has centers.  `Sec3.IsAlgebraicSetOfBalls` is Definition 4.14 of QE:ACVF:min, quoted by the
paper before this lemma. -/
theorem swl_effectiveness (𝓑 : Set (Set 𝕄.M)) (halg : Sec3.IsAlgebraicSetOfBalls 𝓑)
    (hclosed : ∀ b ∈ 𝓑, IsClosedBall b) : Sec3.HasCenters 𝓑 := by
  sorry

/-- **`algebraic:balls:definable:centers`** (paper §3; Yin, QE:ACVF:min, Lemma 4.17): if `S` is
`(VF, Γ)`-generated and `𝓑` is an algebraic set of balls, then `𝓑` has centers *definable over*
`S`.  The `(VF, Γ)`-generated hypothesis needs the `Γ`-sort and is recorded in the paper's own
words rather than as a Lean hypothesis; it is used only to ensure `RV(S) ⊆ rv(VF(S))`, so the
frozen content is the conclusion with `S`-relative definability.  `Sec3.IsDefinableSetOfBalls`
is the definability half of Definition 4.14, and `Sec3.IsSetOfCenters` is its "has centers". -/
theorem swl_algebraic_balls_definable_centers (S : SP 𝕄.M) (𝓑 : Set (Set 𝕄.M))
    (halg : Sec3.IsAlgebraicSetOfBalls 𝓑) (hdef : Sec3.IsDefinableSetOfBalls S 𝓑) :
    ∃ C : Set 𝕄.M, Sec3.IsSetOfCenters 𝓑 C ∧ ∀ a : 𝕄.M, a ∈ C → dcl S a := by
  sorry

/-- **`rv:effectiveness`** (Yin, QE:ACVF:min, Lemma 4.16, the fact behind the paper's
`ball:proper:sub:center`): if an `rv`-ball has a definable proper subset then it has a definable
point. -/
theorem swl_rv_effectiveness (S : SP 𝕄.M) (t : 𝕄.M) (ht : iRV t) (A : Set 𝕄.M)
    (hA : SP.DefinableVF S A) (hne0 : A.Nonempty) (hsub : A ⊆ Sec3.rvBall t)
    (hne : A ≠ Sec3.rvBall t) :
    ∃ c : 𝕄.M, c ∈ Sec3.rvBall t ∧ dcl S c := by
  sorry

end SP

end Milestone0
end SpecialTransformations
