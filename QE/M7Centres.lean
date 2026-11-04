/-
# §3's centre statements (`effectiveness` 720, `algebraic:balls:definable:centers` 738), repaired

*Swarm `smw1qqehg`, member m7, direction d4.*

## What is wrong with the frozen statements

`QE/Sec3_sat.lean` transcribes "`𝓑` has centers" (Yin, QE:ACVF:min, **Definition 4.14**, quoted
verbatim in the docstring of `Sec3.IsSetOfCenters`) as

    Sec3.IsSetOfCenters 𝓑 C  :=  ∀ b ∈ 𝓑, ∃! c : M, c ∈ C ∧ c ∈ b ,

and then states

* `SP.swl_effectiveness` (`QE/Sec3_sat.lean:258`, paper.tex:720, Yin 4.15): an algebraic set of
  closed balls has centres;
* `SP.swl_algebraic_balls_definable_centers` (`QE/Sec3_sat.lean:268`, paper.tex:738, Yin 4.17): if
  `S` is `(VF, Γ)`-generated and `𝓑` is an algebraic set of balls, then `𝓑` has centres definable
  over `S`.

The source does not say that.  Its words are: *"If there is a definable function `f : 𝓑 → VF` such
that `f(𝔟ᵢ) ∈ 𝔟ᵢ` for every `𝔟ᵢ` then we say that `𝓑` has centers and `f(𝓑)` is a set of centers of
`𝓑`."*  That is a **function** on the family, and nothing is required of `f(𝔟ᵢ)` with respect to the
*other* members of the family.

`isSetOfCenters_iff` below is the exact reading of the frozen form: `C` is a "set of centers"
precisely when

1. every `b ∈ 𝓑` meets `C` (this is the source's condition, with `C = f(𝓑)`), **and**
2. `C` has at most one point in each `b ∈ 𝓑` — a condition on *pairs of members* that
   Definition 4.14 never imposes.

For a family with `b₁, b₂ ⊆ b₃` and `b₁ ∩ b₂ = ∅`, condition 2 is unsatisfiable: the unique point of
`C` in `b₃` would have to be at once the unique point in `b₁` and in `b₂`
(`not_isSetOfCenters_of_branching`).  Such a family of closed balls exists in **every** model of
`Axioms.ACVF` — the machine-checked configuration `BallSec3.three_balls`
(`.ultramath/smw1kv9xm/m8/BallSec3.lean`, imported here as the pinned copy `BallSec3.lean` in this
directory): with `x` of value strictly above `v 1`, the balls `C(0, v(x·x))` and `C(x, v(x·x))` are
disjoint, nonempty, and both lie in `C(0, v 1)`.

Hence, in the tree's own vocabulary (`Sec3.IsAlgebraicSetOfBalls`, `IsClosedBall`,
`Sec3.HasCenters`):

* `exists_branching_closed_balls` : there is `𝓑` with `Sec3.IsAlgebraicSetOfBalls 𝓑`, all members
  `IsClosedBall`, and `¬ Sec3.HasCenters 𝓑`;
* `not_swl_effectiveness` : the body of the frozen `SP.swl_effectiveness` is **false**;
* `conclusion_of_738_fails` : for that `𝓑` and **every** `S : SP M`, the conclusion of the frozen
  `SP.swl_algebraic_balls_definable_centers` fails.

## The repairs delivered here

* **Definition 4.14, corrected**: `HasCenterFun` (a function `f : 𝓑 → VF` with `f b ∈ b`) and its
  parameter-relative form `HasCenterFunOver S` (`f b ∈ b` and `f b ∈ dcl S`).
  The frozen notion implies the former (`hasCenterFun_of_hasCenters`); the converse fails (the
  refutation).  So the repair is a weakening, and what the frozen form added is exactly condition 2
  above.
* **`effectiveness` (720), repaired and proved**: `hasCenterFun_of_isClosedBall` — every algebraic
  set of closed balls has a centre *function*, over any model of `Axioms.ACVF`.  This is Yin 4.15 in
  the source's own form; its content, once definability of `f` is not required, is only that closed
  balls are nonempty, which is where the axioms enter (`isClosedBall_nonempty`, via
  `BallSec3.centre_mem`: a closed ball contains its centre).
* **The form the paper's §7–§10 actually use, proved**: in `fun:quo:rep` (paper.tex:777) Yin applies
  `effectiveness` to the balls `𝔟_D ⊆ D` sitting in distinct `G`-cosets, which are *pairwise
  disjoint*.  There the frozen `∃!`-coding carries no extra condition, so the frozen statement is the
  source's and is provable: `hasCenters_of_pairwiseDisjoint` (any family) and
  `hasCenters_of_pairwiseDisjoint_closed` (algebraic sets of closed balls).  The applications are
  therefore unaffected by the defect, and this is the form to cite downstream.
* **738, repaired**: `hasCenterFunOver_of_presentation` — if the family is *presented* by centres
  and radii and the centres are definable over `S`, then the centre function is definable over `S`.
  This shows where 738's content must lie: the paper's "definable set of balls" is a definable
  **family**, and its proof *finds* a definable point in each `𝔟ᵢ` by averaging the roots of the
  polynomials of a formula defining `⋃𝓑` (qe.tex, proof of Lemma 4.15: *"Let `bᵢ` be the average of
  `𝔟ᵢ ∩ R`"*), whereas the frozen hypothesis `Sec3.IsDefinableSetOfBalls` records only that each
  member is definable **as a set** — which fixes no centre and supplies no averaging set.  The
  residue — that an algebraic set of balls admits such a presentation (Yin's root-averaging
  argument) — is **not** formalised here and is not claimed.

## Universe note

The definitions, the characterisation and the branching obstruction are universe-polymorphic.  The
closed-ball results are stated at `M : Type` (universe 0) because they rest on the term-level
arithmetic of `BallSec3` (the encoding's `Fun`-symbols are evaluated through `Matrix` vectors whose
elaboration is pinned to `Type`); the frozen §3 statements themselves are universe-polymorphic, so
this is a limit of the imported ball geometry, not of the mathematics.

Compiled with (`Sec3Sat`, `BallSec3` oleans present in `.scratch2/sec3/`):

    cd .scratch2/sec3 && LEAN_PATH=$PWD:$LEAN_PATH lean M7Centres.lean
-/
import Sec3Sat
import BallSec3

open FirstOrder FirstOrder.Language
open scoped FirstOrder

namespace SpecialTransformations
namespace Milestone0
namespace Sec3Centres

/-! ## 1. Yin's Definition 4.14, in the form the source states it -/

/-- **`𝓑` has centres**, Yin QE:ACVF:min Definition 4.14, in the source's own form: *"If there is a
definable function `f : 𝓑 → VF` such that `f(𝔟ᵢ) ∈ 𝔟ᵢ` for every `𝔟ᵢ` then we say that `𝓑` has
centers"*.  Definability of `f` is recorded separately, in `HasCenterFunOver`; this predicate is the
bare choice condition, which is what `Sec3.IsSetOfCenters` should have been. -/
def HasCenterFun {M : Type*} (𝓑 : Set (Set M)) : Prop :=
  ∃ f : ↥𝓑 → M, ∀ b : ↥𝓑, f b ∈ (b : Set M)

/-- **`f` is a centre function for `𝓑`, definable over `S`**: `f b ∈ b` for every member, and every
value of `f` lies in the definable closure of the parameters `S` — the conclusion of Yin 4.17 as the
paper states it ("there is a definable function `f : 𝓑 → VF`"). -/
def IsCenterFunOver {M : Type*} [LRV.Structure M] (S : SP M) (𝓑 : Set (Set M))
    (f : ↥𝓑 → M) : Prop :=
  ∀ b : ↥𝓑, f b ∈ (b : Set M) ∧ SP.dcl S (f b)

/-- **`𝓑` has centres definable over `S`** (Yin 4.17's conclusion). -/
def HasCenterFunOver {M : Type*} [LRV.Structure M] (S : SP M) (𝓑 : Set (Set M)) : Prop :=
  ∃ f : ↥𝓑 → M, IsCenterFunOver S 𝓑 f

/-- The frozen notion implies the source's: the unique point of `C` in `b` is `f b`, and nothing is
asked of it relative to the other members.  (The converse fails — `not_swl_effectiveness`.) -/
theorem hasCenterFun_of_hasCenters {M : Type*} {𝓑 : Set (Set M)}
    (h : Sec3.HasCenters 𝓑) : HasCenterFun 𝓑 := by
  obtain ⟨C, hC⟩ := h
  choose f hf using fun b : ↥𝓑 => (hC (b : Set M) b.2).exists
  exact ⟨f, fun b => (hf b).2⟩

/-- The source's condition, from nonemptiness alone. -/
theorem hasCenterFun_of_nonempty {M : Type*} {𝓑 : Set (Set M)}
    (hne : ∀ b ∈ 𝓑, b.Nonempty) : HasCenterFun 𝓑 := by
  choose f hf using fun b : ↥𝓑 => hne (b : Set M) b.2
  exact ⟨f, hf⟩

/-! ## 2. The exact content of the frozen coding

The frozen `Sec3.IsSetOfCenters 𝓑 C` is *not* the source's condition: it is the source's condition
plus "`C` has at most one point in each member".  That is the sense in which the frozen statement is
a different (and false) theorem, and it also says exactly what a repair must restore. -/

/-- **Exact reading of the frozen `IsSetOfCenters`.**  `C` is a set of centres in the frozen sense iff
(a) every member of `𝓑` meets `C`, which is the source's condition with `C = f(𝓑)`, and (b) two points
of `C` that lie in a common member of `𝓑` are equal — a condition on *pairs of members* that
Definition 4.14 does not impose. -/
theorem isSetOfCenters_iff {M : Type*} {𝓑 : Set (Set M)} {C : Set M} :
    Sec3.IsSetOfCenters 𝓑 C ↔
      (∀ b ∈ 𝓑, ∃ c, c ∈ C ∧ c ∈ b) ∧
        (∀ c ∈ C, ∀ c' ∈ C, (∃ b ∈ 𝓑, c ∈ b ∧ c' ∈ b) → c = c') := by
  constructor
  · intro h
    refine ⟨fun b hb => (h b hb).exists, ?_⟩
    intro c hc c' hc' ⟨b, hb, hcb, hcb'⟩
    exact (h b hb).unique ⟨hc, hcb⟩ ⟨hc', hcb'⟩
  · rintro ⟨hne, huniq⟩ b hb
    obtain ⟨c, hcC, hcb⟩ := hne b hb
    exact ⟨c, ⟨hcC, hcb⟩, fun c' hc' => huniq c' hc'.1 c hcC ⟨b, hb, hc'.2, hcb⟩⟩

/-- **The obstruction, in the frozen vocabulary.**  If `𝓑` contains `b₁, b₂ ⊆ b₃` with `b₁ ∩ b₂ = ∅`,
then `𝓑` has no set of centres at all: the unique point of `C` in `b₃` would be the unique point in
`b₁` and in `b₂`, and those members are disjoint.  No axiom of `ACVF` is used, so no strengthening of
the frozen theory repairs it. -/
theorem not_isSetOfCenters_of_branching {M : Type*} {b₁ b₂ b₃ C : Set M}
    (h₁₃ : b₁ ⊆ b₃) (h₂₃ : b₂ ⊆ b₃) (hd : b₁ ∩ b₂ = ∅) :
    ¬ Sec3.IsSetOfCenters ({b₁, b₂, b₃} : Set (Set M)) C := by
  intro hC
  obtain ⟨c₁, ⟨hc₁C, hc₁₁⟩, -⟩ := hC b₁ (by simp)
  obtain ⟨c₂, ⟨hc₂C, hc₂₂⟩, -⟩ := hC b₂ (by simp)
  obtain ⟨c₃, ⟨-, hc₃₃⟩, huniq⟩ := hC b₃ (by simp)
  have e₁ : c₁ = c₃ := huniq c₁ ⟨hc₁C, h₁₃ hc₁₁⟩
  have e₂ : c₂ = c₃ := huniq c₂ ⟨hc₂C, h₂₃ hc₂₂⟩
  have hc₁₂ : c₁ ∈ b₂ := e₁.trans e₂.symm ▸ hc₂₂
  have hmem : c₁ ∈ b₁ ∩ b₂ := ⟨hc₁₁, hc₁₂⟩
  rw [hd] at hmem
  exact hmem

/-! ## 3. The frozen `effectiveness` (720) is false, in the tree's own vocabulary -/

/-- **A counterexample to the frozen `SP.swl_effectiveness` in every model of `Axioms.ACVF`.**  The
three balls `C(0, v 1) ⊇ C(0, v(x·x))`, `C(x, v(x·x))` of `BallSec3.three_balls` form an algebraic set
of closed balls with no set of centres in the frozen sense.  (`three_balls` is the machine-checked
configuration of `.ultramath/smw1kv9xm/m8/BallSec3.lean`; everything else here is proved anew in the
tree's vocabulary `Sec3.IsAlgebraicSetOfBalls` / `IsClosedBall` / `Sec3.HasCenters`.) -/
theorem exists_branching_closed_balls {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) :
    ∃ 𝓑 : Set (Set M), Sec3.IsAlgebraicSetOfBalls 𝓑 ∧
      (∀ b ∈ 𝓑, IsClosedBall b) ∧ ¬ Sec3.HasCenters 𝓑 := by
  obtain ⟨b₁, b₂, b₃, hc₁, hc₂, hc₃, -, -, h₁₃, h₂₃, hd⟩ := BallSec3.three_balls hM
  refine ⟨{b₁, b₂, b₃}, ⟨((Set.finite_singleton b₃).insert b₂).insert b₁, ?_⟩, ?_, ?_⟩
  · intro b hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
    rcases hb with rfl | rfl | rfl
    · exact Or.inr (Or.inl hc₁)
    · exact Or.inr (Or.inl hc₂)
    · exact Or.inr (Or.inl hc₃)
  · intro b hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
    rcases hb with rfl | rfl | rfl
    · exact hc₁
    · exact hc₂
    · exact hc₃
  · rintro ⟨C, hC⟩
    exact not_isSetOfCenters_of_branching h₁₃ h₂₃ hd hC

/-- **The frozen `SP.swl_effectiveness` is refutable** (`QE/Sec3_sat.lean:258`, paper.tex:720): its
body, as a universally quantified statement over a model of `ACVF`, is false.  Repair:
`hasCenterFun_of_isClosedBall` (Definition 4.14's function form) and
`hasCenters_of_pairwiseDisjoint_closed` (the pairwise-disjoint form used in §7–§10).

At a monster model this is the refutation of the frozen statement itself: apply it to `𝕄.isModel`.
(The statement is made over an arbitrary model of `Axioms.ACVF` at `M : Type` because the imported
ball geometry `BallSec3` is at universe 0 — see the universe note at the top.) -/
theorem not_swl_effectiveness {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) :
    ¬ (∀ 𝓑 : Set (Set M), Sec3.IsAlgebraicSetOfBalls 𝓑 →
        (∀ b ∈ 𝓑, IsClosedBall b) → Sec3.HasCenters 𝓑) := by
  intro h
  obtain ⟨𝓑, halg, hc, hno⟩ := exists_branching_closed_balls hM
  exact hno (h 𝓑 halg hc)

/-! ## 4. `effectiveness` (720), repaired and proved

Yin 4.15, in the source's form: an algebraic set of closed balls has a centre **function**.  Over a
model of `ACVF` this is exactly the statement that closed balls are nonempty (their centre is in
them), because nothing is required of `f b` in the other members of the family. -/

/-- **Every closed ball is nonempty**, from the encoding's axioms: it contains its centre
(`BallSec3.centre_mem`, whose proof extracts the ultrametric and `∞`-is-top axioms). -/
theorem isClosedBall_nonempty {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {b : Set M}
    (hb : IsClosedBall b) : b.Nonempty := by
  obtain ⟨a, r, ha, hr, hr0, rfl⟩ := hb
  exact ⟨a, BallSec3.centre_mem hM ha hr hr0⟩

/-- **`effectiveness` (paper.tex:720), corrected to Definition 4.14 and proved**: an algebraic set of
closed balls has centres, i.e. a function `f` with `f b ∈ b` for every member.

This is the repair of `SP.swl_effectiveness`: the conclusion is the source's function form
(`HasCenterFun`) instead of the frozen `Sec3.HasCenters`, which additionally demands that no ball
contain two chosen points (`isSetOfCenters_iff`) and is refuted by `not_swl_effectiveness`. -/
theorem hasCenterFun_of_isClosedBall {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF)
    {𝓑 : Set (Set M)} (hc : ∀ b ∈ 𝓑, IsClosedBall b) : HasCenterFun 𝓑 :=
  hasCenterFun_of_nonempty fun b hb => isClosedBall_nonempty hM (hc b hb)

/-! ### The case the paper's applications use: pairwise disjoint closed balls

`fun:quo:rep` (paper.tex:777, cited by §7–§10) applies `effectiveness` to the balls `𝔟_D ⊆ D`, one
inside each `G`-coset `D`; distinct cosets are disjoint, so that family is pairwise disjoint.  There
the frozen `∃!`-coding carries no extra condition (`isSetOfCenters_iff`: two chosen points lying in a
common member would have to be equal, and no member meets two of them), so the frozen statement *is*
the source's and is provable.  This is the repaired form to cite downstream. -/

/-- **Frozen `HasCenters` for a pairwise disjoint family of nonempty sets**: one chosen point per
member meets each member exactly once, because no member contains the point chosen for another. -/
theorem hasCenters_of_pairwiseDisjoint {M : Type*} {𝓑 : Set (Set M)}
    (hne : ∀ b ∈ 𝓑, b.Nonempty)
    (hd : ∀ b ∈ 𝓑, ∀ b' ∈ 𝓑, b ≠ b' → Disjoint b b') : Sec3.HasCenters 𝓑 := by
  choose f hf using fun b : ↥𝓑 => hne (b : Set M) b.2
  refine ⟨Set.range f, ?_⟩
  intro b hb
  have hmem : f ⟨b, hb⟩ ∈ b := hf ⟨b, hb⟩
  refine ⟨f ⟨b, hb⟩, ⟨⟨⟨b, hb⟩, rfl⟩, hmem⟩, ?_⟩
  rintro c ⟨⟨⟨b', hb'⟩, rfl⟩, hcb⟩
  by_cases hbb' : b' = b
  · subst hbb'; rfl
  · exfalso
    exact (Set.disjoint_left.mp (hd b' hb' b hb hbb') (hf ⟨b', hb'⟩)) hcb

/-- **`effectiveness` (720) in the form the paper uses downstream**: an algebraic set of closed balls
that is pairwise disjoint has centres in the frozen sense. -/
theorem hasCenters_of_pairwiseDisjoint_closed {M : Type} [LRV.Structure M]
    (hM : M ⊨ Axioms.ACVF) {𝓑 : Set (Set M)} (hc : ∀ b ∈ 𝓑, IsClosedBall b)
    (hd : ∀ b ∈ 𝓑, ∀ b' ∈ 𝓑, b ≠ b' → Disjoint b b') : Sec3.HasCenters 𝓑 :=
  hasCenters_of_pairwiseDisjoint (fun b hb => isClosedBall_nonempty hM (hc b hb)) hd

/-! ## 5. `algebraic:balls:definable:centers` (738)

Two separate defects, in this order:

1. **The conclusion, as frozen, fails on a family that meets the algebraic hypothesis**: for the
   branching family of §3 no `C` whatsoever is a set of centres, for *any* parameter set `S`
   (`conclusion_of_738_fails`).  So the frozen 738 cannot be proved, whatever is done about
   definability.
2. **The hypothesis `Sec3.IsDefinableSetOfBalls S 𝓑` is not the paper's hypothesis**: the paper's
   "definable set of balls" is a definable *family*, and the proofs of 4.15/4.17 use the centres and
   radii of the members (the averaging of `𝔟ᵢ ∩ R`).  `IsDefinableSetOfBalls` records only that each
   member is definable as a *set*, which fixes no centre.  With the family presentation the statement
   is immediate (`hasCenterFunOver_of_presentation`); what remains is precisely Yin's root-averaging
   argument, which is not formalised here. -/

/-- **The conclusion of the frozen `SP.swl_algebraic_balls_definable_centers` fails for a family
meeting its algebraic hypothesis, for every parameter set `S`** (`QE/Sec3_sat.lean:268`,
paper.tex:738). -/
theorem conclusion_of_738_fails {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) :
    ∃ 𝓑 : Set (Set M), Sec3.IsAlgebraicSetOfBalls 𝓑 ∧
      ∀ S : SP M, ¬ ∃ C : Set M, Sec3.IsSetOfCenters 𝓑 C ∧ ∀ a : M, a ∈ C → SP.dcl S a := by
  obtain ⟨𝓑, halg, -, hno⟩ := exists_branching_closed_balls hM
  exact ⟨𝓑, halg, fun S h => hno ⟨h.choose, h.choose_spec.1⟩⟩

/-- **738, repaired: the family presented by its centres and radii.**

If the members of `𝓑` are the closed balls `C(c i, r i)` of a family whose centres `c i` are
definable over `S` (and `i` runs over the finite index set of the algebraic family), then the centre
function `b ↦` the centre of a presentation of `b` is definable over `S`.  This is the reading under
which Yin 4.17 is true, and it shows where its content lies: in *finding* the presentation — his
averaging argument, "let `bᵢ` be the average of `𝔟ᵢ ∩ R`" (qe.tex, proof of 4.15) — not in passing
from the presentation to the function.  `iVF`/`iRV` of the data are carried explicitly because
`SP.dcl` is a formula-level predicate; both follow from the corresponding sort in any use. -/
theorem hasCenterFunOver_of_presentation {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF)
    {S : SP M} {ι : Type} (c r : ι → M) (hc_dcl : ∀ i, SP.dcl S (c i))
    (hc_vf : ∀ i, iVF (c i)) (hr_rv : ∀ i, iRV (r i)) (hr_ne : ∀ i, r i ≠ iRVZero) :
    HasCenterFunOver S (Set.range (fun i => BallSec3.Ball (c i) (r i))) := by
  classical
  refine ⟨fun b => c (Classical.choose b.2), ?_⟩
  intro b
  have hb : (b : Set M) = BallSec3.Ball (c (Classical.choose b.2)) (r (Classical.choose b.2)) :=
    (Classical.choose_spec b.2).symm
  have hmem : c (Classical.choose b.2) ∈
      BallSec3.Ball (c (Classical.choose b.2)) (r (Classical.choose b.2)) :=
    BallSec3.centre_mem hM (hc_vf _) (hr_rv _) (hr_ne _)
  exact ⟨hb ▸ hmem, hc_dcl _⟩

#print axioms hasCenterFun_of_hasCenters
#print axioms hasCenterFun_of_nonempty
#print axioms isSetOfCenters_iff
#print axioms not_isSetOfCenters_of_branching
#print axioms exists_branching_closed_balls
#print axioms not_swl_effectiveness
#print axioms isClosedBall_nonempty
#print axioms hasCenterFun_of_isClosedBall
#print axioms hasCenters_of_pairwiseDisjoint
#print axioms hasCenters_of_pairwiseDisjoint_closed
#print axioms conclusion_of_738_fails
#print axioms hasCenterFunOver_of_presentation

end Sec3Centres
end Milestone0
end SpecialTransformations
