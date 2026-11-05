/-
Legacy centre-selection geometry and an obstruction to the old uniqueness encoding.

The paper requires a definable function on a definable family of balls.
The choice constructions below establish point membership, and some variants
also require each selected value to lie in a specified definable closure.
They do not establish a definable graph over the original base. They therefore
do not prove Lemma 3.10 or Lemma 3.13.

The branching example correctly refutes the older requirement that one point
set meet every ball exactly once: nested balls can make that requirement
impossible. A centre function may select different points in nested balls.
Pairwise disjointness removes this geometric obstruction but does not by
itself prove definability of the choices. The paper's root-averaging argument
and parameter discipline remain required; see STATUS.md.
-/
import Sec3Sat
import BallSec3

open FirstOrder FirstOrder.Language
open scoped FirstOrder

namespace SpecialTransformations
namespace Milestone0
namespace Sec3Centres

/-! ## 1. Pointwise selections -/

/-- Bare pointwise choice of a point in each member. Definability of the
function or its graph is not part of this predicate. -/
def HasCenterFun {M : Type*} (𝓑 : Set (Set M)) : Prop :=
  ∃ f : ↥𝓑 → M, ∀ b : ↥𝓑, f b ∈ (b : Set M)

/-- Pointwise centre selection with values in dcl(S). This definition does
not include a formula for the graph of the function on the ball family. -/
def IsCenterFunOver {M : Type*} [LRV.Structure M] (S : SP M) (𝓑 : Set (Set M))
    (f : ↥𝓑 → M) : Prop :=
  ∀ b : ↥𝓑, f b ∈ (b : Set M) ∧ SP.dcl S (f b)

/-- Existence of a pointwise centre selection with values in dcl(S).
Uniform graph definability is not included. -/
def HasCenterFunOver {M : Type*} [LRV.Structure M] (S : SP M) (𝓑 : Set (Set M)) : Prop :=
  ∃ f : ↥𝓑 → M, IsCenterFunOver S 𝓑 f

/-- The legacy uniqueness condition implies bare pointwise choice. -/
theorem hasCenterFun_of_hasCenters {M : Type*} {𝓑 : Set (Set M)}
    (h : Sec3.HasCenters 𝓑) : HasCenterFun 𝓑 := by
  obtain ⟨C, hC⟩ := h
  choose f hf using fun b : ↥𝓑 => (hC (b : Set M) b.2).exists
  exact ⟨f, fun b => (hf b).2⟩

/-- Nonempty members admit a pointwise selection by classical choice. -/
theorem hasCenterFun_of_nonempty {M : Type*} {𝓑 : Set (Set M)}
    (hne : ∀ b ∈ 𝓑, b.Nonempty) : HasCenterFun 𝓑 := by
  choose f hf using fun b : ↥𝓑 => hne (b : Set M) b.2
  exact ⟨f, hf⟩

/-! ## 2. The exact point-set content of the legacy uniqueness coding -/

/-- The legacy point-set condition is exactly nonempty intersections plus
uniqueness within each member. No definability assertion occurs in this
equivalence. -/
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

/-- Branching refutes the legacy uniqueness requirement. The choice
constructions below address membership, without proving graph definability. -/
theorem not_swl_effectiveness {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) :
    ¬ (∀ 𝓑 : Set (Set M), Sec3.IsAlgebraicSetOfBalls 𝓑 →
        (∀ b ∈ 𝓑, IsClosedBall b) → Sec3.HasCenters 𝓑) := by
  intro h
  obtain ⟨𝓑, halg, hc, hno⟩ := exists_branching_closed_balls hM
  exact hno (h 𝓑 halg hc)

/-! ## 4. Choice-based centre selections
These are geometric membership results, not the paper's definable-centre theorem. -/

/-- **Every closed ball is nonempty**, from the encoding's axioms: it contains its centre
(`BallSec3.centre_mem`, whose proof extracts the ultrametric and `∞`-is-top axioms). -/
theorem isClosedBall_nonempty {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {b : Set M}
    (hb : IsClosedBall b) : b.Nonempty := by
  obtain ⟨a, r, ha, hr, hr0, rfl⟩ := hb
  exact ⟨a, BallSec3.centre_mem hM ha hr hr0⟩

/-- Closed balls admit a pointwise centre selection by classical choice.
No base-relative definability of this function is proved here. -/
theorem hasCenterFun_of_isClosedBall {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF)
    {𝓑 : Set (Set M)} (hc : ∀ b ∈ 𝓑, IsClosedBall b) : HasCenterFun 𝓑 :=
  hasCenterFun_of_nonempty fun b hb => isClosedBall_nonempty hM (hc b hb)

/-! ### Pairwise disjoint families
Disjointness gives geometric uniqueness for the chosen point set. Definability
of that set and of the selection function remains a separate obligation. -/

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

/-- Pairwise disjoint closed balls admit a choice-based point set with
one point in each ball. There is no graph-definability conclusion. -/
theorem hasCenters_of_pairwiseDisjoint_closed {M : Type} [LRV.Structure M]
    (hM : M ⊨ Axioms.ACVF) {𝓑 : Set (Set M)} (hc : ∀ b ∈ 𝓑, IsClosedBall b)
    (hd : ∀ b ∈ 𝓑, ∀ b' ∈ 𝓑, b ≠ b' → Disjoint b b') : Sec3.HasCenters 𝓑 :=
  hasCenters_of_pairwiseDisjoint (fun b hb => isClosedBall_nonempty hM (hc b hb)) hd

/-! ## 5. Conditional pointwise selections
The presentation hypothesis below already supplies the centres and requires
their individual values to lie in dcl(S). It does not derive the paper's
uniformly definable centre function from an arbitrary algebraic ball family. -/

/-- **The conclusion of the frozen `SP.swl_algebraic_balls_definable_centers` fails for a family
meeting its algebraic hypothesis, for every parameter set `S`** (`QE/Sec3_sat.lean:268`,
paper.tex:738). -/
theorem conclusion_of_738_fails {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) :
    ∃ 𝓑 : Set (Set M), Sec3.IsAlgebraicSetOfBalls 𝓑 ∧
      ∀ S : SP M, ¬ ∃ C : Set M, Sec3.IsSetOfCenters 𝓑 C ∧ ∀ a : M, a ∈ C → SP.dcl S a := by
  obtain ⟨𝓑, halg, -, hno⟩ := exists_branching_closed_balls hM
  exact ⟨𝓑, halg, fun S h => hno ⟨h.choose, h.choose_spec.1⟩⟩

/-- A supplied presentation with pointwise dcl(S) centres yields the
corresponding pointwise selection. This does not construct a defining formula
for its graph or prove existence of such a presentation. -/
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
