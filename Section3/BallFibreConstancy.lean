module

public import Section3.MixedRootFree

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.BallFibreConstancy
open MixedPolynomialSyntax
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {m : ℕ}

def graph (f : VFType (M := M) → Set (Fin m → M)) : Set (Fin (m+1) → M) :=
  {z | ∃ x : VFType (M := M), x.val = z 0 ∧ Fin.tail z ∈ f x}

theorem mem_graph (f : VFType (M := M) → Set (Fin m → M))
    (x : VFType (M := M)) (ys : Fin m → M) :
    Fin.cons x.val ys ∈ graph f ↔ ys ∈ f x := by
  constructor
  · rintro ⟨x', he, hmem⟩
    have he' : x' = x := Subtype.ext he
    simpa only [he', Fin.tail_cons] using hmem
  · intro h; exact ⟨x, rfl, by simpa only [Fin.tail_cons] using h⟩

/-- Uniformly in all RV outputs, only finitely many classes in any
partition into balls can have nonconstant set-valued fibres. -/
theorem finite_exceptions (S : Set M)
    (f : VFType (M := M) → Set (Fin m → M))
    (hf : ∀ x ys, ys ∈ f x → ∀ i, iRV (ys i))
    (hgraph : DefinableOver S contextSort (graph f))
    {Q : Type} (q : VFType (M := M) → Q)
    {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)
    (hq : ∀ d : Q, ∃ a, (∃ r : Balls.OpenRadius Γ, {x | q x = d} = Balls.openDisc v a r) ∨
      (∃ r : Balls.Radius Γ, {x | q x = d} = Balls.closedDisc v a r)) :
    {d : Q | ∃ x y, q x = d ∧ q y = d ∧ f x ≠ f y}.Finite := by
  obtain ⟨R, _, _, hO, hC⟩ := mixed_finite_definable_obstacles v hv S (graph f) hgraph
  apply (R.finite_toSet.image q).subset
  rintro d ⟨x, y, hx, hy, hne⟩
  by_contra hd
  have havoid : ∀ c ∈ R, q c ≠ d := by
    intro c hc he
    exact hd ⟨c, hc, he⟩
  obtain ⟨a, ⟨r, he⟩ | ⟨r, he⟩⟩ := hq d
  · have hav : ∀ c ∈ R, c ∉ Balls.openDisc v a r := by
      intro c hc hh
      exact havoid c hc ((Set.ext_iff.mp he c).mpr hh)
    have hconst : f x = f y := by
      ext ys
      by_cases hs : ∀ i, iRV (ys i)
      · exact (mem_graph f x ys).symm.trans
          ((hO a r hav x ((Set.ext_iff.mp he x).mp hx) y ((Set.ext_iff.mp he y).mp hy) ys hs).trans
            (mem_graph f y ys))
      · exact iff_of_false (fun hh => hs (hf x ys hh)) (fun hh => hs (hf y ys hh))
    exact hne hconst
  · have hav : ∀ c ∈ R, c ∉ Balls.closedDisc v a r := by
      intro c hc hh
      exact havoid c hc ((Set.ext_iff.mp he c).mpr hh)
    have hconst : f x = f y := by
      ext ys
      by_cases hs : ∀ i, iRV (ys i)
      · exact (mem_graph f x ys).symm.trans
          ((hC a r hav x ((Set.ext_iff.mp he x).mp hx) y ((Set.ext_iff.mp he y).mp hy) ys hs).trans
            (mem_graph f y ys))
      · exact iff_of_false (fun hh => hs (hf x ys hh)) (fun hh => hs (hf y ys hh))
    exact hne hconst

end SpecialTransformations.Section3.BallFibreConstancy
