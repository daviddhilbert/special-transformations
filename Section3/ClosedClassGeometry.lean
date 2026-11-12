module

public import Section3.ClassCenterRelation

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.ClosedClassGeometry
open ClosedClassCodes ClosedBallCodes
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable (E : Set (Fin 2 → M)) (R : Set M) (hR : R ⊆ {x | iVF x})
variable {Q : Type} (q : VFType (M := M) → Q)
    (hEq : ∀ x y : VFType (M := M), ![x.val,y.val] ∈ E ↔ q x = q y)
include hR hEq

theorem code_class (t : codes E R) :
    ∃ r : VFType (M := M), r.val ∈ R ∧
      ∀ x : VFType (M := M), x.val ∈ rawBall t.val ↔ q x = q r := by
  obtain ⟨r,hr,ht⟩ := t.property.2
  refine ⟨⟨r,hR hr⟩,hr,?_⟩
  intro x
  exact (Set.ext_iff.mp ht x.val).trans (hEq x ⟨r,hR hr⟩)

theorem same_ball (t : codes E R) (x y : VFType (M := M))
    (hx : x.val ∈ rawBall t.val) (hy : y.val ∈ rawBall t.val) : q x = q y := by
  obtain ⟨r,_,he⟩ := code_class E R hR q hEq t
  exact ((he x).mp hx).trans ((he y).mp hy).symm

theorem mem_of_same_class (t : codes E R) (x y : VFType (M := M))
    (hx : x.val ∈ rawBall t.val) (hxy : q x = q y) : y.val ∈ rawBall t.val := by
  obtain ⟨r,_,he⟩ := code_class E R hR q hEq t
  exact (he y).mpr (hxy.symm.trans ((he x).mp hx))

theorem disjoint_or_eq (t u : codes E R)
    (hne : (rawBall t.val ∩ rawBall u.val).Nonempty) : rawBall t.val = rawBall u.val := by
  obtain ⟨x,hxt,hxu⟩ := hne
  let x' : VFType (M := M) := ⟨x,hxt.2.1⟩
  ext z
  constructor
  · intro hzt
    let z' : VFType (M := M) := ⟨z,hzt.2.1⟩
    exact mem_of_same_class E R hR q hEq u x' z' hxu
      (same_ball E R hR q hEq t x' z' hxt hzt)
  · intro hzu
    let z' : VFType (M := M) := ⟨z,hzu.2.1⟩
    exact mem_of_same_class E R hR q hEq t x' z' hxt
      (same_ball E R hR q hEq u x' z' hxu hzu)

theorem center_invariant (g : codes E R → M)
    (x y : VFType (M := M)) (hxy : q x = q y) (c : M)
    (hc : ![x.val,c] ∈ ClassCenterRelation.relation (codes E R) g) :
    ![y.val,c] ∈ ClassCenterRelation.relation (codes E R) g := by
  obtain ⟨t,hxt,htc⟩ := hc
  exact ⟨t,mem_of_same_class E R hR q hEq t x y hxt hxy,htc⟩

theorem center_same_class (g : codes E R → M) (hm : ∀ t, g t ∈ rawBall t.val)
    (x c : VFType (M := M))
    (hc : ![x.val,c.val] ∈ ClassCenterRelation.relation (codes E R) g) : q c = q x := by
  obtain ⟨t,hxt,htc⟩ := hc
  have htc' : g t = c.val := htc
  have hct : c.val ∈ rawBall t.val := by
    rw [← htc']
    exact hm t
  exact same_ball E R hR q hEq t c x hct hxt

theorem center_exists (g : codes E R → M)
    (hcover : ∀ r ∈ R, ∃ t : codes E R, rawBall t.val = classBody E r)
    (x r : VFType (M := M)) (hr : r.val ∈ R) (hxr : q x = q r) :
    ∃ c, ![x.val,c] ∈ ClassCenterRelation.relation (codes E R) g := by
  obtain ⟨t,he⟩ := hcover r.val hr
  have hrmem : r.val ∈ rawBall t.val := by
    rw [he]
    exact (hEq r r).mpr rfl
  have hxmem := mem_of_same_class E R hR q hEq t r x hrmem hxr.symm
  exact ⟨g t,t,hxmem,rfl⟩

end SpecialTransformations.Section3.ClosedClassGeometry
