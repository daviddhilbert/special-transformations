import Section5.GammaInvariantLogic
import Section5.PullbackLift
import Section4.VFDimensionRank
import Section4.RelationFibres

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section5

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

private def gammaMapGraph {n m j r d : ℕ} {A : Set (Point (M := M) n m)}
    (f : A → Point (M := M) j r × (Fin d → Values.Gamma (M := M))) :
    Point (M := M) n m → Point (M := M) j (r + d) → Prop :=
  fun x y => ∃ a : A, a.val = x ∧ ∃ t : Fin d → GammaParameters.Code (M := M),
    GammaParameters.values t = (f a).2 ∧
    y = ((f a).1.1, Fin.append (f a).1.2 (fun i => (t i).val))

/-- Definition 4.1 over the named Gamma base. The target has a real
mixed block and a block of actual value-group elements. Definability of
the function means definability of the entire graph on proper codes. -/
def GammaHasVFDimLE (B : Base (M := M)) {n m : ℕ}
    (A : Set (Point (M := M) n m)) (k : ℕ) : Prop :=
  ∃ j ≤ k, ∃ r d, ∃ f : A → Point (M := M) j r × (Fin d → Values.Gamma (M := M)),
    (∀ y, {a | f a = y}.Finite) ∧ GammaGraphDefinable B (gammaMapGraph f)

private theorem pointRelation_raw {S : Set M} {n m j r : ℕ}
    {R : Point (M := M) n m → Point (M := M) j r → Prop}
    (h : RelationDefinable (pointSpace n m) (pointSpace j r) S R) :
    RelationDefinable (rawPointSpace n m) (rawPointSpace j r) S R := by
  let P := pointSpace (M := M) n m
  let Q := pointSpace (M := M) j r
  let P' := rawPointSpace (M := M) n m
  let Q' := rawPointSpace (M := M) j r
  let g := rawPointMap (PresentedSet.univ P S)
  let f := rawPointMap (PresentedSet.univ Q S)
  have hg : (fun p p' => ∃ a : PresentedSet.univ P S, a.val = p ∧ (g a).val = p') =
      (fun p p' => p = p') := by
    funext p p'
    apply propext
    exact ⟨fun ⟨a, ha, he⟩ => ha.symm.trans he, fun he => ⟨⟨p, Set.mem_univ _⟩, rfl, he⟩⟩
  have hf : (fun q q' => ∃ a : PresentedSet.univ Q S, a.val = q ∧ (f a).val = q') =
      (fun q q' => q = q') := by
    funext q q'
    apply propext
    exact ⟨fun ⟨a, ha, he⟩ => ha.symm.trans he, fun he => ⟨⟨q, Set.mem_univ _⟩, rfl, he⟩⟩
  have hleft : RelationDefinable P' P S (fun x y => y = x) := by
    have hh := @Space.RelationDefinable.swap LRV M N P P' _ _
      (@DefinableGeometry.Map.graph_definable LRV M N P P' S _ _ g)
    apply @Space.RelationDefinable.congr LRV M N P' P _ _ _ hh
    intro x y
    exact Iff.of_eq (congrFun (congrFun hg y) x)
  have hright : RelationDefinable Q Q' S (fun x y => x = y) := by
    apply @Space.RelationDefinable.congr LRV M N Q Q' _ _ _
      (@DefinableGeometry.Map.graph_definable LRV M N Q Q' S _ _ f)
    intro x y
    exact Iff.of_eq (congrFun (congrFun hf x) y)
  have h₁ := @Space.RelationDefinable.comp LRV M N P' P Q _ _ _ hleft h
  have h₂ := @Space.RelationDefinable.comp LRV M N P' Q Q' _ _ _ h₁ hright
  apply @Space.RelationDefinable.congr LRV M N P' Q' _ _ _ h₂
  intro x y
  constructor
  · rintro ⟨_, ⟨_, rfl, h⟩, rfl⟩
    exact h
  · intro hr
    exact ⟨y, ⟨x, rfl, hr⟩, rfl⟩

theorem gamma_rank_of_dimension {B : Base (M := M)} {n m k : ℕ}
    {A : Set (Point (M := M) n m)} (hA : GammaHasVFDimLE B A k) :
    ∀ x ∈ A, @vfTupleTrdeg M N hN B.real n x.1 ≤ (k : Cardinal) := by
  obtain ⟨j, hj, r, d, f, hfin, hg⟩ := hA
  obtain ⟨e, c, hR⟩ := hg.real_specialize
  let S := B.real
  let T := S ∪ Set.range (GammaParameters.rawTuple c)
  have hR' := pointRelation_raw hR
  let P := rawPointSpace (M := M) n m
  let Q := rawPointSpace (M := M) j (r+d)
  have hrev := @Space.RelationDefinable.swap LRV M N P Q _ _ hR'
  intro x hx
  let a : A := ⟨x, hx⟩
  let t := GammaParameters.representatives (f a).2
  let y : Point (M := M) j (r + d) := ((f a).1.1, Fin.append (f a).1.2 (fun i => (t i).val))
  have hy : gammaMapGraph f x y :=
    ⟨a, rfl, t, GammaParameters.representatives_values (f a).2, rfl⟩
  have hF : {z | gammaMapGraph f z y}.Finite := by
    apply ((hfin (f a)).image Subtype.val).subset
    rintro z ⟨b, hbx, u, hu, he⟩
    have hpoint : (f b).1 = (f a).1 := by
      refine Prod.ext (congrArg Prod.fst he).symm ?_
      funext i
      simpa only [y, Fin.append_left] using
        (congrArg (fun q : Point (M := M) j (r + d) => q.2 (Fin.castAdd d i)) he).symm
    have hcode : u = t := by
      funext i
      apply Subtype.ext
      simpa only [y, Fin.append_right] using
        (congrArg (fun q : Point (M := M) j (r + d) => q.2 (Fin.natAdd r i)) he).symm
    refine ⟨b, Prod.ext hpoint ?_, hbx⟩
    rw [← hu, hcode, GammaParameters.representatives_values]
  have hcodes : ∀ z ∈ Set.range (GammaParameters.rawTuple c), @iRV M N z := by
    rintro _ ⟨i, rfl⟩
    exact (c i).val.property
  let hcan := @CanonicalStructure.normalize_isCanonical M sM
  letI : LRV.Structure M := N
  letI : M ⊨ Axioms.ACVF := hN
  have halg (i : Fin n) := finite_relation_vf_coordinate_isAlgebraic hcan hrev y x hy hF i
  let x' : Fin n → VFType (M := M) := x.1
  let y' : Fin j → VFType (M := M) := y.1
  have hfield : vfParameterField T = vfParameterField S :=
    vfParameterField_union_rv S _ hcodes
  have halg' (i : Fin n) : _root_.IsAlgebraic (tupleField (vfParameterField S) y') (x' i) := by
    rw [← hfield]
    exact halg i
  have hr : vfTupleTrdeg S x' ≤ (j : Cardinal) :=
    tupleField_trdeg_le_of_isAlgebraic (vfParameterField S) x' y' halg'
  have hj' : (j : Cardinal) ≤ (k : Cardinal) := by exact_mod_cast hj
  exact hr.trans hj'

end SpecialTransformations.Section5
