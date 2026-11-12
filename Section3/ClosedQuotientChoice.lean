module

public import Section3.ClosedClassGeometry
public import Section3.ProfileComposition
public import Section3.MixedRootFree

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.ClosedQuotientChoice
open ClosedBallCodes ClosedClassCodes
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)
include hv

theorem choose_profile (h00 : M ⊨ Axioms.ACVF00) (S : Set M)
    {Q : Type} (q : VFType (M := M) → Q) (hq : Function.Surjective q)
    (E : Set (Fin 2 → M)) (hE : DefinableOver S (fun _ => .vf) E)
    (hEq : ∀ x y : VFType (M := M), ![x.val,y.val] ∈ E ↔ q x = q y)
    (hclosed : ∀ d, ClosedBallRoots.IsClosedBall v {x | q x = d})
    {m : ℕ} (f : VFType (M := M) → Set (Fin m → M))
    (hf : ∀ x ys, ys ∈ f x → ∀ i, iRV (ys i))
    (hgraph : DefinableOver S MixedPolynomialSyntax.contextSort (BallFibreConstancy.graph f)) :
    ∃ G : Q → Set (Fin m → M),
      (∀ d ys, ys ∈ G d → ∀ i, iRV (ys i)) ∧
      DefinableOver S MixedPolynomialSyntax.contextSort (BallFibreConstancy.graph (fun x => G (q x))) ∧
      ∀ d, ∃ x : VFType (M := M), q x = d ∧ f x = G d := by
  obtain ⟨R,hRne,hRdef,hO,hC⟩ := mixed_finite_definable_obstacles v hv S (BallFibreConstancy.graph f) hgraph
  let R₀ : Set M := Subtype.val '' (R : Set (VFType (M := M)))
  have hRfin : R₀.Finite := R.finite_toSet.image Subtype.val
  have hRsort : R₀ ⊆ {x | iVF x} := hRdef.2
  have hEsort : ∀ z ∈ E, ∀ i, iVF (z i) :=
    ((definableOver_iff_normalized_raw S (fun _ => .vf) E).mp hE).2
  have hclosedR : ∀ r ∈ R₀, ClosedBallRoots.IsClosedBall v {x : VFType (M := M) | ![x.val,r] ∈ E} := by
    intro r hr
    let r' : VFType (M := M) := ⟨r,hRsort hr⟩
    have he : {x : VFType (M := M) | ![x.val,r] ∈ E} = {x | q x = q r'} :=
      Set.ext (fun x => hEq x r')
    exact he.symm ▸ hclosed (q r')
  have hcover := codes_cover v hv E R₀ hEsort hclosedR
  obtain ⟨g,hm,hg,hinv⟩ := centers h00 S E R₀ hE hRdef hRfin
  let K := ClassCenterRelation.relation (codes E R₀) g
  have hK : DefinableOver S (fun _ => .vf) K := ClassCenterRelation.relation_definable S _ g hm hg
  have hKsort := ((definableOver_iff_normalized_raw S (fun _ => .vf) K).mp hK).2
  have hfun {x c d : M} (hc : ![x,c] ∈ K) (hd : ![x,d] ∈ K) : c = d :=
    ClassCenterRelation.functional _ g (ClosedClassGeometry.disjoint_or_eq E R₀ hRsort q hEq) hinv hc hd
  let V := ProfileComposition.compose K (BallFibreConstancy.graph f)
  let F := ProfileComposition.profile V
  have hV : DefinableOver S MixedPolynomialSyntax.contextSort V :=
    ProfileComposition.compose_definable S K _ hK hgraph
  have hVsort := ((definableOver_iff_normalized_raw S MixedPolynomialSyntax.contextSort V).mp hV).2
  have hFG : BallFibreConstancy.graph F = V := ProfileComposition.graph_profile V (fun z hz => hVsort z hz 0)
  have hOrig (x : VFType (M := M)) :
      ProfileComposition.profile (BallFibreConstancy.graph f) x = f x :=
    Set.ext (fun ys => BallFibreConstancy.mem_graph f x ys)
  have hSome (x c : VFType (M := M)) (hc : ![x.val,c.val] ∈ K) : F x = f c :=
    (ProfileComposition.at_some K _ x c hc (fun d hd => hfun hd hc)).trans (hOrig c)
  have hNone (x : VFType (M := M)) (hn : ∀ c, ![x.val,c] ∉ K) : F x = f x :=
    (ProfileComposition.at_none K _ x hn).trans (hOrig x)
  have hDisc (d : Q) : ∃ a ρ, {x | q x = d} = Balls.closedDisc v a ρ := by
    rcases hclosed d with he | ⟨a,b,he⟩
    · exact ⟨0,⊥,he⟩
    · exact ⟨a,↑(OrderDual.toDual (v b)),he⟩
  have hConst (x y : VFType (M := M)) (hxy : q x = q y)
      (hn : ∀ c, ![x.val,c] ∉ K) : f x = f y := by
    obtain ⟨a,ρ,he⟩ := hDisc (q x)
    have hav : ∀ r ∈ R, r ∉ Balls.closedDisc v a ρ := by
      intro r hr hrd
      have hqr : q r = q x := (Set.ext_iff.mp he r).mpr hrd
      obtain ⟨c,hc⟩ := ClosedClassGeometry.center_exists E R₀ hRsort q hEq g hcover x r ⟨r,hr,rfl⟩ hqr.symm
      exact hn c hc
    have hxD : x ∈ Balls.closedDisc v a ρ := (Set.ext_iff.mp he x).mp rfl
    have hyD : y ∈ Balls.closedDisc v a ρ := (Set.ext_iff.mp he y).mp hxy.symm
    ext ys
    by_cases hs : ∀ i, iRV (ys i)
    · exact (BallFibreConstancy.mem_graph f x ys).symm.trans
        ((hC a ρ hav x hxD y hyD ys hs).trans (BallFibreConstancy.mem_graph f y ys))
    · exact iff_of_false (fun hh => hs (hf x ys hh)) (fun hh => hs (hf y ys hh))
  have hFInv (x y : VFType (M := M)) (hxy : q x = q y) : F x = F y := by
    by_cases hex : ∃ c, ![x.val,c] ∈ K
    · obtain ⟨c,hc⟩ := hex
      let c' : VFType (M := M) := ⟨c,hKsort ![x.val,c] hc 1⟩
      have hyc := ClosedClassGeometry.center_invariant E R₀ hRsort q hEq g x y hxy c hc
      exact (hSome x c' hc).trans (hSome y c' hyc).symm
    · have hn : ∀ c, ![x.val,c] ∉ K := by simpa only [not_exists] using hex
      have hny : ∀ c, ![y.val,c] ∉ K := by
        intro c hc
        exact hn c (ClosedClassGeometry.center_invariant E R₀ hRsort q hEq g y x hxy.symm c hc)
      exact (hNone x hn).trans ((hConst x y hxy hn).trans (hNone y hny).symm)
  let rep (d : Q) : VFType (M := M) := Classical.choose (hq d)
  have hrep (d : Q) : q (rep d) = d := Classical.choose_spec (hq d)
  let G (d : Q) := F (rep d)
  have hfactor : (fun x : VFType (M := M) => G (q x)) = F :=
    funext (fun x => hFInv (rep (q x)) x (hrep (q x)))
  have hrepval (d : Q) : ∃ x : VFType (M := M), q x = d ∧ f x = G d := by
    by_cases hex : ∃ c, ![(rep d).val,c] ∈ K
    · obtain ⟨c,hc⟩ := hex
      let c' : VFType (M := M) := ⟨c,hKsort ![(rep d).val,c] hc 1⟩
      refine ⟨c',?_,(hSome (rep d) c' hc).symm⟩
      exact (ClosedClassGeometry.center_same_class E R₀ hRsort q hEq g hm (rep d) c' hc).trans (hrep d)
    · have hn : ∀ c, ![(rep d).val,c] ∉ K := by simpa only [not_exists] using hex
      exact ⟨rep d,hrep d,(hNone (rep d) hn).symm⟩
  refine ⟨G,?_,?_,hrepval⟩
  · intro d ys hy
    obtain ⟨x,_,hx⟩ := hrepval d
    exact hf x ys (hx.symm ▸ hy)
  · rw [hfactor,hFG]
    exact hV

end SpecialTransformations.Section3.ClosedQuotientChoice
