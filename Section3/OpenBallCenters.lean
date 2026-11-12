module

public import Section3.BallTranslation
public import Section3.ClosedBallCentres
public import Section3.EncodedBallGeometry
public import Section3.FiniteAlgebraicCover
public import Section3.GammaBaseVFAlgebraicity
public import Section3.GammaClosedBallCenters
public import Section3.GammaProjection
public import Section3.GammaRealMap
public import Section3.GammaRealRestriction
public import Section3.GeneratedBaseLifting
public import Section3.OpenBallCodes
public import Section3.OpenBallFamilyHulls
public import Section3.OpenBallHullGeometry

@[expose] public section

/- The proper-open-ball center construction, with its Gamma-base lifting
and full-code graph prerequisites, is kept in one checked module. -/
open SpecialTransformations.Milestone0.Transfer

/- Component: OpenHullCenters -/
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.OpenBallCodes
open GammaParameters
variable {M : Type} [sM : LRV.Structure M]

def hullCenterCode (z : Fin 3 → M) : Fin 4 → M := ![z 0,z 1,iVFOne,z 2]

theorem hullCenterCode_raw_definable (S : Set M) :
    S.DefinableMap LRV (hullCenterCode (M := M)) := by
  intro i
  fin_cases i
  · exact Set.DefinableFun.proj LRV
  · exact Set.DefinableFun.proj LRV
  · exact DefinableConstants.constant (DefinableConstants.function_symbol
      (L := LRV) Fn.vfOne Fin.elim0 (fun i => i.elim0))
  · exact Set.DefinableFun.proj LRV

variable [hM : M ⊨ Axioms.ACVF]

theorem hullCenterCode_normalize :
    @hullCenterCode M (CanonicalStructure.normalize (M := M)) = hullCenterCode (M := M) := by
  funext z i
  fin_cases i
  · rfl
  · rfl
  · exact CanonicalStructure.normalize_fun Fn.vfOne Fin.elim0 (fun i => i.elim0)
  · rfl

/-- Full real-code graph of a function on actual proper open balls. -/
def quotientCenterGraph (A : Set (OpenBall M)) (f : A → M) : Set (Fin 3 → M) :=
  {z | ∃ t : Code M, t.val = Fin.init z ∧
    ∃ D : A, Quotient.mk _ t = D.val ∧ f D = z (Fin.last 2)}

/-- The checked closed-ball center theorem gives a same-base definable
point of each open ball's closed hull. This does not assert open membership. -/
theorem finite_hull_centers (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M))
    (A : Set (OpenBall M)) (hA : A.Finite)
    (hdef : DefinableOverBase B (fun _ => .vf) (pullback A)) :
    ∃ c : A → M, (∀ D, c D ∈ ClosedBallCodes.underlying (hull D.val)) ∧
      DefinableOverBase B (fun _ => .vf) (quotientCenterGraph A c) := by
  obtain ⟨g,hgmem,hgdef⟩ := lemma_3_10_gamma_base h00 B (hull '' A)
    (hA.image hull) (hull_family_definable_base B A hdef)
  have hgs (E : hull '' A) : iVF (g E) := by
    obtain ⟨q,hq⟩ := Quotient.exists_rep E.val
    have hm := hgmem E
    rw [← hq] at hm
    exact hm.2.1
  let c (D : A) := g ⟨hull D.val,Set.mem_image_of_mem hull D.property⟩
  refine ⟨c,?_,?_⟩
  · intro D
    exact hgmem ⟨hull D.val,Set.mem_image_of_mem hull D.property⟩
  let F : (Fin 3 → M) → (Fin 4 → M) := hullCenterCode
  have hF : @Set.DefinableMap M LRV (CanonicalStructure.normalize (M := M))
      (Fin 3) (Fin 4) B.real F := by
    have h := @hullCenterCode_raw_definable M (CanonicalStructure.normalize (M := M)) B.real
    rw [hullCenterCode_normalize] at h
    exact h
  have hi (z : Fin 3 → M) : Fin.init (F z) = hullCode (Fin.init z) := by
    funext i
    fin_cases i <;> rfl
  have hp := hgdef.preimage_real_map (fun _ : Fin 3 => .vf) F hF
  have hd := hdef.preimage_real (fun _ : Fin 3 => .vf) Fin.castSucc
  have hh := hd.inter hp
  convert hh using 1
  all_goals try rfl
  ext z
  constructor
  · rintro ⟨q,hq,D,hD,hc⟩
    have hqs : ∀ i, iVF (z i) := by
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · exact hc ▸ hgs ⟨hull D.val,Set.mem_image_of_mem hull D.property⟩
      · change iVF (Fin.init z j)
        rw [← congrFun hq j]
        exact q.property.1 j
    have hqA : Quotient.mk _ q ∈ A := hD.symm ▸ D.property
    refine ⟨⟨?_,hqs⟩,?_,hqs⟩
    · change Fin.init z ∈ pullback A
      rw [← hq]
      exact ⟨q.property,hqA⟩
    · refine ⟨⟨hullCode q.val,hullCode_sorted q.val q.property⟩,?_,
        ⟨hull D.val,Set.mem_image_of_mem hull D.property⟩,?_,hc⟩
      · rw [hi,← hq]
      · exact congrArg hull hD
  · rintro ⟨⟨hqA,_⟩,⟨u,hu,E,hE,hg⟩,hzs⟩
    obtain ⟨hq,hqA⟩ := hqA
    let q : Code M := ⟨Fin.init z,hq⟩
    let D : A := ⟨Quotient.mk _ q,hqA⟩
    have huq : u.val = hullCode q.val := hu.trans (hi z)
    have hue : Quotient.mk _ u = hull D.val := by
      apply Quotient.sound
      exact congrArg ClosedBallCodes.rawBall huq
    have hval : E.val = hull D.val := hE.symm.trans hue
    have he : E = ⟨hull D.val,Set.mem_image_of_mem hull D.property⟩ := Subtype.ext hval
    refine ⟨q,rfl,D,rfl,?_⟩
    change g ⟨hull D.val,Set.mem_image_of_mem hull D.property⟩ = z (Fin.last 2)
    rw [← he]
    exact hg

/-- A finite family has only finitely many hull centers; projection of the
complete code graph keeps their image definable over precisely B. -/
theorem finite_hull_center_image (B : Base (M := M)) (A : Set (OpenBall M))
    (hA : A.Finite) (c : A → M)
    (hc : DefinableOverBase B (fun _ => .vf) (quotientCenterGraph A c)) :
    DefinableAtBase B .vf (Set.range c) ∧ (Set.range c).Finite := by
  have hd := hc.image_real (fun _ : Fin 1 => Fin.last 2)
  refine ⟨?_,?_⟩
  · change DefinableOverBase B (fun _ : Fin 1 => .vf) {z | z 0 ∈ Set.range c}
    convert hd using 1
    all_goals try rfl
    ext z
    constructor
    · rintro ⟨D,hD⟩
      obtain ⟨q,hq⟩ := Quotient.exists_rep D.val
      let w : Fin 3 → M := Fin.snoc q.val (c D)
      refine ⟨w,⟨q,?_,D,hq,rfl⟩,?_⟩
      · funext i
        fin_cases i <;> rfl
      · funext i
        fin_cases i
        exact hD
    · rintro ⟨w,⟨q,hq,D,hD,hcD⟩,he⟩
      exact ⟨D,hcD.trans (congrFun he 0)⟩
  · letI : Fintype A := hA.fintype
    exact Set.finite_range c

end SpecialTransformations.Section3.OpenBallCodes

/- Component: OpenBallBoundary -/
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.Balls
section General
variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]

theorem strictDisc_recenter_iff (v : Valuation K Γ) (a x y r : K)
    (hx : v (x-a) < v r) : v (y-x) < v r ↔ v (y-a) < v r := by
  constructor
  · intro hy
    have he : y-a = (y-x)+(x-a) := by ring
    rw [he]
    exact v.map_add_lt hy hx
  · intro hy
    have he : y-x = (y-a)+(a-x) := by ring
    rw [he]
    exact v.map_add_lt hy (by rwa [v.map_sub_swap])

/-- A point of the closed hull outside its strict disc is exactly at
the radius from every point of that disc. -/
theorem hull_boundary_distance (v : Valuation K Γ) (a c x r : K)
    (hc : v (c-a) ≤ v r) (hco : ¬ v (c-a) < v r) (hx : v (x-a) < v r) :
    v (x-c) = v r := by
  have hca : v (c-a) = v r := le_antisymm hc (le_of_not_gt hco)
  apply le_antisymm
  · have he : x-c = (x-a)+(a-c) := by ring
    rw [he]
    exact v.map_add_le hx.le (by rw [v.map_sub_swap,hca])
  · apply le_of_not_gt
    intro hxc
    have he : c-a = (c-x)+(x-a) := by ring
    have hbad : v (c-a) < v r := by
      rw [he]
      exact v.map_add_lt (by rwa [v.map_sub_swap]) hx
    exact hco hbad
end General

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)

include hv in
/-- Boundary offsets determine the entire open ball, rather than merely
an RV fibre containing it. The boundary condition is essential. -/
theorem hull_boundary_rv_fibre_iff (a c x r y : VFType (M := M)) (hr : r ≠ 0)
    (hc : v (c-a) ≤ v r) (hco : ¬ v (c-a) < v r) (hx : v (x-a) < v r) :
    iRv (y-c).val = iRv (x-c).val ↔ v (y-a) < v r := by
  have he := hull_boundary_distance v a c x r hc hco hx
  have hxc : x-c ≠ 0 := by
    intro hz
    have hzv : v r = 0 := by rw [← he,hz,map_zero]
    exact hr (v.zero_iff.mp hzv)
  have hF := Set.ext_iff.mp (rvFibre_eq_openDisc v hv (x-c) hxc) (y-c)
  have hd : (y-c)-(x-c) = y-x := by abel
  change iRv (y-c).val = iRv (x-c).val ↔ v ((y-c)-(x-c)) < v (x-c) at hF
  rw [hd,he] at hF
  exact hF.trans (strictDisc_recenter_iff v a x y r hx)

end SpecialTransformations.Section3.Balls

/- Component: OpenCentersFromFiniteSet -/
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.BallFamilies
open RawClosure.Tuple Barycentre ClosedBallRoots
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n : ℕ}

/- Extracted from closed_family_centres: once a finite original-base
hitting set is given, neither finiteness nor real-base definability of the
family is needed to define the invariant center function on real codes. -/
/-- Open-disc adaptation of the checked ClosedCentersFromFiniteSet
construction. The original finite real-base hitting set controls the whole
mean graph; the final containment uses MeanInBalls.mean_mem_openDisc. -/
theorem open_centers_of_finite_hitting_set {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)
    (h00 : M ⊨ Axioms.ACVF00) (S : Set M) (C : Set (Fin n → M))
    (D : (Fin n → M) → Set (VFType (M := M)))
    (hD : RelationDefinable S (relation D))
    (R : Finset (VFType (M := M)))
    (hRdef : DefinableAt S .vf (Subtype.val '' (R : Set (VFType (M := M)))))
    (hhit : ∀ t ∈ C, ∃ x ∈ R, x ∈ D t)
    (hopen : ∀ t ∈ C, ∃ a r : VFType (M := M),
      r ≠ 0 ∧ D t = ValOneEC.openBall v a (v r)) :
    ∃ f : (Fin n → M) → VFType (M := M),
      S.DefinableFun LRV (fun t => (f t).val) ∧ (∀ t ∈ C, f t ∈ D t) ∧
      ∀ t u, D t = D u → f t = f u := by
  let F (t : Fin n → M) : Finset (VFType (M := M)) := R.filter (fun x => x ∈ D t)
  have hF : RelationDefinable S (finiteFibreRelation F) := by
    have hR := hRdef.raw_definable.preimage_comp
      (Sum.inr : Fin 1 → Fin n ⊕ Fin 1)
    change S.Definable LRV {z : Fin n ⊕ Fin 1 → M |
      (z ∘ Sum.inl,z (.inr 0)) ∈ finiteFibreRelation F}
    convert hD.inter hR using 1
    ext z
    change (∃ x ∈ F (z ∘ Sum.inl), x.val = z (.inr 0)) ↔
      (∃ x ∈ D (z ∘ Sum.inl), x.val = z (.inr 0)) ∧
      z (.inr 0) ∈ Subtype.val '' (R : Set (VFType (M := M)))
    constructor
    · rintro ⟨x,hx,he⟩
      obtain ⟨hxR,hxD⟩ := Finset.mem_filter.mp hx
      exact ⟨⟨x,hxD,he⟩,x,hxR,he⟩
    · rintro ⟨⟨x,hxD,he⟩,y,hyR,hy⟩
      have hxy : y = x := Subtype.ext (hy.trans he.symm)
      exact ⟨x,Finset.mem_filter.mpr ⟨hxy ▸ hyR,hxD⟩,he⟩
  refine ⟨fun t => mean (F t),mean_definable h00 S F hF R.card
    (fun t => Finset.card_filter_le _ _),?_,?_⟩
  · intro t ht
    have hne : (F t).Nonempty := by
      obtain ⟨x,hxR,hxD⟩ := hhit t ht
      exact ⟨x,Finset.mem_filter.mpr ⟨hxR,hxD⟩⟩
    obtain ⟨a,r,hr,he⟩ := hopen t ht
    have hn : v r ≠ 0 := (v.ne_zero_iff).mpr hr
    have he' : D t = Balls.openDisc v a (Balls.openRadius (v r) hn) := by
      rw [he]
      rfl
    rw [he']
    exact mean_mem_openDisc v hv h00 (F t) hne a _ (fun x hx => by
      have hxD := (Finset.mem_filter.mp hx).2
      rw [he'] at hxD
      exact hxD)
  · intro t u he
    have hFtu : F t = F u := by simp only [F,he]
    exact congrArg mean hFtu

end SpecialTransformations.Section3.BallFamilies

/- Component: OpenBallMembership -/
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3.OpenBallCodes
variable {M : Type} [sM : LRV.Structure M]

theorem membership_raw_definable (S : Set M) :
    S.Definable LRV {z : Fin 3 → M | z (Fin.last 2) ∈ rawBall (Fin.init z)} := by
  let p : Parameters S := ⟨0,Fin.elim0,(fun _ => .vf),(fun i => i.elim0),(fun i => i.elim0)⟩
  let G : Set (Fin 3 → M) := {z | (∀ i, iVF (z i)) ∧ body.Realize Fin.elim0 z}
  have hG : DefinableOver S (fun _ => .vf) G := ⟨p,body,body_sorted,rfl⟩
  have hzero : S.DefinableFun LRV (fun _ : Fin 3 → M => iVFZero) :=
    DefinableConstants.constant (DefinableConstants.function_symbol
      (L := LRV) Fn.vfZero Fin.elim0 (fun i => i.elim0))
  have hn := ((Set.DefinableFun.proj (L := LRV) (A := S) (i := (1 : Fin 3))).ofPred_eq hzero).compl
  convert hG.raw_definable.inter hn using 1
  ext z
  have ht : tuple (Fin.init z) (z (Fin.last 2)) = z := by
    funext i
    fin_cases i <;> rfl
  change ((∀ i : Fin 2, iVF (Fin.init z i)) ∧ Fin.init z 1 ≠ iVFZero) ∧
      iVF (z (Fin.last 2)) ∧ body.Realize Fin.elim0 (tuple (Fin.init z) (z (Fin.last 2))) ↔
    ((∀ i : Fin 3, iVF (z i)) ∧ body.Realize Fin.elim0 z) ∧ ¬ z 1 = iVFZero
  rw [ht]
  simp only [Fin.forall_fin_succ,Fin.forall_fin_zero,and_true]
  change ((iVF (z 0) ∧ iVF (z 1)) ∧ z 1 ≠ iVFZero) ∧
    iVF (z 2) ∧ body.Realize Fin.elim0 z ↔
    ((iVF (z 0) ∧ iVF (z 1) ∧ iVF (z 2)) ∧ body.Realize Fin.elim0 z) ∧ ¬ z 1 = iVFZero
  tauto

theorem relation_definable (S : Set M) :
    RawClosure.Tuple.RelationDefinable S (BallFamilies.relation (ball (M := M))) := by
  let idx : Fin 3 → Fin 2 ⊕ Fin 1 := ![.inl 0,.inl 1,.inr 0]
  have h := (membership_raw_definable (M := M) S).preimage_comp idx
  change S.Definable LRV {z : Fin 2 ⊕ Fin 1 → M |
    (z ∘ Sum.inl,z (.inr 0)) ∈ BallFamilies.relation (ball (M := M))}
  convert h using 1
  ext z
  have he : Fin.init (z ∘ idx) = z ∘ Sum.inl := by
    funext i
    fin_cases i <;> rfl
  change (∃ x : VFType (M := M), x.val ∈ rawBall (z ∘ Sum.inl) ∧ x.val = z (.inr 0)) ↔
    (z ∘ idx) (Fin.last 2) ∈ rawBall (Fin.init (z ∘ idx))
  rw [he]
  change (∃ x : VFType (M := M), x.val ∈ rawBall (z ∘ Sum.inl) ∧ x.val = z (.inr 0)) ↔
    z (.inr 0) ∈ rawBall (z ∘ Sum.inl)
  constructor
  · rintro ⟨x,hx,he⟩
    exact he ▸ hx
  · intro hx
    exact ⟨⟨z (.inr 0),hx.2.1⟩,hx,rfl⟩

variable [hM : M ⊨ Axioms.ACVF]

theorem rawBall_normalize (q : Fin 2 → M) :
    @rawBall M (CanonicalStructure.normalize (M := M)) q = rawBall q := by
  ext x
  have hz : @iVFZero M (CanonicalStructure.normalize (M := M)) = iVFZero :=
    CanonicalStructure.sortZero_normalize .vf
  have hp : @Proper M (CanonicalStructure.normalize (M := M)) q ↔ Proper q := by
    simp only [Proper,hz]
    rfl
  by_cases hq : Proper q
  · by_cases hx : iVF x
    · have hxs : ∀ i : Fin 3, sortEval SortTag.vf (tuple q x i) := by
        intro i
        fin_cases i
        · exact hq.1 0
        · exact hq.1 1
        · exact hx
      change (_ ∧ iVF x ∧ _) ↔ (_ ∧ iVF x ∧ _)
      rw [hp]
      exact and_congr Iff.rfl (and_congr Iff.rfl
        (CanonicalStructure.realize_normalize hM (fun _ : Fin 0 => .vf)
          Fin.elim0 (fun i => i.elim0) body (fun _ => .vf) (tuple q x) body_sorted hxs))
    · change (_ ∧ iVF x ∧ _) ↔ (_ ∧ iVF x ∧ _)
      simp only [hx,and_false,false_and]
  · change (_ ∧ _ ∧ _) ↔ (_ ∧ _ ∧ _)
    rw [hp]
    simp only [hq,false_and]

theorem membership_definable (S : Set M) :
    DefinableOver S (fun _ : Fin 3 => .vf)
      {z | z (Fin.last 2) ∈ rawBall (Fin.init z)} := by
  apply (definableOver_iff_normalized_raw S (fun _ => .vf) _).mpr
  refine ⟨?_,?_⟩
  · have h := @membership_raw_definable M (CanonicalStructure.normalize (M := M)) S
    simpa only [rawBall_normalize] using h
  · intro z hz i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact hz.2.1
    · exact hz.1.1 j

end SpecialTransformations.Section3.OpenBallCodes

/- Component: OpenBallOffsets -/
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.OpenBallCodes
open GammaParameters
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def differenceSort : Fin 3 → SortTag := ![.vf,.vf,.rv]

def differenceGraph : Set (Fin 3 → M) :=
  {z | (∀ i, sortEval (differenceSort i) (z i)) ∧
    iRv (iVFAdd (z 0) (iVFNeg (z 1))) = z 2}

private theorem realize_unary {β : Type} (f : Fn 1) (t : LRV.Term β) (z : β → M) :
    (Term.func f ![t] : LRV.Term β).realize z = Structure.funMap (L := LRV) f ![t.realize z] := by
  change Structure.funMap (L := LRV) f (fun i => _) = _
  congr 1
  funext i
  fin_cases i
  rfl

private theorem realize_binary {β : Type} (f : Fn 2) (t u : LRV.Term β) (z : β → M) :
    (Term.func f ![t,u] : LRV.Term β).realize z = Structure.funMap (L := LRV) f ![t.realize z,u.realize z] := by
  change Structure.funMap (L := LRV) f (fun i => _) = _
  congr 1
  funext i
  fin_cases i <;> rfl

theorem differenceGraph_definable (S : Set M) :
    DefinableOver S differenceSort (differenceGraph (M := M)) := by
  let p : Parameters S := ⟨0,Fin.elim0,(fun _ => .vf),(fun i => i.elim0),(fun i => i.elim0)⟩
  let v (i : Fin 3) : LRV.Term (Fin 0 ⊕ Fin 3) := .var (.inr i)
  let t : LRV.Term (Fin 0 ⊕ Fin 3) :=
    .func Fn.rvMap ![.func Fn.vfAdd ![v 0,.func Fn.vfNeg ![v 1] ] ]
  let φ : LRV.BoundedFormula (Fin 0) 3 := .equal t (v 2)
  have hw : WellSorted p.sorts differenceSort φ := by
    exact .equal _ (s := .rv)
      (by dsimp only [p,t,v,differenceSort]; decide)
      (by dsimp only [p,v,differenceSort]; decide)
  refine ⟨p,φ,hw,?_⟩
  ext z
  apply and_congr Iff.rfl
  change _ ↔ t.realize (Sum.elim Fin.elim0 z) = z 2
  have he : t.realize (Sum.elim Fin.elim0 z) = iRv (iVFAdd (z 0) (iVFNeg (z 1))) := by
    dsimp only [t]
    rw [realize_unary,realize_binary,realize_unary]
    rfl
  rw [he]

/-- Offsets from the hull center, only for balls which avoid that center. -/
def offsets (A : Set (OpenBall M)) (c : A → M) : Set M :=
  {t | ∃ D : A, c D ∉ underlying D.val ∧
    ∃ x ∈ underlying D.val, iRv (iVFAdd x (iVFNeg (c D))) = t}

theorem center_sort_of_graph (B : Base (M := M)) (A : Set (OpenBall M)) (c : A → M)
    (hc : DefinableOverBase B (fun _ => .vf) (quotientCenterGraph A c))
    (D : A) : iVF (c D) := by
  obtain ⟨q,hq⟩ := Quotient.exists_rep D.val
  let z : Fin 3 → M := Fin.snoc q.val (c D)
  have hz : z ∈ quotientCenterGraph A c := by
    refine ⟨q,?_,D,hq,rfl⟩
    funext i
    fin_cases i <;> rfl
  exact hc.proper z hz (Fin.last 2)

/-- The full set of offsets is definable using the full center graph and
open membership; no ball or point representatives become parameters. -/
theorem offsets_definable_base (B : Base (M := M)) (A : Set (OpenBall M)) (c : A → M)
    (hc : DefinableOverBase B (fun _ => .vf) (quotientCenterGraph A c)) :
    DefinableAtBase B .rv (offsets A c) := by
  let sm : Fin 5 → SortTag := ![.vf,.vf,.vf,.vf,.rv]
  let iqc : Fin 3 → Fin 5 := ![0,1,2]
  let iqx : Fin 3 → Fin 5 := ![0,1,3]
  let idx : Fin 3 → Fin 5 := ![3,2,4]
  have hm := real_definableOverBase B _ _ (membership_definable B.real)
  have hC := hc.preimage_real sm iqc
  have hX := hm.preimage_real sm iqx
  have hN := hm.compl.preimage_real sm iqc
  have hD := (real_definableOverBase B _ _ (differenceGraph_definable B.real)).preimage_real sm idx
  let H : Set (Fin 5 → M) := {z | z ∈ sortedUniverse sm ∧
    z ∘ iqc ∈ quotientCenterGraph A c ∧
    z 3 ∈ rawBall ![z 0,z 1] ∧ z 2 ∉ rawBall ![z 0,z 1] ∧
    iRv (iVFAdd (z 3) (iVFNeg (z 2))) = z 4}
  have hH : DefinableOverBase B sm H := by
    convert ((hC.inter hX).inter hN).inter hD using 1
    ext z
    have hqc : Fin.init (z ∘ iqc) = ![z 0,z 1] := by funext i; fin_cases i <;> rfl
    have hqx : Fin.init (z ∘ iqx) = ![z 0,z 1] := by funext i; fin_cases i <;> rfl
    change _ ↔ (((z ∘ iqc ∈ quotientCenterGraph A c ∧ z ∈ sortedUniverse sm) ∧
      (z 3 ∈ rawBall (Fin.init (z ∘ iqx)) ∧ z ∈ sortedUniverse sm)) ∧
      ((z ∘ iqc ∈ sortedUniverse (fun _ => .vf) ∧
        z 2 ∉ rawBall (Fin.init (z ∘ iqc))) ∧ z ∈ sortedUniverse sm)) ∧
      (((∀ i, sortEval (differenceSort i) ((z ∘ idx) i)) ∧
        iRv (iVFAdd (z 3) (iVFNeg (z 2))) = z 4) ∧ z ∈ sortedUniverse sm)
    rw [hqc,hqx]
    constructor
    · rintro ⟨hs,hc,hx,hn,he⟩
      have hcs : z ∘ iqc ∈ sortedUniverse (fun _ => .vf) := by
        intro i
        fin_cases i
        · exact hs 0
        · exact hs 1
        · exact hs 2
      have hds : ∀ i, sortEval (differenceSort i) ((z ∘ idx) i) := by
        intro i
        fin_cases i
        · exact hs 3
        · exact hs 2
        · exact hs 4
      exact ⟨⟨⟨⟨hc,hs⟩,hx,hs⟩,⟨hcs,hn⟩,hs⟩,⟨hds,he⟩,hs⟩
    · rintro ⟨⟨⟨⟨hc,hs⟩,hx,_⟩,⟨_,hn⟩,_⟩,⟨_,he⟩,_⟩
      exact ⟨hs,hc,hx,hn,he⟩
  have hp := hH.image_real (fun _ : Fin 1 => (4 : Fin 5))
  change DefinableOverBase B (fun _ : Fin 1 => .rv) {z | z 0 ∈ offsets A c}
  convert hp using 1
  all_goals try rfl
  ext z
  constructor
  · rintro ⟨D,hn,x,hx,he⟩
    obtain ⟨q,hq⟩ := Quotient.exists_rep D.val
    have hcVF := center_sort_of_graph B A c hc D
    have hxVF : iVF x := by
      have hh := hx
      rw [← hq] at hh
      exact hh.2.1
    have htVF : iRV (z 0) := he ▸ rv_mem hM (vf_add_mem hM hxVF (vf_neg_mem hM hcVF))
    let w : Fin 5 → M := ![q.val 0,q.val 1,c D,x,z 0]
    have hwq : ![w 0,w 1] = q.val := by funext i; fin_cases i <;> rfl
    have hws : w ∈ sortedUniverse sm := by
      intro i
      fin_cases i
      · exact q.property.1 0
      · exact q.property.1 1
      · exact hcVF
      · exact hxVF
      · exact htVF
    have hwC : w ∘ iqc ∈ quotientCenterGraph A c := by
      refine ⟨q,?_,D,hq,rfl⟩
      funext i
      fin_cases i <;> rfl
    refine ⟨w,⟨hws,hwC,?_,?_,he⟩,?_⟩
    · rw [hwq]
      have hh := hx
      rw [← hq] at hh
      exact hh
    · rw [hwq]
      have hh := hn
      rw [← hq] at hh
      exact hh
    · funext i
      fin_cases i
      rfl
  · rintro ⟨w,⟨_,⟨q,hq,D,hD,hcD⟩,hx,hn,he⟩,hwz⟩
    have hqv : q.val = ![w 0,w 1] := by
      apply hq.trans
      funext i
      fin_cases i <;> rfl
    have hcD' : c D = w 2 := hcD
    have hxD : w 3 ∈ underlying D.val := by
      rw [← hD]
      change w 3 ∈ rawBall q.val
      rwa [hqv]
    have hnD : c D ∉ underlying D.val := by
      rw [hcD',← hD]
      change w 2 ∉ rawBall q.val
      rwa [hqv]
    refine ⟨D,hnD,w 3,hxD,?_⟩
    rw [hcD']
    exact he.trans (congrFun hwz 0)

theorem raw_center_mem (q : Fin 2 → M) (hq : Proper q) : q 0 ∈ rawBall q := by
  obtain ⟨Γ,hΓ,v,hv⟩ := VFValued.exists_valuation_predV (M := M)
  letI := hΓ
  let a : VFType (M := M) := ⟨q 0,hq.1 0⟩
  let r : VFType (M := M) := ⟨q 1,hq.1 1⟩
  have ha : a ∈ ball q := by
    rw [ball_eq_open v hv q hq]
    change v (a-a) < v r
    simpa only [sub_self,map_zero] using
      (zero_lt_iff.mpr ((v.ne_zero_iff).mpr (radius_ne_zero q hq)))
  exact ha

theorem underlying_nonempty (D : OpenBall M) : (underlying D).Nonempty := by
  obtain ⟨q,rfl⟩ := Quotient.exists_rep D
  exact ⟨q.val 0,raw_center_mem q.val q.property⟩

theorem underlying_subset_vf (D : OpenBall M) : underlying D ⊆ {x | iVF x} := by
  obtain ⟨q,rfl⟩ := Quotient.exists_rep D
  exact fun x hx => hx.2.1

/-- One RV offset per actual ball suffices; its infinitely many real
codes are never counted as different balls. -/
theorem offsets_finite (A : Set (OpenBall M)) (hA : A.Finite) (c : A → M)
    (hc : ∀ D, iVF (c D)) : (offsets A c).Finite := by
  let x (D : A) : M := Classical.choose (underlying_nonempty D.val)
  have hx (D : A) : x D ∈ underlying D.val :=
    Classical.choose_spec (underlying_nonempty D.val)
  let f (D : A) := iRv (iVFAdd (x D) (iVFNeg (c D)))
  letI : Fintype A := hA.fintype
  apply (Set.finite_range f).subset
  rintro t ⟨D,hcout,y,hy,hyt⟩
  refine ⟨D,?_⟩
  obtain ⟨q,hq⟩ := Quotient.exists_rep D.val
  obtain ⟨Γ,hΓ,v,hv⟩ := VFValued.exists_valuation_predV (M := M)
  letI := hΓ
  let a : VFType (M := M) := ⟨q.val 0,q.property.1 0⟩
  let r : VFType (M := M) := ⟨q.val 1,q.property.1 1⟩
  let C : VFType (M := M) := ⟨c D,hc D⟩
  let X : VFType (M := M) := ⟨x D,underlying_subset_vf D.val (hx D)⟩
  let Y : VFType (M := M) := ⟨y,underlying_subset_vf D.val hy⟩
  have hn : v r ≠ 0 := (v.ne_zero_iff).mpr (radius_ne_zero q.val q.property)
  have hb : ball q.val = Balls.openDisc v a (Balls.openRadius (v r) hn) := by
    rw [ball_eq_open v hv q.val q.property]
    rfl
  have hx' : X ∈ Balls.openDisc v a (Balls.openRadius (v r) hn) := by
    rw [← hb]
    change x D ∈ rawBall q.val
    have hXD := hx D
    rw [← hq] at hXD
    exact hXD
  have hy' : Y ∈ Balls.openDisc v a (Balls.openRadius (v r) hn) := by
    rw [← hb]
    change y ∈ rawBall q.val
    have hh := hy
    rw [← hq] at hh
    exact hh
  have hc' : C ∉ Balls.openDisc v a (Balls.openRadius (v r) hn) := by
    rw [← hb]
    change c D ∉ rawBall q.val
    have hh := hcout
    rw [← hq] at hh
    exact hh
  have he := Balls.rv_sub_constant_openDisc v hv a C _ hc' X Y hx' hy'
  have hX : (X-C).val = iVFAdd (x D) (iVFNeg (c D)) := by rw [sub_eq_add_neg]; rfl
  have hY : (Y-C).val = iVFAdd y (iVFNeg (c D)) := by rw [sub_eq_add_neg]; rfl
  rw [hX,hY] at he
  exact he.trans hyt

end SpecialTransformations.Section3.OpenBallCodes

/- Component: GammaBallHittingSet -/
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3.GammaParameters
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- Finitely many same-base VF-algebraic points have one finite real-base
definable cover. This supplies the common hitting set for the mean proof. -/
theorem finite_hitting_set_of_algebraic_points (B : Base (M := M))
    {ι : Type} [Finite ι] (D : ι → Set M)
    (hhit : ∀ i, ∃ x : VFType (M := M), AlgebraicAtBase B .vf x.val ∧ x.val ∈ D i) :
    ∃ R : Finset (VFType (M := M)),
      DefinableAt B.real .vf (Subtype.val '' (R : Set (VFType (M := M)))) ∧
      ∀ i, ∃ x ∈ R, x.val ∈ D i := by
  let x (i : ι) : VFType (M := M) := Classical.choose (hhit i)
  have hx (i : ι) : AlgebraicAtBase B .vf (x i).val ∧ (x i).val ∈ D i :=
    Classical.choose_spec (hhit i)
  let T : Set M := Set.range (fun i => (x i).val)
  have hTf : T.Finite := Set.finite_range _
  have hAlg : ∀ a ∈ T, SpecialTransformations.Section3.AlgebraicAt B.real .vf a := by
    rintro a ⟨i,rfl⟩
    exact (algebraic_vf_iff_real B (x i)).mp (hx i).1
  obtain ⟨E,hEd,hEf,hTE⟩ := finite_definable_cover hTf hAlg
  let E' : Set (VFType (M := M)) := Subtype.val ⁻¹' E
  have hE'f : E'.Finite := hEf.preimage Subtype.val_injective.injOn
  let R := hE'f.toFinset
  have hRE : Subtype.val '' (R : Set (VFType (M := M))) = E := by
    ext a
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact hE'f.mem_toFinset.mp hy
    · intro ha
      let y : VFType (M := M) := ⟨a,hEd.2 ha⟩
      exact ⟨y,hE'f.mem_toFinset.mpr ha,rfl⟩
  refine ⟨R,hRE.symm ▸ hEd,?_⟩
  intro i
  exact ⟨x i,hE'f.mem_toFinset.mpr (hTE (Set.mem_range_self i)),(hx i).2⟩

end SpecialTransformations.Section3.GammaParameters

/- Component: OpenBallAlgebraicPoints -/
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.OpenBallCodes
open GammaParameters
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- The arithmetic step in3.13: an algebraic boundary offset and an
algebraic hull center give an algebraic point in the original open ball. -/
theorem algebraic_point_of_boundary_offset {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : Base (M := M)) (hsmall : Cardinal.mk B.real < κ) (hB : VFGammaGeneratedBase B)
    (q : Fin 2 → M) (hq : Proper q) (c x : VFType (M := M))
    (hcAlg : AlgebraicAtBase B .vf c.val)
    (hcHull : c.val ∈ ClosedBallCodes.rawBall (hullCode q))
    (hcOut : c.val ∉ rawBall q) (hx : x.val ∈ rawBall q)
    (htAlg : AlgebraicAtBase B .rv (CanonicalRV.encodedRv (x-c)).val) :
    ∃ y : VFType (M := M), AlgebraicAtBase B .vf y.val ∧ y.val ∈ rawBall q := by
  obtain ⟨A,G,hAB,hGB,hVF,hgen⟩ := hB
  have hAsmall : Cardinal.mk A < κ := (Cardinal.mk_le_mk_of_subset hAB).trans_lt hsmall
  have ht : AlgebraicAtBase (closureBase (⟨A,G⟩ : Base (M := M))) .rv
      (CanonicalRV.encodedRv (x-c)).val := hgen.symm ▸ htAlg
  obtain ⟨u,hu⟩ := algebraic_rv_closure_generated_lifts hκ hs h00 A hVF hAsmall G
    (CanonicalRV.encodedRv (x-c)) ht
  have hc' : AlgebraicAtBase (closureBase (⟨A,G⟩ : Base (M := M))) .vf c.val :=
    hgen.symm ▸ hcAlg
  have hcF : c ∈ vfAlgebraicClosureField A := (mem_vfAlgebraicClosureField A c).mpr
    ((algebraic_vf_closure_generated_iff A G c).mp hc')
  let y : VFType (M := M) := c+u.val
  have hyF : y ∈ vfAlgebraicClosureField A :=
    (vfAlgebraicClosureField A).add_mem hcF u.property
  have hyAlg : AlgebraicAtBase B .vf y.val := (algebraic_vf_iff_real B y).mpr
    (SpecialTransformations.Section3.AlgebraicAt.mono hAB
      ((mem_vfAlgebraicClosureField A y).mp hyF))
  refine ⟨y,hyAlg,?_⟩
  obtain ⟨Γ,hΓ,v,hv⟩ := VFValued.exists_valuation_predV (M := M)
  letI := hΓ
  let a : VFType (M := M) := ⟨q 0,hq.1 0⟩
  let r : VFType (M := M) := ⟨q 1,hq.1 1⟩
  have hcV : v (c-a) ≤ v r := by
    have hh : c ∈ ClosedBallCodes.ball (hullCode q) := hcHull
    rw [ClosedBallCodes.ball_eq_closed v hv (hullCode q)
      (hullCode_sorted q hq) (hullCode_flag_ne_zero q)] at hh
    exact hh
  have hcO : ¬ v (c-a) < v r := by
    intro hh
    apply hcOut
    have hh' : c ∈ ball q := by
      rw [ball_eq_open v hv q hq]
      exact hh
    exact hh'
  have hxV : v (x-a) < v r := by
    have hh : x ∈ ball q := hx
    rw [ball_eq_open v hv q hq] at hh
    exact hh
  have hyc : y-c = u.val := by dsimp [y]; abel
  have he : iRv (y-c).val = iRv (x-c).val := by
    rw [hyc]
    exact congrArg Subtype.val hu
  have hyV := (Balls.hull_boundary_rv_fibre_iff v hv a c x r y
    (radius_ne_zero q hq) hcV hcO hxV).mp he
  have hy : y ∈ ball q := by
    rw [ball_eq_open v hv q hq]
    exact hyV
  exact hy

/-- Every ball in a finite definable proper open family over a
(VF,Gamma)-generated base has a VF point algebraic over exactly that base. -/
theorem finite_family_algebraic_points {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : Base (M := M)) (hsmall : Cardinal.mk B.real < κ) (hB : VFGammaGeneratedBase B)
    (A : Set (OpenBall M)) (hA : A.Finite)
    (hdef : DefinableOverBase B (fun _ => .vf) (pullback A)) :
    ∀ D : A, ∃ y : VFType (M := M), AlgebraicAtBase B .vf y.val ∧ y.val ∈ underlying D.val := by
  obtain ⟨c,hcHull,hcDef⟩ := finite_hull_centers h00 B A hA hdef
  obtain ⟨hcd,hcf⟩ := finite_hull_center_image B A hA c hcDef
  have hcVF (D : A) : iVF (c D) := center_sort_of_graph B A c hcDef D
  have hcAlg (D : A) : AlgebraicAtBase B .vf (c D) :=
    ⟨Set.range c,hcd,hcf,Set.mem_range_self D⟩
  have htd := offsets_definable_base B A c hcDef
  have htf := offsets_finite A hA c hcVF
  intro D
  let C : VFType (M := M) := ⟨c D,hcVF D⟩
  by_cases hcin : c D ∈ underlying D.val
  · exact ⟨C,hcAlg D,hcin⟩
  obtain ⟨x,hx⟩ := underlying_nonempty D.val
  let X : VFType (M := M) := ⟨x,underlying_subset_vf D.val hx⟩
  have htmem : (CanonicalRV.encodedRv (X-C)).val ∈ offsets A c := by
    refine ⟨D,hcin,x,hx,?_⟩
    change iRv (iVFAdd x (iVFNeg (c D))) = iRv (X-C).val
    rw [sub_eq_add_neg]
    rfl
  have htAlg : AlgebraicAtBase B .rv (CanonicalRV.encodedRv (X-C)).val :=
    ⟨offsets A c,htd,htf,htmem⟩
  obtain ⟨q,hq⟩ := Quotient.exists_rep D.val
  have hcH : C.val ∈ ClosedBallCodes.rawBall (hullCode q.val) := by
    have hh := hcHull D
    rw [← hq,hull_mk] at hh
    exact hh
  have hcO : C.val ∉ rawBall q.val := by
    have hh := hcin
    rw [← hq] at hh
    exact hh
  have hxQ : X.val ∈ rawBall q.val := by
    have hh := hx
    rw [← hq] at hh
    exact hh
  obtain ⟨y,hyAlg,hy⟩ := algebraic_point_of_boundary_offset hκ hs h00 B hsmall hB
    q.val q.property C X (hcAlg D) hcH hcO hxQ htAlg
  refine ⟨y,hyAlg,?_⟩
  rw [← hq]
  exact hy

end SpecialTransformations.Section3.OpenBallCodes

/- Component: OpenCenters -/
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.OpenBallCodes
open GammaParameters
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def codedCenterGraph (C : Set (Fin 2 → M)) (f : C → M) : Set (Fin 3 → M) :=
  {z | ∃ t : C, t.val = Fin.init z ∧ f t = z (Fin.last 2)}

theorem coded_open_centers_from_hitting_set (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M))
    (A : Set (OpenBall M)) 
    (hdef : DefinableOverBase B (fun _ => .vf) (pullback A))
    (R : Finset (VFType (M := M)))
    (hRd : DefinableAt B.real .vf (Subtype.val '' (R : Set (VFType (M := M)))))
    (hhit : ∀ D : A, ∃ x ∈ R, x.val ∈ underlying D.val) :
    ∃ f : pullback A → M, (∀ t, f t ∈ rawBall t.val) ∧
      DefinableOverBase B (fun _ => .vf) (codedCenterGraph (pullback A) f) ∧
      ∀ t u : pullback A, rawBall t.val = rawBall u.val → f t = f u := by
  let N := CanonicalStructure.normalize (M := M)
  letI := sM
  have hN : @Theory.Model LRV M N Axioms.ACVF := CanonicalStructure.normalized_model hM
  have h00N : @Theory.Model LRV M N Axioms.ACVF00 := normalized_model00 h00
  have hRN := (definableAt_normalize_iff B.real .vf
    (Subtype.val '' (R : Set (VFType (M := M))))).mpr hRd
  let D : (Fin 2 → M) → Set (VFType (M := M)) := @OpenBallCodes.ball M N
  have hD (q : Fin 2 → M) : D q = ball q := by
    ext x
    exact Set.ext_iff.mp (rawBall_normalize q) x.val
  have hsort (q : Fin 2 → M) (hq : q ∈ pullback A) : ∀ i, @iVF M N (q i) := by
    obtain ⟨hs,_⟩ := hq
    exact hs.1
  obtain ⟨Γ,hΓ,v,hv⟩ := @VFValued.exists_valuation_predV M N hN
  letI := hΓ
  have hopen (q : Fin 2 → M) (hq : q ∈ pullback A) :
      ∃ a r : VFType (M := M), r ≠ 0 ∧ D q = ValOneEC.openBall v a (v r) := by
    have hsq := hsort q hq
    obtain ⟨hqp,_⟩ := hq
    have hz : @iVFZero M N = @iVFZero M sM := CanonicalStructure.sortZero_normalize .vf
    have hqpN : @Proper M N q := by
      exact ⟨hqp.1,fun he => hqp.2 (he.trans hz)⟩
    refine ⟨⟨q 0,hsq 0⟩,⟨q 1,hsq 1⟩,?_,?_⟩
    · intro he
      exact hqpN.2 (congrArg Subtype.val he)
    · exact @ball_eq_open M N hN Γ hΓ v hv q hqpN
  have hhitN (q : Fin 2 → M) (hq : q ∈ pullback A) : ∃ x ∈ R, x ∈ D q := by
    obtain ⟨hqs,hqA⟩ := hq
    let q' : OpenBallCodes.Code M := ⟨q,hqs⟩
    let a : A := ⟨Quotient.mk _ q',hqA⟩
    obtain ⟨x,hxR,hxB⟩ := hhit a
    refine ⟨x,hxR,?_⟩
    rw [hD]
    exact hxB
  obtain ⟨g,hg,hgmem,hgeq⟩ := @BallFamilies.open_centers_of_finite_hitting_set M N hN 2 Γ hΓ
    v hv h00N B.real (pullback A) D (@OpenBallCodes.relation_definable M N B.real)
    R hRN hhitN hopen
  let H : Set (Fin 3 → M) := {z | (∀ i, iVF (z i)) ∧ (g (Fin.init z)).val = z (Fin.last 2)}
  let S : Set M := B.real
  have hHd : SpecialTransformations.Section3.DefinableOver S (fun _ => .vf) H := by
    apply (definableOver_iff_normalized_raw S (fun _ => .vf) H).mpr
    constructor
    · letI := N
      have hi : S.DefinableMap LRV (Fin.init : (Fin 3 → M) → (Fin 2 → M)) :=
        fun _ => Set.DefinableFun.proj LRV
      have he := (hg.comp hi).ofPred_eq
        (Set.DefinableFun.proj (L := LRV) (A := S) (i := Fin.last 2))
      have hs := Set.definable_iInter_of_finite (fun i : Fin 3 =>
        (definableAt_sort S .vf).raw_definable.preimage_comp (fun _ : Fin 1 => i))
      convert hs.inter he using 1
      ext z
      simp only [H,Set.mem_ofPred_eq,Set.mem_inter_iff,Set.mem_iInter,Set.mem_preimage,
        Function.comp_apply]
      rfl
    · exact fun z hz => hz.1
  let f (q : pullback A) := (g q.val).val
  have hfmem (q : pullback A) : f q ∈ rawBall q.val := by
    have hh := hgmem q.val q.property
    rw [hD] at hh
    exact hh
  have he : codedCenterGraph (pullback A) f = {z : Fin 3 → M | Fin.init z ∈ pullback A ∧ z ∈ H} := by
    ext z
    constructor
    · rintro ⟨q,hq,hf⟩
      have hC : Fin.init z ∈ pullback A := hq ▸ q.property
      have heq : (g (Fin.init z)).val = z (Fin.last 2) := by rw [← hq]; exact hf
      refine ⟨hC,?_,heq⟩
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · exact heq ▸ (g (Fin.init z)).property
      · exact hsort (Fin.init z) hC j
    · rintro ⟨hC,_,heq⟩
      exact ⟨⟨Fin.init z,hC⟩,rfl,heq⟩
  have hgraph : DefinableOverBase B (fun _ => .vf) (codedCenterGraph (pullback A) f) := by
    rw [he]
    exact hdef.inter_real_preimage (fun _ => .vf) H hHd Fin.castSucc
  refine ⟨f,hfmem,hgraph,?_⟩
  intro q u heq
  apply congrArg Subtype.val
  apply hgeq
  rw [hD,hD]
  exact congrArg (fun P : Set M => {x : VFType (M := M) | x.val ∈ P}) heq


/-- Open-ball centers from one finite real-base definable hitting set,
on the actual quotient and with the complete same-base code graph. The
construction is adapted from GammaClosedBallCenters. -/
theorem open_centers_from_real_hitting_set (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M))
    (A : Set (OpenBall M)) 
    (hdef : DefinableOverBase B (fun _ => .vf) (pullback A))
    (R : Finset (VFType (M := M)))
    (hRd : DefinableAt B.real .vf (Subtype.val '' (R : Set (VFType (M := M)))))
    (hhit : ∀ D : A, ∃ x ∈ R, x.val ∈ underlying D.val) :
    ∃ f : A → M, (∀ D, f D ∈ underlying D.val) ∧
      DefinableOverBase B (fun _ => .vf) (quotientCenterGraph A f) := by
  obtain ⟨f,hfmem,hfgraph,hfinv⟩ := coded_open_centers_from_hitting_set h00 B A hdef R hRd hhit
  let rep (B : A) : OpenBallCodes.Code M := Classical.choose (Quotient.exists_rep B.val)
  have hrep (B : A) : Quotient.mk _ (rep B) = B.val :=
    Classical.choose_spec (Quotient.exists_rep B.val)
  let repC (B : A) : pullback A := ⟨(rep B).val, (rep B).property, (hrep B).symm ▸ B.property⟩
  let F (B : A) : M := f (repC B)
  have hFc (t : OpenBallCodes.Code M) (ht : Quotient.mk _ t ∈ A) (B : A)
      (he : Quotient.mk _ t = B.val) : F B = f ⟨t.val, t.property, ht⟩ := by
    apply hfinv
    exact congrArg underlying ((hrep B).trans he.symm)
  refine ⟨F, ?_, ?_⟩
  · intro B
    have hh := hfmem (repC B)
    have he : rawBall (rep B).val = underlying B.val := congrArg underlying (hrep B)
    exact he ▸ hh
  · have hgraph : quotientCenterGraph A F = codedCenterGraph (pullback A) f := by
      ext z
      constructor
      · rintro ⟨t, ht, B, he, hF⟩
        have htA : Quotient.mk _ t ∈ A := he.symm ▸ B.property
        exact ⟨⟨t.val, t.property, htA⟩, ht, (hFc t htA B he).symm.trans hF⟩
      · rintro ⟨t, ht, hf⟩
        obtain ⟨hcode, htA⟩ := t.property
        let c : OpenBallCodes.Code M := ⟨t.val, hcode⟩
        let B : A := ⟨Quotient.mk _ c, htA⟩
        exact ⟨c, ht, B, rfl, (hFc c htA B rfl).trans hf⟩
    rw [hgraph]
    exact hfgraph

/-- The proper-open-ball case of Lemma3.13, with the complete graph on
every real code over precisely the original (VF,Gamma)-generated base. -/
theorem lemma_3_13_proper_open {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : Base (M := M)) (hsmall : Cardinal.mk B.real < κ) (hB : VFGammaGeneratedBase B)
    (A : Set (OpenBall M)) (hA : A.Finite)
    (hdef : DefinableOverBase B (fun _ => .vf) (pullback A)) :
    ∃ f : A → M, (∀ D, f D ∈ underlying D.val) ∧
      DefinableOverBase B (fun _ => .vf) (quotientCenterGraph A f) := by
  letI : Fintype A := hA.fintype
  obtain ⟨R,hR,hhit⟩ := finite_hitting_set_of_algebraic_points B
    (fun D : A => underlying D.val)
    (finite_family_algebraic_points hκ hs h00 B hsmall hB A hA hdef)
  exact open_centers_from_real_hitting_set h00 B A hdef R hR hhit

end SpecialTransformations.Section3.OpenBallCodes
