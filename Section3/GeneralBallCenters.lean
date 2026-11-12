module

public import Section3.GammaFiniteMeans
public import Section3.OpenBallCenters

@[expose] public section

/- Component: BallImaginaries -/
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.BallImaginaries
variable {M : Type} [sM : LRV.Structure M]

/-- The closed chart includes singleton and whole-field codes; the open
chart contains proper strict discs. Equal point sets are identified across
both charts as well as within each chart. -/
abbrev Chart (M : Type) [LRV.Structure M] :=
  ClosedBallCodes.ClosedBall M ⊕ OpenBallCodes.OpenBall M

def chartSet : Chart M → Set M :=
  Sum.elim ClosedBallCodes.underlying OpenBallCodes.underlying

def chartSetoid : Setoid (Chart M) where
  r c d := chartSet c = chartSet d
  iseqv := ⟨fun _ => rfl,Eq.symm,Eq.trans⟩

abbrev Ball (M : Type) [LRV.Structure M] := Quotient (chartSetoid (M := M))

def underlying : Ball M → Set M :=
  Quotient.lift chartSet (fun _ _ h => h)

theorem underlying_injective : Function.Injective (underlying (M := M)) := by
  intro D E
  induction D using Quotient.inductionOn with
  | h c =>
    induction E using Quotient.inductionOn with
    | h d => exact fun he => Quotient.sound he

def ofClosed (D : ClosedBallCodes.ClosedBall M) : Ball M := Quotient.mk _ (.inl D)
def ofOpen (D : OpenBallCodes.OpenBall M) : Ball M := Quotient.mk _ (.inr D)

theorem underlying_ofClosed (D : ClosedBallCodes.ClosedBall M) :
    underlying (ofClosed D) = ClosedBallCodes.underlying D := rfl

theorem underlying_ofOpen (D : OpenBallCodes.OpenBall M) :
    underlying (ofOpen D) = OpenBallCodes.underlying D := rfl

variable [hM : M ⊨ Axioms.ACVF]

theorem ofClosed_injective : Function.Injective (ofClosed (M := M)) := by
  intro D E he
  exact ClosedBallCodes.underlying_injective (congrArg underlying he)

theorem ofOpen_injective : Function.Injective (ofOpen (M := M)) := by
  intro D E he
  exact OpenBallCodes.underlying_injective (congrArg underlying he)

def closedFamily (A : Set (Ball M)) : Set (ClosedBallCodes.ClosedBall M) := ofClosed ⁻¹' A
def openFamily (A : Set (Ball M)) : Set (OpenBallCodes.OpenBall M) := ofOpen ⁻¹' A

theorem closedFamily_finite (A : Set (Ball M)) (hA : A.Finite) : (closedFamily A).Finite :=
  hA.preimage ofClosed_injective.injOn

theorem openFamily_finite (A : Set (Ball M)) (hA : A.Finite) : (openFamily A).Finite :=
  hA.preimage ofOpen_injective.injOn

theorem family_cases (A : Set (Ball M)) (D : A) :
    (∃ C : closedFamily A, ofClosed C.val = D.val) ∨
      (∃ O : openFamily A, ofOpen O.val = D.val) := by
  obtain ⟨t,ht⟩ := Quotient.exists_rep D.val
  cases t with
  | inl C =>
    have he : ofClosed C = D.val := ht
    have hC : ofClosed C ∈ A := he.symm ▸ D.property
    exact Or.inl ⟨⟨C,hC⟩,he⟩
  | inr O =>
    have he : ofOpen O = D.val := ht
    have hO : ofOpen O ∈ A := he.symm ▸ D.property
    exact Or.inr ⟨⟨O,hO⟩,he⟩

/-- Every closed disc with an actual VF radius, including radius zero,
is represented in the all-ball quotient. -/
theorem closed_disc_coded {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)
    (a r : VFType (M := M)) :
    ∃ D : Ball M, {x : VFType (M := M) | x.val ∈ underlying D} =
      ValOneEC.closedBall v a (v r) := by
  let q : ClosedBallCodes.Code M := ⟨![a.val,r.val,iVFOne],by
    intro i
    fin_cases i
    · exact a.property
    · exact r.property
    · exact (1 : VFType (M := M)).property⟩
  have hflag : q.val 2 ≠ iVFZero := by
    intro he
    apply (one_ne_zero : (1 : VFType (M := M)) ≠ 0)
    exact Subtype.ext he
  refine ⟨ofClosed (Quotient.mk _ q),?_⟩
  exact ClosedBallCodes.ball_eq_closed v hv q.val q.property hflag

/-- Every proper strict disc with an actual nonzero VF radius is
represented; the degeneracies are supplied by the closed chart. -/
theorem open_disc_coded {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)
    (a r : VFType (M := M)) (hr : r ≠ 0) :
    ∃ D : Ball M, {x : VFType (M := M) | x.val ∈ underlying D} =
      ValOneEC.openBall v a (v r) := by
  let q : OpenBallCodes.Code M := ⟨![a.val,r.val],⟨by
      intro i
      fin_cases i
      · exact a.property
      · exact r.property,by
      intro he
      exact hr (Subtype.ext he)⟩⟩
  refine ⟨ofOpen (Quotient.mk _ q),?_⟩
  exact OpenBallCodes.ball_eq_open v hv q.val q.property

theorem universe_coded : ∃ D : Ball M,
    {x : VFType (M := M) | x.val ∈ underlying D} = Set.univ := by
  let q : ClosedBallCodes.Code M :=
    ⟨(fun _ : Fin 3 => iVFZero),fun _ => (0 : VFType (M := M)).property⟩
  refine ⟨ofClosed (Quotient.mk _ q),?_⟩
  exact ClosedBallCodes.ball_eq_univ q.val q.property rfl

/-- Definability of the entire ball family is the definability of its
full real preimage in each of the two definable code charts. -/
def FamilyDefinableBase (B : GammaParameters.Base (M := M)) (A : Set (Ball M)) : Prop :=
  GammaParameters.DefinableOverBase B (fun _ => .vf)
      (ClosedBallCodes.pullback (closedFamily A)) ∧
    GammaParameters.DefinableOverBase B (fun _ => .vf)
      (OpenBallCodes.pullback (openFamily A))

/-- The single function is on actual balls. Both complete code graphs
therefore give the same value whenever the underlying ball sets agree. -/
def CenterDefinableBase (B : GammaParameters.Base (M := M)) (A : Set (Ball M)) (f : A → M) : Prop :=
  GammaParameters.DefinableOverBase B (fun _ => .vf)
      (ClosedBallCodes.quotientCenterGraph (closedFamily A)
        (fun D => f ⟨ofClosed D.val,D.property⟩)) ∧
    GammaParameters.DefinableOverBase B (fun _ => .vf)
      (OpenBallCodes.quotientCenterGraph (openFamily A)
        (fun D => f ⟨ofOpen D.val,D.property⟩))

end SpecialTransformations.Section3.BallImaginaries

/- Component: BallMeanGraphs -/
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.BallFamilies
open Barycentre RawClosure.Tuple
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n : ℕ}

noncomputable def intersectionMean (R : Finset (VFType (M := M)))
    (D : (Fin n → M) → Set (VFType (M := M))) (q : Fin n → M) : VFType (M := M) :=
  mean (R.filter (fun x => x ∈ D q))

/-- The definability part of the finite-hitting-set proof is independent
of whether the sets in the family are open or closed. This is extracted
from OpenBallCenters and the earlier ClosedCentersFromFiniteSet. -/
theorem intersection_mean_definable (h00 : M ⊨ Axioms.ACVF00) (S : Set M)
    (D : (Fin n → M) → Set (VFType (M := M)))
    (hD : RelationDefinable S (relation D))
    (R : Finset (VFType (M := M)))
    (hR : DefinableAt S .vf (Subtype.val '' (R : Set (VFType (M := M))))) :
    S.DefinableFun LRV (fun q => (intersectionMean R D q).val) := by
  let F (q : Fin n → M) := R.filter (fun x => x ∈ D q)
  have hF : RelationDefinable S (finiteFibreRelation F) := by
    have hr := hR.raw_definable.preimage_comp (Sum.inr : Fin 1 → Fin n ⊕ Fin 1)
    change S.Definable LRV {z : Fin n ⊕ Fin 1 → M |
      (z ∘ Sum.inl,z (.inr 0)) ∈ finiteFibreRelation F}
    convert hD.inter hr using 1
    ext z
    change (∃ x ∈ F (z ∘ Sum.inl), x.val = z (.inr 0)) ↔
      (∃ x ∈ D (z ∘ Sum.inl), x.val = z (.inr 0)) ∧
        z (.inr 0) ∈ Subtype.val '' (R : Set (VFType (M := M)))
    constructor
    · rintro ⟨x,hx,he⟩
      obtain ⟨hxR,hxD⟩ := Finset.mem_filter.mp hx
      exact ⟨⟨x,hxD,he⟩,x,hxR,he⟩
    · rintro ⟨⟨x,hxD,he⟩,y,hyR,hy⟩
      have hyx : y = x := Subtype.ext (hy.trans he.symm)
      exact ⟨x,Finset.mem_filter.mpr ⟨hyx ▸ hyR,hxD⟩,he⟩
  exact mean_definable h00 S F hF R.card (fun q => Finset.card_filter_le _ _)

def normalizedMeanGraph (R : Finset (VFType (M := M)))
    (D : (Fin n → M) → Set (VFType (M := M))) : Set (Fin (n+1) → M) :=
  {z | (∀ i, iVF (z i)) ∧
    GammaParameters.normalizedMean (R.filter (fun x => x ∈ D (Fin.init z))) = z (Fin.last n)}

theorem normalized_mean_graph_definable (h00 : M ⊨ Axioms.ACVF00) (S : Set M)
    (D : (Fin n → M) → Set (VFType (M := M)))
    (hD : @RelationDefinable M (CanonicalStructure.normalize (M := M)) n S (relation D))
    (R : Finset (VFType (M := M)))
    (hR : DefinableAt S .vf (Subtype.val '' (R : Set (VFType (M := M))))) :
    DefinableOver S (fun _ => .vf) (normalizedMeanGraph R D) := by
  let N := CanonicalStructure.normalize (M := M)
  letI := sM
  have hN : @Theory.Model LRV M N Axioms.ACVF := CanonicalStructure.normalized_model hM
  have h00N : @Theory.Model LRV M N Axioms.ACVF00 := normalized_model00 h00
  have hRN := (definableAt_normalize_iff S .vf
    (Subtype.val '' (R : Set (VFType (M := M))))).mpr hR
  let g (q : Fin n → M) := GammaParameters.normalizedMean (R.filter (fun x => x ∈ D q))
  have hg : @Set.DefinableFun M LRV N (Fin n) S g :=
    @intersection_mean_definable M N hN n h00N S D hD R hRN
  apply (definableOver_iff_normalized_raw S (fun _ => .vf) _).mpr
  refine ⟨?_,fun z hz => hz.1⟩
  letI := N
  have hi : S.DefinableMap LRV (Fin.init : (Fin (n+1) → M) → (Fin n → M)) :=
    fun _ => Set.DefinableFun.proj LRV
  have he := (hg.comp hi).ofPred_eq (Set.DefinableFun.proj (L := LRV) (A := S) (i := Fin.last n))
  have hs := Set.definable_iInter_of_finite (fun i : Fin (n+1) =>
    (definableAt_sort S .vf).raw_definable.preimage_comp (fun _ : Fin 1 => i))
  convert hs.inter he using 1
  ext z
  simp only [normalizedMeanGraph,Set.mem_ofPred_eq,Set.mem_inter_iff,Set.mem_iInter,
    Set.mem_preimage,Function.comp_apply]
  rfl

end SpecialTransformations.Section3.BallFamilies

namespace SpecialTransformations.Section3.ClosedBallCodes
open GammaParameters
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

noncomputable def familyMean (R : Finset (VFType (M := M))) (A : Set (ClosedBall M)) (D : A) : M :=
  normalizedMean (R.filter (fun x => x.val ∈ underlying D.val))

def meanGraph (R : Finset (VFType (M := M))) : Set (Fin 4 → M) :=
  BallFamilies.normalizedMeanGraph R (ball (M := M))

theorem meanGraph_definable (h00 : M ⊨ Axioms.ACVF00) (S : Set M)
    (R : Finset (VFType (M := M)))
    (hR : DefinableAt S .vf (Subtype.val '' (R : Set (VFType (M := M))))) :
    DefinableOver S (fun _ => .vf) (meanGraph R) := by
  apply BallFamilies.normalized_mean_graph_definable h00 S (ball (M := M)) _ R hR
  have he : @ball M (CanonicalStructure.normalize (M := M)) = ball (M := M) := by
    funext q
    ext x
    exact Set.ext_iff.mp (rawBall_normalize q) x.val
  have h := @relation_definable M (CanonicalStructure.normalize (M := M)) S
  rwa [he] at h

theorem familyMean_graph_definable_base (h00 : M ⊨ Axioms.ACVF00)
    (B : Base (M := M)) (A : Set (ClosedBall M))
    (hA : DefinableOverBase B (fun _ => .vf) (pullback A))
    (R : Finset (VFType (M := M)))
    (hR : DefinableAt B.real .vf (Subtype.val '' (R : Set (VFType (M := M))))) :
    DefinableOverBase B (fun _ => .vf) (quotientCenterGraph A (familyMean R A)) := by
  have hsort (F : Finset (VFType (M := M))) : iVF (normalizedMean F) :=
    (@Barycentre.mean M (CanonicalStructure.normalize (M := M))
      (CanonicalStructure.normalized_model hM) F).property
  have he : quotientCenterGraph A (familyMean R A) =
      {z : Fin 4 → M | Fin.init z ∈ pullback A ∧ z ∈ meanGraph R} := by
    ext z
    constructor
    · rintro ⟨q,hq,D,hD,hf⟩
      have hqA : Quotient.mk _ q ∈ A := hD.symm ▸ D.property
      have hraw : rawBall q.val = underlying D.val := congrArg underlying hD
      have hmean : normalizedMean (R.filter (fun x => x.val ∈ rawBall (Fin.init z))) = z (Fin.last 3) := by
        rw [← hq,hraw]
        exact hf
      refine ⟨?_,?_,hmean⟩
      · rw [← hq]
        exact ⟨q.property,hqA⟩
      · intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · exact hmean ▸ hsort _
        · change iVF (Fin.init z j)
          rw [← congrFun hq j]
          exact q.property j
    · rintro ⟨⟨hq,hqA⟩,_,hmean⟩
      let q : Code M := ⟨Fin.init z,hq⟩
      let D : A := ⟨Quotient.mk _ q,hqA⟩
      exact ⟨q,rfl,D,rfl,hmean⟩
  rw [he]
  exact hA.inter_real_preimage (fun _ => .vf) (meanGraph R)
    (meanGraph_definable h00 B.real R hR) Fin.castSucc

end SpecialTransformations.Section3.ClosedBallCodes


namespace SpecialTransformations.Section3.OpenBallCodes
open GammaParameters
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

noncomputable def familyMean (R : Finset (VFType (M := M))) (A : Set (OpenBall M)) (D : A) : M :=
  normalizedMean (R.filter (fun x => x.val ∈ underlying D.val))

def meanGraph (R : Finset (VFType (M := M))) : Set (Fin 3 → M) :=
  BallFamilies.normalizedMeanGraph R (ball (M := M))

theorem meanGraph_definable (h00 : M ⊨ Axioms.ACVF00) (S : Set M)
    (R : Finset (VFType (M := M)))
    (hR : DefinableAt S .vf (Subtype.val '' (R : Set (VFType (M := M))))) :
    DefinableOver S (fun _ => .vf) (meanGraph R) := by
  apply BallFamilies.normalized_mean_graph_definable h00 S (ball (M := M)) _ R hR
  have he : @ball M (CanonicalStructure.normalize (M := M)) = ball (M := M) := by
    funext q
    ext x
    exact Set.ext_iff.mp (rawBall_normalize q) x.val
  have h := @relation_definable M (CanonicalStructure.normalize (M := M)) S
  rwa [he] at h

theorem familyMean_graph_definable_base (h00 : M ⊨ Axioms.ACVF00)
    (B : Base (M := M)) (A : Set (OpenBall M))
    (hA : DefinableOverBase B (fun _ => .vf) (pullback A))
    (R : Finset (VFType (M := M)))
    (hR : DefinableAt B.real .vf (Subtype.val '' (R : Set (VFType (M := M))))) :
    DefinableOverBase B (fun _ => .vf) (quotientCenterGraph A (familyMean R A)) := by
  have hsort (F : Finset (VFType (M := M))) : iVF (normalizedMean F) :=
    (@Barycentre.mean M (CanonicalStructure.normalize (M := M))
      (CanonicalStructure.normalized_model hM) F).property
  have he : quotientCenterGraph A (familyMean R A) =
      {z : Fin 3 → M | Fin.init z ∈ pullback A ∧ z ∈ meanGraph R} := by
    ext z
    constructor
    · rintro ⟨q,hq,D,hD,hf⟩
      have hqA : Quotient.mk _ q ∈ A := hD.symm ▸ D.property
      have hraw : rawBall q.val = underlying D.val := congrArg underlying hD
      have hmean : normalizedMean (R.filter (fun x => x.val ∈ rawBall (Fin.init z))) = z (Fin.last 2) := by
        rw [← hq,hraw]
        exact hf
      refine ⟨?_,?_,hmean⟩
      · rw [← hq]
        exact ⟨q.property,hqA⟩
      · intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · exact hmean ▸ hsort _
        · change iVF (Fin.init z j)
          rw [← congrFun hq j]
          exact q.property.1 j
    · rintro ⟨⟨hq,hqA⟩,_,hmean⟩
      let q : Code M := ⟨Fin.init z,hq⟩
      let D : A := ⟨Quotient.mk _ q,hqA⟩
      exact ⟨q,rfl,D,rfl,hmean⟩
  rw [he]
  exact hA.inter_real_preimage (fun _ => .vf) (meanGraph R)
    (meanGraph_definable h00 B.real R hR) Fin.castSucc

end SpecialTransformations.Section3.OpenBallCodes

/- Component: BallMeanContainment -/
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.ClosedBallCodes
open GammaParameters
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem normalized_mean_mem (h00 : M ⊨ Axioms.ACVF00) (D : ClosedBall M)
    (F : Finset (VFType (M := M))) (hne : F.Nonempty)
    (hF : ∀ x ∈ F, x.val ∈ underlying D) : normalizedMean F ∈ underlying D := by
  obtain ⟨q,hq⟩ := Quotient.exists_rep D
  let N := CanonicalStructure.normalize (M := M)
  letI := sM
  have hN : @Theory.Model LRV M N Axioms.ACVF := CanonicalStructure.normalized_model hM
  have h00N : @Theory.Model LRV M N Axioms.ACVF00 := normalized_model00 h00
  obtain ⟨Γ,hΓ,v,hv⟩ := @VFValued.exists_valuation_predV M N hN
  letI := hΓ
  have hFN (x : VFType (M := M)) (hx : x ∈ F) : x ∈ @ball M N q.val := by
    have hh := hF x hx
    rw [← hq] at hh
    change x.val ∈ rawBall q.val at hh
    rw [← rawBall_normalize q.val] at hh
    exact hh
  have hm : (@Barycentre.mean M N hN F) ∈ @ball M N q.val := by
    by_cases hz : q.val 2 = @iVFZero M N
    · rw [@ball_eq_univ M N hN q.val q.property hz]
      trivial
    · have he := @ball_eq_closed M N hN Γ hΓ v hv q.val q.property hz
      rw [he]
      apply @Barycentre.mean_mem_closedDisc M N hN Γ hΓ v hv h00N F hne
        (⟨q.val 0,q.property 0⟩ : VFType (M := M))
        (↑(OrderDual.toDual (v (⟨q.val 1,q.property 1⟩ : VFType (M := M)))))
      intro x hx
      have hh := hFN x hx
      rw [he] at hh
      exact hh
  have hmRaw : normalizedMean F ∈ @rawBall M N q.val := hm
  rw [rawBall_normalize q.val] at hmRaw
  rw [← hq]
  exact hmRaw

end SpecialTransformations.Section3.ClosedBallCodes

namespace SpecialTransformations.Section3.OpenBallCodes
open GammaParameters
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem normalized_mean_mem (h00 : M ⊨ Axioms.ACVF00) (D : OpenBall M)
    (F : Finset (VFType (M := M))) (hne : F.Nonempty)
    (hF : ∀ x ∈ F, x.val ∈ underlying D) : normalizedMean F ∈ underlying D := by
  obtain ⟨q,hq⟩ := Quotient.exists_rep D
  let N := CanonicalStructure.normalize (M := M)
  letI := sM
  have hN : @Theory.Model LRV M N Axioms.ACVF := CanonicalStructure.normalized_model hM
  have h00N : @Theory.Model LRV M N Axioms.ACVF00 := normalized_model00 h00
  have hz : @iVFZero M N = @iVFZero M sM := CanonicalStructure.sortZero_normalize .vf
  have hqN : @Proper M N q.val := ⟨q.property.1,fun he => q.property.2 (he.trans hz)⟩
  obtain ⟨Γ,hΓ,v,hv⟩ := @VFValued.exists_valuation_predV M N hN
  letI := hΓ
  let a : VFType (M := M) := ⟨q.val 0,q.property.1 0⟩
  let r : VFType (M := M) := ⟨q.val 1,q.property.1 1⟩
  have hr : v r ≠ 0 := (v.ne_zero_iff).mpr (@radius_ne_zero M N hN q.val hqN)
  have he : @ball M N q.val = Balls.openDisc v a (Balls.openRadius (v r) hr) := by
    rw [@ball_eq_open M N hN Γ hΓ v hv q.val hqN]
    rfl
  have hFN (x : VFType (M := M)) (hx : x ∈ F) : x ∈ @ball M N q.val := by
    have hh := hF x hx
    rw [← hq] at hh
    change x.val ∈ rawBall q.val at hh
    rw [← rawBall_normalize q.val] at hh
    exact hh
  have hm : (@Barycentre.mean M N hN F) ∈ @ball M N q.val := by
    rw [he]
    apply @Barycentre.mean_mem_openDisc M N hN Γ hΓ v hv h00N F hne a
      (Balls.openRadius (v r) hr)
    intro x hx
    rw [← he]
    exact hFN x hx
  have hmRaw : normalizedMean F ∈ @rawBall M N q.val := hm
  rw [rawBall_normalize q.val] at hmRaw
  rw [← hq]
  exact hmRaw

end SpecialTransformations.Section3.OpenBallCodes

/- Component: GeneralBallCenters -/
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.BallImaginaries
open GammaParameters
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem closed_center_image_definable (B : Base (M := M))
    (A : Set (ClosedBallCodes.ClosedBall M)) (hA : A.Finite) (c : A → M)
    (hc : DefinableOverBase B (fun _ => .vf) (ClosedBallCodes.quotientCenterGraph A c)) :
    DefinableAtBase B .vf (Set.range c) ∧ (Set.range c).Finite := by
  have hd := hc.image_real (fun _ : Fin 1 => Fin.last 3)
  refine ⟨?_,?_⟩
  · change DefinableOverBase B (fun _ : Fin 1 => .vf) {z | z 0 ∈ Set.range c}
    convert hd using 1
    all_goals try rfl
    ext z
    constructor
    · rintro ⟨D,hD⟩
      obtain ⟨q,hq⟩ := Quotient.exists_rep D.val
      let w : Fin 4 → M := Fin.snoc q.val (c D)
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

/-- Closed and proper-open charts cover the actual ball quotient. Each
ball in a finite same-base family contains a same-base VF-algebraic point. -/
theorem finite_family_algebraic_points {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : Base (M := M)) (hsmall : Cardinal.mk B.real < κ) (hB : VFGammaGeneratedBase B)
    (A : Set (Ball M)) (hA : A.Finite) (hdef : FamilyDefinableBase B A) :
    ∀ D : A, ∃ x : VFType (M := M), AlgebraicAtBase B .vf x.val ∧ x.val ∈ underlying D.val := by
  obtain ⟨c,hcMem,hcDef⟩ := lemma_3_10_gamma_base h00 B (closedFamily A)
    (closedFamily_finite A hA) hdef.1
  obtain ⟨hcd,hcf⟩ := closed_center_image_definable B (closedFamily A)
    (closedFamily_finite A hA) c hcDef
  have ho := OpenBallCodes.finite_family_algebraic_points hκ hs h00 B hsmall hB
    (openFamily A) (openFamily_finite A hA) hdef.2
  intro D
  rcases family_cases A D with ⟨C,hC⟩ | ⟨O,hO⟩
  · let x : VFType (M := M) := ⟨c C,hcd.proper _ (Set.mem_range_self C)⟩
    refine ⟨x,⟨Set.range c,hcd,hcf,Set.mem_range_self C⟩,?_⟩
    rw [← hC]
    exact hcMem C
  · obtain ⟨x,hxAlg,hx⟩ := ho O
    refine ⟨x,hxAlg,?_⟩
    rw [← hO]
    exact hx

noncomputable def familyMean (R : Finset (VFType (M := M))) (A : Set (Ball M)) (D : A) : M :=
  normalizedMean (R.filter (fun x => x.val ∈ underlying D.val))

theorem familyMean_definable_base (h00 : M ⊨ Axioms.ACVF00)
    (B : Base (M := M)) (A : Set (Ball M)) (hdef : FamilyDefinableBase B A)
    (R : Finset (VFType (M := M)))
    (hR : DefinableAt B.real .vf (Subtype.val '' (R : Set (VFType (M := M))))) :
    CenterDefinableBase B A (familyMean R A) := by
  constructor
  · exact ClosedBallCodes.familyMean_graph_definable_base h00 B (closedFamily A) hdef.1 R hR
  · exact OpenBallCodes.familyMean_graph_definable_base h00 B (openFamily A) hdef.2 R hR

theorem familyMean_mem (h00 : M ⊨ Axioms.ACVF00) (A : Set (Ball M))
    (R : Finset (VFType (M := M)))
    (hhit : ∀ D : A, ∃ x ∈ R, x.val ∈ underlying D.val) :
    ∀ D : A, familyMean R A D ∈ underlying D.val := by
  intro D
  let F := R.filter (fun x => x.val ∈ underlying D.val)
  have hne : F.Nonempty := by
    obtain ⟨x,hxR,hxD⟩ := hhit D
    exact ⟨x,Finset.mem_filter.mpr ⟨hxR,hxD⟩⟩
  have hF (x : VFType (M := M)) (hx : x ∈ F) : x.val ∈ underlying D.val :=
    (Finset.mem_filter.mp hx).2
  change normalizedMean F ∈ underlying D.val
  rcases family_cases A D with ⟨C,hC⟩ | ⟨O,hO⟩
  · have hh := ClosedBallCodes.normalized_mean_mem h00 C.val F hne (fun x hx => by
      have hh := hF x hx
      rw [← hC] at hh
      exact hh)
    rw [← hC]
    exact hh
  · have hh := OpenBallCodes.normalized_mean_mem h00 O.val F hne (fun x hx => by
      have hh := hF x hx
      rw [← hO] at hh
      exact hh)
    rw [← hO]
    exact hh

/-- Lemma3.13 on actual balls: one center function, including closed and
proper-open discs, singletons and the whole field, with both complete code
graphs definable over the original (VF,Gamma)-generated base. -/
theorem lemma_3_13 {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : Base (M := M)) (hsmall : Cardinal.mk B.real < κ) (hB : VFGammaGeneratedBase B)
    (A : Set (Ball M)) (hA : A.Finite) (hdef : FamilyDefinableBase B A) :
    ∃ f : A → M, (∀ D, f D ∈ underlying D.val) ∧ CenterDefinableBase B A f := by
  letI : Fintype A := hA.fintype
  obtain ⟨R,hR,hhit⟩ := finite_hitting_set_of_algebraic_points B
    (fun D : A => underlying D.val) (finite_family_algebraic_points hκ hs h00 B hsmall hB A hA hdef)
  exact ⟨familyMean R A,familyMean_mem h00 A R hhit,familyMean_definable_base h00 B A hdef R hR⟩

end SpecialTransformations.Section3.BallImaginaries
