module

public import Section9.GenericDifferentiation
public import Section9.MixedJacobian
public import Section3.SmallFiniteParameters
public import Section4.FiniteCorrespondence

@[expose] public section

/-! Generic differentiation on a fixed RV fibre. Naming the two RV
labels leaves the VF parameter field unchanged. The local branch is
extended by zero to use the generic VF continuity theorem. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language Filter Topology MvPolynomial
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8
open SpecialTransformations.DefinableGeometry

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r s : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VFType (M := M)) G]

local notation "VF" => VFType (M := M)
local notation "V" => Fin n → VF

set_option maxHeartbeats 450000 in
/-- The fixed-label derivative at a VF-independent point is computed
by simple equations over the original VF parameter field. -/
theorem mixedDifferentiableAt_of_independent_of_simple_equations [CharZero VF]
    (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    {S : Set M} (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A : DefSet (rawMixedSpace (M := M) n r) S}
    {B : DefSet (rawMixedSpace (M := M) n s) S} (f : Map A B) (p : A)
    (hi : AlgebraicIndependent (vfParameterField S) p.val.1)
    (equations : Fin n → MvPolynomial (Fin n ⊕ Unit) (vfParameterField S))
    (hP : ∀ j, aeval (Sum.elim p.val.1 (fun _ => (f p).val.1 j)) (equations j) = 0)
    (hP' : ∀ j, aeval (Sum.elim p.val.1 (fun _ => (f p).val.1 j))
      (pderiv (Sum.inr ()) (equations j)) ≠ 0) :
    HasMixedVFDerivativeAt f p
      (LinearMap.pi fun j => implicitScalarSlope (equations j) (Sum.elim p.val.1 (fun _ => (f p).val.1 j))) := by
  classical
  let a := p.val.1
  let t := p.val.2
  let u := (f p).val.2
  let T := (S ∪ Set.range (rvValues t)) ∪ Set.range (rvValues u)
  have hsmallT := small_union_range hκ _ (small_union_range hκ S hsmall (rvValues t)) (rvValues u)
  have hfield : vfParameterField T = vfParameterField S := by
    dsimp only [T]
    rw [vfParameterField_union_rv _ _ (by rintro _ ⟨i, rfl⟩; exact (u i).property),
      vfParameterField_union_rv _ _ (by rintro _ ⟨i, rfl⟩; exact (t i).property)]
  have hInd : AlgebraicIndependent (vfParameterField T) a :=
    Eq.mpr (congrArg (fun E : Subfield VF => AlgebraicIndependent E a) hfield) hi
  let fill (z : Fin n ⊕ Fin n → M) : (Fin n ⊕ Fin r) ⊕ (Fin n ⊕ Fin s) → M :=
    Sum.elim (Sum.elim (z ∘ Sum.inl) (rvValues t)) (Sum.elim (z ∘ Sum.inr) (rvValues u))
  have hfill : T.DefinableMap LRV fill := by
    rintro ((i | i) | (i | i))
    · exact Set.DefinableFun.proj LRV
    · exact LRV.definableFun_const _ (Or.inl (Or.inr (Set.mem_range_self i)))
    · exact Set.DefinableFun.proj LRV
    · exact LRV.definableFun_const _ (Or.inr (Set.mem_range_self i))
  let P := rawMixedSpace (M := M) n r
  let Q := rawMixedSpace (M := M) n s
  let H := fill ⁻¹' P.relation Q f.graph
  have hH : T.Definable LRV H := by
    have hG : S.Definable LRV (P.relation Q f.graph) := f.graph_definable
    exact Set.Definable.preimage_map
      hfill (Set.Definable.mono hG (Set.subset_union_left.trans Set.subset_union_left))
  let D (x : V) : Prop := ∃ hx : (x, t) ∈ A.carrier, (f ⟨(x, t), hx⟩).val.2 = u
  let F (x : V) : V := if h : D x then (f ⟨(x, t), h.choose⟩).val.1 else 0
  have hF_mem (x : V) (hx : D x) :
      (f ⟨(x, t), hx.choose⟩).val = (F x, u) := by
    rw [show F x = (f ⟨(x, t), hx.choose⟩).val.1 from dif_pos hx]
    exact Prod.ext rfl hx.choose_spec
  have hmem (x y : V) :
      Sum.elim (vfValues x) (vfValues y) ∈ H ↔ D x ∧ y = F x := by
    have he : fill (Sum.elim (vfValues x) (vfValues y)) =
        Sum.elim (mixedValues (x, t)) (mixedValues (y, u)) := by
      funext i
      rcases i with ((i | i) | (i | i)) <;> rfl
    change fill _ ∈ P.relation Q f.graph ↔ _
    rw [he]
    change (∃ hp : mixedValues (x,t) ∈ P.domain, ∃ hq : mixedValues (y,u) ∈ Q.domain,
      f.graph (P.decode ⟨mixedValues (x,t), hp⟩) (Q.decode ⟨mixedValues (y,u), hq⟩)) ↔ _
    simp only [P, Q, decode_mixedValues]
    constructor
    · rintro ⟨_, _, q, hqx, hqy⟩
      have hxA : (x,t) ∈ A.carrier := hqx ▸ q.property
      have heq : q = ⟨(x,t), hxA⟩ := Subtype.ext hqx
      rw [heq] at hqy
      have hlabel := congrArg (fun q : V × (Fin s → CanonicalRV.RVSort M) => q.2) hqy
      have hx : D x := ⟨hxA, hlabel⟩
      exact ⟨hx, (congrArg Prod.fst hqy).symm.trans
        (congrArg Prod.fst (hF_mem x hx))⟩
    · rintro ⟨hx, rfl⟩
      exact ⟨mixedValues_mem_domain _, mixedValues_mem_domain _, ⟨(x,t), hx.choose⟩,
        rfl, hF_mem x hx⟩
  let X := (fun z : Fin n ⊕ Fin n → M => z ∘ Sum.inl) '' H
  have hX : T.Definable LRV X := hH.image_comp Sum.inl
  have hTyped (z : Fin n ⊕ Fin n → M) (hz : z ∈ H) :
      ∃ x y : V, z = Sum.elim (vfValues x) (vfValues y) := by
    obtain ⟨hx, hy, _⟩ := hz
    let x := (P.decode ⟨fill z ∘ Sum.inl, hx⟩).1
    let y := (Q.decode ⟨fill z ∘ Sum.inr, hy⟩).1
    refine ⟨x, y, ?_⟩
    funext i
    rcases i with (i | i)
    · exact (congrFun (mixedValues_decode ⟨fill z ∘ Sum.inl, hx⟩) (.inl i)).symm
    · exact (congrFun (mixedValues_decode ⟨fill z ∘ Sum.inr, hy⟩) (.inl i)).symm
  have hXmem (x : V) : vfValues x ∈ X ↔ D x := by
    constructor
    · rintro ⟨z, hz, he⟩
      obtain ⟨x', y, rfl⟩ := hTyped z hz
      have hxx : x' = x := vfValues_injective he
      exact hxx ▸ ((hmem x' y).mp hz).1
    · intro hx
      exact ⟨_, (hmem x (F x)).mpr ⟨hx, rfl⟩, rfl⟩
  have hG : T.Definable LRV (vfGraph F) := by
    let Z := {z : Fin n ⊕ Fin n → M |
      z ∘ Sum.inl ∈ vfRawUniverse n ∧ z ∘ Sum.inl ∉ X ∧ ∀ i, z (.inr i) = iVFZero}
    have hZ : T.Definable LRV Z := by
      have hzero : T.DefinableFun LRV (fun _ : Fin n ⊕ Fin n → M => iVFZero) :=
        DefinableConstants.constant (DefinableConstants.function_symbol (L := LRV)
          Fn.vfZero Fin.elim0 (fun i => i.elim0))
      have hz (i : Fin n) := (Set.DefinableFun.proj LRV (i := Sum.inr i)).ofPred_eq hzero
      have he : Z = {z | z ∘ Sum.inl ∈ vfRawUniverse n} ∩ {z | z ∘ Sum.inl ∉ X} ∩
          (⋂ i : Fin n, {z | z (.inr i) = iVFZero}) := by
        ext z
        simp [Z, and_assoc]
      rw [he]
      exact (((vfRawUniverse_definable T n).preimage_comp Sum.inl).inter
        (hX.compl.preimage_comp Sum.inl)).inter (Set.definable_iInter_of_finite hz)
    convert hH.union hZ using 1
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      by_cases hx : D x
      · exact Or.inl ((hmem x (F x)).mpr ⟨hx, rfl⟩)
      · exact Or.inr ⟨fun i => (x i).property, (hXmem x).not.mpr hx, fun i => by
          change (F x i).val = _
          rw [show F x = 0 from dif_neg hx]
          rfl⟩
    · rintro (h | ⟨hVF, hx, hzero⟩)
      · obtain ⟨x, y, rfl⟩ := hTyped z h
        exact ⟨x, by rw [((hmem x y).mp h).2]⟩
      · let x : V := fun i => ⟨z (.inl i), hVF i⟩
        have hn : ¬ D x := (hXmem x).not.mp hx
        refine ⟨x, ?_⟩
        change Sum.elim (vfValues x) (vfValues (F x)) = z
        rw [show F x = 0 from dif_neg hn]
        funext i
        rcases i with (i | i)
        · rfl
        · exact (hzero i).symm
  have hDa : D a := ⟨p.property, rfl⟩
  have haF : F a = (f p).val.1 := by
    rw [show F a = (f ⟨(a,t), hDa.choose⟩).val.1 from dif_pos hDa]
    rfl
  have hXsort := raw_definableOver_sorted hc T (fun _ => .vf) X hX (by
    rintro _ ⟨z, hz, rfl⟩ i
    obtain ⟨x, y, rfl⟩ := hTyped z hz
    exact (x i).property)
  have hNear := independent_definable_mem_nhds hv T X hXsort a hInd ((hXmem a).mpr hDa)
  obtain ⟨rad, hrad, hsub⟩ := exists_uniformBall_subset_of_mem_nhds hv a hNear
  let ρ := Values.gammaOf (CanonicalRV.encodedRv rad)
    (fun h => hrad ((CanonicalRV.encodedRv_zero_iff rad).mp h))
  have hChart : IsVFChartAt f p F := by
    refine ⟨ρ, fun x hx => ?_⟩
    have hval : Values.vfValueHom rad = ρ.val := rfl
    have hx' := (mem_vfBall_iff_gammaUniformBall a x ρ).mp hx
    rw [gammaUniformBall_eq_uniformBall _ ρ rad hrad hval] at hx'
    have hxD := (hXmem x).mp (hsub hx')
    exact ⟨hxD.choose, hF_mem x hxD⟩
  refine ⟨F, hChart, ?_⟩
  have hDer (E : Subfield VF) (P' : Fin n → MvPolynomial (Fin n ⊕ Unit) E)
      (hE : E = vfParameterField T)
      (hroot : ∀ j, aeval (Sum.elim a (fun _ => F a j)) (P' j) = 0)
      (hsimple : ∀ j, aeval (Sum.elim a (fun _ => F a j)) (pderiv (Sum.inr ()) (P' j)) ≠ 0) :
      HasVFDerivativeAt F a
        (LinearMap.pi fun j => implicitScalarSlope (P' j) (Sum.elim a (fun _ => F a j))) := by
    subst E
    exact hasVFDerivativeAt_of_independent_of_simple_equations hc hκ hs hsmallT hv F hG a hInd P' hroot hsimple
  simpa only [haF] using hDer (vfParameterField S) equations hfield.symm
    (by simpa only [haF] using hP) (by simpa only [haF] using hP')

/-- A definable mixed map has a differentiable fixed-label chart at a
VF-independent point. -/
theorem mixedDifferentiableAt_of_independent [CharZero VF]
    (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    {S : Set M} (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A : DefSet (rawMixedSpace (M := M) n r) S}
    {B : DefSet (rawMixedSpace (M := M) n s) S} (f : Map A B) (p : A)
    (hi : AlgebraicIndependent (vfParameterField S) p.val.1) :
    ∃ L : V →ₗ[VF] V, HasMixedVFDerivativeAt f p L := by
  choose P hP hP' using fun j => exists_simpleRoot_equation_of_tupleField _ p.val.1 ((f p).val.1 j)
    (map_output_vf_coordinate_isAlgebraic hc f p j)
  exact ⟨_, mixedDifferentiableAt_of_independent_of_simple_equations hc hκ hs hsmall hv f p hi P hP hP'⟩

/-- A finite-to-one map of equal VF arity sends VF-independent points to
VF-independent points, even when the auxiliary label arities differ. -/
theorem independent_map_of_finiteFibres
    (hc : CanonicalStructure.IsCanonical (M := M)) {S : Set M}
    {A : DefSet (rawMixedSpace (M := M) n r) S}
    {B : DefSet (rawMixedSpace (M := M) n s) S} (f : Map A B)
    (hf : f.FiniteFibres) (p : A) (hp : AlgebraicIndependent (vfParameterField S) p.val.1) :
    AlgebraicIndependent (vfParameterField S) (f p).val.1 := by
  let P := rawMixedSpace (M := M) n r
  let Q := rawMixedSpace (M := M) n s
  have hrel := f.graph_definable.swap P Q
  have hfin : {x | f.graph x (f p).val}.Finite := by
    apply ((hf (f p)).image Subtype.val).subset
    rintro x ⟨q, hqx, hq⟩
    exact ⟨q, Subtype.ext hq, hqx⟩
  have halg (j : Fin n) := finite_relation_vf_coordinate_isAlgebraic hc hrel
    (f p).val p.val ⟨p, rfl, rfl⟩ hfin j
  have hle := tupleField_trdeg_mono_of_isAlgebraic (vfParameterField S) (f p).val.1 p.val.1 halg
  have he : vfTupleTrdeg S p.val.1 = (n : Cardinal) :=
    (tupleField_trdeg_eq_arity_iff (vfParameterField S) p.val.1).mpr hp
  change vfTupleTrdeg S p.val.1 ≤ vfTupleTrdeg S (f p).val.1 at hle
  rw [he] at hle
  exact (tupleField_trdeg_eq_arity_iff (vfParameterField S) (f p).val.1).mp
    ((vfTupleTrdeg_le_arity S (f p).val.1).antisymm hle)

/-- The generic-point version of the approved chain rule in Lemma 9.12.
Finite fibres of the first map ensure the second derivative exists at
the image point. -/
theorem mixedVFJacobian_comp_of_independent [CharZero VF]
    (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    {S : Set M} (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {t : ℕ}
    {A : DefSet (rawMixedSpace (M := M) n r) S}
    {B : DefSet (rawMixedSpace (M := M) n s) S}
    {C : DefSet (rawMixedSpace (M := M) n t) S}
    (f : Map A B) (g : Map B C) (hf : f.FiniteFibres)
    (p : A) (hp : AlgebraicIndependent (vfParameterField S) p.val.1) :
    ∃ J K : VF, HasMixedVFJacobianAt f p J ∧ HasMixedVFJacobianAt g (f p) K ∧
      HasMixedVFJacobianAt (g ∘ f) p (K * J) := by
  obtain ⟨L, hL⟩ := mixedDifferentiableAt_of_independent hc hκ hs hsmall hv f p hp
  obtain ⟨D, hD⟩ := mixedDifferentiableAt_of_independent hc hκ hs hsmall hv g (f p)
    (independent_map_of_finiteFibres hc f hf p hp)
  exact ⟨_, _, mixedVFJacobian_comp_of_full_derivative hL hD⟩

end SpecialTransformations.Section9
