module

public import Section3.VFDefinableClosure
public import Section3.ClosureBridge
public import Section3.AlgebraicFinite

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

omit hM in
theorem relation_fibre_definable {m : ℕ} (S : Set M)
    (R : Set ((Fin m → M) × M)) (hR : RawClosure.Tuple.RelationDefinable S R)
    (t : Fin m → M) : (S ∪ Set.range t).Definable₁ LRV {b | (t, b) ∈ R} := by
  have hR' := hR.mono (Set.subset_union_left : S ⊆ S ∪ Set.range t)
  let F (x : Fin 1 → M) : Fin m ⊕ Fin 1 → M := Sum.elim t x
  have hF : (S ∪ Set.range t).DefinableMap LRV F := by
    intro i
    cases i with
    | inl j => exact LRV.definableFun_const (Fin 1) (Or.inr (Set.mem_range_self j))
    | inr j => exact Set.DefinableFun.proj LRV
  exact hR'.preimage_map hF

omit hM in
theorem relation_image_definable {m : ℕ} (S : Set M)
    (R : Set ((Fin m → M) × M)) (hR : RawClosure.Tuple.RelationDefinable S R) :
    S.Definable₁ LRV {b | ∃ t, (t, b) ∈ R} := by
  have hR' : S.Definable LRV {x : Fin m ⊕ Fin 1 → M | (x ∘ Sum.inl, x (.inr 0)) ∈ R} := hR
  have hr := (hR'.preimage_comp (Equiv.sumComm (Fin m) (Fin 1))).exists_of_finite
  exact hr

theorem finite_rv_to_vf_relation_image (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) (S : Set M) (hsmall : Cardinal.mk S < κ)
    {m : ℕ} (R : Set ((Fin m → M) × M))
    (hR : RawClosure.Tuple.RelationDefinable S R)
    (hsort : ∀ t b, (t, b) ∈ R → (∀ j, iRV (t j)) ∧ iVF b)
    (hf : ∀ t, {b | (t, b) ∈ R}.Finite) : {b | ∃ t, (t, b) ∈ R}.Finite := by
  apply RawClosure.finite_of_definable_subset_algebraic hs S hsmall _
    (relation_image_definable S R hR)
  rintro b ⟨t, htb⟩
  obtain ⟨ht, hb⟩ := hsort t b htb
  have hraw : RawClosure.AlgebraicOver (S ∪ Set.range t) b :=
    ⟨{b | (t, b) ∈ R}, relation_fibre_definable S R hR t, hf t, htb⟩
  have halg := (algebraicAt_iff_raw hc _ .vf b).mpr ⟨hraw, hb⟩
  let b' : VFType (M := M) := ⟨b, hb⟩
  have he' : _root_.IsAlgebraic (vfParameterField S) b' := by
    apply algebraicAt_vf_isAlgebraic (S ∪ Set.range t) (vfParameterField S) ?_ ⟨b, hb⟩ halg
    intro x hx
    rcases hx with hx | ⟨j, hj⟩
    · exact Subfield.subset_closure hx
    · have hh := CanonicalStructure.sort_unique hM (s := .vf) (t := .rv)
        x.property (hj ▸ ht j)
      cases hh
  exact ((algebraicAt_vf_iff_parameterField S ⟨b, hb⟩).mpr he').raw_finite_witness


/-- Finite-valued RV-to-VF relations have finite image in every output arity.
The base is unchanged and may be any small set. The saturation premise is
genuine small-parameter saturation; no field-base convention is required. -/
theorem finite_rv_to_vf_tuple_relation_image
    (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) (S : Set M) (hsmall : Cardinal.mk S < κ)
    {m n : ℕ} (G : Set (Fin m ⊕ Fin n → M))
    (hG : S.Definable LRV G)
    (hsort : ∀ t y, Sum.elim t y ∈ G → (∀ j, iRV (t j)) ∧ ∀ j, iVF (y j))
    (hf : ∀ t, {y | Sum.elim t y ∈ G}.Finite) :
    {y | ∃ t, Sum.elim t y ∈ G}.Finite := by
  classical
  let R (j : Fin n) : Set ((Fin m → M) × M) :=
    {p | ∃ y : Fin n → M, Sum.elim p.1 y ∈ G ∧ y j = p.2}
  have hR (j : Fin n) : RawClosure.Tuple.RelationDefinable S (R j) := by
    let π : Fin m ⊕ Fin 1 → Fin m ⊕ Fin n := Sum.map id (fun _ => j)
    have he : {x : Fin m ⊕ Fin 1 → M | (x ∘ Sum.inl, x (.inr 0)) ∈ R j} =
        (fun z : Fin m ⊕ Fin n → M => z ∘ π) '' G := by
      ext x
      constructor
      · rintro ⟨y, hy, hj⟩
        refine ⟨Sum.elim (x ∘ Sum.inl) y, hy, ?_⟩
        funext i
        cases i with
        | inl i => rfl
        | inr i => fin_cases i; exact hj
      · rintro ⟨z, hz, hzx⟩
        refine ⟨z ∘ Sum.inr, ?_, congrFun hzx (.inr 0)⟩
        have ht : x ∘ Sum.inl = z ∘ Sum.inl := by
          funext i
          exact (congrFun hzx (.inl i)).symm
        rw [ht, Sum.elim_comp_inl_inr]
        exact hz
    change S.Definable LRV _
    rw [he]
    exact hG.image_comp π
  have hcoord (j : Fin n) : {b | ∃ t, (t, b) ∈ R j}.Finite := by
    apply finite_rv_to_vf_relation_image hc hs S hsmall (R j) (hR j)
    · rintro t b ⟨y, hy, rfl⟩
      exact ⟨(hsort t y hy).1, (hsort t y hy).2 j⟩
    · intro t
      have he : {b | (t, b) ∈ R j} = (fun y : Fin n → M => y j) ''
          {y | Sum.elim t y ∈ G} := by
        ext b
        rfl
      rw [he]
      exact (hf t).image _
  apply (Set.Finite.pi' hcoord).subset
  rintro y ⟨t, hty⟩ j
  exact ⟨t, y, hty, rfl⟩

/-- Corollary 3.5, including arbitrary finite input and output arities and a
partial domain A. Definability means the graph over the original base S. -/
theorem corollary_3_5 (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) (S : Set M) (hsmall : Cardinal.mk S < κ)
    {m n : ℕ} (A : Set (Fin m → M))
    (f : A → Fin n → M) (hA : ∀ t ∈ A, ∀ j, iRV (t j))
    (hf : ∀ t j, iVF (f t j))
    (hgraph : S.Definable LRV {z : Fin m ⊕ Fin n → M |
      ∃ t : A, t.val = z ∘ Sum.inl ∧ f t = z ∘ Sum.inr}) :
    (Set.range f).Finite := by
  let G : Set (Fin m ⊕ Fin n → M) :=
    {z | ∃ t : A, t.val = z ∘ Sum.inl ∧ f t = z ∘ Sum.inr}
  have hsort : ∀ t y, Sum.elim t y ∈ G →
      (∀ j, iRV (t j)) ∧ ∀ j, iVF (y j) := by
    rintro t y ⟨a, hat, hay⟩
    have hat' : a.val = t := hat
    have hay' : f a = y := hay
    exact ⟨hat' ▸ hA a.val a.property, hay' ▸ hf a⟩
  have hfin : ∀ t, {y | Sum.elim t y ∈ G}.Finite := by
    intro t
    apply Set.Subsingleton.finite
    rintro y ⟨a, hat, hay⟩ z ⟨b, hbt, hbz⟩
    have hat' : a.val = t := hat
    have hbt' : b.val = t := hbt
    have hab : a = b := Subtype.ext (hat'.trans hbt'.symm)
    subst b
    exact hay.symm.trans hbz
  have he : Set.range f = {y | ∃ t, Sum.elim t y ∈ G} := by
    ext y
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a.val, a, rfl, rfl⟩
    · rintro ⟨t, a, _, hay⟩
      exact ⟨a, hay⟩
  rw [he]
  exact finite_rv_to_vf_tuple_relation_image hc hs S hsmall G hgraph hsort hfin

end SpecialTransformations.Section3
