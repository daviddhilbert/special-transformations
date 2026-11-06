import Section3.RVGammaAlgebraicity

/- Component: RVExchangeGeometry -/
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.ModelTheory
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem same_scalar_normalized_definable (S : Set M) :
    @Set.Definable₂ M S LRV (CanonicalStructure.normalize (M := M))
      {p | SameScalar p.1 p.2} := by
  have hd := @same_scalar_definable M (CanonicalStructure.normalize (M := M)) S
  have he : {z : Fin 2 → M | @SameScalar M (CanonicalStructure.normalize (M := M)) (z 0) (z 1)} =
      {z | SameScalar (z 0) (z 1)} := Set.ext (fun z => same_scalar_normalize (z 0) (z 1))
  change @Set.Definable M S LRV (CanonicalStructure.normalize (M := M)) (Fin 2)
    {z | SameScalar (z 0) (z 1)}
  exact he ▸ hd

theorem same_scalar_symm (a b : M) : SameScalar a b ↔ SameScalar b a := by
  change (_ ∧ _ ∧ _ ∧ _) ↔ (_ ∧ _ ∧ _ ∧ _)
  tauto

theorem same_scalar_code_left (c d : Code (M := M)) (hcd : value c = value d) (x : M) :
    SameScalar (raw c) x ↔ SameScalar (raw d) x := by
  have hv : values (![c] : Fin 1 → Code (M := M)) = values ![d] := by
    funext i; fin_cases i; exact hcd
  have hh := same_with_codes_iff (![x] : Fin 1 → M) ![c] ![d] hv
  have he : SameScalar x (raw c) ↔ SameScalar x (raw d) := by
    constructor
    · intro hc
      have hc' : Same (![x] : Fin 1 → M) (rawTuple ![c]) := by
        intro i; fin_cases i; exact hc
      exact (hh.mp hc') 0
    · intro hd
      have hd' : Same (![x] : Fin 1 → M) (rawTuple ![d]) := by
        intro i; fin_cases i; exact hd
      exact (hh.mpr hd') 0
  exact (same_scalar_symm _ _).trans (he.trans (same_scalar_symm _ _).symm)

def rawValueFibre (c : Code (M := M)) : Set M := {x | SameScalar (raw c) x}

theorem rawValueFibre_definable (S : Set M) (c : Code (M := M)) :
    DefinableAt (insert (raw c) S) .rv (rawValueFibre c) := by
  let a := raw c
  let T := insert a S
  let X := rawValueFibre c
  have hs := same_scalar_normalized_definable (M := M) T
  have hd : @Set.Definable₁ M T LRV (CanonicalStructure.normalize (M := M)) X := by
    letI := CanonicalStructure.normalize (M := M)
    have hm : T.DefinableMap LRV (fun z : Fin 1 → M => (![a,z 0] : Fin 2 → M)) := by
      intro i
      fin_cases i
      · exact LRV.definableFun_const (Fin 1) (Set.mem_insert a S)
      · exact Set.DefinableFun.proj LRV
    exact hs.preimage_map hm
  exact (definableAt_iff_normalized_raw T .rv X).mpr ⟨hd,fun x hx => hx.2.1.1⟩

theorem rawValueFibre_value (c : Code (M := M)) (t : CanonicalRV.RVSort M)
    (ht : t.val ∈ rawValueFibre c) : Values.vrv t = (value c).val := by
  exact (Values.vrv_eq_iff t c.val).mpr ⟨ht.2.2.2,ht.2.2.1⟩

theorem rawValueFibre_infinite (h00 : M ⊨ Axioms.ACVF00) (c : Code (M := M)) :
    (rawValueFibre c).Infinite := by
  let A : Set (CanonicalRV.RVSort M) := {t | Values.vrv t = (value c).val}
  have hA : A.Infinite := Values.infinite_gamma_fibre h00 (value c)
  have hsub : Subtype.val '' A ⊆ rawValueFibre c := by
    rintro x ⟨t,ht,rfl⟩
    have ht0 : t.val ≠ iRVZero := by
      intro hz
      exact (value c).property (ht.symm.trans ((Values.vrv_eq_infinity_iff t).mpr hz))
    have hcmp := (Values.vrv_eq_iff c.val t).mp ht.symm
    exact ⟨⟨raw_rv c,raw_ne_zero c⟩,⟨t.property,ht0⟩,hcmp⟩
  have himage : (Subtype.val '' A).Infinite := hA.image Subtype.val_injective.injOn
  exact himage.mono hsub

theorem rv_reverse_fibre_definable (S : Set M) (R : M → M → Prop)
    (hR : @Set.Definable₂ M S LRV (CanonicalStructure.normalize (M := M)) {p | R p.1 p.2})
    (hsort : ∀ a b, R a b → iRV a ∧ iRV b) (b : M) :
    DefinableAt (insert b S) .rv {a | R a b} := by
  let C : Set M := {a | R a b}
  have hd : @Set.Definable₁ M (insert b S) LRV (CanonicalStructure.normalize (M := M)) C := by
    letI := CanonicalStructure.normalize (M := M)
    have hm : (insert b S).DefinableMap LRV (fun z : Fin 1 → M => (![z 0,b] : Fin 2 → M)) := by
      intro i
      fin_cases i
      · exact Set.DefinableFun.proj LRV
      · exact LRV.definableFun_const (Fin 1) (Set.mem_insert b S)
    exact (hR.mono (Set.subset_insert b S)).preimage_map hm
  exact (definableAt_iff_normalized_raw (insert b S) .rv C).mpr ⟨hd,fun a ha => (hsort a b ha).1⟩

theorem reverse_value_fibre_dichotomy (S : Set M) (R : M → M → Prop)
    (hR : @Set.Definable₂ M S LRV (CanonicalStructure.normalize (M := M)) {p | R p.1 p.2})
    (hsort : ∀ a b, R a b → iRV a ∧ iRV b) (c : Code (M := M)) (b : M) :
    {x | x ∈ rawValueFibre c ∧ R x b}.Finite ∨
      {x | x ∈ rawValueFibre c ∧ ¬ R x b}.Finite := by
  let T := insert (raw c) S
  have hST : S ⊆ T := Set.subset_insert (raw c) S
  let X := rawValueFibre c
  let C : Set M := {x | x ∈ X ∧ R x b}
  have hX : DefinableAt T .rv X := rawValueFibre_definable S c
  have hRd : @Set.Definable₂ M T LRV (CanonicalStructure.normalize (M := M)) {p | R p.1 p.2} := by
    letI := CanonicalStructure.normalize (M := M)
    exact hR.mono hST
  have hC : DefinableAt (insert b T) .rv C :=
    (hX.mono (Set.subset_insert b T)).inter (rv_reverse_fibre_definable T R hRd hsort b)
  have hh := rv_subset_finite_or_finite_sdiff T (insert b T) X C hX hC
    (fun _ hx => hx.1) (value c) (rawValueFibre_value c)
  rcases hh with hf | hf
  · exact Or.inl hf
  · right
    have he : X \ C = {x | x ∈ X ∧ ¬ R x b} := by
      ext x
      change (x ∈ X ∧ ¬ (x ∈ X ∧ R x b)) ↔ (x ∈ X ∧ ¬ R x b)
      tauto
    exact he ▸ hf

def valueReverseRows (R : M → M → Prop) : Set ((Fin 2 → M) × M) :=
  {p | SameScalar (p.1 0) p.2 ∧ R p.2 (p.1 1)}

theorem valueReverseRows_definable (S : Set M) (R : M → M → Prop)
    (hR : @Set.Definable₂ M S LRV (CanonicalStructure.normalize (M := M)) {p | R p.1 p.2}) :
    @RawClosure.Tuple.RelationDefinable M (CanonicalStructure.normalize (M := M)) 2 S (valueReverseRows R) := by
  let U := valueReverseRows R
  have hs := same_scalar_normalized_definable (M := M) S
  letI := CanonicalStructure.normalize (M := M)
  have hv := definable_binary_at hs (Sum.inl (0 : Fin 2)) (Sum.inr (0 : Fin 1))
  have hr := definable_binary_at hR (Sum.inr (0 : Fin 1)) (Sum.inl (1 : Fin 2))
  change S.Definable LRV {z : Fin 2 ⊕ Fin 1 → M | (z ∘ Sum.inl,z (.inr 0)) ∈ U}
  exact hv.inter hr

/-- First-order counting of a reverse relation within a value class,
with full invariance in its Gamma input. The natural bound is syntax. -/
def reverseBadRelation (S : Set M) (R : M → M → Prop)
    (hR : @Set.Definable₂ M S LRV (CanonicalStructure.normalize (M := M)) {p | R p.1 p.2})
    (hsort : ∀ a b, R a b → iRV a ∧ iRV b) (e : ℕ) : Relation S 1 1 (fun _ => .rv) where
  carrier := {p | (![p.1 0,p.2 0] : Fin 2 → M) ∈ ModelTheory.HasMore (valueReverseRows R) e}
  definable := by
    have hr := valueReverseRows_definable S R hR
    let U := valueReverseRows R
    letI := CanonicalStructure.normalize (M := M)
    have hc := ModelTheory.hasMore_definable S U hr e
    exact hc.preimage_comp (![Sum.inl 0,Sum.inr 0] : Fin 2 → Fin 1 ⊕ Fin 1)
  proper := by
    rintro p ⟨u,hu,hm⟩
    have hh := hm 0
    refine ⟨fun i => ?_,fun i => ?_⟩
    · fin_cases i
      exact hh.1.1
    · fin_cases i
      exact (hsort (u 0) (p.2 0) hh.2).2
  invariant := by
    intro t u htu b
    have hv : value (t 0) = value (u 0) := congrFun htu 0
    change (∃ x : Fin (e+1) → M, Function.Injective x ∧
      ∀ i, SameScalar (raw (t 0)) (x i) ∧ R (x i) (b 0)) ↔
      ∃ x : Fin (e+1) → M, Function.Injective x ∧
      ∀ i, SameScalar (raw (u 0)) (x i) ∧ R (x i) (b 0)
    exact exists_congr (fun x => and_congr Iff.rfl (forall_congr' (fun i =>
      and_congr (same_scalar_code_left (t 0) (u 0) hv (x i)) Iff.rfl)))

theorem reverseBadRelation_fibre_iff (S : Set M) (R : M → M → Prop)
    (hR : @Set.Definable₂ M S LRV (CanonicalStructure.normalize (M := M)) {p | R p.1 p.2})
    (hsort : ∀ a b, R a b → iRV a ∧ iRV b) (e : ℕ) (c : Code (M := M)) (b : M) :
    (![b] : Fin 1 → M) ∈ (reverseBadRelation S R hR hsort e).fibre ![value c] ↔
      ∃ x : Fin (e+1) → M, Function.Injective x ∧
        ∀ i, x i ∈ rawValueFibre c ∧ R (x i) b := by
  have hv : values (![c] : Fin 1 → Code (M := M)) = ![value c] := by
    funext i; fin_cases i; rfl
  exact (reverseBadRelation S R hR hsort e).mem_fibre_iff ![c] ![value c] hv ![b]

end SpecialTransformations.Section3.GammaParameters

/- Component: RVReverseUniform -/
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3.GammaParameters
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem uniform_reverse_value_fibre_bound {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (S : Set M) (hsmall : Cardinal.mk S < κ) (R : M → M → Prop)
    (hR : @Set.Definable₂ M S LRV (CanonicalStructure.normalize (M := M)) {p | R p.1 p.2})
    (hsort : ∀ a b, R a b → iRV a ∧ iRV b) (c : Code (M := M)) :
    ∃ e : ℕ, ∀ b : M, {x | x ∈ rawValueFibre c ∧ R x b}.Finite →
      {x | x ∈ rawValueFibre c ∧ R x b}.ncard ≤ e := by
  let T := insert (raw c) S
  have hST : S ⊆ T := Set.subset_insert (raw c) S
  let X := rawValueFibre c
  let P : Set (Fin 1 → M) := Set.univ
  let U : Set ((Fin 1 → M) × M) := {p | p.2 ∈ X ∧ R p.2 (p.1 0)}
  let V : Set ((Fin 1 → M) × M) := {p | p.2 ∈ X ∧ ¬ R p.2 (p.1 0)}
  have hT : Cardinal.mk T < κ := small_insert hκ S hsmall (raw c)
  have hX : DefinableAt T .rv X := rawValueFibre_definable S c
  have hXd := (definableAt_iff_normalized_raw T .rv X).mp hX |>.1
  have hRd : @Set.Definable₂ M T LRV (CanonicalStructure.normalize (M := M)) {p | R p.1 p.2} := by
    letI := CanonicalStructure.normalize (M := M)
    exact hR.mono hST
  have hU : @RawClosure.Tuple.RelationDefinable M (CanonicalStructure.normalize (M := M)) 1 T U := by
    letI := CanonicalStructure.normalize (M := M)
    have hx := hXd.preimage_comp (Sum.inr : Fin 1 → Fin 1 ⊕ Fin 1)
    have hr := hRd.preimage_comp (![Sum.inr 0,Sum.inl 0] : Fin 2 → Fin 1 ⊕ Fin 1)
    exact hx.inter hr
  have hV : @RawClosure.Tuple.RelationDefinable M (CanonicalStructure.normalize (M := M)) 1 T V := by
    letI := CanonicalStructure.normalize (M := M)
    have hx := hXd.preimage_comp (Sum.inr : Fin 1 → Fin 1 ⊕ Fin 1)
    have hr := hRd.preimage_comp (![Sum.inr 0,Sum.inl 0] : Fin 2 → Fin 1 ⊕ Fin 1)
    exact hx.inter hr.compl
  have hP : @Set.Definable M T LRV (CanonicalStructure.normalize (M := M)) (Fin 1) P := by
    letI := CanonicalStructure.normalize (M := M)
    exact Set.definable_univ
  have hside (a : Fin 1 → M) (_ : a ∈ P) :
      {x | (a,x) ∈ U}.Finite ∨ {x | (a,x) ∈ V}.Finite :=
    reverse_value_fibre_dichotomy S R hR hsort c (a 0)
  have hinf (a : Fin 1 → M) (_ : a ∈ P) : ({x | (a,x) ∈ U} ∪ {x | (a,x) ∈ V}).Infinite := by
    have he : {x | (a,x) ∈ U} ∪ {x | (a,x) ∈ V} = X := by
      ext x
      change ((x ∈ X ∧ R x (a 0)) ∨ (x ∈ X ∧ ¬ R x (a 0))) ↔ x ∈ X
      tauto
    rw [he]
    exact rawValueFibre_infinite h00 c
  obtain ⟨e,he⟩ := @RawClosure.Tuple.uniform_finite_fibres_from_dichotomy M
    (CanonicalStructure.normalize (M := M)) 1 κ hs.normalize T hT P hP U V hU hV hside hinf
  exact ⟨e,fun b hb => (he (fun _ => b) (Set.mem_univ _)).1 hb⟩

end SpecialTransformations.Section3.GammaParameters

/- Component: RVReverseFiniteness -/
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3.GammaParameters
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem uniform_forward_relation_bound {κ : Cardinal} (hs : Saturated M κ)
    (S : Set M) (hsmall : Cardinal.mk S < κ) (R : M → M → Prop)
    (hR : @Set.Definable₂ M S LRV (CanonicalStructure.normalize (M := M)) {p | R p.1 p.2})
    (hfinite : ∀ a, {b | R a b}.Finite) :
    ∃ d : ℕ, ∀ a, {b | R a b}.Finite ∧ {b | R a b}.ncard ≤ d := by
  let U : Set ((Fin 1 → M) × M) := {p | R (p.1 0) p.2}
  have hd : @RawClosure.Tuple.RelationDefinable M (CanonicalStructure.normalize (M := M)) 1 S U := by
    letI := CanonicalStructure.normalize (M := M)
    exact hR.preimage_comp (![Sum.inl 0,Sum.inr 0] : Fin 2 → Fin 1 ⊕ Fin 1)
  have hp : @Set.Definable M S LRV (CanonicalStructure.normalize (M := M)) (Fin 1) Set.univ := by
    letI := CanonicalStructure.normalize (M := M)
    exact Set.definable_univ
  obtain ⟨d,he⟩ := @RawClosure.Tuple.uniform_finite_rows M (CanonicalStructure.normalize (M := M)) 1 κ
    hs.normalize S hsmall Set.univ hp U hd (fun a _ => hfinite (a 0))
  exact ⟨d,fun a => he (fun _ => a) (Set.mem_univ _)⟩

theorem reverseBadRelation_finite (h00 : M ⊨ Axioms.ACVF00)
    (S : Set M) (R : M → M → Prop)
    (hR : @Set.Definable₂ M S LRV (CanonicalStructure.normalize (M := M)) {p | R p.1 p.2})
    (hsort : ∀ a b, R a b → iRV a ∧ iRV b) (d e : ℕ)
    (hforward : ∀ a, {b | R a b}.Finite ∧ {b | R a b}.ncard ≤ d)
    (c : Code (M := M))
    (he : ∀ b, {x | x ∈ rawValueFibre c ∧ R x b}.Finite →
      {x | x ∈ rawValueFibre c ∧ R x b}.ncard ≤ e) :
    {b | (![b] : Fin 1 → M) ∈ (reverseBadRelation S R hR hsort e).fibre ![value c]}.Finite := by
  have hbad := cofinite_reverse_fibres_bounded (rawValueFibre c) (rawValueFibre_infinite h00 c)
    R d (fun a _ => hforward a)
  apply hbad.1.subset
  intro b hb
  obtain ⟨u,hu,hm⟩ := (reverseBadRelation_fibre_iff S R hR hsort e c b).mp hb
  have hinf : ¬ {x | x ∈ rawValueFibre c ∧ R x b}.Finite := by
    intro hf
    exact (no_injection_iff_finite_ncard_le.mpr ⟨hf,he b hf⟩) ⟨u,hu,hm⟩
  exact (reverse_value_fibre_dichotomy S R hR hsort c b).resolve_left hinf

theorem reverseBadRelation_definable_base (S : Set M) (R : M → M → Prop)
    (hR : @Set.Definable₂ M S LRV (CanonicalStructure.normalize (M := M)) {p | R p.1 p.2})
    (hsort : ∀ a b, R a b → iRV a ∧ iRV b) (e : ℕ) (c : Code (M := M)) :
    DefinableAtBase ⟨S,{value c}⟩ .rv
      {b | (![b] : Fin 1 → M) ∈ (reverseBadRelation S R hR hsort e).fibre ![value c]} := by
  let Q := reverseBadRelation S R hR hsort e
  refine ⟨1,![value c],?_,Q,?_⟩
  · intro i; fin_cases i; exact Set.mem_singleton _
  · ext z
    change z ∈ Q.fibre ![value c] ↔ (![z 0] : Fin 1 → M) ∈ Q.fibre ![value c]
    have he : (![z 0] : Fin 1 → M) = z := by funext i; fin_cases i; rfl
    rw [he]

theorem reverse_value_fibre_finite_of_nonalg {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (S : Set M) (hsmall : Cardinal.mk S < κ) (R : M → M → Prop)
    (hR : @Set.Definable₂ M S LRV (CanonicalStructure.normalize (M := M)) {p | R p.1 p.2})
    (hsort : ∀ a b, R a b → iRV a ∧ iRV b) (d : ℕ)
    (hforward : ∀ a, {b | R a b}.Finite ∧ {b | R a b}.ncard ≤ d)
    (b : M) (hb : ¬ AlgebraicAt S .rv b) (c : Code (M := M)) :
    {x | x ∈ rawValueFibre c ∧ R x b}.Finite := by
  obtain ⟨e,he⟩ := uniform_reverse_value_fibre_bound hκ hs h00 S hsmall R hR hsort c
  let A : Set M :=
    {t | (![t] : Fin 1 → M) ∈ (reverseBadRelation S R hR hsort e).fibre ![value c]}
  have hAf : A.Finite := reverseBadRelation_finite h00 S R hR hsort d e hforward c he
  have hAd : DefinableAtBase ⟨S,{value c}⟩ .rv A := reverseBadRelation_definable_base S R hR hsort e c
  by_contra hf
  obtain ⟨u,hu,hm⟩ := RawClosure.exists_inj_of_infinite hf e
  have hbA : b ∈ A := (reverseBadRelation_fibre_iff S R hR hsort e c b).mpr ⟨u,hu,hm⟩
  have hba : AlgebraicAtBase ⟨S,{value c}⟩ .rv b := ⟨A,hAd,hAf,hbA⟩
  exact hb ((algebraic_rv_gamma_base_iff hκ hs h00 ⟨S,{value c}⟩ hsmall b).mp hba)

/-- The finite reverse-relation theorem used for RV exchange. Its proof
uses the derived finite/cofinite bounds and the proved removal of Gamma
names, then applies 3.15 to the reverse RV set. -/
theorem rv_reverse_relation_finite_of_nonalg {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (S : Set M) (hsmall : Cardinal.mk S < κ) (R : M → M → Prop)
    (hR : @Set.Definable₂ M S LRV (CanonicalStructure.normalize (M := M)) {p | R p.1 p.2})
    (hsort : ∀ a b, R a b → iRV a ∧ iRV b)
    (hforward : ∀ a, {b | R a b}.Finite) (b : M) (hb : ¬ AlgebraicAt S .rv b) :
    {a | R a b}.Finite := by
  obtain ⟨d,hd⟩ := uniform_forward_relation_bound hs S hsmall R hR hforward
  let A : Set M := {a | R a b}
  have hA : DefinableAt (insert b S) .rv A := rv_reverse_fibre_definable S R hR hsort b
  apply rv_finite_of_finite_value_fibres h00 (insert b S) A hA
  intro γ
  let c := representative γ
  have hf := reverse_value_fibre_finite_of_nonalg hκ hs h00 S hsmall R hR hsort d hd b hb c
  have hpre : (Subtype.val ⁻¹' {x | x ∈ rawValueFibre c ∧ R x b} : Set (CanonicalRV.RVSort M)).Finite :=
    hf.preimage Subtype.val_injective.injOn
  apply hpre.subset
  rintro t ⟨htγ,htA⟩
  have ht0 : t.val ≠ iRVZero := by
    intro hz
    exact γ.property (htγ.symm.trans ((Values.vrv_eq_infinity_iff t).mpr hz))
  have hcv : Values.vrv c.val = γ.val := congrArg Subtype.val (representative_value γ)
  have hcmp := (Values.vrv_eq_iff c.val t).mp (hcv.trans htγ.symm)
  exact ⟨⟨⟨raw_rv c,raw_ne_zero c⟩,⟨t.property,ht0⟩,hcmp⟩,htA⟩

end SpecialTransformations.Section3.GammaParameters

/- Component: RVExchange -/
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3.GammaParameters
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- RV exchange over an arbitrary small real parameter base. The finite
forward relation is constructed by the checked parameter-promotion/cut
theorem; the reverse finiteness argument is proved separately. -/
theorem lemma_3_6_rv {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (S : Set M) (hsmall : Cardinal.mk S < κ) (a b : CanonicalRV.RVSort M)
    (hb : AlgebraicAt (insert a.val S) .rv b.val) (hb0 : ¬ AlgebraicAt S .rv b.val) :
    AlgebraicAt (insert b.val S) .rv a.val := by
  let B : Base (M := M) := ⟨S,∅⟩
  let aa : Fin 1 → M := fun _ => a.val
  have heS : S ∪ Set.range aa = insert a.val S := by
    ext x
    constructor
    · rintro (hx | ⟨i,hi⟩)
      · exact Or.inr hx
      · exact Or.inl hi.symm
    · rintro (rfl | hx)
      · exact Or.inr ⟨0,rfl⟩
      · exact Or.inl hx
  have hb' : AlgebraicAt (S ∪ Set.range aa) .rv b.val := heS.symm ▸ hb
  have hbB : AlgebraicAtBase ⟨B.real ∪ Set.range aa,B.gamma⟩ .rv b.val :=
    (algebraic_base_empty_iff _ .rv b.val).mpr hb'
  obtain ⟨G,hG⟩ := good_base_relation_of_algebraic B (fun _ : Fin 1 => .rv) aa
    (fun _ => a.property) .rv b.val hbB
  let H : M → M → Prop := fun x y => ((fun _ : Fin 1 => x),y) ∈ G.carrier
  let R : M → M → Prop := fun x y => iRV x ∧ iRV y ∧ H x y
  have hgd := (base_empty_iff S (Fin.lastCases .rv (fun _ : Fin 1 => .rv)) _).mp G.definable
  have hgn := (definableOver_iff_normalized_raw S _ _).mp hgd |>.1
  have heGraph : {z : Fin 2 → M | (Fin.init z,z (Fin.last 1)) ∈ G.carrier} =
      {z | H (z 0) (z 1)} := by
    ext z
    change (Fin.init z,z (Fin.last 1)) ∈ G.carrier ↔ H (z 0) (z 1)
    have hi : Fin.init z = (fun _ : Fin 1 => z 0) := by funext i; fin_cases i; rfl
    rw [hi]
    rfl
  have hH : @Set.Definable₂ M S LRV (CanonicalStructure.normalize (M := M)) {p | H p.1 p.2} := by
    change @Set.Definable M S LRV (CanonicalStructure.normalize (M := M)) (Fin 2) {z | H (z 0) (z 1)}
    exact heGraph ▸ hgn
  have hRV := ((definableAt_iff_normalized_raw S .rv {x | iRV x}).mp (definableAt_sort S .rv)).1
  have hR : @Set.Definable₂ M S LRV (CanonicalStructure.normalize (M := M)) {p | R p.1 p.2} := by
    letI := CanonicalStructure.normalize (M := M)
    have h0 := SpecialTransformations.ModelTheory.definable_unary_at hRV (0 : Fin 2)
    have h1 := SpecialTransformations.ModelTheory.definable_unary_at hRV (1 : Fin 2)
    exact h0.inter (h1.inter hH)
  have hsort : ∀ x y, R x y → iRV x ∧ iRV y := fun x y h => ⟨h.1,h.2.1⟩
  have hforward (x : M) : {y | R x y}.Finite :=
    (G.finite (fun _ : Fin 1 => x)).subset (fun y hy => hy.2.2)
  have hf : {x | R x b.val}.Finite :=
    rv_reverse_relation_finite_of_nonalg hκ hs h00 S hsmall R hR hsort hforward b.val hb0
  exact ⟨{x | R x b.val},rv_reverse_fibre_definable S R hR hsort b.val,hf,
    ⟨a.property,b.property,hG⟩⟩

/-- Full RV assertion of 3.6 with genuine Gamma names in the ambient base. -/
theorem lemma_3_6_rv_gamma_base {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : Base (M := M)) (hsmall : Cardinal.mk B.real < κ) (a b : CanonicalRV.RVSort M)
    (hb : AlgebraicAtBase ⟨insert a.val B.real,B.gamma⟩ .rv b.val)
    (hb0 : ¬ AlgebraicAtBase B .rv b.val) :
    AlgebraicAtBase ⟨insert b.val B.real,B.gamma⟩ .rv a.val := by
  have hsa := small_insert hκ B.real hsmall a.val
  have hsb := small_insert hκ B.real hsmall b.val
  have hb' := (algebraic_rv_gamma_base_iff hκ hs h00 ⟨insert a.val B.real,B.gamma⟩ hsa b.val).mp hb
  have hb0' : ¬ AlgebraicAt B.real .rv b.val :=
    fun h => hb0 ((algebraic_rv_gamma_base_iff hκ hs h00 B hsmall b.val).mpr h)
  exact (algebraic_rv_gamma_base_iff hκ hs h00 ⟨insert b.val B.real,B.gamma⟩ hsb a.val).mpr
    (lemma_3_6_rv hκ hs h00 B.real hsmall a b hb' hb0')

end SpecialTransformations.Section3.GammaParameters
