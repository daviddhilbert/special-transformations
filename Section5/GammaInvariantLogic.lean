module

public import Section5.GammaBaseInputs
public import Section5.GammaPolynomialSupport
public import Section5.VerticalObstacles
public import Section3.GammaRealMap
public import Section3.GammaProjection

@[expose] public section

/-! Complete graph operations over named Gamma parameters. Finite real
coordinates are flattened explicitly; projection quantifies over all
proper Gamma codes in the existing invariant relations. -/

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

namespace SpecialTransformations.Section5

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

local notation "N" => (@CanonicalStructure.normalize M sM)

private structure FlatView (P : PresentedSpace (M := M)) where
  arity : ℕ
  sort : Fin arity → SortTag
  index : @DefinableGeometry.Space.Index LRV M N P ≃ Fin arity
  code : Carrier P → Fin arity → M
  domain_iff : ∀ z : Fin arity → M, z ∘ index ∈ pDomain P ↔ ∀ i, sortEval (sort i) (z i)
  code_decode : ∀ c : pDomain P, code (pDecode P c) = c.val ∘ index.symm

namespace FlatView

variable {P Q : PresentedSpace (M := M)}

private def point (n m : ℕ) : FlatView (pointSpace (M := M) n m) where
  arity := n + m
  sort := gammaPointSort n m
  index := finSumFinEquiv
  code := gammaPointCode
  domain_iff z := by
    constructor
    · rintro ⟨hx, hy⟩ i
      cases i using Fin.addCases with
      | left i => simpa only [gammaPointSort, Fin.append_left, Function.comp_apply,
          finSumFinEquiv_apply_left] using hx i
      | right i => simpa only [gammaPointSort, Fin.append_right, Function.comp_apply,
          finSumFinEquiv_apply_right] using hy i
    · intro h
      exact ⟨fun i => by simpa only [gammaPointSort, Fin.append_left, Function.comp_apply,
          finSumFinEquiv_apply_left] using h (Fin.castAdd m i),
        fun i => by simpa only [gammaPointSort, Fin.append_right, Function.comp_apply,
          finSumFinEquiv_apply_right] using h (Fin.natAdd n i)⟩
  code_decode c := by
    funext i
    cases i using Fin.addCases with
    | left i => simp only [gammaPointCode, vfAt, Fin.append_left, Function.comp_apply,
        finSumFinEquiv_symm_apply_castAdd]
    | right i => simp only [gammaPointCode, Fin.append_right, Function.comp_apply,
        finSumFinEquiv_symm_apply_natAdd]

private def prod (F : FlatView P) (G : FlatView Q) : FlatView (spaceProd P Q) where
  arity := F.arity + G.arity
  sort := Fin.append F.sort G.sort
  index := (Equiv.sumCongr F.index G.index).trans finSumFinEquiv
  code x := Fin.append (F.code x.1) (G.code x.2)
  domain_iff z := by
    change (((z ∘ Fin.castAdd G.arity) ∘ F.index) ∈ pDomain P ∧
      ((z ∘ Fin.natAdd F.arity) ∘ G.index) ∈ pDomain Q) ↔ _
    rw [F.domain_iff (z ∘ Fin.castAdd G.arity), G.domain_iff (z ∘ Fin.natAdd F.arity)]
    constructor
    · rintro ⟨hx, hy⟩ i
      cases i using Fin.addCases with
      | left i => simpa only [Fin.append_left, Function.comp_apply] using hx i
      | right i => simpa only [Fin.append_right, Function.comp_apply] using hy i
    · intro h
      exact ⟨fun i => by simpa only [Fin.append_left, Function.comp_apply] using h (Fin.castAdd G.arity i),
        fun i => by simpa only [Fin.append_right, Function.comp_apply] using h (Fin.natAdd F.arity i)⟩
  code_decode c := by
    change Fin.append (F.code (pDecode P ⟨c.val ∘ Sum.inl, c.property.1⟩))
      (G.code (pDecode Q ⟨c.val ∘ Sum.inr, c.property.2⟩)) = _
    rw [F.code_decode, G.code_decode]
    funext i
    cases i using Fin.addCases with
    | left i =>
      rw [Fin.append_left]
      change c.val (Sum.inl (F.index.symm i)) =
        c.val ((Equiv.sumCongr F.index G.index).symm (finSumFinEquiv.symm (Fin.castAdd G.arity i)))
      rw [finSumFinEquiv_symm_apply_castAdd] <;> rfl
    | right i =>
      rw [Fin.append_right]
      change c.val (Sum.inr (G.index.symm i)) =
        c.val ((Equiv.sumCongr F.index G.index).symm (finSumFinEquiv.symm (Fin.natAdd F.arity i)))
      rw [finSumFinEquiv_symm_apply_natAdd] <;> rfl

private theorem code_sorted (F : FlatView P) (x : Carrier P) :
    ∀ i, sortEval (F.sort i) (F.code x i) := by
  obtain ⟨c, rfl⟩ := (@DefinableGeometry.Space.onto LRV M N P) x
  rw [F.code_decode, ← F.domain_iff]
  have he : (c.val ∘ F.index.symm) ∘ F.index = c.val :=
    funext fun i => congrArg c.val (F.index.symm_apply_apply i)
  exact he.symm ▸ c.property

private theorem code_onto (F : FlatView P) (z : Fin F.arity → M)
    (hz : ∀ i, sortEval (F.sort i) (z i)) : ∃ x : Carrier P, F.code x = z := by
  refine ⟨pDecode P ⟨z ∘ F.index, (F.domain_iff z).mpr hz⟩, ?_⟩
  rw [F.code_decode]
  exact funext fun i => congrArg z (F.index.apply_symm_apply i)

private theorem code_injective (F : FlatView P) : Function.Injective F.code := by
  intro x y h
  obtain ⟨c, rfl⟩ := (@DefinableGeometry.Space.onto LRV M N P) x
  obtain ⟨d, rfl⟩ := (@DefinableGeometry.Space.onto LRV M N P) y
  rw [F.code_decode, F.code_decode] at h
  exact congrArg (pDecode P) (Subtype.ext (funext fun i => by
    simpa only [Function.comp_apply, F.index.symm_apply_apply] using congrFun h (F.index i)))

private def Definable (F : FlatView P) (B : Base (M := M)) (A : Set (Carrier P)) : Prop :=
  DefinableOverBase B F.sort (F.code '' A)

private theorem real_to_definable (F : FlatView P) (B : Base (M := M)) (A : Set (Carrier P))
    (hA : SetDefinable P B.real A) : F.Definable B A := by
  apply real_definableOverBase
  apply (definableOver_iff_normalized_raw B.real F.sort (F.code '' A)).mpr
  refine ⟨?_, by rintro _ ⟨a, _, rfl⟩; exact F.code_sorted a⟩
  have hs : @Set.Definable M B.real LRV N (@DefinableGeometry.Space.Index LRV M N P)
      (@DefinableGeometry.Space.preimage LRV M N P A) := hA
  have ht := @Set.Definable.preimage_comp M B.real LRV N _ _ F.index _ hs
  convert ht using 1
  ext z
  constructor
  · rintro ⟨a, ha, rfl⟩
    have hd := (F.domain_iff (F.code a)).mpr (F.code_sorted a)
    refine ⟨hd, ?_⟩
    have he : F.code (pDecode P ⟨F.code a ∘ F.index, hd⟩) = F.code a := by
      rw [F.code_decode]
      exact funext fun i => congrArg (F.code a) (F.index.apply_symm_apply i)
    change pDecode P ⟨F.code a ∘ F.index, hd⟩ ∈ A
    exact (F.code_injective he).symm ▸ ha
  · rintro ⟨hd, ha⟩
    refine ⟨pDecode P ⟨z ∘ F.index, hd⟩, ha, ?_⟩
    rw [F.code_decode]
    exact funext fun i => congrArg z (F.index.apply_symm_apply i)

private theorem real_of_flat (F : FlatView P) {S : Set M} {A : Set (Carrier P)}
    (hA : DefinableOver S F.sort (F.code '' A)) : SetDefinable P S A := by
  have hraw := (definableOver_iff_normalized_raw S F.sort _).mp hA
  have h := @Set.Definable.preimage_comp M S LRV N _ _ F.index.symm _ hraw.1
  change @Set.Definable M S LRV N _ (@DefinableGeometry.Space.preimage LRV M N P A)
  convert h using 1
  ext z
  constructor
  · rintro ⟨hz, ha⟩
    exact ⟨pDecode P ⟨z, hz⟩, ha, F.code_decode ⟨z, hz⟩⟩
  · rintro ⟨a, ha, he⟩
    change F.code a = z ∘ F.index.symm at he
    have hz : z ∈ pDomain P := by
      have hh := (F.domain_iff (z ∘ F.index.symm)).mpr (he ▸ F.code_sorted a)
      have he' : (z ∘ F.index.symm) ∘ F.index = z :=
        funext fun i => congrArg z (F.index.symm_apply_apply i)
      exact he' ▸ hh
    refine ⟨hz, ?_⟩
    change pDecode P ⟨z, hz⟩ ∈ A
    have he' := F.code_injective ((F.code_decode ⟨z, hz⟩).trans he.symm)
    exact he'.symm ▸ ha

private theorem preimage_coords (F : FlatView P) (G : FlatView Q) (B : Base (M := M))
    {A : Set (Carrier Q)} (hA : G.Definable B A) (f : Carrier P → Carrier Q)
    (π : Fin G.arity → Fin F.arity) (hf : ∀ x, G.code (f x) = F.code x ∘ π) :
    F.Definable B {x | f x ∈ A} := by
  have ha : DefinableOverBase B G.sort (G.code '' A) := hA
  have hs := ha.preimage_real F.sort π
  change DefinableOverBase B F.sort _
  convert hs using 1
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨f x, hx, hf x⟩, F.code_sorted x⟩
  · rintro ⟨⟨y, hy, he⟩, hz⟩
    obtain ⟨x, rfl⟩ := F.code_onto z hz
    have hyx : y = f x := G.code_injective (he.trans (hf x).symm)
    refine ⟨x, ?_, rfl⟩
    change f x ∈ A
    exact hyx ▸ hy

private theorem image_coords (F : FlatView P) (G : FlatView Q) (B : Base (M := M))
    {A : Set (Carrier P)} (hA : F.Definable B A) (f : Carrier P → Carrier Q)
    (π : Fin G.arity → Fin F.arity) (hsort : F.sort ∘ π = G.sort)
    (hf : ∀ x, G.code (f x) = F.code x ∘ π) : G.Definable B (f '' A) := by
  have ha : DefinableOverBase B F.sort (F.code '' A) := hA
  have hs := ha.image_real π
  rw [hsort] at hs
  change DefinableOverBase B G.sort _
  convert hs using 1
  ext z
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨F.code x, ⟨x, hx, rfl⟩, (hf x).symm⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨f x, ⟨x, hx, rfl⟩, hf x⟩

private theorem inter (F : FlatView P) (B : Base (M := M)) {A C : Set (Carrier P)}
    (hA : F.Definable B A) (hC : F.Definable B C) : F.Definable B (A ∩ C) := by
  have ha : DefinableOverBase B F.sort (F.code '' A) := hA
  have hc : DefinableOverBase B F.sort (F.code '' C) := hC
  change DefinableOverBase B F.sort _
  convert ha.inter hc using 1
  ext z
  constructor
  · rintro ⟨a, ⟨ha, hc⟩, rfl⟩
    exact ⟨⟨a, ha, rfl⟩, ⟨a, hc, rfl⟩⟩
  · rintro ⟨⟨a, ha, rfl⟩, ⟨c, hc, he⟩⟩
    exact ⟨a, ⟨ha, (F.code_injective he) ▸ hc⟩, rfl⟩

private theorem union (F : FlatView P) (B : Base (M := M)) {A C : Set (Carrier P)}
    (hA : F.Definable B A) (hC : F.Definable B C) : F.Definable B (A ∪ C) := by
  have ha : DefinableOverBase B F.sort (F.code '' A) := hA
  have hc : DefinableOverBase B F.sort (F.code '' C) := hC
  change DefinableOverBase B F.sort _
  rw [Set.image_union]
  exact ha.union hc

private theorem sdiff (F : FlatView P) (B : Base (M := M)) {A C : Set (Carrier P)}
    (hA : F.Definable B A) (hC : F.Definable B C) : F.Definable B (A \ C) := by
  have ha : DefinableOverBase B F.sort (F.code '' A) := hA
  have hc : DefinableOverBase B F.sort (F.code '' C) := hC
  change DefinableOverBase B F.sort _
  convert ha.inter hc.compl using 1
  ext z
  constructor
  · rintro ⟨a, ⟨ha, hna⟩, rfl⟩
    refine ⟨⟨a, ha, rfl⟩, F.code_sorted a, ?_⟩
    rintro ⟨c, hc, he⟩
    exact hna (F.code_injective he ▸ hc)
  · rintro ⟨⟨a, ha, rfl⟩, _, hc⟩
    exact ⟨a, ⟨ha, fun h => hc ⟨a, h, rfl⟩⟩, rfl⟩

private theorem cylinderLeft (F : FlatView P) (G : FlatView Q) (B : Base (M := M))
    {A : Set (Carrier P)} (hA : F.Definable B A) :
    (F.prod G).Definable B {p | p.1 ∈ A} :=
  (F.prod G).preimage_coords F B hA Prod.fst (Fin.castAdd G.arity)
    (fun p => funext fun i => (Fin.append_left _ _ i).symm)

private theorem projectRight (F : FlatView P) (G : FlatView Q) (B : Base (M := M))
    {A : Set (Carrier (spaceProd P Q))} (hA : (F.prod G).Definable B A) :
    G.Definable B (Prod.snd '' A) :=
  (F.prod G).image_coords G B hA Prod.snd (Fin.natAdd F.arity)
    (funext fun i => Fin.append_right _ _ i)
    (fun p => funext fun i => (Fin.append_right _ _ i).symm)

private theorem graphOfReal (F : FlatView P) (G : FlatView Q) (B : Base (M := M))
    {r : Carrier P → Carrier Q → Prop} (h : RelationDefinable P Q B.real r) :
    (F.prod G).Definable B {p | r p.1 p.2} :=
  (F.prod G).real_to_definable B _
    ((@DefinableGeometry.Space.definable_prod_iff LRV M N P Q B.real r).mpr h)

private theorem realMapImage (F : FlatView P) (G : FlatView Q) (B : Base (M := M))
    {A : PresentedSet P B.real} {C : PresentedSet Q B.real} (f : Map A C)
    {X : Set (Carrier P)} (hX : F.Definable B X) :
    G.Definable B {y | ∃ a : A, a.val ∈ X ∧ (f a).val = y} := by
  have hg : (F.prod G).Definable B {p | ∃ a : A, a.val = p.1 ∧ (f a).val = p.2} :=
    F.graphOfReal G B (Map.graph_definable f)
  have hh := F.projectRight G B ((F.prod G).inter B (F.cylinderLeft G B hX) hg)
  convert hh using 1
  ext y
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨(a.val, (f a).val), ⟨ha, a, rfl, rfl⟩, rfl⟩
  · rintro ⟨⟨x, y⟩, ⟨hx, a, ha, he⟩, rfl⟩
    exact ⟨a, ha.symm ▸ hx, he⟩

private theorem graphSwap (F : FlatView P) (G : FlatView Q) (B : Base (M := M))
    {r : Carrier P → Carrier Q → Prop} (h : (F.prod G).Definable B {p | r p.1 p.2}) :
    (G.prod F).Definable B {p | r p.2 p.1} := by
  let π : Fin (F.arity + G.arity) → Fin (G.arity + F.arity) :=
    Fin.addCases (Fin.natAdd G.arity) (Fin.castAdd F.arity)
  exact (G.prod F).preimage_coords (F.prod G) B h Prod.swap π (by
    intro p
    funext i
    cases i using Fin.addCases <;>
      simp [prod, π, Function.comp_apply, Fin.append_left, Fin.append_right])

private theorem graphComp (F : FlatView P) (G : FlatView Q) (B : Base (M := M))
    {R : PresentedSpace (M := M)} (H : FlatView R)
    {r : Carrier P → Carrier Q → Prop} {t : Carrier Q → Carrier R → Prop}
    (hr : (F.prod G).Definable B {p | r p.1 p.2})
    (ht : (G.prod H).Definable B {p | t p.1 p.2}) :
    (F.prod H).Definable B {p | ∃ q, r p.1 q ∧ t q p.2} := by
  let V := (F.prod G).prod H
  let ρ : Fin (G.arity + H.arity) → Fin ((F.arity + G.arity) + H.arity) :=
    Fin.addCases (Fin.castAdd H.arity ∘ Fin.natAdd F.arity)
      (Fin.natAdd (F.arity + G.arity))
  let π : Fin (F.arity + H.arity) → Fin ((F.arity + G.arity) + H.arity) :=
    Fin.addCases (Fin.castAdd H.arity ∘ Fin.castAdd G.arity)
      (Fin.natAdd (F.arity + G.arity))
  have ht' : V.Definable B {p | t p.1.2 p.2} :=
    V.preimage_coords (G.prod H) B ht (fun p => (p.1.2, p.2)) ρ (by
      intro p
      funext i
      cases i using Fin.addCases <;>
        simp [V, prod, ρ, Function.comp_apply, Fin.append_left, Fin.append_right])
  have hc := V.inter B ((F.prod G).cylinderLeft H B hr) ht'
  have hs : V.sort ∘ π = (F.prod H).sort := by
    funext i
    cases i using Fin.addCases <;>
      simp [V, prod, π, Function.comp_apply, Fin.append_left, Fin.append_right]
  have h := V.image_coords (F.prod H) B hc (fun p => (p.1.1, p.2)) π hs (by
    intro p
    funext i
    cases i using Fin.addCases <;>
      simp [V, prod, π, Function.comp_apply, Fin.append_left, Fin.append_right])
  convert h using 1
  ext p
  constructor
  · rintro ⟨q, hr, ht⟩
    exact ⟨((p.1, q), p.2), ⟨hr, ht⟩, rfl⟩
  · rintro ⟨⟨⟨a, q⟩, b⟩, ⟨hr, ht⟩, rfl⟩
    exact ⟨q, hr, ht⟩

private def vf (n : ℕ) : FlatView (@Section4.vfSpace M sM hM n) where
  arity := n
  sort := fun _ => .vf
  index := Equiv.refl _
  code p := fun i => (p i).val
  domain_iff _ := Iff.rfl
  code_decode _ := rfl

end FlatView

private theorem gammaGraph_iff_flat (B : Base (M := M)) {n m u w : ℕ}
    (r : Point (M := M) n m → Point (M := M) u w → Prop) :
    GammaGraphDefinable B r ↔
      ((FlatView.point n m).prod (FlatView.point u w)).Definable B {p | r p.1 p.2} := by
  have h : {z | ∃ p q, r p q ∧ Fin.append (gammaPointCode p) (gammaPointCode q) = z} =
      (fun p : Point (M := M) n m × Point (M := M) u w =>
        Fin.append (gammaPointCode p.1) (gammaPointCode p.2)) '' {p | r p.1 p.2} := by
    ext z
    constructor
    · rintro ⟨p, q, hpq, rfl⟩
      exact ⟨(p, q), hpq, rfl⟩
    · rintro ⟨⟨p, q⟩, hpq, rfl⟩
      exact ⟨p, q, hpq, rfl⟩
  unfold GammaGraphDefinable FlatView.Definable FlatView.prod FlatView.point
  rw [h] <;> rfl

/-- A complete invariant graph can be used as a real relation after
specializing at representatives of finitely many named values. -/
theorem GammaGraphDefinable.real_specialize {B : Base (M := M)} {n m u w : ℕ}
    {r : Point (M := M) n m → Point (M := M) u w → Prop}
    (h : GammaGraphDefinable B r) :
    ∃ d, ∃ t : Fin d → GammaParameters.Code (M := M),
      RelationDefinable (pointSpace n m) (pointSpace u w)
        (B.real ∪ Set.range (GammaParameters.rawTuple t)) r := by
  let F := (FlatView.point (M := M) n m).prod (FlatView.point u w)
  have hF : DefinableOverBase B F.sort (F.code '' {p | r p.1 p.2}) :=
    (gammaGraph_iff_flat B r).mp h
  obtain ⟨d, t, ht⟩ := hF.specialize
  exact ⟨d, t, (@DefinableGeometry.Space.definable_prod_iff LRV M N
    (pointSpace n m) (pointSpace u w) _ r).mp (F.real_of_flat ht)⟩

private theorem gammaScalar_iff_flat (B : Base (M := M)) {n m : ℕ}
    (r : Point (M := M) n m → VF (M := M) → Prop) :
    GammaScalarGraphDefinable B r ↔
      ((FlatView.point n m).prod (FlatView.vf 1)).Definable B {p | r p.1 (p.2 0)} := by
  rw [GammaScalarGraphDefinable, gammaGraph_iff_flat]
  let P := FlatView.point (M := M) n m
  let Q := FlatView.point (M := M) 1 0
  let R := FlatView.vf (M := M) 1
  constructor
  · intro h
    exact (P.prod R).preimage_coords (P.prod Q) B h
      (fun p => (p.1, (p.2, Fin.elim0))) id (by
        intro p
        funext i
        cases i using Fin.addCases with
        | left i =>
          simp only [P, Q, R, FlatView.prod, Function.comp_apply, id_eq, Fin.append_left]
          change P.code p.1 i = Fin.append (P.code p.1) (R.code p.2) (Fin.castAdd 1 i)
          exact (Fin.append_left _ _ i).symm
        | right i =>
          fin_cases i
          simp only [P, Q, R, FlatView.prod, Function.comp_apply, id_eq, Fin.append_right]
          rfl)
  · intro h
    exact (P.prod Q).preimage_coords (P.prod R) B h
      (fun p => (p.1, p.2.1)) id (by
        intro p
        funext i
        cases i using Fin.addCases with
        | left i =>
          simp only [P, Q, R, FlatView.prod, Function.comp_apply, id_eq, Fin.append_left]
          change P.code p.1 i = Fin.append (P.code p.1) (Q.code p.2) (Fin.castAdd 1 i)
          exact (Fin.append_left _ _ i).symm
        | right i =>
          fin_cases i
          simp only [P, Q, R, FlatView.prod, Function.comp_apply, id_eq, Fin.append_right]
          rfl)

theorem gammaLogicInput (B : Base (M := M)) : GammaLogicInput B where
  real_set A h := (FlatView.point _ _).real_to_definable B A h
  real_map_graph f := (gammaGraph_iff_flat B _).mpr
    ((FlatView.point _ _).graphOfReal (FlatView.point _ _) B (Map.graph_definable f))
  real_scalar_graph f := by
    apply (gammaScalar_iff_flat B _).mpr
    have h := (FlatView.point _ _).graphOfReal (FlatView.vf 1) B (Map.graph_definable f)
    convert h using 1
    ext p
    apply exists_congr
    intro a
    apply and_congr_right'
    constructor
    · intro he
      funext i
      fin_cases i
      exact he
    · intro he
      exact congrFun he 0
  inter hA hC := (FlatView.point _ _).inter B hA hC
  union hA hC := (FlatView.point _ _).union B hA hC
  sdiff hA hC := (FlatView.point _ _).sdiff B hA hC
  restrict_graph hA hr := (gammaGraph_iff_flat B _).mpr
    (((FlatView.point _ _).prod (FlatView.point _ _)).inter B
      ((FlatView.point _ _).cylinderLeft (FlatView.point _ _) B hA)
      ((gammaGraph_iff_flat B _).mp hr))
  union_graph hr ht := (gammaGraph_iff_flat B _).mpr
    (((FlatView.point _ _).prod (FlatView.point _ _)).union B
      ((gammaGraph_iff_flat B _).mp hr) ((gammaGraph_iff_flat B _).mp ht))
  comp_graph hr ht := (gammaGraph_iff_flat B _).mpr
    ((FlatView.point _ _).graphComp (FlatView.point _ _) B (FlatView.point _ _)
      ((gammaGraph_iff_flat B _).mp hr) ((gammaGraph_iff_flat B _).mp ht))
  swap_graph hr := (gammaGraph_iff_flat B _).mpr
    ((FlatView.point _ _).graphSwap (FlatView.point _ _) B ((gammaGraph_iff_flat B _).mp hr))
  image_graph hr := by
    have h := (FlatView.point _ _).projectRight (FlatView.point _ _) B ((gammaGraph_iff_flat B _).mp hr)
    change (FlatView.point _ _).Definable B _
    convert h using 1
    ext y
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨(x,y), hx, rfl⟩
    · rintro ⟨⟨x,y⟩, h, rfl⟩
      exact ⟨x,h⟩
  scalar_image_graph hr f := by
    apply (gammaGraph_iff_flat B _).mpr
    have h := ((FlatView.point _ _).prod (FlatView.vf 1)).realMapImage
      ((FlatView.point _ _).prod (FlatView.point _ _)) B f
      ((gammaScalar_iff_flat B _).mp hr)
    convert h using 1
    ext p
    constructor
    · rintro ⟨z, x, hx, hf⟩
      exact ⟨⟨(z, ![x]), Set.mem_univ _⟩, hx, hf⟩
    · rintro ⟨a, ha, hf⟩
      let x := a.val.2 0
      have he : (![x] : Fin 1 → VF (M := M)) = a.val.2 := by
        funext i
        fin_cases i
        rfl
      refine ⟨a.val.1, x, ha, ?_⟩
      have harg : (⟨(a.val.1, ![x]), Set.mem_univ _⟩ : _) = a :=
        Subtype.ext (Prod.ext rfl he)
      rw [harg]
      exact hf

namespace Paper

theorem corollary_5_6_gamma {κ : Cardinal} (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : Base (M := M)) (hsmall : Cardinal.mk B.real < κ) (F : VFFieldBase B.real)
    {n m : ℕ} (A : Set (Point (M := M) n m)) (hA : GammaSetDefinable B A) :
    GammaIsDeformedRVPullback B A :=
  Section5.corollary_5_6_gamma h00 Values.presentationValuation Values.presentation_compatible
    (uniformVerticalObstacles hs hsmall Values.presentationValuation Values.presentation_compatible)
    (gammaLogicInput B) (gammaPolynomialSupportInput_of_fieldBase B F)
    (gammaPresentationInput B) A hA

end Paper

end SpecialTransformations.Section5
