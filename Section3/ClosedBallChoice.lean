module

public import Section3.ClosedBallCentres
public import Section3.ClosedBallCodes
public import Section3.CanonicalContext
public import ValuedFieldExtension

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.ClosedBallCodes
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- Complete graph on real codes; invariance below makes it a function on
actual balls, without adding any representative code to S. -/
def centerGraph (C : Set (Fin 3 → M)) (f : C → M) : Set (Fin 4 → M) :=
  {z | ∃ t : C, t.val = Fin.init z ∧ f t = z (Fin.last 3)}

theorem coded_centers_canonical (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (S : Set M) (C : Set (Fin 3 → M))
    (hC : DefinableOver S (fun _ => .vf) C) (hfin : (rawBall '' C).Finite) :
    ∃ f : C → M, (∀ t, f t ∈ rawBall t.val) ∧
      DefinableOver S (fun _ => .vf) (centerGraph C f) ∧
      ∀ t u : C, rawBall t.val = rawBall u.val → f t = f u := by
  obtain ⟨Γ, hΓ, v, hv⟩ := VFValued.exists_valuation_predV (M := M)
  letI := hΓ
  obtain ⟨ε, hε0, hε⟩ := ValuedFieldExtension.exists_nontrivial_predV (M := M)
  have hnt : ∃ x : VFType (M := M), x ≠ 0 ∧ v x < 1 := by
    refine ⟨ε, hε0, lt_of_not_ge ?_⟩
    intro hle
    exact hε ((hv 1 ε).mpr (by simpa only [map_one] using hle))
  have hCsort := ((definableOver_iff_normalized_raw S (fun _ => .vf) C).mp hC).2
  have hclosed (t : Fin 3 → M) (ht : t ∈ C) : ClosedBallRoots.IsClosedBall v (ball t) := by
    by_cases hz : t 2 = iVFZero
    · left
      ext x
      simp only [ball, rawBall, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      exact ⟨hCsort t ht, x.property, (body_realize t x.val).mpr (Or.inl hz)⟩
    · exact Or.inr ⟨⟨t 0, hCsort t ht 0⟩, ⟨t 1, hCsort t ht 1⟩,
        ball_eq_closed v hv t (hCsort t ht) hz⟩
  have hfin' : (ball '' C).Finite := by
    have hh := hfin.image (fun B : Set M => {x : VFType (M := M) | x.val ∈ B})
    simpa only [Set.image_image, Function.comp_def, ball] using hh
  obtain ⟨g, hg, hgmem, hgeq⟩ := BallFamilies.closed_family_centres v hv hc h00 hnt S C
    hC.raw_definable ball (relation_definable S) hfin' hclosed
  let f (t : C) := (g t.val).val
  have hfmem (t : C) : f t ∈ rawBall t.val := hgmem t.val t.property
  have hgraph : S.Definable LRV (centerGraph C f) := by
    have hin : S.DefinableMap LRV (Fin.init : (Fin 4 → M) → (Fin 3 → M)) := by
      intro i
      exact Set.DefinableFun.proj LRV
    have heq := (hg.comp hin).ofPred_eq
      (Set.DefinableFun.proj (L := LRV) (A := S) (i := Fin.last 3))
    have hh := (hC.raw_definable.preimage_map hin).inter heq
    convert hh using 1
    ext z
    change (∃ t : C, t.val = Fin.init z ∧ f t = z (Fin.last 3)) ↔
      Fin.init z ∈ C ∧ (g (Fin.init z)).val = z (Fin.last 3)
    constructor
    · rintro ⟨t, ht, he⟩
      exact ⟨ht ▸ t.property, ht ▸ he⟩
    · rintro ⟨ht, he⟩
      exact ⟨⟨Fin.init z, ht⟩, rfl, he⟩
  refine ⟨f, hfmem, raw_definableOver_sorted hc S (fun _ => .vf) _ hgraph ?_, ?_⟩
  · rintro z ⟨t, ht, he⟩ i
    by_cases hi : i.val < 3
    · have hti := hCsort t.val t.property (⟨i.val, hi⟩ : Fin 3)
      have hix : (⟨i.val, hi⟩ : Fin 3).castSucc = i := Fin.ext rfl
      have hcoord := congrFun ht (⟨i.val, hi⟩ : Fin 3)
      have hz : t.val (⟨i.val, hi⟩ : Fin 3) = z i :=
        hcoord.trans (congrArg z hix)
      change iVF (z i)
      exact hz ▸ hti
    · have hi' : i = Fin.last 3 := Fin.ext (by change i.val = 3; have := i.isLt; omega)
      subst i
      exact he ▸ (g t.val).property
  · intro t u he
    apply congrArg Subtype.val
    apply hgeq
    exact congrArg (fun B : Set M => {x : VFType (M := M) | x.val ∈ B}) he

/-- Lemma 3.10 on real codes in every ACVF(0,0) model. Its full graph is
definable over the original base and is invariant under equality of balls.
No canonical-totalization, saturation or named-representative premise. -/
theorem coded_centers (h00 : M ⊨ Axioms.ACVF00) (S : Set M)
    (C : Set (Fin 3 → M)) (hC : DefinableOver S (fun _ => .vf) C)
    (hfin : (rawBall '' C).Finite) :
    ∃ f : C → M, (∀ t, f t ∈ rawBall t.val) ∧
      DefinableOver S (fun _ => .vf) (centerGraph C f) ∧
      ∀ t u : C, rawBall t.val = rawBall u.val → f t = f u := by
  let N := CanonicalStructure.normalize (M := M)
  letI := sM
  have hN : @Theory.Model LRV M N Axioms.ACVF := CanonicalStructure.normalized_model hM
  have hcan : @CanonicalStructure.IsCanonical M N := CanonicalStructure.normalize_isCanonical
  have hN00 : @Theory.Model LRV M N Axioms.ACVF00 := normalized_model00 h00
  have hball : @rawBall M N = rawBall (M := M) := funext rawBall_normalize
  have hCN := (definableOver_normalize_iff S (fun _ => .vf) C).mpr hC
  have hfinN : ((@rawBall M N) '' C).Finite := hball.symm ▸ hfin
  obtain ⟨f, hf, hg, he⟩ := @coded_centers_canonical M N hN hcan hN00 S C hCN hfinN
  refine ⟨f, ?_, (definableOver_normalize_iff S (fun _ => .vf) (centerGraph C f)).mp hg, ?_⟩
  · intro t
    simpa only [hball] using hf t
  · intro t u htu
    apply he t u
    simpa only [hball] using htu

end SpecialTransformations.Section3.ClosedBallCodes
