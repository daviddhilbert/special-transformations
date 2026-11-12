module

public import Section3.GammaCounting
public import Section3.GammaParameterBridge

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3.GammaParameters
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n : ℕ}

theorem mem_gammaPullback_code (W : Set (Values.Gamma (M := M))) (t : Code (M := M)) :
    raw t ∈ Values.gammaPullback W ↔ value t ∈ W := by
  constructor
  · rintro ⟨hr,hz,hW⟩
    exact hW
  · intro hW
    exact ⟨raw_rv t,raw_ne_zero t,hW⟩

theorem same_scalar_with_codes_iff (x : M) (t u : Code (M := M))
    (htu : value t = value u) : SameScalar x (raw t) ↔ SameScalar x (raw u) := by
  have hh := same_with_codes_iff (fun _ : Fin 1 => x) (fun _ => t) (fun _ => u)
    (funext (fun _ => htu))
  simpa only [Same,rawTuple,Fin.forall_fin_one] using hh

def invariantHull (R : Set ((Fin n → M) × M)) : Set ((Fin n → M) × M) :=
  {p | NonzeroRV p.2 ∧ ∀ x, SameScalar x p.2 → (p.1,x) ∈ R}

theorem invariantHull_definable (S : Set M) (R : Set ((Fin n → M) × M))
    (hR : @RawClosure.Tuple.RelationDefinable M (CanonicalStructure.normalize (M := M)) n S R) :
    @RawClosure.Tuple.RelationDefinable M (CanonicalStructure.normalize (M := M)) n S
      (invariantHull R) := by
  have hE : @Set.Definable M S LRV (CanonicalStructure.normalize (M := M)) (Fin 2)
      {z | SameScalar (z 0) (z 1)} := by
    convert @same_scalar_definable M (CanonicalStructure.normalize (M := M)) S using 1
    ext z
    exact (same_scalar_normalize (z 0) (z 1)).symm
  have hP : @Set.Definable₁ M S LRV (CanonicalStructure.normalize (M := M))
      {x | NonzeroRV x} := by
    have he : {x : M | @NonzeroRV M (CanonicalStructure.normalize (M := M)) x} =
        {x | NonzeroRV x} := Set.ext (fun x => nonzero_rv_normalize x)
    exact he ▸ @nonzero_rv_definable M (CanonicalStructure.normalize (M := M)) S
  let E : M → M → Prop := SameScalar
  let P : M → Prop := NonzeroRV
  let H := invariantHull R
  let N := CanonicalStructure.normalize (M := M)
  letI := N
  let α := Fin n ⊕ Fin 1
  let idx : Fin n ⊕ Fin 1 → α ⊕ Fin 1 := Sum.elim (fun i => .inl (.inl i)) Sum.inr
  have he := hE.preimage_comp (![Sum.inr 0,Sum.inl (Sum.inr 0)] : Fin 2 → α ⊕ Fin 1)
  have hr := hR.preimage_comp idx
  have hu := (he.compl.union hr).forall_of_finite
  have hp := hP.preimage_comp (Sum.inr : Fin 1 → α)
  change S.Definable LRV {z : α → M | (z ∘ Sum.inl,z (.inr 0)) ∈ H}
  convert hp.inter hu using 1
  ext z
  change (P (z (.inr 0)) ∧ ∀ x, E x (z (.inr 0)) → (z ∘ Sum.inl,x) ∈ R) ↔ _
  simp only [Set.mem_inter_iff,Set.mem_union,Set.mem_compl_iff,Set.mem_ofPred_eq,
    Set.mem_preimage,Function.comp_apply,idx,Sum.elim_inl,Sum.elim_inr]
  constructor
  · rintro ⟨hp,hh⟩
    refine ⟨hp,?_⟩
    intro u
    by_cases he : E (u 0) (z (.inr 0))
    · exact Or.inr (hh (u 0) he)
    · exact Or.inl he
  · rintro ⟨hp,hh⟩
    exact ⟨hp,fun x hx => (hh (fun _ => x)).resolve_left (not_not.mpr hx)⟩

theorem invariantHull_invariant (R : Set ((Fin n → M) × M))
    (a : Fin n → M) (t u : Code (M := M)) (htu : value t = value u) :
    (a,raw t) ∈ invariantHull R ↔ (a,raw u) ∈ invariantHull R := by
  simp only [invariantHull,Set.mem_ofPred_eq,show NonzeroRV (raw t) from ⟨raw_rv t,raw_ne_zero t⟩,
    show NonzeroRV (raw u) from ⟨raw_rv u,raw_ne_zero u⟩,true_and]
  exact forall_congr' (fun x => imp_congr_left (same_scalar_with_codes_iff x t u htu))

structure GoodGammaRelation (S : Set M) (n : ℕ) where
  carrier : Set ((Fin n → M) × M)
  definable : @RawClosure.Tuple.RelationDefinable M (CanonicalStructure.normalize (M := M)) n S carrier
  proper : ∀ a x, (a,x) ∈ carrier → NonzeroRV x
  invariant : ∀ a (t u : Code (M := M)), value t = value u →
    ((a,raw t) ∈ carrier ↔ (a,raw u) ∈ carrier)
  finite : ∀ a, (gammaRow carrier a).Finite

/-- Promotion followed by universal class closure and first-order counting
produces globally finite Gamma rows. No finite RV-preimage is asserted. -/
theorem good_gamma_relation_of_algebraic (S : Set M) (a : Fin n → M)
    (δ : Values.Gamma (M := M))
    (hδ : GammaAlgebraicAtBase (⟨S ∪ Set.range a,∅⟩ : Base (M := M)) δ) :
    ∃ R : GoodGammaRelation S n, (a,raw (representative δ)) ∈ R.carrier := by
  obtain ⟨W,hW,hWf,hδW⟩ := hδ
  have hWreal := (at_base_empty_iff (S ∪ Set.range a) .rv (Values.gammaPullback W)).mp hW
  have hWN := (definableAt_iff_normalized_raw (S ∪ Set.range a) .rv _).mp hWreal
  obtain ⟨R,hRd,hRa⟩ := @RawClosure.Tuple.promote_definable_fibre M
    (CanonicalStructure.normalize (M := M)) n S a (Values.gammaPullback W) hWN.1
  let H := invariantHull R
  have hHd := invariantHull_definable S R hRd
  have hHp (b : Fin n → M) (x : M) (hx : (b,x) ∈ H) : NonzeroRV x := hx.1
  have hHi := invariantHull_invariant R
  have hrow : gammaRow H a = W := by
    ext γ
    constructor
    · intro hγ
      have hs : SameScalar (raw (representative γ)) (raw (representative γ)) :=
        ⟨⟨raw_rv _,raw_ne_zero _⟩,⟨raw_rv _,raw_ne_zero _⟩,
          (value_eq_iff _ _).mp rfl⟩
      have hr := hγ.2 _ hs
      have hw : raw (representative γ) ∈ Values.gammaPullback W := hRa ▸ hr
      simpa only [representative_value] using (mem_gammaPullback_code W _).mp hw
    · intro hγ
      refine ⟨⟨raw_rv _,raw_ne_zero _⟩,?_⟩
      intro x hx
      let t : Code (M := M) := ⟨⟨x,hx.1.1⟩,hx.1.2⟩
      have he : value t = γ := ((value_eq_iff t _).mpr hx.2.2).trans (representative_value γ)
      have hxW : x ∈ Values.gammaPullback W := (mem_gammaPullback_code W t).mpr (he.symm ▸ hγ)
      change x ∈ {y | (a,y) ∈ R}
      rw [hRa]
      exact hxW
  let d := W.ncard
  let Q : Set ((Fin n → M) × M) := {p | p ∈ H ∧ p.1 ∉ HasMoreGamma H d}
  have ha : a ∉ HasMoreGamma H d := (no_moreGamma_iff H hHp hHi a d).mpr
    ⟨hrow.symm ▸ hWf,by simpa only [hrow,d] using (le_refl W.ncard)⟩
  refine ⟨⟨Q,?_,?_,?_,?_⟩,?_,ha⟩
  · have hMore := hasMoreGamma_definable S H hHd d
    let N := CanonicalStructure.normalize (M := M)
    letI := N
    exact hHd.inter (hMore.compl.preimage_comp (Sum.inl : Fin n → Fin n ⊕ Fin 1))
  · exact fun b x hx => hHp b x hx.1
  · intro b t u he
    exact and_congr_left (fun _ => hHi b t u he)
  · intro b
    by_cases hb : b ∈ HasMoreGamma H d
    · have hem : gammaRow Q b = ∅ := by ext γ; simp [gammaRow,Q,hb]
      rw [hem]
      exact Set.finite_empty
    · exact ((no_moreGamma_iff H hHp hHi b d).mp hb).1.subset (fun γ hγ => hγ.1)
  · change δ ∈ gammaRow H a
    rw [hrow]
    exact hδW

end SpecialTransformations.Section3.GammaParameters
