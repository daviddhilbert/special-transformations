import Mathlib.Data.Finset.Max
import Section3.GammaClosureLaws
import Section3.GammaRVSeparation

/- Component: GammaFiniteOrder -/
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3.GammaParameters
open EndpointLogic
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem not_le_pair_definable (S : Set M) :
    SpecialTransformations.Section3.DefinableOver S (fun _ : Fin 2 => .rv)
      {z | (∀ i, iRV (z i)) ∧ ¬ iLe (z 0) (z 1)} := by
  let p : Parameters S := ⟨0,Fin.elim0,(fun _ => .vf),(fun i => i.elim0),(fun i => i.elim0)⟩
  let ts : Fin 2 → LRV.Term (Fin 0 ⊕ Fin 2) := ![.var (.inr 0),.var (.inr 1)]
  let φ : LRV.BoundedFormula (Fin 0) 2 := (BoundedFormula.rel Rel.rvLe ts).not
  have hw : WellSorted p.sorts (fun _ : Fin 2 => .rv) φ := by
    apply wellSorted_not
    apply WellSorted.rel
    intro i
    fin_cases i <;> rfl
  refine ⟨p,φ,hw,?_⟩
  ext z
  have he : (fun i => (ts i).realize (Sum.elim (Fin.elim0 : Fin 0 → M) z)) = ![z 0,z 1] := by
    funext i
    fin_cases i <;> rfl
  change ((∀ i, iRV (z i)) ∧ ¬ iLe (z 0) (z 1)) ↔
    (∀ i, iRV (z i)) ∧ ¬ Structure.RelMap (L := LRV) Rel.rvLe
      (fun i => (ts i).realize (Sum.elim (Fin.elim0 : Fin 0 → M) z))
  rw [he]
  rfl

def badLower (U : Set M) : Set M := {t | iRV t ∧ ∃ u ∈ U, ¬ iLe t u}

theorem badLower_definable_base (B : Base (M := M)) (U : Set M)
    (hU : DefinableAtBase B .rv U) : DefinableAtBase B .rv (badLower U) := by
  have hU2 := hU.preimage_real (fun _ : Fin 2 => .rv) (fun _ : Fin 1 => (1 : Fin 2))
  have hR := real_definableOverBase B _ _ (not_le_pair_definable B.real)
  have hp := (hU2.inter hR).image_real (fun _ : Fin 1 => (0 : Fin 2))
  change DefinableOverBase B (fun _ : Fin 1 => .rv) {z | z 0 ∈ badLower U}
  convert hp using 1
  all_goals try rfl
  ext z
  change (iRV (z 0) ∧ ∃ u ∈ U, ¬ iLe (z 0) u) ↔ ∃ w,
    ((w 1 ∈ U ∧ w ∈ sortedUniverse (fun _ : Fin 2 => .rv)) ∧
      ((∀ i, iRV (w i)) ∧ ¬ iLe (w 0) (w 1))) ∧ w ∘ (fun _ : Fin 1 => (0 : Fin 2)) = z
  constructor
  · rintro ⟨hz,u,hu,hn⟩
    have hs : ∀ i, iRV ((![z 0,u] : Fin 2 → M) i) := by
      intro i; fin_cases i
      · exact hz
      · exact hU.proper u hu
    refine ⟨![z 0,u],⟨⟨hu,hs⟩,⟨hs,hn⟩⟩,?_⟩
    funext i
    fin_cases i
    rfl
  · rintro ⟨w,⟨⟨hu,hs⟩,_,hn⟩,he⟩
    have hz : w 0 = z 0 := congrFun he 0
    rw [← hz]
    exact ⟨hs 0,w 1,hu,hn⟩

def leastCodes (U : Set M) : Set M := {t | t ∈ U ∧ ∀ u ∈ U, iLe t u}

theorem leastCodes_definable_base (B : Base (M := M)) (U : Set M)
    (hU : DefinableAtBase B .rv U) : DefinableAtBase B .rv (leastCodes U) := by
  have h := hU.inter (badLower_definable_base B U hU).compl
  change DefinableOverBase B (fun _ : Fin 1 => .rv) {z | z 0 ∈ leastCodes U}
  convert h using 1
  all_goals try rfl
  ext z
  change (z 0 ∈ U ∧ ∀ u ∈ U, iLe (z 0) u) ↔
    z 0 ∈ U ∧ ((∀ i : Fin 1, iRV (z i)) ∧ z 0 ∉ badLower U)
  constructor
  · rintro ⟨hz,hle⟩
    refine ⟨hz,?_,?_⟩
    · intro i; fin_cases i; exact hU.proper (z 0) hz
    · rintro ⟨_,u,hu,hn⟩
      exact hn (hle u hu)
  · rintro ⟨hz,hzs,hn⟩
    refine ⟨hz,?_⟩
    intro u hu
    by_contra hnot
    exact hn ⟨hzs 0,u,hu,hnot⟩

theorem gammaPullback_mem_codeValue_iff (A : Set (Values.Gamma (M := M)))
    (t : M) (ht : NonzeroRV t) :
    t ∈ Values.gammaPullback A ↔ codeValue t ∈ A := by
  rw [codeValue,dif_pos ht]
  constructor
  · rintro ⟨hr,h0,hA⟩
    exact hA
  · intro hA
    exact ⟨ht.1,ht.2,hA⟩

theorem original_le_codeValue_iff (t u : M) (ht : NonzeroRV t) (hu : NonzeroRV u) :
    iLe t u ↔ codeValue t ≤ codeValue u :=
  (rv_le_normalize t u ht.1 hu.1).symm.trans (codeLe_iff t u ht hu)

theorem leastCodes_gammaPullback_min (F : Finset (Values.Gamma (M := M))) (hne : F.Nonempty) :
    leastCodes (Values.gammaPullback (F : Set (Values.Gamma (M := M)))) =
      Values.gammaPullback {F.min' hne} := by
  ext t
  constructor
  · rintro ⟨ht,hle⟩
    obtain ⟨hr,h0,hF⟩ := ht
    have htNZ : NonzeroRV t := ⟨hr,h0⟩
    have htF : codeValue t ∈ F :=
      (gammaPullback_mem_codeValue_iff _ t htNZ).mp ⟨hr,h0,hF⟩
    obtain ⟨u,hu,he⟩ := codeValue_surjective (F.min' hne)
    have huF : u ∈ Values.gammaPullback (F : Set (Values.Gamma (M := M))) :=
      (gammaPullback_mem_codeValue_iff _ u hu).mpr (he.symm ▸ F.min'_mem hne)
    have htmin := (original_le_codeValue_iff t u htNZ hu).mp (hle u huF)
    rw [he] at htmin
    exact (gammaPullback_mem_codeValue_iff _ t htNZ).mpr
      (le_antisymm htmin (F.min'_le _ htF))
  · intro ht
    obtain ⟨hr,h0,hm⟩ := ht
    have htNZ : NonzeroRV t := ⟨hr,h0⟩
    have he : codeValue t = F.min' hne :=
      (gammaPullback_mem_codeValue_iff _ t htNZ).mp ⟨hr,h0,hm⟩
    refine ⟨(gammaPullback_mem_codeValue_iff _ t htNZ).mpr (he.symm ▸ F.min'_mem hne),?_⟩
    intro u hu
    obtain ⟨huRV,hu0,huF⟩ := hu
    have huNZ : NonzeroRV u := ⟨huRV,hu0⟩
    apply (original_le_codeValue_iff t u htNZ huNZ).mpr
    rw [he]
    exact F.min'_le _ ((gammaPullback_mem_codeValue_iff _ u huNZ).mp ⟨huRV,hu0,huF⟩)

theorem gamma_finset_min_definable_base (B : Base (M := M))
    (F : Finset (Values.Gamma (M := M)))
    (hF : GammaDefinableOverBase B (F : Set (Values.Gamma (M := M)))) (hne : F.Nonempty) :
    GammaDefinableClosureAtBase B (F.min' hne) := by
  have h := leastCodes_definable_base B _ hF
  rwa [leastCodes_gammaPullback_min F hne] at h

theorem gammaPullback_sdiff (A C : Set (Values.Gamma (M := M))) :
    Values.gammaPullback (A \ C) = Values.gammaPullback A \ Values.gammaPullback C := by
  ext t
  constructor
  · rintro ⟨hr,h0,hA,hnC⟩
    refine ⟨⟨hr,h0,hA⟩,?_⟩
    rintro ⟨_,_,hC⟩
    exact hnC hC
  · rintro ⟨⟨hr,h0,hA⟩,hnC⟩
    exact ⟨hr,h0,hA,fun hC => hnC ⟨hr,h0,hC⟩⟩

theorem GammaDefinableOverBase.sdiff {B : Base (M := M)}
    {A C : Set (Values.Gamma (M := M))} (hA : GammaDefinableOverBase B A)
    (hC : GammaDefinableOverBase B C) : GammaDefinableOverBase B (A \ C) := by
  change DefinableAtBase B .rv (Values.gammaPullback (A \ C))
  rw [gammaPullback_sdiff]
  have h := hA.inter hC.compl
  change DefinableOverBase B (fun _ : Fin 1 => .rv)
    {z | z 0 ∈ Values.gammaPullback A \ Values.gammaPullback C}
  convert h using 1
  all_goals try rfl
  ext z
  change (z 0 ∈ Values.gammaPullback A ∧ z 0 ∉ Values.gammaPullback C) ↔
    z 0 ∈ Values.gammaPullback A ∧ ((∀ i : Fin 1, iRV (z i)) ∧ z 0 ∉ Values.gammaPullback C)
  constructor
  · rintro ⟨ha,hc⟩
    refine ⟨ha,?_,hc⟩
    intro i; fin_cases i
    exact hA.proper (z 0) ha
  · rintro ⟨ha,_,hc⟩
    exact ⟨ha,hc⟩

/-- The minimum-erasure induction follows the proof scheme inspected in
the concurrent Section4/GammaFiniteDefinablePoints source, now with the
actual arbitrary Gamma-named base and checked full-code operations. -/
theorem gamma_finset_element_definable_base (B : Base (M := M))
    (F : Finset (Values.Gamma (M := M)))
    (hF : GammaDefinableOverBase B (F : Set (Values.Gamma (M := M))))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ F) : GammaDefinableClosureAtBase B γ := by
  revert hF γ
  induction F using Finset.strongInductionOn
  rename_i F ih
  intro hF γ hγ
  have hne : F.Nonempty := ⟨γ,hγ⟩
  let m := F.min' hne
  have hm : GammaDefinableOverBase B {m} := gamma_finset_min_definable_base B F hF hne
  by_cases he : γ = m
  · exact he.symm ▸ hm
  · have hE : GammaDefinableOverBase B ((F.erase m : Finset _) : Set (Values.Gamma (M := M))) := by
      simpa only [Finset.coe_erase] using hF.sdiff hm
    exact ih (F.erase m) (Finset.erase_ssubset (F.min'_mem hne)) hE γ
      (Finset.mem_erase.mpr ⟨he,hγ⟩)

/-- Algebraic and definable closure agree on the actual ordered Gamma
imaginary, over arbitrary real/Gamma parameter bases. -/
theorem gamma_algebraic_iff_definable_base (B : Base (M := M))
    (γ : Values.Gamma (M := M)) :
    GammaAlgebraicAtBase B γ ↔ GammaDefinableClosureAtBase B γ := by
  constructor
  · rintro ⟨A,hA,hfin,hγ⟩
    have hF : GammaDefinableOverBase B (hfin.toFinset : Set (Values.Gamma (M := M))) := by
      simpa only [hfin.coe_toFinset] using hA
    exact gamma_finset_element_definable_base B hfin.toFinset hF γ (hfin.mem_toFinset.mpr hγ)
  · intro hγ
    exact ⟨{γ},hγ,Set.finite_singleton γ,Set.mem_singleton γ⟩

end SpecialTransformations.Section3.GammaParameters
