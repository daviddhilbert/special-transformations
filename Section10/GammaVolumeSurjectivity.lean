import Section10.GammaVolumeLift
import Section10.RVVolumeSurjectivity
import Section10.RVPreparationData

/-! Gamma-valued surjectivity of the lift. Prepare finite RV data for the
full graph of Gamma codes, then descend the form itself to the lift labels. -/

set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.DefinableGeometry.Space.ofEmbedding
  SpecialTransformations.Section4.rawMixedSpace
  SpecialTransformations.Section4.rawVFSpace SpecialTransformations.Section4.rawRVSpace

open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9

noncomputable section

namespace SpecialTransformations.Section10

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n r : ℕ}
local notation "VF" => VFType (M := M)
local notation "RV" => CanonicalRV.RVSort M

private theorem gamma_codes_rv (hc : CanonicalStructure.IsCanonical (M := M))
    (z : (volumeGammaSpace hc).domain) (i : (volumeGammaSpace hc).Index) : iRV (z.val i) := by
  let IsRVCode (T : LRV.Structure M) (Q : @Space LRV M T) :=
    ∀ (c : @Space.domain LRV M T Q) (j : @Space.Index LRV M T Q), @iRV M T (c.val j)
  have transport {T U : LRV.Structure M} (e : T = U) (Q : @Space LRV M T) :
      IsRVCode T Q → IsRVCode U (e ▸ Q) := by
    cases e
    exact id
  have h := transport (normalize_eq_of_isCanonical hc) (@gammaSpace M sM hM)
  apply h _ z i
  intro c j
  change Fin 1 at j
  have he : j = 0 := Fin.eq_zero j
  subst j
  exact c.property.1

omit hM in
private theorem mixed_code_sorted (c : (rawMixedSpace (M := M) n r).domain) :
    ∀ i, sortEval (Coordinates.mixedSort i) (c.val i) := by
  rw [← mixedValues_decode c]
  intro i
  cases i with
  | inl i =>
    simpa only [Coordinates.mixedSort, mixedValues, Sum.elim_inl, vfValues, sortEval, iVF] using
      (((rawMixedSpace n r).decode c).1 i).property
  | inr i =>
    simpa only [Coordinates.mixedSort, mixedValues, Sum.elim_inr, rvValues, sortEval, iRV] using
      (((rawMixedSpace n r).decode c).2 i).property

/-- A Gamma form factors through a definable real RV tuple. The tuple
contains the old labels and the finite VF tests for the graph, and the
graph argument uses the same code for both Gamma outputs. -/
private theorem gamma_form_rv_data (hc : CanonicalStructure.IsCanonical (M := M))
    {A : DefSet (rawMixedSpace (M := M) n r) S} (ω : GammaVolumeForm hc A) :
    ∃ (d : ℕ) (ν : Map A (DefSet.univ (rawRVSpace d) S)), ∀ a b, ν a = ν b → ω a = ω b := by
  let P := rawMixedSpace (M := M) n r
  let Q := volumeGammaSpace hc
  let H := P.relation Q ω.graph
  have hsort (z) (hz : z ∈ H) :
      ∀ i, sortEval (Sum.elim Coordinates.mixedSort (fun _ : Q.Index => .rv) i) (z i) := by
    obtain ⟨hx, hy, _⟩ := hz
    intro i
    cases i with
    | inl j => exact mixed_code_sorted ⟨z ∘ Sum.inl, hx⟩ j
    | inr j =>
      change sortEval .rv (z (.inr j))
      simpa only [sortEval, iRV, Function.comp_apply] using gamma_codes_rv hc ⟨z ∘ Sum.inr, hy⟩ j
  obtain ⟨d, F, hF, hFrv, hdata⟩ := exists_rv_preparation_data hc
    Coordinates.mixedSort H ω.graph_definable hsort
  let c (a : P.Carrier) : P.domain := ⟨mixedValues a, mixedValues_mem_domain a⟩
  let f (a : P.Carrier) : Fin (r + d) → RV :=
    Fin.append a.2 (fun i => ⟨F (mixedValues a) i, hFrv _ (mixed_code_sorted (c a)) i⟩)
  let G (z : P.Index → M) := Fin.append (z ∘ Sum.inr) (F z)
  have hG : S.DefinableMap LRV G := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [G, Fin.append_left, Function.comp_apply] using
        (Set.DefinableFun.proj (A := S) (i := (Sum.inr j : P.Index)) LRV)
    · simpa only [G, Fin.append_right] using hF j
  have hf (a : P.Carrier) : rvValues (f a) = G (mixedValues a) := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [rvValues, f, G, Fin.append_left, mixedValues, Function.comp_apply, Sum.elim_inr]
    · simp only [rvValues, f, G, Fin.append_right]
  have hdom (z : P.domain) : G z.val ∈ (rawRVSpace (r + d)).domain := by
    refine ⟨f (P.decode z), ?_⟩
    rw [hf, mixedValues_decode]
  let ν : Map A (DefSet.univ (rawRVSpace (r + d)) S) := Map.ofCodes A f G hG hdom (by
    intro z
    apply rvValues_injective
    rw [rvValues_decode, hf, mixedValues_decode])
  refine ⟨r + d, ν, ?_⟩
  intro a b he
  have h := congrArg (fun p : DefSet.univ (rawRVSpace (r + d)) S => rvValues p.val) he
  change rvValues (f a.val) = rvValues (f b.val) at h
  rw [hf, hf] at h
  have hlabels (j : Fin r) : (a.val.2 j).val = (b.val.2 j).val := by
    simpa only [G, Fin.append_left, mixedValues, Function.comp_apply, Sum.elim_inr, rvValues] using
      congrFun h (Fin.castAdd d j)
  have htests : F (mixedValues a.val) = F (mixedValues b.val) := by
    funext j
    simpa only [G, Fin.append_right] using congrFun h (Fin.natAdd r j)
  obtain ⟨t, ht⟩ := Q.onto (ω a).val
  have hab := hdata (mixedValues a.val) (mixedValues b.val) t.val
    (mixed_code_sorted (c a.val)) (mixed_code_sorted (c b.val)) (gamma_codes_rv hc t) (by
      intro i hi
      cases i with
      | inl j => cases hi
      | inr j => exact hlabels j) htests
  have hgraph (p : A) : Sum.elim (mixedValues p.val) t.val ∈ H ↔ (ω p).val = Q.decode t := by
    change Sum.elim (c p.val).val t.val ∈ P.relation Q ω.graph ↔ _
    rw [P.relation_decode Q, show P.decode (c p.val) = p.val from decode_mixedValues p.val,
      ω.graph_apply]
  have ha := (hgraph a).mpr ht.symm
  exact Subtype.ext (((hgraph b).mp (hab.mp ha)).trans ht).symm

/-- The Gamma-valued case of Theorem 10.4 in positive degree. The lifted
form is definable on the finite-volume RV labels over the original base. -/
theorem theorem_10_4_gamma_volume [CharZero VF]
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (_hB : VFGammaGeneratedBase ⟨(C.base : Set M), Ξ⟩)
    {k : ℕ} (A : DefSet (rawMixedSpace (M := M) (k + 1) r) (C.base : Set M))
    (hfin : ∀ a, {t | (a, t) ∈ A.carrier}.Finite) (ω : GammaVolumeForm hc A) :
    ∃ U : GammaVolumeObject hc (C.base : Set M) k,
      ∃ g : EssentialVFMap A (rvLift U.underlying.obj), GammaMeasurePreserving g ω U.liftForm := by
  obtain ⟨_, ν, hν⟩ := gamma_form_rv_data hc ω
  obtain ⟨U, η, g, _, hg⟩ := exists_lift_preserving_rv_determined_map hc C A hfin ω ν hν
  let G : GammaVolumeObject hc (C.base : Set M) k := ⟨U, η⟩
  refine ⟨G, g, fun a => ⟨1, (hg a).1, ?_⟩⟩
  rw [map_one, mul_one]
  have h : G.liftForm ⟨(g.map a).val, g.target_subset (g.map a).property⟩ =
      ω ⟨a.val, g.source_subset a.property⟩ := (hg a).2
  unfold gammaFormValue
  rw [h]

end SpecialTransformations.Section10
