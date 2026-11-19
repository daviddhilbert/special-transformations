import Section9.SimultaneousHeadCover
import Section9.FiniteLabelPartition
import Section9.GammaHeadCover
import Section9.GammaLiftGluing

/-! Gamma counterparts of the simultaneous finite head cover and of the
disjoint refinement of a finite cover. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section7
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable gammaLogicInput)

namespace SpecialTransformations.Section9.GammaLift

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k n r : ℕ} {B : Base (M := M)}
local notation "RV" => CanonicalRV.RVSort M

theorem RVMapGamma.comp' {a b c : ℕ} {A : DefSet (rawRVSpace (M := M) a) S}
    {D : DefSet (rawRVSpace (M := M) b) S} {E : DefSet (rawRVSpace (M := M) c) S}
    {f : Map A D} {g : Map D E} (hf : RVMapGamma f B) (hg : RVMapGamma g B) : RVMapGamma (g.comp f) B := by
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr ((gammaLogicInput B).comp_graph hf hg)
  intro p q
  constructor
  · rintro ⟨m, ⟨u, hu, hm⟩, ⟨w, hw, hq⟩⟩
    have : w = f u := Subtype.ext (hw.trans hm.symm)
    subst this
    exact ⟨u, hu, hq⟩
  · rintro ⟨u, hu, hq⟩
    exact ⟨(Fin.elim0, (f u).val), ⟨u, hu, rfl⟩, ⟨f u, rfl, hq⟩⟩

theorem rv_image_gamma {a b : ℕ} {A : DefSet (rawRVSpace (M := M) a) S} {f : Map A (DefSet.univ (rawRVSpace (M := M) b) S)}
    (hf : RVMapGamma f B) : RVSetGamma f.image B := by
  have h := (gammaLogicInput B).image_graph hf
  unfold RVSetGamma
  convert h using 1
  ext q
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨(Fin.elim0, u.val), u, rfl, hu⟩
  · rintro ⟨p, u, _, hu⟩
    exact ⟨u, hu⟩

def gammaVolumePreimage {A : DefSet (rawRVSpace (M := M) r) S}
    (f : Map A (DefSet.univ (rawRVSpace (M := M) n) S)) (T : DefSet (rawRVSpace (M := M) n) S) :
    DefSet (rawRVSpace (M := M) r) S :=
  ⟨{z | ∃ a : A, a.val = z ∧ (f a).val ∈ T.carrier}, f.definable_preimage T.definable⟩

theorem gamma_finite_restricted_head_row {A : DefSet (rawRVSpace (M := M) r) S}
    (f : Map A (DefSet.univ (rawRVSpace (M := M) n) S)) (hf : f.FiniteFibres)
    (T : DefSet (rawRVSpace (M := M) n) S) (v : Fin k → Fin n) (hv : (rvHeadSelect v T).FiniteFibres)
    (x : Fin k → RV) : {u : A | (f u).val ∈ T.carrier ∧ (f u).val ∘ v = x}.Finite := by
  let D := {a : T | rvHeadSelect v T a = ⟨x, Set.mem_univ _⟩}
  have hD : D.Finite := hv ⟨x, Set.mem_univ _⟩
  let Q (a : T) : Set A := {u | f u = ⟨a.val, Set.mem_univ _⟩}
  have hQ (a : T) : (Q a).Finite := hf ⟨a.val, Set.mem_univ _⟩
  apply (hD.biUnion (fun a _ => hQ a)).subset
  rintro u ⟨hu, hx⟩
  let a : T := ⟨(f u).val, hu⟩
  refine Set.mem_iUnion₂.mpr ⟨a, ?_, ?_⟩
  · exact Subtype.ext hx
  · exact Subtype.ext rfl

theorem rv_preimage_gamma {A : DefSet (rawRVSpace (M := M) r) S}
    {f : Map A (DefSet.univ (rawRVSpace (M := M) n) S)} (hf : RVMapGamma f B)
    {T : DefSet (rawRVSpace (M := M) n) S} (hT : RVSetGamma T B) :
    RVSetGamma (gammaVolumePreimage f T) B := by
  have L := gammaLogicInput B
  have h := L.image_graph (L.restrict_graph hT (L.swap_graph hf))
  unfold RVSetGamma
  convert h using 1
  ext p
  constructor
  · rintro ⟨u, hu, hT'⟩
    exact ⟨(Fin.elim0, (f u).val), hT', u, hu, rfl⟩
  · rintro ⟨q, hq, u, hu, hfq⟩
    refine ⟨u, hu, ?_⟩
    rw [hfq]
    exact hq

theorem gamma_iUnion_set {I : Type} [Finite I] {a b : ℕ} {X : I → Set (Point (M := M) a b)}
    (h : ∀ i, GammaSetDefinable B (X i)) : GammaSetDefinable B (⋃ i, X i) := by
  classical
  letI := Fintype.ofFinite I
  have L := gammaLogicInput B
  have hs : ∀ s : Finset I, GammaSetDefinable B (⋃ i ∈ s, X i) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      convert L.sdiff (gamma_univ_set (B := B) (a := a) (b := b)) gamma_univ_set using 1
      simp
    | insert j s hj ih =>
      convert L.union (h j) ih using 1
      simp [Finset.set_biUnion_insert]
  convert hs Finset.univ using 1
  simp

theorem gamma_exists_disjoint_definable_refinement {ι : Type} [Finite ι] {a : ℕ}
    (D : ι → DefSet (rawRVSpace (M := M) a) S) (hD : ∀ i, RVSetGamma (D i) B) :
    ∃ E : ι → DefSet (rawRVSpace (M := M) a) S, (∀ i, (E i).carrier ⊆ (D i).carrier) ∧
      (∀ i, RVSetGamma (E i) B) ∧
      (∀ x, (∃ i, x ∈ (D i).carrier) → ∃ i, x ∈ (E i).carrier) ∧
      ∀ i j x, x ∈ (E i).carrier → x ∈ (E j).carrier → i = j := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  let P := rawRVSpace (M := M) a
  let e := Fintype.equivFin ι
  let earlier (i : ι) : DefSet P S :=
    ⟨⋃ j : {j : ι // e j < e i}, (D j.val).carrier, by
      change S.Definable LRV (P.preimage (⋃ j : {j : ι // e j < e i}, (D j.val).carrier))
      have he : P.preimage (⋃ j : {j : ι // e j < e i}, (D j.val).carrier) =
          ⋃ j : {j : ι // e j < e i}, P.preimage (D j.val).carrier := by
        ext z
        simp only [Set.mem_iUnion, Space.preimage, Set.mem_setOf_eq]
        aesop
      rw [he]
      exact Set.definable_iUnion_of_finite (fun j => (D j.val).definable)⟩
  let E i := (D i).sdiff (earlier i)
  have memEarlier (i : ι) (x : P.Carrier) : x ∈ (earlier i).carrier ↔
      ∃ j, e j < e i ∧ x ∈ (D j).carrier := by
    change x ∈ ⋃ j : {j : ι // e j < e i}, (D j.val).carrier ↔ _
    simp only [Set.mem_iUnion, Subtype.exists, exists_prop]
  refine ⟨E, fun i => Set.sdiff_subset, fun i => ?_, ?_, ?_⟩
  · have hE : GammaSetDefinable B (⋃ j : {j : ι // e j < e i},
        {p : Point (M := M) 0 a | p.2 ∈ (D j.val).carrier}) := gamma_iUnion_set (fun j => hD j.val)
    unfold RVSetGamma
    convert (gammaLogicInput B).sdiff (hD i) hE using 1
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_diff, Set.mem_iUnion]
    change p.2 ∈ (D i).carrier ∧ p.2 ∉ (earlier i).carrier ↔ _
    rw [memEarlier]
    simp
  · rintro x ⟨j, hj⟩
    let A := Finset.univ.filter (fun r => x ∈ (D (e.symm r)).carrier)
    have hA : A.Nonempty := ⟨e j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      simpa only [e.symm_apply_apply] using hj⟩⟩
    let i := e.symm (A.min' hA)
    refine ⟨i, (Finset.mem_filter.mp (A.min'_mem hA)).2, ?_⟩
    rintro h
    obtain ⟨k, hki, hk⟩ := (memEarlier i x).mp h
    have hkA : e k ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      simpa only [e.symm_apply_apply] using hk⟩
    have hle : e i ≤ e k := by
      simpa only [i, e.apply_symm_apply] using A.min'_le (e k) hkA
    exact (not_lt_of_ge hle) hki
  · intro i j x hi hj
    apply e.injective
    rcases lt_trichotomy (e i) (e j) with h | h | h
    · exact (hj.2 ((memEarlier j x).mpr ⟨i, h, hi.1⟩)).elim
    · exact h
    · exact (hi.2 ((memEarlier i x).mpr ⟨j, h, hj.1⟩)).elim

theorem gamma_exists_simultaneous_finite_head_cover
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (B : Base (M := M)) (hBS : B.real ⊆ (C.base : Set M)) (hkn : k ≤ n)
    {U V : RVFiniteObject (M := M) (C.base : Set M) n} (F : U ≅ V)
    (hUΓ : RVMapGamma U.obj.volume B) (hVΓ : RVMapGamma V.obj.volume B)
    (hFΓ : RVMapGamma ((finiteVolumeProperty (C.base : Set M) n).ι.mapIso F).hom.map B)
    (hU : rvDim U.obj.volume.image ≤ k) (hV : rvDim V.obj.volume.image ≤ k) :
    let f := ((finiteVolumeProperty (C.base : Set M) n).ι.mapIso F).hom.map
    ∃ a b : ℕ, ∃ P : Fin a × Fin b → DefSet (rawRVSpace (M := M) U.obj.arity) (C.base : Set M),
      ∃ v w : Fin a × Fin b → Fin k ↪ Fin n,
        (∀ i, (P i).carrier ⊆ U.obj.domain.carrier ∧ RVSetGamma (P i) B) ∧
        (∀ u : U.obj.domain, ∃ i, u.val ∈ (P i).carrier) ∧
        ∀ i x,
          {u : U.obj.domain | u.val ∈ (P i).carrier ∧ U.obj.value u ∘ v i = x}.Finite ∧
          {u : U.obj.domain | u.val ∈ (P i).carrier ∧ V.obj.value (f u) ∘ w i = x}.Finite := by
  let S := (C.base : Set M)
  let E := (finiteVolumeProperty S n).ι.mapIso F
  let f := U.obj.volume
  let g := V.obj.volume.comp E.hom.map
  have hgΓ : RVMapGamma g B := RVMapGamma.comp' hFΓ hVΓ
  obtain ⟨a, A, v, hv, hA⟩ := gamma_exists_finite_head_cover hc C B hBS hkn U.obj.volume.image
    (rv_image_gamma hUΓ) hU
  obtain ⟨b, B', w, hw, hB⟩ := gamma_exists_finite_head_cover hc C B hBS hkn V.obj.volume.image
    (rv_image_gamma hVΓ) hV
  let P (i : Fin a × Fin b) := (gammaVolumePreimage f (A i.1)).inter (gammaVolumePreimage g (B' i.2))
  have hp (u : U.obj.domain) (i : Fin a × Fin b) : u.val ∈ (P i).carrier ↔
      (f u).val ∈ (A i.1).carrier ∧ (g u).val ∈ (B' i.2).carrier := by
    constructor
    · rintro ⟨⟨u₁, h₁, hu₁⟩, ⟨u₂, h₂, hu₂⟩⟩
      exact ⟨(show u₁ = u from Subtype.ext h₁) ▸ hu₁, (show u₂ = u from Subtype.ext h₂) ▸ hu₂⟩
    · rintro ⟨hu, hu'⟩
      exact ⟨⟨u, rfl, hu⟩, ⟨u, rfl, hu'⟩⟩
  have hg : g.FiniteFibres := V.property.comp (Map.finiteFibres_of_injective (fun u u' h => by
    have he := congrArg E.inv.map h
    rwa [Section7.rvIso_inv_apply, Section7.rvIso_inv_apply] at he))
  refine ⟨a, b, P, v ∘ Prod.fst, w ∘ Prod.snd, ?_, ?_, ?_⟩
  · intro i
    refine ⟨?_, ?_⟩
    · rintro _ ⟨⟨u, rfl, _⟩, _⟩
      exact u.property
    · exact (gammaLogicInput B).inter (rv_preimage_gamma hUΓ (hv i.1).2.1)
        (rv_preimage_gamma hgΓ (hw i.2).2.1)
  · intro u
    obtain ⟨i, hi⟩ := hA ⟨(f u).val, Set.mem_range_self u⟩
    obtain ⟨j, hj⟩ := hB ⟨(g u).val, Set.mem_range_self (E.hom.map u)⟩
    exact ⟨(i,j), (hp u (i,j)).mpr ⟨hi,hj⟩⟩
  · intro i x
    exact ⟨(gamma_finite_restricted_head_row f U.property _ _ (hv i.1).2.2 x).subset
      (fun u hu => ⟨((hp u i).mp hu.1).1, hu.2⟩),
      (gamma_finite_restricted_head_row g hg _ _ (hw i.2).2.2 x).subset
      (fun u hu => ⟨((hp u i).mp hu.1).2, hu.2⟩)⟩

end SpecialTransformations.Section9.GammaLift
