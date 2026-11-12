module

public import Section7.GammaVolumeCorrespondence
public import Section5.GammaLiftRelation
public import Section7.LiftedIsomorphism

@[expose] public section

/-! Lift invariance for isomorphisms definable over the original named Gamma base. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5

noncomputable section

namespace SpecialTransformations.Section7

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {k : ℕ}
variable {U V : GammaRVObject B k}

def gammaLiftGraph (F : rvObjectDomain U.object → rvObjectDomain V.object)
    (A : Set (Fin (k + k) → M))
    (p : Point (M := M) k (rvObjectArity U.object))
    (q : Point (M := M) k (rvObjectArity V.object)) : Prop :=
  p ∈ U.lift ∧ q ∈ V.lift ∧
    (∃ u : rvObjectDomain U.object, u.val = p.2 ∧ (F u).val = q.2) ∧
    productTuple (fun i => (p.1 i).val) (fun i => (q.1 i).val) ∈ A

theorem volume_of_lift (U : GammaRVObject B k) (p : U.lift) :
    ∃ u : rvObjectDomain U.object, u.val = p.val.2 ∧
      gammaVolumeValue U u = fun i => rv (p.val.1 i) := by
  obtain ⟨u, hlabel, hvolume⟩ := p.property
  exact ⟨u, hlabel, hvolume.trans (@normalized_tupleRV M sM hM k p.val.1)⟩

theorem mem_lift_of_volume (U : GammaRVObject B k)
    (p : Point (M := M) k (rvObjectArity U.object))
    (u : rvObjectDomain U.object) (hlabel : u.val = p.2)
    (hvolume : gammaVolumeValue U u = fun i => rv (p.1 i)) : p ∈ U.lift :=
  ⟨u, hlabel, hvolume.trans (@normalized_tupleRV M sM hM k p.1).symm⟩

private theorem vfPoint_in_volume_fibre (x : Fin k → VF (M := M))
    (t : Fin k → RV (M := M)) (h : t = fun i => rv (x i)) :
    (fun i => (x i).val) ∈ rawTupleFibre (fun i => (t i).val) := by
  intro i
  exact ⟨(x i).property,
    (congrArg Subtype.val (congrFun h i)).symm⟩

theorem gammaLiftGraph_existsUnique_right (F : rvObjectDomain U.object → rvObjectDomain V.object)
    (A : Set (Fin (k + k) → M))
    (hA : gammaRawVolumeCorrespondence U V F ⊆ rawLiftDomain A) (p : U.lift) :
    ∃! q, gammaLiftGraph F A p.val q := by
  obtain ⟨u, hu, hvol⟩ := volume_of_lift U p
  let t (i : Fin k) := (gammaVolumeValue U u i).val
  let s (i : Fin k) := (gammaVolumeValue V (F u) i).val
  have hgood := hA (show productTuple t s ∈ gammaRawVolumeCorrespondence U V F from ⟨u, rfl⟩)
  have ht : productTuple t s ∘ productLeft k k = t := funext (productTuple_left t s)
  have hs : productTuple t s ∘ productRight k k = s := funext (productTuple_right t s)
  have hg := hgood.1
  change ∀ a ∈ rawTupleFibre (productTuple t s ∘ productLeft k k),
    ∃! b, b ∈ rawTupleFibre (productTuple t s ∘ productRight k k) ∧ productTuple a b ∈ A at hg
  rw [ht, hs] at hg
  obtain ⟨b, hb, hunique⟩ := hg _ (vfPoint_in_volume_fibre p.val.1 _ hvol)
  let b' : Fin k → VF (M := M) := fun i => ⟨b i, (hb.1 i).1⟩
  have hbvol : gammaVolumeValue V (F u) = fun i => rv (b' i) := by
    funext i
    apply Subtype.ext
    exact (hb.1 i).2.symm
  let q : Point (M := M) k (rvObjectArity V.object) := (b', (F u).val)
  refine ⟨q, ⟨p.property, mem_lift_of_volume V q (F u) rfl hbvol, ⟨u, hu, rfl⟩, hb.2⟩, ?_⟩
  intro q' hq'
  obtain ⟨u', hu', hF⟩ := hq'.2.2.1
  have huu : u' = u := Subtype.ext (hu'.trans hu.symm)
  subst u'
  obtain ⟨v', hv', hvvol⟩ := volume_of_lift V ⟨q', hq'.2.1⟩
  have hvv : v' = F u := Subtype.ext (hv'.trans hF.symm)
  subst v'
  have he := hunique (fun i => (q'.1 i).val)
    ⟨vfPoint_in_volume_fibre q'.1 _ hvvol, hq'.2.2.2⟩
  exact Prod.ext (funext fun i => Subtype.ext (congrFun he i)) hF.symm

theorem gammaLiftGraph_existsUnique_left (F : rvObjectDomain U.object ≃ rvObjectDomain V.object)
    (A : Set (Fin (k + k) → M))
    (hA : gammaRawVolumeCorrespondence U V F ⊆ rawLiftDomain A) (q : V.lift) :
    ∃! p, gammaLiftGraph F A p q.val := by
  let A' := {z : Fin (k + k) → M | z ∘ swapPairCoordinates k ∈ A}
  have hA' : gammaRawVolumeCorrespondence V U F.symm ⊆ rawLiftDomain A' := by
    rintro z ⟨v, rfl⟩
    have h := hA (show productTuple (fun i => (gammaVolumeValue U (F.symm v) i).val)
        (fun i => (gammaVolumeValue V v i).val) ∈ gammaRawVolumeCorrespondence U V F from
      ⟨F.symm v, by rw [Equiv.apply_symm_apply]⟩)
    exact rawLiftDomain_swap h
  apply (existsUnique_congr (fun p => ?_)).mp (gammaLiftGraph_existsUnique_right F.symm A' hA' q)
  unfold gammaLiftGraph
  have hlabel :
      (∃ v : rvObjectDomain V.object, v.val = q.val.2 ∧ (F.symm v).val = p.2) ↔
      (∃ u : rvObjectDomain U.object, u.val = p.2 ∧ (F u).val = q.val.2) := by
    constructor
    · rintro ⟨v, hv, hp⟩
      exact ⟨F.symm v, hp, by rw [Equiv.apply_symm_apply]; exact hv⟩
    · rintro ⟨u, hu, hq⟩
      exact ⟨F u, hq, by rw [Equiv.symm_apply_apply]; exact hu⟩
  simp only [A', Set.mem_ofPred_eq, productTuple_swapPairCoordinates, hlabel]
  tauto

theorem gammaLiftIso_of_graph (F : rvObjectDomain U.object ≃ rvObjectDomain V.object)
    (A : Set (Fin (k + k) → M))
    (hA : gammaRawVolumeCorrespondence U V F ⊆ rawLiftDomain A)
    (hGraph : GammaGraphDefinable B (gammaLiftGraph F A)) :
    Nonempty (GammaIso B U.lift V.lift) := by
  let R := gammaLiftGraph F A
  have hRight (p : U.lift) := gammaLiftGraph_existsUnique_right F A hA p
  have hLeft (q : V.lift) := gammaLiftGraph_existsUnique_left F A hA q
  let f (p : U.lift) : V.lift :=
    ⟨(hRight p).exists.choose, (hRight p).exists.choose_spec.2.1⟩
  have hf (p : U.lift) : R p.val (f p).val := (hRight p).exists.choose_spec
  have hBij : Function.Bijective f := by
    constructor
    · intro p q he
      apply Subtype.ext
      exact (hLeft (f q)).unique (by simpa only [he] using hf p) (hf q)
    · intro q
      obtain ⟨p, hp, _⟩ := hLeft q
      let a : U.lift := ⟨p, hp.1⟩
      exact ⟨a, Subtype.ext ((hRight a).unique (hf a) hp)⟩
  refine ⟨⟨Equiv.ofBijective f hBij, ?_⟩⟩
  apply GammaGraphDefinable.congr hGraph
  intro p q
  constructor
  · intro hp
    let a : U.lift := ⟨p, hp.1⟩
    exact ⟨a, rfl, (hRight a).unique (hf a) hp⟩
  · rintro ⟨a, rfl, hq⟩
    exact hq ▸ hf a

private theorem vfPairGraph_definable (hcan : CanonicalStructure.IsCanonical (M := M))
    (A : Set (Fin (k + k) → M)) (hA : B.real.Definable LRV A) (m l : ℕ) :
    GammaGraphDefinable B (fun (p : Point (M := M) k m) (q : Point (M := M) k l) =>
      productTuple (fun i => (p.1 i).val) (fun i => (q.1 i).val) ∈ A) := by
  let σ := Fin.append (gammaPointSort k m) (gammaPointSort k l)
  let π : Fin (k + k) → Fin ((k + m) + (k + l)) :=
    Fin.addCases (fun i => Fin.castAdd (k + l) (Fin.castAdd m i))
      (fun i => Fin.natAdd (k + m) (Fin.castAdd l i))
  let Z : Set (Fin ((k + m) + (k + l)) → M) :=
    {z | z ∘ π ∈ A ∧ ∀ i, sortEval (σ i) (z i)}
  have hZ : B.real.Definable LRV Z :=
    (hA.preimage_comp π).inter (sortedUniverse_definable B.real σ).raw_definable
  have hZ' := real_definableOverBase B σ Z
    (raw_definableOver_sorted hcan B.real σ Z hZ (fun _ hz => hz.2))
  unfold GammaGraphDefinable
  convert hZ' using 1
  have hcode (p : Point (M := M) k m) (q : Point (M := M) k l) :
      Fin.append (gammaPointCode p) (gammaPointCode q) ∘ π =
        productTuple (fun i => (p.1 i).val) (fun i => (q.1 i).val) := by
    apply productTuple_ext
    · intro i
      rw [productTuple_left]
      change Fin.append (gammaPointCode p) (gammaPointCode q) (π (Fin.castAdd k i)) = _
      simp only [π, Fin.addCases_left, Fin.append_left, gammaPointCode, vfAt]
    · intro i
      rw [productTuple_right]
      change Fin.append (gammaPointCode p) (gammaPointCode q) (π (Fin.natAdd k i)) = _
      simp only [π, Fin.addCases_right, Fin.append_right, gammaPointCode, Fin.append_left, vfAt]
  have hsort {r : ℕ} (p : Point (M := M) k r) (i : Fin (k + r)) :
      sortEval (gammaPointSort k r i) (gammaPointCode p i) := by
    cases i using Fin.addCases with
    | left i => simpa only [gammaPointSort, gammaPointCode, Fin.append_left, vfAt, sortEval, iVF]
        using (p.1 i).property
    | right i => simpa only [gammaPointSort, gammaPointCode, Fin.append_right, sortEval, iRV]
        using (p.2 i).property
  ext z
  constructor
  · rintro ⟨p, q, h, rfl⟩
    refine ⟨(hcode p q).symm ▸ h, ?_⟩
    intro i
    cases i using Fin.addCases with
    | left i => simpa only [σ, Fin.append_left] using hsort p i
    | right i => simpa only [σ, Fin.append_right] using hsort q i
  · intro hz
    let a (i : Fin (k + m)) := z (Fin.castAdd (k + l) i)
    let b (i : Fin (k + l)) := z (Fin.natAdd (k + m) i)
    have ha (i) : sortEval (gammaPointSort k m i) (a i) := by
      simpa only [a, σ, Fin.append_left] using hz.2 (Fin.castAdd (k + l) i)
    have hb (i) : sortEval (gammaPointSort k l i) (b i) := by
      simpa only [b, σ, Fin.append_right] using hz.2 (Fin.natAdd (k + m) i)
    let p : Point (M := M) k m :=
      (fun i => ⟨a (Fin.castAdd m i), by simpa only [gammaPointSort, Fin.append_left, sortEval, iVF] using ha (Fin.castAdd m i)⟩,
        fun i => ⟨a (Fin.natAdd k i), by simpa only [gammaPointSort, Fin.append_right, sortEval, iRV] using ha (Fin.natAdd k i)⟩)
    let q : Point (M := M) k l :=
      (fun i => ⟨b (Fin.castAdd l i), by simpa only [gammaPointSort, Fin.append_left, sortEval, iVF] using hb (Fin.castAdd l i)⟩,
        fun i => ⟨b (Fin.natAdd k i), by simpa only [gammaPointSort, Fin.append_right, sortEval, iRV] using hb (Fin.natAdd k i)⟩)
    have hp : gammaPointCode p = a := by
      funext i
      cases i using Fin.addCases <;> simp [gammaPointCode, vfAt, p]
    have hq : gammaPointCode q = b := by
      funext i
      cases i using Fin.addCases <;> simp [gammaPointCode, vfAt, q]
    have he : Fin.append (gammaPointCode p) (gammaPointCode q) = z := by
      rw [hp, hq]
      funext i
      cases i using Fin.addCases <;> simp [a, b]
    refine ⟨p, q, ?_, he⟩
    change productTuple (fun i => (p.1 i).val) (fun i => (q.1 i).val) ∈ A
    rw [← hcode p q, he]
    exact hz.1

theorem gammaLiftGraph_definable (hcan : CanonicalStructure.IsCanonical (M := M))
    (e : GammaRVIso U V) (A : Set (Fin (k + k) → M)) (hA : B.real.Definable LRV A) :
    GammaGraphDefinable B (gammaLiftGraph e.equiv A) := by
  let m := rvObjectArity U.object
  let l := rvObjectArity V.object
  let L := gammaLogicInput B
  have h := e.graph.preimage_maps (pointLabels B.real k m) (pointLabels B.real k l)
  have hp := L.restrict_graph U.lift_definable h
  have hq := L.swap_graph (L.restrict_graph V.lift_definable (L.swap_graph hp))
  have hR := hq.inter (vfPairGraph_definable hcan A hA m l)
  apply GammaGraphDefinable.congr hR
  intro p q
  unfold gammaLiftGraph gammaRVLabelGraph
  rw [pointLabels_snd, pointLabels_snd]
  tauto

theorem GammaRVIso.liftIso (hcan : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk B.real < κ)
    (hB : VFGammaGeneratedBase B) (e : GammaRVIso U V) :
    Nonempty (GammaIso B U.lift V.lift) := by
  obtain ⟨A, hA, hlift⟩ := e.exists_original_volume_lift hκ hs h00 hsmall hB
  exact gammaLiftIso_of_graph e.equiv A hlift (gammaLiftGraph_definable hcan e A hA)

end SpecialTransformations.Section7
