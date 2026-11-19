import Section7.GammaLiftEquivalence
import Section9.LiftLabelRepresentatives
import Section9.GammaPointMaps

/-! Gamma certificates for RV objects, RV maps and mixed maps whose codes
lie in an arbitrary code set `S`, and their basic closure properties: the
canonical lift of a Gamma RV object is Gamma-definable, the lifted graph of
a Gamma RV map along a set over the real base is Gamma-definable, and the raw
volume correspondence of a Gamma RV map is definable over the Gamma base. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section7
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable gammaLogicInput
  gammaPointCode gammaPointSort vfAt pointLabels pointVolumes pointLabels_snd pointVolumes_snd)

namespace SpecialTransformations.Section9.GammaLift

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M} {B : Base (M := M)}

/-- An RV set with a Gamma-definable carrier. -/
def RVSetGamma {a : ℕ} (A : DefSet (rawRVSpace (M := M) a) S) (B : Base (M := M)) : Prop :=
  GammaSetDefinable B {p : Point (M := M) 0 a | p.2 ∈ A.carrier}

/-- An RV map with a Gamma-definable graph. -/
def RVMapGamma {a b : ℕ} {A : DefSet (rawRVSpace (M := M) a) S} {D : DefSet (rawRVSpace (M := M) b) S}
    (f : Map A D) (B : Base (M := M)) : Prop :=
  GammaGraphDefinable B (fun (p : Point (M := M) 0 a) (q : Point (M := M) 0 b) =>
    ∃ u : A, u.val = p.2 ∧ (f u).val = q.2)

/-- A mixed map with a Gamma-definable graph. -/
def MixedMapGamma {k a l b : ℕ} {A : DefSet (rawMixedSpace (M := M) k a) S}
    {D : DefSet (rawMixedSpace (M := M) l b) S} (f : Map A D) (B : Base (M := M)) : Prop :=
  GammaGraphDefinable B (fun (p : Point (M := M) k a) (q : Point (M := M) l b) =>
    ∃ x : A, x.val = p ∧ (f x).val = q)

/-- A mixed set with a Gamma-definable carrier. -/
def MixedSetGamma {k a : ℕ} (A : DefSet (rawMixedSpace (M := M) k a) S) (B : Base (M := M)) : Prop :=
  GammaSetDefinable B A.carrier

theorem RVMapGamma.domain {a b : ℕ} {A : DefSet (rawRVSpace (M := M) a) S}
    {D : DefSet (rawRVSpace (M := M) b) S} {f : Map A D} (hf : RVMapGamma f B) : RVSetGamma A B := by
  have h := (gammaLogicInput B).image_graph ((gammaLogicInput B).swap_graph hf)
  unfold RVSetGamma
  convert h using 1
  ext p
  constructor
  · intro hp
    exact ⟨(Fin.elim0, (f ⟨p.2, hp⟩).val), ⟨p.2, hp⟩, rfl, rfl⟩
  · rintro ⟨q, u, hu, _⟩
    change p.2 ∈ A.carrier
    rw [← hu]
    exact u.property

theorem MixedMapGamma.domain {k a l b : ℕ} {A : DefSet (rawMixedSpace (M := M) k a) S}
    {D : DefSet (rawMixedSpace (M := M) l b) S} {f : Map A D} (hf : MixedMapGamma f B) :
    MixedSetGamma A B := by
  have h := (gammaLogicInput B).image_graph ((gammaLogicInput B).swap_graph hf)
  unfold MixedSetGamma
  convert h using 1
  ext p
  constructor
  · intro hp
    exact ⟨(f ⟨p, hp⟩).val, ⟨p, hp⟩, rfl, rfl⟩
  · rintro ⟨q, x, hx, _⟩
    rw [← hx]
    exact x.property

theorem MixedMapGamma.image {k a l b : ℕ} {A : DefSet (rawMixedSpace (M := M) k a) S}
    {D : DefSet (rawMixedSpace (M := M) l b) S} {f : Map A D} (hf : MixedMapGamma f B)
    (hsurj : Function.Surjective f) : MixedSetGamma D B := by
  have h := (gammaLogicInput B).image_graph hf
  unfold MixedSetGamma
  convert h using 1
  ext q
  constructor
  · intro hq
    obtain ⟨x, hx⟩ := hsurj ⟨q, hq⟩
    exact ⟨x.val, x, rfl, congrArg Subtype.val hx⟩
  · rintro ⟨p, x, _, hx⟩
    rw [← hx]
    exact (f x).property

/-- The canonical lift of an RV object with a Gamma volume graph is Gamma-definable. -/
theorem lift_gamma {n : ℕ} (U : RVObject (M := M) S n) (hU : RVMapGamma U.volume B) :
    MixedSetGamma (rvLift U) B := by
  have h := (hU.preimage_maps (pointLabels B.real n U.arity) (pointVolumes B.real n U.arity)).diagonal
  unfold MixedSetGamma
  convert h using 1
  ext p
  let a : SpecialTransformations.Section5.PresentedSet.univ
    (SpecialTransformations.Section5.pointSpace (M := M) n U.arity) B.real := ⟨p, Set.mem_univ _⟩
  change (∃ u : U.domain, u.val = p.2 ∧ U.value u = tupleRV p.1) ↔
    ∃ u : U.domain, u.val = (pointLabels B.real n U.arity a).val.2 ∧
      (U.volume u).val = (pointVolumes B.real n U.arity a).val.2
  rw [pointLabels_snd, pointVolumes_snd]
  rfl

/-- A real relation between the VF coordinates of two mixed points has a Gamma graph. -/
theorem vf_pair_graph_gamma (hcan : CanonicalStructure.IsCanonical (M := M)) {k : ℕ}
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

/-- The lifted graph of a Gamma RV map along a set over the real base is Gamma. -/
theorem lifted_graph_gamma (hcan : CanonicalStructure.IsCanonical (M := M)) {k : ℕ}
    {U V : RVObject (M := M) S k} (hU : RVMapGamma U.volume B) (hV : RVMapGamma V.volume B)
    (F : Map U.domain V.domain) (hF : RVMapGamma F B)
    (A : Set (Fin (k + k) → M)) (hA : B.real.Definable LRV A) :
    GammaGraphDefinable B (fun (p : Point (M := M) k U.arity) (q : Point (M := M) k V.arity) =>
      liftedGraph F A p q) := by
  let L := gammaLogicInput B
  have h := hF.preimage_maps (pointLabels B.real k U.arity) (pointLabels B.real k V.arity)
  have hp := L.restrict_graph (lift_gamma U hU) h
  have hq := L.swap_graph (L.restrict_graph (lift_gamma V hV) (L.swap_graph hp))
  have hR := SpecialTransformations.Section5.GammaGraphDefinable.inter hq
    (vf_pair_graph_gamma hcan A hA U.arity V.arity)
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr hR
  intro p q
  rw [pointLabels_snd, pointLabels_snd]
  unfold liftedGraph
  change _ ↔ _ ∧ _ ∧ (∃ u : U.domain, u.val = p.2 ∧ (F u).val = q.2) ∧ _
  tauto

private def rvPairCoordinates (k : ℕ) : Fin (k + k) → Fin ((0 + k) + (0 + k)) :=
  Fin.addCases (fun i => Fin.castAdd (0 + k) (Fin.natAdd 0 i))
    (fun i => Fin.natAdd (0 + k) (Fin.natAdd 0 i))

private theorem rvPairCoordinates_sorted (k : ℕ) :
    (Fin.append (gammaPointSort 0 k) (gammaPointSort 0 k)) ∘ rvPairCoordinates k =
      fun _ => SortTag.rv := by
  funext i
  cases i using Fin.addCases with
  | left i => simp only [rvPairCoordinates, Function.comp_apply, Fin.addCases_left,
      Fin.append_left, gammaPointSort, Fin.append_right]
  | right i => simp only [rvPairCoordinates, Function.comp_apply, Fin.addCases_right,
      Fin.append_right, gammaPointSort]

private theorem rvPairCoordinates_code {k : ℕ} (p q : Point (M := M) 0 k) :
    Fin.append (gammaPointCode p) (gammaPointCode q) ∘ rvPairCoordinates k =
      productTuple (fun i => (p.2 i).val) (fun i => (q.2 i).val) := by
  apply productTuple_ext
  · intro i
    rw [productTuple_left]
    change Fin.append (gammaPointCode p) (gammaPointCode q)
      (rvPairCoordinates k (Fin.castAdd k i)) = _
    simp only [rvPairCoordinates, Fin.addCases_left, Fin.append_left,
      gammaPointCode, Fin.append_right]
  · intro i
    rw [productTuple_right]
    change Fin.append (gammaPointCode p) (gammaPointCode q)
      (rvPairCoordinates k (Fin.natAdd k i)) = _
    simp only [rvPairCoordinates, Fin.addCases_right, Fin.append_right, gammaPointCode]

/-- The raw volume correspondence of a Gamma RV map between Gamma objects. -/
theorem raw_volume_correspondence_gamma {k : ℕ} {U V : RVObject (M := M) S k}
    (hU : RVMapGamma U.volume B) (hV : RVMapGamma V.volume B)
    (F : Map U.domain V.domain) (hF : RVMapGamma F B) :
    DefinableOverBase B (fun _ => .rv) (rawVolumeCorrespondence F) := by
  let L := gammaLogicInput B
  have hvol := L.comp_graph (L.comp_graph (L.swap_graph hU) hF) hV
  have hh := DefinableOverBase.image_real hvol (rvPairCoordinates k)
  rw [rvPairCoordinates_sorted] at hh
  convert hh using 1
  ext z
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨_, ⟨(Fin.elim0, U.value u), (Fin.elim0, V.value (F u)),
      ⟨(Fin.elim0, (F u).val), ⟨(Fin.elim0, u.val), ⟨u, rfl, rfl⟩, ⟨u, rfl, rfl⟩⟩, ⟨F u, rfl, rfl⟩⟩, rfl⟩, ?_⟩
    exact rvPairCoordinates_code _ _
  · rintro ⟨_, ⟨p, q, ⟨y, ⟨x, ⟨u, hu, hp⟩, ⟨u', hu', hx⟩⟩, ⟨v, hv, hq⟩⟩, rfl⟩, rfl⟩
    have e₁ : u' = u := Subtype.ext (hu'.trans hu.symm)
    have e₂ : v = F u := Subtype.ext (hv.trans (e₁ ▸ hx).symm)
    refine ⟨u, ?_⟩
    show Fin.append (gammaPointCode p) (gammaPointCode q) ∘ rvPairCoordinates k = _
    rw [rvPairCoordinates_code, ← e₂]
    congr 1
    · funext i; exact congrArg Subtype.val (congrFun hp i).symm
    · funext i; exact congrArg Subtype.val (congrFun hq i).symm

end SpecialTransformations.Section9.GammaLift
