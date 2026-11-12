module

public import Section7.BalancedCorrespondence
public import Section5.GammaLift
public import Section5.GammaInvariantLogic

@[expose] public section

/-! Volume correspondence of a definable RV isomorphism over a named Gamma base. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5

noncomputable section

namespace SpecialTransformations.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {k : ℕ}

private def rvPoint {n : ℕ} (t : Fin n → RV (M := M)) : Point (M := M) 0 n :=
  (Fin.elim0, t)

def gammaVolumeValue (U : GammaRVObject B k) (u : rvObjectDomain U.object) :
    Fin k → RV (M := M) :=
  (rvObjectVolume U.object u).val

def gammaRVLabelGraph (U V : GammaRVObject B k)
    (F : rvObjectDomain U.object → rvObjectDomain V.object) :
    Point (M := M) 0 (rvObjectArity U.object) → Point (M := M) 0 (rvObjectArity V.object) → Prop :=
  fun p q => ∃ u : rvObjectDomain U.object, u.val = p.2 ∧ (F u).val = q.2

private def gammaVolumeGraph (U V : GammaRVObject B k)
    (F : rvObjectDomain U.object → rvObjectDomain V.object) :
    Point (M := M) 0 k → Point (M := M) 0 k → Prop :=
  fun t s => ∃ u : rvObjectDomain U.object, gammaVolumeValue U u = t.2 ∧ gammaVolumeValue V (F u) = s.2

theorem gammaVolumeGraph_definable (U V : GammaRVObject B k)
    (F : rvObjectDomain U.object → rvObjectDomain V.object)
    (hF : GammaGraphDefinable B (gammaRVLabelGraph U V F)) :
    GammaGraphDefinable B (gammaVolumeGraph U V F) := by
  let L := gammaLogicInput B
  have h := L.comp_graph (L.comp_graph (L.swap_graph U.volume_graph) hF) V.volume_graph
  apply GammaGraphDefinable.congr h
  intro t s
  constructor
  · rintro ⟨q, ⟨p, ⟨u, hu, ht⟩, ⟨a, ha, hq⟩⟩, ⟨b, hb, hs⟩⟩
    have ha' : a = u := Subtype.ext (ha.trans hu.symm)
    have hb' : b = F a := Subtype.ext (hb.trans hq.symm)
    have hs' : gammaVolumeValue V b = s.2 := hs
    rw [hb', ha'] at hs'
    exact ⟨u, ht, hs'⟩
  · rintro ⟨u, ht, hs⟩
    exact ⟨rvPoint (F u).val, ⟨rvPoint u.val, ⟨u, rfl, ht⟩, ⟨u, rfl, rfl⟩⟩, F u, rfl, hs⟩

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

private theorem rvPairCoordinates_code (p q : Point (M := M) 0 k) :
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

def gammaRawVolumeCorrespondence (U V : GammaRVObject B k)
    (F : rvObjectDomain U.object → rvObjectDomain V.object) : Set (Fin (k + k) → M) :=
  {z | ∃ u : rvObjectDomain U.object,
    productTuple (fun i => (gammaVolumeValue U u i).val) (fun i => (gammaVolumeValue V (F u) i).val) = z}

theorem gammaRawVolumeCorrespondence_definable (U V : GammaRVObject B k)
    (F : rvObjectDomain U.object → rvObjectDomain V.object)
    (hF : GammaGraphDefinable B (gammaRVLabelGraph U V F)) :
    DefinableOverBase B (fun _ => .rv) (gammaRawVolumeCorrespondence U V F) := by
  have h := gammaVolumeGraph_definable U V F hF
  have hh := DefinableOverBase.image_real h (rvPairCoordinates k)
  rw [rvPairCoordinates_sorted] at hh
  convert hh using 1
  ext z
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨_, ⟨rvPoint (gammaVolumeValue U u), rvPoint (gammaVolumeValue V (F u)), ⟨u, rfl, rfl⟩, rfl⟩, ?_⟩
    exact rvPairCoordinates_code _ _
  · rintro ⟨_, ⟨p, q, ⟨u, hu, hv⟩, rfl⟩, rfl⟩
    refine ⟨u, ?_⟩
    change _ = Fin.append (gammaPointCode p) (gammaPointCode q) ∘ rvPairCoordinates k
    rw [rvPairCoordinates_code, hu, hv]

/-- An isomorphism of the paper's RV objects over named Gamma parameters. -/
structure GammaRVIso (U V : GammaRVObject B k) where
  equiv : rvObjectDomain U.object ≃ rvObjectDomain V.object
  graph : GammaGraphDefinable B (gammaRVLabelGraph U V equiv)
  weight : ∀ u, rawWeight (fun i => (gammaVolumeValue U u i).val) =
    rawWeight (fun i => (gammaVolumeValue V (equiv u) i).val)
  leftFinite : ∀ b : Fin k → M,
    {a : Fin k → M | productTuple a b ∈ gammaRawVolumeCorrespondence U V equiv}.Finite
  rightFinite : ∀ a : Fin k → M,
    {b : Fin k → M | productTuple a b ∈ gammaRawVolumeCorrespondence U V equiv}.Finite

theorem GammaRVIso.exists_original_volume_lift {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hB : VFGammaGeneratedBase B)
    {U V : GammaRVObject B k} (e : GammaRVIso U V) :
    ∃ A : Set (Fin (k + k) → M), B.real.Definable LRV A ∧
      gammaRawVolumeCorrespondence U V e.equiv ⊆ rawLiftDomain A := by
  apply exists_balancedCorrespondence_lift hκ hs h00 B hsmall hB
    Values.presentationValuation Values.presentation_compatible k _
    (gammaRawVolumeCorrespondence_definable U V e.equiv e.graph)
  · intro t s hz
    obtain ⟨u, hu⟩ := hz
    have ht : (fun i => (gammaVolumeValue U u i).val) = t := funext fun i => by
      simpa only [productTuple_left] using congrFun hu (productLeft k k i)
    have hv : (fun i => (gammaVolumeValue V (e.equiv u) i).val) = s := funext fun i => by
      simpa only [productTuple_right] using congrFun hu (productRight k k i)
    simpa only [ht, hv] using e.weight u
  · exact e.leftFinite
  · exact e.rightFinite

end SpecialTransformations.Section7
