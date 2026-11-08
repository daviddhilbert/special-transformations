import Section3.OpenBallCenters
import Section4.PolydiscLocal

/-! The same finite radius in every VF coordinate, using the released VF/RV
language and the open-ball presentation already used in Section 3. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3

namespace SpecialTransformations.Section8

variable {M : Type} [LRV.Structure M]

abbrev rawOpenBall (a r : M) : Set M := OpenBallCodes.rawBall ![a, r]

/-- The paper's open polydisc of constant radius, presented by a VF tuple
of centres and a nonzero VF representative of the radius. -/
def uniformBall {n : ℕ} (a : Fin n → M) (r : M) : Set (Fin n → M) :=
  {x | ∀ i, x i ∈ rawOpenBall (a i) r}

theorem rawOpenBall_definable {S : Set M} {a r : M} (ha : a ∈ S) (hr : r ∈ S) :
    S.Definable₁ LRV (rawOpenBall a r) := by
  let F (z : Fin 1 → M) : Fin 3 → M := ![a, r, z 0]
  have hF : S.DefinableMap LRV F := by
    intro i
    fin_cases i
    · exact LRV.definableFun_const _ ha
    · exact LRV.definableFun_const _ hr
    · exact Set.DefinableFun.proj LRV
  change S.Definable LRV {z : Fin 1 → M | z 0 ∈ rawOpenBall a r}
  convert (OpenBallCodes.membership_raw_definable S).preimage_map hF using 1
  ext z
  have hinit : Fin.init (F z) = ![a, r] := by
    funext i
    fin_cases i <;> rfl
  change z 0 ∈ rawOpenBall a r ↔ F z (Fin.last 2) ∈ OpenBallCodes.rawBall (Fin.init (F z))
  rw [hinit]
  rfl

variable [hM : M ⊨ Axioms.ACVF]

theorem uniformBall_normalize {n : ℕ} (a : Fin n → M) (r : M) :
    @uniformBall M (CanonicalStructure.normalize (M := M)) n a r = uniformBall a r := by
  ext x
  change (∀ i, x i ∈ @OpenBallCodes.rawBall M (CanonicalStructure.normalize (M := M))
    ![a i, r]) ↔ ∀ i, x i ∈ rawOpenBall (a i) r
  simp only [OpenBallCodes.rawBall_normalize]

variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)
include hv

/-- Ordinary paper radii use strict comparison in the opposite order to the
paper's additive valuation, via the chosen compatible multiplicative valuation. -/
theorem mem_rawOpenBall_iff (a r x : VFType (M := M)) (hr : r ≠ 0) :
    x.val ∈ rawOpenBall a.val r.val ↔ v (x - a) < v r := by
  have hq : OpenBallCodes.Proper (![a.val, r.val] : Fin 2 → M) := by
    refine ⟨?_, fun h => hr (Subtype.ext h)⟩
    intro i
    fin_cases i
    · exact a.property
    · exact r.property
  exact Set.ext_iff.mp (OpenBallCodes.ball_eq_open v hv _ hq) x

theorem rawOpenBall_self {a r : M} (ha : iVF a) (hr : iVF r) (hr0 : r ≠ iVFZero) :
    a ∈ rawOpenBall a r := by
  let a' : VFType (M := M) := ⟨a, ha⟩
  let r' : VFType (M := M) := ⟨r, hr⟩
  have hr' : r' ≠ 0 := fun h => hr0 (congrArg Subtype.val h)
  apply (mem_rawOpenBall_iff v hv a' r' a' hr').mpr
  rw [sub_self, map_zero]
  exact pos_iff_ne_zero.mpr (v.ne_zero_iff.mpr hr')

theorem rawOpenBall_recentre {a r b x : M} (hb : b ∈ rawOpenBall a r)
    (hx : x ∈ rawOpenBall a r) : x ∈ rawOpenBall b r := by
  let a' : VFType (M := M) := ⟨a, hb.1.1 0⟩
  let r' : VFType (M := M) := ⟨r, hb.1.1 1⟩
  let b' : VFType (M := M) := ⟨b, hb.2.1⟩
  let x' : VFType (M := M) := ⟨x, hx.2.1⟩
  have hr' : r' ≠ 0 := fun h => hb.1.2 (congrArg Subtype.val h)
  have hba := (mem_rawOpenBall_iff v hv a' r' b' hr').mp hb
  have hxa := (mem_rawOpenBall_iff v hv a' r' x' hr').mp hx
  apply (mem_rawOpenBall_iff v hv b' r' x' hr').mpr
  simpa only [sub_sub_sub_cancel_right] using v.map_sub_lt hxa hba

theorem mem_uniformBall_iff {n : ℕ} (a x : Fin n → VFType (M := M))
    (r : VFType (M := M)) (hr : r ≠ 0) :
    Section4.vfValues x ∈ uniformBall (Section4.vfValues a) r.val ↔
      x ∈ (Section4.ValuedPolydisc.mk a (fun _ => r) (fun _ => hr) :
        Section4.ValuedPolydisc v n).carrier :=
  forall_congr' (fun i => mem_rawOpenBall_iff v hv (a i) r (x i) hr)

end SpecialTransformations.Section8
