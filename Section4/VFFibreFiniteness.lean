module

public import Section4.VFRealFibres
public import Section4.Fibres
public import Section3.AlgebraicFinite

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.DefinableGeometry.Map

variable {L : Language} {M : Type} [L.Structure M]
variable {P Q : Space L M} {S : Set M} {A : DefSet P S} {B : DefSet Q S}

theorem finiteFibres_iff_fibreCarrier_finite (f : Map A B) :
    f.FiniteFibres ↔ ∀ b, (f.fibreCarrier b).Finite := by
  refine ⟨f.fibreCarrier_finite, ?_⟩
  intro hf b
  apply ((hf b).preimage Subtype.val_injective.injOn).subset
  intro a ha
  exact ⟨a, rfl, ha⟩

theorem finite_source_of_finite_image (f : Map A B) (hf : f.FiniteFibres)
    (him : f.image.carrier.Finite) : A.carrier.Finite := by
  letI : Finite f.image := him.to_subtype
  let target (b : f.image) : B :=
    ⟨b.val, by obtain ⟨a, ha⟩ := b.property; exact ha ▸ (f a).property⟩
  have h := Set.finite_iUnion (fun b : f.image => f.fibreCarrier_finite hf (target b))
  apply h.subset
  intro a ha
  let a' : A := ⟨a, ha⟩
  let b' : f.image := ⟨(f a').val, ⟨a', rfl⟩⟩
  exact Set.mem_iUnion.mpr ⟨b', ⟨a', rfl, rfl⟩⟩

theorem FiniteFibres.restrict {f : Map A B} (hf : f.FiniteFibres)
    {A' : DefSet P S} (h : A'.carrier ⊆ A.carrier) : (f.restrict h).FiniteFibres := by
  apply hf.comp
  apply finiteFibres_of_injective
  intro a b he
  exact Subtype.ext (congrArg (fun x : A => x.val) he)

end SpecialTransformations.DefinableGeometry.Map

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] {S : Set M} {n r : ℕ}

theorem finite_vf_projection_of_algebraic {κ : Cardinal} (hs : Saturated M κ)
    (hsmall : Cardinal.mk S < κ) (A : DefSet (rawMixedSpace (M := M) n r) S)
    (ha : ∀ a : A, ∀ i, AlgebraicAt S .vf (a.val.1 i).val) :
    (Prod.fst '' A.carrier).Finite := by
  have hcoord (i : Fin n) : (vfCoordinateSet A i).Finite := by
    apply RawClosure.finite_of_definable_subset_algebraic hs S hsmall _
      (vfCoordinateSet_definable A i)
    rintro x ⟨a, rfl⟩
    exact (ha a i).raw_finite_witness
  apply ((Set.Finite.pi' hcoord).preimage vfValues_injective.injOn).subset
  rintro a ⟨p, hp, rfl⟩ i
  exact ⟨⟨p, hp⟩, rfl⟩

/-- A mixed tuple set is finite if its VF projection and each RV fibre
are finite. This is an ordinary finite-union statement. -/
theorem finite_mixed_of_finite_projection
    (A : Set (rawMixedSpace (M := M) n r).Carrier)
    (hVF : (Prod.fst '' A).Finite)
    (hRV : ∀ a, {t | (a, t) ∈ A}.Finite) : A.Finite := by
  have h := hVF.biUnion (fun a _ => (hRV a).image (fun t => (a, t)))
  apply h.subset
  intro p hp
  exact Set.mem_iUnion.mpr ⟨p.1, Set.mem_iUnion.mpr
    ⟨⟨p, hp, rfl⟩, ⟨p.2, hp, Prod.eta p⟩⟩⟩

end SpecialTransformations.Section4

end
