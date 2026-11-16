module

public import Section4.Fibres
public import Section4.DefinableCategory
public import Mathlib.Order.Lattice.Nat

@[expose] public section

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] {S : Set M} {m l : ℕ}

instance rawRVSpace_zero_nonempty : Nonempty (rawRVSpace (M := M) 0).Carrier := by
  change Nonempty (Fin 0 → CanonicalRV.RVSort M)
  exact ⟨Fin.elim0⟩

instance rawRVSpace_zero_subsingleton : Subsingleton (rawRVSpace (M := M) 0).Carrier := by
  change Subsingleton (Fin 0 → CanonicalRV.RVSort M)
  exact ⟨fun a b => funext (fun i => i.elim0)⟩

/-- Definition 4.9 uses actual definable finite-to-one maps. RV^0 is the
singleton empty tuple; the existing absorbing RV element is unchanged. -/
def HasRVDimLE (A : DefSet (rawRVSpace (M := M) m) S) (k : ℕ) : Prop :=
  ∃ d ≤ k, ∃ f : Map A (DefSet.univ (rawRVSpace (M := M) d) S), f.FiniteFibres

def rvDim (A : DefSet (rawRVSpace (M := M) m) S) : ℕ := sInf {k | HasRVDimLE A k}

theorem rv_dimension_bound (A : DefSet (rawRVSpace (M := M) m) S) : HasRVDimLE A m :=
  ⟨m, le_rfl, (Map.id A).toUniv,
    Map.finiteFibres_of_injective (Map.toUniv_injective Function.injective_id)⟩

theorem rvDim_le_arity (A : DefSet (rawRVSpace (M := M) m) S) : rvDim A ≤ m :=
  Nat.sInf_le (rv_dimension_bound A)

theorem rvDim_le_iff (A : DefSet (rawRVSpace (M := M) m) S) (k : ℕ) :
    rvDim A ≤ k ↔ HasRVDimLE A k := by
  have hmin : HasRVDimLE A (rvDim A) := by
    change sInf {k | HasRVDimLE A k} ∈ {k | HasRVDimLE A k}
    exact Nat.sInf_mem ⟨m, rv_dimension_bound A⟩
  constructor
  · intro h
    obtain ⟨d, hd, f, hf⟩ := hmin
    exact ⟨d, hd.trans h, f, hf⟩
  · intro h
    exact Nat.sInf_le h

theorem rvDim_attained (A : DefSet (rawRVSpace (M := M) m) S) :
    ∃ f : Map A (DefSet.univ (rawRVSpace (M := M) (rvDim A)) S), f.FiniteFibres := by
  obtain ⟨d, hd, f, hf⟩ := (rvDim_le_iff A (rvDim A)).mp le_rfl
  have hmin : rvDim A ≤ d := Nat.sInf_le (show HasRVDimLE A d from ⟨d, le_rfl, f, hf⟩)
  have he : d = rvDim A := hd.antisymm hmin
  subst d
  exact ⟨f, hf⟩

theorem rvDim_le_of_finite_map {A : DefSet (rawRVSpace (M := M) m) S}
    {B : DefSet (rawRVSpace (M := M) l) S} (f : Map A B) (hf : f.FiniteFibres) :
    rvDim A ≤ rvDim B := by
  obtain ⟨g, hg⟩ := rvDim_attained B
  exact (rvDim_le_iff A _).mpr ⟨rvDim B, le_rfl, g.comp f, hg.comp hf⟩

theorem rvDim_eq_of_bijective {A : DefSet (rawRVSpace (M := M) m) S}
    {B : DefSet (rawRVSpace (M := M) l) S} (f : Map A B) (hf : Function.Bijective f) :
    rvDim A = rvDim B := by
  apply (rvDim_le_of_finite_map f (Map.finiteFibres_of_injective hf.1)).antisymm
  apply rvDim_le_of_finite_map (f.inverse hf)
  apply Map.finiteFibres_of_injective
  intro a b he
  have h := congrArg f he
  simpa only [Map.apply_inverse] using h

theorem rvDim_eq_zero_iff_finite (A : DefSet (rawRVSpace (M := M) m) S) :
    rvDim A = 0 ↔ A.carrier.Finite := by
  constructor
  · intro hz
    obtain ⟨d, hd, f, hf⟩ := (rvDim_le_iff A 0).mp hz.le
    have hd0 : d = 0 := Nat.eq_zero_of_le_zero hd
    subst d
    let b : DefSet.univ (rawRVSpace (M := M) 0) S := ⟨Fin.elim0, Set.mem_univ _⟩
    apply (f.fibreCarrier_finite hf b).subset
    intro a ha
    exact ⟨⟨a, ha⟩, rfl, Subsingleton.elim _ _⟩
  · intro hfin
    let f := Map.toSubsingleton A (rawRVSpace (M := M) 0)
    exact Nat.eq_zero_of_le_zero ((rvDim_le_iff A 0).mpr
      ⟨0, le_rfl, f, Map.finiteFibres_of_finite f hfin⟩)

end SpecialTransformations.Section4

end
