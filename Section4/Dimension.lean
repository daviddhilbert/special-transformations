module

public import Section4.FiniteMaps
public import Mathlib.Order.Lattice.Nat

@[expose] public section

/-!
# The minimum of definable finite-to-one dimension witnesses

The field and auxiliary presentations remain explicit parameters here.
Concrete VF and mixed RV/Gamma presentations are supplied by Spaces. The
existence of a witness is a separate theorem about those concrete spaces.
-/

open Classical FirstOrder FirstOrder.Language

namespace SpecialTransformations.DefinableGeometry.Dimension

variable {L : Language} {M : Type} [L.Structure M]
variable (VF : ℕ → Space L M) {ι : Type} (Aux : ι → Space L M)
variable {P Q : Space L M} {S : Set M}

def HasDim (A : DefSet P S) (k : ℕ) : Prop :=
  ∃ k' ≤ k, ∃ i : ι, ∃ f : Map A (DefSet.univ ((VF k').prod (Aux i)) S), f.FiniteFibres

noncomputable def dim (A : DefSet P S) : ℕ := sInf {k | HasDim VF Aux A k}

theorem HasDim.upward {A : DefSet P S} {k l : ℕ}
    (hA : HasDim VF Aux A k) (hkl : k ≤ l) : HasDim VF Aux A l := by
  obtain ⟨k', hk', i, f, hf⟩ := hA
  exact ⟨k', hk'.trans hkl, i, f, hf⟩

theorem dim_le_iff {A : DefSet P S} (hbounded : ∃ k, HasDim VF Aux A k) (k : ℕ) :
    dim VF Aux A ≤ k ↔ HasDim VF Aux A k := by
  have hmem : HasDim VF Aux A (dim VF Aux A) := Nat.sInf_mem hbounded
  exact ⟨fun h => hmem.upward VF Aux h, fun h => Nat.sInf_le h⟩

theorem dim_attained {A : DefSet P S} (hbounded : ∃ k, HasDim VF Aux A k) :
    HasDim VF Aux A (dim VF Aux A) := Nat.sInf_mem hbounded

theorem HasDim.of_finiteFibres {A : DefSet P S} {B : DefSet Q S}
    (f : Map A B) (hf : f.FiniteFibres) {k : ℕ} (hB : HasDim VF Aux B k) :
    HasDim VF Aux A k := by
  obtain ⟨k', hk', i, g, hg⟩ := hB
  exact ⟨k', hk', i, g.comp f, hg.comp hf⟩

theorem dim_le_of_finiteFibres {A : DefSet P S} {B : DefSet Q S}
    (f : Map A B) (hf : f.FiniteFibres) (hB : ∃ k, HasDim VF Aux B k) :
    dim VF Aux A ≤ dim VF Aux B := by
  exact Nat.sInf_le ((dim_attained VF Aux hB).of_finiteFibres VF Aux f hf)

theorem dim_mono {A A' : DefSet P S} (h : A'.carrier ⊆ A.carrier)
    (hA : ∃ k, HasDim VF Aux A k) : dim VF Aux A' ≤ dim VF Aux A := by
  let inc : Map A' A := Map.inclusion h
  have hinj : Function.Injective inc := by
    intro a b he
    apply Subtype.ext
    change (inc a).val = (inc b).val
    exact congrArg (fun x : A => x.val) he
  exact dim_le_of_finiteFibres VF Aux inc (Map.finiteFibres_of_injective hinj) hA

theorem hasDim_of_injective {A : DefSet P S} {k' k : ℕ} (h : k' ≤ k) (i : ι)
    (f : Map A (DefSet.univ ((VF k').prod (Aux i)) S)) (hf : Function.Injective f) :
    HasDim VF Aux A k := ⟨k', h, i, f, Map.finiteFibres_of_injective hf⟩

theorem dim_eq_zero_of_finite {A : DefSet P S} (hA : A.carrier.Finite)
    (i : ι) [Nonempty ((VF 0).prod (Aux i)).Carrier]
    [Subsingleton ((VF 0).prod (Aux i)).Carrier] : dim VF Aux A = 0 := by
  have hw : HasDim VF Aux A 0 :=
    ⟨0, le_rfl, i, Map.toSubsingleton A _, Map.finiteFibres_of_finite _ hA⟩
  exact Nat.eq_zero_of_le_zero (Nat.sInf_le hw)

theorem dim_empty (i : ι) : dim VF Aux (DefSet.empty P S) = 0 := by
  have hw : HasDim VF Aux (DefSet.empty P S) 0 :=
    ⟨0, le_rfl, i, Map.empty P _ S, Map.finiteFibres_of_finite _ Set.finite_empty⟩
  exact Nat.eq_zero_of_le_zero (Nat.sInf_le hw)

end SpecialTransformations.DefinableGeometry.Dimension
