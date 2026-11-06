import Section4.RVDimension
import Section4.VFRealFibres
import Section4.VFCategories

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] {S : Set M} {n r : ℕ}

/-- An actual RV fibre with the VF tuple named in its parameter base. -/
def fixedVFFibre (A : DefSet (rawMixedSpace (M := M) n r) S)
    (a : Fin n → VFType (M := M)) :
    DefSet (rawRVSpace (M := M) r) (S ∪ Set.range (vfValues a)) where
  carrier := {t | (a, t) ∈ A.carrier}
  definable := by
    let B := S ∪ Set.range (vfValues a)
    let P := rawMixedSpace (M := M) n r
    let F (z : Fin r → M) : Fin n ⊕ Fin r → M := Sum.elim (vfValues a) z
    have hF : B.DefinableMap LRV F := by
      intro i
      cases i with
      | inl i => exact LRV.definableFun_const (Fin r) (Or.inr (Set.mem_range_self i))
      | inr i => exact Set.DefinableFun.proj LRV
    have hA : B.Definable LRV (P.preimage A.carrier) := A.definable.mono P Set.subset_union_left
    have h := hA.preimage_map hF
    have hdom (z : Fin r → M) (hz : z ∈ (rawRVSpace (M := M) r).domain) : F z ∈ P.domain :=
      ⟨⟨a, rfl⟩, hz⟩
    have hdecode (z : Fin r → M) (hz : F z ∈ P.domain) :
        P.decode ⟨F z, hz⟩ = (a, (rawRVSpace r).decode ⟨z, hz.2⟩) := by
      apply Prod.ext
      · exact decode_vfValues a
      · rfl
    have he : (rawRVSpace (M := M) r).preimage {t | (a, t) ∈ A.carrier} =
        F ⁻¹' P.preimage A.carrier := by
      ext z
      constructor
      · rintro ⟨hz, hmem⟩
        refine ⟨hdom z hz, ?_⟩
        rw [hdecode]
        exact hmem
      · rintro ⟨hz, hmem⟩
        refine ⟨hz.2, ?_⟩
        rw [hdecode] at hmem
        exact hmem
    change B.Definable LRV ((rawRVSpace (M := M) r).preimage {t | (a, t) ∈ A.carrier})
    rw [he]
    exact h

/-- Definition 4.12. Indexing by points repeats equal VF fibres but gives
the same maximum over the VF projection, with zero on the empty set. -/
def rvFibreDim (A : DefSet (rawMixedSpace (M := M) n r) S) : ℕ :=
  ⨆ a : A, rvDim (fixedVFFibre A a.val.1)

theorem rvFibreDim_bounded (A : DefSet (rawMixedSpace (M := M) n r) S) :
    BddAbove (Set.range (fun a : A => rvDim (fixedVFFibre A a.val.1))) := by
  refine ⟨r, ?_⟩
  rintro _ ⟨a, rfl⟩
  exact rvDim_le_arity _

theorem rvFibreDim_le_arity (A : DefSet (rawMixedSpace (M := M) n r) S) :
    rvFibreDim A ≤ r := ciSup_le' (fun _ => rvDim_le_arity _)

theorem rvFibreDim_attained (A : DefSet (rawMixedSpace (M := M) n r) S)
    (hne : A.carrier.Nonempty) : ∃ a : A, rvDim (fixedVFFibre A a.val.1) = rvFibreDim A := by
  obtain ⟨a, ha⟩ := hne
  have hne' : (Set.range (fun a : A => rvDim (fixedVFFibre A a.val.1))).Nonempty :=
    ⟨_, ⟨a, ha⟩, rfl⟩
  exact Nat.sSup_mem hne' (rvFibreDim_bounded A)

theorem rvFibreDim_eq_zero_iff_finite_fibres
    (A : DefSet (rawMixedSpace (M := M) n r) S) :
    rvFibreDim A = 0 ↔ ∀ a : Fin n → VFType (M := M),
      {t : Fin r → CanonicalRV.RVSort M | (a, t) ∈ A.carrier}.Finite := by
  constructor
  · intro hz a
    by_cases hne : (fixedVFFibre A a).carrier.Nonempty
    · obtain ⟨t, ht⟩ := hne
      let p : A := ⟨(a, t), ht⟩
      have hd := le_ciSup (rvFibreDim_bounded A) p
      change rvDim (fixedVFFibre A a) ≤ rvFibreDim A at hd
      rw [hz] at hd
      exact (rvDim_eq_zero_iff_finite _).mp (Nat.eq_zero_of_le_zero hd)
    · have he := Set.not_nonempty_iff_eq_empty.mp hne
      change (fixedVFFibre A a).carrier.Finite
      rw [he]
      exact Set.finite_empty
  · intro hfin
    apply Nat.eq_zero_of_le_zero
    apply ciSup_le'
    intro a
    exact ((rvDim_eq_zero_iff_finite _).mpr (hfin a.val.1)).le

theorem rvFibreDim_eq_zero_iff_finiteRVFibres (U : VFAllObject (M := M) S) :
    rvFibreDim U.set = 0 ↔ finiteRVFibres U :=
  rvFibreDim_eq_zero_iff_finite_fibres U.set

end SpecialTransformations.Section4

end
