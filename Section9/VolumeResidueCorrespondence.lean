module

public import Section9.RVJacobian
public import Section4.ResidueComparison
public import Section7.LiftedIsomorphism

@[expose] public section

/-! The pairwise volume correspondence in Definition 9.14 is a
definable RV set. Normalizing one value fibre gives a definable
residue-field correspondence with both projections finite. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section4.ResiduePurity SpecialTransformations.Section7
open SpecialTransformations.DefinableGeometry

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ} {S : Set M}
local notation "RV" => CanonicalRV.RVSort M
local notation "k" => ModelResidue M
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

def volumeCorrespondence {U V : RVObject (M := M) S n} (F : Map U.domain V.domain) :
    DefSet (rawRVSpace (M := M) (n + n)) S where
  carrier := Set.range fun u : U.domain => productTuple (U.value u) (V.value (F u))
  definable := by
    let Q := rawRVSpace (M := M) (n + n)
    have hcode (u : U.domain) : rvValues (productTuple (U.value u) (V.value (F u))) =
        productTuple (rvValues (U.value u)) (rvValues (V.value (F u))) := by
      apply productTuple_ext
      · intro i
        simp only [rvValues, productTuple_left]
      · intro i
        simp only [rvValues, productTuple_right]
    let W := Set.range fun u : U.domain => productTuple (U.value u) (V.value (F u))
    have hW : Q.preimage W = rawVolumeCorrespondence F := by
      ext z
      constructor
      · rintro ⟨hz, u, hu⟩
        exact ⟨u, (rvValues_decode ⟨z, hz⟩).symm.trans ((congrArg rvValues hu).symm.trans (hcode u))⟩
      · rintro ⟨u, h⟩
        have hz : z ∈ Q.domain := ⟨_, (hcode u).trans h.symm⟩
        refine ⟨hz, u, rvValues_injective ?_⟩
        exact (hcode u).trans (h.symm.trans (rvValues_decode ⟨z,hz⟩).symm)
    change S.Definable LRV (Q.preimage W)
    rw [hW]
    exact rawVolumeCorrespondence_definable F

theorem normalizedCorrespondence_definable_of_base
    (hc : CanonicalStructure.IsCanonical (M := M)) (B : LRV.Substructure M)
    (C : DefSet (rawRVSpace (M := M) (n + n)) (B : Set M)) (a b : Fin n → RV)
    (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0)
    (haB : ∀ i, (a i).val ∈ B) (hbB : ∀ i, (b i).val ∈ B) :
    Relative.Def (residueParameterField B) (normalizedCorrespondence C.carrier a b) := by
  let e := productTuple a b
  have he (i) : e i ≠ 0 ∧ (e i).val ∈ B := by
    obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective i
    cases j with
    | inl j =>
      change productTuple a b (productLeft n n j) ≠ 0 ∧ (productTuple a b (productLeft n n j)).val ∈ B
      rw [productTuple_left]
      exact ⟨ha j, haB j⟩
    | inr j =>
      change productTuple a b (productRight n n j) ≠ 0 ∧ (productTuple a b (productRight n n j)).val ∈ B
      rw [productTuple_right]
      exact ⟨hb j, hbB j⟩
  let E := residueParameterField B
  have hD := normalizedResidueSet_definable_base hc B C e (fun i => (he i).2)
  have hnz (i : Fin (n+n)) : Relative.Def E {z : Fin (n+n) → k | z i ≠ 0} :=
    ((Relative.projection (E := E) i).eq_const 0 E.zero_mem).compl
  have h := hD.inter (Set.definable_iInter_of_finite hnz)
  convert h using 1
  ext z
  change (residueScale e z ∈ C.carrier ∧ ∀ i, z i ≠ 0) ↔
    (residueScale e z ∈ C.carrier ∧ residueZeroPattern e z) ∧ z ∈ ⋂ i : Fin (n+n), {z | z i ≠ 0}
  rw [Set.mem_iInter]
  exact ⟨fun h => ⟨⟨h.1, fun i h₀ => ((he i).1 h₀).elim⟩, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩

theorem normalizedVolumeCorrespondence_finite {U V : RVObject (M := M) S n} (F : U ≅ V)
    (a b : Fin n → RV) (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0) :
    let C := normalizedCorrespondence (volumeCorrespondence F.hom.map).carrier a b
    (∀ x : Fin n → k, {y | productTuple x y ∈ C}.Finite) ∧
    (∀ y : Fin n → k, {x | productTuple x y ∈ C}.Finite) := by
  let C := normalizedCorrespondence (volumeCorrespondence F.hom.map).carrier a b
  let φ (s : Fin n → RV) (z : Fin n → k) := rvValues (residueScale s z)
  have hinj (s : Fin n → RV) (hs : ∀ i, s i ≠ 0) : Function.Injective (φ s) := by
    intro x y h
    apply residueScale_injective_on_zeroPattern s
      (fun i hi => (hs i hi).elim) (fun i hi => (hs i hi).elim)
    exact rvValues_injective h
  have hmem (x y : Fin n → k) (h : productTuple x y ∈ C) :
      productTuple (φ a x) (φ b y) ∈ rawVolumeCorrespondence F.hom.map := by
    obtain ⟨⟨u, hu⟩, _⟩ := h
    refine ⟨u, ?_⟩
    apply productTuple_ext
    · intro i
      simpa only [productTuple_left, residueScale, φ, rvValues] using
        (congrArg (fun z : Fin (n+n) → RV => (z (productLeft n n i)).val) hu).symm
    · intro i
      simpa only [productTuple_right, residueScale, φ, rvValues] using
        (congrArg (fun z : Fin (n+n) → RV => (z (productRight n n i)).val) hu).symm
  refine ⟨fun x => Set.Finite.of_finite_image (f := φ b) ?_ (hinj b hb).injOn,
    fun y => Set.Finite.of_finite_image (f := φ a) ?_ (hinj a ha).injOn⟩
  · apply (rawVolumeCorrespondence_right_finite F.hom (φ a x)).subset
    rintro _ ⟨y, hy, rfl⟩
    exact hmem x y hy
  · apply (rawVolumeCorrespondence_left_finite F (φ b y)).subset
    rintro _ ⟨x, hx, rfl⟩
    exact hmem x y hx

end SpecialTransformations.Section9
