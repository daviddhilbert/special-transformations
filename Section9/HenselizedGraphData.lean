module

public import Section9.BoundedCoordinateDerivations
public import Section9.GaussFieldRestriction

@[expose] public section

/-! The data used from the henselization and the finite extension of
the Gauss field. The reference facts are kept separate from the
derivations and from the definable map. -/

set_option backward.isDefEq.respectTransparency false

namespace SpecialTransformations.Section9

open IsLocalRing

variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ] {n m : ℕ}

def graphTuple {d : ℕ} (L : Subfield K) (x : Fin d → K) (h : ∀ i, x i ∈ L) : Fin d → L :=
  fun i => ⟨x i, h i⟩

structure HenselizedGraphData (v : Valuation K Γ) (E : Subfield K) (x : Fin n → K) (y : Fin m → K) where
  field : Subfield K
  coefficients : E ≤ field
  input_mem : ∀ i, x i ∈ field
  output_mem : ∀ i, y i ∈ field
  henselization : Subfield field
  contains_gauss_field :
    (IntermediateField.adjoin (E.comap field.subtype) (Set.range (graphTuple field x input_mem))).toSubfield ≤
      henselization
  algebraic_graph : Algebra.IsAlgebraic
    (IntermediateField.adjoin (E.comap field.subtype) (Set.range (graphTuple field x input_mem))) field
  finite_graph : FiniteDimensional henselization field
  henselian_graph : HenselianLocalRing (v.comap field.subtype).valuationSubring
  residue_charZero : CharZero (ResidueField (v.comap field.subtype).valuationSubring)
  etale_cover :
    let w := v.comap field.subtype
    let F := (IntermediateField.adjoin (E.comap field.subtype)
      (Set.range (graphTuple field x input_mem))).toSubfield
    EtaleCovered (valuationRingInside w F) (valuationRingInside w henselization)
      (valuationRingInside_mono w contains_gauss_field)
  immediate : ∀ z ∈ henselization, ∃ a ∈ IntermediateField.adjoin (E.comap field.subtype)
    (Set.range (graphTuple field x input_mem)), v (a : K) = v (z : K)
  residue_degree :
    let w := v.comap field.subtype
    letI := (residueFieldInclusion w henselization).toAlgebra
    Module.finrank henselization field = Module.finrank
      (ResidueField (w.comap henselization.subtype).valuationSubring) (ResidueField w.valuationSubring)

/-- The algebraic input from the embedded henselization and the
fundamental equality in residue characteristic zero. The hypotheses
describe the Gauss field and a finite tuple algebraic over it. -/
def HenselizedGaussGraphInput (K : Type) [Field K] : Prop :=
  ∀ (G : Type) [LinearOrderedCommGroupWithZero G] (v : Valuation K G)
    [CharZero (ResidueField v.valuationSubring)] (E : Subfield K) [IsAlgClosed E]
    {n m : ℕ} (x : Fin n → K) (y : Fin m → K),
    (∀ i, v (x i) = 1) → IsGaussEvaluation (E := E) v x →
    (∀ i, IsAlgebraic (IntermediateField.adjoin E (Set.range x)) (y i)) →
    Nonempty (HenselizedGraphData v E x y)

theorem HenselizedGraphData.exists_coordinate_derivations [CharZero K]
    (v : Valuation K Γ) (E : Subfield K) [IsAlgClosed E] (x : Fin n → K) (y : Fin m → K)
    (hx : ∀ i, v (x i) ≤ 1) (hGauss : IsGaussEvaluation (E := E) v x)
    (data : HenselizedGraphData v E x y) :
    let L := data.field
    let A := E.comap L.subtype
    let X := graphTuple L x data.input_mem
    let w := v.comap L.subtype
    ∃ D : Fin n → Derivation A L L, (∀ j i, D j (X i) = if j = i then 1 else 0) ∧
      ∀ j z, w (D j z) ≤ w z := by
  let L := data.field
  let A := E.comap L.subtype
  let e := graphCoefficientEquiv E L data.coefficients
  let X := graphTuple L x data.input_mem
  let w := v.comap L.subtype
  let H := data.henselization
  letI : FiniteDimensional H L := data.finite_graph
  letI : HenselianLocalRing w.valuationSubring := data.henselian_graph
  letI : CharZero (ResidueField w.valuationSubring) := data.residue_charZero
  letI : IsAlgClosed A := by
    constructor
    intro p
    have h := (IsAlgClosed.splits (p.map e.toRingHom)).map e.symm.toRingHom
    have he : (p.map e.toRingHom).map e.symm.toRingHom = p := by
      apply Polynomial.ext
      intro i
      rw [Polynomial.coeff_map, Polynomial.coeff_map]
      exact e.symm_apply_apply (p.coeff i)
    exact he ▸ h
  have hGauss' : IsGaussEvaluation (E := A) w X :=
    isGaussEvaluation_comap_subfield v E L data.coefficients X hGauss
  exact exists_bounded_coordinate_derivations w A X hx hGauss' H
    data.algebraic_graph data.contains_gauss_field data.etale_cover data.immediate data.residue_degree

theorem exists_bounded_graph_derivations_of_henselization [CharZero K]
    (v : Valuation K Γ) (E : Subfield K) [IsAlgClosed E] (x : Fin n → K) (y : Fin m → K)
    (hx : ∀ i, v (x i) ≤ 1) (hGauss : IsGaussEvaluation (E := E) v x)
    (data : HenselizedGraphData v E x y) :
    ∃ (L : Type) (fL : Field L), letI := fL
      ∃ aL : Algebra E L, letI := aL
        ∃ (g : L →ₐ[E] K) (X : Fin n → L) (Y : Fin m → L) (D : Fin n → Derivation E L L),
          (∀ i, g (X i) = x i) ∧ (∀ i, g (Y i) = y i) ∧
          (∀ j i, D j (X i) = if j = i then 1 else 0) ∧ ∀ j z, v (g (D j z)) ≤ v (g z) := by
  let L := data.field
  let A := E.comap L.subtype
  let e := graphCoefficientEquiv E L data.coefficients
  let X := graphTuple L x data.input_mem
  let Y := graphTuple L y data.output_mem
  obtain ⟨D, hD, hBound⟩ := HenselizedGraphData.exists_coordinate_derivations v E x y hx hGauss data
  letI : Algebra E A := e.symm.toRingHom.toAlgebra
  letI : Algebra E L := (A.subtype.comp e.symm.toRingHom).toAlgebra
  letI : IsScalarTower E A L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let g : L →ₐ[E] K := { toRingHom := L.subtype, commutes' := fun _ => rfl }
  refine ⟨L, inferInstance, inferInstance, g, X, Y, fun j => (D j).restrictScalars E,
    fun _ => rfl, fun _ => rfl, hD, hBound⟩

end SpecialTransformations.Section9
