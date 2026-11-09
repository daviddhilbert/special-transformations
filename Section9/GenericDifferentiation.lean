import Section9.ImplicitDifferentiation
import Section9.SimpleRootEquations
import Section9.DerivativeCoordinates
import Section8.GenericOutputBall
import Section4.PolynomialZero

/-! Differentiation on the generic VF locus. The local equation uses only
coefficients in the original parameter field, and its simple-root
condition is proved by separability. -/

open FirstOrder FirstOrder.Language MvPolynomial Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8

set_option backward.isDefEq.respectTransparency false

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n m : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VFType (M := M)) G]

local notation "VF" => VFType (M := M)
local notation "Γ" => Values.Gamma (M := M)
local notation "v" => Values.vfValueHom (M := M)

private theorem near_of_mem_nhds
    (hv : ∀ x y : VF, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {a : Fin n → VF} {U : Set (Fin n → VF)} (hU : U ∈ 𝓝 a) :
    ∃ δ : Γ, ∀ h, δ.val < vfTupleValue h → a + h ∈ U := by
  obtain ⟨r, hr, hsub⟩ := exists_uniformBall_subset_of_mem_nhds hv a hU
  let δ := Values.gammaOf (CanonicalRV.encodedRv r)
    (fun he => hr ((CanonicalRV.encodedRv_zero_iff r).mp he))
  refine ⟨δ, fun h hh => hsub ?_⟩
  have he : δ.val = v r := rfl
  have hb : a + h ∈ vfBall a δ := by
    intro i
    change δ.val < v ((a i + h i) - a i)
    rw [add_sub_cancel_left]
    exact hh.trans_le (vfTupleValue_le_component h i)
  have hh' := (mem_vfBall_iff_gammaUniformBall a (a + h) δ).mp hb
  rwa [gammaUniformBall_eq_uniformBall _ δ r hr he.symm] at hh'

private theorem coordinate_equation_near
    (hc : CanonicalStructure.IsCanonical (M := M))
    (hv : ∀ x y : VF, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {S : Set M} (f : (Fin n → VF) → Fin m → VF) (hf : S.Definable LRV (vfGraph f))
    (a : Fin n → VF) (ha : AlgebraicIndependent (vfParameterField S) a)
    (j : Fin m) (P : MvPolynomial (Fin n ⊕ Unit) (vfParameterField S))
    (hP : aeval (Sum.elim a (fun _ => f a j)) P = 0) :
    ∃ δ : Γ, ∀ h, δ.val < vfTupleValue h →
      aeval (Sum.elim (a + h) (fun _ => f (a + h) j)) P = 0 := by
  classical
  let e : Fin n ⊕ Unit ≃ Fin (n + 1) := (Equiv.sumCongr (Equiv.refl _) (Equiv.ofUnique _ _)).trans
    finSumFinEquiv
  let Q := rename e P
  let E := vfParameterField S
  let code (k : Fin (n + 1)) : Fin n ⊕ Fin m := Sum.map id (fun _ => j) (e.symm k)
  let H := vfGraph f ∩ (fun z => z ∘ code) ⁻¹' PolynomialZero.zeroSet E Q
  let X := (fun z : Fin n ⊕ Fin m → M => z ∘ Sum.inl) '' H
  have hX : S.Definable LRV X :=
    (hf.inter ((PolynomialZero.zeroSet_parameterField_definable S Q).raw_definable.preimage_comp
      code)).image_comp Sum.inl
  have hsem (x : Fin n → VF) :
      Sum.elim (vfValues x) (vfValues (f x)) ∘ code ∈ PolynomialZero.zeroSet E Q ↔
        aeval (Sum.elim x (fun _ => f x j)) P = 0 := by
    let z := Sum.elim x (fun _ : Unit => f x j) ∘ e.symm
    have hz : Sum.elim (vfValues x) (vfValues (f x)) ∘ code = vfValues z := by
      funext k
      change Sum.elim (vfValues x) (vfValues (f x)) (Sum.map id (fun _ => j) (e.symm k)) =
        (Sum.elim x (fun _ : Unit => f x j) (e.symm k)).val
      cases e.symm k <;> rfl
    rw [hz]
    have hq : aeval z Q = aeval (Sum.elim x (fun _ => f x j)) P := by
      have he : z ∘ e = Sum.elim x (fun _ : Unit => f x j) := by
        funext k
        simp [z]
      rw [show Q = rename e P from rfl, aeval_rename, he]
    constructor
    · rintro ⟨hs, hz⟩
      let z' : Fin (n + 1) → VF := fun i => ⟨(z i).val, hs i⟩
      have he : z' = z := funext (fun i => Subtype.ext rfl)
      change aeval z' Q = 0 at hz
      rwa [he, hq] at hz
    · intro hp
      refine ⟨fun i => (z i).property, ?_⟩
      change aeval z Q = 0
      exact hq.trans hp
  have hXs := raw_definableOver_sorted hc S (fun _ => .vf) X hX (by
    rintro _ ⟨_, ⟨⟨x, rfl⟩, _⟩, rfl⟩ i
    exact (x i).property)
  have haX : vfValues a ∈ X :=
    ⟨_, ⟨⟨a, rfl⟩, (hsem a).mpr hP⟩, rfl⟩
  obtain ⟨δ, hδ⟩ := near_of_mem_nhds hv (independent_definable_mem_nhds hv S X hXs a ha haX)
  refine ⟨δ, fun h hh => ?_⟩
  obtain ⟨_, ⟨⟨x, rfl⟩, hx⟩, hxa⟩ := hδ h hh
  have he : x = a + h := vfValues_injective hxa
  exact he ▸ (hsem x).mp hx

private theorem coordinate_increment_small
    (hv : ∀ x y : VF, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {f : (Fin n → VF) → Fin m → VF} {a : Fin n → VF} (hf : ContinuousAt f a)
    (j : Fin m) (ε : Γ) :
    ∃ δ : Γ, ∀ h, δ.val < vfTupleValue h → ε.val < v (f (a + h) j - f a j) := by
  obtain ⟨r, hr, he⟩ := gamma_has_vf_representative ε
  have hu := hf.preimage_mem_nhds (uniformBall_mem_nhds hv (f a) r hr)
  obtain ⟨δ, hδ⟩ := near_of_mem_nhds hv hu
  refine ⟨δ, fun h hh => ?_⟩
  rw [← he, vfValue_lt_iff_presentation]
  exact (mem_rawOpenBall_iff Values.presentationValuation Values.presentation_compatible
    (f a j) r (f (a + h) j) hr).mp (hδ h hh j)

/-- Any simple equations over the parameter field give the derivative
at an independent input. -/
theorem hasVFDerivativeAt_of_independent_of_simple_equations
    [CharZero VF] (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    {S : Set M} (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (f : (Fin n → VF) → Fin m → VF) (hf : S.Definable LRV (vfGraph f))
    (a : Fin n → VF) (ha : AlgebraicIndependent (vfParameterField S) a)
    (P : Fin m → MvPolynomial (Fin n ⊕ Unit) (vfParameterField S))
    (hP : ∀ j, aeval (Sum.elim a (fun _ => f a j)) (P j) = 0)
    (hP' : ∀ j, aeval (Sum.elim a (fun _ => f a j)) (pderiv (Sum.inr ()) (P j)) ≠ 0) :
    HasVFDerivativeAt f a
      (LinearMap.pi fun j => implicitScalarSlope (P j) (Sum.elim a (fun _ => f a j))) := by
  classical
  have hcont := continuousAt_of_independent hc hκ hs hsmall hv f hf a ha
  let L (j : Fin m) := implicitScalarSlope (P j) (Sum.elim a (fun _ => f a j))
  have hL (j : Fin m) := implicitScalarSlope_isDerivative (fun x => f x j) a
    (P j) (hP j) (hP' j) (coordinate_equation_near hc hv f hf a ha j (P j) (hP j))
    (coordinate_increment_small hv hcont j)
  exact hasVFDerivativeAt_of_components (LinearMap.pi L) hL

/-- On the generic VF locus, algebraic output coordinates give a full
linear derivative. -/
theorem differentiableAt_of_independent_of_algebraic_coordinates
    [CharZero VF] (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    {S : Set M} (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (f : (Fin n → VF) → Fin m → VF) (hf : S.Definable LRV (vfGraph f))
    (a : Fin n → VF) (ha : AlgebraicIndependent (vfParameterField S) a)
    (halg : ∀ j, IsAlgebraic (tupleField (vfParameterField S) a) (f a j)) :
    VFDifferentiableAt f a := by
  choose P hP hP' using fun j => exists_simpleRoot_equation_of_tupleField _ a (f a j) (halg j)
  exact ⟨_, hasVFDerivativeAt_of_independent_of_simple_equations hc hκ hs hsmall hv f hf a ha P hP hP'⟩

private theorem vfGraph_coordinate_algebraic
    (hc : CanonicalStructure.IsCanonical (M := M))
    {S : Set M} (f : (Fin n → VF) → Fin m → VF) (hf : S.Definable LRV (vfGraph f))
    (a : Fin n → VF) (j : Fin m) :
    IsAlgebraic (tupleField (vfParameterField S) a) (f a j) := by
  let T := S ∪ Set.range (vfValues a)
  let fill (z : Fin m → M) := Sum.elim (vfValues a) z
  have hfill : T.DefinableMap LRV fill := by
    rintro (i | i)
    · exact LRV.definableFun_const _ (Or.inr (Set.mem_range_self i))
    · exact Set.DefinableFun.proj LRV
  let Y := fill ⁻¹' vfGraph f
  have hY : T.Definable LRV Y := (hf.mono Set.subset_union_left).preimage_map hfill
  have hmem (z : Fin m → M) : z ∈ Y ↔ z = vfValues (f a) := by
    constructor
    · rintro ⟨x, hx⟩
      have ha : x = a := vfValues_injective (funext fun i => congrFun hx (.inl i))
      exact funext fun i => (congrFun hx (.inr i)).symm.trans
        (congrArg (fun b => (f b i).val) ha)
    · rintro rfl
      exact ⟨a, rfl⟩
  have hdef : T.Definable₁ LRV {(f a j).val} := by
    change T.Definable LRV {z : Fin 1 → M | z 0 ∈ {(f a j).val}}
    convert hY.image_comp (fun _ : Fin 1 => j) using 1
    ext z
    constructor
    · intro hz
      exact ⟨vfValues (f a), (hmem _).mpr rfl, funext fun i => by fin_cases i; exact hz.symm⟩
    · rintro ⟨y, hy, rfl⟩
      rw [(hmem _).mp hy]
      rfl
  have ha := (definableClosureAt_iff_raw hc T .vf (f a j).val).mpr ⟨hdef, (f a j).property⟩
  rw [← vfParameterField_union_tuple]
  exact algebraicAt_vf_parameterField T _ ha.algebraic

/-- Generic full differentiation of a definable VF function. In particular,
all partial derivatives of Lemma 9.8 exist at these points. -/
theorem differentiableAt_of_independent [CharZero VF]
    (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    {S : Set M} (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (f : (Fin n → VF) → Fin m → VF) (hf : S.Definable LRV (vfGraph f))
    (a : Fin n → VF) (ha : AlgebraicIndependent (vfParameterField S) a) :
    VFDifferentiableAt f a :=
  differentiableAt_of_independent_of_algebraic_coordinates hc hκ hs hsmall hv f hf a ha
    (vfGraph_coordinate_algebraic hc f hf a)

end SpecialTransformations.Section9
