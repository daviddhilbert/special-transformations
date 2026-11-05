import MaximalRVExtension
import SubstructureField
import JohnsonValuedExtension

set_option backward.isDefEq.respectTransparency false

/-!
Assembly of the checked local algebra and model-theoretic bridges.

This file isolates `Preparation` as an intermediate construction. In the author's
language with named RV inversion, `Theorem23.lean` supplies the proved ACF
extension and residue-field algebraic-closedness inputs to construct it.
The whole valued-field extension is supplied by the repository's Johnson
proof, through `JohnsonValuedExtension`, with no ordinary ACVF QE hypothesis.
-/

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open ResidueTranscendentalTransport

namespace LocalAssembly

variable {M N : Type} [LRV.Structure M] [LRV.Structure N]
variable [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]

/-- Concrete data which the preparation argument must construct. In particular,
the old RV map must extend to a multiplicative, inverse-closed graph compatible
with one actual embedding of the full residue fields. -/
structure PreparedFrame (S : LRV.Substructure M) (f : S ↪[LRV] N)
    {Γ Δ : Type} [LinearOrderedCommGroupWithZero Γ] [LinearOrderedCommGroupWithZero Δ]
    (v : Valuation (VFType (M := M)) Γ) (w : Valuation (VFType (M := N)) Δ) where
  sourceComparison : ∀ a b, VFValued.predV a b ↔ v a ≤ v b
  targetComparison : ∀ a b, VFValued.predV a b ↔ w a ≤ w b
  residueMap : Residue v →+* Residue w
  graph : _root_.RVCalc.RV v → _root_.RVCalc.RV w → Prop
  laws : RVFrame v w residueMap graph
  functional : ∀ x y z, graph x y → graph x z → y = z
  baseCompatibility : ∀ a : SubstructureField.generatedField S,
    graph (_root_.RVCalc.rv v a.1)
      (_root_.RVCalc.rv w (SubstructureField.fieldMap S f a))
  oldRV : ∀ (x : S), iRV (x : M) →
    ∃ (c : VFType (M := M)) (d : VFType (M := N)),
      iRv c.1 = (x : M) ∧ iRv d.1 = f x ∧
        graph (_root_.RVCalc.rv v c) (_root_.RVCalc.rv w d)

section Extension

variable {S : LRV.Substructure M} {f : S ↪[LRV] N}
variable {Γ Δ : Type} [LinearOrderedCommGroupWithZero Γ] [LinearOrderedCommGroupWithZero Δ]
variable {v : Valuation (VFType (M := M)) Γ} {w : Valuation (VFType (M := N)) Δ}

/-- A prepared RV graph is represented in an actual subfield by maximality;
Johnson's valued-field QE then supplies an embedding of whole models. -/
theorem embedding_of_preparedFrame
    (hSat : MarkerBridge.SatAt LRV N (Order.succ (Cardinal.mk M)))
    (hcM : CanonicalStructure.IsCanonical (M := M))
    (hcN : CanonicalStructure.IsCanonical (M := N)) (p : PreparedFrame S f v w) :
    ∃ F : M ↪[LRV] N, ∀ x : S, F (x : M) = f x := by
  letI : IsAlgClosed (VFType (M := M)) := VFAlgClosed.isAlgClosed_vfType
  letI : IsAlgClosed (VFType (M := N)) := VFAlgClosed.isAlgClosed_vfType
  obtain ⟨E, hFE, τ, hτbase, hτgraph, hrep⟩ :=
    MaximalRVExtension.exists_field_representing_graph v w p.residueMap p.graph p.laws
      p.functional (SubstructureField.generatedField S) (SubstructureField.fieldMap S f)
      p.baseCompatibility
  let oldGenerator (x : S) (hx : iVF (x : M)) : SubstructureField.generatedField S :=
    SubfieldExtension.generator (SubstructureField.vfRing S).subtype ⟨⟨(x : M), hx⟩, x.2⟩
  have hContains : VFGeneratedFinish.ContainsVF S E := by
    intro x hx
    exact hFE (oldGenerator x hx).2
  have hVF : VFGeneratedFinish.AgreesVF S E f τ hContains := by
    intro x hx
    have hh := congrArg Subtype.val (hτbase (oldGenerator x hx))
    exact hh.trans (SubstructureField.fieldMap_agrees S f x hx)
  have hRV : VFGeneratedFinish.RepresentsRV S E f τ := by
    intro x hx
    obtain ⟨c, d, hc, hd, hcd⟩ := p.oldRV x hx
    obtain ⟨a, ha, hb⟩ := hrep c d hcd
    have ha' : iRv a.1.1 = iRv c.1 :=
      congrArg Subtype.val ((CanonicalRV.same_fibers v p.sourceComparison a.1 c).mp ha)
    have hb' : iRv (τ a).1 = iRv d.1 :=
      congrArg Subtype.val ((CanonicalRV.same_fibers w p.targetComparison (τ a) d).mp hb)
    exact ⟨a, ha'.trans hc, hb'.trans hd⟩
  have hComparison : ∀ a b : E,
      VFValued.predV (τ a) (τ b) ↔ VFValued.predV a.1 b.1 := by
    intro a b
    have hh := p.laws.order _ _ _ _ (hτgraph a) (hτgraph b)
    simp only [_root_.RVCalc.vrv_rv] at hh
    exact (p.targetComparison (τ a) (τ b)).trans
      (hh.symm.trans (p.sourceComparison a.1 b.1).symm)
  obtain ⟨e⟩ := JohnsonValuedExtension.valuedExtension_of_johnson hSat E τ hComparison
  exact ⟨VFGeneratedFinish.canonicalFinish e hcM hcN,
    VFGeneratedFinish.canonicalFinish_agrees e hcM hcN hContains hVF hRV⟩

end Extension

/-- The intermediate preparation construction, stated in actual algebraic data.
It is proved by `preparation_of_standard_results` in `Theorem23.lean`, using the
named RV inverse and the actual residue-field interpretation. It is not a
quoted textbook result or a definition of saturation. -/
def Preparation : Prop :=
  ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N]
    [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
    CanonicalStructure.IsCanonical (M := M) → CanonicalStructure.IsCanonical (M := N) →
    MarkerBridge.SatAt LRV N (Order.succ (Cardinal.mk M)) →
    ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N)
      {Γ Δ : Type} [LinearOrderedCommGroupWithZero Γ] [LinearOrderedCommGroupWithZero Δ]
      (v : Valuation (VFType (M := M)) Γ) (w : Valuation (VFType (M := N)) Δ),
      (∀ a b, VFValued.predV a b ↔ v a ≤ v b) →
      (∀ a b, VFValued.predV a b ↔ w a ≤ w b) → Nonempty (PreparedFrame S f v w)

theorem canonicalExtension_of_preparation
    (hPrep : Preparation) :
    MarkerBridge.CanonicalExtension := by
  intro M N sM sN hMC hNC hSat S f
  have hm := CanonicalTheory.model_CanonicalACVF_iff.mp hMC
  have hn := CanonicalTheory.model_CanonicalACVF_iff.mp hNC
  letI : M ⊨ Axioms.ACVF := hm.1
  letI : N ⊨ Axioms.ACVF := hn.1
  obtain ⟨Γ, hΓ, v, hv⟩ := VFValued.exists_valuation_predV (M := M)
  obtain ⟨Δ, hΔ, w, hw⟩ := VFValued.exists_valuation_predV (M := N)
  letI := hΓ
  letI := hΔ
  obtain ⟨p⟩ := hPrep M N hm.2 hn.2 hSat S f v w hv hw
  exact embedding_of_preparedFrame hSat hm.2 hn.2 p

/-- The assembly step with preparation exposed as an input. `Theorem23.lean`
discharges that input and proves the required countable-language QE criterion,
so the public theorem has no additional mathematical hypotheses. -/
theorem qe_conditional_on_preparation
    (hMarker : MarkerBridge.MarkerProposition4328)
    (hPrep : Preparation) :
    HasQE Axioms.ACVF :=
  MarkerBridge.qe_of_marker_and_extension hMarker
    (canonicalExtension_of_preparation hPrep)

end LocalAssembly

#print axioms LocalAssembly.embedding_of_preparedFrame
#print axioms LocalAssembly.canonicalExtension_of_preparation
#print axioms LocalAssembly.qe_conditional_on_preparation
