import CanonicalRV
import SubstructureValuation

set_option backward.isDefEq.respectTransparency false

/-! Compatibility with old RV elements passes to the entire VF field generated
by a language substructure. The proof uses only fractions and multiplication/
inverse closure of the graph; no residue-field embedding is assumed. -/

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open ResidueTranscendentalTransport

namespace SubstructureRVCompatibility

variable {M N : Type} [LRV.Structure M] [LRV.Structure N]
  [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]
  {Γ Δ : Type} [LinearOrderedCommGroupWithZero Γ] [LinearOrderedCommGroupWithZero Δ]
  (v : Valuation (VFType (M := M)) Γ) (w : Valuation (VFType (M := N)) Δ)
  (hv : ∀ a b : VFType (M := M), VFValued.predV a b ↔ v a ≤ v b)
  (hw : ∀ a b : VFType (M := N), VFValued.predV a b ↔ w a ≤ w b)
  (S : LRV.Substructure M) (f : S ↪[LRV] N)
  (R : _root_.RVCalc.RV v → _root_.RVCalc.RV w → Prop)

/-- Every RV element of the original substructure has related source and target
VF representatives. This is precisely the old-RV clause of PreparedFrame. -/
def OldRVRepresentatives : Prop :=
  ∀ (x : S), iRV (x : M) →
    ∃ (c : VFType (M := M)) (d : VFType (M := N)),
      iRv c.1 = (x : M) ∧ iRv d.1 = f x ∧ R (_root_.RVCalc.rv v c) (_root_.RVCalc.rv w d)

include hv hw

theorem ring_compat (hOld : OldRVRepresentatives v w S f R)
    (a : SubstructureField.vfRing S) :
    R (_root_.RVCalc.rv v (a : VFType (M := M)))
      (_root_.RVCalc.rv w (SubstructureField.ringMap S f a)) := by
  let x : S := ⟨a.1.1, a.2⟩
  obtain ⟨c, d, hc, hd, hcd⟩ :=
    hOld (SubstructureField.rvElement S x) (rv_mem hM a.1.2)
  have hc' : _root_.RVCalc.rv v c = _root_.RVCalc.rv v a.1 :=
    (CanonicalRV.same_fibers v hv c a.1).mpr (Subtype.ext hc)
  have hd' : _root_.RVCalc.rv w d = _root_.RVCalc.rv w (SubstructureField.ringMap S f a) := by
    apply (CanonicalRV.same_fibers w hw d (SubstructureField.ringMap S f a)).mpr
    apply Subtype.ext
    exact hd.trans (SubstructureField.map_rvElement S f x)
  rw [hc', hd'] at hcd
  exact hcd

theorem field_compat
    (hmul : ∀ a b a' b', R a a' → R b b' →
      R (_root_.RVCalc.rvMul v a b) (_root_.RVCalc.rvMul w a' b'))
    (hinv : ∀ a a', R a a' → R (rvInv v a) (rvInv w a'))
    (hOld : OldRVRepresentatives v w S f R)
    (z : SubstructureField.generatedField S) :
    R (_root_.RVCalc.rv v (z : VFType (M := M)))
      (_root_.RVCalc.rv w (SubstructureField.fieldMap S f z)) := by
  obtain ⟨a, b, _, hz⟩ := SubfieldExtension.generator_div_surjective
    (SubstructureField.vfRing S).subtype Subtype.coe_injective z
  have hzval : (z : VFType (M := M)) =
      (a : VFType (M := M)) / (b : VFType (M := M)) :=
    congrArg (fun q : SubstructureField.generatedField S => (q : VFType (M := M))) hz.symm
  have hzmap : SubstructureField.fieldMap S f z =
      SubstructureField.ringMap S f a / SubstructureField.ringMap S f b :=
    (congrArg (SubstructureField.fieldMap S f) hz.symm).trans
      (SubfieldExtension.extend_generator_div (SubstructureField.vfRing S).subtype
        Subtype.coe_injective (SubstructureField.ringMap S f)
        (SubstructureField.ringMap_injective S f) a b)
  rw [hzval, hzmap]
  exact rv_div_relation v w R hmul hinv
    (ring_compat v w hv hw S f R hOld a) (ring_compat v w hv hw S f R hOld b)

end SubstructureRVCompatibility

#print axioms SubstructureRVCompatibility.ring_compat
#print axioms SubstructureRVCompatibility.field_compat
