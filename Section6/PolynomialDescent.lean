module

public import Section6.ContractionGraph
public import Section5.PolynomialPreparation

@[expose] public section

/-! A concrete polynomial certificate for Lemma 6.3. The finite tuple map
and its preparation are supplied by the accepted earlier section. The
full QF contraction graph and descent are produced here, with the same
base and every zero/empty-tuple case retained. This is a fixed-ambient
certificate; model-uniform syntactic elimination is a further assembly.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section5

namespace SpecialTransformations.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {n k : ℕ}

def polynomialRVMap (A : DefSet (M := M) S n 0)
    (p : Fin k → MvPolynomial (Fin n) (VF (M := M)))
    (hc : ∀ i d, ((p i).coeff d).val ∈ S) :
    Map A (PresentedSet.univ (pointSpace (M := M) 0 k) S) :=
  Map.comp (flattenKeyMap (PresentedSet.univ (keySpace k 0) S))
    (Map.comp (keyMap (PresentedSet.univ (pointSpace k 0) S)) (mvPolynomialTupleMap A p hc))

theorem polynomialRVMap_values (A : DefSet (M := M) S n 0)
    (p : Fin k → MvPolynomial (Fin n) (VF (M := M)))
    (hc : ∀ i d, ((p i).coeff d).val ∈ S) (a : A) :
    (polynomialRVMap A p hc a).val.2 = fun i => rv (MvPolynomial.eval (R := VF (M := M)) a.val.1 (p i)) := by
  funext i
  change Fin.append (fun j => rv (MvPolynomial.eval (R := VF (M := M)) a.val.1 (p j))) Fin.elim0 i = _
  simpa using Fin.append_left (fun j => rv (MvPolynomial.eval (R := VF (M := M)) a.val.1 (p j))) Fin.elim0 i

theorem polynomial_descent_certificate
    {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (h00 : M ⊨ Axioms.ACVF00) (v : Valuation (VF (M := M)) Γ)
    (hv : ∀ a b, VFValued.predV a b ↔ v a ≤ v b)
    (hObstacles : ∀ N, UniformVerticalObstacles v S N)
    (p : Fin k → MvPolynomial (Fin n) (VF (M := M)))
    (hc : ∀ i d, ((p i).coeff d).val ∈ S) :
    let A := PresentedSet.univ (pointSpace (M := M) n 0) S
    let D := PresentedSet.univ (pointSpace (M := M) 0 k) S
    let f : Map A D := polynomialRVMap A p hc
    ∃ l : ℕ, ∃ B : DefSet (M := M) S n l, ∃ T : SpecialBijection A B,
      IsRVPullback (carrier B) ∧
      ∃ hf : Contractible (Map.comp f T.inverseMap),
      (∃ b : Parameters S, ∃ ψ : LRV.BoundedFormula (Fin b.length) (n + l + k),
        ψ.IsQF ∧ WellSorted b.sorts (fun _ => .rv) ψ ∧
        ∀ z, z ∈ contractionGraphCodes (contractionMap (Map.comp f T.inverseMap) hf) ↔
          (∀ i, iRV (z i)) ∧ ψ.Realize b.values z) ∧
      ∀ X : Set M, NormalizedDclClosed X → S ⊆ X →
        (∀ a : VF (M := M), a.val ∈ X → (rv a).val ∈ X) →
        (∀ t : RV (M := M), t.val ∈ X →
          ∃ a : VF (M := M), a.val ∈ X ∧ rv a = t) →
        ∀ P : (Fin k → RV (M := M)) → Prop,
          ((∃ a : A, PointIn X a.val ∧ P (fun i => rv (MvPolynomial.eval (R := VF (M := M)) a.val.1 (p i)))) ↔
            ∃ u : keyImage B, KeyIn X u.val ∧
              KeyIn X (contractionFun (Map.comp f T.inverseMap) u).val ∧
              P (contractionFun (Map.comp f T.inverseMap) u).val.2) := by
  dsimp only
  let A := PresentedSet.univ (pointSpace (M := M) n 0) S
  let f := polynomialRVMap A p hc
  obtain ⟨l, B, T, _, hB, hf⟩ :=
    map_preparation h00 v hv hObstacles (SpecialBijection.refl A) f
  refine ⟨l, B, T, hB, hf, exists_qf_contraction_graph
    (contractionMap (Map.comp f T.inverseMap) hf), ?_⟩
  intro X hX hSX hrv hRV P
  have hd := prepared_exists_descends hX hSX hrv hRV T hB f hf P
  simpa only [f, polynomialRVMap_values] using hd

end SpecialTransformations.Section6
