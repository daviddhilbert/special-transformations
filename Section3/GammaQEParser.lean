module

/-
Extracted from https://github.com/daviddhilbert/diamond-integral/blob/ba6249a11b39e8e71fd0130ab0087e7185b95433/section%205/GammaQEParser.lean
Original declaration namespaces and notices are retained.
-/
public import Section3.GammaQERVVariableMaps

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Actual Gamma predicates have a finite flat RV normal form with fixed
VF and RV coefficients. All nonzero representatives are retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace DiamondIntegral.Section5.GammaQE
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3 SpecialTransformations.Section4
open CanonicalRV GuardedRVNormalForm
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem gamma_flat_normal_form (S : Set M) (P : (Fin 2 → Values.Gamma (M := M)) → Prop)
    (hP : GammaSyntax.Definable S P) :
    ∃ (I R : Type) (a : I → VFType (M := M)) (r : R → RVSort M)
      (D : LiteralDNF I R (Fin 2)),
      ∀ (x : Fin 2 → RVSort M) (hx : ∀ i,x i ≠ 0),
        P (fun i => rvGamma (x i) (hx i)) ↔ PolarityDNF.holds (RVLiteral.holds a r x) D := by
  let B : Set (Fin 2 → M) := {x | GammaSyntax.Proper x ∧ P (GammaSyntax.decode x)}
  have hd : DefinableOver S (fun _ : Fin 2 => .rv) B :=
    (definableOver_iff_normalized_raw S _ B).mpr
      ⟨hP,fun x hx i => (hx.1 i).1⟩
  obtain ⟨p,φ,hq,hws,hφ⟩ := hd.quantifier_free hM
  obtain ⟨E,hE⟩ := qf_source_boolean p.sorts (fun _ : Fin 2 => .rv) φ hq hws
  let u : Fin 2 → M := fun _ => (1 : RVSort M).val
  have hu : ∀ i,sortEval SortTag.rv (u i) := fun _ => (1 : RVSort M).property
  let a := SourceAssignment.vfValues p.sorts (fun _ : Fin 2 => .rv) p.values u p.sorted hu
  let r := SourceAssignment.rvParameters p.sorts p.values p.sorted
  let E' := mapRVBooleanVariables (fun i : RVVariableSlot (fun _ : Fin 2 => .rv) => i.val) E
  refine ⟨_,_,a,r,booleanNormalForm E',?_⟩
  intro x hx
  let w : Fin 2 → M := fun i => (x i).val
  have hw : ∀ i,sortEval SortTag.rv (w i) := fun i => (x i).property
  have hp : GammaSyntax.Proper w := fun i => ⟨(x i).property,fun he =>
    hx i (Subtype.ext (he.trans RVOperations.zero_val.symm))⟩
  have hdec : GammaSyntax.decode w = fun i => rvGamma (x i) (hx i) := by
    funext i
    exact rvGamma_codeValue (x i) (hx i)
  have hraw := Set.ext_iff.mp hφ w
  change (GammaSyntax.Proper w ∧ P (GammaSyntax.decode w)) ↔ _ at hraw
  have hformula : P (fun i => rvGamma (x i) (hx i)) ↔ φ.Realize p.values w := by
    simpa only [Set.mem_ofPred_eq,hp,hdec,hw,forall_const,true_and] using hraw
  have ha := sourceVFValues_allRV p.sorts p.values p.sorted w u hw hu
  have hv : SourceAssignment.rvVariables (fun _ : Fin 2 => .rv) w hw =
      x ∘ (fun i : RVVariableSlot (fun _ : Fin 2 => .rv) => i.val) := by
    funext i
    apply Subtype.ext
    rfl
  have hh := hE M p.values w p.sorted hw
  rw [ha,hv] at hh
  exact hformula.trans (hh.trans
    ((mapRVBooleanVariables_eval _ E a r x).symm.trans
      (booleanNormalForm_correct a r x E').symm))

end DiamondIntegral.Section5.GammaQE
