/-
Extracted from https://github.com/daviddhilbert/diamond-integral/blob/ba6249a11b39e8e71fd0130ab0087e7185b95433/section%205/GammaQEFiniteLaws.lean
Original declaration namespaces and notices are retained.
-/
import Section3.GammaQEGraphCritical
import HilbertMathlib.Foundation.Euler.GammaQEPositiveLaw

/-! The exact unary Gamma rational-affine input is proved from original
RV quantifier elimination. No saturation or additional parameters occur. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
namespace DiamondIntegral.Section5.GammaQE
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3 SpecialTransformations.Section4
open CanonicalRV GuardedRVNormalForm
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {I R : Type}

theorem finite_laws_of_flat_graph (a : I → VFType (M := M)) (r : R → RVSort M)
    (D : LiteralDNF I R (Fin 2)) (A : Set (Values.Gamma (M := M)))
    (f : Values.Gamma (M := M) → Values.Gamma (M := M))
    (hgraph : ∀ (x : Fin 2 → RVSort M) (hx : ∀ i,x i ≠ 0),
      (rvGamma (x 0) (hx 0) ∈ A ∧ f (rvGamma (x 0) (hx 0)) = rvGamma (x 1) (hx 1)) ↔
        PolarityDNF.holds (RVLiteral.holds a r x) D) :
    ∃ (k : ℕ) (p : Fin k → ℤ) (q : Fin k → ℕ) (c : Fin k → Values.Gamma (M := M)),
      (∀ i,q i ≠ 0) ∧ ∀ z ∈ A,∃ i,f z ^ q i = c i*z^p i := by
  let s := dnfMonomials D
  let T : Fin s.length → Monomial I R (Fin 2) := s.get
  let J := {j : Fin s.length × Fin s.length //
    flatCoefficient (T j.1) a r ≠ 0 ∧ flatCoefficient (T j.2) a r ≠ 0 ∧
      (T j.2).powers 1 < (T j.1).powers 1}
  let pp : J → ℤ := fun j => (T j.val.2).powers 0 - (T j.val.1).powers 0
  let qq : J → ℕ := fun j => ((T j.val.1).powers 1 - (T j.val.2).powers 1).toNat
  let cc : J → Values.Gamma (M := M) := fun j =>
    rvGamma (flatCoefficient (T j.val.2) a r) j.property.2.1 /
      rvGamma (flatCoefficient (T j.val.1) a r) j.property.1
  let e := Fintype.equivFin J
  refine ⟨Fintype.card J,pp ∘ e.symm,qq ∘ e.symm,cc ∘ e.symm,?_,?_⟩
  · intro i
    exact positive_power_denominator _ _ (e.symm i).property.2.2
  · intro z hz
    obtain ⟨u,hu,huz⟩ := rvGamma_surjective z
    obtain ⟨v,hv,hvf⟩ := rvGamma_surjective (f z)
    let x : Fin 2 → RVSort M := ![u,v]
    have hx : ∀ i,x i ≠ 0 := by intro i; fin_cases i <;> assumption
    have hxz : rvGamma (x 0) (hx 0) = z := huz
    have hxf : rvGamma (x 1) (hx 1) = f z := hvf
    obtain ⟨P,hP,Q,hQ,hP0,hQ0,he,hne⟩ := graph_has_critical_pair a r D A f hgraph x hx
      ⟨hxz.symm ▸ hz,by rw [hxz,hxf]⟩
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp hP
    obtain ⟨j,hj⟩ := List.mem_iff_get.mp hQ
    have hPi : T i = P := hi
    have hQj : T j = Q := hj
    have hPc : flatCoefficient (T i) a r ≠ 0 :=
      (flat_rawEval_ne_zero _ a r x hx).mp (hPi.symm ▸ hP0)
    have hQc : flatCoefficient (T j) a r ≠ 0 :=
      (flat_rawEval_ne_zero _ a r x hx).mp (hQj.symm ▸ hQ0)
    have heq : rvGamma (flatCoefficient (T i) a r) hPc * z^(T i).powers 0 * (f z)^(T i).powers 1 =
        rvGamma (flatCoefficient (T j) a r) hQc * z^(T j).powers 0 * (f z)^(T j).powers 1 := by
      have hval : Values.vrv ((T i).rawEval a r x) = Values.vrv ((T j).rawEval a r x) := by
        simpa only [hPi,hQj] using he
      have hγ := (rvGamma_eq_iff ((T i).rawEval a r x) ((T j).rawEval a r x)
        ((flat_rawEval_ne_zero _ a r x hx).mpr hPc)
        ((flat_rawEval_ne_zero _ a r x hx).mpr hQc)).mpr hval
      rw [flat_value _ a r hPc x hx,flat_value _ a r hQc x hx] at hγ
      simpa only [flatValue,hxz,hxf] using hγ
    have hneq : (T i).powers 1 ≠ (T j).powers 1 := by simpa only [hPi,hQj] using hne
    have finish (w : J) (hw : f z ^ qq w = cc w*z^pp w) :
        ∃ i,f z ^ (qq ∘ e.symm) i = (cc ∘ e.symm) i*z^(pp ∘ e.symm) i := by
      refine ⟨e w,?_⟩
      simpa only [Function.comp_apply,Equiv.symm_apply_apply] using hw
    rcases lt_or_gt_of_ne hneq with hlt | hgt
    · let w : J := ⟨(j,i),hQc,hPc,hlt⟩
      exact finish w (positive_power_law _ _ _ _ _ _ _ _ hlt heq.symm)
    · let w : J := ⟨(i,j),hPc,hQc,hgt⟩
      exact finish w (positive_power_law _ _ _ _ _ _ _ _ hgt heq)

end DiamondIntegral.Section5.GammaQE
