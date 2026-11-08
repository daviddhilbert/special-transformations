import Section3.GuardedRationalNormalForm
import Section3.FieldBase
import Section3.GeneratedBaseLifting
import Section3.GammaDefinableClosureField
import Section5.GammaBaseInputs

/-! Finite VF polynomial support for graphs over a genuine Gamma-named
base. A real representative is used only to read the formula. Every
coefficient comes from the original base's VF field. -/

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GuardedRVNormalForm

noncomputable section

namespace SpecialTransformations.Section5

private def termSupport {I R V : Type} : RVExpr I R V → List (VFPolynomial I)
  | .vf p => [p]
  | .mul p q | .addK p q => termSupport p ++ termSupport q
  | .inv p | .negK p => termSupport p
  | _ => []

private def atomSupport {I R V : Type} : RVAtom I R V → List (VFPolynomial I)
  | .equality p q | .order p q => termSupport p ++ termSupport q

private def formulaSupport {I R V : Type} :
    PolarityDNF.Expr (RVAtom I R V) → List (VFPolynomial I)
  | .falsum => []
  | .atom p => atomSupport p
  | .imp p q => formulaSupport p ++ formulaSupport q

attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

private theorem rvExpr_eq_of_support {I R V : Type} (a b : I → VF (M := M))
    (r : R → RV (M := M)) (y : V → RV (M := M)) (t : RVExpr I R V)
    (ht : ∀ p ∈ termSupport t, rv (p.realize a) = rv (p.realize b)) :
    t.eval a r y = t.eval b r y := by
  induction t with
  | zero | one | parameter | ofVariable => rfl
  | vf p => exact ht p List.mem_cons_self
  | mul p q hp hq | addK p q hp hq =>
    simp only [RVExpr.eval, hp (fun u hu => ht u (List.mem_append_left _ hu)),
      hq (fun u hu => ht u (List.mem_append_right _ hu))]
  | inv p hp | negK p hp => simp only [RVExpr.eval, hp ht]

private theorem boolean_iff_of_support {I R V : Type} (a b : I → VF (M := M))
    (r : R → RV (M := M)) (y : V → RV (M := M))
    (t : PolarityDNF.Expr (RVAtom I R V))
    (ht : ∀ p ∈ formulaSupport t, rv (p.realize a) = rv (p.realize b)) :
    t.eval (RVAtom.eval a r y) ↔ t.eval (RVAtom.eval b r y) := by
  induction t with
  | falsum => rfl
  | atom p =>
    cases p with
    | equality p q | order p q =>
      have hp := rvExpr_eq_of_support a b r y p (fun u hu => ht u (List.mem_append_left _ hu))
      have hq := rvExpr_eq_of_support a b r y q (fun u hu => ht u (List.mem_append_right _ hu))
      simp only [PolarityDNF.Expr.eval, RVAtom.eval, hp, hq]
  | imp p q hp hq =>
    exact imp_congr (hp (fun u hu => ht u (List.mem_append_left _ hu)))
      (hq (fun u hu => ht u (List.mem_append_right _ hu)))

private theorem sorted_finite_vf_support {S T : Set M} (F : VFFieldBase S)
    (hTS : ∀ a : VF (M := M), a.val ∈ T → a.val ∈ S)
    {n l : ℕ} (sn : Fin l → SortTag) (π : Fin n → Fin l)
    (hπ : ∀ i, sn (π i) = .vf)
    (hcover : ∀ i, sn i = .vf → ∃ j, π j = i)
    (U : Set (Fin l → M)) (hU : DefinableOver T sn U) :
    ∃ d : ℕ, ∃ P : Fin d → MvPolynomial (Fin n) (VF (M := M)),
      (∀ i e, ((P i).coeff e).val ∈ S) ∧
      ∀ (x y : Fin l → M) (hx : ∀ i, sortEval (sn i) (x i))
        (hy : ∀ i, sortEval (sn i) (y i)),
        (∀ i, sn i = .rv → x i = y i) →
        (∀ j, rv (MvPolynomial.eval
          (fun i => ⟨x (π i), by simpa only [hπ i, sortEval, iVF] using hx (π i)⟩) (P j)) =
          rv (MvPolynomial.eval
            (fun i => ⟨y (π i), by simpa only [hπ i, sortEval, iVF] using hy (π i)⟩) (P j))) →
        (x ∈ U ↔ y ∈ U) := by
  obtain ⟨p, φ, hq, hws, hUφ⟩ := hU.quantifier_free (inferInstance : M ⊨ Axioms.ACVF)
  obtain ⟨e, he⟩ := qf_source_boolean p.sorts sn φ hq hws
  let I := VFSlot p.sorts sn
  let pp (i : Fin p.length) (hi : p.sorts i = .vf) : F.field :=
    let v : VF (M := M) := ⟨p.values i, by simpa only [hi, sortEval, iVF] using p.sorted i⟩
    ⟨v, (F.mem_iff v).mpr (hTS v (p.mem_base i))⟩
  let position (i : Fin l) (hi : sn i = .vf) : Fin n := Classical.choose (hcover i hi)
  have hposition (i : Fin l) (hi : sn i = .vf) : π (position i hi) = i :=
    Classical.choose_spec (hcover i hi)
  let values (w : Fin l → M) (hw : ∀ i, sortEval (sn i) (w i)) (i : Fin n) :
      VF (M := M) := ⟨w (π i), by simpa only [hπ i, sortEval, iVF] using hw (π i)⟩
  let substPoly : I → MvPolynomial (Fin n) F.field := fun i =>
    match h : i.val with
    | .inl j => MvPolynomial.C (pp j (by simpa only [h, Sum.elim_inl] using i.property))
    | .inr j => MvPolynomial.X (position j (by simpa only [h, Sum.elim_inr] using i.property))
  let coefRing : ℤ →+* MvPolynomial (Fin n) F.field :=
    MvPolynomial.C.comp (Int.castRingHom F.field)
  let toPoly (q : VFPolynomial I) : MvPolynomial (Fin n) (VF (M := M)) :=
    (MvPolynomial.eval₂ coefRing substPoly q.polynomial).map F.field.subtype
  have hEval (q : VFPolynomial I) (w : Fin l → M) (hw : ∀ i, sortEval (sn i) (w i)) :
      MvPolynomial.eval (values w hw) (toPoly q) =
        q.realize (SourceAssignment.vfValues p.sorts sn p.values w p.sorted hw) := by
    let K := VF (M := M)
    let out := MvPolynomial.eval₂Hom F.field.subtype (values w hw)
    change MvPolynomial.eval (values w hw) ((MvPolynomial.eval₂ coefRing substPoly q.polynomial).map
      F.field.subtype) = _
    rw [MvPolynomial.eval_map]
    change out (MvPolynomial.eval₂ coefRing substPoly q.polynomial) = _
    rw [MvPolynomial.eval₂_comp_left, ← q.polynomial_realize]
    have hco : out.comp coefRing = Int.castRingHom K := by
      ext a
      simp [out, coefRing]
    rw [hco]
    congr 1
    funext i
    rcases i with ⟨i, hi⟩
    cases i with
    | inl j =>
      apply Subtype.ext
      simp [out, substPoly, pp, SourceAssignment.vfValues]
    | inr j =>
      apply Subtype.ext
      simp [out, substPoly, values, hposition, SourceAssignment.vfValues]
  let L := formulaSupport e
  refine ⟨L.length, fun i => toPoly L[i], ?_, ?_⟩
  · intro i a
    change (((MvPolynomial.eval₂ coefRing substPoly L[i].polynomial).map F.field.subtype).coeff a).val ∈ S
    rw [MvPolynomial.coeff_map]
    exact (F.mem_iff _).mp ((MvPolynomial.eval₂ coefRing substPoly L[i].polynomial).coeff a).property
  · intro x y hx hy hrv hv
    have hform (w : Fin l → M) (hw : ∀ i, sortEval (sn i) (w i)) :
        w ∈ U ↔ φ.Realize p.values w := (Set.ext_iff.mp hUφ w).trans (and_iff_right hw)
    have hvar : SourceAssignment.rvVariables sn x hx = SourceAssignment.rvVariables sn y hy := by
      funext i
      exact Subtype.ext (hrv i.val i.property)
    rw [hform x hx, hform y hy, he M p.values x p.sorted hx, he M p.values y p.sorted hy, hvar]
    apply boolean_iff_of_support
    intro q hq
    obtain ⟨i, hi, hqi⟩ := List.getElem_of_mem hq
    let j : Fin L.length := ⟨i, hi⟩
    have hj : L[j] = q := hqi
    have hh := hv j
    change rv (MvPolynomial.eval (values x hx) (toPoly L[j])) =
      rv (MvPolynomial.eval (values y hy) (toPoly L[j])) at hh
    rw [hEval, hEval, hj] at hh
    exact hh

omit [M ⊨ Axioms.ACVF] in
private theorem pointCode_sorted {n m : ℕ} (p : Point (M := M) n m) (i : Fin (n + m)) :
    sortEval (gammaPointSort n m i) (gammaPointCode p i) := by
  cases i using Fin.addCases with
  | left i =>
    simp only [gammaPointSort, gammaPointCode, Fin.append_left, vfAt]
    exact (p.1 i).property
  | right i =>
    simp only [gammaPointSort, gammaPointCode, Fin.append_right]
    exact (p.2 i).property

omit [M ⊨ Axioms.ACVF] in
private theorem code_injective {n m : ℕ} :
    Function.Injective (gammaPointCode (M := M) (n := n) (m := m)) := by
  intro x y h
  refine Prod.ext (funext fun i => Subtype.ext ?_) (funext fun i => Subtype.ext ?_)
  · simpa only [gammaPointCode, vfAt, Fin.append_left] using congrFun h (Fin.castAdd m i)
  · simpa only [gammaPointCode, Fin.append_right] using congrFun h (Fin.natAdd n i)

theorem gammaPolynomialSupportInput_of_fieldBase
    (B : GammaParameters.Base (M := M)) (F : VFFieldBase B.real) :
    GammaPolynomialSupportInput B := by
  intro n m k r hr
  let sn := Fin.append (gammaPointSort n m) (gammaPointSort 0 k)
  let code (x : Point (M := M) n m) (z : Point (M := M) 0 k) :=
    Fin.append (gammaPointCode x) (gammaPointCode z)
  let U : Set (Fin (n + m + (0 + k)) → M) :=
    {w | ∃ x z, r x z ∧ code x z = w}
  obtain ⟨d, γ, _, h⟩ := hr
  let t := GammaParameters.representatives γ
  have hT : DefinableOver (B.real ∪ Set.range (GammaParameters.rawTuple t)) sn U :=
    h.specialize t (GammaParameters.representatives_values γ)
  have hTS (a : VF (M := M))
      (ha : a.val ∈ B.real ∪ Set.range (GammaParameters.rawTuple t)) : a.val ∈ B.real := by
    rcases ha with ha | ⟨i, hi⟩
    · exact ha
    · exact (TypedModelMap.not_rv_of_vf a.property
        (hi ▸ GammaParameters.raw_rv (t i))).elim
  let π (i : Fin n) : Fin (n + m + (0 + k)) := Fin.castAdd (0 + k) (Fin.castAdd m i)
  have hπ (i : Fin n) : sn (π i) = .vf := by simp only [sn, π, gammaPointSort, Fin.append_left]
  have hcover (i : Fin (n + m + (0 + k))) (hi : sn i = .vf) : ∃ j, π j = i := by
    cases i using Fin.addCases with
    | left i =>
      cases i using Fin.addCases with
      | left i => exact ⟨i, rfl⟩
      | right i => simp [sn, gammaPointSort] at hi
    | right i =>
      cases i using Fin.addCases with
      | left i => exact i.elim0
      | right i =>
        simp only [sn, gammaPointSort, Fin.append_right] at hi
        cases hi
  obtain ⟨q, P, hP, hconst⟩ := sorted_finite_vf_support F hTS sn π hπ hcover U hT
  have hsort (x : Point (M := M) n m) (z : Point (M := M) 0 k) :
      ∀ i, sortEval (sn i) (code x z i) := by
    intro i
    cases i using Fin.addCases with
    | left i => simpa only [code, sn, Fin.append_left] using pointCode_sorted x i
    | right i => simpa only [code, sn, Fin.append_right] using pointCode_sorted z i
  have hcode (x : Point (M := M) n m) (z : Point (M := M) 0 k) :
      code x z ∈ U ↔ r x z := by
    constructor
    · rintro ⟨x', z', h, he⟩
      have hx : x' = x := code_injective (funext fun i => by
        simpa only [code, Fin.append_left] using congrFun he (Fin.castAdd (0 + k) i))
      have hz : z' = z := code_injective (funext fun i => by
        simpa only [code, Fin.append_right] using congrFun he (Fin.natAdd (n + m) i))
      exact hx ▸ hz ▸ h
    · intro h
      exact ⟨x, z, h, rfl⟩
  refine ⟨q, P, hP, ?_⟩
  intro x y hxy he z
  have hrveq (i : Fin (n + m + (0 + k))) (hi : sn i = .rv) :
      code x z i = code y z i := by
    cases i using Fin.addCases with
    | left i =>
      cases i using Fin.addCases with
      | left i => simp [sn, gammaPointSort] at hi
      | right i => simp only [code, gammaPointCode, Fin.append_left, Fin.append_right, hxy]
    | right i => simp only [code, Fin.append_right]
  have hx (i : Fin n) :
      (⟨code x z (π i), by simpa only [hπ i, sortEval, iVF] using hsort x z (π i)⟩ :
        VF (M := M)) = x.1 i := by
    apply Subtype.ext
    simp only [code, π, gammaPointCode, vfAt, Fin.append_left]
  have hy (i : Fin n) :
      (⟨code y z (π i), by simpa only [hπ i, sortEval, iVF] using hsort y z (π i)⟩ :
        VF (M := M)) = y.1 i := by
    apply Subtype.ext
    simp only [code, π, gammaPointCode, vfAt, Fin.append_left]
  exact (hcode x z).symm.trans ((hconst _ _ (hsort x z) (hsort y z) hrveq
    (fun j => by
      have hj := he j
      change rv (MvPolynomial.eval x.1 (P j)) = rv (MvPolynomial.eval y.1 (P j)) at hj
      simpa only [funext hx, funext hy] using hj)).trans (hcode y z))

theorem gammaPolynomialSupportInput_of_generatedBase
    (B : GammaParameters.Base (M := M)) (hB : GammaParameters.VFGammaGeneratedBase B) :
    GammaPolynomialSupportInput B := by
  apply gammaPolynomialSupportInput_of_fieldBase B
  refine ⟨GammaParameters.vfDefinableClosureFieldBase B, fun x => ?_⟩
  have hr := congrArg GammaParameters.Base.real hB.closure_eq_self
  change GammaParameters.DefinableClosureAtBase B .vf x.val ↔ x.val ∈ B.real
  rw [← hr]
  constructor
  · exact fun h => ⟨.vf, h⟩
  · rintro ⟨σ, hσ⟩
    cases σ with
    | vf => exact hσ
    | rv =>
      change GammaParameters.DefinableAtBase B .rv {x.val} at hσ
      exact (TypedModelMap.not_rv_of_vf x.property
        (hσ.proper _ (Set.mem_singleton _))).elim

end SpecialTransformations.Section5
