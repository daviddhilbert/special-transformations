import Section7.GuardedLaurentSide
import Section7.LaurentClearing
import Section7.GuardedFibreDomains
import Section7.WeightedPolynomialTests
import Section7.AlgebraicRowWitness
import Section7.FiniteRVPolynomialPattern
import Section7.GuardedParameterScope
import Section7.ResidueCharacteristic

section GuardedPolynomialSideProof

/-!
# Clear an original-field weighted Laurent sum, including zero terms

The two sides of a guarded equality use one common variable monomial.
Individual coefficients may be zero. The zero terms are removed from the
gamma presentation while retaining their exact evaluation in the sum.
-/

open MvPolynomial

namespace SpecialTransformations.Section7

variable {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]

theorem gammaPolynomial_of_shiftedLaurent_allow_zero (v : Valuation K Γ) (E : Subfield K)
    {ι : Type*} [Fintype ι] {n : ℕ} (a : ι → E) (m : ι → Fin n → ℤ)
    (d : Fin n →₀ ℕ) (k : ι → Fin n →₀ ℕ)
    (hk : ∀ j i, (k j i : ℤ) = m j i + (d i : ℤ))
    {γ : Fin n → Γ} {α : Γ} (hγ : ∀ i, γ i ≠ 0) (hα : α ≠ 0)
    (hw : ∀ j, a j ≠ 0 → v (a j : K) * (∏ i, γ i ^ m j i) = α) :
    ∃ P : MvPolynomial (Fin n) E,
      IsGammaPolynomial v γ (α * ∏ i, γ i ^ d i) (P.map E.subtype) ∧
      ∀ x : Fin n → K, (∀ i, x i ≠ 0) →
        (P.map E.subtype).eval x =
          (∑ j, (a j : K) * ∏ i, x i ^ m j i) * (∏ i, x i ^ d i) := by
  classical
  let P := ∑ j, monomial (k j) (a j)
  have hmap : P.map E.subtype = ∑ j, monomial (k j) (a j : K) := by
    simp [P, map_sum, map_monomial]
  refine ⟨P, ?_, ?_⟩
  · rw [hmap]
    have hshift : (∏ i, γ i ^ d i) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (hγ i))
    apply IsGammaPolynomial.sum v hγ (mul_ne_zero hα hshift)
    intro j
    by_cases hj : a j = 0
    · simpa [hj] using isGammaPolynomial_zero v hγ (mul_ne_zero hα hshift)
    · apply isGammaPolynomial_monomial v hγ (mul_ne_zero hα hshift)
      rw [prod_shiftedLaurent_pow γ hγ (hk j), ← mul_assoc, hw j hj]
  · intro x hx
    rw [hmap, map_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [eval_monomial]
    have hp : (k j).prod (fun i e => x i ^ e) = ∏ i, x i ^ k j i := by
      rw [Finsupp.prod_fintype]
      intro i
      simp
    rw [hp, prod_shiftedLaurent_pow x hx (hk j), mul_assoc]

end SpecialTransformations.Section7

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GuardedRVNormalForm
open CanonicalRV ValuedModelMap

set_option backward.isDefEq.respectTransparency false

namespace SpecialTransformations.Section7

variable {M I R V Γ : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
    [LinearOrderedCommGroupWithZero Γ] {n : ℕ}
variable (E : Subfield (VFType (M := M))) (a : I → E) (r : R → E)
    (e : V ≃ Fin n)

noncomputable def guardedSideExponent (T : Monomial I R V) (P : KPolynomial I R V)
    (j : Fin P.size) (i : Fin n) : ℤ :=
  (T.powers + (P.terms j).powers) (e.symm i)

noncomputable def guardedSideCoefficient (T : Monomial I R V) (P : KPolynomial I R V)
    (j : Fin P.size) : E :=
  originalMonomialCoefficient E T a r * originalMonomialCoefficient E (P.terms j) a r

theorem guardedSideLaurentTerm_eq (T : Monomial I R V) (P : KPolynomial I R V)
    (x : Fin n → VFType (M := M)) (hx : ∀ i, x i ≠ 0) (j : Fin P.size) :
    (guardedSideCoefficient E a r T P j : VFType (M := M)) *
        (∏ i, x i ^ guardedSideExponent e T P j i) =
      originalLaurentValue E a r (x ∘ e) T *
        originalLaurentValue E a r (x ∘ e) (P.terms j) := by
  classical
  rw [originalLaurentValue_mul E a r (x ∘ e) T (P.terms j) (fun i => hx (e i))]
  letI : Fintype V := Fintype.ofEquiv (Fin n) e.symm
  rw [Finsupp.prod_fintype _ _ (fun _ => zpow_zero _)]
  congr 1
  exact Fintype.prod_equiv e.symm _ _ (fun i => by simp [guardedSideExponent])

/-- On a fixed value fibre, after one variable monomial shift, a guarded
side is the leading term of a genuine gamma polynomial over the original
coefficient field. The anchor determines weights and checks the guards. -/
theorem exists_guardedSide_polynomial
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ u w : VFType (M := M), VFValued.predV u w ↔ v u ≤ v w)
    (T : Monomial I R V) (P : KPolynomial I R V)
    {γ : Fin n → Γ} (hγ : ∀ i, γ i ≠ 0)
    (c : Fin n → VFType (M := M)) (hc : ∀ i, v (c i) = γ i)
    (hP : P.Domain (fun i => (a i : VFType (M := M)))
      (fun i => CanonicalRV.encodedRv (r i : VFType (M := M)))
      (fun i => CanonicalRV.encodedRv (c (e i))))
    (d : Fin n →₀ ℕ) (k : Fin P.size → Fin n →₀ ℕ)
    (hk : ∀ j i, (k j i : ℤ) = guardedSideExponent e T P j i + (d i : ℤ)) :
    ∃ (α : Γ) (G : MvPolynomial (Fin n) E),
      IsGammaPolynomial v γ α (G.map E.subtype) ∧
      ∀ (x : Fin n → VFType (M := M)), (∀ i, v (x i) = γ i) →
        (T.rawEval (fun i => (a i : VFType (M := M)))
          (fun i => CanonicalRV.encodedRv (r i : VFType (M := M)))
          (fun i => CanonicalRV.encodedRv (x (e i))) *
        P.rawEval (fun i => (a i : VFType (M := M)))
          (fun i => CanonicalRV.encodedRv (r i : VFType (M := M)))
          (fun i => CanonicalRV.encodedRv (x (e i)))) *
        CanonicalRV.encodedRv (∏ i, x i ^ d i) =
          CanonicalRV.equiv v hv (weightedLeadingTerm v α ((G.map E.subtype).eval x)) := by
  classical
  let W := fun x : Fin n → VFType (M := M) => originalLaurentValue E a r (x ∘ e) T
  let S := fun x : Fin n → VFType (M := M) =>
    ∑ j, originalLaurentValue E a r (x ∘ e) (P.terms j)
  let b := fun x : Fin n → VFType (M := M) => ∏ i, x i ^ d i
  let δ := ∏ i, γ i ^ d i
  have hδ : δ ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (hγ i))
  have hnonzero (x : Fin n → VFType (M := M)) (hx : ∀ i, v (x i) = γ i) (i : Fin n) :
      x i ≠ 0 := (Valuation.ne_zero_iff v).mp (hx i ▸ hγ i)
  have hW (x : Fin n → VFType (M := M)) (hx : ∀ i, v (x i) = γ i) :
      v (W x) = v (W c) :=
    originalLaurentValue_value_eq E a r (x ∘ e) v T (c ∘ e)
      (fun i => (hx (e i)).trans (hc (e i)).symm)
  have hb (x : Fin n → VFType (M := M)) (hx : ∀ i, v (x i) = γ i) : v (b x) = δ := by
    simp only [b, δ, map_prod, map_pow, hx]
  by_cases hzero : v (W c) = 0
  · refine ⟨1, 0, ?_, ?_⟩
    · simpa only [map_zero] using isGammaPolynomial_zero v hγ one_ne_zero
    · intro x hx
      have hWx : W x = 0 := (Valuation.zero_iff v).mp ((hW x hx).trans hzero)
      have hencoded := originalLaurentValue_encoded E a r (x ∘ e) T
      simp only [Function.comp_apply] at hencoded
      rw [hencoded]
      change (CanonicalRV.encodedRv (W x) * _) * _ = _
      have hnone : CanonicalRV.equiv v hv (none : _root_.RVCalc.RV v) =
          CanonicalRV.encodedRv (0 : VFType (M := M)) := by
        rw [← _root_.RVCalc.rv_zero, CanonicalRV.equiv_rv]
      rw [hWx, map_zero, map_zero, weightedLeadingTerm, Valuation.map_zero,
        if_neg zero_ne_one, hnone]
      simp only [RVOperations.rv_zero, zero_mul]
  · let A := guardedSideCoefficient E a r T P
    let m := guardedSideExponent e T P
    have hw (j : Fin P.size) (hj : A j ≠ 0) : v (A j : VFType (M := M)) *
        (∏ i, γ i ^ m j i) = v (W c) := by
      have he := guardedSideLaurentTerm_eq E a r e T P c (hnonzero c hc) j
      have hvEq := congrArg v he
      change v ((A j : VFType (M := M)) * ∏ i, c i ^ m j i) =
        v (W c * originalLaurentValue E a r (c ∘ e) (P.terms j)) at hvEq
      simp only [map_mul, map_prod, map_zpow₀, hc] at hvEq
      rcases originalLaurentValue_value_of_inK E a r (c ∘ e) v hv (P.terms j) (hP j).2
        with hunit | hterm0
      · simpa only [hunit, mul_one] using hvEq
      · rw [hterm0, Valuation.map_zero, mul_zero] at hvEq
        exact (mul_ne_zero ((Valuation.ne_zero_iff v).mpr (fun h => hj (Subtype.ext h)))
          (Finset.prod_ne_zero_iff.mpr (fun i _ => zpow_ne_zero _ (hγ i))) hvEq).elim
    obtain ⟨G, hG, heval⟩ :=
      gammaPolynomial_of_shiftedLaurent_allow_zero v E A m d k hk hγ hzero hw
    refine ⟨v (W c) * δ, G, hG, ?_⟩
    intro x hx
    have hPx : P.Domain (fun i => (a i : VFType (M := M)))
        (fun i => CanonicalRV.encodedRv (r i : VFType (M := M)))
        (fun i => CanonicalRV.encodedRv (x (e i))) :=
      (residuePolynomial_domain_iff_of_values _ _ P
        (fun i => encodedRV_absolute_eq_of_equal_values v hv (c (e i)) (x (e i))
          ((hc (e i)).trans (hx (e i)).symm))).mp hP
    have hWx : v (W x) ≠ 0 := fun hz => hzero ((hW x hx).symm.trans hz)
    have he := (guarded_outer_times_residue_sum E a r (x ∘ e) v hv T P hPx hWx).2
    have hsum : (∑ j, (A j : VFType (M := M)) * ∏ i, x i ^ m j i) = W x * S x := by
      change (∑ j, (A j : VFType (M := M)) * ∏ i, x i ^ m j i) =
        W x * (∑ j, originalLaurentValue E a r (x ∘ e) (P.terms j))
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl
        (fun j _ => guardedSideLaurentTerm_eq E a r e T P x (hnonzero x hx) j)
    have hEval : (G.map E.subtype).eval x = b x * (W x * S x) := by
      rw [heval x (hnonzero x hx), hsum, mul_comm]
    rw [hEval, mul_comm (v (W c)) δ,
      encoded_weightedLeadingTerm_mul_of_exact v hv hδ (v (W c)) (hb x hx),
      ← hW x hx, ← he, mul_comm] <;> simp only [b, Function.comp_apply]

end SpecialTransformations.Section7

end GuardedPolynomialSideProof

section GuardedLiteralTestsProof

/-!
# Polynomial tests for guarded clauses on a fixed value fibre

A single common Laurent shift cancels in each RV equality. Order and
domain conditions are fixed by the coordinate values. Equality and
disequality are decided by a finite family of residue-root tests over the
original coefficient field, even when the two sides have different values.
-/

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GuardedRVNormalForm
open CanonicalRV ValuedModelMap MvPolynomial

set_option backward.isDefEq.respectTransparency false

namespace SpecialTransformations.Section7

variable {M I R V Γ : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
    [LinearOrderedCommGroupWithZero Γ] {n : ℕ}
variable (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ u w : VFType (M := M), VFValued.predV u w ↔ v u ≤ v w)
    (E : Subfield (VFType (M := M))) (a : I → E) (r : R → E) (e : V ≃ Fin n)

local notation "av" => (fun i => (a i : VFType (M := M)))
local notation "rr" => (fun i => CanonicalRV.encodedRv (r i : VFType (M := M)))
local notation "ev" => (fun (s : Fin n → _root_.RVCalc.RV v) i => CanonicalRV.equiv v hv (s (e i)))

theorem encodedGuardedVariables_eq {s : Fin n → _root_.RVCalc.RV v}
    {x : Fin n → VFType (M := M)} (hx : x ∈ RVFibre v s) :
    ev s = fun i => CanonicalRV.encodedRv (x (e i)) := by
  funext i
  change CanonicalRV.equiv v hv (s (e i)) = CanonicalRV.encodedRv (x (e i))
  rw [← hx (e i), CanonicalRV.equiv_rv]

theorem encodedGuardedVariables_absolute_eq {s t : Fin n → _root_.RVCalc.RV v}
    (hst : ∀ i, _root_.RVCalc.vrv v (s i) = _root_.RVCalc.vrv v (t i)) (i : V) :
    RVOperations.absoluteHom (ev s i) = RVOperations.absoluteHom (ev t i) := by
  obtain ⟨x, hx⟩ := rvFibre_nonempty v s
  obtain ⟨y, hy⟩ := rvFibre_nonempty v t
  rw [encodedGuardedVariables_eq v hv e hx, encodedGuardedVariables_eq v hv e hy]
  exact encodedRV_absolute_eq_of_equal_values v hv _ _
    ((rvFibre_value v hx (e i)).trans ((hst (e i)).trans (rvFibre_value v hy (e i)).symm))

theorem exists_guardedLiteral_tests (t : Fin n → _root_.RVCalc.RV v)
    (ht : ∀ i, t i ≠ none) (L : RVLiteral I R V) (hL : RVLiteral.Domain av rr (ev t) L) :
    ∃ J : Finset (Γ × MvPolynomial (Fin n) E),
      (∀ j ∈ J, IsGammaPolynomial v (fun i => _root_.RVCalc.vrv v (t i)) j.1
        (j.2.map E.subtype)) ∧
      ∀ s : Fin n → _root_.RVCalc.RV v,
        (∀ i, _root_.RVCalc.vrv v (s i) = _root_.RVCalc.vrv v (t i)) →
        (∀ j ∈ J, IsResidueRoot v s j.1 (j.2.map E.subtype) ↔
          IsResidueRoot v t j.1 (j.2.map E.subtype)) →
        (RVLiteral.holds av rr (ev s) L ↔ RVLiteral.holds av rr (ev t) L) := by
  classical
  cases L with
  | order L pos =>
    refine ⟨∅, by simp, ?_⟩
    intro s hs _
    exact orderLiteral_holds_iff_of_values _ _ L pos
      (encodedGuardedVariables_absolute_eq v hv e hs)
  | equality L pos =>
    obtain ⟨c, hc⟩ := rvFibre_nonempty v t
    let γ := fun i => _root_.RVCalc.vrv v (t i)
    have hγ (i : Fin n) : γ i ≠ 0 := by
      change _root_.RVCalc.vrv v (t i) ≠ 0
      rw [← rvFibre_value v hc i]
      exact (Valuation.ne_zero_iff v).mpr (fun h =>
        ht i ((hc i).symm.trans (h ▸ _root_.RVCalc.rv_zero)))
    have hd := hL
    rw [encodedGuardedVariables_eq v hv e hc] at hd
    change L.left.PoleFree av ∧ L.leftK.Domain av rr _ ∧
      L.right.PoleFree av ∧ L.rightK.Domain av rr _ at hd
    let m : Fin L.leftK.size ⊕ Fin L.rightK.size → Fin n → ℤ :=
      Sum.elim (guardedSideExponent e L.left L.leftK) (guardedSideExponent e L.right L.rightK)
    obtain ⟨d, k, hk⟩ := exists_clearLaurentExponents m
    obtain ⟨α, P, hP, hleft⟩ := exists_guardedSide_polynomial E a r e v hv L.left L.leftK
      hγ c (rvFibre_value v hc) hd.2.1 d (fun j => k (.inl j)) (fun j i => hk (.inl j) i)
    obtain ⟨β, Q, hQ, hright⟩ := exists_guardedSide_polynomial E a r e v hv L.right L.rightK
      hγ c (rvFibre_value v hc) hd.2.2.2 d (fun j => k (.inr j)) (fun j i => hk (.inr j) i)
    let test (s : Fin n → _root_.RVCalc.RV v) :=
      if α = β then IsResidueRoot v s α ((P - Q).map E.subtype)
      else IsResidueRoot v s α (P.map E.subtype) ∧ IsResidueRoot v s β (Q.map E.subtype)
    have htest (s : Fin n → _root_.RVCalc.RV v)
        (hs : ∀ i, _root_.RVCalc.vrv v (s i) = γ i) :
        (L.left.rawEval av rr (ev s) * L.leftK.rawEval av rr (ev s) =
          L.right.rawEval av rr (ev s) * L.rightK.rawEval av rr (ev s)) ↔ test s := by
      obtain ⟨x, hx⟩ := rvFibre_nonempty v s
      have hxv (i : Fin n) : v (x i) = γ i := (rvFibre_value v hx i).trans (hs i)
      have hs0 (i : Fin n) : s i ≠ none := by
        intro h
        have he := hs i
        rw [h, _root_.RVCalc.vrv_none] at he
        exact hγ i he.symm
      let b := ∏ i, x i ^ d i
      have hb : b ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ =>
        pow_ne_zero _ ((Valuation.ne_zero_iff v).mp (hxv i ▸ hγ i))
      have hbRV : CanonicalRV.encodedRv b ≠ 0 := by
        intro h
        have he := (CanonicalRV.same_fibers v hv b 0).mpr (h.trans RVOperations.rv_zero.symm)
        rw [_root_.RVCalc.rv_zero] at he
        exact hb ((_root_.RVCalc.rv_eq_none_iff (v := v)).mp he)
      have hPs : IsGammaPolynomial v (fun i => _root_.RVCalc.vrv v (s i)) α (P.map E.subtype) := by
        rw [funext hs]
        exact hP
      have hQs : IsGammaPolynomial v (fun i => _root_.RVCalc.vrv v (s i)) β (Q.map E.subtype) := by
        rw [funext hs]
        exact hQ
      have hmul (u w : RVSort M) :
          u = w ↔ u * CanonicalRV.encodedRv b = w * CanonicalRV.encodedRv b :=
        ⟨fun h => congrArg (fun z => z * CanonicalRV.encodedRv b) h, mul_right_cancel₀ hbRV⟩
      rw [encodedGuardedVariables_eq v hv e hx]
      refine (hmul _ _).trans ?_
      change _ * CanonicalRV.encodedRv b = _ * CanonicalRV.encodedRv b ↔ _
      dsimp only [b]
      rw [hleft x hxv, hright x hxv]
      exact (CanonicalRV.equiv v hv).injective.eq_iff.trans
        (weightedPolynomialEquality_iff v E hs0 P Q hPs hQs hx)
    have hcompare (s : Fin n → _root_.RVCalc.RV v)
        (hs : ∀ i, _root_.RVCalc.vrv v (s i) = γ i) (hpat : test s ↔ test t) :
        RVLiteral.holds av rr (ev s) (.equality L pos) ↔
          RVLiteral.holds av rr (ev t) (.equality L pos) := by
      unfold RVLiteral.holds
      refine and_congr (literal_domain_iff_of_values _ _ _
        (encodedGuardedVariables_absolute_eq v hv e hs)) ?_
      simp only [RVLiteral.comparison]
      have h := (htest s hs).trans (hpat.trans (htest t (fun _ => rfl)).symm)
      cases pos
      · exact not_congr h
      · exact h
    by_cases hab : α = β
    · refine ⟨{(α, P - Q)}, ?_, ?_⟩
      · intro j hj
        rw [Finset.mem_singleton.mp hj]
        change IsGammaPolynomial v γ α ((P - Q).map E.subtype)
        rw [map_sub, sub_eq_add_neg]
        exact hP.add v ((hab.symm ▸ hQ).neg v)
      · intro s hs hpat
        apply hcompare s hs
        simpa only [test, if_pos hab] using hpat (α, P - Q) (Finset.mem_singleton_self _)
    · refine ⟨{(α, P), (β, Q)}, ?_, ?_⟩
      · intro j hj
        rcases Finset.mem_insert.mp hj with h | h
        · subst j; exact hP
        · rw [Finset.mem_singleton.mp h]; exact hQ
      · intro s hs hpat
        apply hcompare s hs
        simpa only [test, if_neg hab] using and_congr
          (hpat (α, P) (Finset.mem_insert_self _ _))
          (hpat (β, Q) (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))

theorem exists_guardedClause_tests (t : Fin n → _root_.RVCalc.RV v)
    (ht : ∀ i, t i ≠ none) (C : List (RVLiteral I R V))
    (hC : ∀ L ∈ C, RVLiteral.holds av rr (ev t) L) :
    ∃ J : Finset (Γ × MvPolynomial (Fin n) E),
      (∀ j ∈ J, IsGammaPolynomial v (fun i => _root_.RVCalc.vrv v (t i)) j.1
        (j.2.map E.subtype)) ∧
      ∀ s : Fin n → _root_.RVCalc.RV v,
        (∀ i, _root_.RVCalc.vrv v (s i) = _root_.RVCalc.vrv v (t i)) →
        (∀ j ∈ J, IsResidueRoot v s j.1 (j.2.map E.subtype) ↔
          IsResidueRoot v t j.1 (j.2.map E.subtype)) →
        ∀ L ∈ C, RVLiteral.holds av rr (ev s) L := by
  classical
  induction C with
  | nil =>
    exact ⟨∅, by simp, by simp⟩
  | cons L C ih =>
    have hL := hC L List.mem_cons_self
    obtain ⟨J, hJ, hJpat⟩ := exists_guardedLiteral_tests v hv E a r e t ht L hL.1
    obtain ⟨K, hK, hKpat⟩ := ih (fun L' h => hC L' (List.mem_cons_of_mem _ h))
    refine ⟨J ∪ K, ?_, ?_⟩
    · intro j hj
      exact (Finset.mem_union.mp hj).elim (hJ j) (hK j)
    · intro s hs hpat L' hL'
      rcases List.mem_cons.mp hL' with h | h
      · subst L'
        exact (hJpat s hs (fun j hj => hpat j (Finset.mem_union_left _ hj))).mpr hL
      · exact hKpat s hs (fun j hj => hpat j (Finset.mem_union_right _ hj)) _ h

end SpecialTransformations.Section7

end GuardedLiteralTestsProof

section AlgebraicResidueRootProof

/-!
# Lemma 7.4: an original-base polynomial at an algebraic RV coordinate

The finite row comes from actual model-theoretic algebraicity. A true
clause of the checked guarded normal form gives finitely many polynomial
tests on the last-coordinate value fibre. Their finite truth pattern
supplies a simple residue root over the original generated VF field.
-/

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section3.GuardedRVNormalForm
open MvPolynomial IsLocalRing

set_option backward.isDefEq.respectTransparency false

namespace SpecialTransformations.Section7

variable {M Γ : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
    [LinearOrderedCommGroupWithZero Γ]

theorem lemma_7_4 {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : Base (M := M)) (hsmall : Cardinal.mk B.real < κ) (hB : VFGammaGeneratedBase B)
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ u w : VFType (M := M), VFValued.predV u w ↔ v u ≤ v w)
    {n : ℕ} (t : Fin (n + 1) → _root_.RVCalc.RV v) (ht : ∀ i, t i ≠ none)
    (halg : AlgebraicAtBase
      ⟨B.real ∪ Set.range (fun i : Fin n => (CanonicalRV.equiv v hv (t i.castSucc)).val),
        B.gamma⟩ .rv (CanonicalRV.equiv v hv (t (Fin.last n))).val) :
    let E := vfDefinableClosureFieldBase B
    ∃ (α : Γ) (F : MvPolynomial (Fin (n + 1)) E),
      IsGammaPolynomial v (fun i => _root_.RVCalc.vrv v (t i)) α (F.map E.subtype) ∧
      IsResidueRoot v t α (F.map E.subtype) ∧
      ¬ IsResidueRoot v t (α / _root_.RVCalc.vrv v (t (Fin.last n)))
        ((pderiv (Fin.last n) F).map E.subtype) := by
  classical
  let E := vfDefinableClosureFieldBase B
  let sn := fun _ : Fin (n + 1) => SortTag.rv
  let e := allRVVariableEquiv (n + 1)
  let raw : _root_.RVCalc.RV v → M := fun u => (CanonicalRV.equiv v hv u).val
  let tup (s : Fin (n + 1) → _root_.RVCalc.RV v) := fun i => raw (s i)
  have hsort (s : Fin (n + 1) → _root_.RVCalc.RV v) (i : Fin (n + 1)) :
      iRV (tup s i) := (CanonicalRV.equiv v hv (s i)).property
  obtain ⟨A, hA, htA, hfin⟩ := originalBase_finite_RV_row hκ hs h00 B hsmall
    (fun i => CanonicalRV.equiv v hv (t i)) halg
  obtain ⟨p, φ, hφ, hA⟩ := hA
  obtain ⟨D, hD⟩ := model_uniform_raw_normal_form p.sorts sn φ hφ
  obtain ⟨a, r, ha, hr⟩ := originalBase_guarded_parameters hκ hs h00 B hsmall hB p (n + 1)
  let av : VFSlot p.sorts sn → VFType (M := M) := fun i => a i
  let rr : RVParameterSlot p.sorts → CanonicalRV.RVSort M := fun i =>
    CanonicalRV.encodedRv (r i : VFType (M := M))
  let ev (s : Fin (n + 1) → _root_.RVCalc.RV v) := fun i =>
    CanonicalRV.equiv v hv (s (e i))
  have hNF (s : Fin (n + 1) → _root_.RVCalc.RV v) :
      (φ.Realize p.values (tup s) ↔ PolarityDNF.holds (RVLiteral.comparison av rr (ev s)) D) ∧
      LiteralDNF.Certified av rr (ev s) D := by
    have h := hD M p.values (tup s) p.sorted (hsort s)
    have hev : SourceAssignment.rvVariables sn (tup s) (hsort s) = ev s := by
      funext i
      apply Subtype.ext
      rfl
    rw [ha (tup s) (hsort s), hr, hev] at h
    exact h
  have htφ : φ.Realize p.values (tup t) := by
    change tup t ∈ A at htA
    rw [hA] at htA
    exact htA.2
  obtain ⟨C, hCD, hC⟩ := (hNF t).1.mp htφ
  obtain ⟨J, hJ, hJpat⟩ := exists_guardedClause_tests v hv E a r e t ht C
    (fun L hL => ⟨(hNF t).2 C hCD hC L hL, hC L hL⟩)
  let i := Fin.last n
  let α (j : J) := j.val.1
  let F (j : J) := j.val.2
  let S : Set (_root_.RVCalc.RV v) := {u | _root_.RVCalc.vrv v u = _root_.RVCalc.vrv v (t i) ∧
    ∀ j : J, IsResidueRoot v (Function.update t i u) (α j) ((F j).map E.subtype) ↔
      IsResidueRoot v t (α j) ((F j).map E.subtype)}
  have hS : S.Finite := by
    apply Set.Finite.of_injOn (f := raw) ?_ ?_ hfin
    · intro u hu
      let s := Function.update t i u
      have hsval (j : Fin (n + 1)) : _root_.RVCalc.vrv v (s j) = _root_.RVCalc.vrv v (t j) := by
        by_cases hj : j = i
        · subst j
          simpa [s] using hu.1
        · simp [s, hj]
      have hCs := hJpat s hsval (fun j hj => hu.2 ⟨j, hj⟩)
      have hsA : tup s ∈ A := by
        rw [hA]
        exact ⟨hsort s, (hNF s).1.mpr ⟨C, hCD, fun L hL => (hCs L hL).2⟩⟩
      have hsnoc : Fin.snoc (fun j : Fin n => raw (t j.castSucc)) (raw u) = tup s := by
        funext j
        refine Fin.lastCases ?_ (fun k => ?_) j
        · simp [i, s, tup]
        · simp [i, s, tup, Fin.castSucc_ne_last]
      change Fin.snoc (fun j : Fin n => raw (t j.castSucc)) (raw u) ∈ A
      rwa [hsnoc]
    · intro u _ w _ huw
      exact (CanonicalRV.equiv v hv).injective (Subtype.ext huw)
  letI : CharZero (ResidueField v.valuationSubring) := residueField_charZero_of_model00 v hv h00
  exact exists_simpleResidueRoot_of_finite_RV_pattern v E t ht i α F
    (fun j => hJ j.val j.property) hS

end SpecialTransformations.Section7

end AlgebraicResidueRootProof
