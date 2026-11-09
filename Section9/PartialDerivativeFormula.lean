import Section9.VFJacobian
import Section8.ContinuityFormula

/-! Same-base formula for a partial derivative. The three scalar
quantifiers range over nonzero VF elements. Their values are the
tolerance, the radius, and the punctured increment. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n m : ℕ}

private abbrev GraphIndex (n m : ℕ) := Fin n ⊕ Fin m
private abbrev DerivativeIndex (n m : ℕ) := GraphIndex n m ⊕ Fin 1
private abbrev ToleranceIndex (n m : ℕ) := DerivativeIndex n m ⊕ Fin 1
private abbrev RadiusIndex (n m : ℕ) := ToleranceIndex n m ⊕ Fin 1
private abbrev IncrementIndex (n m : ℕ) := RadiusIndex n m ⊕ Fin 1
private abbrev TestIndex (n m : ℕ) := IncrementIndex n m ⊕ Fin m

private noncomputable def ringTerm {ι : Type} (p : FreeCommRing ι) : LRV.Term ι :=
  RingSyntax.ofRingTerm (FirstOrder.Ring.termOfFreeCommRing p)

private def inputIndex (j : Fin n) : TestIndex n m := .inl (.inl (.inl (.inl (.inl (.inl j)))))
private def valueIndex (i : Fin m) : TestIndex n m := .inl (.inl (.inl (.inl (.inl (.inr i)))))
private def slopeIndex : TestIndex n m := .inl (.inl (.inl (.inl (.inr 0))))
private def toleranceIndex : TestIndex n m := .inl (.inl (.inl (.inr 0)))
private def radiusIndex : TestIndex n m := .inl (.inl (.inr 0))
private def incrementIndex : TestIndex n m := .inl (.inr 0)

private def shiftedTerm (j l : Fin n) : LRV.Term (TestIndex n m) :=
  if j = l then .func Fn.vfAdd ![.var (inputIndex l), .var incrementIndex]
  else .var (inputIndex l)

private noncomputable def shiftedCode (j : Fin n) (z : TestIndex n m → M) : GraphIndex n m → M :=
  Sum.elim (fun l => (shiftedTerm j l).realize z) (z ∘ Sum.inr)

private noncomputable def scaledTerm : LRV.Term (TestIndex n m) :=
  ringTerm (FreeCommRing.of toleranceIndex * FreeCommRing.of incrementIndex)

private noncomputable def errorTerm (i : Fin m) : LRV.Term (TestIndex n m) :=
  ringTerm (FreeCommRing.of (.inr i) - FreeCommRing.of (valueIndex i) -
    FreeCommRing.of slopeIndex * FreeCommRing.of incrementIndex)

private def badIncrement (G : Set (GraphIndex n m → M)) (j : Fin n) (i : Fin m) :
    Set (TestIndex n m → M) :=
  {z | shiftedCode j z ∈ G ∧
    (iVF (z incrementIndex) ∧ z incrementIndex ≠ iVFZero) ∧
    ¬ termValueLe (.var radiusIndex) (.var incrementIndex) z ∧
    termValueLe scaledTerm (errorTerm i) z}

private theorem badIncrement_definable {S : Set M} {G : Set (GraphIndex n m → M)}
    (hG : S.Definable LRV G) (j : Fin n) (i : Fin m) :
    S.Definable LRV (badIncrement G j i) := by
  have hshift : S.DefinableMap LRV (shiftedCode (M := M) (m := m) j) := by
    rintro (l | l)
    · exact ((shiftedTerm (m := m) j l).definableFun_realize).mono (Set.empty_subset S)
    · exact Set.DefinableFun.proj LRV
  exact (hG.preimage_map hshift).inter ((properRadiusAt_definable S incrementIndex).inter
    ((termValueLe_definable S (.var radiusIndex) (.var incrementIndex)).compl.inter
      (termValueLe_definable S scaledTerm (errorTerm i))))

private def badOnRadius (G : Set (GraphIndex n m → M)) (j : Fin n) (i : Fin m) :
    Set (RadiusIndex n m → M) :=
  {z | ∃ t : Fin 1 → M, ∃ y : Fin m → M, Sum.elim (Sum.elim z t) y ∈ badIncrement G j i}

private theorem badOnRadius_definable {S : Set M} {G : Set (GraphIndex n m → M)}
    (hG : S.Definable LRV G) (j : Fin n) (i : Fin m) :
    S.Definable LRV (badOnRadius G j i) :=
  ((badIncrement_definable hG j i).exists_of_finite).exists_of_finite

private def hasGoodRadius (G : Set (GraphIndex n m → M)) (j : Fin n) (i : Fin m) :
    Set (ToleranceIndex n m → M) :=
  {z | ∃ r : Fin 1 → M, (iVF (r 0) ∧ r 0 ≠ iVFZero) ∧
    Sum.elim z r ∉ badOnRadius G j i}

private theorem hasGoodRadius_definable {S : Set M} {G : Set (GraphIndex n m → M)}
    (hG : S.Definable LRV G) (j : Fin n) (i : Fin m) :
    S.Definable LRV (hasGoodRadius G j i) :=
  ((properRadiusAt_definable S (.inr 0 : RadiusIndex n m)).inter
    (badOnRadius_definable hG j i).compl).exists_of_finite

/-- The raw derivative graph records the original input and output and
one proposed partial slope. -/
def partialDerivativeCodes (G : Set (GraphIndex n m → M)) (j : Fin n) (i : Fin m) :
    Set (DerivativeIndex n m → M) :=
  {z | z ∘ Sum.inl ∈ G ∧ iVF (z (.inr 0)) ∧ ∀ e : Fin 1 → M,
    (iVF (e 0) ∧ e 0 ≠ iVFZero) → Sum.elim z e ∈ hasGoodRadius G j i}

theorem partialDerivativeCodes_definable {S : Set M} {G : Set (GraphIndex n m → M)}
    (hG : S.Definable LRV G) (j : Fin n) (i : Fin m) :
    S.Definable LRV (partialDerivativeCodes G j i) :=
  (hG.preimage_comp Sum.inl).inter
    ((((definableAt_sort S .vf).raw_definable).preimage_comp
      (Sum.inr : Fin 1 → DerivativeIndex n m)).inter
      (((properRadiusAt_definable S (.inr 0 : ToleranceIndex n m)).himp
        (hasGoodRadius_definable hG j i)).forall_of_finite))

attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

local notation "VF" => VFType (M := M)
local notation "v" => Values.vfValueHom (M := M)

theorem termValueLe_iff_vfValue {ι : Type} {z : ι → M} (l r : LRV.Term ι)
    {x y : VF} (hx : l.realize z = x.val) (hy : r.realize z = y.val) :
    termValueLe l r z ↔ v y ≤ v x := by
  have hrv (t : LRV.Term ι) :
      (.func Fn.rvMap ![t] : LRV.Term ι).realize z = iRv (t.realize z) := by
    rw [Term.realize]
    unfold iRv
    congr 1
    funext i
    fin_cases i
    rfl
  change iLe ((.func Fn.rvMap ![r] : LRV.Term ι).realize z)
    ((.func Fn.rvMap ![l] : LRV.Term ι).realize z) ↔ _
  rw [hrv, hrv, hx, hy]
  exact Values.vf_pred_iff_gamma_le x y

def derivativeCode (a : Fin n → VF) (b : Fin m → VF) (d : VF) :
    DerivativeIndex n m → M := Sum.elim (Sum.elim (vfValues a) (vfValues b)) ![d.val]

private theorem badOnRadius_iff (f : (Fin n → VF) → Fin m → VF) (j : Fin n) (i : Fin m)
    (a : Fin n → VF) (d e r : VF) :
    Sum.elim (Sum.elim (derivativeCode a (f a) d) ![e.val]) ![r.val] ∈
        badOnRadius (vfGraph f) j i ↔
      ∃ t : VF, t ≠ 0 ∧ v r < v t ∧
        v (f (a + Pi.single j t) i - f a i - d * t) ≤ v e * v t := by
  let z := Sum.elim (Sum.elim (derivativeCode a (f a) d) ![e.val]) ![r.val]
  have htSem (t : VF) (y : Fin m → M) :
      shiftedCode j (Sum.elim (Sum.elim z ![t.val]) y) =
        Sum.elim (vfValues (a + Pi.single j t)) y := by
    funext k
    rcases k with l | l
    · by_cases hl : j = l
      · subst l
        simp only [shiftedCode, Sum.elim_inl, shiftedTerm, if_true, Term.realize,
          vfValues, Pi.add_apply, Pi.single_eq_same]
        congr 1
        funext i
        fin_cases i <;> rfl
      · simp only [shiftedCode, Sum.elim_inl, shiftedTerm, if_neg hl, Term.realize_var,
          vfValues, Pi.add_apply, Pi.single_eq_of_ne (Ne.symm hl), add_zero]
        rfl
    · rfl
  have hy (t : VF) (y : Fin m → M) :
      shiftedCode j (Sum.elim (Sum.elim z ![t.val]) y) ∈ vfGraph f ↔
        y = vfValues (f (a + Pi.single j t)) := by
    rw [htSem]
    constructor
    · rintro ⟨x, hx⟩
      have he : x = a + Pi.single j t :=
        vfValues_injective (funext fun k => congrFun hx (.inl k))
      subst x
      exact funext fun k => (congrFun hx (.inr k)).symm
    · rintro rfl
      exact ⟨_, rfl⟩
  have hsem (t : VF) :
      Sum.elim (Sum.elim z ![t.val]) (vfValues (f (a + Pi.single j t))) ∈
          badIncrement (vfGraph f) j i ↔
        t ≠ 0 ∧ v r < v t ∧ v (f (a + Pi.single j t) i - f a i - d * t) ≤ v e * v t := by
    let code : TestIndex n m → M :=
      Sum.elim (Sum.elim z ![t.val]) (vfValues (f (a + Pi.single j t)))
    let c0 : DerivativeIndex n m → VF := Sum.elim (Sum.elim a (f a)) ![d]
    let c1 : ToleranceIndex n m → VF := Sum.elim c0 ![e]
    let c2 : RadiusIndex n m → VF := Sum.elim c1 ![r]
    let c3 : IncrementIndex n m → VF := Sum.elim c2 ![t]
    let typed : TestIndex n m → VF := Sum.elim c3 (f (a + Pi.single j t))
    have hcode : code = fun k => (typed k).val := by
      funext k
      rcases k with (((((k | k) | k) | k) | k) | k) | k <;> first | rfl | (fin_cases k <;> rfl)
    have hScaled : (scaledTerm (n := n) (m := m)).realize code = (e * t).val := by
      dsimp only [scaledTerm, ringTerm]
      rw [hcode, RingSyntax.realizes, FirstOrder.Ring.realize_termOfFreeCommRing, map_mul,
        FreeCommRing.lift_of, FreeCommRing.lift_of]
      rfl
    have hError : (errorTerm (n := n) i).realize code =
        (f (a + Pi.single j t) i - f a i - d * t).val := by
      dsimp only [errorTerm, ringTerm]
      rw [hcode, RingSyntax.realizes, FirstOrder.Ring.realize_termOfFreeCommRing]
      simp only [map_sub, map_mul, FreeCommRing.lift_of]
      rfl
    have hzero : code incrementIndex ≠ iVFZero ↔ t ≠ 0 := by
      change t.val ≠ (0 : VF).val ↔ t ≠ 0
      exact not_congr Subtype.val_inj
    have hclose : (¬ termValueLe (.var radiusIndex) (.var incrementIndex) code) ↔ v r < v t := by
      rw [termValueLe_iff_vfValue _ _ (show _ = r.val from rfl) (show _ = t.val from rfl), not_le]
    have hbound := termValueLe_iff_vfValue _ _ hScaled hError
    rw [map_mul] at hbound
    change (shiftedCode j code ∈ vfGraph f ∧
      (iVF (code incrementIndex) ∧ code incrementIndex ≠ iVFZero) ∧
      (¬ termValueLe (.var radiusIndex) (.var incrementIndex) code) ∧
      termValueLe scaledTerm (errorTerm i) code) ↔ _
    have htVF : iVF (code incrementIndex) := t.property
    rw [hy, eq_self, true_and, and_iff_right htVF, hzero, hclose, hbound]
  constructor
  · rintro ⟨t, y, ht⟩
    let u : VF := ⟨t 0, ht.2.1.1⟩
    have he : ![u.val] = t := funext fun k => by fin_cases k; rfl
    rw [← he] at ht
    have hval := (hy u y).mp ht.1
    rw [hval] at ht
    exact ⟨u, (hsem u).mp ht⟩
  · rintro ⟨t, ht⟩
    exact ⟨![t.val], _, (hsem t).mpr ht⟩

/-- The raw formula recognizes the derivative in the paper's value
quotient without naming any representatives as parameters. -/
theorem partialDerivativeCodes_iff (f : (Fin n → VF) → Fin m → VF)
    (j : Fin n) (i : Fin m) (a : Fin n → VF) (d : VF) :
    derivativeCode a (f a) d ∈ partialDerivativeCodes (vfGraph f) j i ↔
      HasVFPartialAt f a j i d := by
  constructor
  · intro h ε
    obtain ⟨e, he, hve⟩ := gamma_has_vf_representative ε
    obtain ⟨r, hr, hgood⟩ := h.2.2 ![e.val] ⟨e.property, fun h => he (Subtype.ext h)⟩
    let b : VF := ⟨r 0, hr.1⟩
    have hb : b ≠ 0 := fun h => hr.2 (congrArg Subtype.val h)
    let δ := Values.gammaOf (CanonicalRV.encodedRv b)
      (fun h => hb ((CanonicalRV.encodedRv_zero_iff b).mp h))
    have hr' : ![b.val] = r := funext fun k => by fin_cases k; rfl
    rw [← hr'] at hgood
    refine ⟨δ, fun t ht hclose => ?_⟩
    apply lt_of_not_ge
    intro hbad
    apply hgood
    exact (badOnRadius_iff f j i a d e b).mpr ⟨t, ht, hclose, by rwa [hve]⟩
  · intro h
    refine ⟨⟨a, rfl⟩, d.property, fun e he => ?_⟩
    let b : VF := ⟨e 0, he.1⟩
    have hb : b ≠ 0 := fun h => he.2 (congrArg Subtype.val h)
    let ε := Values.gammaOf (CanonicalRV.encodedRv b)
      (fun h => hb ((CanonicalRV.encodedRv_zero_iff b).mp h))
    obtain ⟨δ, hδ⟩ := h ε
    obtain ⟨r, hr, hvr⟩ := gamma_has_vf_representative δ
    have he' : ![b.val] = e := funext fun k => by fin_cases k; rfl
    rw [← he']
    refine ⟨![r.val], ⟨r.property, fun h => hr (Subtype.ext h)⟩, fun hbad => ?_⟩
    obtain ⟨t, ht, hclose, hle⟩ := (badOnRadius_iff f j i a d b r).mp hbad
    exact (not_le_of_gt (hδ t ht (hvr ▸ hclose))) hle

end SpecialTransformations.Section9
