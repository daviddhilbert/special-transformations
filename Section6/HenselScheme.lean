import Section6.HenselSchemeSemantics

/-! The native scheme expresses simple-root lifting in the valuation ring. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer

namespace SpecialTransformations.Section6.HenselianTheory

variable {K Γ M : Type} [Field K] [LinearOrderedCommGroupWithZero Γ] [LRV.Structure M]
variable {v : Valuation K Γ} (F : FieldInterpretation (M := M) v)

def SimpleRootLiftAt (v : Valuation K Γ) (n : ℕ) : Prop :=
  ∀ (c : Fin (n + 1) → K) (a : K), (∀ i, v (c i) ≤ 1) → v a ≤ 1 →
    v ((coefficientPolynomial c).eval a) < 1 →
    v ((coefficientPolynomial c).derivative.eval a) = 1 →
    ∃ b : K, v b ≤ 1 ∧ (coefficientPolynomial c).eval b = 0 ∧ v (b - a) < 1

private theorem allVF_realize {n : ℕ} (φ : Bf n) :
    (M ⊨ allSorted (fun _ => .vf) φ) ↔
      ∀ z : Fin n → K, φ.Realize default (F.pack ∘ z) := by
  simp only [allSorted, Sentence.Realize, BoundedFormula.realize_alls,
    BoundedFormula.realize_imp, sortedHyps_realize]
  constructor
  · intro h z
    exact h _ (fun i => F.pack_sort (z i))
  · intro h z hz
    choose w hw using fun i => (F.sort (z i)).mp (hz i)
    exact (funext hw) ▸ h w

private theorem exVF_realize {n : ℕ} (φ : Bf (n + 1)) (z : Fin n → M) :
    (exSorted .vf φ).Realize default z ↔
      ∃ b : K, φ.Realize default (Fin.snoc z (F.pack b)) := by
  simp only [exSorted, BoundedFormula.realize_ex, BoundedFormula.realize_inf,
    sortPred_realize, RVElim.realize_tv_last_snoc]
  constructor
  · rintro ⟨y, hy, h⟩
    obtain ⟨b, rfl⟩ := (F.sort y).mp hy
    exact ⟨b, h⟩
  · rintro ⟨b, hb⟩
    exact ⟨F.pack b, F.pack_sort b, hb⟩

private theorem foldr_and_realize {n : ℕ} {I : Type} (φ : I → Bf n)
    (z : Fin n → M) (l : List I) :
    ((l.map φ).foldr (· ⊓ ·) ⊤).Realize default z ↔
      ∀ i ∈ l, (φ i).Realize default z := by
  induction l with
  | nil => simp
  | cons i l ih => simp [ih]

include F in
theorem henselScheme_realize (n : ℕ) :
    (M ⊨ henselScheme n) ↔ SimpleRootLiftAt v n := by
  unfold henselScheme
  rw [allVF_realize F]
  have h (c : Fin (n + 1) → K) (a : K) :
      let z : Fin (n + 2) → M := F.pack ∘ Fin.snoc c a
      let t : Fin (n + 1) → Tm (n + 2) := fun i => .var (.inr i.castSucc)
      let x : Tm (n + 2) := .var (.inr (Fin.last (n + 1)))
      let ci : Bf (n + 2) :=
        ((List.finRange (n + 1)).map (fun i => integral (t i))).foldr (· ⊓ ·) ⊤
      let t' : Fin (n + 1) → Tm (n + 3) := fun i => .var (.inr i.castSucc.castSucc)
      let x' : Tm (n + 3) := .var (.inr (Fin.last (n + 1)).castSucc)
      let y : Tm (n + 3) := .var (.inr (Fin.last (n + 2)))
      ((ci ⊓ integral x ⊓ inMaximalIdeal (polynomialTerm t x) ⊓
          valuationOne (derivativeTerm t x)) ⟹
        exSorted .vf (integral y ⊓ pEq (polynomialTerm t' y) tVFZero ⊓
          inMaximalIdeal (tVFAdd y (tVFNeg x')))).Realize default z ↔
        ((∀ i, v (c i) ≤ 1) → v a ≤ 1 → v ((coefficientPolynomial c).eval a) < 1 →
          v ((coefficientPolynomial c).derivative.eval a) = 1 →
            ∃ b : K, v b ≤ 1 ∧ (coefficientPolynomial c).eval b = 0 ∧ v (b - a) < 1) := by
    dsimp only
    let z : Fin (n + 2) → M := F.pack ∘ Fin.snoc c a
    let t : Fin (n + 1) → Tm (n + 2) := fun i => .var (.inr i.castSucc)
    let x : Tm (n + 2) := .var (.inr (Fin.last (n + 1)))
    let t' : Fin (n + 1) → Tm (n + 3) := fun i => .var (.inr i.castSucc.castSucc)
    let x' : Tm (n + 3) := .var (.inr (Fin.last (n + 1)).castSucc)
    let y : Tm (n + 3) := .var (.inr (Fin.last (n + 2)))
    let z' (b : K) : Fin (n + 3) → M := Fin.snoc z (F.pack b)
    have ht (i) : (t i).realize (Sum.elim default z) = F.pack (c i) := by
      simp [t, z, Term.realize]
    have hx : x.realize (Sum.elim default z) = F.pack a := by
      simp [x, z, Term.realize]
    have ht' (b i) : (t' i).realize (Sum.elim default (z' b)) = F.pack (c i) := by
      simp [t', z', z, Term.realize]
    have hx' (b) : x'.realize (Sum.elim default (z' b)) = F.pack a := by
      simp [x', z', z, Term.realize]
    have hy (b) : y.realize (Sum.elim default (z' b)) = F.pack b := by
      simp [y, z', Term.realize]
    have hδ (b) : (tVFAdd y (tVFNeg x')).realize (Sum.elim default (z' b)) =
        F.pack (b - a) := by
      rw [realize_tVFAdd, realize_tVFNeg, hy, hx', sub_eq_add_neg, F.add, F.neg]
    have hc : (((List.finRange (n + 1)).map (fun i => integral (t i))).foldr (· ⊓ ·) ⊤).Realize
        default z ↔ ∀ i, v (c i) ≤ 1 := by
      rw [foldr_and_realize]
      simp only [List.mem_finRange, realize_integral F _ _ _ (ht _)]
      exact ⟨fun he i => he i trivial, fun he i _ => he i⟩
    have hconcl (b) :
        (integral y ⊓ pEq (polynomialTerm t' y) tVFZero ⊓
          inMaximalIdeal (tVFAdd y (tVFNeg x'))).Realize default (Fin.snoc z (F.pack b)) ↔
          v b ≤ 1 ∧ (coefficientPolynomial c).eval b = 0 ∧ v (b - a) < 1 := by
      change (integral y ⊓ pEq (polynomialTerm t' y) tVFZero ⊓
        inMaximalIdeal (tVFAdd y (tVFNeg x'))).Realize default (z' b) ↔ _
      simp only [BoundedFormula.realize_inf, realize_integral F y _ b (hy b),
        pEq, BoundedFormula.realize_bdEqual, realize_polynomialTerm F _ t' y c b (ht' b) (hy b),
        realize_tVFZero, ← F.zero, F.injective.eq_iff, realize_inMaximalIdeal F _ _ _ (hδ b),
        and_assoc]
    change
      (((List.finRange (n + 1)).map (fun i => integral (t i))).foldr (· ⊓ ·) ⊤ ⊓
        integral x ⊓ inMaximalIdeal (polynomialTerm t x) ⊓
        valuationOne (derivativeTerm t x) ⟹
          exSorted .vf (integral y ⊓ pEq (polynomialTerm t' y) tVFZero ⊓
            inMaximalIdeal (tVFAdd y (tVFNeg x')))).Realize default z ↔ _
    simp only [BoundedFormula.realize_imp, BoundedFormula.realize_inf, hc,
      realize_integral F x z a hx,
      realize_inMaximalIdeal F _ _ _ (realize_polynomialTerm F _ t x c a ht hx),
      realize_valuationOne F _ _ _ (realize_derivativeTerm F _ t x c a ht hx),
      exVF_realize F, hconcl, and_imp]
  constructor
  · intro hh c a
    exact (h c a).mp (hh (Fin.snoc c a))
  · intro hh z
    let c := z ∘ Fin.castSucc
    let a := z (Fin.last (n + 1))
    have hz : Fin.snoc c a = z := by
      funext i
      cases i using Fin.lastCases <;> simp [c, a]
    rw [← hz]
    exact (h c a).mpr (hh c a)

end SpecialTransformations.Section6.HenselianTheory
