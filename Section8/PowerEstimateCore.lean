module

public import Section4.PolydiscLocal
public import Section8.UnarySlope
public import Section8.VFNeighbourhoods
public import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
public import Section8.UnaryGerm
public import Section8.NeighbourhoodRelations

@[expose] public section

section

/-! The ultrametric step of 8.6 and the continuity consequence used in
8.7. Bounds are expressed in the reversed multiplicative order. -/

open Filter Topology
open SpecialTransformations.Section4

namespace SpecialTransformations.Section8

variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]

theorem power_bound_raise (v : Valuation K Γ) {p q d : ℕ} {z : K} {C R : Γ}
    (h : v z ^ q ≤ C * R ^ p) : v z ^ (q * d) ≤ C ^ d * R ^ (p * d) := by
  rw [pow_mul, pow_mul, ← mul_pow]
  exact pow_le_pow_left₀ zero_le h d

theorem power_bound_add (v : Valuation K Γ) {p q : ℕ} {x y : K} {C D R T : Γ}
    (hx : v x ^ q ≤ C * R ^ p) (hy : v y ^ q ≤ D * T ^ p) :
    v (x + y) ^ q ≤ max C D * (max R T) ^ p := by
  have h₁ : v x ^ q ≤ max C D * (max R T) ^ p := hx.trans
    (mul_le_mul (le_max_left C D) (pow_le_pow_left₀ zero_le (le_max_left R T) p)
      zero_le zero_le)
  have h₂ : v y ^ q ≤ max C D * (max R T) ^ p := hy.trans
    (mul_le_mul (le_max_right C D) (pow_le_pow_left₀ zero_le (le_max_right R T) p)
      zero_le zero_le)
  apply (pow_le_pow_left₀ zero_le (v.map_add x y) q).trans
  rcases le_total (v x) (v y) with h | h
  · rwa [max_eq_right h]
  · rwa [max_eq_left h]

theorem tendsto_of_positive_power_bound {α : Type} {l : Filter α} [Valued K Γ]
    (f : α → K) (a c : K) (hc : c ≠ 0) (R : α → Γ) {p q : ℕ} (hp : 0 < p)
    (hR : ∀ r : K, r ≠ 0 → ∀ᶠ x in l, R x < Valued.v r)
    (h : ∀ᶠ x in l, Valued.v (f x - a) ^ q ≤ Valued.v c * R x ^ p) :
    Tendsto f l (𝓝 a) := by
  let v : Valuation K Γ := Valued.v
  intro U hU
  obtain ⟨s, hs, hsub⟩ := exists_nonzero_ball_subset a hU
  let d := s ^ q / c
  have hd : d ≠ 0 := div_ne_zero (pow_ne_zero _ hs) hc
  obtain ⟨r, hr, hrd, hr₁⟩ : ∃ r : K, r ≠ 0 ∧ v r ≤ v d ∧ v r ≤ 1 := by
    by_cases h : v d ≤ 1
    · exact ⟨d, hd, le_rfl, h⟩
    · exact ⟨1, one_ne_zero, by simpa only [map_one] using le_of_not_ge h, by rw [map_one]⟩
  change f ⁻¹' U ∈ l
  filter_upwards [hR r hr, h] with x hx hval
  apply hsub
  change v (f x - a) < v s
  have hp' : R x ^ p ≤ R x := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
    rw [pow_succ]
    exact mul_le_of_le_one_left zero_le (pow_le_one₀ zero_le (hx.le.trans hr₁))
  have hx' : R x < v s ^ q / v c := by
    simpa only [d, map_div₀, map_pow] using hx.trans_le hrd
  have hcpos : 0 < v c := pos_iff_ne_zero.mpr (v.ne_zero_iff.mpr hc)
  have hsmall : v (f x - a) ^ q < v s ^ q := calc
    _ ≤ v c * R x ^ p := hval
    _ ≤ v c * R x := mul_le_mul_of_nonneg_left hp' zero_le
    _ = R x * v c := mul_comm _ _
    _ < v s ^ q := (lt_div_iff₀ hcpos).mp hx'
  exact lt_of_not_ge (fun h => (not_le_of_gt hsmall) (pow_le_pow_left₀ zero_le h q))

end SpecialTransformations.Section8

end

section

/-! The power inequality of 8.6 on the actual Gamma quotient implies
continuity in the product valuation topology. -/

set_option backward.isDefEq.respectTransparency false

open Filter Topology FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace SpecialTransformations.Section8

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n m : ℕ}

theorem vfValue_lt_iff_presentation (x y : VFType (M := M)) :
    Values.vfValueHom x < Values.vfValueHom y ↔
      Values.presentationValuation y < Values.presentationValuation x :=
  lt_iff_not_ge.trans ((not_congr ((Values.vf_pred_iff_gamma_le x y).symm.trans
    (Values.presentation_compatible x y))).trans lt_iff_not_ge.symm)

theorem mem_uniformBall_iff_tupleValue (hn : 0 < n) (a x : Fin n → VFType (M := M))
    (r : VFType (M := M)) (hr : r ≠ 0) :
    vfValues x ∈ uniformBall (vfValues a) r.val ↔ Values.vfValueHom r < vfTupleValue (x - a) := by
  have hi (i : Fin n) : (x i).val ∈ rawOpenBall (a i).val r.val ↔
      Values.vfValueHom r < Values.vfValueHom (x i - a i) :=
    (mem_rawOpenBall_iff Values.presentationValuation Values.presentation_compatible (a i) r (x i) hr).trans
      (vfValue_lt_iff_presentation r (x i - a i)).symm
  constructor
  · intro hx
    obtain ⟨i, he⟩ := vfTupleValue_eq_component (x - a) hn
    rw [he]
    exact (hi i).mp (hx i)
  · intro hx i
    exact (hi i).mpr (hx.trans_le (vfTupleValue_le_component (x - a) i))

def vfPositivePowerEstimate
    (f : (Fin n → VFType (M := M)) → (Fin m → VFType (M := M)))
    (a : Fin n → VFType (M := M)) (p q : ℕ) (c r : Values.Gamma (M := M)) : Prop :=
  ∀ x, r.val < vfTupleValue (x - a) →
    c.val ^ q * vfTupleValue (x - a) ^ p ≤ vfTupleValue (f x - f a) ^ q

inductive PowerComparison where
  | lowerBound
  | equality
  | constant

/-- The conditions tested by the common family formula. -/
def PowerComparison.holds (mode : PowerComparison) (p q : ℕ)
    (a b : Fin n → VFType (M := M)) (y z : Fin m → VFType (M := M)) (c : Values.GammaTop (M := M)) : Prop :=
  match mode with
  | .lowerBound => c ^ q * vfTupleValue (b - a) ^ p ≤ vfTupleValue (z - y) ^ q
  | .equality => vfTupleValue (z - y) ^ q = c ^ q * vfTupleValue (b - a) ^ p
  | .constant => z = y

def PowerComparison.onBall (mode : PowerComparison)
    (f : (Fin n → VFType (M := M)) → (Fin m → VFType (M := M)))
    (a : Fin n → VFType (M := M)) (p q : ℕ) (c r : Values.Gamma (M := M)) : Prop :=
  ∀ x, r.val < vfTupleValue (x - a) → mode.holds p q a x (f a) (f x) c.val

theorem continuousAt_of_vfPositivePowerEstimate
    (f : (Fin n → VFType (M := M)) → (Fin m → VFType (M := M)))
    (a : Fin n → VFType (M := M)) (hn : 0 < n) {p q : ℕ} (hp : 0 < p)
    {c r : Values.Gamma (M := M)} (h : vfPositivePowerEstimate f a p q c r) :
    letI : Valued (VFType (M := M)) (Values.presentationType (M := M)) :=
      Valued.mk' Values.presentationValuation
    ContinuousAt f a := by
  let v := Values.presentationValuation (M := M)
  letI : Valued (VFType (M := M)) (Values.presentationType (M := M)) := Valued.mk' v
  by_cases hm : 0 < m
  · let R (x : Fin n → VFType (M := M)) := v (dominantCoordinate v (x - a) hn)
    have hR (s : VFType (M := M)) (hs : s ≠ 0) : ∀ᶠ x in 𝓝 a, R x < v s := by
      filter_upwards [uniformBall_mem_nhds Values.presentation_compatible a s hs] with x hx
      exact ((mem_uniformBall_iff v Values.presentation_compatible a x s hs).mp hx)
        (dominantIndex v (x - a) hn)
    obtain ⟨u, hu, huv⟩ := gamma_has_vf_representative c
    obtain ⟨s, hs, hsv⟩ := gamma_has_vf_representative r
    have hbound : ∀ᶠ x in 𝓝 a, ∀ i,
        v (f x i - f a i) ^ q ≤ v (u ^ q) * R x ^ p := by
      filter_upwards [uniformBall_mem_nhds Values.presentation_compatible a s hs] with x hx i
      have hx' := (mem_uniformBall_iff_tupleValue hn a x s hs).mp hx
      rw [hsv] at hx'
      let X := dominantCoordinate v (x - a) hn
      let Y := dominantCoordinate v (f x - f a) hm
      have he : Values.vfValueHom (u ^ q * X ^ p) ≤ Values.vfValueHom (Y ^ q) := by
        have he := h x hx'
        simpa only [vfTupleValue, dif_pos hn, dif_pos hm, X, Y, v, map_mul, map_pow, huv] using he
      have hv := (Values.presentation_compatible _ _).mp ((Values.vf_pred_iff_gamma_le _ _).mpr he)
      have hi := value_le_dominantCoordinate v (f x - f a) hm i
      exact (pow_le_pow_left₀ zero_le hi q).trans (by
        change v (Y ^ q) ≤ v (u ^ q * X ^ p) at hv
        simpa only [R, X, map_pow, map_mul] using hv)
    apply tendsto_pi_nhds.mpr
    intro i
    exact tendsto_of_positive_power_bound (fun x => f x i) (f a i) (u ^ q) (pow_ne_zero _ hu) R hp hR
      (hbound.mono (fun x hx => hx i))
  · have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
    subst m
    have he : f = fun _ => f a := funext (fun x => funext (fun i => i.elim0))
    rw [he]
    exact continuousAt_const

end SpecialTransformations.Section8

end

section

/-! Combine horizontal and vertical estimates in the proof of 8.6.
One common positive denominator works after shrinking the radii. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3

namespace SpecialTransformations.Section8

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n m : ℕ}

theorem vfTupleValue_snoc (a : Fin n → VFType (M := M)) (b : VFType (M := M)) :
    vfTupleValue (Fin.snoc a b) = min (vfTupleValue a) (Values.vfValueHom b) := by
  apply le_antisymm
  · apply le_min
    · by_cases hn : 0 < n
      · obtain ⟨i, hi⟩ := vfTupleValue_eq_component a hn
        rw [hi]
        simpa only [Fin.snoc_castSucc] using vfTupleValue_le_component (Fin.snoc a b) i.castSucc
      · have he : vfTupleValue a = Values.infinity := by simp only [vfTupleValue, dif_neg hn]
        rw [he]
        exact Values.le_infinity _
    · simpa only [Fin.snoc_last] using vfTupleValue_le_component (Fin.snoc a b) (Fin.last n)
  · obtain ⟨i, hi⟩ := vfTupleValue_eq_component (Fin.snoc a b) (Nat.succ_pos n)
    rw [hi]
    refine Fin.lastCases ?_ (fun i => ?_) i
    · rw [Fin.snoc_last]
      exact min_le_right _ _
    · rw [Fin.snoc_castSucc]
      exact (min_le_left _ _).trans (vfTupleValue_le_component a i)

theorem vfTupleValue_add_ge_min (x y : Fin m → VFType (M := M)) :
    min (vfTupleValue x) (vfTupleValue y) ≤ vfTupleValue (x + y) := by
  by_cases hm : 0 < m
  · obtain ⟨i, hi⟩ := vfTupleValue_eq_component (x + y) hm
    rw [hi]
    let v := Values.presentationValuation (M := M)
    have hv := v.map_add (x i) (y i)
    rcases le_total (v (x i)) (v (y i)) with h | h
    · rw [max_eq_right h] at hv
      exact (min_le_right _ _).trans ((vfTupleValue_le_component y i).trans
        ((Values.vf_pred_iff_gamma_le _ _).mp ((Values.presentation_compatible _ _).mpr hv)))
    · rw [max_eq_left h] at hv
      exact (min_le_left _ _).trans ((vfTupleValue_le_component x i).trans
        ((Values.vf_pred_iff_gamma_le _ _).mp ((Values.presentation_compatible _ _).mpr hv)))
  · simp only [vfTupleValue, dif_neg hm, min_self, le_refl]

theorem vfPositivePowerEstimate_to_unit_numerator
    {f : (Fin n → VFType (M := M)) → (Fin m → VFType (M := M))}
    {a : Fin n → VFType (M := M)} {p q d : ℕ} (hp : 0 < p) (hd : 0 < d)
    {c r : Values.Gamma (M := M)} (h : vfPositivePowerEstimate f a p q c r) :
    vfPositivePowerEstimate f a 1 (q * d) c (max r 1) := by
  intro x hx
  have hr : r.val < vfTupleValue (x - a) :=
    (show r.val ≤ (max r 1).val from le_max_left r 1).trans_lt hx
  have h₁ : (1 : Values.GammaTop (M := M)) ≤ vfTupleValue (x - a) :=
    (show (1 : Values.Gamma (M := M)).val ≤ (max r 1).val from le_max_right r 1).trans hx.le
  have he := pow_le_pow_left' (h x hr) d
  rw [mul_pow, ← pow_mul, ← pow_mul, ← pow_mul] at he
  rw [pow_one]
  exact (mul_le_mul' le_rfl (le_self_pow h₁ (Nat.mul_ne_zero hp.ne' hd.ne'))).trans he

theorem vfPositivePowerEstimate_snoc_of_uniform_slices
    (f : (Fin (n + 1) → VFType (M := M)) → (Fin m → VFType (M := M)))
    (a : Fin n → VFType (M := M)) (b : VFType (M := M)) (q : ℕ)
    (c₁ r₁ c₂ r₂ : Values.Gamma (M := M))
    (hfirst : ∀ y : VFType (M := M), r₂.val < Values.vfValueHom (y - b) →
      vfPositivePowerEstimate (fun x => f (Fin.snoc x y)) a 1 q c₁ r₁)
    (hlast : ∀ y : VFType (M := M), r₂.val < Values.vfValueHom (y - b) →
      c₂.val ^ q * Values.vfValueHom (y - b) ≤ vfTupleValue (f (Fin.snoc a y) - f (Fin.snoc a b)) ^ q) :
    vfPositivePowerEstimate f (Fin.snoc a b) 1 q (min c₁ c₂) (max r₁ r₂) := by
  intro z hz
  let x := Fin.init z
  let y := z (Fin.last n)
  have hzy : Fin.snoc x y = z := Fin.snoc_init_self _
  have hdiff : z - Fin.snoc a b = Fin.snoc (x - a) (y - b) := by
    rw [← hzy]
    funext i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp only [Pi.sub_apply, Fin.snoc_last]
    · simp only [Pi.sub_apply, Fin.snoc_castSucc]
  let X := vfTupleValue (x - a)
  let Y := Values.vfValueHom (y - b)
  have hXY : vfTupleValue (z - Fin.snoc a b) = min X Y := by
    rw [hdiff, vfTupleValue_snoc]
  rw [hXY] at hz ⊢
  have hx : r₁.val < X := lt_of_le_of_lt (le_max_left r₁ r₂) (hz.trans_le (min_le_left _ _))
  have hy : r₂.val < Y := lt_of_le_of_lt (le_max_right r₁ r₂) (hz.trans_le (min_le_right _ _))
  let u := f (Fin.snoc x y) - f (Fin.snoc a y)
  let w := f (Fin.snoc a y) - f (Fin.snoc a b)
  have hu : c₁.val ^ q * X ≤ vfTupleValue u ^ q := by
    simpa only [X, u, pow_one] using hfirst y hy x hx
  have hw : c₂.val ^ q * Y ≤ vfTupleValue w ^ q := hlast y hy
  have he : f z - f (Fin.snoc a b) = u + w := by
    rw [← hzy]
    exact (sub_add_sub_cancel _ _ _).symm
  rw [he, pow_one]
  let C := (min c₁ c₂).val ^ q * min X Y
  have h₁ : C ≤ vfTupleValue u ^ q := (mul_le_mul'
    (pow_le_pow_left' (show (min c₁ c₂).val ≤ c₁.val from min_le_left _ _) q) (min_le_left _ _)).trans hu
  have h₂ : C ≤ vfTupleValue w ^ q := (mul_le_mul'
    (pow_le_pow_left' (show (min c₁ c₂).val ≤ c₂.val from min_le_right _ _) q) (min_le_right _ _)).trans hw
  have h₃ : C ≤ (min (vfTupleValue u) (vfTupleValue w)) ^ q := by
    rcases le_total (vfTupleValue u) (vfTupleValue w) with h | h
    · rwa [min_eq_left h]
    · rwa [min_eq_right h]
  exact h₃.trans (pow_le_pow_left' (vfTupleValue_add_ge_min u w) q)

end SpecialTransformations.Section8

end

section

/-! One formula tests a powered local estimate in every VF family
fibre. The shift and radius remain variables of the formula. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace SpecialTransformations.Section8

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {ι : Type} {n m k : ℕ}
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

private noncomputable def estimateLeft (q : ℕ) : LRV.Term (Fin 5) :=
  let t : Fin 5 → FreeCommRing (Fin 5) := FreeCommRing.of
  RingSyntax.ofRingTerm (FirstOrder.Ring.termOfFreeCommRing ((t 0 - t 1) ^ q))

private noncomputable def estimateRight (p q : ℕ) : LRV.Term (Fin 5) :=
  let t : Fin 5 → FreeCommRing (Fin 5) := FreeCommRing.of
  RingSyntax.ofRingTerm (FirstOrder.Ring.termOfFreeCommRing (t 2 ^ q * (t 3 - t 4) ^ p))

private def estimateClause (mode : PowerComparison) (p q : ℕ)
    (a b : Fin n → M) (y z : Fin m → M) (c : M) : Prop :=
  let forward := fun i : Fin m => fun j : Fin n =>
    termValueLe (estimateLeft q) (estimateRight p q) ![z i, y i, c, b j, a j]
  let reverse := fun i : Fin m => fun j : Fin n =>
    termValueLe (estimateRight p q) (estimateLeft q) ![z i, y i, c, b j, a j]
  match mode with
  | .lowerBound => ∀ i, ∃ j, forward i j
  | .equality => (∀ i, ∃ j, forward i j) ∧ ∃ i, ∀ j, reverse i j
  | .constant => z = y

def estimateGraphCodes (G : Set (ι ⊕ (Fin n ⊕ Fin m) → M)) (p q : ℕ)
    (mode : PowerComparison := .lowerBound) :
    Set (((ι ⊕ (Fin n ⊕ Fin m)) ⊕ Fin 2) → M) :=
  {z | z ∘ Sum.inl ∈ G ∧ ¬ ∃ w : Fin n ⊕ Fin m → M,
    Sum.elim (fun i => z (.inl (.inl i))) w ∈ G ∧
    w ∘ Sum.inl ∈ uniformBall (fun i => z (.inl (.inr (.inl i)))) (z (.inr 1)) ∧
    ¬ estimateClause mode p q (fun i => z (.inl (.inr (.inl i)))) (w ∘ Sum.inl)
      (fun i => z (.inl (.inr (.inr i)))) (w ∘ Sum.inr) (z (.inr 0))}

theorem estimateGraphCodes_definable {S : Set M} {G : Set (ι ⊕ (Fin n ⊕ Fin m) → M)}
    (hG : S.Definable LRV G) (p q : ℕ) (mode : PowerComparison := .lowerBound) :
    S.Definable LRV (estimateGraphCodes G p q mode) := by
  let X := Fin n ⊕ Fin m
  let Z := (ι ⊕ X) ⊕ Fin 2
  let W := Z ⊕ X
  let a (j : Fin n) : W := .inl (.inl (.inr (.inl j)))
  let y (i : Fin m) : W := .inl (.inl (.inr (.inr i)))
  let c : W := .inl (.inr 0)
  let r : W := .inl (.inr 1)
  let b (j : Fin n) : W := .inr (.inl j)
  let z (i : Fin m) : W := .inr (.inr i)
  let comp : ι ⊕ X → W := Sum.elim (Sum.inl ∘ Sum.inl ∘ Sum.inl) Sum.inr
  let box : (Fin n ⊕ Fin n) ⊕ Fin 1 → W := Sum.elim (Sum.elim a b) (fun _ => r)
  let row (i : Fin m) (j : Fin n) (w : W → M) := ![w (z i), w (y i), w c, w (b j), w (a j)]
  have hRow (i : Fin m) (j : Fin n) (l r : LRV.Term (Fin 5)) :
      S.Definable LRV {w : W → M | termValueLe l r (row i j w)} := by
    convert (termValueLe_definable S l r).preimage_comp (![z i, y i, c, b j, a j] : Fin 5 → W) using 1
    ext w
    have he : w ∘ (![z i, y i, c, b j, a j] : Fin 5 → W) = row i j w := by
      funext t
      fin_cases t <;> rfl
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, he]
  have hForward : S.Definable LRV {w : W → M | ∀ i, ∃ j,
      termValueLe (estimateLeft q) (estimateRight p q) (row i j w)} := by
    simp only [Set.ofPred_forall, Set.ofPred_exists]
    exact Set.definable_iInter_of_finite (fun i => Set.definable_iUnion_of_finite
      (fun j => hRow i j (estimateLeft q) (estimateRight p q)))
  have hClause : S.Definable LRV {w : W → M |
      estimateClause mode p q (w ∘ a) (w ∘ b) (w ∘ y) (w ∘ z) (w c)} := by
    cases mode with
    | lowerBound => exact hForward
    | equality =>
      have hReverse : S.Definable LRV {w : W → M | ∃ i, ∀ j,
          termValueLe (estimateRight p q) (estimateLeft q) (row i j w)} := by
        simp only [Set.ofPred_forall, Set.ofPred_exists]
        exact Set.definable_iUnion_of_finite (fun i => Set.definable_iInter_of_finite
          (fun j => hRow i j (estimateRight p q) (estimateLeft q)))
      exact hForward.inter hReverse
    | constant =>
      change S.Definable LRV {w : W → M | w ∘ z = w ∘ y}
      simp only [funext_iff, Set.ofPred_forall, Function.comp_apply]
      exact Set.definable_iInter_of_finite (fun i =>
        (Set.DefinableFun.proj LRV (i := z i)).ofPred_eq (Set.DefinableFun.proj LRV (i := y i)))
  have hBad := ((hG.preimage_comp comp).inter
    (((uniformBallRelation_definable S n).preimage_comp box).inter hClause.compl)).exists_of_finite
  convert (hG.preimage_comp (Sum.inl : ι ⊕ X → Z)).inter hBad.compl using 1
  ext u
  have hcomp (w : X → M) :
      Sum.elim (fun i => u (.inl (.inl i))) w = Sum.elim u w ∘ comp := by
    funext i
    cases i <;> rfl
  simp only [estimateGraphCodes, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_inter_iff, Set.mem_compl_iff,
    hcomp, Function.comp_apply, box, a, b, y, z, c, r, Sum.elim_inl, Sum.elim_inr] <;> rfl

private theorem termValueLe_iff_gamma {v : Fin 5 → M} (l r : LRV.Term (Fin 5))
    {x y : VFType (M := M)} (hl : l.realize v = x.val) (hr : r.realize v = y.val) :
    termValueLe l r v ↔ Values.vfValueHom y ≤ Values.vfValueHom x := by
  have hrv (s : LRV.Term (Fin 5)) :
      (.func Fn.rvMap ![s] : LRV.Term (Fin 5)).realize v = iRv (s.realize v) := by
    rw [Term.realize]
    unfold iRv
    congr 1
    funext i
    fin_cases i
    rfl
  change iLe ((.func Fn.rvMap ![r] : LRV.Term (Fin 5)).realize v)
    ((.func Fn.rvMap ![l] : LRV.Term (Fin 5)).realize v) ↔ _
  simp only [hrv, hl, hr]
  exact Values.vf_pred_iff_gamma_le x y

private theorem estimateTerm_iff (a b y z c : VFType (M := M)) (p q : ℕ) :
    (termValueLe (estimateLeft q) (estimateRight p q) ![z.val, y.val, c.val, b.val, a.val] ↔
      Values.vfValueHom c ^ q * Values.vfValueHom (b - a) ^ p ≤ Values.vfValueHom (z - y) ^ q) ∧
    (termValueLe (estimateRight p q) (estimateLeft q) ![z.val, y.val, c.val, b.val, a.val] ↔
      Values.vfValueHom (z - y) ^ q ≤ Values.vfValueHom c ^ q * Values.vfValueHom (b - a) ^ p) := by
  let t : Fin 5 → VFType (M := M) := ![z, y, c, b, a]
  have hcode : ![z.val, y.val, c.val, b.val, a.val] = fun i => (t i).val := by
    funext i
    fin_cases i <;> rfl
  have hl : (estimateLeft q).realize (fun i => (t i).val) = ((z - y) ^ q).val := by
    dsimp only [estimateLeft]
    rw [RingSyntax.realizes, FirstOrder.Ring.realize_termOfFreeCommRing]
    simp only [map_pow, map_sub, FreeCommRing.lift_of] <;> rfl
  have hr : (estimateRight p q).realize (fun i => (t i).val) = (c ^ q * (b - a) ^ p).val := by
    dsimp only [estimateRight]
    rw [RingSyntax.realizes, FirstOrder.Ring.realize_termOfFreeCommRing]
    simp only [map_pow, map_mul, map_sub, FreeCommRing.lift_of] <;> rfl
  rw [hcode]
  constructor
  · simpa only [map_mul, map_pow] using termValueLe_iff_gamma _ _ hl hr
  · simpa only [map_mul, map_pow] using termValueLe_iff_gamma _ _ hr hl

private theorem lowerEstimateClause_iff (hn : 0 < n) (hm : 0 < m)
    (a b : Fin n → VFType (M := M)) (y z : Fin m → VFType (M := M))
    (c : VFType (M := M)) (p q : ℕ) :
    estimateClause .lowerBound p q (vfValues a) (vfValues b) (vfValues y) (vfValues z) c.val ↔
      Values.vfValueHom c ^ q * vfTupleValue (b - a) ^ p ≤ vfTupleValue (z - y) ^ q := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := vfTupleValue_eq_component (z - y) hm
    obtain ⟨j, hj⟩ := h i
    rw [hi]
    have he := (estimateTerm_iff (a j) (b j) (y i) (z i) c p q).1.mp hj
    apply le_trans _ he
    have hmin : vfTupleValue (b - a) ≤ Values.vfValueHom (b j - a j) :=
      vfTupleValue_le_component (b - a) j
    exact mul_le_mul' le_rfl (pow_le_pow_left' hmin p)
  · intro h i
    obtain ⟨j, hj⟩ := vfTupleValue_eq_component (b - a) hn
    refine ⟨j, (estimateTerm_iff (a j) (b j) (y i) (z i) c p q).1.mpr ?_⟩
    change Values.vfValueHom c ^ q * Values.vfValueHom ((b - a) j) ^ p ≤
      Values.vfValueHom ((z - y) i) ^ q
    rw [← hj]
    apply h.trans
    have hmin := vfTupleValue_le_component (z - y) i
    gcongr

private theorem estimateClause_iff (hn : 0 < n) (hm : 0 < m) (mode : PowerComparison)
    (a b : Fin n → VFType (M := M)) (y z : Fin m → VFType (M := M))
    (c : VFType (M := M)) (p q : ℕ) :
    estimateClause mode p q (vfValues a) (vfValues b) (vfValues y) (vfValues z) c.val ↔
      mode.holds p q a b y z (Values.vfValueHom c) := by
  cases mode with
  | lowerBound => exact lowerEstimateClause_iff hn hm a b y z c p q
  | constant => exact vfValues_injective.eq_iff
  | equality =>
    have hReverse : (∃ i : Fin m, ∀ j : Fin n,
        termValueLe (estimateRight p q) (estimateLeft q)
          ![(z i).val, (y i).val, c.val, (b j).val, (a j).val]) ↔
        vfTupleValue (z - y) ^ q ≤ Values.vfValueHom c ^ q * vfTupleValue (b - a) ^ p := by
      constructor
      · rintro ⟨i, h⟩
        obtain ⟨j, hj⟩ := vfTupleValue_eq_component (b - a) hn
        rw [hj]
        exact (pow_le_pow_left' (vfTupleValue_le_component (z - y) i) q).trans
          ((estimateTerm_iff (a j) (b j) (y i) (z i) c p q).2.mp (h j))
      · intro h
        obtain ⟨i, hi⟩ := vfTupleValue_eq_component (z - y) hm
        refine ⟨i, fun j => (estimateTerm_iff (a j) (b j) (y i) (z i) c p q).2.mpr ?_⟩
        change Values.vfValueHom ((z - y) i) ^ q ≤ Values.vfValueHom c ^ q *
          Values.vfValueHom ((b - a) j) ^ p
        rw [← hi]
        exact h.trans (mul_le_mul' le_rfl (pow_le_pow_left' (vfTupleValue_le_component (b - a) j) p))
    change (estimateClause .lowerBound p q (vfValues a) (vfValues b) (vfValues y) (vfValues z) c.val ∧
      (∃ i : Fin m, ∀ j : Fin n, termValueLe (estimateRight p q) (estimateLeft q)
        ![(z i).val, (y i).val, c.val, (b j).val, (a j).val])) ↔ _
    rw [lowerEstimateClause_iff hn hm, hReverse, PowerComparison.holds]
    exact ⟨fun h => le_antisymm h.2 h.1, fun h => ⟨h.ge, h.le⟩⟩

theorem mem_estimateGraphCodes_iff (hn : 0 < n) (hm : 0 < m)
    (f : (Fin k → VFType (M := M)) → (Fin n → VFType (M := M)) → (Fin m → VFType (M := M)))
    (t : Fin k → VFType (M := M)) (a : Fin n → VFType (M := M))
    (c r : VFType (M := M)) (hc : c ≠ 0) (hr : r ≠ 0) (p q : ℕ)
    (mode : PowerComparison := .lowerBound) :
    Sum.elim (Sum.elim (vfValues t) (Sum.elim (vfValues a) (vfValues (f t a)))) ![c.val, r.val] ∈
        estimateGraphCodes (vfFamilyGraph f) p q mode ↔
      mode.onBall (f t) a p q
        (GammaThresholdGeometry.vfGamma c hc) (GammaThresholdGeometry.vfGamma r hr) := by
  constructor
  · intro h b hb
    apply (estimateClause_iff hn hm mode a b (f t a) (f t b) c p q).mp
    by_contra hnot
    exact h.2 ⟨Sum.elim (vfValues b) (vfValues (f t b)), ⟨(t, b), rfl⟩,
      (mem_uniformBall_iff_tupleValue hn a b r hr).mpr hb, hnot⟩
  · intro h
    refine ⟨⟨(t, a), rfl⟩, ?_⟩
    rintro ⟨w, hw, hb, hnot⟩
    change w ∈ {w | Sum.elim (vfValues t) w ∈ vfFamilyGraph f} at hw
    rw [vfFamilyGraph_fibre] at hw
    obtain ⟨b, rfl⟩ := hw
    have harg := (mem_uniformBall_iff_tupleValue hn a b r hr).mp hb
    exact hnot ((estimateClause_iff hn hm mode a b (f t a) (f t b) c p q).mpr (h b harg))

end SpecialTransformations.Section8

end

section

/-! Keep the valid shifts and radii as an RV fibre. Constancy of this
entire fibre can be used in the induction for 8.6. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace SpecialTransformations.Section8

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {ι : Type} {n m k : ℕ}

private abbrev EstimateIndices (ι : Type) (n m : ℕ) := ((ι ⊕ (Fin n ⊕ Fin m)) ⊕ Fin 2) ⊕ Fin 2

private def estimateRVGraphCodes (G : Set (ι ⊕ (Fin n ⊕ Fin m) → M)) (p q : ℕ)
    (mode : PowerComparison) :
    Set (EstimateIndices ι n m → M) :=
  {z | z ∘ Sum.inl ∈ estimateGraphCodes G p q mode ∧ ∀ i : Fin 2,
    iVF (z (.inl (.inr i))) ∧ GammaParameters.NonzeroRV (z (.inr i)) ∧
      iRv (z (.inl (.inr i))) = z (.inr i)}

private def estimateProject : (ι ⊕ Fin n) ⊕ Fin 2 → EstimateIndices ι n m :=
  Sum.elim (Sum.elim (fun i => .inl (.inl (.inl i))) (fun i => .inl (.inl (.inr (.inl i))))) Sum.inr

def estimateRVCodes (G : Set (ι ⊕ (Fin n ⊕ Fin m) → M)) (p q : ℕ)
    (mode : PowerComparison := .lowerBound) :
    Set (((ι ⊕ Fin n) ⊕ Fin 2) → M) :=
  (fun z => z ∘ estimateProject) '' estimateRVGraphCodes G p q mode

theorem estimateRVCodes_definable [Finite ι] {S : Set M} {G : Set (ι ⊕ (Fin n ⊕ Fin m) → M)}
    (hG : S.Definable LRV G) (p q : ℕ) (mode : PowerComparison := .lowerBound) :
    S.Definable LRV (estimateRVCodes G p q mode) := by
  let W := EstimateIndices ι n m
  have hCode (i : Fin 2) : S.Definable LRV {z : W → M |
      iVF (z (.inl (.inr i))) ∧ GammaParameters.NonzeroRV (z (.inr i)) ∧
        iRv (z (.inl (.inr i))) = z (.inr i)} := by
    let t : LRV.Term W := .func Fn.rvMap ![.var (.inl (.inr i))]
    have hterm (z : W → M) : t.realize z = iRv (z (.inl (.inr i))) := by
      dsimp only [t]
      rw [Term.realize]
      unfold iRv
      congr 1
      funext j
      fin_cases j
      rfl
    have he : S.Definable LRV {z : W → M | iRv (z (.inl (.inr i))) = z (.inr i)} := by
      convert (t.definableFun_realize.mono (Set.empty_subset S)).ofPred_eq
        (Set.DefinableFun.proj LRV (i := (.inr i : W))) using 1
      ext z
      simp only [Set.mem_ofPred_eq, hterm]
    exact (((definableAt_sort S .vf).raw_definable).preimage_comp (fun _ : Fin 1 => .inl (.inr i))).inter
      (((GammaParameters.nonzero_rv_definable S).preimage_comp (fun _ : Fin 1 => .inr i)).inter
        he)
  have hall : S.Definable LRV {z : W → M | ∀ i : Fin 2,
      iVF (z (.inl (.inr i))) ∧ GammaParameters.NonzeroRV (z (.inr i)) ∧
        iRv (z (.inl (.inr i))) = z (.inr i)} := by
    rw [Set.ofPred_forall]
    exact Set.definable_iInter_of_finite hCode
  exact (((estimateGraphCodes_definable hG p q mode).preimage_comp Sum.inl).inter hall).image_comp estimateProject

theorem estimateRVCodes_rv_proper {G : Set (ι ⊕ (Fin n ⊕ Fin m) → M)}
    {p q : ℕ} {mode : PowerComparison} {z : (ι ⊕ Fin n) ⊕ Fin 2 → M}
    (hz : z ∈ estimateRVCodes G p q mode) :
    GammaParameters.Proper (z ∘ Sum.inr) := by
  obtain ⟨w, hw, rfl⟩ := hz
  exact fun i => (hw.2 i).2.1

/-- Attach a fixed prefix before the VF parameter block. -/
def attachEstimatePrefix {I J X : Type} (u : I → M) (z : J ⊕ X → M) : (I ⊕ J) ⊕ X → M :=
  Sum.elim (Sum.elim u (z ∘ Sum.inl)) (z ∘ Sum.inr)

theorem mem_estimateRVCodes_attachPrefix {I J : Type}
    (G : Set ((I ⊕ J) ⊕ (Fin n ⊕ Fin m) → M)) (u : I → M) (p q : ℕ)
    (z : (J ⊕ Fin n) ⊕ Fin 2 → M) (mode : PowerComparison := .lowerBound) :
    Sum.elim (attachEstimatePrefix u (z ∘ Sum.inl)) (z ∘ Sum.inr) ∈ estimateRVCodes G p q mode ↔
      z ∈ estimateRVCodes {w | attachEstimatePrefix u w ∈ G} p q mode := by
  let X := Fin n ⊕ Fin m
  let lift (w : EstimateIndices J n m → M) : EstimateIndices (I ⊕ J) n m → M :=
    Sum.elim (Sum.elim (attachEstimatePrefix u (w ∘ Sum.inl ∘ Sum.inl))
      (w ∘ Sum.inl ∘ Sum.inr)) (w ∘ Sum.inr)
  let strip (w : EstimateIndices (I ⊕ J) n m → M) : EstimateIndices J n m → M :=
    Sum.elim (Sum.elim
      (Sum.elim (fun i => w (.inl (.inl (.inl (.inr i))))) (w ∘ Sum.inl ∘ Sum.inl ∘ Sum.inr))
      (w ∘ Sum.inl ∘ Sum.inr)) (w ∘ Sum.inr)
  let row : Set (J ⊕ X → M) := {w | attachEstimatePrefix u w ∈ G}
  have hgraph (w : EstimateIndices J n m → M) :
      lift w ∈ estimateRVGraphCodes G p q mode ↔ w ∈ estimateRVGraphCodes row p q mode := by
    simp only [lift, estimateRVGraphCodes, estimateGraphCodes, row, Set.mem_ofPred_eq, attachEstimatePrefix,
      Function.comp_apply, Sum.elim_inl, Sum.elim_inr, Sum.elim_comp_inl, Sum.elim_comp_inr]
    rfl
  have hproj (w : EstimateIndices J n m → M) :
      lift w ∘ estimateProject =
        Sum.elim (attachEstimatePrefix u ((w ∘ estimateProject) ∘ Sum.inl))
          ((w ∘ estimateProject) ∘ Sum.inr) := by
    funext i
    rcases i with ((i | i) | i) | i <;> rfl
  constructor
  · rintro ⟨w, hw, he⟩
    have hfix (i : I) : w (.inl (.inl (.inl (.inl i)))) = u i :=
      congrFun he (.inl (.inl (.inl i)))
    have hweq : w = lift (strip w) := by
      funext i
      rcases i with (((i | i) | i) | i) | i
      · exact hfix i
      all_goals rfl
    rw [hweq] at hw he
    refine ⟨strip w, (hgraph _).mp hw, ?_⟩
    change lift (strip w) ∘ estimateProject = _ at he
    rw [hproj] at he
    funext i
    rcases i with (i | i) | i
    · exact congrFun he (.inl (.inl (.inr i)))
    · exact congrFun he (.inl (.inr i))
    · exact congrFun he (.inr i)
  · rintro ⟨w, hw, rfl⟩
    exact ⟨lift w, (hgraph _).mpr hw, hproj w⟩

theorem mem_estimateRVCodes_iff (hn : 0 < n) (hm : 0 < m)
    (f : (Fin k → VFType (M := M)) → (Fin n → VFType (M := M)) → (Fin m → VFType (M := M)))
    (t : Fin k → VFType (M := M)) (a : Fin n → VFType (M := M))
    (d : Fin 2 → CanonicalRV.RVSort M) (hd : ∀ i, (d i).val ≠ iRVZero) (p q : ℕ)
    (mode : PowerComparison := .lowerBound) :
    Sum.elim (Sum.elim (vfValues t) (vfValues a)) (rvValues d) ∈ estimateRVCodes (vfFamilyGraph f) p q mode ↔
      mode.onBall (f t) a p q (Values.gammaOf (d 0) (hd 0)) (Values.gammaOf (d 1) (hd 1)) := by
  have hΓ (c : VFType (M := M)) (hc : c ≠ 0) (i : Fin 2) (h : iRv c.val = (d i).val) :
      GammaThresholdGeometry.vfGamma c hc = Values.gammaOf (d i) (hd i) :=
    Subtype.ext (congrArg Values.vrv (Subtype.ext h))
  have hnonzero (c : VFType (M := M)) (i : Fin 2) (h : iRv c.val = (d i).val) : c ≠ 0 :=
    fun hz => hd i (h.symm.trans ((CanonicalRV.encodedRv_zero_iff c).mpr hz))
  constructor
  · rintro ⟨u, hu, he⟩
    obtain ⟨⟨t', a'⟩, hg⟩ := hu.1.1
    have ht : t' = t := vfValues_injective (funext (fun i =>
      (congrFun hg (.inl i)).trans (congrFun he (.inl (.inl i)))))
    have ha : a' = a := vfValues_injective (funext (fun i =>
      (congrFun hg (.inr (.inl i))).trans (congrFun he (.inl (.inr i)))))
    subst t'
    subst a'
    let c : VFType (M := M) := ⟨u (.inl (.inr 0)), (hu.2 0).1⟩
    let r : VFType (M := M) := ⟨u (.inl (.inr 1)), (hu.2 1).1⟩
    have hc : iRv c.val = (d 0).val := (hu.2 0).2.2.trans (congrFun he (.inr 0))
    have hr : iRv r.val = (d 1).val := (hu.2 1).2.2.trans (congrFun he (.inr 1))
    have he' : u ∘ Sum.inl =
        Sum.elim (Sum.elim (vfValues t) (Sum.elim (vfValues a) (vfValues (f t a)))) ![c.val, r.val] := by
      funext i
      cases i with
      | inl j => exact (congrFun hg j).symm
      | inr j => fin_cases j <;> rfl
    have h := hu.1
    rw [he'] at h
    have hp := (mem_estimateGraphCodes_iff hn hm f t a c r (hnonzero c 0 hc) (hnonzero r 1 hr) p q mode).mp h
    rwa [hΓ c (hnonzero c 0 hc) 0 hc, hΓ r (hnonzero r 1 hr) 1 hr] at hp
  · intro h
    obtain ⟨c, hc⟩ := CanonicalRV.encodedRv_surjective (d 0)
    obtain ⟨r, hr⟩ := CanonicalRV.encodedRv_surjective (d 1)
    have hc' : iRv c.val = (d 0).val := congrArg Subtype.val hc
    have hr' : iRv r.val = (d 1).val := congrArg Subtype.val hr
    have hc₀ := hnonzero c 0 hc'
    have hr₀ := hnonzero r 1 hr'
    let u := Sum.elim (Sum.elim (vfValues t) (Sum.elim (vfValues a) (vfValues (f t a)))) ![c.val, r.val]
    refine ⟨Sum.elim u (rvValues d), ⟨?_, ?_⟩, ?_⟩
    · apply (mem_estimateGraphCodes_iff hn hm f t a c r hc₀ hr₀ p q mode).mpr
      rwa [hΓ c hc₀ 0 hc', hΓ r hr₀ 1 hr']
    · intro i
      fin_cases i
      · exact ⟨c.property, ⟨(d 0).property, hd 0⟩, hc'⟩
      · exact ⟨r.property, ⟨(d 1).property, hd 1⟩, hr'⟩
    · funext i
      rcases i with (i | i) | i <;> rfl

end SpecialTransformations.Section8

end
