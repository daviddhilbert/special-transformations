import Section3.GammaSpecialization
import Section8.ValuedSlopeIntegrality
import Mathlib.Topology.Algebra.Valued.ValuedField
import Mathlib.Algebra.Order.Group.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Tactic.Abel
import Section8.UnaryGerm
import Section8.UnaryPolynomial
import Section3.DefinableConstants

section

/-! The ball-preservation assumption in Lemma 8.4 gives the required
nonisolation property at zero, before applying the scalar power germ. -/

set_option backward.isDefEq.respectTransparency false

namespace SpecialTransformations.Section8

variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]

def centeredBall (v : Valuation K Γ) (r : K) : Set K := {x | v x < v r}

theorem zero_mem_centeredBall (v : Valuation K Γ) {r : K} (hr : r ≠ 0) :
    0 ∈ centeredBall v r := by
  change v 0 < v r
  rw [map_zero]
  exact pos_iff_ne_zero.mpr (v.ne_zero_iff.mpr hr)

theorem centered_bijection_zero (v : Valuation K Γ) (f : K → K) {a b : K} (hb : b ≠ 0)
    (hbij : Set.BijOn f (centeredBall v a) (centeredBall v b))
    (hballs : ∀ r : K, r ≠ 0 → ∃ s : K, s ≠ 0 ∧
      f '' (centeredBall v a ∩ centeredBall v r) = centeredBall v b ∩ centeredBall v s) : f 0 = 0 := by
  obtain ⟨x, hx, hfx⟩ := hbij.2.2 (zero_mem_centeredBall v hb)
  by_cases h : x = 0
  · rwa [h] at hfx
  · obtain ⟨s, hs, he⟩ := hballs x h
    have hzero : 0 ∈ f '' (centeredBall v a ∩ centeredBall v x) := by
      rw [he]
      exact ⟨zero_mem_centeredBall v hb, zero_mem_centeredBall v hs⟩
    obtain ⟨y, hy, hfy⟩ := hzero
    have hxy := hbij.2.1 hx hy.1 (hfx.trans hfy.symm)
    have hyx : v y < v x := hy.2
    rw [← hxy] at hyx
    exact False.elim ((lt_irrefl (v x)) hyx)

private theorem three_centered_balls_have_nonzero (v : Valuation K Γ)
    (e : K) (he : e ≠ 0) (he₁ : v e < 1) {a b c : K}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    ∃ x : K, x ≠ 0 ∧ x ∈ centeredBall v a ∧ x ∈ centeredBall v b ∧ x ∈ centeredBall v c := by
  classical
  let T : Finset K := {a, b, c}
  obtain ⟨r, hr, hmin⟩ := Finset.exists_min_image T v ⟨a, by simp [T]⟩
  have hr₀ : r ≠ 0 := by
    simp only [T, Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl <;> assumption
  have hlt : v (e * r) < v r := by
    rw [map_mul]
    exact (mul_lt_mul_of_pos_right he₁ (pos_iff_ne_zero.mpr (v.ne_zero_iff.mpr hr₀))).trans_le
      (by rw [one_mul])
  exact ⟨e * r, mul_ne_zero he hr₀, hlt.trans_le (hmin a (by simp [T])),
    hlt.trans_le (hmin b (by simp [T])), hlt.trans_le (hmin c (by simp [T]))⟩

theorem centered_bijection_close_nonzero (v : Valuation K Γ) (f : K → K) {a b : K} (hb : b ≠ 0)
    (hnt : ∃ e : K, e ≠ 0 ∧ v e < 1)
    (hbij : Set.BijOn f (centeredBall v a) (centeredBall v b))
    (hballs : ∀ r : K, r ≠ 0 → ∃ s : K, s ≠ 0 ∧
      f '' (centeredBall v a ∩ centeredBall v r) = centeredBall v b ∩ centeredBall v s)
    (r s : K) (hr : r ≠ 0) (hs : s ≠ 0) :
    ∃ x, x ≠ 0 ∧ x ∈ centeredBall v a ∧ x ∈ centeredBall v r ∧
      f x ≠ 0 ∧ f x ∈ centeredBall v s := by
  obtain ⟨e, he, he₁⟩ := hnt
  obtain ⟨t, ht, himage⟩ := hballs r hr
  obtain ⟨y, hy, hyb, hyt, hys⟩ := three_centered_balls_have_nonzero v e he he₁ hb ht hs
  have hyim : y ∈ f '' (centeredBall v a ∩ centeredBall v r) := by
    rw [himage]
    exact ⟨hyb, hyt⟩
  obtain ⟨x, hx, rfl⟩ := hyim
  refine ⟨x, ?_, hx.1, hx.2, hy, hys⟩
  intro hx₀
  apply hy
  rw [hx₀]
  exact centered_bijection_zero v f hb hbij hballs

theorem centered_bijection_preimage_neighbourhood (v : Valuation K Γ) (f : K → K)
    {a b : K} (hb : b ≠ 0) (hnt : ∃ e : K, e ≠ 0 ∧ v e < 1)
    (hbij : Set.BijOn f (centeredBall v a) (centeredBall v b))
    (hballs : ∀ r : K, r ≠ 0 → ∃ s : K, s ≠ 0 ∧
      f '' (centeredBall v a ∩ centeredBall v r) = centeredBall v b ∩ centeredBall v s)
    (s : K) (hs : s ≠ 0) :
    ∃ r : K, r ≠ 0 ∧ Set.MapsTo f (centeredBall v a ∩ centeredBall v r) (centeredBall v s) := by
  obtain ⟨e, he, he₁⟩ := hnt
  obtain ⟨y, hy, hyb, hys, _⟩ := three_centered_balls_have_nonzero v e he he₁ hb hs hs
  obtain ⟨x, hx, hxy⟩ := hbij.2.2 hyb
  have hx₀ : x ≠ 0 := by
    intro h
    exact hy (hxy.symm.trans (h ▸ centered_bijection_zero v f hb hbij hballs))
  obtain ⟨u, hu, himage⟩ := hballs x hx₀
  have hyu : y ∉ centeredBall v u := by
    intro hyu
    have hm : y ∈ f '' (centeredBall v a ∩ centeredBall v x) := himage.symm ▸ ⟨hyb, hyu⟩
    obtain ⟨z, hz, hzy⟩ := hm
    have heq := hbij.2.1 hz.1 hx (hzy.trans hxy.symm)
    exact (lt_irrefl (v x)) (heq ▸ hz.2)
  refine ⟨x, hx₀, fun z hz => ?_⟩
  have hm : f z ∈ centeredBall v b ∩ centeredBall v u := himage ▸ ⟨z, hz, rfl⟩
  exact (show v (f z) < v u from hm.2).trans_le
    ((le_of_not_gt hyu).trans (show v y < v s from hys).le)

end SpecialTransformations.Section8

end

section

/-! Arithmetic of the slope in 8.4. A new value with no nonzero integer
multiple in the old value group detects the integral part of a slope. -/

namespace SpecialTransformations.Section8

theorem integral_slope_of_value_coset {G : Type} [AddCommGroup G]
    (H : AddSubgroup G) {x y c : G}
    (hnew : ∀ j : ℤ, j ≠ 0 → j • x ∉ H) (hc : c ∈ H)
    (hy : ∃ (j : ℤ) (b : G), b ∈ H ∧ y = b + j • x)
    {p q : ℕ} (h : (q : ℤ) • y = (q : ℤ) • c + (p : ℤ) • x) :
    ∃ j : ℤ, (p : ℤ) = (q : ℤ) * j := by
  obtain ⟨j, b, hb, hy⟩ := hy
  refine ⟨j, sub_eq_zero.mp ?_⟩
  have he : (q : ℤ) • b + ((q : ℤ) * j) • x = (q : ℤ) • c + (p : ℤ) • x := by
    rw [hy, smul_add, smul_smul] at h
    exact h
  have he' : ((p : ℤ) - (q : ℤ) * j) • x = (q : ℤ) • b - (q : ℤ) • c := by
    calc
      _ = (-((q : ℤ) • c) + ((q : ℤ) • c + (p : ℤ) • x)) - ((q : ℤ) * j) • x := by
        rw [sub_smul]
        abel
      _ = _ := by rw [← he]; abel
  by_contra hne
  apply hnew _ hne
  rw [he']
  exact H.sub_mem (H.zsmul_mem hb _) (H.zsmul_mem hc _)

private theorem reciprocal_slope_identity {G : Type} [AddCommGroup G]
    (p q r s : ℤ) (c d x y : G)
    (hf : q • y = c + p • x) (hg : s • x = d + r • y) :
    (q * s - r * p) • x = q • d + r • c := by
  have he : (q * s) • x = q • d + (r • c + (r * p) • x) := by
    calc
      _ = q • (s • x) := by rw [smul_smul]
      _ = q • (d + r • y) := by rw [hg]
      _ = q • d + r • (q • y) := by rw [smul_add, smul_smul, smul_smul, mul_comm q r]
      _ = _ := by rw [hf, smul_add, smul_smul]
  rw [sub_smul, he]
  abel

theorem reciprocal_power_slopes {G : Type} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    (p q r s : ℤ) (c d x₁ x₂ y₁ y₂ : G) (hx : x₁ < x₂)
    (hf₁ : q • y₁ = c + p • x₁) (hf₂ : q • y₂ = c + p • x₂)
    (hg₁ : s • x₁ = d + r • y₁) (hg₂ : s • x₂ = d + r • y₂) : q * s = r * p := by
  have h₁ := reciprocal_slope_identity p q r s c d x₁ y₁ hf₁ hg₁
  have h₂ := reciprocal_slope_identity p q r s c d x₂ y₂ hf₂ hg₂
  have he : (q * s - r * p) • (x₂ - x₁) = (0 : ℤ) • (x₂ - x₁) := by
    rw [smul_sub, h₁, h₂, sub_self, zero_smul]
  exact sub_eq_zero.mp ((zsmul_left_inj (sub_pos.mpr hx)).mp he)

theorem reciprocal_power_slopes_mul {G : Type} [LinearOrderedCommGroupWithZero G]
    {p q r s : ℕ} {c d x₁ x₂ y₁ y₂ : G}
    (hc : c ≠ 0) (hd : d ≠ 0) (hx₁ : x₁ ≠ 0) (hx₂ : x₂ ≠ 0) (hx : x₁ ≠ x₂)
    (hf₁ : y₁ ^ q = c ^ q * x₁ ^ p) (hf₂ : y₂ ^ q = c ^ q * x₂ ^ p)
    (hg₁ : x₁ ^ s = d ^ s * y₁ ^ r) (hg₂ : x₂ ^ s = d ^ s * y₂ ^ r) : s * q = p * r := by
  let X := x₁ / x₂
  let Y := y₁ / y₂
  have hX : 0 < X := pos_iff_ne_zero.mpr (div_ne_zero hx₁ hx₂)
  have hX₁ : X ≠ 1 := fun h => hx (by simpa only [one_mul] using (div_eq_iff hx₂).mp h)
  have hF : Y ^ q = X ^ p := by
    dsimp only [X, Y]
    rw [div_pow, hf₁, hf₂, mul_div_mul_comm, div_self (pow_ne_zero _ hc), one_mul, ← div_pow]
  have hG : X ^ s = Y ^ r := by
    dsimp only [X, Y]
    rw [div_pow, hg₁, hg₂, mul_div_mul_comm, div_self (pow_ne_zero _ hd), one_mul, ← div_pow]
  apply (pow_right_injective₀ hX hX₁)
  calc
    X ^ (s * q) = (X ^ s) ^ q := pow_mul _ _ _
    _ = (Y ^ r) ^ q := congrArg (· ^ q) hG
    _ = (Y ^ q) ^ r := by rw [← pow_mul, Nat.mul_comm r q, pow_mul]
    _ = (X ^ p) ^ r := congrArg (· ^ r) hF
    _ = X ^ (p * r) := (pow_mul _ _ _).symm

theorem positive_integral_reciprocal_slope_eq_one {p q r s : ℕ}
    (hp : 0 < p) (hq : 0 < q) (hs : 0 < s)
    (hF : ∃ j : ℤ, (p : ℤ) = (q : ℤ) * j)
    (hG : ∃ j : ℤ, (r : ℤ) = (s : ℤ) * j) (hrec : s * q = p * r) : p = q := by
  obtain ⟨j, hj⟩ := hF
  obtain ⟨k, hk⟩ := hG
  have he : (q : ℤ) * (s : ℤ) = (p : ℤ) * (r : ℤ) := by exact_mod_cast (Nat.mul_comm q s).trans hrec
  have he' : ((q : ℤ) * (s : ℤ)) * 1 = ((q : ℤ) * (s : ℤ)) * (j * k) := by
    calc
      _ = (q : ℤ) * (s : ℤ) := mul_one _
      _ = (p : ℤ) * (r : ℤ) := he
      _ = _ := by rw [hj, hk]; ac_rfl
  have hjk := (mul_left_cancel₀ (mul_ne_zero (by exact_mod_cast hq.ne') (by exact_mod_cast hs.ne')) he').symm
  rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hjk with h | h
  · have he : (p : ℤ) = (q : ℤ) := by simpa only [h.1, mul_one] using hj
    exact_mod_cast he
  · rw [h.1, mul_neg_one] at hj
    omega

end SpecialTransformations.Section8

end

section

/-! Lemma 8.4 for definable extensions of a centred ball bijection and
its inverse. Two arbitrarily close nonzero graph points force the two
positive integral slopes to be reciprocal. -/

set_option backward.isDefEq.respectTransparency false

open Filter Topology FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace SpecialTransformations.Section8

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ] [Valued (VFType (M := M)) Γ]

private theorem exists_centered_power_germ
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal} (hs : Saturated M κ)
    {S : Set M} (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (f : VFType (M := M) → VFType (M := M)) (hf : S.Definable LRV (unaryScalarGraph f))
    (hclose : ∀ r s : VFType (M := M), r ≠ 0 → s ≠ 0 →
      ∃ x : VFType (M := M), x ≠ 0 ∧ Valued.v x < Valued.v r ∧ f x ≠ 0 ∧ Valued.v (f x) < Valued.v s) :
    ∃ (p q : ℕ) (c r : VFType (M := M)), 0 < p ∧ 0 < q ∧ c ≠ 0 ∧ r ≠ 0 ∧
      ∀ x : VFType (M := M), x ≠ 0 → Valued.v x < Valued.v r →
        Valued.v (f x) ^ q = Valued.v c ^ q * Valued.v x ^ p := by
  let v : Valuation (VFType (M := M)) Γ := Valued.v
  let E := vfParameterField S
  obtain ⟨P, hP, hPzero⟩ := unary_graph_polynomial_relation hc hs hsmall f hf
  let p := MvPolynomial.map E.subtype P
  have hp : p ≠ 0 := fun h => hP
    ((MvPolynomial.map_injective E.subtype Subtype.val_injective) (h.trans (map_zero _).symm))
  obtain ⟨D, d, hd, he⟩ := mvPolynomial_has_shape p hp
  have hpoly (x : VFType (M := M)) :
      ((shapedPolynomial D d).map (Polynomial.evalRingHom x)).eval (f x) = 0 := by
    rw [← he]
    change MvPolynomial.eval ![x, f x] (MvPolynomial.map E.subtype P) = 0
    rw [MvPolynomial.eval_map]
    exact hPzero x
  have hnear (r s : VFType (M := M)) (hr : r ≠ 0) (hs : s ≠ 0) :
      ∃ x : VFType (M := M), x ≠ 0 ∧ v (x - 0) < v r ∧ v (f x) < v s := by
    obtain ⟨x, hx, hxr, _, hxs⟩ := hclose r s hr hs
    exact ⟨x, hx, by simpa only [sub_zero] using hxr, hxs⟩
  rcases scalar_eventually_zero_or_positive_power hc hv hf D d hd hpoly 0 hnear with hzero | hpower
  · obtain ⟨r, hr, hrsub⟩ := exists_nonzero_ball_subset (0 : VFType (M := M)) hzero
    obtain ⟨x, hx, hxr, hfx, _⟩ := hclose r r hr hr
    have hxball : x ∈ {y : VFType (M := M) | Valued.v (y - 0) < Valued.v r} := by
      change v (x - 0) < v r
      rwa [sub_zero]
    exact False.elim (hfx (hrsub hxball hx))
  · obtain ⟨p, q, hp, _, hq, _, u, hu, h⟩ := hpower
    letI : IsAlgClosed (VFType (M := M)) := VFAlgClosed.isAlgClosed_vfType
    obtain ⟨c, hcu⟩ := IsAlgClosed.exists_pow_nat_eq u hq
    have hc₀ : c ≠ 0 := fun h => hu (hcu.symm.trans (by rw [h, zero_pow hq.ne']))
    obtain ⟨r, hr, hrsub⟩ := exists_nonzero_ball_subset (0 : VFType (M := M)) h
    refine ⟨p, q, c, r, hp, hq, hc₀, hr, fun x hx hxr => ?_⟩
    have hxball : x ∈ {y : VFType (M := M) | Valued.v (y - 0) < Valued.v r} := by
      change v (x - 0) < v r
      rwa [sub_zero]
    have hpow := (hrsub hxball hx).2
    have hvcu : v c ^ q = v u := (map_pow v c q).symm.trans (congrArg v hcu)
    change v (f x) ^ q = v c ^ q * v x ^ p
    rw [hvcu]
    simpa only [sub_zero] using hpow

theorem definable_local_inverse_slope_one [CharZero (VFType (M := M))]
    (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    {S : Set M} (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hEP : ∀ E : Subfield (VFType (M := M)), ∃ H, E ≤ H ∧ ImmediateHenselianExtension Valued.v E H)
    (f g : VFType (M := M) → VFType (M := M))
    (hf : S.Definable LRV (unaryScalarGraph f)) (hg : S.Definable LRV (unaryScalarGraph g))
    (hzero : f 0 = 0)
    (hclose : ∀ r s : VFType (M := M), r ≠ 0 → s ≠ 0 →
      ∃ x, x ≠ 0 ∧ Valued.v x < Valued.v r ∧ f x ≠ 0 ∧ Valued.v (f x) < Valued.v s ∧ g (f x) = x) :
    ∃ c r : VFType (M := M), c ≠ 0 ∧ r ≠ 0 ∧
      ∀ x ∈ centeredBall Valued.v r, Valued.v (f x) = Valued.v c * Valued.v x := by
  let v : Valuation (VFType (M := M)) Γ := Valued.v
  obtain ⟨p, q, c, r, hp, hq, hc₀, hr, hF⟩ := exists_centered_power_germ hc hs hsmall hv f hf (by
    intro r s hr hs
    obtain ⟨x, hx, hxr, hfx, hfs, _⟩ := hclose r s hr hs
    exact ⟨x, hx, hxr, hfx, hfs⟩)
  obtain ⟨u, w, d, s, hu, hw, hd, hs₀, hG⟩ := exists_centered_power_germ hc hs hsmall hv g hg (by
    intro r s hr hs
    obtain ⟨x, hx, hxs, hfx, hfr, hInv⟩ := hclose s r hs hr
    exact ⟨f x, hfx, hfr, by rwa [hInv], by rwa [hInv]⟩)
  have hFint := definable_power_germ_slope_integral hc hκ hs hv hEP hf c r hc₀ hr hq hF
  have hGint := definable_power_germ_slope_integral hc hκ hs hv hEP hg d s hd hs₀ hw hG
  obtain ⟨x₁, hx₁, hx₁r, hfx₁, hfx₁s, hInv₁⟩ := hclose r s hr hs₀
  obtain ⟨x₂, hx₂, hx₂x₁, hfx₂, hfx₂s, hInv₂⟩ := hclose x₁ s hx₁ hs₀
  have hx₂r : v x₂ < v r := (show v x₂ < v x₁ from hx₂x₁).trans hx₁r
  have hG₁ := hG (f x₁) hfx₁ hfx₁s
  have hG₂ := hG (f x₂) hfx₂ hfx₂s
  rw [hInv₁] at hG₁
  rw [hInv₂] at hG₂
  have hrec := reciprocal_power_slopes_mul (v.ne_zero_iff.mpr hc₀) (v.ne_zero_iff.mpr hd)
    (v.ne_zero_iff.mpr hx₁) (v.ne_zero_iff.mpr hx₂) (ne_of_gt (show v x₂ < v x₁ from hx₂x₁))
    (hF x₁ hx₁ hx₁r) (hF x₂ hx₂ hx₂r) hG₁ hG₂
  have he := positive_integral_reciprocal_slope_eq_one hp hq hw hFint hGint hrec
  refine ⟨c, r, hc₀, hr, fun x hx => ?_⟩
  by_cases hx₀ : x = 0
  · rw [hx₀, hzero, map_zero, mul_zero]
  · have h := hF x hx₀ hx
    rw [he, ← mul_pow] at h
    exact (pow_left_inj₀ zero_le zero_le hq.ne').mp h

theorem lemma_8_4_canonical [CharZero (VFType (M := M))]
    (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    {S : Set M} (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hEP : ∀ E : Subfield (VFType (M := M)), ∃ H, E ≤ H ∧ ImmediateHenselianExtension Valued.v E H)
    (f g : VFType (M := M) → VFType (M := M))
    (hf : S.Definable LRV (unaryScalarGraph f)) (hg : S.Definable LRV (unaryScalarGraph g))
    (a b : VFType (M := M)) (hb : b ≠ 0)
    (hbij : Set.BijOn f (centeredBall Valued.v a) (centeredBall Valued.v b))
    (hInv : ∀ x ∈ centeredBall Valued.v a, g (f x) = x)
    (hballs : ∀ r : VFType (M := M), r ≠ 0 → ∃ s : VFType (M := M), s ≠ 0 ∧
      f '' (centeredBall Valued.v a ∩ centeredBall Valued.v r) =
        centeredBall Valued.v b ∩ centeredBall Valued.v s) :
    ∃ c r : VFType (M := M), c ≠ 0 ∧ r ≠ 0 ∧
      centeredBall Valued.v r ⊆ centeredBall Valued.v a ∧
      ∀ x ∈ centeredBall Valued.v r, Valued.v (f x) = Valued.v c * Valued.v x := by
  let v : Valuation (VFType (M := M)) Γ := Valued.v
  have hclose := centered_bijection_close_nonzero v f hb (model_valuation_nontrivial hv) hbij hballs
  have hf₀ := centered_bijection_zero v f hb hbij hballs
  obtain ⟨c, r, hc₀, hr, h⟩ := definable_local_inverse_slope_one hc hκ hs hsmall hv hEP f g hf hg hf₀ (by
    intro r s hr hs
    obtain ⟨x, hx, hxa, hxr, hfx, hfs⟩ := hclose r s hr hs
    exact ⟨x, hx, hxr, hfx, hfs, hInv x hxa⟩)
  obtain ⟨x, hx, hxa, hxr, _, _⟩ := hclose r r hr hr
  exact ⟨c, x, hc₀, hx, fun y hy => (show v y < v x from hy).trans hxa,
    fun y hy => h y ((show v y < v x from hy).trans hxr)⟩

end SpecialTransformations.Section8

end

section

/-! A definable partial VF bijection has definable zero extensions of
the map and inverse. Only the original partial graph is needed. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3

namespace SpecialTransformations.Section8

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def partialUnaryGraph (A : Set M) (f : VFType (M := M) → VFType (M := M)) : Set (Fin 2 → M) :=
  {z | z 0 ∈ A ∧ z ∈ unaryScalarGraph f}

theorem partialUnaryGraph_domain_definable {S A : Set M}
    {f : VFType (M := M) → VFType (M := M)} (hA : A ⊆ {x | iVF x})
    (hf : S.Definable LRV (partialUnaryGraph A f)) : S.Definable₁ LRV A := by
  change S.Definable LRV {z : Fin 1 → M | z 0 ∈ A}
  convert hf.image_comp (fun _ : Fin 1 => (0 : Fin 2)) using 1
  ext z
  constructor
  · intro hz
    let x : VFType (M := M) := ⟨z 0, hA hz⟩
    exact ⟨![x.val, (f x).val], ⟨hz, x, rfl, rfl⟩, funext (fun j => by fin_cases j; rfl)⟩
  · rintro ⟨w, hw, rfl⟩
    exact hw.1

theorem zero_extension_unaryGraph_definable {S A : Set M}
    {f : VFType (M := M) → VFType (M := M)} (hA : S.Definable₁ LRV A)
    (hf : S.Definable LRV (partialUnaryGraph A f)) :
    ∃ F : VFType (M := M) → VFType (M := M), S.Definable LRV (unaryScalarGraph F) ∧
      ∀ x : VFType (M := M), x.val ∈ A → F x = f x := by
  classical
  let F := fun x : VFType (M := M) => if x.val ∈ A then f x else 0
  refine ⟨F, ?_, fun x hx => if_pos hx⟩
  have hVF := ((definableAt_sort S .vf).raw_definable).preimage_comp (fun _ : Fin 1 => (0 : Fin 2))
  have hOutside := (hA.preimage_comp (fun _ : Fin 1 => (0 : Fin 2))).compl
  have hz : S.DefinableFun LRV (fun _ : Fin 2 → M => iVFZero) :=
    DefinableConstants.constant (DefinableConstants.function_symbol (L := LRV) Fn.vfZero
      Fin.elim0 (fun j => j.elim0))
  have hZero := (Set.DefinableFun.proj LRV (i := (1 : Fin 2))).ofPred_eq hz
  convert hf.union (hVF.inter (hOutside.inter hZero)) using 1
  ext z
  constructor
  · rintro ⟨x, hx, hy⟩
    by_cases h : x.val ∈ A
    · exact Or.inl ⟨hx ▸ h, x, hx, (congrArg Subtype.val (if_pos h)).symm.trans hy⟩
    · refine Or.inr ⟨?_, ?_, hy.symm.trans (congrArg Subtype.val (if_neg h))⟩
      · change iVF (z 0)
        exact hx ▸ x.property
      · change z 0 ∉ A
        exact hx ▸ h
  · rintro (⟨ha, x, hx, hy⟩ | ⟨hv, ha, hzero⟩)
    · exact ⟨x, hx, (congrArg Subtype.val (if_pos (hx.symm ▸ ha))).trans hy⟩
    · let x : VFType (M := M) := ⟨z 0, hv⟩
      exact ⟨x, rfl, (congrArg Subtype.val (if_neg ha)).trans hzero.symm⟩

theorem unaryPartialBijection_definable_extensions {S A B : Set M}
    {f : VFType (M := M) → VFType (M := M)} (hA : A ⊆ {x | iVF x}) (hB : B ⊆ {x | iVF x})
    (hbij : Set.BijOn f {x | x.val ∈ A} {y | y.val ∈ B})
    (hf : S.Definable LRV (partialUnaryGraph A f)) :
    ∃ F G : VFType (M := M) → VFType (M := M),
      S.Definable LRV (unaryScalarGraph F) ∧ S.Definable LRV (unaryScalarGraph G) ∧
      ∀ x : VFType (M := M), x.val ∈ A → F x = f x ∧ G (F x) = x := by
  classical
  let g (y : VFType (M := M)) : VFType (M := M) :=
    if hy : y.val ∈ B then Classical.choose (hbij.2.2 hy) else 0
  have hg (y : VFType (M := M)) (hy : y.val ∈ B) :
      (g y).val ∈ A ∧ f (g y) = y := by
    dsimp only [g]
    rw [dif_pos hy]
    exact Classical.choose_spec (hbij.2.2 hy)
  have hgf (x : VFType (M := M)) (hx : x.val ∈ A) : g (f x) = x :=
    hbij.2.1 (hg (f x) (hbij.1 hx)).1 hx (hg (f x) (hbij.1 hx)).2
  have hgDef : S.Definable LRV (partialUnaryGraph B g) := by
    let e : Fin 2 → Fin 2 := ![1, 0]
    convert hf.preimage_comp e using 1
    ext z
    change (z 0 ∈ B ∧ z ∈ unaryScalarGraph g) ↔ z 1 ∈ A ∧ z ∘ e ∈ unaryScalarGraph f
    constructor
    · rintro ⟨hy, y, he, hgy⟩
      have hY : y.val ∈ B := he.symm ▸ hy
      exact ⟨hgy ▸ (hg y hY).1, g y, hgy, (congrArg Subtype.val (hg y hY).2).trans he⟩
    · rintro ⟨hx, x, he, hfx⟩
      have hX : x.val ∈ A := he.symm ▸ hx
      change (f x).val = z 0 at hfx
      exact ⟨hfx ▸ hbij.1 hX, f x, hfx, (congrArg Subtype.val (hgf x hX)).trans he⟩
  obtain ⟨F, hF, hFagree⟩ := zero_extension_unaryGraph_definable
    (partialUnaryGraph_domain_definable hA hf) hf
  obtain ⟨G, hG, hGagree⟩ := zero_extension_unaryGraph_definable
    (partialUnaryGraph_domain_definable hB hgDef) hgDef
  refine ⟨F, G, hF, hG, fun x hx => ⟨hFagree x hx, ?_⟩⟩
  rw [hFagree x hx, hGagree (f x) (hbij.1 hx)]
  exact hgf x hx

end SpecialTransformations.Section8

end

section

/-! State the two slope lemmas on their original partial graphs. The
definable zero extensions and inverse are internal to the proofs. -/

set_option backward.isDefEq.respectTransparency false

open Filter Topology FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace SpecialTransformations.Section8

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ] [Valued (VFType (M := M)) Γ]

theorem lemma_8_4_partial [CharZero (VFType (M := M))]
    (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    {S : Set M} (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hEP : ∀ E : Subfield (VFType (M := M)), ∃ H, E ≤ H ∧ ImmediateHenselianExtension Valued.v E H)
    (f : VFType (M := M) → VFType (M := M)) (a b : VFType (M := M)) (hb : b ≠ 0)
    (hf : S.Definable LRV (partialUnaryGraph ((fun x : VFType (M := M) => x.val) '' centeredBall Valued.v a) f))
    (hbij : Set.BijOn f (centeredBall Valued.v a) (centeredBall Valued.v b))
    (hballs : ∀ r : VFType (M := M), r ≠ 0 → ∃ s : VFType (M := M), s ≠ 0 ∧
      f '' (centeredBall Valued.v a ∩ centeredBall Valued.v r) =
        centeredBall Valued.v b ∩ centeredBall Valued.v s) :
    ∃ c r : VFType (M := M), c ≠ 0 ∧ r ≠ 0 ∧
      centeredBall Valued.v r ⊆ centeredBall Valued.v a ∧
      ∀ x ∈ centeredBall Valued.v r, Valued.v (f x) = Valued.v c * Valued.v x := by
  let v : Valuation (VFType (M := M)) Γ := Valued.v
  let A := (fun x : VFType (M := M) => x.val) '' centeredBall v a
  let B := (fun x : VFType (M := M) => x.val) '' centeredBall v b
  have hA : A ⊆ {x | iVF x} := by rintro _ ⟨x, _, rfl⟩; exact x.property
  have hB : B ⊆ {x | iVF x} := by rintro _ ⟨x, _, rfl⟩; exact x.property
  have ha (x : VFType (M := M)) : x.val ∈ A ↔ x ∈ centeredBall v a := by
    constructor
    · rintro ⟨y, hy, he⟩
      exact (Subtype.ext he : y = x) ▸ hy
    · exact fun hx => ⟨x, hx, rfl⟩
  have hb' (y : VFType (M := M)) : y.val ∈ B ↔ y ∈ centeredBall v b := by
    constructor
    · rintro ⟨x, hx, he⟩
      exact (Subtype.ext he : x = y) ▸ hx
    · exact fun hy => ⟨y, hy, rfl⟩
  have hBij : Set.BijOn f {x | x.val ∈ A} {y | y.val ∈ B} := by
    rw [show {x | x.val ∈ A} = centeredBall v a from Set.ext ha,
      show {y | y.val ∈ B} = centeredBall v b from Set.ext hb']
    exact hbij
  obtain ⟨F, G, hF, hG, hFG⟩ := unaryPartialBijection_definable_extensions hA hB hBij hf
  have hFagree (x : VFType (M := M)) (hx : x ∈ centeredBall v a) : F x = f x := (hFG x ((ha x).mpr hx)).1
  have hFbij : Set.BijOn F (centeredBall v a) (centeredBall v b) := by
    refine ⟨fun x hx => (hFagree x hx).symm ▸ hbij.1 hx, ?_, ?_⟩
    · intro x hx y hy he
      exact hbij.2.1 hx hy ((hFagree x hx).symm.trans (he.trans (hFagree y hy)))
    · intro y hy
      obtain ⟨x, hx, h⟩ := hbij.2.2 hy
      exact ⟨x, hx, (hFagree x hx).trans h⟩
  have hFballs (r : VFType (M := M)) (hr : r ≠ 0) : ∃ s : VFType (M := M), s ≠ 0 ∧
      F '' (centeredBall v a ∩ centeredBall v r) = centeredBall v b ∩ centeredBall v s := by
    obtain ⟨s, hs, h⟩ := hballs r hr
    have he : F '' (centeredBall v a ∩ centeredBall v r) =
        f '' (centeredBall v a ∩ centeredBall v r) := Set.image_congr (fun x hx => hFagree x hx.1)
    exact ⟨s, hs, he.trans h⟩
  obtain ⟨c, r, hc₀, hr, hsub, he⟩ := lemma_8_4_canonical hc hκ hs hsmall hv hEP F G hF hG a b hb
    hFbij (fun x hx => (hFG x ((ha x).mpr hx)).2) hFballs
  exact ⟨c, r, hc₀, hr, hsub, fun x hx => by simpa only [hFagree x (hsub hx)] using he x hx⟩

theorem lemma_8_4_partial_gamma_base [CharZero (VFType (M := M))]
    (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    {B : GammaParameters.Base (M := M)} (hsmall : Cardinal.mk ↥B.real < κ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hEP : ∀ E : Subfield (VFType (M := M)), ∃ H, E ≤ H ∧ ImmediateHenselianExtension Valued.v E H)
    (f : VFType (M := M) → VFType (M := M)) (a b : VFType (M := M)) (hb : b ≠ 0)
    (hf : GammaParameters.DefinableOverBase B (fun _ => .vf)
      (partialUnaryGraph ((fun x : VFType (M := M) => x.val) '' centeredBall Valued.v a) f))
    (hbij : Set.BijOn f (centeredBall Valued.v a) (centeredBall Valued.v b))
    (hballs : ∀ r : VFType (M := M), r ≠ 0 → ∃ s : VFType (M := M), s ≠ 0 ∧
      f '' (centeredBall Valued.v a ∩ centeredBall Valued.v r) =
        centeredBall Valued.v b ∩ centeredBall Valued.v s) :
    ∃ c r : VFType (M := M), c ≠ 0 ∧ r ≠ 0 ∧
      centeredBall Valued.v r ⊆ centeredBall Valued.v a ∧
      ∀ x ∈ centeredBall Valued.v r, Valued.v (f x) = Valued.v c * Valued.v x := by
  obtain ⟨_, t, ht⟩ := hf.specialize
  exact lemma_8_4_partial hc hκ hs (small_union_range hκ B.real hsmall (GammaParameters.rawTuple t))
    hv hEP f a b hb ht.raw_definable hbij hballs

end SpecialTransformations.Section8

end
