import Mathlib

/-!
# The `RV` sort of an algebraically closed valued field

This file builds, for a Mathlib `Valuation K Γ₀`, the Basarab–Kuhlmann `RV` sort of a valued
field as it is used in Yin's proof of quantifier elimination for `ACVF`
(`arXiv:1006.1390` / `arXiv:1006.2467`, §3): the multiplicative part is
`RV× = Kˣ / (1 + 𝔪)` with a point at infinity adjoined, and `rv : K → RV` is the quotient map,
`rv 0 = ∞`. The value map `vrv : RV → Γ₀` is induced by `v` and satisfies `vv = vrv ∘ rv`.

The results below are the structural facts about the `RV` sort that the lifting lemmas 3.2–3.8
of `qe.tex` rest on (the `RV`-form of "only the leading term matters", and the henselian lifting
step), together with the two facts about `rv` and the valuation ring that the axioms of `ACVF`
demand:

* `rv_eq_iff` — `rv` is the **leading-term map**: `rv x = rv y ↔ v (x - y) < v x`.
* `rv_mul` — `rv` is multiplicative.
* `rv_add_of_lt`, `rv_sum_eq_of_lt`, `rv_poly_eval_eq_of_lt` — `rv` of a sum, of a finite sum
  and of a polynomial evaluation is the `rv` of the **strictly leading term** (the "`rv` sees
  only the leading term" principle, used throughout §3).
* `vrv_rv`, `vrv_mul` — `vv = vrv ∘ rv` and `vrv` is a monoid homomorphism with zero, i.e. the
  bottom row of the defining diagram of the `RV` sort (axiom 6 of `ACVF`).
* `exists_root_of_eval_lt_one` — **Hensel lifting** over an algebraically closed valued field:
  a monic polynomial that vanishes modulo `𝔪` at `a₀` has a root congruent to `a₀` modulo `𝔪`;
  `exists_root_rv_eq` states that the root can be taken with the same leading term
  `rv b = rv a₀` when `a₀` is a unit. This is the step "since `(VF(Ŝ), 𝒪(Ŝ))` is henselian"
  in the proof of Lemma 3.4 of `qe.tex`, and it is *not* in Mathlib.
* `instHenselianLocalRing` — consequently the valuation ring `𝒪 = v.valuationSubring` of an
  algebraically closed valued field is a `HenselianLocalRing`.
* `v_add_lt_iff` — cancellation is exactly agreement of leading terms up to sign:
  `v (x + y) < v x ↔ v y = v x ∧ rv y = rv (-x)`.
* `mem_valuationSubring_iff_vrv` — the valuation ring is `rv⁻¹(RV^{≥ 1})`, as in axiom 6.
* `residueFieldUnitsEquivKernel` — `κ^× ≃* ker vrv`, where `κ` is Mathlib's residue field of
  the valuation ring: the exact sequence `1 → κ^× → RV× → Γ → 1` inside the `RV` sort, i.e.
  axioms 4 and 5 of `ACVF` (`κ^×` is the class of `1`).

Everything is proved; there is no `sorry`, and no new axiom.  The axioms used are printed at
the end of the file.
-/

open Polynomial

namespace RVCalc

variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]

section LeadingTerm

variable (v : Valuation K Γ₀)

/-- `1 + 𝔪`, the group of principal units of the valuation ring of `v`. -/
def principalUnits : Subgroup Kˣ where
  carrier := {u | v ((u : K) - 1) < 1}
  mul_mem' := by
    intro a b ha hb
    have hb1 : v ((b : K)) = 1 := by
      have h : (b : K) = (b - 1) + 1 := by ring
      rw [h, Valuation.map_add_eq_of_lt_right v (by simpa using hb), Valuation.map_one]
    have hkey : ((a : K) * (b : K) - 1) = ((a : K) - 1) * (b : K) + ((b : K) - 1) := by
      ring
    show v (((a : K) * (b : K)) - 1) < 1
    rw [hkey]
    refine lt_of_le_of_lt (v.map_add _ _) (max_lt ?_ hb)
    rw [map_mul, hb1, mul_one]
    exact ha
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    have ha1 : v ((a : K)) = 1 := by
      have h : (a : K) = (a - 1) + 1 := by ring
      rw [h, Valuation.map_add_eq_of_lt_right v (by simpa using ha), Valuation.map_one]
    have hsub : (((a⁻¹ : Kˣ) : K)) - 1 = -((a : K) - 1) / (a : K) := by
      simp only [Units.val_inv_eq_inv_val]
      field_simp
      ring
    show v ((((a⁻¹ : Kˣ) : K)) - 1) < 1
    rw [hsub, Valuation.map_div v, Valuation.map_neg v, ha1, div_one]
    exact ha

@[simp] theorem mem_principalUnits {u : Kˣ} :
    u ∈ principalUnits v ↔ v ((u : K) - 1) < 1 := Iff.rfl

/-- `RV× = Kˣ/(1+𝔪)`, the multiplicative part of the `RV` sort. -/
abbrev RVUnit : Type _ := Kˣ ⧸ principalUnits v

/-- The `RV` sort `RV× ∪ {∞}`; `none` is `∞ = rv 0`. -/
abbrev RV : Type _ := Option (RVUnit v)

/-- The quotient map `rv : K → RV`, with `rv 0 = ∞`. -/
noncomputable def rv (x : K) : RV v := by
  classical
  exact if h : x = 0 then none else some (QuotientGroup.mk' (principalUnits v) (Units.mk0 x h))

variable {v}

@[simp] theorem rv_zero : rv v 0 = none := by
  rw [rv]; exact dif_pos rfl

theorem rv_of_ne {x : K} (h : x ≠ 0) :
    rv v x = some (QuotientGroup.mk' (principalUnits v) (Units.mk0 x h)) := by
  rw [rv]; exact dif_neg h

theorem rv_eq_none_iff {x : K} : rv v x = none ↔ x = 0 := by
  rw [rv]
  split_ifs with h
  · simp [h]
  · simp [h]

theorem rv_ne_none {x : K} (h : x ≠ 0) : rv v x ≠ none := fun hc => h (rv_eq_none_iff.1 hc)


/-- `rv` is surjective onto `RV×`: every leading term has a field representative. -/
theorem rv_surjective (v : Valuation K Γ₀) (t : RVUnit v) :
    ∃ x : K, x ≠ 0 ∧ rv v x = some t := by
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (principalUnits v) t
  refine ⟨(u : K), Units.ne_zero u, ?_⟩
  rw [rv_of_ne (v := v) (Units.ne_zero u),
    show Units.mk0 (u : K) (Units.ne_zero u) = u from Units.ext rfl]


/-- `rv` is a group homomorphism on units: `rv (x⁻¹) = (rv x)⁻¹`. -/
theorem rv_inv {x : K} (hx : x ≠ 0) :
    rv v x⁻¹ = some (QuotientGroup.mk' (principalUnits v) (Units.mk0 x hx))⁻¹ := by
  have hunit : Units.mk0 x⁻¹ (inv_ne_zero hx) = (Units.mk0 x hx)⁻¹ := by
    ext
    rw [Units.val_inv_eq_inv_val, Units.val_mk0, Units.val_mk0]
  rw [rv_of_ne (inv_ne_zero hx), hunit, map_inv]

/-- Multiplication of the `RV` sort, with `∞` absorbing. -/
def rvMul (v : Valuation K Γ₀) : RV v → RV v → RV v
  | none, _ => none
  | some _, none => none
  | some a, some b => some (a * b)

@[simp] theorem rvMul_none_left (t : RV v) : rvMul v none t = none := by cases t <;> rfl

@[simp] theorem rvMul_none_right (t : RV v) : rvMul v t none = none := by cases t <;> rfl

@[simp] theorem rvMul_some (a b : RVUnit v) : rvMul v (some a) (some b) = some (a * b) := rfl

/-- `rv` is multiplicative. -/
theorem rv_mul {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    rv v (x * y) = rvMul v (rv v x) (rv v y) := by
  rw [rv_of_ne (mul_ne_zero hx hy), rv_of_ne hx, rv_of_ne hy, rvMul_some, ← map_mul]
  congr 2
  ext
  rfl

/-- The fibres of `rv` are the classes modulo `1 + 𝔪`: `rv` is the leading-term map. -/
theorem rv_eq_iff {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    rv v x = rv v y ↔ v (x - y) < v x := by
  have hxpos : 0 < v x := zero_lt_iff.2 ((Valuation.ne_zero_iff v).2 hx)
  rw [rv_of_ne hx, rv_of_ne hy, Option.some.injEq,
    QuotientGroup.mk'_eq_mk' (N := principalUnits v)]
  constructor
  · rintro ⟨z, hz, hzy⟩
    have hz' : v ((z : K) - 1) < 1 := hz
    have h1 : x * (z : K) = y := by
      simpa using congrArg Units.val hzy
    have hzx : (z : K) = y / x := by
      rw [eq_div_iff hx, mul_comm]
      exact h1
    have h2 : v (y / x - 1) < 1 := by rw [← hzx]; exact hz'
    calc v (x - y) = v (x * (1 - y / x)) := by
            rw [mul_sub, mul_one, mul_div_cancel₀ y hx]
      _ = v x * v (1 - y / x) := map_mul ..
      _ = v x * v (y / x - 1) := by
            rw [show 1 - y / x = -((y / x) - 1) by ring, Valuation.map_neg v]
      _ < v x * 1 := mul_lt_mul_of_pos_left h2 hxpos
      _ = v x := mul_one _
  · intro h
    refine ⟨(Units.mk0 x hx)⁻¹ * Units.mk0 y hy, ?_, ?_⟩
    · rw [mem_principalUnits]
      have hzK : (((Units.mk0 x hx)⁻¹ * Units.mk0 y hy : Kˣ) : K) = y / x := by
        simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0]
        ring
      rw [hzK, show y / x - 1 = (y - x) / x by field_simp,
        Valuation.map_div v, show y - x = -(x - y) by ring, Valuation.map_neg v,
        div_lt_one₀ hxpos]
      exact h
    · simp

/-- `rv` of a sum is the `rv` of its leading term. -/
theorem rv_add_of_lt {x y : K} (h : v y < v x) : rv v (x + y) = rv v x := by
  have hxpos : 0 < v x := lt_of_le_of_lt zero_le h
  have hx : x ≠ 0 := fun hc => by
    rw [hc, Valuation.map_zero] at hxpos; exact lt_irrefl 0 hxpos
  have hsum : v (x + y) = v x := Valuation.map_add_eq_of_lt_left v h
  have hxy : x + y ≠ 0 := fun hc => by
    rw [hc, Valuation.map_zero] at hsum; rw [hsum] at hxpos; exact lt_irrefl _ hxpos
  refine (rv_eq_iff hxy hx).2 ?_
  rw [add_sub_cancel_left, hsum]
  exact h

/-- `rv` of a difference is the `rv` of its leading term. -/
theorem rv_sub_of_lt {x y : K} (h : v y < v x) : rv v (x - y) = rv v x := by
  have h' : v (-y) < v x := by rwa [Valuation.map_neg v]
  rw [sub_eq_add_neg]
  exact rv_add_of_lt h'


/-- **Cancellation is agreement of leading terms, up to sign.**  For `x, y ≠ 0`,
`v (x + y) < v x` holds exactly when `x` and `y` have the same value and `y` has the same
leading term as `-x`.  This is the `rv`-form of the "no cancellation unless the leading terms
cancel" principle that drives the Newton-polygon analysis of Lemma 3.2 of `qe.tex`. -/
theorem v_add_lt_iff {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    v (x + y) < v x ↔ v y = v x ∧ rv v y = rv v (-x) := by
  constructor
  · intro h
    have hxle : v y ≤ v x := by
      by_contra hlt
      have hlt' : v x < v y := not_le.1 hlt
      rw [Valuation.map_add_eq_of_lt_right v hlt'] at h
      exact absurd h (not_lt.2 (le_of_lt hlt'))
    have hvy : v y = v x := by
      rcases lt_or_eq_of_le hxle with h' | h'
      · rw [Valuation.map_add_eq_of_lt_left v h'] at h
        exact absurd h (lt_irrefl _)
      · exact h'
    refine ⟨hvy, ?_⟩
    have h' : v (x + y) < v (-x) := by rwa [Valuation.map_neg v]
    have h2 := rv_add_of_lt (v := v) (x := -x) (y := x + y) h'
    rwa [show -x + (x + y) = y by ring] at h2
  · rintro ⟨hvy, hrv⟩
    have hneg : -x ≠ 0 := neg_ne_zero.2 hx
    have h' := (rv_eq_iff hy hneg).1 hrv
    rw [sub_neg_eq_add] at h'
    rwa [add_comm, hvy] at h'

/-- `rv` of a finite sum whose terms are all strictly smaller in value than one term. -/
theorem rv_sum_eq_of_lt {ι : Type*} [DecidableEq ι] {s : Finset ι} {f : ι → K} {j : ι}
    (hj : j ∈ s) (h0 : v (f j) ≠ 0) (hf : ∀ i ∈ s \ {j}, v (f i) < v (f j)) :
    rv v (∑ i ∈ s, f i) = rv v (f j) := by
  have hfj : f j ≠ 0 := by rintro h; rw [h, Valuation.map_zero] at h0; exact h0 rfl
  have hval : v (∑ i ∈ s, f i) = v (f j) := Valuation.map_sum_eq_of_lt v hj hf
  have hne : (∑ i ∈ s, f i) ≠ 0 := by
    rintro h; rw [h, Valuation.map_zero] at hval; exact h0 hval.symm
  refine (rv_eq_iff hne hfj).2 ?_
  rw [hval, Finset.sum_eq_add_sum_sdiff_singleton_of_mem hj, add_sub_cancel_left]
  exact Valuation.map_sum_lt v h0 hf


/-- The polynomial form of `rv_sum_eq_of_lt`: if the `j`-th term of `∑_{i ≤ n} aᵢ bⁱ`
strictly dominates all others in value, then the `rv` of the value of the polynomial is the
`rv` of that term. -/
theorem rv_poly_eval_eq_of_lt (v : Valuation K Γ₀) {n : ℕ} {a : ℕ → K} {b : K} {j : ℕ}
    (hj : j ≤ n) (h0 : v (a j * b ^ j) ≠ 0)
    (hf : ∀ i ≤ n, i ≠ j → v (a i * b ^ i) < v (a j * b ^ j)) :
    rv v (∑ i ∈ Finset.range (n + 1), a i * b ^ i) = rv v (a j * b ^ j) := by
  refine rv_sum_eq_of_lt (s := Finset.range (n + 1)) (f := fun i => a i * b ^ i) ?_ h0 ?_
  · simp [hj]
  · intro i hi
    rw [Finset.mem_sdiff, Finset.mem_singleton] at hi
    exact hf i (by simpa using hi.1) hi.2

end LeadingTerm

/-- A product of elements `≥ 1` in `Γ₀` is `≥ 1`. -/
theorem one_le_multiset_prod {s : Multiset Γ₀} (h : ∀ a ∈ s, 1 ≤ a) : 1 ≤ s.prod := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a t ih =>
      rw [Multiset.prod_cons]
      exact one_le_mul (h a (by simp)) (ih fun b hb => h b (by simp [hb]))

/-- **Hensel lifting over an algebraically closed valued field.**
A monic polynomial that has a root modulo the maximal ideal has a genuine root which is
congruent to it modulo the maximal ideal. -/
theorem exists_root_of_eval_lt_one [IsAlgClosed K] (v : Valuation K Γ₀) {f : K[X]}
    (hf : f.Monic) {a₀ : K} (h : v (f.eval a₀) < 1) :
    ∃ b : K, f.IsRoot b ∧ v (a₀ - b) < 1 := by
  obtain ⟨m, hm⟩ := Polynomial.splits_iff_exists_multiset.1 (IsAlgClosed.splits f)
  rw [hf.leadingCoeff, map_one, one_mul] at hm
  have hev : ∀ c : K, f.eval c = (m.map fun r => c - r).prod := by
    intro c
    rw [hm, Polynomial.eval_multiset_prod]
    simp [Multiset.map_map, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  have hex : ∃ r ∈ m, v (a₀ - r) < 1 := by
    by_contra hc
    have hc' : ∀ r ∈ m, 1 ≤ v (a₀ - r) := by
      intro r hr
      by_contra h1
      exact hc ⟨r, hr, not_le.1 h1⟩
    have h1 : 1 ≤ (m.map fun r => v (a₀ - r)).prod := by
      refine one_le_multiset_prod ?_
      intro a ha
      obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.1 ha
      exact hc' r hr
    have h2 : v (f.eval a₀) = (m.map fun r => v (a₀ - r)).prod := by
      rw [hev a₀, map_multiset_prod]
      simp [Multiset.map_map]
    rw [h2] at h
    exact absurd h (not_lt.2 h1)
  obtain ⟨r, hr, hrv⟩ := hex
  refine ⟨r, ?_, hrv⟩
  rw [Polynomial.IsRoot.def, hev r]
  refine Multiset.prod_eq_zero_iff.2 ?_
  have := Multiset.mem_map_of_mem (f := fun r' => r - r') hr
  simpa using this


section ValueMap

variable (v : Valuation K Γ₀)

theorem val_eq_one_of_mem_principalUnits {u : Kˣ} (hu : u ∈ principalUnits v) :
    v ((u : K)) = 1 := by
  have h : (u : K) = ((u : K) - 1) + 1 := by ring
  rw [h, Valuation.map_add_eq_of_lt_right v (by simpa using hu), Valuation.map_one]

/-- The valuation of a unit, as a monoid homomorphism to `Γ₀`. -/
def vrvUnitHom : Kˣ →* Γ₀ :=
  (Units.coeHom Γ₀).comp (Units.map v.toMonoidWithZeroHom.toMonoidHom)

theorem vrvUnitHom_apply (u : Kˣ) : vrvUnitHom v u = v (u : K) := by
  rw [vrvUnitHom, MonoidHom.comp_apply, Units.coeHom_apply, Units.coe_map]
  rfl

/-- `vrv : RV× → Γ`, the value of a leading term: well defined because `v` is constant on
classes modulo `1 + 𝔪`. -/
def vrvUnit : RVUnit v →* Γ₀ :=
  QuotientGroup.lift (principalUnits v) (vrvUnitHom v) (by
    intro u hu
    rw [MonoidHom.mem_ker, vrvUnitHom_apply]
    exact val_eq_one_of_mem_principalUnits v hu)

theorem vrvUnit_mk (u : Kˣ) :
    vrvUnit v (QuotientGroup.mk' (principalUnits v) u) = v (u : K) := by
  rw [vrvUnit]
  exact vrvUnitHom_apply v u

/-- `vrv : RV → Γ ∪ {∞}`, with `vrv ∞ = 0` (axiom 6 of `ACVF`). -/
def vrv : RV v → Γ₀
  | none => 0
  | some a => vrvUnit v a

@[simp] theorem vrv_none : vrv v (none : RV v) = 0 := rfl

@[simp] theorem vrv_some (a : RVUnit v) : vrv v (some a) = vrvUnit v a := rfl

/-- `vv = vrv ∘ rv`: the valuation of an element is the value of its leading term. -/
theorem vrv_rv (x : K) : vrv v (rv v x) = v x := by
  rw [rv]
  split_ifs with h
  · rw [h, Valuation.map_zero]; rfl
  · rw [vrv_some, vrvUnit_mk, Units.val_mk0]

theorem vrv_mul (t s : RV v) : vrv v (rvMul v t s) = vrv v t * vrv v s := by
  match t, s with
  | none, _ => simp
  | some _, none => simp
  | some a, some b => simp only [rvMul_some, vrv_some, map_mul]


/-- `rv` determines the value: the class of `x` modulo `1 + 𝔪` fixes `v x`. -/
theorem v_eq_of_rv_eq {x y : K} (h : rv v x = rv v y) (hx : x ≠ 0) (hy : y ≠ 0) : v x = v y := by
  have hlt : v (x - y) < v x := (rv_eq_iff hx hy).1 h
  have hneg : v (-(x - y)) < v x := by rwa [Valuation.map_neg v]
  have hsplit : y = x + (-(x - y)) := by ring
  rw [hsplit, Valuation.map_add_eq_of_lt_left v hneg]

/-- A representative of the kernel of `vrv` is a unit of the valuation ring. -/
theorem isUnit_of_vrv_eq_one {u : Kˣ} (h : vrv v (some (QuotientGroup.mk' (principalUnits v) u)) = 1) :
    v ((u : K)) = 1 := by
  rw [vrv_some, vrvUnit_mk] at h
  exact h

/-- The kernel of `vrv` is the image of the units of the valuation ring: the exact sequence
`1 → κ^× → RV^× → Γ → 1` of the `RV` sort. -/
theorem vrv_eq_one_iff (u : Kˣ) :
    vrv v (some (QuotientGroup.mk' (principalUnits v) u)) = 1 ↔ v ((u : K)) = 1 := by
  refine ⟨isUnit_of_vrv_eq_one v, ?_⟩
  intro h
  rw [vrv_some, vrvUnit_mk]
  exact h

/-- `vrv` is surjective onto the value group of `v`. -/
theorem vrv_surjective {γ : Γ₀} (hγ : γ ∈ Set.range v) : ∃ t : RV v, vrv v t = γ := by
  obtain ⟨x, rfl⟩ := hγ
  by_cases hx : x = 0
  · exact ⟨none, by rw [hx, Valuation.map_zero]; rfl⟩
  · exact ⟨rv v x, vrv_rv v x⟩


/-- Axiom 6 of `ACVF`: the valuation ring is `rv⁻¹(RV^{≥ 1})`. -/
theorem mem_valuationSubring_iff_vrv {x : K} :
    x ∈ v.valuationSubring ↔ vrv v (rv v x) ≤ 1 := by
  rw [Valuation.mem_valuationSubring_iff, vrv_rv]

/-- Restatement of `vrv_rv`: an element lies in `𝔪` exactly when its leading term is `< 1`. -/
theorem v_lt_one_iff_vrv {x : K} : v x < 1 ↔ vrv v (rv v x) < 1 := by
  rw [vrv_rv]

end ValueMap

section HenselRV

/-- The paper's use of Hensel's lemma (Lemma 3.4 of `qe.tex`): a monic polynomial over an
algebraically closed valued field that vanishes modulo `𝔪` at a unit `a₀` has a root with the
same leading term as `a₀`. -/
theorem exists_root_rv_eq [IsAlgClosed K] (v : Valuation K Γ₀) {f : K[X]} (hf : f.Monic)
    {a₀ : K} (h : v (f.eval a₀) < 1) (hu : v a₀ = 1) :
    ∃ b : K, f.IsRoot b ∧ rv v b = rv v a₀ := by
  obtain ⟨b, hb, hbc⟩ := exists_root_of_eval_lt_one v hf h
  have ha₀ : a₀ ≠ 0 := by rintro rfl; rw [Valuation.map_zero] at hu; exact zero_ne_one hu
  have hbv : v (b - a₀) < 1 := by
    rw [show b - a₀ = -(a₀ - b) by ring, Valuation.map_neg v]; exact hbc
  have hb1 : v b = 1 := by
    have hsplit : b = (b - a₀) + a₀ := by ring
    rw [hsplit, Valuation.map_add_eq_of_lt_right v (by rw [hu]; exact hbv), hu]
  have hb0 : b ≠ 0 := by rintro rfl; rw [Valuation.map_zero] at hb1; exact zero_ne_one hb1
  refine ⟨b, hb, (rv_eq_iff hb0 ha₀).2 ?_⟩
  rw [hb1]
  exact hbv

end HenselRV

variable (v : Valuation K Γ₀)

/-- The valuation ring of an algebraically closed valued field is a Henselian local ring. -/
instance instHenselianLocalRing [IsAlgClosed K] : HenselianLocalRing ↥(v.valuationSubring) where
  is_henselian := by
    intro f hf a₀ ha₀ hunit
    classical
    set F : K[X] := f.map (v.valuationSubring).subtype with hF
    have hFmonic : F.Monic := hf.map _
    have hev : ∀ a : ↥(v.valuationSubring),
        F.eval (a : K) = ((f.eval a : ↥(v.valuationSubring)) : K) := by
      intro a
      rw [hF, Polynomial.eval_map]
      exact Polynomial.eval₂_at_apply _ a
    have hlt : v (F.eval ((a₀ : ↥(v.valuationSubring)) : K)) < 1 := by
      rw [hev a₀]
      exact (Valuation.mem_maximalIdeal_iff (K := K) v).1 ha₀
    obtain ⟨b, hbroot, hbclose⟩ := exists_root_of_eval_lt_one v hFmonic hlt
    have ha₀le : v ((a₀ : ↥(v.valuationSubring)) : K) ≤ 1 := a₀.2
    have hdiff : b - ((a₀ : ↥(v.valuationSubring)) : K) =
        -(((a₀ : ↥(v.valuationSubring)) : K) - b) := by ring
    have hbA : b ∈ v.valuationSubring := by
      have hsplit : b = ((a₀ : ↥(v.valuationSubring)) : K) +
          (b - ((a₀ : ↥(v.valuationSubring)) : K)) := by ring
      rw [hsplit]
      refine le_trans (v.map_add _ _) (max_le ha₀le ?_)
      rw [hdiff, Valuation.map_neg v]
      exact le_of_lt hbclose
    refine ⟨⟨b, hbA⟩, ?_, ?_⟩
    · rw [Polynomial.IsRoot.def]
      have h0 : ((f.eval ⟨b, hbA⟩ : ↥(v.valuationSubring)) : K) = 0 := by
        rw [← hev ⟨b, hbA⟩]
        rw [Polynomial.IsRoot.def] at hbroot
        exact hbroot
      exact Subtype.coe_injective (by simpa using h0)
    · rw [Valuation.mem_maximalIdeal_iff (K := K) v]
      have hcoe : (((⟨b, hbA⟩ - a₀ : ↥(v.valuationSubring))) : K) =
          b - ((a₀ : ↥(v.valuationSubring)) : K) := rfl
      rw [hcoe, hdiff, Valuation.map_neg v]
      exact hbclose


/-! ## Axiom check -/

#print axioms RVCalc.rv_eq_iff
#print axioms RVCalc.rv_add_of_lt
#print axioms RVCalc.v_add_lt_iff
#print axioms RVCalc.rv_sum_eq_of_lt
#print axioms RVCalc.rv_poly_eval_eq_of_lt
#print axioms RVCalc.rv_sub_of_lt
#print axioms RVCalc.rv_inv
#print axioms RVCalc.vrv_rv
#print axioms RVCalc.vrv_mul
#print axioms RVCalc.exists_root_of_eval_lt_one
#print axioms RVCalc.v_eq_of_rv_eq
#print axioms RVCalc.vrv_eq_one_iff
#print axioms RVCalc.mem_valuationSubring_iff_vrv
#print axioms RVCalc.vrv_surjective
#print axioms RVCalc.exists_root_rv_eq
#print axioms RVCalc.instHenselianLocalRing

section ResidueUnits

variable (v : Valuation K Γ₀)

/-- The value `v` and the valuation of the valuation ring agree on the ring itself. -/
theorem valuationSubring_valuation_lt_one_iff (a : ↥(v.valuationSubring)) :
    v.valuationSubring.valuation a < 1 ↔ v (a : K) < 1 := by
  have h1 : v.valuationSubring.valuation a < 1 ↔ ¬ IsUnit a := by
    constructor
    · intro h hu
      rw [((v.valuationSubring).valuation_eq_one_iff a).1 hu] at h
      exact lt_irrefl _ h
    · intro h
      rcases lt_or_eq_of_le ((v.valuationSubring).valuation_le_one a) with h' | h'
      · exact h'
      · exact absurd (((v.valuationSubring).valuation_eq_one_iff a).2 h') h
  rw [h1]
  exact (IsLocalRing.mem_maximalIdeal (x := a)).symm.trans
    (Valuation.mem_maximalIdeal_iff (K := K) v)

/-- The bridge for an element of the field that lies in the valuation ring. -/
theorem valuation_lt_one_iff {a : K} (ha : a ∈ v.valuationSubring) :
    v.valuationSubring.valuation a < 1 ↔ v a < 1 :=
  valuationSubring_valuation_lt_one_iff v ⟨a, ha⟩

/-- On the units of the valuation ring, the principal units of `v` are the principal units of
the valuation ring: this identifies `RV× = Kˣ/(1+𝔪)` on the two sides. -/
theorem mem_principalUnits_iff (x : v.valuationSubring.unitGroup) :
    (x : Kˣ) ∈ principalUnits v ↔
      x ∈ v.valuationSubring.principalUnitGroup.comap v.valuationSubring.unitGroup.subtype := by
  have hmem : (((x : Kˣ)) : K) - 1 ∈ v.valuationSubring := by
    rw [Valuation.mem_valuationSubring_iff, sub_eq_add_neg]
    refine Valuation.map_add_le v ?_ ?_
    · rw [show v (((x : Kˣ)) : K) = 1 from
        (Valuation.mem_unitGroup_iff (v := v) (x := (x : Kˣ))).1 x.2]
    · rw [Valuation.map_neg v, Valuation.map_one]
  rw [Subgroup.mem_comap, v.valuationSubring.mem_principalUnitGroup_iff, mem_principalUnits]
  simp only [Subgroup.coe_subtype]
  exact (valuation_lt_one_iff v hmem).symm


/-- The units of the valuation ring mapped into `RV×`. -/
noncomputable def unitGroupToRV (v : Valuation K Γ₀) : v.valuationSubring.unitGroup →* RVUnit v :=
  (QuotientGroup.mk' (principalUnits v)).comp v.valuationSubring.unitGroup.subtype

theorem unitGroupToRV_apply (x : v.valuationSubring.unitGroup) :
    unitGroupToRV v x = QuotientGroup.mk' (principalUnits v) (x : Kˣ) := rfl

theorem ker_unitGroupToRV (v : Valuation K Γ₀) : (unitGroupToRV v).ker =
    v.valuationSubring.principalUnitGroup.comap v.valuationSubring.unitGroup.subtype := by
  ext x
  rw [MonoidHom.mem_ker, unitGroupToRV_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff]
  exact mem_principalUnits_iff v x

theorem range_unitGroupToRV (v : Valuation K Γ₀) :
    (unitGroupToRV v).range = (vrvUnit v).ker := by
  ext t
  constructor
  · rintro ⟨x, rfl⟩
    rw [MonoidHom.mem_ker, unitGroupToRV_apply, vrvUnit_mk]
    exact (Valuation.mem_unitGroup_iff (v := v) (x := (x : Kˣ))).1 x.2
  · intro ht
    rw [MonoidHom.mem_ker] at ht
    obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective (principalUnits v) (t : RVUnit v)
    rw [← hu, vrvUnit_mk] at ht
    exact ⟨⟨u, (Valuation.mem_unitGroup_iff (v := v) (x := u)).2 ht⟩, hu⟩

/-- **The kernel of `vrv` is the multiplicative group of the residue field**:
`1 → κ^× → RV× → Γ → 1` inside the `RV` sort.  This identifies the `RV` sort built here with
the paper's `RV(K) = K^×/(1+𝔪)`, whose class of `1` is `κ^×` (axiom 4 of `ACVF`). -/
noncomputable def residueFieldUnitsEquivKernel (v : Valuation K Γ₀) :
    (IsLocalRing.ResidueField ↥(v.valuationSubring))ˣ ≃* (vrvUnit v).ker := by
  rw [← range_unitGroupToRV v]
  exact (v.valuationSubring.unitsModPrincipalUnitsEquivResidueFieldUnits).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq (ker_unitGroupToRV v).symm).trans
      (QuotientGroup.quotientKerEquivRange (unitGroupToRV v)))

end ResidueUnits




#print axioms RVCalc.residueFieldUnitsEquivKernel
#print axioms RVCalc.ker_unitGroupToRV

end RVCalc
