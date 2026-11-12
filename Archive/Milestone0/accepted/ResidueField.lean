module

/-
The residue-field block of the intended model of `ACVF`.

Reference: Yimu Yin, *Special transformations in algebraically closed valued fields*,
APAL 2010, arXiv:1006.2467, Definition 2.2 items 3, 6 and `ACVF(0,0)`.

The paper's `K = K^× ∪ {0}` is the residue field of the valued field `(K, v)`
(internalised inside the `RV`-sort).  This file builds the residue field of a Mathlib
valuation `v : Valuation K Γ₀` and proves the two facts about it that the axioms of
`ACVF` need and that Mathlib does not have:

* `isAlgClosed_residueField` : the residue field of an algebraically closed valued
  field is algebraically closed (axiom 3, `kAlgClosed` of the encoding);
* `charZero_residueField_iff` : when the residue field has characteristic zero
  (the residue-characteristic-zero sentences of `ACVF(0,0)`).

Only `import Mathlib`.  No `sorry`.
-/
public import Mathlib

@[expose] public section

open Polynomial

namespace ACVFResidue

variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)

/-- The residue field of the valuation ring of `v`.  This is the paper's `K`
(the field `K^× ∪ {0}` that sits inside the `RV`-sort). -/
abbrev ResidueField : Type _ := IsLocalRing.ResidueField v.valuationSubring

noncomputable instance : Field (ResidueField v) := inferInstanceAs (Field (IsLocalRing.ResidueField v.valuationSubring))

/-- A root in the fraction field of a monic-izable polynomial over the valuation ring is
integral over the valuation ring.  (Used to show that a root of a lift of a polynomial over
the residue field lies in the valuation ring.) -/
theorem isIntegral_of_isUnit_leadingCoeff {F : (v.valuationSubring)[X]}
    (hu : IsUnit F.leadingCoeff) {x : K}
    (hx : F.eval₂ (algebraMap v.valuationSubring K) x = 0) :
    IsIntegral v.valuationSubring x := by
  obtain ⟨u, hu'⟩ := hu
  refine ⟨C ((u⁻¹ : (v.valuationSubring)ˣ) : v.valuationSubring) * F,
    Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one ?_, ?_⟩
  · show ((u⁻¹ : (v.valuationSubring)ˣ) : v.valuationSubring) * F.leadingCoeff = 1
    rw [← hu', ← Units.val_mul, inv_mul_cancel, Units.val_one]
  · rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, hx, mul_zero]

/-- **A monic polynomial of positive degree over the residue field has a root.**

The lift of a monic `p` to the valuation ring `𝒪` is made monic-izable (its leading
coefficient is a unit of `𝒪`), so a root `x ∈ K` of its image in `K[X]` is integral over
`𝒪`; since `𝒪` is integrally closed in `K` (Mathlib:
`ValuationSubring.instIsIntegrallyClosed`), `x ∈ 𝒪`; then `rv x` is a root of `p`. -/
theorem exists_root_of_monic [IsAlgClosed K] (p : (ResidueField v)[X]) (hp : p.Monic)
    (hdeg : 1 ≤ p.natDegree) : ∃ y : ResidueField v, p.IsRoot y := by
  classical
  obtain ⟨G, hG⟩ := Polynomial.map_surjective (IsLocalRing.residue v.valuationSubring)
    (IsLocalRing.residue_surjective) p
  -- truncate the lift to degree at most `natDegree p`
  obtain ⟨n, hn⟩ : ∃ n, n = p.natDegree := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F : (v.valuationSubring)[X], F = G %ₘ X ^ (n + 1) := ⟨_, rfl⟩
  have hXm : (X ^ (n + 1) : (v.valuationSubring)[X]).Monic := monic_X_pow _
  have hXne : (X ^ (n + 1) : (v.valuationSubring)[X]) ≠ 1 := by
    intro h
    have h1 : (X ^ (n + 1) : (v.valuationSubring)[X]).natDegree = n + 1 := natDegree_X_pow _
    rw [h] at h1
    simp at h1
  have hpn : p.degree < (X ^ (n + 1) : (ResidueField v)[X]).degree := by
    rw [Polynomial.degree_eq_natDegree hp.ne_zero, ← hn, Polynomial.degree_X_pow]
    exact_mod_cast Nat.lt_succ_self n
  have hmapX : (X ^ (n + 1) : (v.valuationSubring)[X]).map
      (IsLocalRing.residue v.valuationSubring) = (X ^ (n + 1) : (ResidueField v)[X]) := by
    simp
  have hFmap : F.map (IsLocalRing.residue v.valuationSubring) = p := by
    rw [hF, Polynomial.map_modByMonic _ hXm, hG, hmapX]
    exact (Polynomial.modByMonic_eq_self_iff (monic_X_pow (n + 1))).mpr hpn
  have hFle : F.natDegree ≤ n := by
    have h := Polynomial.natDegree_modByMonic_lt G hXm hXne
    rw [natDegree_X_pow] at h
    rw [hF]; omega
  have hFcoeff : IsLocalRing.residue v.valuationSubring (F.coeff n) = 1 := by
    have h : (F.map (IsLocalRing.residue v.valuationSubring)).coeff n = p.coeff n := by rw [hFmap]
    rw [Polynomial.coeff_map] at h
    rw [h, hn, hp.coeff_natDegree]
  have hFnat : F.natDegree = n := by
    refine le_antisymm hFle (by_contra fun h => ?_)
    rw [not_le] at h
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt h, map_zero] at hFcoeff
    exact zero_ne_one hFcoeff
  have hlc : F.leadingCoeff = F.coeff n := by rw [Polynomial.leadingCoeff, hFnat]
  have hunit : IsUnit F.leadingCoeff := by
    rw [← IsLocalRing.notMem_maximalIdeal]
    intro hmem
    have hzero : IsLocalRing.residue v.valuationSubring F.leadingCoeff = 0 :=
      (IsLocalRing.residue_eq_zero_iff _).mpr hmem
    rw [hlc, hFcoeff] at hzero
    exact one_ne_zero hzero
  have hF0 : F ≠ 0 := fun h => by
    rw [h, Polynomial.leadingCoeff_zero] at hunit
    exact not_isUnit_zero hunit
  -- a root of the image of `F` in `K[X]`
  have hKnat : (F.map (algebraMap v.valuationSubring K)).natDegree = n := by
    rw [Polynomial.natDegree_map_eq_of_injective (FaithfulSMul.algebraMap_injective (v.valuationSubring) K), hFnat]
  have hn0 : n ≠ 0 := by omega
  have hKne : F.map (algebraMap v.valuationSubring K) ≠ 0 := by
    intro h
    rw [h] at hKnat
    simp at hKnat
    omega
  have hKdeg : (F.map (algebraMap v.valuationSubring K)).degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hKne, hKnat]
    exact_mod_cast hn0
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (F.map (algebraMap v.valuationSubring K)) hKdeg
  have hxev : F.eval₂ (algebraMap v.valuationSubring K) x = 0 := by
    rw [← hx, Polynomial.eval_map]
  obtain ⟨y, hy⟩ := (IsIntegrallyClosedIn.isIntegral_iff (R := v.valuationSubring) (A := K)).mp
    (isIntegral_of_isUnit_leadingCoeff v hunit hxev)
  refine ⟨IsLocalRing.residue v.valuationSubring y, ?_⟩
  rw [Polynomial.IsRoot.def, ← hFmap, Polynomial.eval_map]
  have hFeval : F.eval y = 0 := by
    have h := hxev
    rw [← hy] at h
    rw [Polynomial.eval₂_at_apply] at h
    exact (FaithfulSMul.algebraMap_injective (v.valuationSubring) K) (by rw [h, map_zero])
  rw [Polynomial.eval₂_at_apply, hFeval, map_zero]

/-- **Axiom 3 of Definition 2.2**: the residue field of an algebraically closed valued
field is algebraically closed. -/
theorem isAlgClosed_residueField [IsAlgClosed K] : IsAlgClosed (ResidueField v) :=
  IsAlgClosed.of_exists_root _ fun p hp hpirr =>
    exists_root_of_monic v p hp hpirr.natDegree_pos

/-- A natural number is zero in the residue field exactly when it is zero, provided the
valuation is `≥ 1` on the positive integers (i.e. provided the residue field has
characteristic `0`). -/
theorem natCast_eq_zero_iff (h : ∀ n : ℕ, n ≠ 0 → (1 : Γ₀) ≤ v (n : K)) (n : ℕ) :
    (n : ResidueField v) = 0 ↔ n = 0 := by
  constructor
  · intro hzero
    by_contra hn
    have hlt : v (n : K) < 1 := by
      have hres : IsLocalRing.residue v.valuationSubring (n : v.valuationSubring) = 0 := by
        rw [map_natCast]
        exact hzero
      have hmem := (IsLocalRing.residue_eq_zero_iff _).mp hres
      rw [Valuation.mem_maximalIdeal_iff] at hmem
      simpa using hmem
    exact absurd (h n hn) (not_le.mpr hlt)
  · rintro rfl
    simp

/-- **Residue characteristic zero.**  The residue field of `v` has characteristic zero iff
every positive integer has valuation `1`, i.e. iff every positive integer is a unit of the
valuation ring.  (This is an extra hypothesis on `v`: it fails for the `p`-adic valuation on
`ℚ` and holds for the trivial valuation, where the residue field *is* `K`.) -/
theorem charZero_residueField_iff :
    CharZero (ResidueField v) ↔ ∀ n : ℕ, n ≠ 0 → (1 : Γ₀) ≤ v (n : K) := by
  constructor
  · intro hc n hn
    by_contra h
    have hlt : v (n : K) < 1 := lt_of_not_ge h
    have hmem : (n : v.valuationSubring) ∈ IsLocalRing.maximalIdeal v.valuationSubring := by
      rw [Valuation.mem_maximalIdeal_iff]
      simpa using hlt
    have hres : IsLocalRing.residue v.valuationSubring (n : v.valuationSubring) = 0 :=
      (IsLocalRing.residue_eq_zero_iff _).mpr hmem
    rw [map_natCast] at hres
    exact hn (hc.cast_injective (by simpa using hres))
  · intro h
    refine ⟨fun a b hab => ?_⟩
    rcases le_total a b with hle | hle
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
      have hk : (k : ResidueField v) = 0 := by
        have h2 : (a : ResidueField v) + (k : ResidueField v) = (a : ResidueField v) + 0 := by
          rw [← Nat.cast_add, ← hab]
          simp
        exact add_left_cancel h2
      have hk0 : k = 0 := (natCast_eq_zero_iff v h k).mp hk
      omega
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
      have hk : (k : ResidueField v) = 0 := by
        have h2 : (b : ResidueField v) + (k : ResidueField v) = (b : ResidueField v) + 0 := by
          rw [← Nat.cast_add, hab]
          simp
        exact add_left_cancel h2
      have hk0 : k = 0 := (natCast_eq_zero_iff v h k).mp hk
      omega

section Bridge

/-- `RV^× = Kˣ / (1 + 𝔪)`, exactly as in `Milestone0/RVModel.lean` (repeated here because a
deliverable of this swarm must be a single file with `import Mathlib` as its only import). -/
abbrev RVUnit : Type _ := Kˣ ⧸ v.valuationSubring.principalUnitGroup

/-- The valuation, as a monoid homomorphism on the units of `K`. -/
noncomputable def vUnits : Kˣ →* Γ₀ˣ where
  toFun u := Units.mk0 (v (u : K)) (by rw [Valuation.ne_zero_iff]; exact Units.ne_zero u)
  map_one' := by ext; simp
  map_mul' a b := by ext; simp [Valuation.map_mul]

/-- `vrv` restricted to the group part of the `RV`-sort: the quotient map
`RV^× = Kˣ/(1+𝔪) → Γ`. -/
noncomputable def vrvUnit : RVUnit v →* Γ₀ˣ :=
  QuotientGroup.lift _ (vUnits v) (by
    intro x hx
    rw [MonoidHom.mem_ker, Units.ext_iff]
    exact (Valuation.mem_unitGroup_iff K v x).1 (v.valuationSubring.principal_units_le_units hx))

/-- The paper's `K^×` as a subgroup of `RV^×`: the equivalence class of `1`, i.e. `ker vrv`.
(Axiom 4 of Definition 2.2: `K^× = {x ∈ RV : vrv x = 1}`.) -/
noncomputable def kUnitsSubgroup : Subgroup (RVUnit v) := MonoidHom.ker (vrvUnit v)

abbrev KUnits : Type _ := kUnitsSubgroup v

/-- The units of the valuation ring, mapped to `K^× ⊂ RV^×`. -/
noncomputable def unitGroupToKUnits : v.valuationSubring.unitGroup →* KUnits v where
  toFun u := ⟨QuotientGroup.mk' v.valuationSubring.principalUnitGroup (u : Kˣ), by
    change vrvUnit v (QuotientGroup.mk' v.valuationSubring.principalUnitGroup (u : Kˣ)) = 1
    refine Units.ext ?_
    show v ((u : Kˣ) : K) = 1
    exact (Valuation.mem_unitGroup_iff K v (u : Kˣ)).1 u.2⟩
  map_one' := by ext; simp
  map_mul' a b := by ext; simp

theorem unitGroupToKUnits_ker :
    (unitGroupToKUnits v).ker =
      v.valuationSubring.principalUnitGroup.comap v.valuationSubring.unitGroup.subtype := by
  ext u
  rw [MonoidHom.mem_ker, Subgroup.mem_comap]
  constructor
  · intro h
    have h1 : (QuotientGroup.mk' v.valuationSubring.principalUnitGroup (u : Kˣ)) = 1 :=
      congrArg Subtype.val h
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact h1
  · intro h
    have h1 : (QuotientGroup.mk' v.valuationSubring.principalUnitGroup (u : Kˣ)) = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact h
    exact Subtype.ext h1

theorem unitGroupToKUnits_surjective : Function.Surjective (unitGroupToKUnits v) := by
  rintro ⟨q, hq⟩
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective v.valuationSubring.principalUnitGroup q
  have hu : u ∈ v.valuationSubring.unitGroup := by
    rw [Valuation.mem_unitGroup_iff]
    have h := congrArg (fun x : Γ₀ˣ => (x : Γ₀)) hq
    simpa [vrvUnit, vUnits] using h
  exact ⟨⟨u, hu⟩, Subtype.ext rfl⟩

/-- **`K^×` is the residue field's unit group**: the units of the valuation ring modulo the
principal units agree with `ker vrv`. -/
noncomputable def unitsQuotEquivKUnits :
    (v.valuationSubring.unitGroup ⧸
        v.valuationSubring.principalUnitGroup.comap v.valuationSubring.unitGroup.subtype) ≃*
      KUnits v :=
  (QuotientGroup.quotientMulEquivOfEq (unitGroupToKUnits_ker v).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (unitGroupToKUnits v)
      (unitGroupToKUnits_surjective v))

/-- **The units of the internal residue field `K^× ⊂ RV` are the residue field's units**,
i.e. `RV^× ∩ ker vrv ≅ k^×` (`(𝒪 ∖ 𝔪)/(1+𝔪) ≅ k^×` of the paper). -/
noncomputable def kUnitsEquivResidueUnits : KUnits v ≃* (ResidueField v)ˣ :=
  (unitsQuotEquivKUnits v).symm.trans
    v.valuationSubring.unitsModPrincipalUnitsEquivResidueFieldUnits

/-- The internal residue field `k = K^× ∪ {0}` of the `RV`-sort as a type: `0` adjoined to
`K^× = ker vrv`.  This is the paper's `K` of Definition 2.1(2d). -/
noncomputable def kToResidue : Option (KUnits v) → ResidueField v
  | none => 0
  | some u => ((kUnitsEquivResidueUnits v u : (ResidueField v)ˣ) : ResidueField v)

theorem kToResidue_bijective : Function.Bijective (kToResidue v) := by
  constructor
  · rintro (_ | ⟨u, hu⟩) (_ | ⟨u', hu'⟩) h
    · rfl
    · exact absurd h.symm (Units.ne_zero (kUnitsEquivResidueUnits v ⟨u', hu'⟩))
    · exact absurd h (Units.ne_zero (kUnitsEquivResidueUnits v ⟨u, hu⟩))
    · have h' : kUnitsEquivResidueUnits v ⟨u, hu⟩ = kUnitsEquivResidueUnits v ⟨u', hu'⟩ :=
        Units.val_injective h
      have h'' : (⟨u, hu⟩ : KUnits v) = ⟨u', hu'⟩ := (kUnitsEquivResidueUnits v).injective h'
      rw [h'']
  · intro x
    rcases eq_or_ne x 0 with rfl | hx
    · exact ⟨none, rfl⟩
    · obtain ⟨u, hu'⟩ := (kUnitsEquivResidueUnits v).surjective (Units.mk0 x hx)
      refine ⟨some u, ?_⟩
      show ((kUnitsEquivResidueUnits v u : (ResidueField v)ˣ) : ResidueField v) = x
      rw [hu']
      exact Units.val_mk0 hx

/-- `k = K^× ∪ {0}` is the residue field. -/
noncomputable def kEquiv : Option (KUnits v) ≃ ResidueField v :=
  Equiv.ofBijective _ (kToResidue_bijective v)

/-- **The field structure of the residue field, transported to the `RV`-sort's `K`.** -/
noncomputable def kField : Field (Option (KUnits v)) :=
  (kEquiv v).field

section KFieldInstance

attribute [local instance] kField

/-- **Axiom 3 on the `RV`-sort's `K`**: `k = K^× ∪ {0}` is algebraically closed when `K` is. -/
theorem isAlgClosed_k [IsAlgClosed K] : IsAlgClosed (Option (KUnits v)) := by
  haveI : IsAlgClosed (ResidueField v) := isAlgClosed_residueField v
  exact IsAlgClosed.of_ringEquiv (k' := Option (KUnits v)) (e := (kEquiv v).ringEquiv.symm)

end KFieldInstance

end Bridge

end ACVFResidue

#print axioms ACVFResidue.isAlgClosed_residueField
#print axioms ACVFResidue.exists_root_of_monic
#print axioms ACVFResidue.isIntegral_of_isUnit_leadingCoeff
#print axioms ACVFResidue.isAlgClosed_k
#print axioms ACVFResidue.charZero_residueField_iff
