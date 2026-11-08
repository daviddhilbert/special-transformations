import Section8.UnarySlope
import Section3.GammaFiniteOrder

/-! An upper ray of valid open-ball radii contains its finite endpoint,
which is definable over the original Gamma base. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section3.GammaParameters.EndpointLogic (codeValue_surjective)
open SpecialTransformations.Section4

namespace SpecialTransformations.Section8

variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem normalize_eq_of_isCanonical (hc : CanonicalStructure.IsCanonical (M := M)) :
    @CanonicalStructure.normalize M sM = sM := by
  classical
  apply Language.Structure.ext
  · funext n f xs
    by_cases hs : ∀ i, sortEval (Fn.argSort f i) (xs i)
    · exact CanonicalStructure.normalize_fun f xs hs
    · change (if ∀ i, sortEval (Fn.argSort f i) (xs i) then
        Structure.funMap (L := LRV) f xs else CanonicalStructure.sortZero (Fn.resSort f)) = _
      rw [if_neg hs, hc.1 f xs hs]
  · funext n r xs
    apply propext
    cases r with
    | memVF => rfl
    | memRV => rfl
    | memUnits => rfl
    | rvLe =>
      change ((∀ i, sortEval .rv (xs i)) ∧ Structure.RelMap (L := LRV) Rel.rvLe xs) ↔
        Structure.RelMap (L := LRV) Rel.rvLe xs
      exact ⟨And.right, fun h => ⟨not_not.mp (fun hxs => hc.2 xs hxs h), h⟩⟩

theorem gamma_least_definable_base (B : Base (M := M)) {A : Set (Values.Gamma (M := M))}
    (hA : GammaDefinableOverBase B A) (r : Values.Gamma (M := M))
    (hr : IsLeast A r) : GammaDefinableClosureAtBase B r := by
  have he : leastCodes (Values.gammaPullback A) = Values.gammaPullback {r} := by
    ext t
    constructor
    · rintro ⟨ht, hle⟩
      obtain ⟨htRV, ht₀, htA⟩ := ht
      let htNZ : NonzeroRV t := ⟨htRV, ht₀⟩
      have hm := (gammaPullback_mem_codeValue_iff A t htNZ).mp ⟨htRV, ht₀, htA⟩
      obtain ⟨u, hu, hur⟩ := codeValue_surjective r
      have huA := (gammaPullback_mem_codeValue_iff A u hu).mpr (hur.symm ▸ hr.1)
      have htr := (original_le_codeValue_iff t u htNZ hu).mp (hle u huA)
      rw [hur] at htr
      exact (gammaPullback_mem_codeValue_iff _ t htNZ).mpr (le_antisymm htr (hr.2 hm))
    · intro ht
      obtain ⟨htRV, ht₀, htR⟩ := ht
      let htNZ : NonzeroRV t := ⟨htRV, ht₀⟩
      have htR' : codeValue t = r :=
        (gammaPullback_mem_codeValue_iff _ t htNZ).mp ⟨htRV, ht₀, htR⟩
      refine ⟨(gammaPullback_mem_codeValue_iff A t htNZ).mpr (htR'.symm ▸ hr.1), ?_⟩
      intro u hu
      obtain ⟨huRV, hu₀, huA⟩ := hu
      let huNZ : NonzeroRV u := ⟨huRV, hu₀⟩
      apply (original_le_codeValue_iff t u htNZ huNZ).mpr
      rw [htR']
      exact hr.2 ((gammaPullback_mem_codeValue_iff A u huNZ).mp ⟨huRV, hu₀, huA⟩)
  have h := leastCodes_definable_base B _ hA
  rwa [he] at h

theorem gamma_upper_ray_has_definable_radius_base (h00 : M ⊨ Axioms.ACVF00)
    (B : Base (M := M)) {A : Set (Values.Gamma (M := M))}
    (hA : GammaDefinableOverBase B A) (hne : A.Nonempty)
    (hup : ∀ x ∈ A, ∀ y, x ≤ y → y ∈ A)
    (hclosed : ∀ x, (∀ y, x < y → y ∈ A) → x ∈ A) :
    ∃ r ∈ A, GammaDefinableClosureAtBase B r := by
  by_cases hcomp : Aᶜ.Nonempty
  · obtain ⟨r, hr⟩ := gamma_canonical_endpoint_exists h00 B A hA hne hcomp
    have hlower (b : Values.Gamma (M := M)) (hb : b ∉ A) : ∀ x ∈ A, b ≤ x := by
      intro x hx
      exact le_of_not_gt (fun h => hb (hup x hx b h.le))
    have hbounded : FiniteThresholds.BoundedBelow A :=
      ⟨hcomp.choose, hlower hcomp.choose hcomp.choose_spec⟩
    have hrinf := (hr.resolve_right (fun h => h.1 hbounded)).2
    have hrA : r ∈ A := hclosed r (fun x hx => by
      by_contra hnot
      exact (not_le_of_gt hx) (hrinf.2 x (hlower x hnot)))
    exact ⟨r, hrA, gamma_least_definable_base B hA r ⟨hrA, hrinf.1⟩⟩
  · refine ⟨1, ?_, real_definableAtBase B .rv _ (GammaSyntax.one_definable B.real)⟩
    by_contra h
    exact hcomp ⟨1, h⟩

private def gammaBadUpperCodes (U : Set M) : Set M :=
  {t | iRV t ∧ ∃ u ∈ U, ¬ iLe u t}

private theorem gammaBadUpperCodes_definable (B : Base (M := M)) (U : Set M)
    (hU : DefinableAtBase B .rv U) : DefinableAtBase B .rv (gammaBadUpperCodes U) := by
  have hU2 := hU.preimage_real (fun _ : Fin 2 => .rv) (fun _ : Fin 1 => (0 : Fin 2))
  have hR := real_definableOverBase B _ _ (not_le_pair_definable B.real)
  have hp := (hU2.inter hR).image_real (fun _ : Fin 1 => (1 : Fin 2))
  change DefinableOverBase B (fun _ : Fin 1 => .rv) {z | z 0 ∈ gammaBadUpperCodes U}
  convert hp using 1 <;> try rfl
  ext z
  change (iRV (z 0) ∧ ∃ u ∈ U, ¬ iLe u (z 0)) ↔ ∃ w,
    ((w 0 ∈ U ∧ w ∈ sortedUniverse (fun _ : Fin 2 => .rv)) ∧
      ((∀ i, iRV (w i)) ∧ ¬ iLe (w 0) (w 1))) ∧ w ∘ (fun _ : Fin 1 => (1 : Fin 2)) = z
  constructor
  · rintro ⟨hz, u, hu, hlt⟩
    have hs : ∀ i, iRV ((![u, z 0] : Fin 2 → M) i) := by
      intro i
      fin_cases i
      · exact hU.proper u hu
      · exact hz
    exact ⟨![u, z 0], ⟨⟨hu, hs⟩, ⟨hs, hlt⟩⟩, funext (fun i => by fin_cases i; rfl)⟩
  · rintro ⟨w, ⟨⟨hu, hs⟩, _, hlt⟩, he⟩
    have h := congrFun he 0
    change w 1 = z 0 at h
    rw [← h]
    exact ⟨hs 1, w 0, hu, hlt⟩

theorem gamma_upperBounds_definable_base (B : Base (M := M)) {A : Set (Values.Gamma (M := M))}
    (hA : GammaDefinableOverBase B A) :
    GammaDefinableOverBase B (upperBounds A) := by
  let T : Set M := {t | NonzeroRV t}
  have hT : DefinableAtBase B .rv T :=
    real_definableAtBase B .rv _ ((definableAt_iff_normalized_raw B.real .rv T).mpr
      ⟨nonzero_codes_normalized_definable B.real, fun _ h => h.1⟩)
  have h := hT.inter (gammaBadUpperCodes_definable B (Values.gammaPullback A) hA).compl
  change DefinableOverBase B (fun _ : Fin 1 => .rv) {z | z 0 ∈ Values.gammaPullback (upperBounds A)}
  convert h using 1
  ext z
  change z 0 ∈ Values.gammaPullback (upperBounds A) ↔
    NonzeroRV (z 0) ∧ ((∀ i : Fin 1, iRV (z i)) ∧ z 0 ∉ gammaBadUpperCodes (Values.gammaPullback A))
  constructor
  · intro hz
    let h₀ : NonzeroRV (z 0) := ⟨hz.choose, hz.choose_spec.choose⟩
    refine ⟨h₀, fun i => ?_, ?_⟩
    · fin_cases i
      exact h₀.1
    · rintro ⟨_, u, hu, hlt⟩
      let hu₀ : NonzeroRV u := ⟨hu.choose, hu.choose_spec.choose⟩
      have hu' := (gammaPullback_mem_codeValue_iff A u hu₀).mp hu
      have hupper := (gammaPullback_mem_codeValue_iff _ (z 0) h₀).mp hz
      exact hlt ((original_le_codeValue_iff u (z 0) hu₀ h₀).mpr (hupper hu'))
  · rintro ⟨hz, _, hn⟩
    apply (gammaPullback_mem_codeValue_iff _ (z 0) hz).mpr
    intro x hx
    obtain ⟨u, hu, he⟩ := codeValue_surjective x
    have huA := (gammaPullback_mem_codeValue_iff A u hu).mpr (he.symm ▸ hx)
    have hle : iLe u (z 0) := not_not.mp (fun h => hn ⟨hz.1, u, huA, h⟩)
    exact he ▸ (original_le_codeValue_iff u (z 0) hu hz).mp hle

theorem gamma_div_definable_base (B : Base (M := M)) (x y : Values.Gamma (M := M))
    (hx : GammaDefinableClosureAtBase B x) (hy : GammaDefinableClosureAtBase B y) :
    GammaDefinableClosureAtBase B (x / y) := by
  let Q : Set (Fin 3 → M) := {z | GammaSyntax.Proper z ∧
    GammaSyntax.decode z 0 * GammaSyntax.decode z 1 = GammaSyntax.decode z 2}
  have hQ := GammaSyntax.mul_definable (M := M) B.real (0 : Fin 3) 1 2
  have hQ' : DefinableOver B.real (fun _ : Fin 3 => .rv) Q :=
    (definableOver_iff_normalized_raw B.real (fun _ : Fin 3 => .rv) Q).mpr
      ⟨hQ, fun z hz i => (hz.1 i).1⟩
  let pick : Fin 2 → Fin 3 := ![1, 2]
  have hName := (gamma_fibre_tuple_definable_base B (![y, x] : Fin 2 → Values.Gamma (M := M))
    (by intro i; fin_cases i; exact hy; exact hx)).preimage_real (fun _ : Fin 3 => .rv) pick
  have hp := ((real_definableOverBase B _ _ hQ').inter hName).image_real (fun _ : Fin 1 => (0 : Fin 3))
  change DefinableOverBase B (fun _ : Fin 1 => .rv) {z | z 0 ∈ Values.gammaPullback {x / y}}
  convert hp using 1 <;> try rfl
  ext z
  constructor
  · intro hz
    obtain ⟨u, hu, huval⟩ := codeValue_surjective y
    obtain ⟨w, hw, hwval⟩ := codeValue_surjective x
    let t : Fin 3 → M := ![z 0, u, w]
    have hz₀ : NonzeroRV (z 0) := ⟨hz.choose, hz.choose_spec.choose⟩
    have ht : GammaSyntax.Proper t := by intro i; fin_cases i; exact hz₀; exact hu; exact hw
    have hcode := (gammaPullback_mem_codeValue_iff _ (z 0) hz₀).mp hz
    refine ⟨t, ⟨⟨ht, ?_⟩, ⟨?_, fun i => (ht i).1⟩⟩, funext (fun i => by fin_cases i; rfl)⟩
    · change codeValue (z 0) * codeValue u = codeValue w
      rw [hcode, huval, hwval, div_mul_cancel]
    · intro i
      fin_cases i
      · exact (gammaPullback_mem_codeValue_iff _ u hu).mpr huval
      · exact (gammaPullback_mem_codeValue_iff _ w hw).mpr hwval
  · rintro ⟨t, ⟨⟨ht, hMul⟩, ⟨hn, _⟩⟩, he⟩
    have h₁ : codeValue (t 1) = y := (gammaPullback_mem_codeValue_iff _ (t 1) (ht 1)).mp (hn 0)
    have h₂ : codeValue (t 2) = x := (gammaPullback_mem_codeValue_iff _ (t 2) (ht 2)).mp (hn 1)
    have h₀ : t 0 = z 0 := congrFun he 0
    change z 0 ∈ Values.gammaPullback {x / y}
    rw [← h₀]
    apply (gammaPullback_mem_codeValue_iff _ (t 0) (ht 0)).mpr
    change codeValue (t 0) * codeValue (t 1) = codeValue (t 2) at hMul
    rw [h₁, h₂] at hMul
    exact eq_div_iff_mul_eq'.mpr hMul

theorem gamma_lower_ray_has_named_point (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M))
    {A : Set (Values.Gamma (M := M))} (hA : GammaDefinableOverBase B A) (hne : A.Nonempty)
    (hdown : ∀ x ∈ A, ∀ y, y ≤ x → y ∈ A)
    (δ : Values.Gamma (M := M)) (hδ : GammaDefinableClosureAtBase B δ) (hδ₁ : 1 < δ) :
    ∃ x ∈ A, GammaDefinableClosureAtBase B x := by
  by_cases hcomp : Aᶜ.Nonempty
  · obtain ⟨r, hr⟩ := gamma_canonical_endpoint_exists h00 B A hA hne hcomp
    have hbelow : ¬ FiniteThresholds.BoundedBelow A := by
      rintro ⟨b, hb⟩
      obtain ⟨x, hx⟩ := hne
      obtain ⟨y, hy⟩ := exists_lt (min b x)
      exact (not_le_of_gt (hy.trans_le (min_le_left _ _))) (hb y (hdown x hx y (hy.le.trans (min_le_right _ _))))
    have hr' := (hr.resolve_left (fun h => hbelow h.1)).2
    have hrUB : r ∈ upperBounds A := fun x hx => hr'.2 x (fun y hy =>
      le_of_not_gt (fun h => hy (hdown x hx y h.le)))
    have hrLeast : IsLeast (upperBounds A) r := ⟨hrUB, fun x hx => le_of_not_gt (fun h => by
      obtain ⟨z, hxz, hzr⟩ := exists_between h
      have hz : z ∈ Aᶜ := fun ha => (not_le_of_gt hxz) (hx ha)
      exact (not_le_of_gt hzr) (hr'.1 z hz))⟩
    have hrd := gamma_least_definable_base B (gamma_upperBounds_definable_base B hA) r hrLeast
    refine ⟨r / δ, ?_, gamma_div_definable_base B r δ hrd hδ⟩
    have hlt : r / δ < r := (div_lt_iff_lt_mul).mpr (lt_mul_of_one_lt_right' r hδ₁)
    by_contra hnot
    exact (not_le_of_gt hlt) (hr'.1 _ hnot)
  · refine ⟨1, ?_, real_definableAtBase B .rv _ (GammaSyntax.one_definable B.real)⟩
    by_contra h
    exact hcomp ⟨1, h⟩

end SpecialTransformations.Section8
