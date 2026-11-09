import Section7.AlgebraicResidueRoot
import Section7.LiftingDefinability
import Section7.LiftingAlgebra
import Section7.EncodedHensel
import Section7.ResidueCharacteristic
import Section4.PolynomialZero
import Section3.GammaSpecialization
import Section3.SmallFiniteParameters

section LocalLiftingPointProof

/-!
# The pointwise part of Theorem 7.6

Both finite projections give coordinate algebraicity. Apply Lemma 7.4
to the other block plus one coordinate, and reindex each polynomial
into the full tuple. The coefficient field is the original VF part
of the generated base throughout.
-/

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open MvPolynomial IsLocalRing

set_option backward.isDefEq.respectTransparency false

namespace SpecialTransformations.Section7

def appendCoordinate {n m : ℕ} (f : Fin n ↪ Fin m) (i : Fin m) (hi : i ∉ Set.range f) :
    Fin (n + 1) ↪ Fin m where
  toFun := Fin.snoc f i
  inj' := by
    intro a b
    refine Fin.lastCases ?_ (fun j => ?_) a
    · refine Fin.lastCases (fun _ => rfl) (fun k h => ?_) b
      rw [Fin.snoc_last, Fin.snoc_castSucc] at h
      exact (hi ⟨k, h.symm⟩).elim
    · refine Fin.lastCases (fun h => ?_) (fun k h => ?_) b
      · rw [Fin.snoc_castSucc, Fin.snoc_last] at h
        exact (hi ⟨j, h⟩).elim
      · rw [Fin.snoc_castSucc, Fin.snoc_castSucc] at h
        exact congrArg Fin.castSucc (f.injective h)

@[simp] theorem appendCoordinate_castSucc {n m : ℕ} (f : Fin n ↪ Fin m)
    (i : Fin m) (hi : i ∉ Set.range f) (j : Fin n) :
    appendCoordinate f i hi j.castSucc = f j := by
  simp [appendCoordinate]

@[simp] theorem appendCoordinate_last {n m : ℕ} (f : Fin n ↪ Fin m)
    (i : Fin m) (hi : i ∉ Set.range f) :
    appendCoordinate f i hi (Fin.last n) = i := by
  simp [appendCoordinate]

theorem notMem_range_appendCoordinate {n m : ℕ} (f : Fin n ↪ Fin m)
    (i : Fin m) (hi : i ∉ Set.range f) {j : Fin m} (hj : j ∉ Set.range f) (hji : j ≠ i) :
    j ∉ Set.range (appendCoordinate f i hi) := by
  rintro ⟨k, hk⟩
  refine Fin.lastCases ?_ (fun l => ?_) k hk
  · intro h
    exact hji (((appendCoordinate_last f i hi).symm.trans h).symm)
  · intro h
    exact hj ⟨l, (appendCoordinate_castSucc f i hi l).symm.trans h⟩

variable {M Γ : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
    [LinearOrderedCommGroupWithZero Γ]

theorem exists_originalPolynomial_for_coordinate {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : Base (M := M)) (hsmall : Cardinal.mk B.real < κ) (hB : VFGammaGeneratedBase B)
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)
    {n m : ℕ} (f : Fin n ↪ Fin m) (i : Fin m) (hi : i ∉ Set.range f)
    (t : Fin m → _root_.RVCalc.RV v) (ht : ∀ j, t j ≠ none)
    (halg : AlgebraicAtBase
      ⟨B.real ∪ Set.range (fun j : Fin n => (CanonicalRV.equiv v hv (t (f j))).val), B.gamma⟩
        .rv (CanonicalRV.equiv v hv (t i)).val) :
    let E := vfDefinableClosureFieldBase B
    ∃ (α : Γ) (F : MvPolynomial (Fin m) E),
      IsGammaPolynomial v (fun j => _root_.RVCalc.vrv v (t j)) α (F.map E.subtype) ∧
      IsResidueRoot v t α (F.map E.subtype) ∧
      (¬ IsResidueRoot v t (α / _root_.RVCalc.vrv v (t i)) (pderiv i (F.map E.subtype))) ∧
      (∀ j, j ∉ Set.range f → j ≠ i → pderiv j (F.map E.subtype) = 0) := by
  let E := vfDefinableClosureFieldBase B
  let g := appendCoordinate f i hi
  have halg' : AlgebraicAtBase
      ⟨B.real ∪ Set.range (fun j : Fin n => (CanonicalRV.equiv v hv ((t ∘ g) j.castSucc)).val),
        B.gamma⟩ .rv (CanonicalRV.equiv v hv ((t ∘ g) (Fin.last n))).val := by
    simpa only [Function.comp_apply, g, appendCoordinate_castSucc, appendCoordinate_last] using halg
  obtain ⟨α, P, hP, hr, hd⟩ := lemma_7_4 hκ hs h00 B hsmall hB v hv
    (t ∘ g) (fun j => ht (g j)) halg'
  have hγ (j : Fin m) : _root_.RVCalc.vrv v (t j) ≠ 0 := by
    obtain ⟨a, ha⟩ := rvFibre_nonempty v t
    rw [← rvFibre_value v ha j]
    exact (Valuation.ne_zero_iff v).mpr
      (fun h => ht j ((ha j).symm.trans (h ▸ _root_.RVCalc.rv_zero)))
  refine ⟨α, rename g P, ?_, ?_, ?_, ?_⟩
  · rw [map_rename]
    exact IsGammaPolynomial.rename v g hP hγ
  · rw [map_rename]
    exact (residueRoot_rename_iff v ht g hP).mpr hr
  · have hg : g (Fin.last n) = i := appendCoordinate_last f i hi
    rw [map_rename, ← hg, pderiv_rename g.injective]
    rw [← pderiv_map] at hd
    exact fun h => hd ((residueRoot_rename_iff v ht g (hP.pderiv v (Fin.last n))).mp h)
  · intro j hj hji
    rw [map_rename]
    exact pderiv_rename_eq_zero_of_notMem_range g (notMem_range_appendCoordinate f i hi hj hji) _

/-- A finite-to-finite RV correspondence has local lifting equations with
weights and simple Jacobian blocks over the same coefficient field. -/
theorem exists_correspondence_weighted_local_polynomials {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hsat : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : Base (M := M)) (hsmall : Cardinal.mk B.real < κ) (hB : VFGammaGeneratedBase B)
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)
    {n : ℕ} (C : Set (Fin (n + n) → M)) (hC : DefinableOverBase B (fun _ => .rv) C)
    (t s : Fin n → _root_.RVCalc.RV v) (ht : ∀ i, t i ≠ none) (hs : ∀ i, s i ≠ none) :
    let raw := fun u => (CanonicalRV.equiv v hv u).val
    productTuple (raw ∘ t) (raw ∘ s) ∈ C →
    {b : Fin n → M | productTuple (raw ∘ t) b ∈ C}.Finite →
    {a : Fin n → M | productTuple a (raw ∘ s) ∈ C}.Finite →
    let E := vfDefinableClosureFieldBase B
    ∃ (H : Fin n → MvPolynomial (Fin (n + n)) E) (w : Fin n → Γ),
      let u := productTuple t s
      let Z := fun i => (H i).map E.subtype
      (∀ i, IsGammaPolynomial v (fun j => _root_.RVCalc.vrv v (u j)) (w i) (Z i)) ∧
      ¬ IsResidueRoot v u (jacobianValue (fun j => _root_.RVCalc.vrv v (t j)) w)
        (partialJacobianPolynomial (productLeft n n) Z) ∧
      ¬ IsResidueRoot v u (jacobianValue (fun j => _root_.RVCalc.vrv v (s j)) w)
        (partialJacobianPolynomial (productRight n n) Z) ∧
      FibreBijection v {p | ∀ i, (Z i).eval (productTuple p.1 p.2) = 0} t s := by
  classical
  intro raw hab hright hleft
  let L := productLeft n n
  let R := productRight n n
  let u := productTuple t s
  have hu (j : Fin (n + n)) : u j ≠ none := by
    obtain ⟨k, rfl⟩ := finSumFinEquiv.surjective j
    cases k with
    | inl k =>
      change u (L k) ≠ none
      simpa [u, L] using ht k
    | inr k =>
      change u (R k) ≠ none
      simpa [u, R] using hs k
  have hL (i : Fin n) : L i ∉ Set.range R := fun ⟨j, h⟩ => productLeft_ne_right i j h.symm
  have hR (i : Fin n) : R i ∉ Set.range L := fun ⟨j, h⟩ => productLeft_ne_right j i h
  have htu : u ∘ L = t := funext (productTuple_left t s)
  have hsu : u ∘ R = s := funext (productTuple_right t s)
  have halgR (i : Fin n) : AlgebraicAtBase
      ⟨B.real ∪ Set.range (raw ∘ (u ∘ L)), B.gamma⟩ .rv (raw (u (R i))) := by
    rw [htu]
    simpa only [u, L, R, Function.comp_apply, productTuple_left, productTuple_right] using
      correspondenceRight_algebraic B C hC (raw ∘ t) (raw ∘ s) hab hright i
  have halgL (i : Fin n) : AlgebraicAtBase
      ⟨B.real ∪ Set.range (raw ∘ (u ∘ R)), B.gamma⟩ .rv (raw (u (L i))) := by
    rw [hsu]
    simpa only [u, L, R, Function.comp_apply, productTuple_left, productTuple_right] using
      correspondenceLeft_algebraic B C hC (raw ∘ t) (raw ∘ s) hab hleft i
  choose α F hF hrF hdF hoF using fun i =>
    exists_originalPolynomial_for_coordinate hκ hsat h00 B hsmall hB v hv L (R i) (hR i) u hu (halgR i)
  choose β G hG hrG hdG hoG using fun i =>
    exists_originalPolynomial_for_coordinate hκ hsat h00 B hsmall hB v hv R (L i) (hL i) u hu (halgL i)
  letI : IsAlgClosed (VFType (M := M)) := VFAlgClosed.isAlgClosed_vfType
  letI : CharZero (ResidueField v.valuationSubring) := residueField_charZero_of_model00 v hv h00
  simpa only [productTuple_left, productTuple_right] using
    exists_weightedLocalPolynomialSystem v (vfDefinableClosureFieldBase B) t s ht hs α β F G
      hF hG hrF hrG hdF hdG
      (fun i j h => hoF i (R j) (hR j) (fun he => h ((R.injective he).symm)))
      (fun i j h => hoG i (L j) (hL j) (fun he => h ((L.injective he).symm)))

theorem exists_correspondence_local_polynomials {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hsat : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : Base (M := M)) (hsmall : Cardinal.mk B.real < κ) (hB : VFGammaGeneratedBase B)
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)
    {n : ℕ} (C : Set (Fin (n + n) → M)) (hC : DefinableOverBase B (fun _ => .rv) C)
    (t s : Fin n → _root_.RVCalc.RV v) (ht : ∀ i, t i ≠ none) (hs : ∀ i, s i ≠ none) :
    let raw := fun u => (CanonicalRV.equiv v hv u).val
    productTuple (raw ∘ t) (raw ∘ s) ∈ C →
    {b : Fin n → M | productTuple (raw ∘ t) b ∈ C}.Finite →
    {a : Fin n → M | productTuple a (raw ∘ s) ∈ C}.Finite →
    let E := vfDefinableClosureFieldBase B
    ∃ H : Fin n → MvPolynomial (Fin (n + n)) E,
      FibreBijection v {p | ∀ i, ((H i).map E.subtype).eval (productTuple p.1 p.2) = 0} t s := by
  intro raw hab hright hleft
  obtain ⟨H, w, h⟩ := exists_correspondence_weighted_local_polynomials hκ hsat h00 B hsmall hB
    v hv C hC t s ht hs hab hright hleft
  exact ⟨H, h.2.2.2⟩

end SpecialTransformations.Section7

end LocalLiftingPointProof

section CorrespondenceLiftingProof

/-!
# Theorem 7.6: lifting a finite-to-finite RV correspondence

The pointwise polynomial construction gives local graphs over the
original real base. Genuine saturation extracts a finite cover, using
temporary codes only for the finitely many Gamma names of the domain.
The final VF relation has no such temporary parameters.
-/

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 MvPolynomial

set_option backward.isDefEq.respectTransparency false

namespace SpecialTransformations.Section7

variable {M Γ : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
    [LinearOrderedCommGroupWithZero Γ]

theorem exists_gluedLift_of_gamma_definable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hsat : Saturated M κ) (B : Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    {n : ℕ} (C : Set (Fin (n + n) → M)) (hC : DefinableOverBase B (fun _ => .rv) C)
    (hloc : ∀ z ∈ C, ∃ A : Set (Fin (n + n) → M),
      B.real.Definable LRV A ∧ z ∈ rawLiftDomain A) :
    ∃ A : Set (Fin (n + n) → M), B.real.Definable LRV A ∧ C ⊆ rawLiftDomain A := by
  obtain ⟨k, c, hc⟩ := hC.specialize
  exact exists_originalBase_gluedLift hsat B.real (B.real ∪ Set.range (rawTuple c))
    Set.subset_union_left (small_union_range hκ B.real hsmall (rawTuple c)) C hc.raw_definable hloc

theorem theorem_7_6 {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hsat : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : Base (M := M)) (hsmall : Cardinal.mk B.real < κ) (hB : VFGammaGeneratedBase B)
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)
    {n : ℕ} (C : Set (Fin (n + n) → M)) (hC : DefinableOverBase B (fun _ => .rv) C)
    (h0 : ∀ z ∈ C, ∀ i, z i ≠ iRVZero)
    (hleft : ∀ b : Fin n → M, {a : Fin n → M | productTuple a b ∈ C}.Finite)
    (hright : ∀ a : Fin n → M, {b : Fin n → M | productTuple a b ∈ C}.Finite) :
    ∃ A : Set (Fin (n + n) → M),
      B.real.Definable LRV A ∧
      (∀ z ∈ A, ∀ i, iVF (z i)) ∧
      C ⊆ rawLiftDomain A ∧
      IsLift v
        {p | productTuple (rawRV v hv p.1) (rawRV v hv p.2) ∈ C}
        {p | productTuple (rawVF p.1) (rawVF p.2) ∈ A} := by
  classical
  let E := vfDefinableClosureFieldBase B
  have hloc : ∀ z ∈ C, ∃ A : Set (Fin (n + n) → M),
      B.real.Definable LRV A ∧ z ∈ rawLiftDomain A := by
    intro z hz
    let t : Fin n → _root_.RVCalc.RV v := fun i =>
      (CanonicalRV.equiv v hv).symm ⟨z (productLeft n n i), by
        simpa only [sortEval, iRV] using hC.proper z hz (productLeft n n i)⟩
    let s : Fin n → _root_.RVCalc.RV v := fun i =>
      (CanonicalRV.equiv v hv).symm ⟨z (productRight n n i), by
        simpa only [sortEval, iRV] using hC.proper z hz (productRight n n i)⟩
    have ht_raw (i : Fin n) : rawRV v hv t i = z (productLeft n n i) := by
      simp [rawRV, t]
    have hs_raw (i : Fin n) : rawRV v hv s i = z (productRight n n i) := by
      simp [rawRV, s]
    have hz_eq : productTuple (rawRV v hv t) (rawRV v hv s) = z := by
      apply productTuple_ext
      · intro i; simpa only [productTuple_left] using ht_raw i
      · intro i; simpa only [productTuple_right] using hs_raw i
    have hnone : (CanonicalRV.equiv v hv (none : _root_.RVCalc.RV v)).val = iRVZero := by
      rw [← _root_.RVCalc.rv_zero, CanonicalRV.equiv_rv]
      exact RVCalc.rv_zero_eq hM
    have ht (i : Fin n) : t i ≠ none := by
      intro he
      have h := ht_raw i
      rw [rawRV, he, hnone] at h
      exact h0 z hz _ h.symm
    have hs (i : Fin n) : s i ≠ none := by
      intro he
      have h := hs_raw i
      rw [rawRV, he, hnone] at h
      exact h0 z hz _ h.symm
    obtain ⟨H, hH⟩ := exists_correspondence_local_polynomials hκ hsat h00 B hsmall hB
      v hv C hC t s ht hs (by
        change productTuple (rawRV v hv t) (rawRV v hv s) ∈ C
        rwa [hz_eq]) (hright _) (hleft _)
    let A := {x | ∀ i, x ∈ PolynomialZero.zeroSet E (H i)}
    have hA (i : Fin n) : B.real.Definable LRV (PolynomialZero.zeroSet E (H i)) :=
      (PolynomialZero.zeroSet_named_definable B.real E
        (fun c => (mem_generatedBase_vfField B hB c.val).mp c.property) (H i)).raw_definable
    have hAd : B.real.Definable LRV A := by
      convert Set.definable_iInter_of_finite hA using 1
      ext x
      simp [A]
    have hmem (p : (Fin n → VFType (M := M)) × (Fin n → VFType (M := M))) :
        productTuple (rawVF p.1) (rawVF p.2) ∈ A ↔
          ∀ i, ((H i).map E.subtype).eval (productTuple p.1 p.2) = 0 := by
      have he : productTuple (rawVF p.1) (rawVF p.2) = rawVF (productTuple p.1 p.2) := by
        apply productTuple_ext
        · intro i; simp [rawVF]
        · intro i; simp [rawVF]
      rw [he]
      apply forall_congr'
      intro i
      rw [eval_map]
      exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨fun j => (productTuple p.1 p.2 j).property, h⟩⟩
    refine ⟨A, hAd, ?_⟩
    rw [← hz_eq]
    apply (rawLiftDomain_mem_iff v hv A t s).mpr
    have he : {p : (Fin n → VFType (M := M)) × (Fin n → VFType (M := M)) |
        productTuple (rawVF p.1) (rawVF p.2) ∈ A} =
        {p | ∀ i, ((H i).map E.subtype).eval (productTuple p.1 p.2) = 0} := Set.ext hmem
    rw [he]
    exact hH
  obtain ⟨A, hAd, hA⟩ := exists_gluedLift_of_gamma_definable hκ hsat B hsmall C hC hloc
  let V := sortedUniverse (M := M) (fun _ : Fin (n + n) => SortTag.vf)
  have hsorted (z : Fin (n + n) → M) {a b : Fin n → M}
      (ha : a ∈ rawTupleFibre (z ∘ productLeft n n))
      (hb : b ∈ rawTupleFibre (z ∘ productRight n n)) : productTuple a b ∈ V := by
    intro j
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective j
    cases i with
    | inl i =>
      change iVF (productTuple a b (productLeft n n i))
      simpa only [productTuple_left] using (ha i).1
    | inr i =>
      change iVF (productTuple a b (productRight n n i))
      simpa only [productTuple_right] using (hb i).1
  have hgood : C ⊆ rawLiftDomain (A ∩ V) := by
    intro z hz
    have hg := hA hz
    refine ⟨?_, ?_⟩
    · intro a ha
      exact (existsUnique_congr (fun b => and_congr_right (fun hb =>
        ⟨fun h => ⟨h, hsorted z ha hb⟩, And.left⟩))).mp (hg.1 a ha)
    · intro b hb
      exact (existsUnique_congr (fun a => and_congr_right (fun ha =>
        ⟨fun h => ⟨h, hsorted z ha hb⟩, And.left⟩))).mp (hg.2 b hb)
  refine ⟨A ∩ V, hAd.inter ((sortedUniverse_definable B.real _).raw_definable),
    (fun _ hz i => hz.2 i), hgood, ?_⟩
  intro p hp
  exact (rawLiftDomain_mem_iff v hv _ p.1 p.2).mp (hgood hp)

theorem theorem_7_6_sorted (hcan : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hsat : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : Base (M := M)) (hsmall : Cardinal.mk B.real < κ) (hB : VFGammaGeneratedBase B)
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)
    {n : ℕ} (C : Set (Fin (n + n) → M)) (hC : DefinableOverBase B (fun _ => .rv) C)
    (h0 : ∀ z ∈ C, ∀ i, z i ≠ iRVZero)
    (hleft : ∀ b : Fin n → M, {a : Fin n → M | productTuple a b ∈ C}.Finite)
    (hright : ∀ a : Fin n → M, {b : Fin n → M | productTuple a b ∈ C}.Finite) :
    ∃ A : Set (Fin (n + n) → M), DefinableOverBase B (fun _ => .vf) A ∧
      IsLift v
        {p | productTuple (rawRV v hv p.1) (rawRV v hv p.2) ∈ C}
        {p | productTuple (rawVF p.1) (rawVF p.2) ∈ A} := by
  obtain ⟨A, hA, hsort, _, hlift⟩ :=
    theorem_7_6 hκ hsat h00 B hsmall hB v hv C hC h0 hleft hright
  exact ⟨A, real_definableOverBase B _ A
    (raw_definableOver_sorted hcan B.real _ A hA hsort), hlift⟩

end SpecialTransformations.Section7

end CorrespondenceLiftingProof
