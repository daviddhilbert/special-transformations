module

public import Section8.UnarySlope
public import Section3.GammaSpecialization
public import Section3.NormalizationSaturation
public import Section8.GammaPairChoice
public import Section8.PowerEstimateFamily

@[expose] public section

section

/-! The unary good locus itself descends to the original Gamma base.
This retains the full invariant preimage on RV representatives. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters

namespace SpecialTransformations.Section8

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {k m g : ℕ}

def unaryFamilyIndexEquiv (k m : ℕ) : Fin k ⊕ (Fin 1 ⊕ Fin m) ≃ Fin (k + (1 + m)) :=
  (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans finSumFinEquiv

private def unaryGoodPrefixGraph {S : Set M}
    (Q : Relation S g (k + (1 + m)) (fun _ => .vf)) :
    Set ((Fin g ⊕ Fin k) ⊕ (Fin 1 ⊕ Fin m) → M) :=
  {z | ((fun i => z (.inl (.inl i))),
    Sum.elim (fun i => z (.inl (.inr i))) (z ∘ Sum.inr) ∘ (unaryFamilyIndexEquiv k m).symm) ∈ Q.carrier}

private def unaryGoodRelation {S : Set M}
    (Q : Relation S g (k + (1 + m)) (fun _ => .vf)) :
    Relation S g (k + 1) (fun _ => .vf) where
  carrier := {p | Proper p.1 ∧ (∀ i, iVF (p.2 i)) ∧
    p.2 ∘ finSumFinEquiv ∉ @isolatedInputsFamily M (@CanonicalStructure.normalize M sM) (Fin k) 1 m
      {w | (p.1, w ∘ (unaryFamilyIndexEquiv k m).symm) ∈ Q.carrier}}
  definable := by
    let N := @CanonicalStructure.normalize M sM
    let E := unaryFamilyIndexEquiv k m
    let e : Fin g ⊕ Fin (k + (1 + m)) → (Fin g ⊕ Fin k) ⊕ (Fin 1 ⊕ Fin m) :=
      Sum.elim (Sum.inl ∘ Sum.inl) (Sum.elim (Sum.inl ∘ Sum.inr) Sum.inr ∘ E.symm)
    letI := sM
    have hQN := Q.definable
    let P := unaryGoodPrefixGraph Q
    have hProper (t : Fin g → M) : @Proper M N g t ↔ @Proper M sM g t := by
      change (∀ i, @NonzeroRV M N (t i)) ↔ (∀ i, @NonzeroRV M sM (t i))
      exact forall_congr' (fun i => @nonzero_rv_normalize M sM hM (t i))
    let C := Q.carrier
    letI := N
    letI : M ⊨ Axioms.ACVF := @CanonicalStructure.normalized_model M sM hM
    have hG : S.Definable LRV P := by
      convert hQN.preimage_comp e using 1
      ext z
      have hz : (z ∘ e) ∘ Sum.inr = Sum.elim (fun i => z (.inl (.inr i))) (z ∘ Sum.inr) ∘ E.symm := by
        funext i
        cases hi : E.symm i <;> simp [e, hi]
      change (_, _) ∈ C ↔ (_, (z ∘ e) ∘ Sum.inr) ∈ C
      rw [hz]
      rfl
    let idx : (Fin g ⊕ Fin k) ⊕ Fin 1 → Fin g ⊕ Fin (k + 1) :=
      Sum.elim (Sum.elim Sum.inl (Sum.inr ∘ finSumFinEquiv ∘ Sum.inl))
        (Sum.inr ∘ finSumFinEquiv ∘ Sum.inr)
    have hIso := (isolatedInputsFamily_definable hG).preimage_comp idx
    have hP : S.Definable LRV {t : Fin g → M | @Proper M sM g t} := by
      have hp : S.Definable LRV {t : Fin g → M | ∀ i, NonzeroRV (t i)} := by
        rw [Set.ofPred_forall]
        exact Set.definable_iInter_of_finite (fun i =>
          (nonzero_rv_definable S).preimage_comp (fun _ : Fin 1 => i))
      convert hp using 1
      ext t
      exact (hProper t).symm
    have hV := (sortedUniverse_definable S (fun _ : Fin (k + 1) => .vf)).raw_definable
    convert (hP.preimage_comp (Sum.inl : Fin g → Fin g ⊕ Fin (k + 1))).inter
      ((hV.preimage_comp (Sum.inr : Fin (k + 1) → Fin g ⊕ Fin (k + 1))).inter hIso.compl) using 1
    ext z
    change (@Proper M sM g (z ∘ Sum.inl) ∧ (∀ i, iVF (z (.inr i))) ∧ _) ↔
      @Proper M sM g (z ∘ Sum.inl) ∧ (∀ i, iVF (z (.inr i))) ∧ z ∘ idx ∉ isolatedInputsFamily P
    apply and_congr_right
    intro _
    apply and_congr_right
    intro _
    apply not_congr
    change ((z ∘ Sum.inr ∘ finSumFinEquiv) ∘ Sum.inr) ∈ isolatedInputs _ ↔
      ((z ∘ idx) ∘ Sum.inr) ∈ isolatedInputs _
    have hrow : {w : Fin 1 ⊕ Fin m → M |
        (z ∘ Sum.inl, Sum.elim ((z ∘ Sum.inr ∘ finSumFinEquiv) ∘ Sum.inl) w ∘ E.symm) ∈ C} =
        {w : Fin 1 ⊕ Fin m → M |
          Sum.elim ((z ∘ idx) ∘ Sum.inl) w ∈ P} := by
      ext w
      rfl
    change ((z ∘ Sum.inr ∘ finSumFinEquiv) ∘ Sum.inr) ∈ isolatedInputs
        {w | (z ∘ Sum.inl, Sum.elim ((z ∘ Sum.inr ∘ finSumFinEquiv) ∘ Sum.inl) w ∘ E.symm) ∈ C} ↔
      ((z ∘ idx) ∘ Sum.inr) ∈ isolatedInputs {w | Sum.elim ((z ∘ idx) ∘ Sum.inl) w ∈ P}
    rw [hrow]
    rfl
  proper := fun _ hp => ⟨hp.1, hp.2.1⟩
  invariant := by
    intro t u htu z
    have he : {w : Fin k ⊕ (Fin 1 ⊕ Fin m) → M |
        (rawTuple t, w ∘ (unaryFamilyIndexEquiv k m).symm) ∈ Q.carrier} =
      {w : Fin k ⊕ (Fin 1 ⊕ Fin m) → M |
        (rawTuple u, w ∘ (unaryFamilyIndexEquiv k m).symm) ∈ Q.carrier} :=
      Set.ext (fun w => Q.invariant t u htu _)
    change Proper (rawTuple t) ∧ _ ∧ z ∘ finSumFinEquiv ∉ @isolatedInputsFamily M
      (@CanonicalStructure.normalize M sM) (Fin k) 1 m _ ↔
        Proper (rawTuple u) ∧ _ ∧ z ∘ finSumFinEquiv ∉ @isolatedInputsFamily M
          (@CanonicalStructure.normalize M sM) (Fin k) 1 m _
    rw [he]
    exact and_congr (iff_of_true (rawTuple_proper t) (rawTuple_proper u)) Iff.rfl

def normalizedUnaryGood (G : Set (Fin k ⊕ (Fin 1 ⊕ Fin m) → M)) : Set (Fin (k + 1) → M) :=
  {z | (∀ i, iVF (z i)) ∧ z ∘ finSumFinEquiv ∉
    @isolatedInputsFamily M (@CanonicalStructure.normalize M sM) (Fin k) 1 m G}

theorem normalizedUnaryGood_gamma_definable {B : Base (M := M)}
    {G : Set (Fin k ⊕ (Fin 1 ⊕ Fin m) → M)}
    (hG : DefinableOverBase B (fun _ : Fin (k + (1 + m)) => .vf)
      {z | z ∘ unaryFamilyIndexEquiv k m ∈ G}) :
    DefinableOverBase B (fun _ => .vf) (normalizedUnaryGood G) := by
  obtain ⟨g, γ, hγ, Q, hQ⟩ := hG
  refine ⟨g, γ, hγ, unaryGoodRelation Q, ?_⟩
  let E := unaryFamilyIndexEquiv k m
  have he : {w : Fin k ⊕ (Fin 1 ⊕ Fin m) → M | w ∘ E.symm ∈ Q.fibre γ} = G := by
    rw [hQ]
    ext w
    change (w ∘ E.symm) ∘ E ∈ G ↔ w ∈ G
    rw [show (w ∘ E.symm) ∘ E = w from funext (fun i => congrArg w (E.symm_apply_apply i))]
  ext z
  change Proper (rawTuple (representatives γ)) ∧ (∀ i, iVF (z i)) ∧ z ∘ finSumFinEquiv ∉
    @isolatedInputsFamily M (@CanonicalStructure.normalize M sM) (Fin k) 1 m
      {w | w ∘ E.symm ∈ Q.fibre γ} ↔
      z ∈ normalizedUnaryGood G
  rw [he]
  exact and_iff_right (rawTuple_proper _)

end SpecialTransformations.Section8

end

section

/-! For a fixed positive slope, the intercept of the unary germ is
unique. The valid radii form a definable upper ray over the same base. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section3.GammaParameters.EndpointLogic (codeValue_surjective)

namespace SpecialTransformations.Section8

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {m : ℕ}

def unaryGammaPowerLaw (f : VFType (M := M) → Fin m → VFType (M := M))
    (a : VFType (M := M)) (p q : ℕ) (c r : Values.Gamma (M := M)) : Prop :=
  ∀ x, r.val < Values.vfValueHom (x - a) →
    vfTupleValue (f x - f a) ^ q = c.val ^ q * Values.vfValueHom (x - a) ^ p

theorem unaryGammaPowerLaw_intercept_unique
    {f : VFType (M := M) → Fin m → VFType (M := M)} {a : VFType (M := M)}
    {p q : ℕ} (hq : 0 < q) {c d r s : Values.Gamma (M := M)}
    (hc : unaryGammaPowerLaw f a p q c r) (hd : unaryGammaPowerLaw f a p q d s) : c = d := by
  obtain ⟨γ, hγ⟩ := exists_gt (max r s)
  obtain ⟨u, hu, he⟩ := gamma_has_vf_representative γ
  let x := u + a
  have hxa : x - a = u := add_sub_cancel_right u a
  have hr : r.val < Values.vfValueHom (x - a) := by
    rw [hxa, he]
    exact (le_max_left r s).trans_lt hγ
  have hs : s.val < Values.vfValueHom (x - a) := by
    rw [hxa, he]
    exact (le_max_right r s).trans_lt hγ
  have hn : Values.vfValueHom (x - a) ≠ 0 := by
    rw [hxa, he, ← Values.infinity_eq_zero]
    exact γ.property
  have h := mul_right_cancel₀ (pow_ne_zero p hn) ((hc x hr).symm.trans (hd x hs))
  have hpow : c ^ q = d ^ q := by
    apply Subtype.ext
    change Values.gammaValHom (c ^ q) = Values.gammaValHom (d ^ q)
    exact (map_pow Values.gammaValHom c q).trans (h.trans (map_pow Values.gammaValHom d q).symm)
  have hq' : 0 < (q : ℤ) := by exact_mod_cast hq
  apply (zpow_left_strictMono (Values.Gamma (M := M)) hq').injective
  simpa only [zpow_natCast] using hpow

theorem named_unaryGammaPowerLaw_of_definable_witnesses (h00 : M ⊨ Axioms.ACVF00)
    (B : Base (M := M)) (f : VFType (M := M) → Fin m → VFType (M := M))
    (a : VFType (M := M)) (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (P : Set (Fin 2 → M)) (hP : DefinableOverBase B (fun _ => .rv) P) (hne : P.Nonempty)
    (hProper : ∀ z ∈ P, Proper z)
    (hsem : ∀ z : Fin 2 → M, Proper z →
      (z ∈ P ↔ unaryGammaPowerLaw f a p q (codeValue (z 0)) (codeValue (z 1)))) :
    ∃ c r, GammaDefinableClosureAtBase B c ∧ GammaDefinableClosureAtBase B r ∧
      unaryGammaPowerLaw f a p q c r := by
  apply gamma_named_unique_shift_radius h00 B (unaryGammaPowerLaw f a p q) P hP hne hProper hsem
  · intro c r d s h₁ h₂
    exact unaryGammaPowerLaw_intercept_unique hq h₁ h₂
  · intro c r hr s hrs x hx
    exact hr x ((show r.val ≤ s.val from hrs).trans_lt hx)
  · intro c r hr x hx
    by_cases hxa : x = a
    · subst x
      simp only [sub_self, vfTupleValue_zero, map_zero, zero_pow hp.ne', zero_pow hq.ne', mul_zero]
    · let d := GammaThresholdGeometry.vfGamma (x - a) (sub_ne_zero.mpr hxa)
      obtain ⟨s, hs, hsd⟩ := exists_between (show r < d from hx)
      exact hr s hs x hsd

theorem named_unaryGammaConstantLaw_of_definable_witnesses (h00 : M ⊨ Axioms.ACVF00)
    (B : Base (M := M)) (f : VFType (M := M) → Fin m → VFType (M := M))
    (a : VFType (M := M)) (P : Set (Fin 2 → M)) (hP : DefinableOverBase B (fun _ => .rv) P)
    (hProper : ∀ z ∈ P, Proper z)
    (hsem : ∀ z : Fin 2 → M, Proper z →
      (z ∈ P ↔ ∀ x, (codeValue (z 1)).val < Values.vfValueHom (x - a) → f x = f a))
    (hne : ∃ r : Values.Gamma (M := M), ∀ x, r.val < Values.vfValueHom (x - a) → f x = f a) :
    ∃ r : Values.Gamma (M := M), GammaDefinableClosureAtBase B r ∧
      ∀ x, r.val < Values.vfValueHom (x - a) → f x = f a := by
  let R : Set (Values.Gamma (M := M)) := {r | ∀ x, r.val < Values.vfValueHom (x - a) → f x = f a}
  have hR : GammaDefinableOverBase B R := by
    have h := hP.image_real (fun _ : Fin 1 => (1 : Fin 2))
    change DefinableOverBase B (fun _ : Fin 1 => .rv) {z | z 0 ∈ Values.gammaPullback R}
    convert h using 1 <;> try rfl
    ext z
    constructor
    · intro hz
      let hz₀ : NonzeroRV (z 0) := ⟨hz.choose, hz.choose_spec.choose⟩
      have hr := (gammaPullback_mem_codeValue_iff R (z 0) hz₀).mp hz
      obtain ⟨c, hc, _⟩ := codeValue_surjective (1 : Values.Gamma (M := M))
      let u : Fin 2 → M := ![c, z 0]
      have hu : Proper u := by
        intro i
        fin_cases i
        · exact hc
        · exact hz₀
      exact ⟨u, (hsem u hu).mpr hr, funext (fun i => by fin_cases i; rfl)⟩
    · rintro ⟨u, hu, he⟩
      have hz : z 0 = u 1 := (congrFun he 0).symm
      change z 0 ∈ Values.gammaPullback R
      rw [hz]
      exact (gammaPullback_mem_codeValue_iff R (u 1) (hProper u hu 1)).mpr ((hsem u (hProper u hu)).mp hu)
  obtain ⟨r, hr, hrd⟩ := gamma_upper_ray_has_definable_radius_base h00 B hR hne
    (fun r hr s hrs x hx => hr x ((show r.val ≤ s.val from hrs).trans_lt hx)) (by
      intro r hr x hx
      by_cases hxa : x = a
      · rw [hxa]
      · let d := GammaThresholdGeometry.vfGamma (x - a) (sub_ne_zero.mpr hxa)
        obtain ⟨s, hs, hsd⟩ := exists_between (show r < d from hx)
        exact hr s hs x hsd)
  exact ⟨r, hrd, hr⟩

end SpecialTransformations.Section8

end

section

/-! The unary slope theorem with the good locus, intercept, and radius
definable over the original Gamma parameters. -/

set_option backward.isDefEq.respectTransparency false

open Filter Topology FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section3.GammaParameters.EndpointLogic (codeValue_surjective)
open SpecialTransformations.Section4

namespace SpecialTransformations.Section8

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k m : ℕ}

def unaryLocalSlopeAtBase (T : Base (M := M)) (R : Finset ℚ) (a : VFType (M := M))
    (f : VFType (M := M) → Fin m → VFType (M := M)) : Prop :=
  ∃ c r : Values.Gamma (M := M), GammaDefinableClosureAtBase T c ∧ GammaDefinableClosureAtBase T r ∧
    ∃ p q : ℕ, 0 < p ∧ 0 < q ∧ (p : ℚ) / q ∈ R ∧
      ((∀ x, r.val < Values.vfValueHom (x - a) → f x = f a) ∨ unaryGammaPowerLaw f a p q c r)

private theorem unary_onBall_iff (mode : PowerComparison)
    (f : (Fin 1 → VFType (M := M)) → Fin m → VFType (M := M))
    (a : VFType (M := M)) (p q : ℕ) (c r : Values.Gamma (M := M)) :
    mode.onBall f ![a] p q c r ↔ ∀ x, r.val < Values.vfValueHom (x - a) →
      match mode with
      | .lowerBound => c.val ^ q * Values.vfValueHom (x - a) ^ p ≤ vfTupleValue (f ![x] - f ![a]) ^ q
      | .equality => vfTupleValue (f ![x] - f ![a]) ^ q = c.val ^ q * Values.vfValueHom (x - a) ^ p
      | .constant => f ![x] = f ![a] := by
  have ht (x : Fin 1 → VFType (M := M)) : (![x 0] : Fin 1 → VFType (M := M)) = x := by
    funext i
    fin_cases i
    rfl
  constructor
  · intro h x hx
    have h' := h ![x] (by simpa only [vfTupleValue_unary, Pi.sub_apply, Matrix.cons_val_zero] using hx)
    cases mode <;> simpa only [PowerComparison.holds, vfTupleValue_unary, Pi.sub_apply, Matrix.cons_val_zero] using h'
  · intro h x hx
    have h' := h (x 0) (by simpa only [vfTupleValue_unary, Pi.sub_apply, Matrix.cons_val_zero] using hx)
    cases mode <;> simpa only [PowerComparison.holds, vfTupleValue_unary, Pi.sub_apply,
      Matrix.cons_val_zero, ht] using h'

theorem lemma_8_3_gamma_base (h00 : M ⊨ Axioms.ACVF00)
    (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    {B : Base (M := M)} (hsmall : Cardinal.mk ↥B.real < κ)
    (f : (Fin k → VFType (M := M)) → (Fin 1 → VFType (M := M)) → Fin m → VFType (M := M))
    (hf : DefinableOverBase B (fun _ : Fin (k + (1 + m)) => .vf)
      {z | z ∘ vfFamilyIndexEquiv k 1 m ∈ vfFamilyGraph f}) :
    ∃ U : Set (Fin (k + 1) → M), DefinableOverBase B (fun _ => .vf) U ∧
      (∀ b : Fin k → VFType (M := M), {a : VFType (M := M) |
        Sum.elim (vfValues b) (vfValues ![a]) ∘ finSumFinEquiv.symm ∉ U}.Finite) ∧
      ∃ R : Finset ℚ, (∀ s ∈ R, 0 < s) ∧ ∀ (b : Fin k → VFType (M := M)) (a : VFType (M := M)),
        Sum.elim (vfValues b) (vfValues ![a]) ∘ finSumFinEquiv.symm ∈ U →
        unaryLocalSlopeAtBase (powerEstimatePointBase B b ![a]) R a (fun x => f b ![x]) := by
  let U := normalizedUnaryGood (vfFamilyGraph f)
  let e := vfFamilyIndexEquiv k 1 m
  have hU : DefinableOverBase B (fun _ => .vf) U := normalizedUnaryGood_gamma_definable hf
  obtain ⟨_, d, hd⟩ := hf.specialize
  let S := B.real ∪ Set.range (rawTuple d)
  have hS : Cardinal.mk S < κ := small_union_range hκ B.real hsmall _
  have hF : S.Definable LRV (unaryFamilyGraph f) := by
    convert hd.raw_definable.preimage_comp e.symm using 1
    ext z
    change z ∈ vfFamilyGraph f ↔ (z ∘ e.symm) ∘ e ∈ vfFamilyGraph f
    rw [show (z ∘ e.symm) ∘ e = z from funext (fun i => congrArg z (e.symm_apply_apply i))]
  have hu (z : Fin k ⊕ Fin 1 → M) : z ∘ finSumFinEquiv.symm ∈ U ↔ z ∈ unaryGoodLocus f := by
    unfold U normalizedUnaryGood unaryGoodLocus
    rw [normalize_eq_of_isCanonical hc]
    have hz : (z ∘ finSumFinEquiv.symm) ∘ finSumFinEquiv = z :=
      funext (fun i => congrArg z (finSumFinEquiv.symm_apply_apply i))
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, hz]
    exact and_congr_left (fun _ => ⟨fun h i => by simpa using h (finSumFinEquiv i), fun h i => h _⟩)
  have hFinite (b : Fin k → VFType (M := M)) : {a : VFType (M := M) |
      Sum.elim (vfValues b) (vfValues ![a]) ∘ finSumFinEquiv.symm ∉ U}.Finite := by
    have h := unaryGoodLocus_finite_exception hc hκ hs hS _ (rawRVSpace_rvCoded 1) hF b
    exact (h.preimage (fun _ _ _ _ he => congrFun he 0)).subset (fun _ ha => fun hz => ha ((hu _).mpr hz))
  refine ⟨U, hU, hFinite, ?_⟩
  by_cases hm : 0 < m
  · let v := Values.presentationValuation (M := M)
    letI : Valued (VFType (M := M)) (Values.presentationType (M := M)) := Valued.mk' v
    have hv := Values.presentation_compatible (M := M)
    obtain ⟨N, D, hND⟩ := unary_family_uniform_positive_power_germ hc hκ hs hS hv hm f hF
    let F := ((Finset.Icc 1 N).product (Finset.Icc 1 D)).image (fun t : ℕ × ℕ => (t.1 : ℚ) / t.2)
    let R := insert 1 F
    refine ⟨R, ?_, fun b a ha => ?_⟩
    · intro s hs
      rcases Finset.mem_insert.mp hs with rfl | hs
      · exact zero_lt_one
      obtain ⟨⟨p, q⟩, h, rfl⟩ := Finset.mem_image.mp hs
      obtain ⟨hp, hq⟩ := Finset.mem_product.mp h
      exact div_pos (by exact_mod_cast (Finset.mem_Icc.mp hp).1) (by exact_mod_cast (Finset.mem_Icc.mp hq).1)
    let T := powerEstimatePointBase B b ![a]
    let g := centeredUnaryFamily v hm f (Fin.snoc b a)
    rcases hND b a ((hu _).mp ha) with hconst | hpow
    · have hne : ∃ r : Values.Gamma (M := M), ∀ x, r.val < Values.vfValueHom (x - a) → f b ![x] = f b ![a] := by
        obtain ⟨r, hr⟩ := (exists_gammaPuncturedBallHolds_iff_eventually hv a
          (fun x => f b ![x] = f b ![a])).mpr (hconst.mono (fun _ h _ => h))
        refine ⟨r, fun x hx => ?_⟩
        by_cases h : x = a
        · rw [h]
        · exact hr x h hx
      obtain ⟨P, hP, hp, hsem⟩ := powerWitness_slice_gamma_base hc (by decide) hm f hf b ![a] 1 1 .constant
      obtain ⟨r, hrd, hr⟩ := named_unaryGammaConstantLaw_of_definable_witnesses h00 T
        (fun x => f b ![x]) a P hP hp (fun z hz => (hsem z hz).trans (unary_onBall_iff .constant _ _ _ _ _ _)) hne
      exact ⟨1, r, real_definableAtBase T .rv _ (GammaSyntax.one_definable T.real), hrd,
        1, 1, one_pos, one_pos, by simp [R], Or.inl hr⟩
    · obtain ⟨p, q, hp, hpN, hq, hqD, s, hs₀, hg⟩ := hpow
      obtain ⟨c, r, hcr⟩ := exists_gammaPowerGerm hv g a s hs₀ p q hq.ne' hg
      have hlaw : unaryGammaPowerLaw (fun x => f b ![x]) a p q c r := by
        intro x hx
        by_cases hxa : x = a
        · subst x
          simp only [sub_self, vfTupleValue_zero, map_zero, zero_pow hq.ne', zero_pow hp.ne', mul_zero]
        · have he : vfTupleValue (f b ![x] - f b ![a]) = Values.vfValueHom (g x) := by
            simp only [vfTupleValue, dif_pos hm, g, centeredUnaryFamily, Fin.init_snoc, Fin.snoc_last] <;> rfl
          rw [he]
          exact (hcr x hxa hx).2
      obtain ⟨P, hP, hPproper, hPsem⟩ := powerWitness_slice_gamma_base hc (by decide) hm f hf b ![a] p q .equality
      have hsem (z : Fin 2 → M) (hz : Proper z) : z ∈ P ↔
          unaryGammaPowerLaw (fun x => f b ![x]) a p q (codeValue (z 0)) (codeValue (z 1)) :=
        (hPsem z hz).trans (unary_onBall_iff .equality _ _ _ _ _ _)
      have hne : P.Nonempty := by
        obtain ⟨u, hu, heu⟩ := codeValue_surjective c
        obtain ⟨w, hw, hew⟩ := codeValue_surjective r
        let z : Fin 2 → M := ![u, w]
        have hz : Proper z := by intro i; fin_cases i; exact hu; exact hw
        refine ⟨z, (hsem z hz).mpr ?_⟩
        change unaryGammaPowerLaw (fun x => f b ![x]) a p q (codeValue u) (codeValue w)
        rwa [heu, hew]
      obtain ⟨c', r', hcd, hrd, hcr'⟩ := named_unaryGammaPowerLaw_of_definable_witnesses h00 T
        (fun x => f b ![x]) a p q hp hq P hP hne hPproper hsem
      have hF : (p : ℚ) / q ∈ F := Finset.mem_image.mpr
        ⟨(p, q), Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hp, hpN⟩, Finset.mem_Icc.mpr ⟨hq, hqD⟩⟩, rfl⟩
      exact ⟨c', r', hcd, hrd, p, q, hp, hq, Finset.mem_insert.mpr (Or.inr hF), Or.inr hcr'⟩
  · have hm₀ : m = 0 := Nat.eq_zero_of_not_pos hm
    subst m
    refine ⟨{1}, by simp, fun b a _ => ?_⟩
    let T := powerEstimatePointBase B b ![a]
    have hOne : GammaDefinableClosureAtBase T 1 := real_definableAtBase T .rv _ (GammaSyntax.one_definable T.real)
    exact ⟨1, 1, hOne, hOne, 1, 1, one_pos, one_pos, by simp, Or.inl (fun x _ => funext (fun i => i.elim0))⟩

end SpecialTransformations.Section8

end
