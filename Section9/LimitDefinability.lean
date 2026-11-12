module

public import Section9.FiniteFibreLimit
public import Section8.ContinuityFormula
public import Section3.GammaCodeDefinability

@[expose] public section

/-! Same-base definability of the finite minimal limit. A Boolean mask
indicates which output coordinates are finite. Quantifying over
nonzero VF representatives supplies all Gamma radii without a section. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M]

private theorem rawOpenBallAt_definable {ι : Type} {S : Set M}
    {a r y : (ι → M) → M} (ha : S.DefinableFun LRV a) (hr : S.DefinableFun LRV r)
    (hy : S.DefinableFun LRV y) :
    S.Definable LRV {z | y z ∈ rawOpenBall (a z) (r z)} := by
  let F (z : ι → M) : Fin 3 → M := ![a z, r z, y z]
  have hF : S.DefinableMap LRV F := by
    intro i
    fin_cases i
    · exact ha
    · exact hr
    · exact hy
  convert (OpenBallCodes.membership_raw_definable S).preimage_map hF using 1
  ext z
  have hinit : Fin.init (F z) = ![a z, r z] := by
    funext i
    fin_cases i <;> rfl
  change y z ∈ rawOpenBall (a z) (r z) ↔ F z (Fin.last 2) ∈ OpenBallCodes.rawBall (Fin.init (F z))
  rw [hinit]
  rfl

public def rawInfinitySide (r y : M) : Prop :=
  ¬ iLe (iRv iVFOne) (iRv (iVFMul y r))

private theorem rawInfinitySide_definable {ι : Type} (S : Set M) (r y : ι) :
    S.Definable LRV {z : ι → M | rawInfinitySide (z r) (z y)} := by
  have hmul : S.DefinableFun LRV (fun z : ι → M => iVFMul (z y) (z r)) :=
    (Set.DefinableFun.of_empty (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.vfMul)).comp
      (show S.DefinableMap LRV (fun z : ι → M => ![z y, z r]) from by
        intro j
        fin_cases j <;> exact Set.DefinableFun.proj LRV)
  have hone : S.DefinableFun LRV (fun _ : ι → M => iVFOne) :=
    DefinableConstants.constant (DefinableConstants.function_symbol
      (L := LRV) Fn.vfOne Fin.elim0 (fun i => i.elim0))
  have hrv {f : (ι → M) → M} (hf : S.DefinableFun LRV f) :
      S.DefinableFun LRV (fun z => iRv (f z)) :=
    (Set.DefinableFun.of_empty (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.rvMap)).comp
      (show S.DefinableMap LRV (fun z : ι → M => ![f z]) from by
        intro j
        fin_cases j
        exact hf)
  exact ((GammaParameters.raw_le_definable S).preimage_map
    (show S.DefinableMap LRV (fun z : ι → M => ![iRv iVFOne, iRv (iVFMul (z y) (z r))]) from by
      intro j
      fin_cases j
      · exact hrv hone
      · exact hrv hmul)).compl

public def rawLimitHit {m : ℕ} (finite : Fin m → Bool) (G : Set (Fin 1 ⊕ Fin m → M)) :
    Set (Fin m ⊕ Fin 2 → M) :=
  {q | ∃ z ∈ G, (iVF (z (.inl 0)) ∧ z (.inl 0) ≠ iVFZero) ∧
    z (.inl 0) ∈ rawOpenBall iVFZero (q (.inr 1)) ∧ ∀ i,
      if finite i then z (.inr i) ∈ rawOpenBall (q (.inl i)) (q (.inr 0))
      else rawInfinitySide (q (.inr 0)) (z (.inr i))}

private theorem rawLimitHit_definable {m : ℕ} {S : Set M} (finite : Fin m → Bool)
    {G : Set (Fin 1 ⊕ Fin m → M)} (hG : S.Definable LRV G) :
    S.Definable LRV (rawLimitHit finite G) := by
  let W := (Fin m ⊕ Fin 2) ⊕ (Fin 1 ⊕ Fin m)
  let r : W := .inl (.inr 0)
  let s : W := .inl (.inr 1)
  let x : W := .inr (.inl 0)
  let b (i : Fin m) : W := .inl (.inl i)
  let y (i : Fin m) : W := .inr (.inr i)
  have hzero : S.DefinableFun LRV (fun _ : W → M => iVFZero) :=
    DefinableConstants.constant (DefinableConstants.function_symbol
      (L := LRV) Fn.vfZero Fin.elim0 (fun i => i.elim0))
  have hin : S.Definable LRV {z : W → M | z x ∈ rawOpenBall iVFZero (z s)} :=
    rawOpenBallAt_definable hzero (Set.DefinableFun.proj LRV) (Set.DefinableFun.proj LRV)
  have hout (i : Fin m) : S.Definable LRV {z : W → M |
      if finite i then z (y i) ∈ rawOpenBall (z (b i)) (z r) else rawInfinitySide (z r) (z (y i))} := by
    by_cases h : finite i
    · simp only [if_pos h]
      exact rawOpenBallAt_definable (Set.DefinableFun.proj LRV) (Set.DefinableFun.proj LRV)
        (Set.DefinableFun.proj LRV)
    · simpa only [if_neg h] using rawInfinitySide_definable S r (y i)
  have hAll : S.Definable LRV {z : W → M | ∀ i,
      if finite i then z (y i) ∈ rawOpenBall (z (b i)) (z r) else rawInfinitySide (z r) (z (y i))} := by
    rw [Set.ofPred_forall]
    exact Set.definable_iInter_of_finite hout
  have h := ((hG.preimage_comp (Sum.inr : Fin 1 ⊕ Fin m → W)).inter
    ((properRadiusAt_definable S x).inter (hin.inter hAll))).exists_of_finite
  exact h

def rawFrequentLimit {m : ℕ} (finite : Fin m → Bool) (G : Set (Fin 1 ⊕ Fin m → M)) :
    Set (Fin m → M) :=
  {b | b ∈ vfRawUniverse m ∧ ∀ t : Fin 2 → M,
    ((iVF (t 0) ∧ t 0 ≠ iVFZero) ∧ (iVF (t 1) ∧ t 1 ≠ iVFZero)) →
      Sum.elim b t ∈ rawLimitHit finite G}

theorem rawFrequentLimit_definable {m : ℕ} {S : Set M} (finite : Fin m → Bool)
    {G : Set (Fin 1 ⊕ Fin m → M)} (hG : S.Definable LRV G) :
    S.Definable LRV (rawFrequentLimit finite G) := by
  let W := Fin m ⊕ Fin 2
  have h0 := properRadiusAt_definable S (.inr 0 : W)
  have h1 := properRadiusAt_definable S (.inr 1 : W)
  exact (vfRawUniverse_definable S m).inter
    (((h0.inter h1).himp (rawLimitHit_definable finite hG)).forall_of_finite)

variable [M ⊨ Axioms.ACVF]

local notation "VF" => VFType (M := M)
local notation "Γ" => Values.Gamma (M := M)
local notation "w" => Values.presentationValuation (M := M)

def maskedLimitPoint {m : ℕ} (finite : Fin m → Bool) (b : Fin m → VF) : Fin m → LimitPoint M :=
  fun i => if finite i then some (b i) else none

/-- Definability in every finite/infinite chart of the auxiliary limit
space. The original model language only codes the finite coordinates. -/
def LimitSetDefinable {m : ℕ} (S : Set M) (L : Set (Fin m → LimitPoint M)) : Prop :=
  ∀ finite : Fin m → Bool,
    S.Definable LRV (vfValues '' {b : Fin m → VF | maskedLimitPoint finite b ∈ L})

private theorem rawInfinitySide_iff (r y : VF) (hr : r ≠ 0) :
    rawInfinitySide r.val y.val ↔ (w r)⁻¹ < w y := by
  change (¬ VFValued.predV (y * r) 1) ↔ _
  rw [Values.presentation_compatible, map_mul, map_one, not_le, ← one_div]
  exact (div_lt_iff₀ (pos_iff_ne_zero.mpr
    ((Values.presentationValuation (M := M)).ne_zero_iff.mpr hr))).symm

private theorem rawLimitHit_iff {m : ℕ} (A : Set (Fin 1 → VF))
    (f : (Fin 1 → VF) → Set (Fin m → VF)) (finite : Fin m → Bool) (b : Fin m → VF)
    (r s : VF) (hr : r ≠ 0) (hs : s ≠ 0) (ε δ : Γ)
    (hrv : Values.vfValueHom r = ε.val) (hsv : Values.vfValueHom s = δ.val) :
    Sum.elim (vfValues b) ![r.val, s.val] ∈ rawLimitHit finite (unaryLimitGraph A f) ↔
      ∃ x ∈ A \ {0}, x ∈ vfBall 0 δ ∧ ∃ y ∈ f x, y ∈ limitBall (maskedLimitPoint finite b) ε := by
  have hinput (x : Fin 1 → VF) : (x 0).val ∈ rawOpenBall iVFZero s.val ↔ x ∈ vfBall 0 δ := by
    have h := mem_rawOpenBall_iff w Values.presentation_compatible (0 : VF) s (x 0) hs
    rw [sub_zero] at h
    constructor
    · intro hx i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      change δ.val < Values.vfValueHom (x 0 - 0)
      simpa only [Pi.zero_apply, sub_zero, ← hsv] using
        (vfValue_lt_iff_presentation s (x 0)).mpr (h.mp hx)
    · intro hx
      apply h.mpr
      apply (vfValue_lt_iff_presentation s (x 0)).mp
      simpa only [Pi.zero_apply, sub_zero, ← hsv] using hx 0
  have houtput (i : Fin m) (y : VF) :
      (if finite i then y.val ∈ rawOpenBall (b i).val r.val else rawInfinitySide r.val y.val) ↔
        memLimitBall (maskedLimitPoint finite b i) ε y := by
    by_cases hi : finite i
    · simp only [maskedLimitPoint, if_pos hi]
      exact (mem_rawOpenBall_iff w Values.presentation_compatible (b i) r y hr).trans
        (memValuedLimitSide_iff_memLimitBall r ε hrv (some (b i)) y)
    · simp only [maskedLimitPoint, if_neg hi]
      exact (rawInfinitySide_iff r y hr).trans (memValuedLimitSide_iff_memLimitBall r ε hrv none y)
  have hzero (x : Fin 1 → VF) : (x 0).val ≠ iVFZero ↔ x ≠ 0 := by
    constructor
    · intro h he
      exact h (congrArg (fun a : Fin 1 → VF => (a 0).val) he)
    · intro h he
      exact h (funext (fun i => by fin_cases i; exact Subtype.ext he))
  constructor
  · rintro ⟨_, ⟨x, hx, y, hy, rfl⟩, hx₀, hnear, hout⟩
    exact ⟨x, ⟨hx, (hzero x).mp hx₀.2⟩, (hinput x).mp hnear,
      y, hy, fun i => (houtput i (y i)).mp (hout i)⟩
  · rintro ⟨x, hx, hnear, y, hy, hout⟩
    exact ⟨Sum.elim (vfValues x) (vfValues y), ⟨x, hx.1, y, hy, rfl⟩,
      ⟨(x 0).property, (hzero x).mpr hx.2⟩, (hinput x).mpr hnear,
      fun i => (houtput i (y i)).mpr (hout i)⟩

private theorem mem_rawFrequentLimit_iff {m : ℕ} (A : Set (Fin 1 → VF))
    (f : (Fin 1 → VF) → Set (Fin m → VF)) (finite : Fin m → Bool) (b : Fin m → VF) :
    vfValues b ∈ rawFrequentLimit finite (unaryLimitGraph A f) ↔
      ∀ ε δ : Γ, ∃ x ∈ A \ {0}, x ∈ vfBall 0 δ ∧
        ∃ y ∈ f x, y ∈ limitBall (maskedLimitPoint finite b) ε := by
  constructor
  · intro hb ε δ
    obtain ⟨r, hr, hrv⟩ := gamma_has_vf_representative ε
    obtain ⟨s, hs, hsv⟩ := gamma_has_vf_representative δ
    apply (rawLimitHit_iff A f finite b r s hr hs ε δ hrv hsv).mp
    exact hb.2 ![r.val, s.val] ⟨⟨r.property, fun h => hr (Subtype.ext h)⟩,
      ⟨s.property, fun h => hs (Subtype.ext h)⟩⟩
  · intro hb
    refine ⟨fun i => (b i).property, fun t ht => ?_⟩
    let r : VF := ⟨t 0, ht.1.1⟩
    let s : VF := ⟨t 1, ht.2.1⟩
    have hr : r ≠ 0 := fun he => ht.1.2 (congrArg Subtype.val he)
    have hs : s ≠ 0 := fun he => ht.2.2 (congrArg Subtype.val he)
    let ε := Values.gammaOf (CanonicalRV.encodedRv r)
      (fun h => hr ((CanonicalRV.encodedRv_zero_iff r).mp h))
    let δ := Values.gammaOf (CanonicalRV.encodedRv s)
      (fun h => hs ((CanonicalRV.encodedRv_zero_iff s).mp h))
    have ht' : ![r.val, s.val] = t := funext (fun i => by fin_cases i <;> rfl)
    rw [← ht']
    exact (rawLimitHit_iff A f finite b r s hr hs ε δ rfl rfl).mpr (hb ε δ)

theorem IsMinimalLimitSet.definable_of_finite {m : ℕ} {S : Set M}
    {A : Set (Fin 1 → VF)} {f : (Fin 1 → VF) → Set (Fin m → VF)}
    (hG : S.Definable LRV (unaryLimitGraph A f)) {L : Set (Fin m → LimitPoint M)}
    (hL : IsMinimalLimitSet A 0 f L) (hLf : L.Finite) : LimitSetDefinable S L := by
  intro finite
  have heq : vfValues '' {b : Fin m → VF | maskedLimitPoint finite b ∈ L} =
      rawFrequentLimit finite (unaryLimitGraph A f) := by
    ext z
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact (mem_rawFrequentLimit_iff A f finite b).mpr
        ((hL.mem_iff_frequently_hits hLf (maskedLimitPoint finite b)).mp hb)
    · intro hz
      let b : Fin m → VF := fun i => ⟨z i, hz.1 i⟩
      exact ⟨b, (hL.mem_iff_frequently_hits hLf (maskedLimitPoint finite b)).mpr
        ((mem_rawFrequentLimit_iff A f finite b).mp hz), rfl⟩
  rw [heq]
  exact rawFrequentLimit_definable finite hG

/-- Lemma 9.5. A definable unary set-valued map with finite VF fibres
has a finite minimal limit at zero, definable over the same base. -/
theorem lemma_9_5 {m : ℕ}
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal} (hs : Saturated M κ)
    {S : Set M} (hsmall : Cardinal.mk S < κ) (A : Set (Fin 1 → VF))
    (f : (Fin 1 → VF) → Set (Fin m → VF))
    (hG : S.Definable LRV (unaryLimitGraph A f)) (hfin : ∀ x ∈ A, (f x).Finite) :
    ∃ L : Set (Fin m → LimitPoint M), L.Finite ∧ IsMinimalLimitSet A 0 f L ∧ LimitSetDefinable S L := by
  obtain ⟨L, hLf, hL⟩ := lemma_9_5_finite_minimal hc hs hsmall A f hG hfin
  exact ⟨L, hLf, hL, hL.definable_of_finite hG hLf⟩

end SpecialTransformations.Section9
