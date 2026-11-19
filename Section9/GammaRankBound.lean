import Section4.RVInfiniteValueDefinability
import Section4.RVSequenceMovement
import Section4.RVParameterInvariance
import Section4.RVFiniteMapRank
import Section4.RVSequenceBounds
import Section4.AlgebraicAutomorphisms
import Section9.GammaLiftObjects
import Section4.EarlierRVInputs
import Section3.ModelContext
import Section8.GammaRadiusBase

/-! Points of a Gamma-definable RV set have rank over the real base at most
its RV dimension (computed over any small code set containing the real
base). Proof: choose codes for the Gamma parameters generically over the
point (they exist since value classes are infinite), so a real basis of the
point stays independent over the real base with these codes; the set is
definable over that base (code invariance), and an automorphism fixing it
moves the basis to an independent one over the code set (strong
homogeneity). -/

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace SpecialTransformations.Section9.GammaLift

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem range_rvValues_snoc {m : ℕ} (w : Fin (m + 1) → CanonicalRV.RVSort M) :
    Set.range (rvValues w) = Set.range (rvValues (Fin.init w)) ∪ {(w (Fin.last m)).val} := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact Or.inr rfl
    · exact Or.inl ⟨j, rfl⟩
  · rintro (⟨j, rfl⟩ | hx)
    · exact ⟨j.castSucc, rfl⟩
    · rw [Set.mem_singleton_iff] at hx
      exact ⟨Fin.last m, hx.symm⟩

/-- Adding a parameter not algebraic over a sequence keeps it independent (exchange). -/
theorem rvSequenceIndependent_insert (hex : RVExchangeInput (M := M)) {S : Set M} :
    ∀ {n : ℕ} (t : Fin n → CanonicalRV.RVSort M), RVSequenceIndependent S t →
      ∀ y : CanonicalRV.RVSort M, ¬ AlgebraicAt (S ∪ Set.range (rvValues t)) .rv y.val →
        RVSequenceIndependent (S ∪ {y.val}) t := by
  intro n
  induction n with
  | zero => intro _ _ _ _; trivial
  | succ n ih =>
    intro t ht y hy
    have hsub : Set.range (rvValues (Fin.init t)) ⊆ Set.range (rvValues t) := by
      rintro _ ⟨j, rfl⟩
      exact ⟨j.castSucc, rfl⟩
    refine ⟨ih (Fin.init t) ht.1 y (fun h => hy (h.mono (Set.union_subset_union_right S hsub))), ?_⟩
    intro hx
    let B₀ := S ∪ Set.range (rvValues (Fin.init t))
    have hx' : AlgebraicAt (insert y.val B₀) .rv (t (Fin.last n)).val := by
      apply hx.mono
      rintro z ((hz | hz) | hz)
      · exact Or.inr (Or.inl hz)
      · exact Or.inl hz
      · exact Or.inr (Or.inr hz)
    have hy' := hex B₀ (t (Fin.last n)) y hx' ht.2
    apply hy
    apply hy'.mono
    rintro z (rfl | hz | hz)
    · exact Or.inr ⟨Fin.last n, rfl⟩
    · exact Or.inl hz
    · exact Or.inr (hsub hz)

/-- A sequence stays independent over parameters forming an independent sequence over it. -/
theorem rvSequenceIndependent_union (hex : RVExchangeInput (M := M)) {S : Set M} {n : ℕ}
    (t : Fin n → CanonicalRV.RVSort M) (ht : RVSequenceIndependent S t) :
    ∀ {m : ℕ} (w : Fin m → CanonicalRV.RVSort M),
      RVSequenceIndependent (S ∪ Set.range (rvValues t)) w →
        RVSequenceIndependent (S ∪ Set.range (rvValues w)) t := by
  intro m
  induction m with
  | zero =>
    intro w _
    have he : S ∪ Set.range (rvValues w) = S := by
      ext x
      constructor
      · rintro (hx | ⟨i, _⟩)
        · exact hx
        · exact i.elim0
      · exact Or.inl
    rw [he]
    exact ht
  | succ m ih =>
    intro w hw
    have h₁ := ih (Fin.init w) hw.1
    have h₂ := rvSequenceIndependent_insert hex t h₁ (w (Fin.last m)) (by
      intro h
      apply hw.2
      apply h.mono
      rintro z ((hz | hz) | hz)
      · exact Or.inl (Or.inl hz)
      · exact Or.inr hz
      · exact Or.inl (Or.inr hz))
    have he : S ∪ Set.range (rvValues w) = (S ∪ Set.range (rvValues (Fin.init w))) ∪ {(w (Fin.last m)).val} := by
      rw [range_rvValues_snoc, Set.union_assoc]
    rw [he]
    exact h₂

/-- Value classes of nonzero RV elements are infinite. -/
theorem sameScalar_class_infinite (h00 : M ⊨ Axioms.ACVF00) (c : M) (hc : NonzeroRV c) :
    {x : M | SameScalar x c}.Infinite := by
  intro hfin
  apply rawRVValuePart_not_both_finite h00 (Set.univ : Set ((Fin 0 → M) × M)) ![c] hc
  refine ⟨?_, ?_⟩
  · convert hfin using 1
    ext x
    simp [rawRVValuePart]
  · convert Set.finite_empty using 1
    ext x
    simp [rawRVValuePart]

/-- Codes with prescribed values forming an independent sequence over a small set. -/
theorem exists_generic_codes (hcan : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    {X : Set M} (hX : Cardinal.mk X < κ) :
    ∀ {g : ℕ} (t : Fin g → Code (M := M)), ∃ t' : Fin g → Code (M := M),
      values t' = values t ∧ RVSequenceIndependent X (fun i => (t' i).val) := by
  intro g
  induction g with
  | zero => intro t; exact ⟨t, rfl, trivial⟩
  | succ g ih =>
    intro t
    obtain ⟨t₀, hv₀, hi₀⟩ := ih (Fin.init t)
    let c := raw (t (Fin.last g))
    have hc : NonzeroRV c := ⟨raw_rv _, raw_ne_zero _⟩
    let X' := (X ∪ Set.range (rawTuple t₀)) ∪ Set.range ![c]
    have hX' : Cardinal.mk X' < κ := small_union_range hκ _ (small_union_range hκ X hX _) _
    let C := {x : M | SameScalar x c}
    have hCd : X'.Definable₁ LRV C := by
      have h := (same_scalar_definable (M := M) X').preimage_map
        (F := fun z : Fin 1 → M => ![z 0, c]) (by
          intro i
          fin_cases i
          · exact Set.DefinableFun.proj LRV
          · exact LRV.definableFun_const (Fin 1) (Or.inr ⟨0, rfl⟩))
      unfold Set.Definable₁
      convert h using 1
      ext z
      exact Iff.rfl
    have hnot : ¬ ∀ x ∈ C, RawClosure.AlgebraicOver X' x :=
      fun h => sameScalar_class_infinite h00 c hc
        (RawClosure.finite_of_definable_subset_algebraic hs X' hX' C hCd h)
    push_neg at hnot
    obtain ⟨x, hxC, hxn⟩ := hnot
    let cx : Code (M := M) := ⟨⟨x, hxC.1.1⟩, hxC.1.2⟩
    let t' : Fin (g + 1) → Code (M := M) := Fin.snoc t₀ cx
    refine ⟨t', ?_, ?_⟩
    · funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · change value (t' (Fin.last g)) = value (t (Fin.last g))
        simp only [t', Fin.snoc_last]
        exact (value_eq_iff cx (t (Fin.last g))).mpr ⟨hxC.2.2.1, hxC.2.2.2⟩
      · change value (t' j.castSucc) = value (t j.castSucc)
        simp only [t', Fin.snoc_castSucc]
        exact congrFun hv₀ j
    · refine ⟨?_, ?_⟩
      · have he : (Fin.init fun i => (t' i).val) = fun i => (t₀ i).val := by
          funext i
          simp [t', Fin.init]
        rw [he]
        exact hi₀
      · intro halg
        apply hxn
        have hsub : (X ∪ Set.range (rvValues (Fin.init fun i => (t' i).val))) ⊆ X' := by
          rintro z (hz | ⟨i, rfl⟩)
          · exact Or.inl (Or.inl hz)
          · refine Or.inl (Or.inr ⟨i, ?_⟩)
            simp [t', rvValues, rawTuple, raw, Fin.init]
        have h'' := halg.mono hsub
        have hx : (t' (Fin.last g)).val.val = x := by simp [t', cx]
        rw [hx] at h''
        exact ((algebraicAt_iff_raw hcan X' .rv x).mp h'').1

theorem gammaPointCode_injective' {n m : ℕ} :
    Function.Injective (SpecialTransformations.Section5.gammaPointCode (M := M) (n := n) (m := m)) := by
  intro p q h
  apply Prod.ext
  · funext i
    apply Subtype.ext
    simpa only [SpecialTransformations.Section5.gammaPointCode, SpecialTransformations.Section5.vfAt,
      Fin.append_left] using congrFun h (Fin.castAdd m i)
  · funext i
    apply Subtype.ext
    simpa only [SpecialTransformations.Section5.gammaPointCode, Fin.append_right] using congrFun h (Fin.natAdd n i)

/-- **Gamma rank bound.** A point of a Gamma-definable RV set has rank over the real
base at most the RV dimension of the set (over the code set of a base context). -/
theorem gamma_rank_le_rvDim (hcan : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (B : Base (M := M)) (hBS : B.real ⊆ (C.base : Set M)) {n : ℕ}
    (A : DefSet (rawRVSpace (M := M) n) (C.base : Set M)) (hA : RVSetGamma A B) (a : A) :
    rvTupleRank hcan (rvExchangeInput_of_earlier C.uncountable.le C.saturated C.model00) B.real a.val ≤
      rvDim A := by
  let hex := rvExchangeInput_of_earlier C.uncountable.le C.saturated C.model00
  have hκ : Cardinal.aleph0 ≤ C.κ := C.uncountable.le
  have hBsmall : Cardinal.mk B.real < C.κ := (Cardinal.mk_le_mk_of_subset hBS).trans_lt C.small
  obtain ⟨g, γ, _, hW⟩ := hA
  obtain ⟨v, hvinj, hinj, hI, _⟩ := exists_rv_coordinate_basis_independent hcan hex B.real a.val
  let seq := a.val ∘ v
  have hseq : RVSequenceIndependent B.real seq :=
    (rvSequenceIndependent_iff hcan hex B.real seq).mpr ⟨hinj, hI⟩
  let X := B.real ∪ Set.range (rvValues a.val)
  have hX : Cardinal.mk X < C.κ := small_union_range hκ _ hBsmall _
  obtain ⟨t', hvals, hgen⟩ := exists_generic_codes hcan C.model00 hκ C.saturated hX (representatives γ)
  have hgen' : RVSequenceIndependent (B.real ∪ Set.range (rvValues seq)) (fun i => (t' i).val) := by
    apply hgen.mono_base
    rintro z (hz | ⟨i, rfl⟩)
    · exact Or.inl hz
    · exact Or.inr ⟨v i, rfl⟩
  have hseqT := rvSequenceIndependent_union hex seq hseq _ hgen'
  let T := B.real ∪ Set.range (rawTuple t')
  have hTe : B.real ∪ Set.range (rvValues (fun i => (t' i).val)) = T := rfl
  rw [hTe] at hseqT
  have hT : Cardinal.mk T < C.κ := small_union_range hκ _ hBsmall _
  let T' := T ∪ (C.base : Set M)
  have hTT' : T ⊆ T' := Set.subset_union_left
  have hT' : Cardinal.mk T' < C.κ := by
    apply (Cardinal.mk_union_le T (C.base : Set M)).trans_lt
    exact Cardinal.add_lt_of_lt hκ hT C.small
  -- the code set of `A` is definable over `T`
  have hWT := hW.specialize t' (hvals.trans (representatives_values γ))
  have hXdef := ((definableOver_iff_normalized_raw T _ _).mp hWT).1
  rw [SpecialTransformations.Section8.normalize_eq_of_isCanonical hcan] at hXdef
  obtain ⟨e, hefix, heind⟩ := exists_automorphism_rv_sequence_independent hcan hκ C.saturated
    C.homogeneous hTT' hT hT' seq hseqT
  let a' := rvAutomorphism e ∘ a.val
  have ha' : a' ∈ A.carrier := by
    let p : SpecialTransformations.Section5.Point (M := M) 0 n := (Fin.elim0, a.val)
    let p' : SpecialTransformations.Section5.Point (M := M) 0 n := (Fin.elim0, a')
    have hp : SpecialTransformations.Section5.gammaPointCode p ∈
        SpecialTransformations.Section5.gammaPointCode '' {q : SpecialTransformations.Section5.Point (M := M) 0 n |
          q.2 ∈ A.carrier} := ⟨p, a.property, rfl⟩
    have hcode : e ∘ SpecialTransformations.Section5.gammaPointCode p =
        SpecialTransformations.Section5.gammaPointCode p' := by
      funext i
      cases i using Fin.addCases with
      | left i => exact i.elim0
      | right i =>
        simp only [Function.comp_apply, SpecialTransformations.Section5.gammaPointCode, Fin.append_right, p, p', a']
        rfl
    have hp' := (definable_mem_automorphism_iff e hefix hXdef _).mpr hp
    rw [hcode] at hp'
    obtain ⟨q, hq, hqe⟩ := hp'
    have := gammaPointCode_injective' hqe
    rw [this] at hq
    exact hq
  let b : A.extend (show (C.base : Set M) ⊆ T' from Set.subset_union_right) := ⟨a', ha'⟩
  have h₁ := rvTupleRank_eq_arity_of_sequence hcan hex T' _ heind
  have h₂ := rvTupleRank_subsequence_le hcan hex T' a' v
  have h₃ := rvTupleRank_le_rvDim hcan hex (A.extend (show (C.base : Set M) ⊆ T' from Set.subset_union_right)) b
  have h₄ := rvDim_extend_le (show (C.base : Set M) ⊆ T' from Set.subset_union_right) A
  have hcomp : rvAutomorphism e ∘ seq = a' ∘ v := rfl
  rw [hcomp] at h₁
  calc rvTupleRank hcan hex B.real a.val = rvTupleRank hcan hex T' (a' ∘ v) := h₁.symm
    _ ≤ rvTupleRank hcan hex T' a' := h₂
    _ ≤ rvDim (A.extend _) := h₃
    _ ≤ rvDim A := h₄

end SpecialTransformations.Section9.GammaLift
