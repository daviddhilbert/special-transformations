module

public import Section7.DefinableTupleQuantifiers
public import Section7.TupleCoordinates
public import Section7.LiftRelations
public import Section7.EncodedResidueRoots
public import Section3.TupleCompactness
public import Section3.GammaRealMap
public import Section3.GammaProjection

@[expose] public section

section DefinableLiftDomainsProof

/-!
# Definable domains of local lifts

Membership in the domain says that the fixed VF relation is a bijective
graph between the indicated RV fibres. The domain is defined by the
first-order existence and uniqueness tests in both directions. No
parameter from either fibre is named.
-/

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3

set_option backward.isDefEq.respectTransparency false

namespace SpecialTransformations.Section7

variable {M : Type} [LRV.Structure M]

def rawTupleFibre {n : ℕ} (t : Fin n → M) : Set (Fin n → M) :=
  {a | ∀ i, iVF (a i) ∧ iRv (a i) = t i}

def rawLiftDomain {n : ℕ} (A : Set (Fin (n + n) → M)) : Set (Fin (n + n) → M) :=
  {z |
    (∀ a ∈ rawTupleFibre (z ∘ productLeft n n),
      ∃! b, b ∈ rawTupleFibre (z ∘ productRight n n) ∧ productTuple a b ∈ A) ∧
    (∀ b ∈ rawTupleFibre (z ∘ productRight n n),
      ∃! a, a ∈ rawTupleFibre (z ∘ productLeft n n) ∧ productTuple a b ∈ A)}

theorem rawOneWayLiftDomain_definable (S : Set M) {ι : Type} {n : ℕ}
    (A : Set (Fin (n + n) → M)) (hA : S.Definable LRV A)
    (l r : Fin n → ι) (f : Fin (n + n) → Fin n ⊕ Fin n) :
    S.Definable LRV {z : ι → M | ∀ a ∈ rawTupleFibre (z ∘ l),
      ∃! b, b ∈ rawTupleFibre (z ∘ r) ∧ Sum.elim a b ∘ f ∈ A} := by
  let π : Fin (n + n) → (ι ⊕ Fin n) ⊕ Fin n :=
    Sum.elim (Sum.inl ∘ Sum.inr) Sum.inr ∘ f
  have h := (rawTupleFibreGuard_definable S
    (Sum.inr : Fin n → (ι ⊕ Fin n) ⊕ Fin n) (Sum.inl ∘ Sum.inl ∘ r)).inter
    (hA.preimage_comp π)
  have hP : S.Definable LRV {w : (ι ⊕ Fin n) ⊕ Fin n → M |
      w ∘ Sum.inr ∈ rawTupleFibre ((w ∘ Sum.inl ∘ Sum.inl) ∘ r) ∧
      Sum.elim (w ∘ Sum.inl ∘ Sum.inr) (w ∘ Sum.inr) ∘ f ∈ A} := by
    convert h using 1
    ext w
    have he : Sum.elim (w ∘ Sum.inl ∘ Sum.inr) (w ∘ Sum.inr) ∘ f = w ∘ π := by
      funext j
      rcases hj : f j with k | k <;> simp [π, Function.comp_def, hj]
    rw [Set.mem_inter_iff]
    exact and_congr Iff.rfl (by rw [he]; rfl)
  have hU := definable_existsUnique_tuple
    (fun (w : ι ⊕ Fin n → M) (b : Fin n → M) =>
      b ∈ rawTupleFibre ((w ∘ Sum.inl) ∘ r) ∧ Sum.elim (w ∘ Sum.inr) b ∘ f ∈ A) hP
  have hd := (rawTupleFibreGuard_definable S (Sum.inr : Fin n → ι ⊕ Fin n)
      (Sum.inl ∘ l)).compl.union hU
  have hall := hd.forall_of_finite
  convert hall using 1
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_compl_iff, Sum.elim_comp_inl,
    Sum.elim_comp_inr]
  classical
  constructor
  · intro h a
    by_cases ha : a ∈ rawTupleFibre (z ∘ l)
    · exact Or.inr (h a ha)
    · exact Or.inl ha
  · intro h a ha
    exact (h a).resolve_left (fun hn => hn ha)

theorem rawLiftDomain_definable (S : Set M) {n : ℕ}
    (A : Set (Fin (n + n) → M)) (hA : S.Definable LRV A) :
    S.Definable LRV (rawLiftDomain A) := by
  let e : Fin (n + n) ≃ Fin n ⊕ Fin n := finSumFinEquiv.symm
  have hL := rawOneWayLiftDomain_definable S A hA (productLeft n n) (productRight n n) e
  have hR := rawOneWayLiftDomain_definable S A hA (productRight n n) (productLeft n n) (Sum.swap ∘ e)
  have hswap (b a : Fin n → M) : Sum.elim b a ∘ (Sum.swap ∘ e) = productTuple a b := by
    funext j
    change Sum.elim b a (Sum.swap (e j)) = Sum.elim a b (e j)
    cases e j <;> rfl
  convert hL.inter hR using 1
  ext z
  simp only [rawLiftDomain, Set.mem_inter_iff, Set.mem_ofPred_eq, hswap] <;> rfl

end SpecialTransformations.Section7

end DefinableLiftDomainsProof

section RawFibreTransportProof

/-! Transport both existence and uniqueness between the released
encoded sorts and the actual quotient RV fibres. -/

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer

namespace SpecialTransformations.Section7

variable {M Γ : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
    [LinearOrderedCommGroupWithZero Γ]
variable (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ u w : VFType (M := M), VFValued.predV u w ↔ v u ≤ v w)

def rawVF {n : ℕ} (a : Fin n → VFType (M := M)) : Fin n → M :=
  Subtype.val ∘ a

theorem rawVF_injective (n : ℕ) :
    Function.Injective (rawVF (M := M) (n := n)) := by
  intro a b h
  funext i
  exact Subtype.ext (congrFun h i)

noncomputable def rawRV {n : ℕ} (t : Fin n → _root_.RVCalc.RV v) : Fin n → M :=
  fun i => (CanonicalRV.equiv v hv (t i)).val

theorem rawVF_mem_rawTupleFibre_iff {n : ℕ} (t : Fin n → _root_.RVCalc.RV v)
    (a : Fin n → VFType (M := M)) :
    rawVF a ∈ rawTupleFibre (rawRV v hv t) ↔ a ∈ RVFibre v t := by
  constructor
  · intro ha i
    apply (CanonicalRV.equiv v hv).injective
    rw [CanonicalRV.equiv_rv]
    exact Subtype.ext (ha i).2
  · intro ha i
    refine ⟨(a i).property, ?_⟩
    have h := congrArg (fun u => (CanonicalRV.equiv v hv u).val) (ha i)
    change iRv (a i).val = (CanonicalRV.equiv v hv (t i)).val
    simpa only [CanonicalRV.equiv_rv, CanonicalRV.encodedRv] using h

theorem existsUnique_rawTupleFibre_iff {n : ℕ} (t : Fin n → _root_.RVCalc.RV v)
    (P : (Fin n → M) → Prop) :
    (∃! a : Fin n → VFType (M := M), a ∈ RVFibre v t ∧ P (rawVF a)) ↔
      ∃! a : Fin n → M, a ∈ rawTupleFibre (rawRV v hv t) ∧ P a := by
  constructor
  · rintro ⟨a, ⟨ha, hPa⟩, hunique⟩
    refine ⟨rawVF a, ⟨(rawVF_mem_rawTupleFibre_iff v hv t a).mpr ha, hPa⟩, ?_⟩
    rintro b ⟨hb, hPb⟩
    let b' : Fin n → VFType (M := M) := fun i => ⟨b i, (hb i).1⟩
    have hb' : rawVF b' = b := rfl
    have h := hunique b'
      ⟨(rawVF_mem_rawTupleFibre_iff v hv t b').mp hb, hPb⟩
    exact hb'.symm.trans (congrArg rawVF h)
  · rintro ⟨a, ⟨ha, hPa⟩, hunique⟩
    let a' : Fin n → VFType (M := M) := fun i => ⟨a i, (ha i).1⟩
    have ha' : rawVF a' = a := rfl
    refine ⟨a', ⟨(rawVF_mem_rawTupleFibre_iff v hv t a').mp ha, hPa⟩, ?_⟩
    rintro b ⟨hb, hPb⟩
    exact rawVF_injective n
      ((hunique (rawVF b) ⟨(rawVF_mem_rawTupleFibre_iff v hv t b).mpr hb, hPb⟩).trans ha'.symm)

theorem rawLiftDomain_mem_iff {n : ℕ} (A : Set (Fin (n + n) → M))
    (t s : Fin n → _root_.RVCalc.RV v) :
    productTuple (rawRV v hv t) (rawRV v hv s) ∈ rawLiftDomain A ↔
      FibreBijection v {p | productTuple (rawVF p.1) (rawVF p.2) ∈ A} t s := by
  have hl : productTuple (rawRV v hv t) (rawRV v hv s) ∘ productLeft n n = rawRV v hv t :=
    funext (productTuple_left _ _)
  have hr : productTuple (rawRV v hv t) (rawRV v hv s) ∘ productRight n n = rawRV v hv s :=
    funext (productTuple_right _ _)
  unfold rawLiftDomain
  simp only [Set.mem_ofPred_eq, hl, hr, FibreBijection]
  constructor
  · rintro ⟨hL, hR⟩
    refine ⟨?_, ?_⟩
    · intro a ha
      exact (existsUnique_rawTupleFibre_iff v hv s
        (fun b => productTuple (rawVF a) b ∈ A)).mpr
        (hL (rawVF a) ((rawVF_mem_rawTupleFibre_iff v hv t a).mpr ha))
    · intro b hb
      exact (existsUnique_rawTupleFibre_iff v hv t
        (fun a => productTuple a (rawVF b) ∈ A)).mpr
        (hR (rawVF b) ((rawVF_mem_rawTupleFibre_iff v hv s b).mpr hb))
  · rintro ⟨hL, hR⟩
    refine ⟨?_, ?_⟩
    · intro a ha
      let a' : Fin n → VFType (M := M) := fun i => ⟨a i, (ha i).1⟩
      exact (existsUnique_rawTupleFibre_iff v hv s
        (fun b => productTuple a b ∈ A)).mp
        (hL a' ((rawVF_mem_rawTupleFibre_iff v hv t a').mp ha))
    · intro b hb
      let b' : Fin n → VFType (M := M) := fun i => ⟨b i, (hb i).1⟩
      exact (existsUnique_rawTupleFibre_iff v hv t
        (fun a => productTuple a b ∈ A)).mp
        (hR b' ((rawVF_mem_rawTupleFibre_iff v hv s b').mp hb))

theorem rawVF_rvTuple_of_RVFibre {n : ℕ} {t : Fin n → _root_.RVCalc.RV v}
    {a : Fin n → VFType (M := M)} (ha : a ∈ RVFibre v t) :
    iRv ∘ rawVF a = rawRV v hv t :=
  funext (fun i => ((rawVF_mem_rawTupleFibre_iff v hv t a).mpr ha i).2)

end SpecialTransformations.Section7

end RawFibreTransportProof

section FiniteLiftGluingProof

/-!
# Finite gluing over the original real base

Saturation is used only to extract a finite cover of the RV
correspondence. The domain of each candidate and its VF relation are
already definable over the original real base. On overlaps choose the
first piece, keeping exactly one bijection per RV pair.
-/

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

set_option backward.isDefEq.respectTransparency false

namespace SpecialTransformations.Section7

variable {M : Type} [LRV.Structure M] {n : ℕ}

def firstLiftPiece {k : ℕ} (A : Fin k → Set (Fin (n + n) → M)) (i : Fin k) :
    Set (Fin (n + n) → M) :=
  {z | z ∈ rawLiftDomain (A i) ∧ ∀ j < i, z ∉ rawLiftDomain (A j)}

def gluedLift {k : ℕ} (A : Fin k → Set (Fin (n + n) → M)) :
    Set (Fin (n + n) → M) :=
  {x | ∃ i, x ∈ A i ∧ iRv ∘ x ∈ firstLiftPiece A i}

theorem firstLiftPiece_definable (S : Set M) {k : ℕ}
    (A : Fin k → Set (Fin (n + n) → M)) (hA : ∀ i, S.Definable LRV (A i)) (i : Fin k) :
    S.Definable LRV (firstLiftPiece A i) := by
  have h (j : {j : Fin k // j < i}) : S.Definable LRV (rawLiftDomain (A j.val))ᶜ :=
    (rawLiftDomain_definable S _ (hA j.val)).compl
  convert (rawLiftDomain_definable S _ (hA i)).inter (Set.definable_iInter_of_finite h) using 1
  ext z
  simp only [firstLiftPiece, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter,
    Set.mem_compl_iff, Subtype.forall]

theorem gluedLift_definable (S : Set M) {k : ℕ}
    (A : Fin k → Set (Fin (n + n) → M)) (hA : ∀ i, S.Definable LRV (A i)) :
    S.Definable LRV (gluedLift A) := by
  have h (i : Fin k) : S.Definable LRV {x | x ∈ A i ∧ iRv ∘ x ∈ firstLiftPiece A i} :=
    (hA i).inter ((firstLiftPiece_definable S A hA i).preimage_map (definable_rvTuple S))
  convert Set.definable_iUnion_of_finite h using 1
  ext z
  simp only [gluedLift, Set.mem_ofPred_eq, Set.mem_iUnion]

theorem productTuple_rv_of_rawTupleFibre {z : Fin (n + n) → M} {a b : Fin n → M}
    (ha : a ∈ rawTupleFibre (z ∘ productLeft n n))
    (hb : b ∈ rawTupleFibre (z ∘ productRight n n)) :
    iRv ∘ productTuple a b = z := by
  apply productTuple_ext
  · intro i
    simpa only [Function.comp_apply, productTuple_left] using (ha i).2
  · intro i
    simpa only [Function.comp_apply, productTuple_right] using (hb i).2

theorem gluedLift_good {k : ℕ} (A : Fin k → Set (Fin (n + n) → M))
    {z : Fin (n + n) → M} (hz : ∃ i, z ∈ rawLiftDomain (A i)) :
    z ∈ rawLiftDomain (gluedLift A) := by
  classical
  let I := Finset.univ.filter (fun i : Fin k => z ∈ rawLiftDomain (A i))
  have hI : I.Nonempty := by
    obtain ⟨i, hi⟩ := hz
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  let i := I.min' hI
  have hi : z ∈ firstLiftPiece A i := by
    refine ⟨(Finset.mem_filter.mp (I.min'_mem hI)).2, ?_⟩
    intro j hji hj
    exact (not_le_of_gt hji) (I.min'_le j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩))
  have unique (j : Fin k) (hj : z ∈ firstLiftPiece A j) : j = i := by
    rcases lt_trichotomy j i with h | h | h
    · exact (hi.2 j h hj.1).elim
    · exact h
    · exact (hj.2 i h hi.1).elim
  have hmem (a b : Fin n → M)
      (ha : a ∈ rawTupleFibre (z ∘ productLeft n n))
      (hb : b ∈ rawTupleFibre (z ∘ productRight n n)) :
      productTuple a b ∈ gluedLift A ↔ productTuple a b ∈ A i := by
    change (∃ j, productTuple a b ∈ A j ∧ iRv ∘ productTuple a b ∈ firstLiftPiece A j) ↔ _
    rw [productTuple_rv_of_rawTupleFibre ha hb]
    constructor
    · rintro ⟨j, h, hj⟩
      rwa [unique j hj] at h
    · exact fun h => ⟨i, h, hi⟩
  refine ⟨?_, ?_⟩
  · intro a ha
    exact (existsUnique_congr (fun b => and_congr_right (fun hb => hmem a b ha hb))).mpr
      (hi.1.1 a ha)
  · intro b hb
    exact (existsUnique_congr (fun a => and_congr_right (fun ha => hmem a b ha hb))).mpr
      (hi.1.2 b hb)

theorem exists_originalBase_gluedLift {κ : Cardinal} (hs : Saturated M κ)
    (S T : Set M) (hST : S ⊆ T) (hsmall : Cardinal.mk T < κ)
    (C : Set (Fin (n + n) → M)) (hC : T.Definable LRV C)
    (hloc : ∀ z ∈ C, ∃ A : Set (Fin (n + n) → M),
      S.Definable LRV A ∧ z ∈ rawLiftDomain A) :
    ∃ A : Set (Fin (n + n) → M), S.Definable LRV A ∧ C ⊆ rawLiftDomain A := by
  classical
  let D := {A : Set (Fin (n + n) → M) // S.Definable LRV A}
  let family := Set.range (fun A : D => rawLiftDomain A.val)
  have hfamily : ∀ d ∈ family, T.Definable LRV d := by
    rintro d ⟨A, rfl⟩
    exact (rawLiftDomain_definable S A.val A.property).mono hST
  have hcover : ∀ z ∈ C, ∃ d ∈ family, z ∈ d := by
    intro z hz
    obtain ⟨A, hA, hzA⟩ := hloc z hz
    exact ⟨rawLiftDomain A, Set.mem_range_self (⟨A, hA⟩ : D), hzA⟩
  obtain ⟨E, hE, hsub, hcov⟩ :=
    hs.definable_finite_subcover_tuple T hsmall C hC family hfamily hcover
  letI : Fintype E := hE.fintype
  let k := Fintype.card E
  let e := (Fintype.equivFin E).symm
  choose A hA using (fun i : Fin k => hsub (e i).property)
  refine ⟨gluedLift (fun i => (A i).val), gluedLift_definable S _ (fun i => (A i).property), ?_⟩
  intro z hz
  obtain ⟨d, hd, hzd⟩ := hcov z hz
  obtain ⟨i, hi⟩ := e.surjective (⟨d, hd⟩ : E)
  apply gluedLift_good
  refine ⟨i, ?_⟩
  have hAi : rawLiftDomain (A i).val = (e i).val := hA i
  rw [hAi, hi]
  exact hzd

end SpecialTransformations.Section7

end FiniteLiftGluingProof

section CorrespondenceAlgebraicityProof

/-!
# Finite rows of a definable RV correspondence

Projection of the actual finite row gives algebraicity of each
coordinate over the other tuple and the original real/Gamma base.
This does not add a representative of a Gamma name to the base.
-/

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

set_option backward.isDefEq.respectTransparency false

namespace SpecialTransformations.Section7

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem finiteRVCoordinate_algebraic (B : Base (M := M)) {n : ℕ}
    (A : Set (Fin n → M)) (hA : DefinableOverBase B (fun _ => .rv) A)
    (hfin : A.Finite) {a : Fin n → M} (ha : a ∈ A) (i : Fin n) :
    AlgebraicAtBase B .rv (a i) := by
  let U := (fun b : Fin n → M => b i) '' A
  have hU := hA.image_real (fun _ : Fin 1 => i)
  have hEq : (fun b : Fin n → M => b ∘ (fun _ : Fin 1 => i)) '' A =
      {x | x 0 ∈ U} := by
    ext x
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨b, hb, rfl⟩
    · rintro ⟨b, hb, hbx⟩
      exact ⟨b, hb, funext (fun j => by fin_cases j; exact hbx)⟩
  rw [hEq] at hU
  exact ⟨U, hU, hfin.image _, ⟨a, ha, rfl⟩⟩

theorem correspondenceRight_algebraic (B : Base (M := M)) {n m : ℕ}
    (C : Set (Fin (n + m) → M)) (hC : DefinableOverBase B (fun _ => .rv) C)
    (a : Fin n → M) (b : Fin m → M) (hab : productTuple a b ∈ C)
    (hfin : {b' : Fin m → M | productTuple a b' ∈ C}.Finite) (i : Fin m) :
    AlgebraicAtBase ⟨B.real ∪ Set.range a, B.gamma⟩ .rv (b i) := by
  let B' : Base (M := M) := ⟨B.real ∪ Set.range a, B.gamma⟩
  let A := {b' : Fin m → M | productTuple a b' ∈ C}
  have hC' : DefinableOverBase B' (fun _ => .rv) C :=
    hC.mono Set.subset_union_left (fun _ h => h)
  let S' : Set M := B'.real
  have hmap : @Set.DefinableMap M LRV (CanonicalStructure.normalize (M := M))
      (Fin m) (Fin (n + m)) S' (productTuple a) := by
    letI : LRV.Structure M := @CanonicalStructure.normalize M sM
    intro j
    obtain ⟨k, rfl⟩ := finSumFinEquiv.surjective j
    cases k with
    | inl k =>
      change @Set.DefinableFun M LRV (@CanonicalStructure.normalize M sM) (Fin m)
        S' (fun b' => productTuple a b' (productLeft n m k))
      have hk : a k ∈ S' := Or.inr (Set.mem_range_self k)
      have hconst : @Set.DefinableFun M LRV (@CanonicalStructure.normalize M sM) (Fin m)
          S' (fun _ => a k) := LRV.definableFun_const (Fin m) hk
      simpa only [productTuple_left] using hconst
    | inr k =>
      change @Set.DefinableFun M LRV (@CanonicalStructure.normalize M sM) (Fin m)
        S' (fun b' => productTuple a b' (productRight n m k))
      simpa only [productTuple_right] using
        (Set.DefinableFun.proj (A := S') LRV (i := k))
  have hA' := hC'.preimage_real_map (fun _ : Fin m => .rv) (productTuple a) hmap
  have hA : DefinableOverBase B' (fun _ => .rv) A := by
    convert hA' using 1
    ext x
    refine ⟨fun hx => ⟨hx, ?_⟩, And.left⟩
    intro j
    simpa only [productTuple_right] using hC.proper _ hx (productRight n m j)
  exact finiteRVCoordinate_algebraic B' A hA hfin hab i

theorem correspondenceLeft_algebraic (B : Base (M := M)) {n m : ℕ}
    (C : Set (Fin (n + m) → M)) (hC : DefinableOverBase B (fun _ => .rv) C)
    (a : Fin n → M) (b : Fin m → M) (hab : productTuple a b ∈ C)
    (hfin : {a' : Fin n → M | productTuple a' b ∈ C}.Finite) (i : Fin n) :
    AlgebraicAtBase ⟨B.real ∪ Set.range b, B.gamma⟩ .rv (a i) := by
  let f : Fin (n + m) → Fin (m + n) := fun j =>
    finSumFinEquiv (Sum.swap ((finSumFinEquiv : Fin n ⊕ Fin m ≃ Fin (n + m)).symm j))
  have hf (a' : Fin n → M) : productTuple b a' ∘ f = productTuple a' b := by
    apply productTuple_ext
    · intro j
      simp [Function.comp_apply, f, productLeft, productRight, productTuple]
    · intro j
      simp [Function.comp_apply, f, productLeft, productRight, productTuple]
  let C' : Set (Fin (m + n) → M) := {z | z ∘ f ∈ C ∧ z ∈ sortedUniverse (fun _ => .rv)}
  have hC' : DefinableOverBase B (fun _ => .rv) C' := hC.preimage_real _ f
  have hmem (a' : Fin n → M) : productTuple b a' ∈ C' ↔ productTuple a' b ∈ C := by
    change (_ ∈ C ∧ _) ↔ _
    rw [hf]
    refine ⟨And.left, fun h => ⟨h, ?_⟩⟩
    intro j
    obtain ⟨k, rfl⟩ := finSumFinEquiv.surjective j
    cases k with
    | inl k =>
      change iRV (productTuple b a' (productLeft m n k))
      simpa only [productTuple_left, productTuple_right, sortEval, iRV] using
        hC.proper _ h (productRight n m k)
    | inr k =>
      change iRV (productTuple b a' (productRight m n k))
      simpa only [productTuple_left, productTuple_right, sortEval, iRV] using
        hC.proper _ h (productLeft n m k)
  exact correspondenceRight_algebraic B C' hC' b a ((hmem a).mpr hab)
    (hfin.subset (fun x hx => (hmem x).mp hx)) i

end SpecialTransformations.Section7

end CorrespondenceAlgebraicityProof
