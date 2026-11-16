module

public import Section3.GammaCodes
public import Section3.EncodedBallGeometry
public import Section3.SortedBoolean
public import Section3.DefinableConstants

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3.GammaParameters
variable {M : Type} [sM : LRV.Structure M]

def NonzeroRV (x : M) : Prop := iRV x ∧ x ≠ iRVZero

def SameScalar (x y : M) : Prop := NonzeroRV x ∧ NonzeroRV y ∧ iLe x y ∧ iLe y x

def Same {n : ℕ} (a b : Fin n → M) : Prop := ∀ i, SameScalar (a i) (b i)

theorem nonzero_rv_definable (S : Set M) : S.Definable₁ LRV {x | NonzeroRV x} := by
  have hr := (definableAt_sort S .rv).raw_definable
  have hz : S.DefinableFun LRV (fun _ : Fin 1 → M => iRVZero) :=
    DefinableConstants.constant (DefinableConstants.function_symbol (L := LRV) Fn.rvZero Fin.elim0 (fun i => i.elim0))
  have hn := ((Set.DefinableFun.proj (L := LRV) (A := S) (i := (0 : Fin 1))).ofPred_eq hz).compl
  exact hr.inter hn

theorem raw_le_definable (S : Set M) : S.Definable LRV {z : Fin 2 → M | iLe (z 0) (z 1)} := by
  have h : (∅ : Set M).Definable LRV {z : Fin 2 → M | Structure.RelMap (L := LRV) Rel.rvLe z} :=
    Set.empty_definable_iff.mpr ⟨.rel Rel.rvLe (fun i => .var (.inl i)),rfl⟩
  convert h.mono (Set.empty_subset S) using 1
  ext z
  have he : ![z 0,z 1] = z := by funext i; fin_cases i <;> rfl
  change Structure.RelMap (L := LRV) Rel.rvLe ![z 0,z 1] ↔ Structure.RelMap (L := LRV) Rel.rvLe z
  rw [he]

theorem same_scalar_definable (S : Set M) :
    S.Definable LRV {z : Fin 2 → M | SameScalar (z 0) (z 1)} := by
  have h0 := (nonzero_rv_definable S).preimage_comp (fun _ : Fin 1 => (0 : Fin 2))
  have h1 := (nonzero_rv_definable S).preimage_comp (fun _ : Fin 1 => (1 : Fin 2))
  have hl := raw_le_definable S
  have hr : S.Definable LRV {z : Fin 2 → M | iLe (z 1) (z 0)} := by
    convert hl.preimage_comp (![1,0] : Fin 2 → Fin 2) using 1
    ext z; rfl
  convert ((h0.inter h1).inter hl).inter hr using 1
  ext z
  change (NonzeroRV (z 0) ∧ NonzeroRV (z 1) ∧ iLe (z 0) (z 1) ∧ iLe (z 1) (z 0)) ↔ _
  simp only [Set.mem_inter_iff,Set.mem_preimage,Set.mem_ofPred_eq,Function.comp_apply]
  tauto

theorem same_definable (S : Set M) {n : ℕ} :
    S.Definable LRV {z : Fin n ⊕ Fin n → M | Same (z ∘ Sum.inl) (z ∘ Sum.inr)} := by
  change S.Definable LRV {z : Fin n ⊕ Fin n → M | ∀ i, SameScalar (z (.inl i)) (z (.inr i))}
  rw [Set.ofPred_forall]
  exact Set.definable_iInter_of_finite (fun i => (same_scalar_definable S).preimage_comp
    (![Sum.inl i,Sum.inr i] : Fin 2 → Fin n ⊕ Fin n))

variable [hM : M ⊨ Axioms.ACVF]

theorem nonzero_rv_normalize (x : M) :
    @NonzeroRV M (CanonicalStructure.normalize (M := M)) x ↔ NonzeroRV x := by
  change (iRV x ∧ x ≠ @iRVZero M (CanonicalStructure.normalize (M := M))) ↔ (iRV x ∧ x ≠ iRVZero)
  have hz : @iRVZero M (CanonicalStructure.normalize (M := M)) = iRVZero :=
    CanonicalStructure.sortZero_normalize .rv
  rw [hz]

theorem same_scalar_normalize (x y : M) :
    @SameScalar M (CanonicalStructure.normalize (M := M)) x y ↔ SameScalar x y := by
  change (@NonzeroRV M (CanonicalStructure.normalize (M := M)) x ∧
      @NonzeroRV M (CanonicalStructure.normalize (M := M)) y ∧ _ ∧ _) ↔
    (NonzeroRV x ∧ NonzeroRV y ∧ _ ∧ _)
  rw [nonzero_rv_normalize,nonzero_rv_normalize]
  apply and_congr_right
  intro hx
  apply and_congr_right
  intro hy
  exact and_congr (rv_le_normalize x y hx.1 hy.1) (rv_le_normalize y x hy.1 hx.1)

theorem same_normalize {n : ℕ} (a b : Fin n → M) :
    @Same M (CanonicalStructure.normalize (M := M)) n a b ↔ Same a b :=
  forall_congr' (fun i => same_scalar_normalize (a i) (b i))

theorem same_normalized_definable (S : Set M) {n : ℕ} :
    @Set.Definable M S LRV (CanonicalStructure.normalize (M := M)) (Fin n ⊕ Fin n)
      {z | Same (z ∘ Sum.inl) (z ∘ Sum.inr)} := by
  have h := @same_definable M (CanonicalStructure.normalize (M := M)) S n
  have he : {z : Fin n ⊕ Fin n → M |
      @Same M (CanonicalStructure.normalize (M := M)) n (z ∘ Sum.inl) (z ∘ Sum.inr)} =
      {z | Same (z ∘ Sum.inl) (z ∘ Sum.inr)} := Set.ext (fun z => same_normalize _ _)
  exact he ▸ h

theorem Same.proper_left {n : ℕ} {a b : Fin n → M} (h : Same a b) : Proper a := fun i => (h i).1

theorem Same.proper_right {n : ℕ} {a b : Fin n → M} (h : Same a b) : Proper b := fun i => (h i).2.1

theorem same_refl {n : ℕ} (a : Fin n → M) (ha : Proper a) : Same a a := by
  intro i
  exact ⟨ha i,ha i,RVCalc.le_refl_rv hM (ha i).1,RVCalc.le_refl_rv hM (ha i).1⟩

theorem same_codes_iff {n : ℕ} (t u : Fin n → Code (M := M)) :
    Same (rawTuple t) (rawTuple u) ↔ values t = values u := by
  constructor
  · intro h
    exact (values_eq_iff t u).mpr (fun i => (h i).2.2)
  · intro h i
    exact ⟨⟨raw_rv (t i),raw_ne_zero (t i)⟩,⟨raw_rv (u i),raw_ne_zero (u i)⟩,
      (values_eq_iff t u).mp h i⟩

theorem same_with_codes_iff {n : ℕ} (a : Fin n → M) (t u : Fin n → Code (M := M))
    (htu : values t = values u) : Same a (rawTuple t) ↔ Same a (rawTuple u) := by
  have hf (t u : Fin n → Code (M := M)) (htu : values t = values u)
      (h : Same a (rawTuple t)) : Same a (rawTuple u) := by
    intro i
    have he := (values_eq_iff t u).mp htu i
    refine ⟨(h i).1,⟨raw_rv (u i),raw_ne_zero (u i)⟩,?_,?_⟩
    · exact RVCalc.le_trans_rv hM (h i).1.1 (raw_rv (t i)) (raw_rv (u i)) (h i).2.2.1 he.1
    · exact RVCalc.le_trans_rv hM (raw_rv (u i)) (raw_rv (t i)) (h i).1.1 he.2 (h i).2.2.2
  exact ⟨hf t u htu,hf u t htu.symm⟩


theorem proper_normalized_definable (S : Set M) {n : ℕ} :
    @Set.Definable M S LRV (CanonicalStructure.normalize (M := M)) (Fin n)
      {a | Proper a} := by
  let idx : Fin n ⊕ Fin n → Fin n := Sum.elim id id
  have h := @Set.Definable.preimage_comp M S LRV (CanonicalStructure.normalize (M := M))
    (Fin n ⊕ Fin n) (Fin n) idx _ (same_normalized_definable S)
  convert h using 1
  ext a
  change Proper a ↔ Same a a
  exact ⟨same_refl a,Same.proper_left⟩

end SpecialTransformations.Section3.GammaParameters
