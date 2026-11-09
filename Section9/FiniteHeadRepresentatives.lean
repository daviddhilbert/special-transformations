import Section7.GeneratedRVRepresentatives
import Section7.LiftingDefinability
import Section3.DefinableLocalChoice

/-! Representatives for finitely many RV labels above a fixed VF head.
Only the VF generators and the finite head are enlarged in the
algebraic-lifting step. The uniform choice graph uses the original
real parameters, even when its required domain uses Gamma names. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section7

namespace SpecialTransformations.Section9

variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}

theorem definable_rv_representative_over_head
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    (hB : VFGammaGeneratedBase B) (a : Fin k → M) (ha : ∀ i, iVF (a i))
    (t : CanonicalRV.RVSort M) (ht₀ : t ≠ 0)
    (ht : AlgebraicAtBase ⟨B.real ∪ Set.range a, B.gamma⟩ .rv t.val) :
    ∃ x : VFType (M := M), DefinableClosureAt ((B.real ∪ Set.range a) ∪ {t.val}) .vf x.val ∧
      CanonicalRV.encodedRv x = t := by
  obtain ⟨A, G, hAB, _, hA, he⟩ := hB
  let A' := A ∪ Set.range a
  let T : Base (M := M) := ⟨A', G⟩
  have hTA : ∀ x ∈ A', iVF x := by
    rintro x (hx | ⟨i, rfl⟩)
    · exact hA x hx
    · exact ha i
  have hTsmall := small_union_range hκ A ((Cardinal.mk_le_mk_of_subset hAB).trans_lt hsmall) a
  have hmono := closureBase_mono (B := ⟨A,G⟩) (C := T) Set.subset_union_left (fun _ h => h)
  rw [he] at hmono
  have haT : Set.range a ⊆ (closureBase T).real :=
    Set.subset_union_right.trans (subset_closureBase T).1
  have ht' := ht.mono (Set.union_subset hmono.1 haT) hmono.2
  obtain ⟨c, hc⟩ := algebraic_rv_closure_generated_lifts hκ hs h00 A' hTA hTsmall G t ht'
  have hsub : A' ⊆ (B.real ∪ Set.range a) ∪ {t.val} :=
    (Set.union_subset (hAB.trans Set.subset_union_left) Set.subset_union_right).trans
      Set.subset_union_left
  have hcAlg := ((mem_vfAlgebraicClosureField A' c.val).mp c.property).mono hsub
  exact definable_rv_representative_of_algebraic_lift h00 _ t (Or.inr (Set.mem_singleton _)) ht₀
    c.val hc hcAlg

def headRVSort (k : ℕ) : Fin (k + 1) → SortTag :=
  productTuple (fun _ : Fin k => .vf) (fun _ : Fin 1 => .rv)

/-- A definable finite family of nonzero RV classes over each VF head
admits a representative function definable over the original base.
The graph is allowed a larger domain and is single-valued there. -/
theorem exists_uniform_finiteHead_representatives
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    (hB : VFGammaGeneratedBase B)
    (C : Set (Fin (k + 1) → M)) (hC : DefinableOverBase B (headRVSort k) C)
    (hfin : ∀ a : Fin k → M, {b : Fin 1 → M | productTuple a b ∈ C}.Finite)
    (hnz : ∀ z ∈ C, z (productRight k 1 0) ≠ iRVZero) :
    ∃ U : Set ((Fin (k + 1) → M) × M), RawClosure.Tuple.RelationDefinable B.real U ∧
      RawClosure.Tuple.SingleValued U ∧
      (∀ p ∈ U, iVF p.2 ∧ iRv p.2 = p.1 (productRight k 1 0)) ∧
      ∀ z ∈ C, ∃ x, (z,x) ∈ U := by
  let P : Set ((Fin (k + 1) → M) × M) :=
    {p | iVF p.2 ∧ iRv p.2 = p.1 (productRight k 1 0)}
  have hP : RawClosure.Tuple.RelationDefinable B.real P := by
    change B.real.Definable LRV {z : Fin (k + 1) ⊕ Fin 1 → M | (z ∘ Sum.inl, z (.inr 0)) ∈ P}
    convert rawTupleFibreGuard_definable B.real (fun i : Fin 1 => Sum.inr i)
      (fun i => Sum.inl (productRight k 1 i)) using 1
    ext z
    change (iVF (z (.inr 0)) ∧ iRv (z (.inr 0)) = z (.inl (productRight k 1 0))) ↔
      (∀ i : Fin 1, iVF (z (.inr i)) ∧ iRv (z (.inr i)) = z (.inl (productRight k 1 i)))
    exact ⟨fun h i => by fin_cases i; exact h, fun h => h 0⟩
  obtain ⟨m, c, hc⟩ := hC.specialize
  apply RawClosure.Tuple.definable_choice_graph_over hs B.real (B.real ∪ Set.range (rawTuple c))
    Set.subset_union_left (small_union_range hκ B.real hsmall (rawTuple c)) C hc.raw_definable P hP
  intro z hz
  let a := z ∘ productLeft k 1
  let b := z ∘ productRight k 1
  have he : productTuple a b = z := by
    apply productTuple_ext
    · intro i; exact productTuple_left a b i
    · intro i; exact productTuple_right a b i
  have ha (i : Fin k) : iVF (a i) := by
    simpa only [a, Function.comp_apply, headRVSort, productTuple_left, sortEval, iVF]
      using hC.proper z hz (productLeft k 1 i)
  have hb (i : Fin 1) : iRV (b i) := by
    simpa only [b, Function.comp_apply, headRVSort, productTuple_right, sortEval, iRV]
      using hC.proper z hz (productRight k 1 i)
  let t : CanonicalRV.RVSort M := ⟨b 0, hb 0⟩
  have ht₀ : t ≠ 0 := fun h => hnz z hz ((congrArg Subtype.val h).trans RVOperations.zero_val)
  let T : Base (M := M) := ⟨B.real ∪ Set.range a, B.gamma⟩
  let Treal : Set M := T.real
  have hCT := hC.mono (C := T) Set.subset_union_left (fun _ h => h)
  have hmap : @Set.DefinableMap M LRV (@CanonicalStructure.normalize M sM)
      (Fin 1) (Fin (k + 1)) Treal (productTuple a) := by
    letI : LRV.Structure M := @CanonicalStructure.normalize M sM
    intro j
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective j
    cases i with
    | inl i =>
      change @Set.DefinableFun M LRV (@CanonicalStructure.normalize M sM) (Fin 1) Treal
        (fun u => productTuple a u (productLeft k 1 i))
      have hi : a i ∈ Treal := Or.inr (Set.mem_range_self i)
      simpa only [productTuple_left] using (LRV.definableFun_const (Fin 1) hi)
    | inr i =>
      change @Set.DefinableFun M LRV (@CanonicalStructure.normalize M sM) (Fin 1) Treal
        (fun u => productTuple a u (productRight k 1 i))
      simpa only [productTuple_right] using
        (Set.DefinableFun.proj (A := Treal) LRV (i := i))
  let C' := {u : Fin 1 → M | productTuple a u ∈ C}
  have hC' : DefinableOverBase T (fun _ => .rv) C' := by
    have h := hCT.preimage_real_map (fun _ : Fin 1 => .rv) (productTuple a) hmap
    convert h using 1
    ext u
    exact ⟨fun hu => ⟨hu, fun i => by
      simpa only [headRVSort, productTuple_right] using hC.proper _ hu (productRight k 1 i)⟩, And.left⟩
  have ht : AlgebraicAtBase T .rv t.val :=
    finiteRVCoordinate_algebraic T C' hC' (hfin a) (he.symm ▸ hz) 0
  obtain ⟨x, hx, hrv⟩ := definable_rv_representative_over_head hκ hs h00 B hsmall hB a ha t ht₀ ht
  have hsubset : (B.real ∪ Set.range a) ∪ {t.val} ⊆ B.real ∪ Set.range z := by
    rintro _ ((hy | ⟨i, rfl⟩) | hy)
    · exact Or.inl hy
    · exact Or.inr (Set.mem_range_self (productLeft k 1 i))
    · rw [Set.mem_singleton_iff.mp hy]
      exact Or.inr (Set.mem_range_self (productRight k 1 0))
  refine ⟨x.val, ⟨x.property, congrArg Subtype.val hrv⟩, ?_⟩
  exact (hx.mono hsubset).raw_definable

end SpecialTransformations.Section9
