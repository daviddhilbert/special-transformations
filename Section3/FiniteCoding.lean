module

public import Section3.RawBarycentricCode
public import Section3.SortedTuples
public import Section3.CanonicalContext

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.FiniteCoding
open Barycentre RawClosure.Tuple
variable {M : Type} [LRV.Structure M]

def values {n : ℕ} (a : Fin n → VFType (M := M)) : Fin n → M := fun i => (a i).val

theorem values_injective {n : ℕ} : Function.Injective (values (M := M) (n := n)) := by
  intro a b hab
  funext i
  exact Subtype.ext (congrFun hab i)

def graphSort {n m : ℕ} : Fin (n + m) → SortTag :=
  Sum.elim (fun _ : Fin n => .vf) (fun _ : Fin m => .rv) ∘ finSumFinEquiv.symm

def graph {n m : ℕ} (A : Set (Fin n → VFType (M := M))) (f : A → Fin m → M) :
    Set (Fin (n + m) → M) :=
  {z | ∃ a : A, values a.val = z ∘ finSumFinEquiv ∘ Sum.inl ∧
    f a = z ∘ finSumFinEquiv ∘ Sum.inr}

theorem graph_sorted {n m : ℕ} (A : Set (Fin n → VFType (M := M)))
    (f : A → Fin m → M) (hf : ∀ a j, iRV (f a j)) :
    ∀ z ∈ graph A f, ∀ i, sortEval (graphSort (n := n) (m := m) i) (z i) := by
  rintro z ⟨a, hx, hy⟩ i
  change sortEval (Sum.elim (fun _ : Fin n => .vf) (fun _ : Fin m => .rv)
    (finSumFinEquiv.symm i)) (z i)
  cases h : finSumFinEquiv.symm i with
  | inl j =>
    have hi : finSumFinEquiv (Sum.inl j) = i :=
      (congrArg finSumFinEquiv h).symm.trans (finSumFinEquiv.apply_symm_apply i)
    have hxj := congrFun hx j
    change (a.val j).val = z (finSumFinEquiv (.inl j)) at hxj
    rw [hi] at hxj
    change iVF (z i)
    rw [← hxj]
    exact (a.val j).property
  | inr j =>
    have hi : finSumFinEquiv (Sum.inr j) = i :=
      (congrArg finSumFinEquiv h).symm.trans (finSumFinEquiv.apply_symm_apply i)
    have hyj := congrFun hy j
    change f a j = z (finSumFinEquiv (.inr j)) at hyj
    rw [hi] at hyj
    change iRV (z i)
    rw [← hyj]
    exact hf a j

theorem projection_definable (S : Set M) {n : ℕ} (A : Set (Fin n → VFType (M := M)))
    (hA : S.Definable LRV (values '' A)) (i : Fin n) :
    S.Definable₁ LRV {b | ∃ a ∈ A, (a i).val = b} := by
  change S.Definable LRV {z : Fin 1 → M | ∃ a ∈ A, (a i).val = z 0}
  have h := hA.image_comp (fun _ : Fin 1 => i)
  convert h using 1
  ext z
  constructor
  · rintro ⟨a, ha, hai⟩
    refine ⟨values a, ⟨a, ha, rfl⟩, ?_⟩
    funext j
    fin_cases j
    exact hai
  · rintro ⟨v, ⟨a, ha, rfl⟩, hv⟩
    exact ⟨a, ha, congrFun hv 0⟩

variable [hM : M ⊨ Axioms.ACVF]

/-- The full finite-tuple coding construction on the canonical representation.
All coordinates are coded uniformly at depth card(A), over the original S. -/
theorem finite_coding_canonical (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (S : Set M) {n : ℕ}
    (A : Set (Fin n → VFType (M := M))) (hfin : A.Finite)
    (hA : DefinableOver S (fun _ => .vf) (values '' A)) :
    ∃ m : ℕ, ∃ f : A → Fin m → M, Function.Injective f ∧
      (∀ a j, iRV (f a j)) ∧ DefinableOver S graphSort (graph A f) := by
  let d := A.ncard
  let D (i : Fin n) : Finset (VFType (M := M)) := (hfin.image (fun a => a i)).toFinset
  let F (i : Fin n) (_ : Fin 0 → M) := D i
  have hcard (i : Fin n) : (D i).card ≤ d := by
    change (hfin.image (fun a => a i)).toFinset.card ≤ A.ncard
    rw [← Set.ncard_eq_toFinset_card _ (hfin.image (fun a => a i))]
    exact Set.ncard_image_le hfin
  have hmem (i : Fin n) (a : A) : a.val i ∈ D i :=
    (Set.Finite.mem_toFinset (hfin.image (fun a => a i))).mpr ⟨a.val, a.property, rfl⟩
  have hF (i : Fin n) : RelationDefinable S (finiteFibreRelation (F i)) := by
    have hp := (projection_definable S A hA.raw_definable i).preimage_comp
      (Sum.inr : Fin 1 → Fin 0 ⊕ Fin 1)
    change S.Definable LRV _
    convert hp using 1
    ext w
    change (∃ x ∈ D i, x.val = w (.inr 0)) ↔ ∃ a ∈ A, (a i).val = w (.inr 0)
    constructor
    · rintro ⟨x, hx, he⟩
      obtain ⟨a, ha, hai⟩ := (Set.Finite.mem_toFinset (hfin.image (fun a => a i))).mp hx
      refine ⟨a, ha, ?_⟩
      exact (congrArg Subtype.val hai).trans he
    · rintro ⟨a, ha, he⟩
      exact ⟨a i, (Set.Finite.mem_toFinset (hfin.image (fun a => a i))).mpr ⟨a, ha, rfl⟩, he⟩
  have hcoord (i : Fin n) (j : Fin d) : S.DefinableFun LRV
      (fun z : Fin n → M => rawCode d (F i) Fin.elim0 (z i) j) := by
    have hh := rawCode_definable h00 S d (F i) (hF i) d (fun _ => hcard i) j
    exact hh.comp (show S.DefinableMap LRV
      (fun z : Fin n → M => Sum.elim Fin.elim0 (fun _ : Fin 1 => z i)) from by
      intro u
      cases u with
      | inl k => exact k.elim0
      | inr k => exact Set.DefinableFun.proj LRV)
  let f (a : A) (k : Fin (n * d)) : M :=
    rawCode d (F (finProdFinEquiv.symm k).1) Fin.elim0
      (a.val (finProdFinEquiv.symm k).1).val (finProdFinEquiv.symm k).2
  have hsort (a : A) (k : Fin (n * d)) : iRV (f a k) := by
    dsimp only [f]
    rw [rawCode_eq_code]
    exact code_sorted _ _ _ _
  have hinj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    funext i
    apply code_injective_of_card_le h00 d (D i) ((hcard i).trans (Nat.le_succ d))
      (hmem i a) (hmem i b)
    funext j
    have h := congrFun hab (finProdFinEquiv (i, j))
    simpa only [f, Equiv.symm_apply_apply, rawCode_eq_code] using h
  let e : Fin n ⊕ Fin (n * d) ≃ Fin (n + n * d) := finSumFinEquiv
  let input (z : Fin (n + n * d) → M) := z ∘ e ∘ Sum.inl
  have hinput : S.DefinableMap LRV input := by
    intro i
    change S.DefinableFun LRV (fun z => z (e (.inl i)))
    exact Set.DefinableFun.proj LRV
  have hpred (k : Fin (n * d)) : S.Definable LRV
      {z : Fin (n + n * d) → M | z (e (.inr k)) =
        rawCode d (F (finProdFinEquiv.symm k).1) Fin.elim0
          (input z (finProdFinEquiv.symm k).1) (finProdFinEquiv.symm k).2} :=
    (Set.DefinableFun.proj (L := LRV) (A := S) (i := e (.inr k))).ofPred_eq
      ((hcoord (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2).comp hinput)
  have hraw : S.Definable LRV (graph A f) := by
    have hg := (hA.raw_definable.preimage_map hinput).inter
      (Set.definable_iInter_of_finite hpred)
    convert hg using 1
    ext z
    simp only [graph, Set.mem_inter_iff, Set.mem_preimage, Set.mem_iInter, Set.mem_ofPred_eq]
    change (∃ a : A, values a.val = input z ∧ f a = z ∘ e ∘ Sum.inr) ↔
      input z ∈ values '' A ∧ ∀ k, z (e (.inr k)) =
        rawCode d (F (finProdFinEquiv.symm k).1) Fin.elim0
          (input z (finProdFinEquiv.symm k).1) (finProdFinEquiv.symm k).2
    constructor
    · rintro ⟨a, hx, hy⟩
      refine ⟨⟨a.val, a.property, hx⟩, ?_⟩
      intro k
      rw [← congrFun hx (finProdFinEquiv.symm k).1]
      exact (congrFun hy k).symm
    · rintro ⟨⟨a, ha, hx⟩, hy⟩
      refine ⟨⟨a, ha⟩, hx, ?_⟩
      funext k
      change rawCode d (F (finProdFinEquiv.symm k).1) Fin.elim0
        (a (finProdFinEquiv.symm k).1).val (finProdFinEquiv.symm k).2 = z (e (.inr k))
      have hv : (a (finProdFinEquiv.symm k).1).val = input z (finProdFinEquiv.symm k).1 :=
        congrFun hx (finProdFinEquiv.symm k).1
      exact (congrArg (fun v : M => rawCode d (F (finProdFinEquiv.symm k).1)
        Fin.elim0 v (finProdFinEquiv.symm k).2) hv).trans (hy k).symm
  exact ⟨n * d, f, hinj, hsort,
    raw_definableOver_sorted hc S graphSort (graph A f) hraw (graph_sorted A f hsort)⟩

end SpecialTransformations.Section3.FiniteCoding

namespace SpecialTransformations.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- Lemma 3.9 in every ACVF(0,0) model, for all finite VF tuple arities and
the original arbitrary base. The conclusion includes the complete sorted
definable graph; no elements of A are named as additional parameters. -/
theorem lemma_3_9 (h00 : M ⊨ Axioms.ACVF00) (S : Set M) {n : ℕ}
    (A : Set (Fin n → VFType (M := M))) (hfin : A.Finite)
    (hA : DefinableOver S (fun _ => .vf) (FiniteCoding.values '' A)) :
    ∃ m : ℕ, ∃ f : A → Fin m → M, Function.Injective f ∧
      (∀ a j, iRV (f a j)) ∧
      DefinableOver S FiniteCoding.graphSort (FiniteCoding.graph A f) := by
  let N := CanonicalStructure.normalize (M := M)
  letI := sM
  have hN : @Theory.Model LRV M N Axioms.ACVF := CanonicalStructure.normalized_model hM
  have hN00 : @Theory.Model LRV M N Axioms.ACVF00 := normalized_model00 h00
  have hc : @CanonicalStructure.IsCanonical M N := CanonicalStructure.normalize_isCanonical
  have hAN : @DefinableOver M N S n (fun _ => .vf) (FiniteCoding.values '' A) :=
    (definableOver_normalize_iff S _ _).mpr hA
  obtain ⟨m, f, hf, hs, hg⟩ :=
    @FiniteCoding.finite_coding_canonical M N hN hc hN00 S n A hfin hAN
  exact ⟨m, f, hf, hs, (definableOver_normalize_iff S _ _).mp hg⟩

end SpecialTransformations.Section3
