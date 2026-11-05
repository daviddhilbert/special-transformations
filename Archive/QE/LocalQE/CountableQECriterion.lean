import CountableSaturatedExtension
import QESaturatedExtension
import JohnsonCriterion
import Mathlib.ModelTheory.Skolem

/-! The saturated-embedding criterion for quantifier elimination in a
countable language. Downward Löwenheim–Skolem reduces each existential test
to a countable source; the nonprincipal ultrapower supplies an elementary
target with the required genuine saturation. Compactness then gives one
quantifier-free equivalent uniformly over all models.

The proof uses no saturated-extension existence hypothesis or QE theorem.
The sole theory-specific premise is extension of substructure embeddings.
-/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open scoped FirstOrder

namespace CountableQECriterion

variable {L : FirstOrder.Language.{0, 0}}

/-- A countable set in a structure for a countable language is contained in
a countable elementary substructure, including when the model is finite. -/
theorem exists_countable_elementarySubstructure [Countable L.Symbols]
    {M : Type} [L.Structure M] (s : Set M) (hs : s.Countable) :
    ∃ A : L.ElementarySubstructure M, s ⊆ A ∧ Countable A := by
  classical
  by_cases hM : Cardinal.mk M ≤ Cardinal.aleph0
  · letI : Countable M := Cardinal.mk_le_aleph0_iff.mp hM
    exact ⟨⊤, fun _ _ => ElementarySubstructure.mem_top _, inferInstance⟩
  · obtain ⟨A, hA, hcard⟩ := L.exists_elementarySubstructure_card_eq s
      (Cardinal.aleph0 : Cardinal.{0}) le_rfl
      (by simpa using Cardinal.le_aleph0_iff_set_countable.mpr hs)
      (by simpa only [Cardinal.lift_id, FirstOrder.Language.card] using
        (Cardinal.mk_le_aleph0 : Cardinal.mk L.Symbols ≤ Cardinal.aleph0))
      (by simpa using le_of_not_ge hM)
    refine ⟨A, hA, Cardinal.mk_le_aleph0_iff.mp ?_⟩
    exact le_of_eq (by simpa using hcard)

/-- Restricting the free parameter set introduces no quantifiers. -/
theorem isQF_restrictFreeVar {α β : Type} [DecidableEq α] {n : ℕ}
    {φ : L.BoundedFormula α n} (hφ : φ.IsQF) :
    ∀ f : φ.freeVarFinset → β, (φ.restrictFreeVar f).IsQF := by
  induction hφ with
  | falsum => intro f; exact BoundedFormula.IsQF.falsum
  | of_isAtomic h =>
    cases h with
    | equal t₁ t₂ => intro f; exact (BoundedFormula.IsAtomic.equal _ _).isQF
    | rel R ts => intro f; exact (BoundedFormula.IsAtomic.rel _ _).isQF
  | imp _ _ ih₁ ih₂ => intro f; exact (ih₁ _).imp (ih₂ _)

/-- Substitution of terms for parameters preserves quantifier-freeness. -/
theorem isQF_subst {α β : Type} {n : ℕ} {φ : L.BoundedFormula α n}
    (hφ : φ.IsQF) (f : α → L.Term β) : (φ.subst f).IsQF := by
  induction hφ with
  | falsum => exact BoundedFormula.IsQF.falsum
  | of_isAtomic h =>
    cases h with
    | equal t₁ t₂ => exact (BoundedFormula.IsAtomic.equal _ _).isQF
    | rel R ts => exact (BoundedFormula.IsAtomic.rel _ _).isQF
  | imp _ _ ih₁ ih₂ => exact ih₁.imp ih₂

variable [Countable L.Symbols] {T : L.Theory}

/-- One existential QF statement transfers between tuples of the same QF
type when the parameter index is countable. Only a countable elementary
piece of the source must be embedded into the saturated target. -/
theorem exists_transfer_countable
    (hExt : MarkerBridge.SaturatedEmbeddingExtension T)
    {α : Type} [Countable α] {n : ℕ}
    (θ : L.BoundedFormula α (n + 1)) (hθ : θ.IsQF)
    (M N : Theory.ModelType.{0, 0, 0} T)
    (v : α → M) (xs : Fin n → M) (w : α → N) (ys : Fin n → N)
    (hQF : ∀ ψ : L.BoundedFormula α n, ψ.IsQF →
      (ψ.Realize v xs ↔ ψ.Realize w ys)) :
    θ.ex.Realize v xs → θ.ex.Realize w ys := by
  classical
  intro hex
  obtain ⟨a, ha⟩ := BoundedFormula.realize_ex.mp hex
  let s : Set M := (Set.range v ∪ Set.range xs) ∪ {a}
  have hs : s.Countable :=
    ((Set.countable_range v).union (Set.countable_range xs)).union (Set.countable_singleton a)
  obtain ⟨A, hA, hcount⟩ := exists_countable_elementarySubstructure (L := L) s hs
  letI : Countable A := hcount
  letI : A ⊨ T := (A.subtype.theory_model_iff T).mpr inferInstance
  let vA : α → A := fun i => ⟨v i, hA (Or.inl (Or.inl ⟨i, rfl⟩))⟩
  let xsA : Fin n → A := fun i => ⟨xs i, hA (Or.inl (Or.inr ⟨i, rfl⟩))⟩
  let aA : A := ⟨a, hA (Or.inr (Set.mem_singleton a))⟩
  have hvA : A.subtype ∘ vA = v := rfl
  have hxA : A.subtype ∘ xsA = xs := rfl
  have haA : θ.Realize vA (Fin.snoc xsA aA) := by
    apply (A.subtype.map_boundedFormula θ vA (Fin.snoc xsA aA)).mp
    simpa only [Fin.comp_snoc, hvA, hxA, ElementarySubstructure.subtype_apply] using ha
  have hQFA : ∀ ψ : L.BoundedFormula α n, ψ.IsQF →
      (ψ.Realize vA xsA ↔ ψ.Realize w ys) := by
    intro ψ hψ
    exact (A.subtype.map_boundedFormula ψ vA xsA).symm.trans (hQF ψ hψ)
  let gA : α ⊕ Fin n → A := Sum.elim vA xsA
  let gN : α ⊕ Fin n → N := Sum.elim w ys
  have hker : ∀ t t' : L.Term (α ⊕ Fin n),
      t.realize gA = t'.realize gA ↔ t.realize gN = t'.realize gN := by
    intro t t'
    have h := hQFA (Term.bdEqual t t') (BoundedFormula.IsAtomic.equal t t' |>.isQF)
    simpa only [BoundedFormula.realize_bdEqual, gA, gN] using h
  have hrel : ∀ {k : ℕ} (R : L.Relations k) (ts : Fin k → L.Term (α ⊕ Fin n)),
      Structure.RelMap R (fun i => (ts i).realize gA) ↔
      Structure.RelMap R (fun i => (ts i).realize gN) := by
    intro k R ts
    have h := hQFA (R.boundedFormula ts) (BoundedFormula.IsAtomic.rel R ts |>.isQF)
    simpa only [BoundedFormula.realize_rel, gA, gN] using h
  let S : L.Substructure A := HQEDerive.termSub gA
  let e : S ↪[L] N := HQEDerive.termSubEmb gA gN hker hrel
  let U := CountableSaturatedExtension.CountableUltrapower N
  let d : N ↪ₑ[L] U := CountableSaturatedExtension.CountableUltrapower.diagonal
  letI : U ⊨ T := (d.theory_model_iff T).mp inferInstance
  let f : S ↪[L] U := d.toEmbedding.comp e
  obtain ⟨G, hG⟩ := hExt A U inferInstance inferInstance
    (CountableSaturatedExtension.CountableUltrapower.satAt_of_countable (L := L) (M := N) A)
    S f
  have hvar (i : α ⊕ Fin n) : G (gA i) = d (gN i) := by
    calc
      G (gA i) = f (HQEDerive.termSubMk gA i) := by
        simpa only [HQEDerive.termSubMk_val] using hG (HQEDerive.termSubMk (L := L) gA i)
      _ = d (gN i) := by
        change d (HQEDerive.termSubEmb gA gN hker hrel (HQEDerive.termSubMk gA i)) = _
        rw [HQEDerive.termSubEmb_apply_var]
  have hv : G ∘ vA = d ∘ w := funext fun i => hvar (Sum.inl i)
  have hx : G ∘ xsA = d ∘ ys := funext fun i => hvar (Sum.inr i)
  have hθU := (QESaturatedExtension.embedding_realize_isQF G hθ vA (Fin.snoc xsA aA)).mpr haA
  change θ.Realize (G ∘ vA) (G ∘ Fin.snoc xsA aA) at hθU
  rw [Fin.comp_snoc, hv, hx] at hθU
  apply (d.map_boundedFormula θ.ex w ys).mp
  exact BoundedFormula.realize_ex.mpr ⟨G aA, hθU⟩

/-- Countable parameter indices suffice to test one existential QF step. -/
theorem exists_iff_countable
    (hExt : MarkerBridge.SaturatedEmbeddingExtension T)
    {α : Type} [Countable α] {n : ℕ}
    (θ : L.BoundedFormula α (n + 1)) (hθ : θ.IsQF)
    (M N : Theory.ModelType.{0, 0, 0} T)
    (v : α → M) (xs : Fin n → M) (w : α → N) (ys : Fin n → N)
    (hQF : ∀ ψ : L.BoundedFormula α n, ψ.IsQF →
      (ψ.Realize v xs ↔ ψ.Realize w ys)) :
    θ.ex.Realize v xs ↔ θ.ex.Realize w ys :=
  ⟨exists_transfer_countable hExt θ hθ M N v xs w ys hQF,
    exists_transfer_countable hExt θ hθ N M w ys v xs (fun ψ hψ => (hQF ψ hψ).symm)⟩

/-- A formula uses finitely many free parameters, so the countable test gives
the unrestricted QF-type determinacy needed by compactness. -/
theorem qf_type_determines_exists
    (hExt : MarkerBridge.SaturatedEmbeddingExtension T)
    (α : Type) (n : ℕ) (θ : L.BoundedFormula α (n + 1)) (hθ : θ.IsQF)
    (M N : Theory.ModelType.{0, 0, 0} T)
    (v : α → M) (xs : Fin n → M) (w : α → N) (ys : Fin n → N)
    (hQF : ∀ ψ : L.BoundedFormula α n, ψ.IsQF →
      (ψ.Realize v xs ↔ ψ.Realize w ys)) :
    θ.ex.Realize v xs ↔ θ.ex.Realize w ys := by
  classical
  let β := θ.freeVarFinset
  let θ' : L.BoundedFormula β (n + 1) := θ.restrictFreeVar id
  let v' : β → M := fun b => v b.val
  let w' : β → N := fun b => w b.val
  have hθ' : θ'.IsQF := isQF_restrictFreeVar hθ id
  have hQF' : ∀ ψ : L.BoundedFormula β n, ψ.IsQF →
      (ψ.Realize v' xs ↔ ψ.Realize w' ys) := by
    intro ψ hψ
    let r : β → L.Term α := fun b => Term.var b.val
    have h := hQF (ψ.subst r) (isQF_subst hψ r)
    simpa only [BoundedFormula.realize_subst, r, Term.realize_var] using h
  have hM : θ'.ex.Realize v' xs ↔ θ.ex.Realize v xs := by
    simp only [BoundedFormula.realize_ex]
    exact exists_congr fun a => BoundedFormula.realize_restrictFreeVar v (fun _ => rfl)
  have hN : θ'.ex.Realize w' ys ↔ θ.ex.Realize w ys := by
    simp only [BoundedFormula.realize_ex]
    exact exists_congr fun a => BoundedFormula.realize_restrictFreeVar w (fun _ => rfl)
  exact hM.symm.trans ((exists_iff_countable hExt θ' hθ' M N v' xs w' ys hQF').trans hN)

/-- The saturated embedding criterion yields uniform bounded-formula QE. -/
theorem hasQEb_of_saturatedExtension
    (hExt : MarkerBridge.SaturatedEmbeddingExtension T) : QECriterion.HasQEb T :=
  QECriterion.hasQEb_iff_QEExStep.mpr
    (BoundedQE.qeExStep_theoryIff (qf_type_determines_exists hExt))

/-- Marker’s saturated-model criterion for countable languages with a
constant, proved from compactness, downward Löwenheim–Skolem, and the
countably saturated ultrapower construction. -/
theorem fullQE_of_saturatedExtension (hc : Nonempty (L.Functions 0))
    (hExt : MarkerBridge.SaturatedEmbeddingExtension T) : MarkerBridge.FullQE T := by
  intro α n φ
  obtain ⟨ψ, hψ, heq⟩ := hasQEb_of_saturatedExtension hExt α n φ
  refine ⟨ψ, hψ, ?_⟩
  intro M sM hM v xs
  letI := sM
  letI := hM
  letI : Nonempty M := ⟨Structure.funMap (L := L) (Classical.choice hc) Fin.elim0⟩
  have h := heq (Theory.ModelType.of (T := T) M) v xs
  simpa only [BoundedFormula.realize_iff] using h

end CountableQECriterion

#print axioms CountableQECriterion.exists_countable_elementarySubstructure
#print axioms CountableQECriterion.qf_type_determines_exists
#print axioms CountableQECriterion.hasQEb_of_saturatedExtension
#print axioms CountableQECriterion.fullQE_of_saturatedExtension
