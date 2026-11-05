import Mathlib

set_option linter.style.haveILetI false

open FirstOrder FirstOrder.Language

universe u v

namespace ShoenfieldQE

variable {L : FirstOrder.Language.{u, v}}

/-! ## Quantifier elimination, formula level

`HasQE T` is the formula-level statement that every `L`-formula is `T`-equivalent to a
quantifier-free one.  It has the same shape as `SpecialTransformations.Milestone0.HasQE`
(`Milestone0/Encoding.lean`), only at a general language `L`. -/

/-- `T` admits quantifier elimination. -/
def HasQE (T : L.Theory) : Prop :=
  ∀ (α : Type u) (φ : L.Formula α), ∃ ψ : L.Formula α, ψ.IsQF ∧ T ⊨ᵇ (φ ⇔ ψ)

/-! ## Finite conjunctions and disjunctions -/

section Finite

variable {α : Type u} {β : Type*}

lemma isQF_listFoldr_sup (l : List β) (f : β → L.Formula α) (h : ∀ b ∈ l, (f b).IsQF) :
    (l.map f).foldr (· ⊔ ·) ⊥ |>.IsQF := by
  induction l with
  | nil => exact BoundedFormula.isQF_bot
  | cons a l ih =>
      rw [List.map_cons, List.foldr_cons]
      exact (h a (by simp)).sup (ih (fun b hb => h b (by simp [hb])))

lemma isQF_listFoldr_inf (l : List β) (f : β → L.Formula α)
    (h : ∀ b ∈ l, (f b).IsQF) : (l.map f).foldr (· ⊓ ·) ⊤ |>.IsQF := by
  induction l with
  | nil => exact BoundedFormula.IsQF.top
  | cons a l ih =>
      rw [List.map_cons, List.foldr_cons]
      exact (h a (by simp)).inf (ih (fun b hb => h b (by simp [hb])))

/-- A finite disjunction of quantifier-free formulas is quantifier-free. -/
lemma isQF_iSup {β : Type*} [Finite β] (f : β → L.Formula α) (h : ∀ b, (f b).IsQF) :
    (Formula.iSup f).IsQF := by
  classical
  rw [Formula.iSup, BoundedFormula.iSup]
  exact isQF_listFoldr_sup _ f (fun b _ => h b)

/-- A finite conjunction of quantifier-free formulas is quantifier-free. -/
lemma isQF_iInf {β : Type*} [Finite β] (f : β → L.Formula α) (h : ∀ b, (f b).IsQF) :
    (Formula.iInf f).IsQF := by
  classical
  rw [Formula.iInf, BoundedFormula.iInf]
  exact isQF_listFoldr_inf _ f (fun b _ => h b)

/-- The realization of a finite disjunction of formulas. -/
lemma realize_iSup {β : Type*} [Finite β] (f : β → L.Formula α) {M : Type*} [L.Structure M]
    (v : α → M) : (Formula.iSup f).Realize v ↔ ∃ b, (f b).Realize v :=
  BoundedFormula.realize_iSup

/-- The realization of a finite conjunction of formulas. -/
lemma realize_iInf {β : Type*} [Finite β] (f : β → L.Formula α) {M : Type*} [L.Structure M]
    (v : α → M) : (Formula.iInf f).Realize v ↔ ∀ b, (f b).Realize v :=
  BoundedFormula.realize_iInf

end Finite

/-! ## Compactness for a set of formulas with free variables -/

/-- **Compactness, realization form.** If every finite set of formulas taken from `Γ` can be
realized together with `φ` in a model of `T`, then `Γ` itself can be realized together with `φ`. -/
theorem exists_model_realize_of_finset {α : Type u} {T : L.Theory} {Γ : Set (L.Formula α)}
    {φ : L.Formula α}
    (h : ∀ Γ0 : Finset (L.Formula α), (∀ ψ ∈ Γ0, ψ ∈ Γ) →
      ∃ (M : Theory.ModelType.{u, v, max u v} T) (v : α → M.Carrier),
        (∀ ψ ∈ Γ0, ψ.Realize v) ∧ φ.Realize v) :
    ∃ (M : Theory.ModelType.{u, v, max u v} T) (v : α → M.Carrier),
      (∀ ψ ∈ Γ, ψ.Realize v) ∧ φ.Realize v := by
  classical
  set U : (L[[α]]).Theory :=
    (L.lhomWithConstants α).onTheory T ∪ Formula.equivSentence '' Γ ∪
      {Formula.equivSentence φ} with hUdef
  have hfin : U.IsFinitelySatisfiable := by
    intro U0 hU0
    -- the part of `Γ` that shows up in `U0`
    set Γ0 : Finset (L.Formula α) :=
      (U0.filter (fun s => s ∈ Formula.equivSentence '' Γ)).image
        (fun s => Formula.equivSentence.symm s) with hΓ0def
    have hΓ0 : ∀ ψ ∈ Γ0, ψ ∈ Γ := by
      intro ψ hψ
      obtain ⟨s, hs, hseq⟩ := Finset.mem_image.mp hψ
      obtain ⟨-, hs2⟩ := Finset.mem_filter.mp hs
      obtain ⟨ψ', hψ', hψ'eq⟩ := (Set.mem_image _ _ _).mp hs2
      rw [← hseq, ← hψ'eq, Equiv.symm_apply_apply]
      exact hψ'
    obtain ⟨M, v, hv, hφv⟩ := h Γ0 hΓ0
    letI : (constantsOn α).Structure M.Carrier := constantsOn.structure v
    have hmem : ∀ s ∈ U0, M.Carrier ⊨ s := by
      intro s hs
      have hsU : s ∈ U := hU0 hs
      simp only [hUdef, Set.mem_union, Set.mem_image, Set.mem_singleton_iff] at hsU
      rcases hsU with (hsT | ⟨ψ, hψ, hψs⟩) | hφs
      · exact ((LHom.onTheory_model (L.lhomWithConstants α) T).2 M.is_model).realize_of_mem s hsT
      · rw [← hψs] at hs ⊢
        refine (Formula.realize_equivSentence M.Carrier ψ).2 (hv ψ ?_)
        rw [hΓ0def]
        exact Finset.mem_image.mpr
          ⟨Formula.equivSentence ψ, Finset.mem_filter.mpr ⟨hs, ⟨ψ, hψ, rfl⟩⟩, by simp⟩
      · rw [hφs]
        exact (Formula.realize_equivSentence M.Carrier φ).2 hφv
    haveI : M.Carrier ⊨ (U0 : (L[[α]]).Theory) := ⟨fun s hs => hmem s hs⟩
    exact Theory.Model.isSatisfiable M.Carrier
  obtain ⟨N⟩ := Theory.isSatisfiable_iff_isFinitelySatisfiable.2 hfin
  have hNU : ∀ s ∈ U, N.Carrier ⊨ s := fun s hs => N.is_model.realize_of_mem s hs
  letI : L.Structure N.Carrier := (L.lhomWithConstants α).reduct N.Carrier
  have hNT : N.Carrier ⊨ T :=
    (LHom.onTheory_model (L.lhomWithConstants α) T).1
      ⟨fun s hs => hNU s (by rw [hUdef]; exact Or.inl (Or.inl hs))⟩
  refine ⟨Theory.ModelType.of T N.Carrier, fun a => (L.con a : N.Carrier), ?_, ?_⟩
  · intro ψ hψ
    refine (Formula.realize_equivSentence N.Carrier ψ).1 (hNU _ ?_)
    rw [hUdef]
    exact Or.inl (Or.inr ⟨ψ, hψ, rfl⟩)
  · refine (Formula.realize_equivSentence N.Carrier φ).1 (hNU _ ?_)
    rw [hUdef]
    exact Or.inr rfl

end ShoenfieldQE

/-! ## The quantifier-free bridge

If quantifier-free types determine first-order types in models of `T`, then `T` has quantifier
elimination.  This is the compactness ("hard") direction of Shoenfield's test, in the
saturation-free form: only qf-type invariance is used, no saturated model. -/

namespace ShoenfieldQE

variable {L : FirstOrder.Language.{u, v}}

/-- Packaging two implications into a `⇔`. -/
lemma models_iff_of_models_imp {α : Type u} {T : L.Theory} {φ ψ : L.Formula α}
    (h1 : T ⊨ᵇ (ψ ⟹ φ)) (h2 : T ⊨ᵇ (φ ⟹ ψ)) : T ⊨ᵇ (φ ⇔ ψ) := by
  rw [Theory.models_formula_iff] at h1 h2 ⊢
  intro M v
  rw [Formula.realize_iff]
  exact ⟨fun h => h2 M v h, fun h => h1 M v h⟩

/-- **Isolation step.** Under qf-type invariance, every tuple satisfying `φ` is separated from the
complement of `φ` by a quantifier-free formula which provably implies `φ`. -/
theorem exists_qf_imp_of_realize {α : Type u} {T : L.Theory} {φ : L.Formula α}
    (H : ∀ (M N : Theory.ModelType.{u, v, max u v} T) (v : α → M.Carrier) (w : α → N.Carrier),
      (∀ ψ : L.Formula α, ψ.IsQF → (ψ.Realize v ↔ ψ.Realize w)) →
      (φ.Realize v ↔ φ.Realize w))
    (M : Theory.ModelType.{u, v, max u v} T) (v : α → M.Carrier) (hv : φ.Realize v) :
    ∃ ψ : L.Formula α, ψ.IsQF ∧ ψ.Realize v ∧ T ⊨ᵇ (ψ ⟹ φ) := by
  classical
  by_contra hcon
  push Not at hcon
  set Γ : Set (L.Formula α) := {ψ | ψ.IsQF ∧ ψ.Realize v} with hΓdef
  have hfin : ∀ Γ0 : Finset (L.Formula α), (∀ ψ ∈ Γ0, ψ ∈ Γ) →
      ∃ (N : Theory.ModelType.{u, v, max u v} T) (w : α → N.Carrier),
        (∀ ψ ∈ Γ0, ψ.Realize w) ∧ φ.not.Realize w := by
    intro Γ0 hΓ0
    have hq : ∀ ψ : ↥Γ0, ((ψ : L.Formula α)).IsQF := fun ψ => (hΓ0 ψ.1 ψ.2).1
    have hr : ∀ ψ : ↥Γ0, ((ψ : L.Formula α)).Realize v := fun ψ => (hΓ0 ψ.1 ψ.2).2
    have hnot : ¬ T ⊨ᵇ (Formula.iInf (fun ψ : ↥Γ0 => (ψ : L.Formula α)) ⟹ φ) :=
      hcon _ (isQF_iInf _ hq) ((realize_iInf _ v).2 hr)
    rw [Theory.models_formula_iff] at hnot
    rw [not_forall] at hnot
    obtain ⟨N, hnot⟩ := hnot
    rw [not_forall] at hnot
    obtain ⟨w, hnot⟩ := hnot
    simp only [Formula.realize_imp, Classical.not_imp] at hnot
    refine ⟨N, w, ?_, ?_⟩
    · intro ψ hψ
      exact (realize_iInf _ w).1 hnot.1 ⟨ψ, hψ⟩
    · exact (Formula.realize_not).2 hnot.2
  obtain ⟨N, w, hw, hnφ⟩ := exists_model_realize_of_finset hfin
  have htypes : ∀ ψ : L.Formula α, ψ.IsQF → (ψ.Realize v ↔ ψ.Realize w) := by
    intro ψ hψ
    constructor
    · intro hvψ
      exact hw ψ ⟨hψ, hvψ⟩
    · intro hwψ
      by_contra hvψ
      have hcontr := hw ψ.not ⟨hψ.not, (Formula.realize_not).2 hvψ⟩
      rw [Formula.realize_not] at hcontr
      exact hcontr hwψ
  have hiff := H M N v w htypes
  rw [Formula.realize_not] at hnφ
  exact hnφ (hiff.mp hv)

/-- **Shoenfield's hard direction**, saturation-free form: if quantifier-free types determine
first-order types in models of `T`, then every formula is `T`-equivalent to a quantifier-free
one. -/
theorem hasQE_of_qf_type {T : L.Theory}
    (H : ∀ (α : Type u) (φ : L.Formula α) (M N : Theory.ModelType.{u, v, max u v} T)
      (v : α → M.Carrier) (w : α → N.Carrier),
      (∀ ψ : L.Formula α, ψ.IsQF → (ψ.Realize v ↔ ψ.Realize w)) →
      (φ.Realize v ↔ φ.Realize w)) :
    HasQE T := by
  intro α φ
  classical
  set Ψ : Set (L.Formula α) := {ψ | ψ.IsQF ∧ T ⊨ᵇ (ψ ⟹ φ)} with hΨdef
  have hcov : ∃ Ψ0 : Finset (L.Formula α), (∀ ψ ∈ Ψ0, ψ ∈ Ψ) ∧
      T ⊨ᵇ (φ ⟹ Formula.iSup (fun ψ : ↥Ψ0 => (ψ : L.Formula α))) := by
    by_contra hno
    push Not at hno
    set Γ : Set (L.Formula α) := {η | ∃ ψ ∈ Ψ, ψ.not = η} with hΓdef
    have hfin : ∀ Γ0 : Finset (L.Formula α), (∀ η ∈ Γ0, η ∈ Γ) →
        ∃ (M : Theory.ModelType.{u, v, max u v} T) (v : α → M.Carrier),
          (∀ η ∈ Γ0, η.Realize v) ∧ φ.Realize v := by
      intro Γ0 hΓ0
      -- choose, for each `η ∈ Γ0`, a qf formula in `Ψ` whose negation is `η`
      set f : ↥Γ0 → L.Formula α := fun η => (hΓ0 η.1 η.2).choose with hfdef
      have hf_mem : ∀ η : ↥Γ0, f η ∈ Ψ := fun η => (hΓ0 η.1 η.2).choose_spec.1
      have hf_eq : ∀ η : ↥Γ0, (f η).not = η.1 := fun η => (hΓ0 η.1 η.2).choose_spec.2
      set Ψ0 : Finset (L.Formula α) := (Finset.univ : Finset ↥Γ0).image f with hΨ0def
      have hΨ0 : ∀ ψ ∈ Ψ0, ψ ∈ Ψ := by
        intro ψ hψ
        obtain ⟨η, -, rfl⟩ := Finset.mem_image.mp hψ
        exact hf_mem η
      have hnot : ¬ T ⊨ᵇ (φ ⟹ Formula.iSup (fun ψ : ↥Ψ0 => (ψ : L.Formula α))) := hno Ψ0 hΨ0
      rw [Theory.models_formula_iff] at hnot
      rw [not_forall] at hnot
      obtain ⟨M, hnot⟩ := hnot
      rw [not_forall] at hnot
      obtain ⟨v, hnot⟩ := hnot
      simp only [Formula.realize_imp, Classical.not_imp] at hnot
      have hnone : ∀ ψ : ↥Ψ0, ¬ ((ψ : L.Formula α)).Realize v := by
        intro ψ hreal
        exact hnot.2 ((realize_iSup (fun ψ : ↥Ψ0 => (ψ : L.Formula α)) v).2 ⟨ψ, hreal⟩)
      refine ⟨M, v, ?_, hnot.1⟩
      intro η hη
      have hψ0 : f ⟨η, hη⟩ ∈ Ψ0 :=
        Finset.mem_image.mpr ⟨⟨η, hη⟩, Finset.mem_univ _, rfl⟩
      have h1 : ¬ (f ⟨η, hη⟩).Realize v := hnone ⟨f ⟨η, hη⟩, hψ0⟩
      have heq : (⟨η, hη⟩ : ↥Γ0).1.Realize v ↔ ¬ (f ⟨η, hη⟩).Realize v := by
        rw [← hf_eq ⟨η, hη⟩, Formula.realize_not]
      exact heq.mpr h1
    obtain ⟨M, v, hv, hφv⟩ := exists_model_realize_of_finset hfin
    obtain ⟨ψ, hqf, hvψ, himp⟩ := exists_qf_imp_of_realize (H α φ) M v hφv
    have hmem : ψ ∈ Ψ := ⟨hqf, himp⟩
    have hnot : ψ.not ∈ Γ := by
      rw [hΓdef]
      exact ⟨ψ, hmem, rfl⟩
    have hcontr := hv ψ.not hnot
    rw [Formula.realize_not] at hcontr
    exact hcontr hvψ
  obtain ⟨Ψ0, hΨ0, hcov⟩ := hcov
  have himp : T ⊨ᵇ (Formula.iSup (fun ψ : ↥Ψ0 => (ψ : L.Formula α)) ⟹ φ) := by
    rw [Theory.models_formula_iff]
    intro M v hsup
    obtain ⟨η, hη⟩ := (realize_iSup (fun ψ : ↥Ψ0 => (ψ : L.Formula α)) v).1 hsup
    exact (Theory.models_formula_iff.1 (hΨ0 η.1 η.2).2) M v hη
  exact ⟨Formula.iSup (fun ψ : ↥Ψ0 => (ψ : L.Formula α)),
    isQF_iSup _ (fun ψ => (hΨ0 ψ.1 ψ.2).1), models_iff_of_models_imp himp hcov⟩

end ShoenfieldQE

/-! ## The criterion is an equivalence

Quantifier elimination implies qf-type invariance (the easy direction), so
`hasQE_of_qf_type` is an exact criterion, not just a sufficient condition. -/

namespace ShoenfieldQE

variable {L : FirstOrder.Language.{u, v}}

/-- The easy direction: quantifier elimination makes quantifier-free types determine all types. -/
theorem qf_type_of_hasQE {T : L.Theory} (h : HasQE T) :
    ∀ (α : Type u) (φ : L.Formula α) (M N : Theory.ModelType.{u, v, max u v} T)
      (v : α → M.Carrier) (w : α → N.Carrier),
      (∀ ψ : L.Formula α, ψ.IsQF → (ψ.Realize v ↔ ψ.Realize w)) →
      (φ.Realize v ↔ φ.Realize w) := by
  intro α φ M N v w htypes
  obtain ⟨ψ, hqf, heq⟩ := h α φ
  have hM : ψ.Realize v ↔ ψ.Realize w := htypes ψ hqf
  have hv := (Theory.models_formula_iff.1 heq) M v
  have hw := (Theory.models_formula_iff.1 heq) N w
  rw [Formula.realize_iff] at hv hw
  exact hv.trans (hM.trans hw.symm)

/-- **Shoenfield's test**, saturation-free: `T` has quantifier elimination exactly when
quantifier-free types determine first-order types in models of `T`. -/
theorem hasQE_iff_qf_type {T : L.Theory} :
    HasQE T ↔
      (∀ (α : Type u) (φ : L.Formula α) (M N : Theory.ModelType.{u, v, max u v} T)
        (v : α → M.Carrier) (w : α → N.Carrier),
        (∀ ψ : L.Formula α, ψ.IsQF → (ψ.Realize v ↔ ψ.Realize w)) →
        (φ.Realize v ↔ φ.Realize w)) :=
  ⟨qf_type_of_hasQE, hasQE_of_qf_type⟩

end ShoenfieldQE

#print axioms ShoenfieldQE.models_iff_of_models_imp
#print axioms ShoenfieldQE.exists_model_realize_of_finset
#print axioms ShoenfieldQE.isQF_iSup
#print axioms ShoenfieldQE.exists_qf_imp_of_realize
#print axioms ShoenfieldQE.hasQE_of_qf_type
#print axioms ShoenfieldQE.qf_type_of_hasQE
#print axioms ShoenfieldQE.hasQE_iff_qf_type
