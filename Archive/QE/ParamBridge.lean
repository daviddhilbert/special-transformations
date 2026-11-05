/-
**The parameter bridge, forward half: `hasQE_of_hasQE_empty`** — the construction is swarm
`smw1bwjo2` m2's; the two remaining elaboration errors (the `rw`/`Function.comp_apply` order in
`hleft`'s `Sum.inr` case, and the argument order in the `shrinkAux`/`realize_shrinkAux` calls) were
closed here.  Verified: compiled, 0 errors, no `sorry`,
`hasQE_of_hasQE_empty_aux : ∀ T, HasQEempty T → HasQE T` with axioms within
{propext, Classical.choice, Quot.sound}.

Why this is the item the tree wanted: the frozen `HasQE` (and `qc.tex`'s Theorem 2.3) quantifies over
*every* parameter type `α` and every variable context `Fin n`, while the routes through the QF-type
assembly naturally produce QE only at the empty parameter context and then have to move a formula
across the parameter/variable distinction.  This file does that:

1. shrink the parameter type to the finite support of the formula (`ParamSupport.support`,
   `realize_congr`), adjoining one witness per occurring sort so that `sα (V (g a)) = sα a` holds for
   *every* parameter `a`, not just those in the support;
2. promote the parameters to leading variables by `g` (`ParamBridgeRelabel.wellSorted_relabel`), so
   the hypothesis `HasQEempty` — QE at the empty parameter context with an arbitrary variable
   context — applies at the enlarged context `card + n`;
3. shrink back with `ParamShrink.shrinkAux` (quantifier-free, hence `ParamSortTransport`'s
   `wellSorted_shrink_of_isQF`), and transport the truth values with `realize_relabel`,
   `realize_congr` and `realize_shrinkAux`.

`HasQEempty` is QE at the empty *parameter* type only — strictly weaker than `HasQE`, which is the
point: the RV-side work can be done for sentences and the parameters are free.
-/
/-
**The parameter bridge, forward half**: quantifier elimination at the empty parameter context
(`α = Empty`, arbitrary variable context) implies the frozen `HasQE` at all parameter types.

The forward direction is the relabel that turns the finite support of a formula into the leading
free variables (`wellSorted_relabel`); the witness is brought back with W4's `shrinkAux`.
-/
import ParamSupport
import ParamSortTransport
import ParamBridgeRelabel

open FirstOrder FirstOrder.Language
open scoped FirstOrder

namespace SpecialTransformations
namespace Milestone0
namespace ParamBridge

open LRV

set_option maxHeartbeats 2000000

/-- **Quantifier elimination at the empty parameter context**: every well-sorted formula of `L_RV`
with no parameters is `T`-equivalent, at sorted tuples, to a quantifier-free well-sorted formula. -/
def HasQEempty (T : LRV.Theory) : Prop :=
  ∀ (k : ℕ) (sk : Fin k → SortTag) (φ : LRV.BoundedFormula Empty k),
    WellSorted (fun e : Empty => e.elim) sk φ →
    ∃ ψ : LRV.BoundedFormula Empty k, ψ.IsQF ∧ WellSorted (fun e : Empty => e.elim) sk ψ ∧
      ∀ (M : Type) [LRV.Structure M], M ⊨ T → ∀ (x : Fin k → M),
        (∀ i, sortEval (sk i) (x i)) →
        (φ.Realize (fun e : Empty => e.elim) x ↔ ψ.Realize (fun e : Empty => e.elim) x)

/-! ### `IsQF` is preserved by the shrink -/

theorem isQF_of_imp {k : ℕ} {φ ψ : LRV.BoundedFormula Empty k} (h : (φ.imp ψ).IsQF) :
    φ.IsQF ∧ ψ.IsQF := by
  cases h with
  | imp h1 h2 => exact ⟨h1, h2⟩
  | of_isAtomic h => cases h

theorem isQF_shrinkAux {γ : Type} {m : ℕ} (V : Fin m → γ) :
    ∀ (k : ℕ) (χ : LRV.BoundedFormula Empty (m + (n + k))),
      χ.IsQF → (W4.shrinkAux (n := n) V k χ).IsQF
  | _, .falsum, _ => by simp only [W4.shrinkAux]; exact BoundedFormula.IsQF.falsum
  | _, .equal t u, _ => by
      simp only [W4.shrinkAux]
      exact BoundedFormula.IsQF.of_isAtomic (BoundedFormula.IsAtomic.equal _ _)
  | _, .rel R ts, _ => by
      simp only [W4.shrinkAux]
      exact BoundedFormula.IsQF.of_isAtomic (BoundedFormula.IsAtomic.rel _ _)
  | k, .imp a b, h => by
      simp only [W4.shrinkAux]
      obtain ⟨h1, h2⟩ := isQF_of_imp h
      exact BoundedFormula.IsQF.imp (isQF_shrinkAux V k a h1) (isQF_shrinkAux V k b h2)
  | _, .all χ, h => absurd h (BoundedFormula.not_all_isQF χ)

/-! ### The sorts of the shrink -/

theorem sortAssem_comp_gVar {γ : Type} {m : ℕ} (V : Fin m → γ) (sα : γ → SortTag)
    (snT : Fin n → SortTag) :
    sortAssem (m := m) (fun j => sα (V j)) snT
      = fun i => Sum.elim sα snT (W4.gVar V 0 i) := by
  funext i
  induction i using Fin.addCases with
  | left j =>
      show sortAssem (m := m) (fun j => sα (V j)) snT (Fin.castAdd n j)
        = Sum.elim sα snT (W4.gVar V 0 (Fin.castAdd n j))
      rw [sortAssem_castAdd, W4.gVar_of_lt V 0 _ j.isLt]
      rfl
  | right j =>
      show sortAssem (m := m) (fun j => sα (V j)) snT (Fin.natAdd m j)
        = Sum.elim sα snT (W4.gVar V 0 (Fin.natAdd m j))
      rw [sortAssem_natAdd, W4.gVar_of_ge V 0 _ (by simp)]
      congr 1
      exact Fin.ext (by simp only [Fin.val_natAdd]; omega)

/-! ### The support enumeration -/

theorem hasQE_of_hasQE_empty_aux (T : LRV.Theory) (h : HasQEempty T) :
    HasQE T := by
  intro α sα n sn φ hφ
  classical
  set S0 : Finset α := support φ with hS0
  set wf : Finset α := (if h : ∃ a : α, sα a = .vf then {Classical.choose h} else ∅) with hwf
  set wr : Finset α := (if h : ∃ a : α, sα a = .rv then {Classical.choose h} else ∅) with hwr
  set T0 : Finset α := S0 ∪ wf ∪ wr with hT0
  have mem_wf : ∀ (hv : ∃ a : α, sα a = .vf), Classical.choose hv ∈ T0 := by
    intro hv
    have h1 : wf = {Classical.choose hv} := by
      rw [hwf, dif_pos hv]
    rw [hT0, h1]
    exact Finset.mem_union.2 (Or.inl (Finset.mem_union.2 (Or.inr (Finset.mem_singleton_self _))))
  have mem_wr : ∀ (hv : ∃ a : α, sα a = .rv), Classical.choose hv ∈ T0 := by
    intro hv
    have h1 : wr = {Classical.choose hv} := by
      rw [hwr, dif_pos hv]
    rw [hT0, h1]
    exact Finset.mem_union.2 (Or.inr (Finset.mem_singleton_self _))
  -- the enumeration of the support
  let e : ↥T0 ≃ Fin (Fintype.card ↥T0) := Fintype.equivFin T0
  let V : Fin (Fintype.card ↥T0) → α := fun j => (e.symm j).1
  have V_e : ∀ (a : α) (ha : a ∈ T0), V (e ⟨a, ha⟩) = a := by
    intro a ha
    show (e.symm (e ⟨a, ha⟩)).1 = a
    rw [Equiv.symm_apply_apply]
  -- the parameter map into the leading free variables
  have exists_rv : ∀ a : α, ¬ sα a = .vf → ∃ b : α, sα b = .rv := by
    intro a ha
    rcases h : sα a with _ | _
    · exact absurd h ha
    · exact ⟨a, h⟩
  let g : α → Empty ⊕ Fin (Fintype.card ↥T0) := fun a =>
    if ha : a ∈ T0 then Sum.inr (e ⟨a, ha⟩)
    else if hs : sα a = .vf then Sum.inr (e ⟨Classical.choose ⟨a, hs⟩, mem_wf ⟨a, hs⟩⟩)
    else Sum.inr (e ⟨Classical.choose (exists_rv a hs), mem_wr (exists_rv a hs)⟩)
  -- the sort of the image of a parameter
  have g_sort : ∀ (a : α) (j : Fin (Fintype.card ↥T0)), g a = Sum.inr j → sα (V j) = sα a := by
    intro a j hj
    by_cases ha : a ∈ T0
    · have hga : g a = Sum.inr (e ⟨a, ha⟩) := dif_pos ha
      rw [hga] at hj
      have hje : e ⟨a, ha⟩ = j := by simpa using hj
      subst hje
      rw [V_e a ha]
    · by_cases hs : sα a = .vf
      · have hga : g a = Sum.inr (e ⟨Classical.choose ⟨a, hs⟩, mem_wf ⟨a, hs⟩⟩) := by
          rw [show g a = (if hs : sα a = .vf then Sum.inr (e ⟨Classical.choose ⟨a, hs⟩,
            mem_wf ⟨a, hs⟩⟩) else Sum.inr (e ⟨Classical.choose (exists_rv a hs),
              mem_wr (exists_rv a hs)⟩)) from dif_neg ha]
          exact dif_pos hs
        rw [hga] at hj
        have hje : e ⟨Classical.choose ⟨a, hs⟩, mem_wf ⟨a, hs⟩⟩ = j := by simpa using hj
        subst hje
        rw [V_e, Classical.choose_spec (⟨a, hs⟩ : ∃ b : α, sα b = .vf), hs]
      · have hga : g a = Sum.inr (e ⟨Classical.choose (exists_rv a hs),
            mem_wr (exists_rv a hs)⟩) := by
          rw [show g a = (if hs : sα a = .vf then Sum.inr (e ⟨Classical.choose ⟨a, hs⟩,
            mem_wf ⟨a, hs⟩⟩) else Sum.inr (e ⟨Classical.choose (exists_rv a hs),
              mem_wr (exists_rv a hs)⟩)) from dif_neg ha]
          exact dif_neg hs
        rw [hga] at hj
        have hje : e ⟨Classical.choose (exists_rv a hs), mem_wr (exists_rv a hs)⟩ = j := by
          simpa using hj
        subst hje
        have hrv : sα a = .rv := by
          rcases h : sα a with _ | _
          · exact absurd h hs
          · rfl
        rw [V_e, Classical.choose_spec (exists_rv a hs), hrv]
  have hg : ∀ a : α, (∀ b' : Empty, g a = Sum.inl b' → (fun e : Empty => e.elim) b' = sα a) ∧
      (∀ j : Fin (Fintype.card ↥T0), g a = Sum.inr j → (fun j => sα (V j)) j = sα a) := by
    intro a
    constructor
    · intro b' _
      exact nomatch b'
    · intro j hj
      exact g_sort a j hj
  -- the forward relabel
  have hws : WellSorted (fun e : Empty => e.elim) (sortAssem (m := Fintype.card ↥T0) (fun j => sα (V j)) sn)
      (φ.relabel g) :=
    wellSorted_relabel g sα (fun e : Empty => e.elim) (fun j => sα (V j)) hg hφ
  obtain ⟨ψ₁, hQF₁, hWS₁, hEquiv₁⟩ := h (Fintype.card ↥T0 + n)
    (sortAssem (m := Fintype.card ↥T0) (fun j => sα (V j)) sn) (φ.relabel g) hws
  refine ⟨@W4.shrinkAux α (Fintype.card ↥T0) n V 0 ψ₁, isQF_shrinkAux V 0 ψ₁ hQF₁, ?_, ?_⟩
  · have hsh := W4.wellSorted_shrink_of_isQF (n := n) V sα 0 sn ψ₁ hQF₁ ?_
    · convert hsh using 2
    · rw [← sortAssem_comp_gVar]
      exact hWS₁
  · intro M _ hM v x hv hx
    have hsort : ∀ i : Fin (Fintype.card ↥T0 + n),
        sortEval ((sortAssem (m := Fintype.card ↥T0) (fun j => sα (V j)) sn) i)
          (Fin.append (fun j => v (V j)) x i) := by
      intro i
      induction i using Fin.addCases with
      | left j =>
          rw [sortAssem_castAdd, Fin.append_left]
          exact hv (V j)
      | right j =>
          rw [sortAssem_natAdd, Fin.append_right]
          exact hx j
    have step1 : ((φ.relabel g).Realize (fun e : Empty => e.elim)
        (Fin.append (fun j => v (V j)) x) ↔ φ.Realize v x) := by
      rw [BoundedFormula.realize_relabel]
      have hleft : (Sum.elim (fun e : Empty => e.elim)
          ((Fin.append (fun j => v (V j)) x) ∘ Fin.castAdd n)) ∘ g
          = fun a => v (V (Sum.elim (fun e : Empty => nomatch e) (fun j => j) (g a))) := by
        funext a
        rcases hga : g a with b | j
        · exact b.elim
        · simp only [Function.comp_apply]
          rw [hga]
          simp only [Sum.elim_inr, Function.comp_apply, Fin.append_left]
      have hright : ((Fin.append (fun j => v (V j)) x) ∘ Fin.natAdd (Fintype.card ↥T0)) = x := by
        funext j
        exact Fin.append_right _ _ j
      rw [hleft, hright]
      refine realize_congr φ x (fun a ha => ?_)
      have hT : a ∈ T0 := by
        rw [hT0]
        exact Finset.mem_union.2 (Or.inl (Finset.mem_union.2 (Or.inl ha)))
      have hga : g a = Sum.inr (e ⟨a, hT⟩) := dif_pos hT
      rw [hga]
      simp only [Sum.elim_inr, V_e a hT]
    have step2 : (ψ₁.Realize (fun e : Empty => e.elim) (Fin.append (fun j => v (V j)) x)
        ↔ (W4.shrinkAux (n := n) V 0 ψ₁).Realize v x) := by
      have h2 := (W4.realize_shrinkAux (n := n) V 0 ψ₁ v x).symm
      have h3 : (fun i => Sum.elim v x (W4.gVar V 0 i)) = Fin.append (fun j => v (V j)) x := by
        funext i
        exact (W4.tupleAt_apply V 0 v x i).symm ▸ rfl
      rw [← h3]
      exact h2
    exact step1.symm.trans ((hEquiv₁ M hM _ hsort).trans step2)

end ParamBridge
end Milestone0
end SpecialTransformations
