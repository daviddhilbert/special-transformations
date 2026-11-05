import MarkerBridge
import QESaturatedBackAndForth
import Mathlib.Data.Set.Finite.Basic

/-! Full QE implies extension of substructure embeddings into genuinely
saturated models. The pushed complete one-variable type is proved finitely
satisfiable using QE; saturation is used only after that proof. Chain exhaustion
and atomic-type packaging reuse the checked proofs in QE/BackAndForth.lean.
No saturated-extension property or valued-field theorem is assumed. -/

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open scoped FirstOrder

namespace QESaturatedExtension

variable {L : FirstOrder.Language.{0, 0}} {M N : Type} [L.Structure M] [L.Structure N]

/- The following three QF preservation lemmas are extracted from
QE/Semantics_saturation.lean, with their proofs unchanged. -/

theorem embedding_realize_isAtomic (g : M ↪[L] N) {α : Type} {n : ℕ}
    {φ : L.BoundedFormula α n} (h : φ.IsAtomic) (v : α → M) (xs : Fin n → M) :
    φ.Realize (fun a => g (v a)) (fun i => g (xs i)) ↔ φ.Realize v xs := by
  have hcomp : (Sum.elim (fun a => g (v a)) (fun i => g (xs i)))
      = (fun s => g (Sum.elim v xs s)) := by
    funext s; cases s <;> rfl
  have key : ∀ t : L.Term (α ⊕ Fin n),
      t.realize (Sum.elim (fun a => g (v a)) (fun i => g (xs i)))
        = g (t.realize (Sum.elim v xs)) := by
    intro t; rw [hcomp]; exact HomClass.realize_term g
  cases h with
  | equal t₁ t₂ =>
    simp only [BoundedFormula.realize_bdEqual]
    rw [key t₁, key t₂, g.injective.eq_iff]
  | rel R ts =>
    simp only [BoundedFormula.realize_rel]
    have hrs : (fun i => (ts i).realize (Sum.elim (fun a => g (v a)) (fun i => g (xs i))))
        = (fun i => g ((ts i).realize (Sum.elim v xs))) := by
      funext i; exact key (ts i)
    rw [hrs]
    exact StrongHomClass.map_rel (r := R) g (fun i => (ts i).realize (Sum.elim v xs))

theorem embedding_realize_isQF (g : M ↪[L] N) {α : Type} {n : ℕ}
    {φ : L.BoundedFormula α n} (h : φ.IsQF) :
    ∀ (v : α → M) (xs : Fin n → M),
      φ.Realize (fun a => g (v a)) (fun i => g (xs i)) ↔ φ.Realize v xs := by
  induction h with
  | falsum => intro v xs; exact Iff.rfl
  | of_isAtomic ha => exact fun v xs => embedding_realize_isAtomic g ha v xs
  | imp _ _ ih1 ih2 => intro v xs; simp only [BoundedFormula.realize_imp, ih1 v xs, ih2 v xs]

theorem embedding_realize_formula_isQF (g : M ↪[L] N) {α : Type}
    {φ : L.Formula α} (h : φ.IsQF) (v : α → M) :
    φ.Realize (fun a => g (v a)) ↔ φ.Realize v := by
  have h0 : (fun i : Fin 0 => g ((default : Fin 0 → M) i)) = (default : Fin 0 → N) :=
    Subsingleton.elim _ _
  have h1 := embedding_realize_isQF (n := 0) g h v (default : Fin 0 → M)
  rw [h0] at h1
  exact h1

variable {T : L.Theory}

/-- QE makes any substructure embedding a partial elementary map between
ambient models. The substructure itself need not model T. -/
theorem partial_elementary (hQE : MarkerBridge.FullQE T)
    (hM : M ⊨ T) (hN : N ⊨ T) (S : L.Substructure M) (f : S ↪[L] N)
    {α : Type} (φ : L.Formula α) (a : α → S) :
    φ.Realize (fun i => (a i : M)) ↔ φ.Realize (fun i => f (a i)) := by
  obtain ⟨ψ, hψ, heq⟩ := hQE α 0 φ
  have hMφ : φ.Realize (fun i => (a i : M)) ↔ Formula.Realize ψ (fun i => (a i : M)) :=
    heq M hM (fun i => (a i : M)) (default : Fin 0 → M)
  have hNφ : φ.Realize (fun i => f (a i)) ↔ Formula.Realize ψ (fun i => f (a i)) :=
    heq N hN (fun i => f (a i)) (default : Fin 0 → N)
  exact hMφ.trans ((embedding_realize_formula_isQF S.subtype hψ a).trans
    ((embedding_realize_formula_isQF f hψ a).symm.trans hNφ.symm))

/-- The complete one-variable type of a source element over a substructure. -/
def completeType (S : L.Substructure M) (m : M) : MarkerBridge.TypeOver L S :=
  {φ | φ.Realize (Sum.elim (fun s : S => (s : M)) (fun _ : Unit => m))}

/-- A finite conjunction from the source type has a target witness: existential
closure removes its one new variable and QE transports that sentence over S. -/
theorem completeType_finSat (hQE : MarkerBridge.FullQE T)
    (hM : M ⊨ T) (hN : N ⊨ T) (S : L.Substructure M) (f : S ↪[L] N) (m : M) :
    MarkerBridge.FinSat (fun s : S => f s) (completeType S m) := by
  intro p₀ hpfinite hpsub
  let l : List (L.Formula (S ⊕ Unit)) := hpfinite.toFinset.toList
  have hl : ∀ φ, φ ∈ l ↔ φ ∈ p₀ := by
    intro φ
    simp only [l, Finset.mem_toList, Set.Finite.mem_toFinset]
  let ψ : L.Formula (S ⊕ Unit) := l.foldr (· ⊓ ·) ⊤
  have hm : ψ.Realize (Sum.elim (fun s : S => (s : M)) (fun _ : Unit => m)) := by
    change BoundedFormula.Realize (l.foldr (· ⊓ ·) ⊤) _ (default : Fin 0 → M)
    apply (BoundedFormula.realize_foldr_inf l _ _).mpr
    intro φ hφ
    exact hpsub ((hl φ).mp hφ)
  have hMex : (ψ.iExs Unit).Realize (fun s : S => (s : M)) :=
    Formula.realize_iExs.mpr ⟨fun _ => m, hm⟩
  have hNex : (ψ.iExs Unit).Realize (fun s : S => f s) :=
    (partial_elementary hQE hM hN S f (ψ.iExs Unit) id).mp hMex
  obtain ⟨b, hb⟩ := Formula.realize_iExs.mp hNex
  refine ⟨b (), ?_⟩
  intro φ hφ
  have hh : φ.Realize (Sum.elim (fun s : S => f s) b) :=
    (BoundedFormula.realize_foldr_inf l _ (default : Fin 0 → N)).mp hb φ ((hl φ).mpr hφ)
  have he : (fun _ : Unit => b ()) = b := by funext u; cases u; rfl
  rw [he]
  exact hh

/-- Realizing the complete type gives precisely the atomic information needed
to extend to the generated substructure. Negated formulas give reflection. -/
theorem realizesAtomic_of_completeType (S : L.Substructure M) (f : S ↪[L] N)
    (m : M) (b : N)
    (hb : ∀ φ ∈ completeType S m,
      φ.Realize (Sum.elim (fun s : S => f s) (fun _ : Unit => b))) :
    QESaturatedBackAndForth.Realize.RealizesAtomic S f m b := by
  have hiff (φ : L.Formula (S ⊕ Unit)) :
      φ.Realize (Sum.elim (fun s : S => (s : M)) (fun _ : Unit => m)) ↔
        φ.Realize (Sum.elim (fun s : S => f s) (fun _ : Unit => b)) := by
    constructor
    · exact hb φ
    · intro htarget
      by_contra hsource
      have hn : φ.not ∈ completeType S m := Formula.realize_not.mpr hsource
      exact (Formula.realize_not.mp (hb φ.not hn)) htarget
  constructor
  · intro u v
    simpa only [Formula.realize_equal, QESaturatedBackAndForth.Realize.mv,
      QESaturatedBackAndForth.Realize.wv] using hiff (u.equal v)
  · intro n r ts
    simpa only [Formula.realize_rel, QESaturatedBackAndForth.Realize.mv,
      QESaturatedBackAndForth.Realize.wv] using hiff (r.formula ts)

/-- The converse direction of the saturated-model QE criterion, proved from
ordinary type realization. No extension theorem is assumed. -/
theorem extension_of_fullQE (hQE : MarkerBridge.FullQE T) :
    MarkerBridge.SaturatedEmbeddingExtension T := by
  intro M N sM sN hM hN hSat S f
  apply QESaturatedBackAndForth.Realize.exists_total_embedding_of_realizesAtomic ?_ S f
  intro A g m _
  have hsize : Cardinal.mk A < Order.succ (Cardinal.mk M) :=
    lt_of_le_of_lt (Cardinal.mk_le_of_injective (Subtype.coe_injective)) (Order.lt_succ _)
  obtain ⟨b, hb⟩ := hSat A (fun a => g a) hsize (completeType A m)
    (completeType_finSat hQE hM hN A g m)
  exact ⟨b, realizesAtomic_of_completeType A g m b hb⟩

end QESaturatedExtension

#print axioms QESaturatedExtension.partial_elementary
#print axioms QESaturatedExtension.completeType_finSat
#print axioms QESaturatedExtension.realizesAtomic_of_completeType
#print axioms QESaturatedExtension.extension_of_fullQE
