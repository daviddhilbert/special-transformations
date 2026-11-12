module

public import Section3.ModelContext
public import MarkerBridge

public import Section6.EnvelopeUniformity
public import Section6.RVReductQE
public import Section5.VerticalObstacles
public import Section3.GammaPresentation
public import CanonicalCountable

@[expose] public section

/-! Checked producers for the earlier preparation needed by the native
comparison, including the finite-tuple form of Marker saturation. -/

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0

namespace SpecialTransformations.Section3

variable {M : Type} [LRV.Structure M]

private def nameLast {α : Type} (n : ℕ) :
    α ⊕ Fin (n + 1) → (α ⊕ Unit) ⊕ Fin n :=
  Sum.elim (Sum.inl ∘ Sum.inl) (Fin.lastCases (.inl (.inr ())) Sum.inr)

private def nameLastFormula {α : Type} {n : ℕ} (φ : LRV.BoundedFormula α (n + 1)) :
    LRV.BoundedFormula (α ⊕ Unit) n :=
  BoundedFormula.relabel (nameLast n) φ.toFormula

private theorem realize_nameLastFormula {α : Type} {n : ℕ}
    (φ : LRV.BoundedFormula α (n + 1)) (v : α → M) (b : M) (a : Fin n → M) :
    (nameLastFormula φ).Realize (Sum.elim v (fun _ => b)) a ↔
      φ.Realize v (Fin.snoc a b) := by
  rw [nameLastFormula, BoundedFormula.realize_relabel]
  simp only [Fin.castAdd_zero, Function.comp_id]
  rw [show (a ∘ Fin.natAdd n : Fin 0 → M) = default from Subsingleton.elim _ _]
  change φ.toFormula.Realize (Sum.elim (Sum.elim v (fun _ => b)) a ∘ nameLast n) ↔ _
  rw [BoundedFormula.realize_toFormula]
  have he : ((Sum.elim (Sum.elim v (fun _ => b)) a ∘ nameLast n) ∘ Sum.inr) =
      Fin.snoc a b := by
    funext i
    cases i using Fin.lastCases <;> simp [nameLast]
  rw [he]
  rfl

private def conjoin {α : Type} {n : ℕ} :
    List (LRV.BoundedFormula α n) → LRV.BoundedFormula α n
  | [] => ⊤
  | φ :: l => φ ⊓ conjoin l

private theorem realize_conjoin {α : Type} {n : ℕ} (l : List (LRV.BoundedFormula α n))
    (v : α → M) (a : Fin n → M) :
    (conjoin l).Realize v a ↔ ∀ φ ∈ l, φ.Realize v a := by
  induction l with
  | nil => simp [conjoin]
  | cons φ l ih => simp [conjoin, ih]

private def lastTypeFormula {α : Type} {n : ℕ} (l : List (LRV.BoundedFormula α (n + 1))) :
    LRV.Formula (α ⊕ Unit) :=
  (conjoin (l.map nameLastFormula)).exs

private theorem realize_lastTypeFormula {α : Type} {n : ℕ}
    (l : List (LRV.BoundedFormula α (n + 1))) (v : α → M) (b : M) :
    (lastTypeFormula l).Realize (Sum.elim v (fun _ => b)) ↔
      ∃ a : Fin n → M, ∀ φ ∈ l, φ.Realize v (Fin.snoc a b) := by
  simp only [lastTypeFormula, BoundedFormula.realize_exs, realize_conjoin,
    List.forall_mem_map, realize_nameLastFormula]

/-- Marker one-variable saturation realizes all finite tuple types.
The proof names one coordinate at a time, adding only one parameter. -/
theorem saturated_of_markerSatAt {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : MarkerBridge.SatAt LRV M κ) : Saturated M κ := by
  suffices h : ∀ n, ∀ (α : Type) (v : α → M), Cardinal.mk α < κ →
      ∀ p : Set (LRV.BoundedFormula α n), FinitelySatisfiable v p →
        ∃ a : Fin n → M, ∀ φ ∈ p, φ.Realize v a by
    exact fun α v hsmall n => h n α v hsmall
  intro n
  induction n with
  | zero =>
    intro α v hsmall p hp
    refine ⟨Fin.elim0, ?_⟩
    intro φ hφ
    obtain ⟨a, ha⟩ := hp [φ] (by simpa using hφ)
    exact Subsingleton.elim a Fin.elim0 ▸ ha φ (by simp)
  | succ n ih =>
    intro α v hsmall p hp
    let q : MarkerBridge.TypeOver LRV α :=
      lastTypeFormula '' {l : List (LRV.BoundedFormula α (n + 1)) | ∀ φ ∈ l, φ ∈ p}
    have hq : MarkerBridge.FinSat v q := by
      intro q₀ hq₀ hsub
      haveI : Fintype q₀ := hq₀.fintype
      choose l hl hle using fun x : q₀ => hsub x.property
      let L := (Finset.univ.toList : List q₀).flatMap l
      have hL : ∀ φ ∈ L, φ ∈ p := by
        intro φ hφ
        obtain ⟨x, _, hx⟩ := List.mem_flatMap.mp hφ
        exact hl x φ hx
      obtain ⟨a, ha⟩ := hp L hL
      refine ⟨a (Fin.last n), ?_⟩
      intro χ hχ
      let x : q₀ := ⟨χ, hχ⟩
      rw [← (show lastTypeFormula (l x) = χ from hle x), realize_lastTypeFormula]
      refine ⟨a ∘ Fin.castSucc, ?_⟩
      intro φ hφ
      have hs : Fin.snoc (a ∘ Fin.castSucc) (a (Fin.last n)) = a := by
        funext i
        cases i using Fin.lastCases <;> simp
      rw [hs]
      exact ha φ (List.mem_flatMap.mpr ⟨x, by simp, hφ⟩)
    obtain ⟨b, hb⟩ := hs α v hsmall q hq
    let r : Set (LRV.BoundedFormula (α ⊕ Unit) n) := nameLastFormula '' p
    have hr : FinitelySatisfiable (Sum.elim v (fun _ => b)) r := by
      intro l hl
      have h : ∃ L : List (LRV.BoundedFormula α (n + 1)), L.map nameLastFormula = l ∧
          (∀ φ ∈ L, φ ∈ p) := by
        induction l with
        | nil => exact ⟨[], rfl, by simp⟩
        | cons χ l ih =>
          obtain ⟨φ, hφ, rfl⟩ := hl χ (by simp)
          obtain ⟨L, rfl, hL⟩ := ih (by intro ψ hψ; exact hl ψ (by simp [hψ]))
          exact ⟨φ :: L, rfl, by simpa [hφ] using hL⟩
      obtain ⟨L, rfl, hL⟩ := h
      obtain ⟨a, ha⟩ := (realize_lastTypeFormula L v b).mp
        (hb (lastTypeFormula L) ⟨L, hL, rfl⟩)
      exact ⟨a, by simpa only [List.forall_mem_map, realize_nameLastFormula] using ha⟩
    have hsmall' : Cardinal.mk (α ⊕ Unit) < κ := by
      simp only [Cardinal.mk_sum, Cardinal.mk_unit, Cardinal.lift_id]
      exact Cardinal.add_lt_of_lt hκ hsmall (Cardinal.one_lt_aleph0.trans_le hκ)
    obtain ⟨a, ha⟩ := ih (α ⊕ Unit) (Sum.elim v (fun _ => b)) hsmall' r hr
    exact ⟨Fin.snoc a b, fun φ hφ => (realize_nameLastFormula φ v b a).mp
      (ha _ ⟨φ, hφ, rfl⟩)⟩

end SpecialTransformations.Section3
set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section5

namespace SpecialTransformations.Section6.EnvelopeUniformity

open RVTermSupport RVAbstraction RVGraphLanguage AlignedComparison

/-- The RV-reduct clause of the published earlier preparation interface. -/
def EarlierRVDefinitions : Prop :=
  ∀ (C : Type) (sC : LRV.Structure C) (hC : @Theory.Model LRV C sC Axioms.ACVF)
    (h00 : @Theory.Model LRV C sC Axioms.ACVF00)
    (hc : @CanonicalStructure.IsCanonical C sC) (κ : Cardinal),
    Order.succ Cardinal.aleph0 ≤ κ → @MarkerBridge.SatAt LRV C sC κ →
    ∀ (r m : ℕ) (z : Context r m → C),
      (∀ i, @sortEval C sC (sorts i) (z i)) →
        @RVQFDefinitions C sC hC (@Substructure.closure LRV C sC (Set.range z))

theorem earlierPreparation_of_rvDefinitions (hDefs : EarlierRVDefinitions) : EarlierPreparation := by
  intro C sC hC h00 hc κ hκ hSat r m z hz
  letI := sC
  letI := hC
  let S := Substructure.closure LRV (Set.range z)
  have hcount : Countable (Σ n, LRV.Functions n) :=
    Function.Injective.countable (f := fun f : (Σ n, LRV.Functions n) => (Sum.inl f : LRV.Symbols))
      Sum.inl_injective
  letI := hcount
  have hS : Countable S := Set.Countable.substructure_closure (L := LRV) (Set.finite_range z).countable
  have hsmall : Cardinal.mk ↥(S : Set C) < κ :=
    (Cardinal.mk_le_aleph0_iff.mpr hS).trans_lt ((Order.lt_succ _).trans_le hκ)
  have hSat' := saturated_of_markerSatAt ((Order.le_succ _).trans hκ) hSat
  let v := Values.presentationValuation (M := C)
  have hv := Values.presentation_compatible (M := C)
  exact PreparationInputs.of_valuation v hv (hDefs C sC hC h00 hc κ hκ hSat r m z hz)
    (uniformVerticalObstacles hSat' hsmall v hv)

/-- Both earlier preparation requirements are obtained from the checked
RV reduction and the Section 5 vertical-obstacle theorem. -/
theorem earlierPreparation : EarlierPreparation := by
  apply earlierPreparation_of_rvDefinitions
  intro C sC hC h00 hc κ hκ hSat r m z hz
  exact @RVGraphLanguage.rvQFDefinitions_of_acvf C sC hC
    (@Substructure.closure LRV C sC (Set.range z))

end SpecialTransformations.Section6.EnvelopeUniformity
