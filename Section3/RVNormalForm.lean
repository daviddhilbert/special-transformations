import Section3.RVLiteralReduction
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3

def rvOnly {α : Type} {n : ℕ} (sα : α → SortTag) (sn : Fin n → SortTag) :
    LRV.BoundedFormula α n → LRV.BoundedFormula α n
  | .falsum => .falsum
  | .equal t u => if TmSort sα sn t = some .vf then rvEquality t u else .equal t u
  | .rel .memVF _ => ⊤
  | .rel .memRV _ => ⊤
  | .rel R ts => .rel R ts
  | .imp φ ψ => .imp (rvOnly sα sn φ) (rvOnly sα sn ψ)
  | .all _ => ⊥

theorem rvOnly_correct {α : Type} {n : ℕ} (sα : α → SortTag) (sn : Fin n → SortTag)
    (φ : LRV.BoundedFormula α n) (hqf : φ.IsQF) (hws : WellSorted sα sn φ) :
    (rvOnly sα sn φ).IsQF ∧ WellSorted sα sn (rvOnly sα sn φ) ∧
    ∀ (M : Type) [LRV.Structure M] [_hM : M ⊨ Axioms.ACVF]
      (v : α → M) (x : Fin n → M),
      (∀ a, sortEval (sα a) (v a)) → (∀ i, sortEval (sn i) (x i)) →
      (φ.Realize v x ↔ (rvOnly sα sn φ).Realize v x) := by
  induction hqf with
  | falsum => exact ⟨.falsum, hws, fun _ _ _ _ _ _ _ => Iff.rfl⟩
  | of_isAtomic ha =>
    cases ha with
    | equal t u =>
      cases hws with
      | @equal _ _ _ _ σ ht hu =>
        cases σ with
        | vf =>
          simp only [Term.bdEqual, rvOnly, ht]
          exact ⟨.of_isAtomic (.equal _ _), rvEquality_wellSorted sα sn t u ht hu,
            fun _ _ _ v x hv hx => realize_rvEquality sα sn v x hv hx t u ht hu⟩
        | rv =>
          simp only [Term.bdEqual, rvOnly, ht]
          exact ⟨.of_isAtomic (.equal _ _), .equal sn ht hu,
            fun _ _ _ _ _ _ _ => Iff.rfl⟩
    | rel R ts =>
      cases hws with
      | rel _ _ _ hts =>
        cases R with
        | memVF =>
          refine ⟨BoundedFormula.IsQF.top, wellSorted_top sα sn, ?_⟩
          intro M _ hM v x hv hx
          have h := CanonicalStructure.term_sort hM sα sn v x hv hx (ts 0) (hts 0)
          simp only [Relations.boundedFormula, rvOnly, BoundedFormula.realize_top]
          have he : (fun i => (ts i).realize (Sum.elim v x)) =
              (![(ts 0).realize (Sum.elim v x)] : Fin 1 → M) := by
            funext i; fin_cases i; rfl
          change Structure.RelMap (L := LRV) Rel.memVF
            (fun i => (ts i).realize (Sum.elim v x)) ↔ True
          rw [he]
          exact iff_true_intro h
        | memRV =>
          refine ⟨BoundedFormula.IsQF.top, wellSorted_top sα sn, ?_⟩
          intro M _ hM v x hv hx
          have h := CanonicalStructure.term_sort hM sα sn v x hv hx (ts 0) (hts 0)
          simp only [Relations.boundedFormula, rvOnly, BoundedFormula.realize_top]
          have he : (fun i => (ts i).realize (Sum.elim v x)) =
              (![(ts 0).realize (Sum.elim v x)] : Fin 1 → M) := by
            funext i; fin_cases i; rfl
          change Structure.RelMap (L := LRV) Rel.memRV
            (fun i => (ts i).realize (Sum.elim v x)) ↔ True
          rw [he]
          exact iff_true_intro h
        | memUnits => exact ⟨.of_isAtomic (.rel _ _), .rel sn _ _ hts,
            fun _ _ _ _ _ _ _ => Iff.rfl⟩
        | rvLe => exact ⟨.of_isAtomic (.rel _ _), .rel sn _ _ hts,
            fun _ _ _ _ _ _ _ => Iff.rfl⟩
  | @imp φ ψ hφ hψ ihφ ihψ =>
    cases hws with
    | imp _ hwφ hwψ =>
      obtain ⟨hqφ, hsφ, heφ⟩ := ihφ hwφ
      obtain ⟨hqψ, hsψ, heψ⟩ := ihψ hwψ
      refine ⟨hqφ.imp hqψ, .imp sn hsφ hsψ, ?_⟩
      intro M _ hM v x hv hx
      exact imp_congr (heφ M v x hv hx) (heψ M v x hv hx)
end SpecialTransformations.Section3