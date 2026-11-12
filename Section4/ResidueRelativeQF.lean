module

public import Section4.ResidueScopedContext
public import Section4.RVCoordinates
public import Section3.SortedTuples

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4.ResiduePurity.Scoped

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n : ℕ}
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

private theorem rel_unary {α : Type} {n : ℕ} (R : Rel 1)
    (ts : Fin 1 → LRV.Term (α ⊕ Fin n)) (v : α → M) (x : Fin n → M) :
    (BoundedFormula.rel R ts).Realize v x ↔
      Structure.RelMap (L := LRV) R ![(ts 0).realize (Sum.elim v x)] := by
  change Structure.RelMap (L := LRV) R _ ↔ _
  have he : (fun i => (ts i).realize (Sum.elim v x)) =
      (![(ts 0).realize (Sum.elim v x)] : Fin 1 → M) := by
    funext i
    fin_cases i
    rfl
  rw [he]

private theorem rel_binary {α : Type} {n : ℕ} (R : Rel 2)
    (ts : Fin 2 → LRV.Term (α ⊕ Fin n)) (v : α → M) (x : Fin n → M) :
    (BoundedFormula.rel R ts).Realize v x ↔
      Structure.RelMap (L := LRV) R
        ![(ts 0).realize (Sum.elim v x), (ts 1).realize (Sum.elim v x)] := by
  change Structure.RelMap (L := LRV) R _ ↔ _
  have he : (fun i => (ts i).realize (Sum.elim v x)) =
      (![(ts 0).realize (Sum.elim v x), (ts 1).realize (Sum.elim v x)] : Fin 2 → M) := by
    funext i
    fin_cases i <;> rfl
  rw [he]

theorem qf_definable {p : Parameters S} {s : Fin n → CanonicalRV.RVSort M}
    (Q : TermContext p s) (φ : LRV.BoundedFormula (Fin p.length) n) (hq : φ.IsQF)
    (hw : WellSorted p.sorts (fun _ => .rv) φ) :
    Relative.Def Q.coefficients.field
      {x : Fin n → ModelResidue M | φ.Realize p.values (residueInputs s x)} := by
  induction hq with
  | falsum => exact Set.definable_empty
  | of_isAtomic ha =>
    cases ha with
    | equal t u =>
      cases hw with
      | @equal _ _ _ _ σ ht hu =>
        cases σ with
        | vf =>
          obtain ⟨a, haB, ha⟩ := term_representation Q t .vf ht
          obtain ⟨b, hbB, hb⟩ := term_representation Q u .vf hu
          convert Relative.proposition (ι := Fin n) Q.coefficients.field (a.val = b.val) using 1
          ext x
          change t.realize _ = u.realize _ ↔ _
          rw [← residueEval, ← residueEval, ha, hb]
          exact Iff.rfl
        | rv =>
          obtain ⟨a, ha, hea⟩ := term_representation Q t .rv ht
          obtain ⟨b, hb, heb⟩ := term_representation Q u .rv hu
          convert ha.eq hb using 1
          ext x
          change t.realize _ = u.realize _ ↔ _
          rw [← residueEval, ← residueEval, hea, heb]
          exact Subtype.val_inj
    | rel R ts =>
      cases hw with
      | rel _ _ _ hts =>
        cases R with
        | memVF =>
          obtain ⟨a, haB, ha⟩ := term_representation Q (ts 0) .vf (hts 0)
          convert Relative.proposition (ι := Fin n) Q.coefficients.field True using 1
          ext x
          change (BoundedFormula.rel Rel.memVF ts).Realize p.values (residueInputs s x) ↔ True
          rw [rel_unary]
          change iVF ((ts 0).realize _) ↔ True
          rw [← residueEval, ha]
          exact iff_true_intro a.property
        | memRV =>
          obtain ⟨a, ha, hea⟩ := term_representation Q (ts 0) .rv (hts 0)
          convert Relative.proposition (ι := Fin n) Q.coefficients.field True using 1
          ext x
          change (BoundedFormula.rel Rel.memRV ts).Realize p.values (residueInputs s x) ↔ True
          rw [rel_unary]
          change iRV ((ts 0).realize _) ↔ True
          rw [← residueEval, hea]
          exact iff_true_intro (a x).property
        | memUnits =>
          obtain ⟨a, ha, hea⟩ := term_representation Q (ts 0) .rv (hts 0)
          convert ha.units using 1
          ext x
          change (BoundedFormula.rel Rel.memUnits ts).Realize p.values (residueInputs s x) ↔
            iUnits (a x).val
          rw [rel_unary]
          change iUnits ((ts 0).realize _) ↔ _
          rw [← residueEval, hea]
        | rvLe =>
          obtain ⟨a, ha, hea⟩ := term_representation Q (ts 0) .rv (hts 0)
          obtain ⟨b, hb, heb⟩ := term_representation Q (ts 1) .rv (hts 1)
          convert ha.le hb using 1
          ext x
          change (BoundedFormula.rel Rel.rvLe ts).Realize p.values (residueInputs s x) ↔
            iLe (a x).val (b x).val
          rw [rel_binary]
          change iLe ((ts 0).realize _) ((ts 1).realize _) ↔ _
          rw [← residueEval, ← residueEval, hea, heb]
  | @imp φ ψ hφ hψ ihφ ihψ =>
    cases hw with
    | imp _ hwφ hwψ =>
      convert (ihφ hwφ).compl.union (ihψ hwψ) using 1
      ext x
      simp only [BoundedFormula.realize_imp, Set.mem_ofPred_eq, Set.mem_union, Set.mem_compl_iff,
        imp_iff_not_or]

theorem formula_definable {p : Parameters S} {s : Fin n → CanonicalRV.RVSort M}
    (Q : TermContext p s) (φ : LRV.BoundedFormula (Fin p.length) n)
    (hw : WellSorted p.sorts (fun _ => .rv) φ) :
    Relative.Def Q.coefficients.field
      {x : Fin n → ModelResidue M | φ.Realize p.values (residueInputs s x)} := by
  obtain ⟨ψ, hq, hwψ, he⟩ := theorem_2_3_quantifier_elimination (Fin p.length) p.sorts n
    (fun _ => .rv) φ hw
  convert qf_definable Q ψ hq hwψ using 1
  ext x
  exact he M hM p.values (residueInputs s x) p.sorted
    (fun i => (s i * residueRV (x i)).property)

/-- All residue coordinates and all field coefficients are interpreted
over the displayed actual field E; the context above is constructed from
the real base, rather than assumed as a purity or algebraicity theorem. -/
theorem residue_pullback_definable (hcan : CanonicalStructure.IsCanonical (M := M))
    (B : LRV.Substructure M) (E : Subfield (ModelResidue M)) (hE : residueParameterField B ≤ E)
    (A : DefSet (rawRVSpace (M := M) n) (residueExtendedBase B E))
    (s : Fin n → CanonicalRV.RVSort M) (hs : ∀ i, s i ∈ extendedCoefficients B E) :
    Relative.Def E {x : Fin n → ModelResidue M | (fun i => s i * residueRV (x i)) ∈ A.carrier} := by
  have hraw : (residueExtendedBase B E).Definable LRV ((rawRVSpace n).preimage A.carrier) := A.definable
  have hsorted : ∀ a ∈ (rawRVSpace n).preimage A.carrier, ∀ i, iRV (a i) := by
    rintro a ⟨ha, _⟩ i
    obtain ⟨t, rfl⟩ := ha
    exact (t i).property
  obtain ⟨p, φ, hw, he⟩ := raw_definableOver_sorted hcan (residueExtendedBase B E)
    (fun _ : Fin n => .rv) _ hraw hsorted
  let Q := scopedContextOfSubstructure B E hE p s hs
  have h := formula_definable Q φ hw
  change Relative.Def E _ at h
  convert h using 1
  ext x
  let t : Fin n → CanonicalRV.RVSort M := fun i => s i * residueRV (x i)
  have hc : residueInputs s x ∈ (rawRVSpace n).preimage A.carrier ↔ t ∈ A.carrier := by
    change rvValues t ∈ (rawRVSpace n).preimage A.carrier ↔ _
    exact ⟨fun ⟨ha, hb⟩ => by simpa only [decode_rvValues] using hb,
      fun hb => ⟨⟨t, rfl⟩, by simpa only [decode_rvValues] using hb⟩⟩
  have hs := Set.ext_iff.mp he (residueInputs s x)
  change (_ ↔ (∀ i, iRV (residueInputs s x i)) ∧ φ.Realize _ _) at hs
  have hproper : ∀ i, iRV (residueInputs s x i) := fun i => (t i).property
  exact hc.symm.trans (hs.trans (and_iff_right hproper))

end SpecialTransformations.Section4.ResiduePurity.Scoped

end
