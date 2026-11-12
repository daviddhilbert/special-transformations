module

public import JohnsonLanguagePrime

@[expose] public section
set_option linter.style.haveILetI false
open FirstOrder FirstOrder.Language
namespace SpecialTransformations.Section3.ValuedDefinability
variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ)
variable {α : Type}

abbrev FunDef (f : (α → K) → K) : Prop :=
  letI := FirstOrder.valStructure v
  (Set.univ : Set K).DefinableFun Language.val f

abbrev SetDef (s : Set (α → K)) : Prop :=
  letI := FirstOrder.valStructure v
  (Set.univ : Set K).Definable Language.val s

abbrev MapDef {β : Type} (f : (α → K) → β → K) : Prop :=
  letI := FirstOrder.valStructure v
  (Set.univ : Set K).DefinableMap Language.val f

theorem constant (a : K) : FunDef v
    (fun _ : α → K => a) := by
  letI := FirstOrder.valStructure v
  exact Language.val.definableFun_const α (Set.mem_univ a)

theorem add {f g : (α → K) → K}
    (hf : FunDef v f)
    (hg : FunDef v g) :
    FunDef v (fun x => f x + g x) := by
  letI := FirstOrder.valStructure v
  have h := (Set.DefinableFun.fun_symbol (M := K) (L := Language.val) ValFunc.add).of_empty
    (A := (Set.univ : Set K))
  exact h.comp (show MapDef v
    (fun x => ![f x, g x]) from by intro i; fin_cases i; exact hf; exact hg)

theorem mul {f g : (α → K) → K}
    (hf : FunDef v f)
    (hg : FunDef v g) :
    FunDef v (fun x => f x * g x) := by
  letI := FirstOrder.valStructure v
  have h := (Set.DefinableFun.fun_symbol (M := K) (L := Language.val) ValFunc.mul).of_empty
    (A := (Set.univ : Set K))
  exact h.comp (show MapDef v
    (fun x => ![f x, g x]) from by intro i; fin_cases i; exact hf; exact hg)

theorem neg {f : (α → K) → K}
    (hf : FunDef v f) :
    FunDef v (fun x => -f x) := by
  letI := FirstOrder.valStructure v
  have h := (Set.DefinableFun.fun_symbol (M := K) (L := Language.val) ValFunc.neg).of_empty
    (A := (Set.univ : Set K))
  exact h.comp (show MapDef v
    (fun x => ![f x]) from by intro i; fin_cases i; exact hf)

theorem val_le {f g : (α → K) → K}
    (hf : FunDef v f)
    (hg : FunDef v g) :
    SetDef v {x | v (f x) ≤ v (g x)} := by
  letI := FirstOrder.valStructure v
  have h : SetDef v
      {x : Fin 2 → K | v (x 0) ≤ v (x 1)} := by
    change (Set.univ : Set K).Definable Language.val _
    rw [Set.definable_iff_exists_formula_sum]
    exact ⟨.rel ValRel.le (fun i => .var (.inl (.inr i))), rfl⟩
  exact h.preimage_map (show MapDef v
    (fun x => ![f x, g x]) from by intro i; fin_cases i; exact hf; exact hg)

theorem val_eq_one {f : (α → K) → K}
    (hf : FunDef v f) :
    SetDef v {x | v (f x) = 1} := by
  letI := FirstOrder.valStructure v
  have h1 := constant v (α := α) (1 : K)
  change (Set.univ : Set K).Definable Language.val _
  convert (val_le v hf h1).inter (val_le v h1 hf) using 1
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, map_one, le_antisymm_iff]

theorem inv {f : (α → K) → K}
    (hf : FunDef v f) :
    FunDef v (fun x => (f x)⁻¹) := by
  letI := FirstOrder.valStructure v
  have hinv : FunDef v
      (fun x : Fin 1 → K => (x 0)⁻¹) := by
    let a (w : Option (Fin 1) → K) := w (some 0)
    let b (w : Option (Fin 1) → K) := w none
    have ha : FunDef v a := Set.DefinableFun.proj Language.val
    have hb : FunDef v b := Set.DefinableFun.proj Language.val
    have h0 := (ha.ofPred_eq (constant v 0)).inter (hb.ofPred_eq (constant v 0))
    have h1 := (mul v ha hb).ofPred_eq (constant v 1)
    have he : Function.tupleGraph (fun x : Fin 1 → K => (x 0)⁻¹) =
        {w | a w = 0 ∧ b w = 0} ∪ {w | a w * b w = 1} := by
      ext w
      change (a w)⁻¹ = b w ↔ (a w = 0 ∧ b w = 0) ∨ a w * b w = 1
      by_cases hz : a w = 0
      · simp [hz, eq_comm]
      · constructor
        · intro hi
          exact Or.inr (by rw [← hi, mul_inv_cancel₀ hz])
        · rintro (⟨h, _⟩ | h)
          · exact (hz h).elim
          · calc
              (a w)⁻¹ = (a w)⁻¹ * (a w * b w) := by rw [h, mul_one]
              _ = b w := by rw [← mul_assoc, inv_mul_cancel₀ hz, one_mul]
    change SetDef v _
    rw [he]
    exact h0.union h1
  exact hinv.comp (show MapDef v
    (fun x => ![f x]) from by intro i; fin_cases i; exact hf)

end SpecialTransformations.Section3.ValuedDefinability
