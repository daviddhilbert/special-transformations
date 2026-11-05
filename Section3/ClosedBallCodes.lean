import Section3.MinimalBallFamilies
import Section3.SortedTuples
import Section3.BallGeometry
import Section3.ClosedBallRoots
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.ClosedBallCodes
variable {M : Type} [LRV.Structure M]

private def variableTerm (i : Fin 4) : LRV.Term (Fin 0 ⊕ Fin 4) := .var (.inr i)

/-- The first coordinates are a center, a radius representative and a flag.
Flag zero codes the whole field; any other flag codes the closed ball. -/
def body : LRV.BoundedFormula (Fin 0) 4 :=
  (.equal (variableTerm 2) (.func Fn.vfZero Fin.elim0)) ⊔
    .rel Rel.rvLe ![.func Fn.rvMap ![variableTerm 1],
      .func Fn.rvMap ![.func Fn.vfAdd ![variableTerm 3, .func Fn.vfNeg ![variableTerm 0] ] ] ]

theorem body_sorted : WellSorted (fun _ : Fin 0 => .vf) (fun _ => .vf) body := by
  apply wellSorted_sup
  · exact WellSorted.equal _ (s := .vf) (by decide) (by decide)
  · apply WellSorted.rel
    intro i
    fin_cases i <;> decide

def tuple (t : Fin 3 → M) (x : M) : Fin 4 → M := ![t 0, t 1, t 2, x]

def rawBall (t : Fin 3 → M) : Set M :=
  {x | (∀ i, iVF (t i)) ∧ iVF x ∧ body.Realize Fin.elim0 (tuple t x)}

def ball (t : Fin 3 → M) : Set (VFType (M := M)) := {x | x.val ∈ rawBall t}

private theorem realize_func0 {β : Type} (f : Fn 0) (v : β → M) :
    (Term.func f Fin.elim0 : LRV.Term β).realize v = Structure.funMap (L := LRV) f Fin.elim0 := by
  change Structure.funMap (L := LRV) f (fun i => _) = _
  congr 1; funext i; exact i.elim0

private theorem realize_func1 {β : Type} (f : Fn 1) (t : LRV.Term β) (v : β → M) :
    (Term.func f ![t]).realize v = Structure.funMap (L := LRV) f ![t.realize v] := by
  change Structure.funMap (L := LRV) f (fun i => _) = _
  congr 1; funext i; fin_cases i; rfl

private theorem realize_func2 {β : Type} (f : Fn 2) (t u : LRV.Term β) (v : β → M) :
    (Term.func f ![t, u]).realize v = Structure.funMap (L := LRV) f ![t.realize v, u.realize v] := by
  change Structure.funMap (L := LRV) f (fun i => _) = _
  congr 1; funext i; fin_cases i <;> rfl

theorem body_realize (t : Fin 3 → M) (x : M) :
    body.Realize Fin.elim0 (tuple t x) ↔
      t 2 = iVFZero ∨ iLe (iRv (t 1)) (iRv (iVFAdd x (iVFNeg (t 0)))) := by
  rw [body, BoundedFormula.realize_sup]
  apply or_congr
  · change (variableTerm 2).realize _ = (Term.func Fn.vfZero Fin.elim0 : LRV.Term (Fin 0 ⊕ Fin 4)).realize _ ↔ _
    rw [realize_func0]
    rfl
  · change Structure.RelMap (L := LRV) Rel.rvLe (fun i =>
      (![Term.func Fn.rvMap ![variableTerm 1],
        Term.func Fn.rvMap ![Term.func Fn.vfAdd ![variableTerm 3,
          Term.func Fn.vfNeg ![variableTerm 0] ] ] ] i).realize _) ↔ _
    have he : (fun i =>
      (![Term.func Fn.rvMap ![variableTerm 1],
        Term.func Fn.rvMap ![Term.func Fn.vfAdd ![variableTerm 3,
          Term.func Fn.vfNeg ![variableTerm 0] ] ] ] i).realize
            (Sum.elim (Fin.elim0 : Fin 0 → M) (tuple t x))) =
      ![iRv (t 1), iRv (iVFAdd x (iVFNeg (t 0)))] := by
      funext i
      fin_cases i
      · change (Term.func Fn.rvMap ![variableTerm 1]).realize
          (Sum.elim (Fin.elim0 : Fin 0 → M) (tuple t x)) = iRv (t 1)
        rw [realize_func1]
        rfl
      · change (Term.func Fn.rvMap ![Term.func Fn.vfAdd ![variableTerm 3,
          Term.func Fn.vfNeg ![variableTerm 0] ] ]).realize
          (Sum.elim (Fin.elim0 : Fin 0 → M) (tuple t x)) = iRv (iVFAdd x (iVFNeg (t 0)))
        rw [realize_func1, realize_func2, realize_func1]
        rfl
    rw [he]
    rfl

/-- Every actual closed ball has a real code, with no chosen code named
as a base parameter. Radius zero is the singleton convention. -/
theorem ball_eq_closed [hM : M ⊨ Axioms.ACVF]
    {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)
    (t : Fin 3 → M) (ht : ∀ i, iVF (t i)) (hflag : t 2 ≠ iVFZero) :
    ball t = ValOneEC.closedBall v (⟨t 0, ht 0⟩ : VFType (M := M))
      (v (⟨t 1, ht 1⟩ : VFType (M := M))) := by
  apply Set.ext
  intro (x : VFType (M := M))
  change x.val ∈ rawBall t ↔ _
  rw [rawBall, Set.mem_ofPred_eq, body_realize, and_iff_right ht,
    and_iff_right x.property, or_iff_right hflag]
  let a : VFType (M := M) := ⟨t 0, ht 0⟩
  let b : VFType (M := M) := ⟨t 1, ht 1⟩
  have hd : (x - a).val = iVFAdd x.val (iVFNeg (t 0)) := by
    rw [sub_eq_add_neg]; rfl
  have he : iLe (iRv (t 1)) (iRv (iVFAdd x.val (iVFNeg (t 0)))) ↔
      VFValued.predV (x - a) b := by
    change _ ↔ iLe (iRv (t 1)) (iRv (x - a).val)
    rw [hd]
  exact he.trans (hv (x - a) b)

/-- The whole-field special radius is included in the real coding. -/
theorem ball_eq_univ [hM : M ⊨ Axioms.ACVF] (t : Fin 3 → M)
    (ht : ∀ i, iVF (t i)) (hz : t 2 = iVFZero) : ball t = Set.univ := by
  ext x
  change ((∀ i, iVF (t i)) ∧ iVF x.val ∧ body.Realize Fin.elim0 (tuple t x.val)) ↔ True
  exact iff_true_intro ⟨ht, x.property, (body_realize t x.val).mpr (Or.inl hz)⟩

/-- Every actual closed ball, including a singleton or the whole field,
has a real VF code. No representative is adjoined to the parameter base. -/
theorem exists_code_of_closed [hM : M ⊨ Axioms.ACVF]
    {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)
    (B : Set (VFType (M := M))) (hB : ClosedBallRoots.IsClosedBall v B) :
    ∃ t : Fin 3 → M, (∀ i, iVF (t i)) ∧ B = ball t := by
  rcases hB with rfl | ⟨a, b, rfl⟩
  · let z : VFType (M := M) := 0
    let t : Fin 3 → M := ![z.val, z.val, z.val]
    have ht : ∀ i, iVF (t i) := by intro i; fin_cases i <;> exact z.property
    exact ⟨t, ht, (ball_eq_univ t ht rfl).symm⟩
  · let e : VFType (M := M) := 1
    let t : Fin 3 → M := ![a.val, b.val, e.val]
    have ht : ∀ i, iVF (t i) := by
      intro i; fin_cases i
      · exact a.property
      · exact b.property
      · exact e.property
    have hz : t 2 ≠ iVFZero := by
      intro h
      have he : (1 : VFType (M := M)) = 0 := Subtype.ext h
      exact one_ne_zero he
    exact ⟨t, ht, (ball_eq_closed v hv t ht hz).symm⟩

/-- The complete membership graph is definable without additional parameters. -/
theorem relation_definable (S : Set M) :
    RawClosure.Tuple.RelationDefinable S (BallFamilies.relation (ball (M := M))) := by
  let p : Parameters S := ⟨0, Fin.elim0, fun _ => .vf, (fun i => i.elim0), (fun i => i.elim0)⟩
  let G : Set (Fin 4 → M) := {z | (∀ i, iVF (z i)) ∧ body.Realize Fin.elim0 z}
  have hG : DefinableOver S (fun _ => .vf) G := ⟨p, body, body_sorted, rfl⟩
  let idx : Fin 4 → Fin 3 ⊕ Fin 1 := ![.inl 0, .inl 1, .inl 2, .inr 0]
  have h := hG.raw_definable.preimage_comp idx
  have hset : {z : Fin 3 ⊕ Fin 1 → M |
      (z ∘ Sum.inl, z (.inr 0)) ∈ BallFamilies.relation ball} =
      (fun g => g ∘ idx) ⁻¹' G := by
    ext z
    change (∃ x : VFType (M := M), x.val ∈ rawBall (z ∘ Sum.inl) ∧ x.val = z (.inr 0)) ↔
      (∀ i, iVF ((z ∘ idx) i)) ∧ body.Realize Fin.elim0 (z ∘ idx)
    have he : z ∘ idx = tuple (z ∘ Sum.inl) (z (.inr 0)) := by
      funext i; fin_cases i <;> rfl
    rw [he]
    have hsort : (∀ i : Fin 4, iVF (tuple (z ∘ Sum.inl) (z (.inr 0)) i)) ↔
        (∀ i : Fin 3, iVF (z (.inl i))) ∧ iVF (z (.inr 0)) := by
      simp only [Fin.forall_fin_succ, Fin.forall_fin_zero, and_true, tuple,
        Matrix.cons_val_zero, Matrix.cons_val_succ, Function.comp_apply]
      tauto
    rw [hsort]
    constructor
    · rintro ⟨x, ⟨ht, hx, hb⟩, he⟩
      exact ⟨⟨ht, he ▸ hx⟩, he ▸ hb⟩
    · rintro ⟨⟨ht, hx⟩, hb⟩
      exact ⟨⟨z (.inr 0), hx⟩, ⟨ht, hx, hb⟩, rfl⟩
  change S.Definable LRV {z : Fin 3 ⊕ Fin 1 → M |
    (z ∘ Sum.inl, z (.inr 0)) ∈ BallFamilies.relation ball}
  rw [hset]
  exact h

variable [hM : M ⊨ Axioms.ACVF]

theorem rawBall_normalize (t : Fin 3 → M) :
    @rawBall M (CanonicalStructure.normalize (M := M)) t = rawBall t := by
  ext x
  by_cases ht : ∀ i, iVF (t i)
  · by_cases hx : iVF x
    · have hxs : ∀ i : Fin 4, sortEval SortTag.vf (tuple t x i) := by
        intro i; fin_cases i
        · exact ht 0
        · exact ht 1
        · exact ht 2
        · exact hx
      exact and_congr Iff.rfl (and_congr Iff.rfl
        (CanonicalStructure.realize_normalize hM (fun _ : Fin 0 => .vf)
          Fin.elim0 (fun i => i.elim0) body (fun _ => .vf) (tuple t x) body_sorted hxs))
    · change (_ ∧ iVF x ∧ _) ↔ (_ ∧ iVF x ∧ _)
      simp only [hx, and_false, false_and]
  · change ((∀ i, iVF (t i)) ∧ _ ∧ _) ↔ ((∀ i, iVF (t i)) ∧ _ ∧ _)
    simp only [ht, false_and]

end SpecialTransformations.Section3.ClosedBallCodes
