import Section6.HenselianElimination

/-! Naming an arbitrary sorted base preserves the constructed relative
QE theorem. Constants are opened as free parameters and then closed by
Mathlib's actual syntax equivalence; no finiteness of the named base is
required. The atomic diagram supplies the sorts of the named constants. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.Milestone0.LRV FirstOrder.Language.sum
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Section6.NamedLogic
open RVTermSupport

private theorem rel_one_realize {L : Language} {I M : Type} [L.Structure M]
    {n : ℕ} (r : L.Relations 1) (ts : Fin 1 → L.Term (I ⊕ Fin n))
    (v : I → M) (x : Fin n → M) :
    (BoundedFormula.rel r ts).Realize v x ↔
      Structure.RelMap r ![(ts 0).realize (Sum.elim v x)] := by
  change Structure.RelMap r _ ↔ _
  have he : (fun i => (ts i).realize (Sum.elim v x)) =
      ![(ts 0).realize (Sum.elim v x)] := by
    funext i
    fin_cases i
    rfl
  rw [he]

def WellSorted {E : Language} {B I : Type} (sB : B → SortTag) (sI : I → SortTag)
    {n : ℕ} (sn : Fin n → SortTag) (φ : (Expanded E)[[B]].BoundedFormula I n) : Prop :=
  ExpandedLogic.WellSorted (Sum.elim sB sI) sn (BoundedFormula.constantsVarsEquiv φ)

def IsVFQF {E : Language} {B I : Type} {n : ℕ}
    (φ : (Expanded E)[[B]].BoundedFormula I n) : Prop :=
  ExpandedLogic.IsVFQF (BoundedFormula.constantsVarsEquiv φ)

def HasVFQE {E : Language} {B : Type} (sB : B → SortTag)
    (T : (Expanded E)[[B]].Theory) : Prop :=
  ∀ (I : Type) (sI : I → SortTag) (n : ℕ) (sn : Fin n → SortTag)
    (φ : (Expanded E)[[B]].BoundedFormula I n), WellSorted sB sI sn φ →
    ∃ ψ : (Expanded E)[[B]].BoundedFormula I n, IsVFQF ψ ∧ WellSorted sB sI sn ψ ∧
      ∀ (M : Type) [(Expanded E).Structure M] [(Expanded E)[[B]].Structure M]
        [((Expanded E).lhomWithConstants B).IsExpansionOn M], M ⊨ T →
        ∀ (v : I → M) (x : Fin n → M),
          (∀ i, ExpandedLogic.tagEval (E := E) (sI i) (v i)) →
          (∀ i, ExpandedLogic.tagEval (E := E) (sn i) (x i)) →
          (φ.Realize v x ↔ ψ.Realize v x)

theorem of_unnamed {E : Language} {B : Type} (sB : B → SortTag)
    (T : (Expanded E).Theory) (T' : (Expanded E)[[B]].Theory)
    (hQE : ExpandedLogic.HasVFQE T)
    (hbase : ((Expanded E).lhomWithConstants B).onTheory T ⊆ T')
    (hnames : ∀ (M : Type) [(Expanded E).Structure M] [(Expanded E)[[B]].Structure M]
      [((Expanded E).lhomWithConstants B).IsExpansionOn M], M ⊨ T' →
        ∀ b, ExpandedLogic.tagEval (E := E) (sB b) ((Expanded E).con b : M)) :
    HasVFQE sB T' := by
  intro I sI n sn φ hsφ
  obtain ⟨χ, hχ, hsχ, heχ⟩ := hQE (B ⊕ I) (Sum.elim sB sI) n sn
    (BoundedFormula.constantsVarsEquiv φ) hsφ
  let ψ : (Expanded E)[[B]].BoundedFormula I n := BoundedFormula.constantsVarsEquiv.symm χ
  have hψ : BoundedFormula.constantsVarsEquiv ψ = χ := Equiv.apply_symm_apply _ _
  refine ⟨ψ, by simpa only [IsVFQF, hψ] using hχ,
    by simpa only [WellSorted, hψ] using hsχ, ?_⟩
  intro M _ _ _ hM v x hv hx
  have hT' : M ⊨ ((Expanded E).lhomWithConstants B).onTheory T :=
    ⟨fun σ hσ => hM.realize_of_mem σ (hbase hσ)⟩
  have hT : M ⊨ T := (LHom.onTheory_model _ _).mp hT'
  have hz : ∀ i : B ⊕ I, ExpandedLogic.tagEval (E := E) (Sum.elim sB sI i)
      (Sum.elim (fun b => ((Expanded E).con b : M)) v i) := by
    rintro (b | i)
    · exact hnames M hM b
    · exact hv i
  have he := heχ M hT (Sum.elim (fun b => ((Expanded E).con b : M)) v) x hz hx
  have hleft := BoundedFormula.realize_constantsVarsEquiv (φ := φ) (v := v) (xs := x)
  have hright := BoundedFormula.realize_constantsVarsEquiv (φ := ψ) (v := v) (xs := x)
  rw [hψ] at hright
  exact hleft.symm.trans (he.trans hright)

theorem named_sorts {C : Type} [LRV.Structure C] (E : Language)
    (S : LRV.Substructure C) (sS : ↥(S : Set C) → SortTag)
    (hS : ∀ s, sortEval (sS s) (s : C))
    (M : Type) [(Expanded E).Structure M] [(Expanded E)[[(S : Set C)]].Structure M]
    [((Expanded E).lhomWithConstants (S : Set C)).IsExpansionOn M]
    (hM : M ⊨ HenselianTheory.named E S) (s : (S : Set C)) :
    ExpandedLogic.tagEval (E := E) (sS s) ((Expanded E).con s : M) := by
  let σ : LRV[[(S : Set C)]].Sentence := .rel
    (.inl (match sS s with | .vf => Rel.memVF | .rv => Rel.memRV))
    ![(LRV.con s).term]
  have hσ : C ⊨ σ := by
    change BoundedFormula.Realize σ default default
    rw [rel_one_realize]
    simp only [Matrix.cons_val_zero, Term.realize_con]
    cases h : sS s
    all_goals
      exact Eq.mpr ((LRV.lhomWithConstants (S : Set C)).map_onRelation _ _)
        (by simpa only [h, sortEval] using hS s)
  have hmem : σ ∈ SubstructureTheory.atomicDiagram S := Or.inl ⟨trivial, hσ⟩
  have hm := hM.realize_of_mem ((HenselianTheory.namedNativeInclusion E S).onSentence σ)
    (Or.inr (Set.mem_image_of_mem _ hmem))
  have hm' : Structure.RelMap (L := (Expanded E)[[(S : Set C)]])
      (.inl (ExpandedLogic.sortRelation (sS s))) ![((Expanded E).con s : M)] := by
    change BoundedFormula.Realize (BoundedFormula.rel _ _) default default at hm
    rw [rel_one_realize] at hm
    have hc : (HenselianTheory.namedNativeInclusion E S).onTerm
        ((LRV.con s).term : LRV[[(S : Set C)]].Term (Empty ⊕ Fin 0)) =
        ((Expanded E).con s).term := by
      change Term.func (L := (Expanded E)[[(S : Set C)]]) (l := 0) (.inr s) _ =
        Term.func (L := (Expanded E)[[(S : Set C)]]) (l := 0) (.inr s) _
      congr 1
      exact Subsingleton.elim _ _
    simp only [σ, Function.comp_apply, Matrix.cons_val_zero, hc,
      Term.realize_constants] at hm
    cases h : sS s <;> simpa only [h, ExpandedLogic.sortRelation,
      HenselianTheory.namedNativeInclusion, LHom.sumMap, LHom.sumInl, LHom.id,
      Sum.map_inl] using hm
  change Structure.RelMap (L := Expanded E) (ExpandedLogic.sortRelation (sS s)) _
  exact Eq.mp (((Expanded E).lhomWithConstants (S : Set C)).map_onRelation _ _) hm'

/-- Proposition 6.4 with the original substructure named. All parameter
names and the original free and bound contexts are retained. -/
theorem proposition_6_4 {C : Type} [LRV.Structure C] (E : Language)
    (S : LRV.Substructure C) (sS : ↥(S : Set C) → SortTag)
    (hS : ∀ s, sortEval (sS s) (s : C))
    (hMarker : NativeAmalgamation.SaturatedElementaryExtensionAt)
    (hEarlier : EnvelopeUniformity.EarlierPreparation)
    (hEnvelopes : UniformNormalizedElimination.NativeEnvelopes E)
    (hNormal : HenselianElimination.RVLiteralNormalForm E) :
    HasVFQE sS (HenselianTheory.named E S) := by
  apply of_unnamed sS (HenselianTheory.expanded E) (HenselianTheory.named E S)
    (HenselianElimination.hasVFQE E hMarker hEarlier hEnvelopes hNormal)
  · exact Set.subset_union_left
  · intro M _ _ _ hM s
    exact named_sorts E S sS hS M hM s

end SpecialTransformations.Section6.NamedLogic


