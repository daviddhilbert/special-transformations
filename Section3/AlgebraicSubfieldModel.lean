import Section3.AlgebraicRVLifting

/- Component: ValuedSubfieldWitness -/
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
namespace SpecialTransformations.Section3

def valuedSubfieldSubstructure {N Γ : Type} [Field N] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation N Γ) (F : Subfield N) :
    letI := FirstOrder.valStructure v
    Language.val.Substructure N := by
  letI := FirstOrder.valStructure v
  refine { carrier := F, fun_mem := ?_ }
  intro n f xs hxs
  cases f with
  | add => exact F.add_mem (hxs 0) (hxs 1)
  | mul => exact F.mul_mem (hxs 0) (hxs 1)
  | neg => exact F.neg_mem (hxs 0)
  | zero => exact F.zero_mem
  | one => exact F.one_mem

/-- The proved valued QE embedding identifies the actual subfield with
an elementary substructure, retaining its exact inherited operations. -/
noncomputable def valuedSubfieldElementarySubstructure {N Γ : Type} [Field N] [IsAlgClosed N]
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation N Γ)
    (F : Subfield N) [IsAlgClosed F]
    (hnt : ∃ x : F, x ≠ 0 ∧ v x.val ≠ 1) :
    letI := FirstOrder.valStructure v
    Language.val.ElementarySubstructure N := by
  letI := FirstOrder.valStructure v
  letI := FirstOrder.valStructure (v.comap F.subtype)
  let T := valuedSubfieldSubstructure v F
  let e := valuedSubfieldElementary v F hnt
  have hstructure :
      @Substructure.inducedStructure Language.val N (FirstOrder.valStructure v) T =
        FirstOrder.valStructure (v.comap F.subtype) := by
    apply Language.Structure.ext
    · funext n f xs
      cases f <;> rfl
    · funext n r xs
      cases r <;> rfl
  refine ⟨T,?_⟩
  intro n φ x
  have he := e.map_formula' φ x
  change φ.Realize (Subtype.val ∘ x) ↔
    @Formula.Realize Language.val F (FirstOrder.valStructure (v.comap F.subtype)) (Fin n) φ x at he
  rw [← hstructure] at he
  exact he

theorem valued_definable_nonempty_meets_subfield {N Γ : Type} [Field N] [IsAlgClosed N]
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation N Γ)
    (F : Subfield N) [IsAlgClosed F] (hnt : ∃ x : F, x ≠ 0 ∧ v x.val ≠ 1)
    (U : Set N)
    (hU : @Set.Definable₁ N (F : Set N) Language.val (FirstOrder.valStructure v) U)
    (hne : U.Nonempty) : ∃ x : F, x.val ∈ U := by
  letI := FirstOrder.valStructure v
  let E := valuedSubfieldElementarySubstructure v F hnt
  obtain ⟨x,hxU,hxF⟩ := E.meetsDefinable U hne hU
  exact ⟨⟨x,hxF⟩,hxU⟩

end SpecialTransformations.Section3

/- Component: SubfieldDefinableWitness -/
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)

include hv in
theorem decode_preimage_definable_over_subfield (F : Subfield (VFType (M := M)))
    (S A : Set M) (hS : S ⊆ Subtype.val '' (F : Set (VFType (M := M))))
    (σ : SortTag) (hA : DefinableAt S σ A) :
    @Set.Definable₁ (VFType (M := M)) (F : Set (VFType (M := M))) Language.val
      (FirstOrder.valStructure v) {x | RVRepresentatives.decode σ x ∈ A} := by
  letI := FirstOrder.valStructure v
  obtain ⟨⟨p,φ,hw,heq⟩,hsort⟩ := hA
  have hp (i : Fin p.length) : ∃ x : F, (x.val : VFType (M := M)).val = p.values i := by
    obtain ⟨x,hx,he⟩ := hS (p.mem_base i)
    exact ⟨⟨x,hx⟩,he⟩
  choose q hq using hp
  have hps (i : Fin p.length) : p.sorts i = .vf := by
    cases hi : p.sorts i with
    | vf => rfl
    | rv =>
      have hr : iRV (p.values i) := by simpa only [hi,sortEval,iRV] using p.sorted i
      have hvf : iVF (p.values i) := (hq i) ▸ (q i).val.property
      exact (TypedModelMap.not_rv_of_vf hvf hr).elim
  obtain ⟨ψ,hψq,hψw,hψ⟩ := theorem_2_3_quantifier_elimination
    (Fin p.length) p.sorts 1 (fun _ => σ) φ hw
  have hdecode : (fun i => RVRepresentatives.decode (p.sorts i) (q i).val) = p.values := by
    funext i
    rw [hps i]
    exact hq i
  have hd := RVRepresentatives.Over.qf_definable v F hv p.sorts (fun _ : Fin 1 => σ)
    (fun _ : Fin 1 → VFType (M := M) => fun i => (q i).val) (fun z => z)
    (fun i => ValuedOver.constant v F (q i).val (q i).property)
    (fun _ => Set.DefinableFun.proj Language.val) ψ hψq hψw
  rw [hdecode] at hd
  change (F : Set (VFType (M := M))).Definable Language.val
    {z : Fin 1 → VFType (M := M) | RVRepresentatives.decode σ (z 0) ∈ A}
  convert hd using 1
  ext z
  have he := Set.ext_iff.mp heq ![RVRepresentatives.decode σ (z 0)]
  change RVRepresentatives.decode σ (z 0) ∈ A ↔
    ψ.Realize p.values (fun i => RVRepresentatives.decode σ (z i))
  have hz : (fun i => RVRepresentatives.decode σ (z i)) =
      (![RVRepresentatives.decode σ (z 0)] : Fin 1 → M) := by
    funext i; fin_cases i; rfl
  rw [hz]
  exact he.trans (and_iff_right (by
    intro i; fin_cases i; exact RVRepresentatives.decode_sorted σ (z 0))) |>.trans
      (hψ M hM p.values _ p.sorted (by
        intro i; fin_cases i; exact RVRepresentatives.decode_sorted σ (z 0)))

include hv in
theorem sorted_definable_nonempty_meets_subfield
    (F : Subfield (VFType (M := M))) [IsAlgClosed F]
    (hnt : ∃ x : F, x ≠ 0 ∧ v x.val ≠ 1)
    (S A : Set M) (hS : S ⊆ Subtype.val '' (F : Set (VFType (M := M))))
    (σ : SortTag) (hA : DefinableAt S σ A) (hne : A.Nonempty) :
    ∃ x : F, RVRepresentatives.decode σ x.val ∈ A := by
  letI : IsAlgClosed (VFType (M := M)) := VFAlgClosed.isAlgClosed_vfType
  have hd := decode_preimage_definable_over_subfield v hv F S A hS σ hA
  have hn : {x : VFType (M := M) | RVRepresentatives.decode σ x ∈ A}.Nonempty := by
    obtain ⟨a,ha⟩ := hne
    cases σ with
    | vf => exact ⟨⟨a,hA.2 ha⟩,ha⟩
    | rv =>
      obtain ⟨x,hx⟩ := CanonicalRV.encodedRv_surjective (⟨a,hA.2 ha⟩ : CanonicalRV.RVSort M)
      refine ⟨x,?_⟩
      change (CanonicalRV.encodedRv x).val ∈ A
      rw [hx]
      exact ha
  exact valued_definable_nonempty_meets_subfield v F hnt _ hd hn

end SpecialTransformations.Section3
