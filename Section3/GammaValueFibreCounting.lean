module

public import Section3.GammaCodeDefinability
public import Section3.GammaParameters
public import Section3.FiniteValueDefinability
public import Section3.GammaSupport

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3.GammaParameters
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

private theorem scalar_same_normalized_definable (S : Set M) :
    @Set.Definable M S LRV (CanonicalStructure.normalize (M := M)) (Fin 2)
      {z | SameScalar (z 0) (z 1)} := by
  have he : {z : Fin 2 → M | @SameScalar M (CanonicalStructure.normalize (M := M)) (z 0) (z 1)} =
      {z | SameScalar (z 0) (z 1)} := Set.ext (fun z => same_scalar_normalize _ _)
  exact he ▸ @same_scalar_definable M (CanonicalStructure.normalize (M := M)) S

def valueFibreRelation {S : Set M} {k : ℕ} (Q : Relation S k 1 (fun _ => .rv)) :
    Set ((Fin (k+1) → M) × M) :=
  {p | (Fin.init p.1,fun _ : Fin 1 => p.2) ∈ Q.carrier ∧ SameScalar p.2 (p.1 (Fin.last k))}

theorem valueFibreRelation_definable {S : Set M} {k : ℕ} (Q : Relation S k 1 (fun _ => .rv)) :
    @RawClosure.Tuple.RelationDefinable M (CanonicalStructure.normalize (M := M)) (k+1) S
      (valueFibreRelation Q) := by
  let U := Q.carrier
  let V := valueFibreRelation Q
  have hQ := Q.definable
  have hSame := scalar_same_normalized_definable (M := M) S
  let N := CanonicalStructure.normalize (M := M)
  letI := N
  let α := Fin (k+1) ⊕ Fin 1
  let idx : Fin k ⊕ Fin 1 → α := Sum.elim (fun i => .inl i.castSucc) (fun _ => .inr 0)
  have hq := hQ.preimage_comp idx
  have he := hSame.preimage_comp (![Sum.inr 0,Sum.inl (Fin.last k)] : Fin 2 → α)
  change S.Definable LRV {z : α → M | (z ∘ Sum.inl,z (.inr 0)) ∈ V}
  convert hq.inter he using 1
  ext z
  rfl

theorem valueFibreRelation_code_invariant {S : Set M} {k : ℕ}
    (Q : Relation S k 1 (fun _ => .rv)) (t u : Fin k → Code (M := M))
    (htu : values t = values u) (w x : M) :
    (Fin.snoc (rawTuple t) w,x) ∈ valueFibreRelation Q ↔
      (Fin.snoc (rawTuple u) w,x) ∈ valueFibreRelation Q := by
  simp only [valueFibreRelation,Set.mem_ofPred_eq,Fin.init_snoc,Fin.snoc_last]
  exact and_congr (Q.invariant t u htu (fun _ => x)) Iff.rfl

/-- A uniform first-order count on the actual RV points within a value
class. It retains the original Gamma support and requires no global bound. -/
def smallValueRelation {S : Set M} {k : ℕ} (Q : Relation S k 1 (fun _ => .rv)) (d : ℕ) :
    Relation S k 1 (fun _ => .rv) where
  carrier := {p | (∃ x, (Fin.snoc p.1 (p.2 0),x) ∈ valueFibreRelation Q) ∧
    Fin.snoc p.1 (p.2 0) ∉ RawClosure.Tuple.HasMore (valueFibreRelation Q) d}
  definable := by
    let R := valueFibreRelation Q
    have hR := valueFibreRelation_definable Q
    let N := CanonicalStructure.normalize (M := M)
    letI := N
    let α := Fin k ⊕ Fin 1
    let F (z : α → M) : Fin (k+1) → M := Fin.snoc (z ∘ Sum.inl) (z (.inr 0))
    have hF : S.DefinableMap LRV F := by
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [F,Fin.snoc_last] using
          (Set.DefinableFun.proj (L := LRV) (A := S) (i := Sum.inr 0))
      · simpa only [F,Fin.snoc_castSucc,Function.comp_apply] using
          (Set.DefinableFun.proj (L := LRV) (A := S) (i := Sum.inl j))
    have hd := RawClosure.Tuple.domain_definable S R hR
    have hm := RawClosure.Tuple.hasMore_definable S R hR d
    exact (hd.inter hm.compl).preimage_map hF
  proper := by
    rintro p ⟨⟨x,hx⟩,_⟩
    have hQ : (p.1,fun _ : Fin 1 => x) ∈ Q.carrier := by
      simpa only [Fin.init_snoc] using hx.1
    have hS : SameScalar x (p.2 0) := by simpa only [Fin.snoc_last] using hx.2
    refine ⟨(Q.proper _ hQ).1,?_⟩
    intro i; fin_cases i; exact hS.2.1.1
  invariant := by
    intro t u htu b
    have hrow := valueFibreRelation_code_invariant Q t u htu (b 0)
    have hm : Fin.snoc (rawTuple t) (b 0) ∈ RawClosure.Tuple.HasMore (valueFibreRelation Q) d ↔
        Fin.snoc (rawTuple u) (b 0) ∈ RawClosure.Tuple.HasMore (valueFibreRelation Q) d := by
      change (∃ x : Fin (d+1) → M, Function.Injective x ∧
        ∀ i, (Fin.snoc (rawTuple t) (b 0),x i) ∈ valueFibreRelation Q) ↔
        (∃ x : Fin (d+1) → M, Function.Injective x ∧
        ∀ i, (Fin.snoc (rawTuple u) (b 0),x i) ∈ valueFibreRelation Q)
      exact exists_congr (fun x => and_congr Iff.rfl (forall_congr' (fun i => hrow (x i))))
    exact and_congr (exists_congr hrow) (not_congr hm)

theorem valueFibreRelation_row {S : Set M} {k : ℕ} (Q : Relation S k 1 (fun _ => .rv))
    (γ : Fin k → Values.Gamma (M := M)) (A : Set M)
    (hQA : Q.fibre γ = {z | z 0 ∈ A}) (w x : M) :
    (Fin.snoc (rawTuple (representatives γ)) w,x) ∈ valueFibreRelation Q ↔
      (![w],x) ∈ RawValueFibres.relation A := by
  have hQx : (rawTuple (representatives γ),fun _ : Fin 1 => x) ∈ Q.carrier ↔ x ∈ A :=
    Set.ext_iff.mp hQA (fun _ => x)
  simp only [valueFibreRelation,Set.mem_ofPred_eq,Fin.init_snoc,Fin.snoc_last]
  rw [hQx]
  change (x ∈ A ∧ SameScalar x w) ↔
    (iRV w ∧ w ≠ iRVZero ∧ x ∈ A ∧ iLe w x ∧ iLe x w)
  constructor
  · rintro ⟨hx,hS⟩
    exact ⟨hS.2.1.1,hS.2.1.2,hx,hS.2.2.2,hS.2.2.1⟩
  · rintro ⟨hw,hw0,hx,hwx,hxw⟩
    have hxRV : iRV x := (Q.proper _ (hQx.mpr hx)).2 0
    have hx0 : x ≠ iRVZero := by
      intro hz
      rw [hz] at hxw
      exact hw0 (RVCalc.le_infty_eq hM hw hxw)
    exact ⟨hx,⟨hxRV,hx0⟩,⟨hw,hw0⟩,hxw,hwx⟩

theorem smallValueRelation_fibre {S : Set M} {k : ℕ} (Q : Relation S k 1 (fun _ => .rv))
    (γ : Fin k → Values.Gamma (M := M)) (A : Set M)
    (hQA : Q.fibre γ = {z | z 0 ∈ A}) (d : ℕ) :
    (smallValueRelation Q d).fibre γ = {z | z 0 ∈ RawValueFibres.smallNonempty A d} := by
  ext z
  have hrow := valueFibreRelation_row Q γ A hQA (z 0)
  change ((∃ x, (Fin.snoc (rawTuple (representatives γ)) (z 0),x) ∈ valueFibreRelation Q) ∧
    ¬ ∃ u : Fin (d+1) → M, Function.Injective u ∧
      ∀ i, (Fin.snoc (rawTuple (representatives γ)) (z 0),u i) ∈ valueFibreRelation Q) ↔
    ((∃ x, (![z 0],x) ∈ RawValueFibres.relation A) ∧
    ¬ ∃ u : Fin (d+1) → M, Function.Injective u ∧
      ∀ i, (![z 0],u i) ∈ RawValueFibres.relation A)
  exact and_congr (exists_congr hrow) (not_congr (exists_congr
    (fun u => and_congr Iff.rfl (forall_congr' (fun i => hrow (u i))))))

theorem small_nonempty_definable_base (B : Base (M := M)) (A : Set M)
    (hA : DefinableAtBase B .rv A) (d : ℕ) :
    DefinableAtBase B .rv (RawValueFibres.smallNonempty A d) := by
  obtain ⟨k,γ,hγ,Q,hQA⟩ := hA
  exact ⟨k,γ,hγ,smallValueRelation Q d,smallValueRelation_fibre Q γ A hQA d⟩

end SpecialTransformations.Section3.GammaParameters
