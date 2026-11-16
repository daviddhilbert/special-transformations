module

public import Section4.RVInfiniteValueDefinability
public import Section4.CanonicalNormalization
public import Section3.GammaGoodRelations

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {g r : ℕ}

def rvLastRelation (Q : Relation S g (r + 1) (fun _ => .rv)) :
    Set ((Fin (g + r) → M) × M) :=
  {p | (p.1 ∘ Fin.castAdd r, Fin.snoc (p.1 ∘ Fin.natAdd g) p.2) ∈ Q.carrier}

theorem rvLastRelation_definable (hcan : CanonicalStructure.IsCanonical (M := M))
    (Q : Relation S g (r + 1) (fun _ => .rv)) :
    RawClosure.Tuple.RelationDefinable S (rvLastRelation Q) := by
  have hQ := Q.definable
  rw [canonical_normalize_eq hcan] at hQ
  let idx : Fin g ⊕ Fin (r + 1) → Fin (g + r) ⊕ Fin 1 :=
    Sum.elim (fun i => Sum.inl (Fin.castAdd r i))
      (Fin.lastCases (Sum.inr 0) (fun i => Sum.inl (Fin.natAdd g i)))
  have h := hQ.preimage_comp idx
  change S.Definable LRV _
  convert h using 1
  ext z
  have he : (z ∘ idx) ∘ Sum.inr =
      Fin.snoc ((z ∘ Sum.inl) ∘ Fin.natAdd g) (z (Sum.inr 0)) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Function.comp_apply, idx, Sum.elim_inr, Fin.lastCases_last, Fin.snoc_last]
    · simp only [Function.comp_apply, idx, Sum.elim_inr, Fin.lastCases_castSucc, Fin.snoc_castSucc]
  change ((z ∘ Sum.inl) ∘ Fin.castAdd r,
    Fin.snoc ((z ∘ Sum.inl) ∘ Fin.natAdd g) (z (Sum.inr 0))) ∈ Q.carrier ↔
      ((z ∘ idx) ∘ Sum.inl, (z ∘ idx) ∘ Sum.inr) ∈ Q.carrier
  rw [he]
  rfl

def rvInfiniteLastCarrier (Q : Relation S g (r + 1) (fun _ => .rv)) (j : Fin g) :
    Set ((Fin g → M) × (Fin r → M)) :=
  {p | {x | SameScalar x (p.1 j) ∧ (p.1, Fin.snoc p.2 x) ∈ Q.carrier}.Infinite}

theorem rvInfiniteLastCarrier_proper
    (Q : Relation S g (r + 1) (fun _ => .rv)) (j : Fin g)
    (p : (Fin g → M) × (Fin r → M)) (hp : p ∈ rvInfiniteLastCarrier Q j) :
    Proper p.1 ∧ ∀ i, iRV (p.2 i) := by
  obtain ⟨x, _, hx⟩ := hp.nonempty
  have hQ := Q.proper _ hx
  exact ⟨hQ.1, fun i => by
    simpa only [Fin.snoc_castSucc, sortEval, iRV] using hQ.2 i.castSucc⟩

theorem rvInfiniteLastCarrier_invariant
    (Q : Relation S g (r + 1) (fun _ => .rv)) (j : Fin g)
    (t u : Fin g → Code (M := M)) (htu : values t = values u) (b : Fin r → M) :
    (rawTuple t, b) ∈ rvInfiniteLastCarrier Q j ↔
      (rawTuple u, b) ∈ rvInfiniteLastCarrier Q j := by
  have he : {x | SameScalar x (rawTuple t j) ∧ (rawTuple t, Fin.snoc b x) ∈ Q.carrier} =
      {x | SameScalar x (rawTuple u j) ∧ (rawTuple u, Fin.snoc b x) ∈ Q.carrier} := by
    ext x
    exact and_congr (same_scalar_with_codes_iff x (t j) (u j) (congrFun htu j))
      (Q.invariant t u htu (Fin.snoc b x))
  exact congrArg Set.Infinite he |>.to_iff

theorem rvInfiniteLastCarrier_definable
    (hcan : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (Q : Relation S g (r + 1) (fun _ => .rv)) (j : Fin g) :
    @Set.Definable M S LRV (CanonicalStructure.normalize (M := M)) (Fin g ⊕ Fin r)
      {z | (z ∘ Sum.inl, z ∘ Sum.inr) ∈ rvInfiniteLastCarrier Q j} := by
  have hi := infinite_RV_value_fibres_definable hcan h00 hs hsmall
    (rvLastRelation Q) (rvLastRelation_definable hcan Q)
  let F (z : Fin g ⊕ Fin r → M) : Fin (g + r + 1) → M :=
    Fin.snoc (Fin.append (z ∘ Sum.inl) (z ∘ Sum.inr)) (z (Sum.inl j))
  have hF : S.DefinableMap LRV F := by
    intro i
    refine Fin.lastCases ?_ (fun q => ?_) i
    · simpa only [F, Fin.snoc_last] using
        (Set.DefinableFun.proj (L := LRV) (A := S) (i := Sum.inl j))
    · refine Fin.addCases (fun a => ?_) (fun b => ?_) q
      · simpa only [F, Fin.snoc_castSucc, Fin.append_left, Function.comp_apply] using
          (Set.DefinableFun.proj (L := LRV) (A := S) (i := Sum.inl a))
      · simpa only [F, Fin.snoc_castSucc, Fin.append_right, Function.comp_apply] using
          (Set.DefinableFun.proj (L := LRV) (A := S) (i := Sum.inr b))
  have h := hi.preimage_map hF
  rw [canonical_normalize_eq hcan]
  convert h using 1
  ext z
  have hrow : {x | (F z, x) ∈ rawRVValuePart (rvLastRelation Q) true} =
      {x | SameScalar x (z (Sum.inl j)) ∧
        (z ∘ Sum.inl, Fin.snoc (z ∘ Sum.inr) x) ∈ Q.carrier} := by
    ext x
    simp only [rawRVValuePart, rvLastRelation, Bool.true_eq, ite_true, Set.mem_ofPred_eq,
      F, Fin.snoc_last, Fin.init_snoc, Function.comp_def, Fin.append_left, Fin.append_right]
  change Set.Infinite _ ↔ (NonzeroRV (F z (Fin.last (g + r))) ∧ Set.Infinite _)
  rw [hrow]
  simp only [F, Fin.snoc_last]
  constructor
  · intro hz
    obtain ⟨x, hx, _⟩ := hz.nonempty
    exact ⟨hx.2.1, hz⟩
  · exact fun hz => hz.2

/-- One step of the paper's repeated infinite-fibre construction. The
entire Gamma tuple is retained and no RV representative is named in S. -/
def rvInfiniteLast
    (hcan : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (Q : Relation S g (r + 1) (fun _ => .rv)) (j : Fin g) :
    Relation S g r (fun _ => .rv) where
  carrier := rvInfiniteLastCarrier Q j
  definable := rvInfiniteLastCarrier_definable hcan h00 hs hsmall Q j
  proper := rvInfiniteLastCarrier_proper Q j
  invariant := rvInfiniteLastCarrier_invariant Q j

end SpecialTransformations.Section4

end
