module

public import Section4.RVCoordinates
public import Section4.RVPadding
public import Section3.TupleRelations

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- Pad only with the existing absorbing RV element. -/
def padRVTo {d k : ℕ} (hdk : d ≤ k) (t : Fin d → CanonicalRV.RVSort M) :
    Fin k → CanonicalRV.RVSort M :=
  fun i => if hi : i.val < d then t ⟨i.val, hi⟩ else ⟨iRVZero, rv_zero_mem hM⟩

theorem padRVTo_injective {d k : ℕ} (hdk : d ≤ k) :
    Function.Injective (padRVTo (M := M) hdk) := by
  intro a b he
  funext i
  have h := congrFun he (Fin.castLE hdk i)
  simpa only [padRVTo, Fin.castLE, i.isLt, ↓reduceDIte] using h

def rvPadTo {d k : ℕ} (hdk : d ≤ k) (S : Set M) :
    Map (DefSet.univ (rawRVSpace (M := M) d) S)
      (DefSet.univ (rawRVSpace (M := M) k) S) := by
  let F (z : Fin d → M) : Fin k → M :=
    fun i => if hi : i.val < d then z ⟨i.val, hi⟩ else iRVZero
  have hF : S.DefinableMap LRV F := by
    intro i
    dsimp only [F]
    split_ifs
    · exact Set.DefinableFun.proj LRV
    · exact (Set.DefinableFun.of_empty
        (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.rvZero)).comp
        (show S.DefinableMap LRV (fun _ : Fin d → M => Fin.elim0) from fun j => j.elim0)
  have hcode (c : (rawRVSpace (M := M) d).domain) :
      rvValues (padRVTo hdk ((rawRVSpace d).decode c)) = F c.val := by
    funext i
    dsimp only [rvValues, padRVTo, F]
    split_ifs with hi
    · exact congrFun (rvValues_decode c) ⟨i.val, hi⟩
    · rfl
  refine Map.ofCodes _ (padRVTo hdk) F hF
    (fun c => ⟨padRVTo hdk ((rawRVSpace d).decode c), hcode c⟩) ?_
  intro c
  apply rvValues_injective
  exact (rvValues_decode _).trans (hcode c).symm

theorem rvPadTo_injective {d k : ℕ} (hdk : d ≤ k) (S : Set M) :
    Function.Injective (rvPadTo (M := M) hdk S) := by
  intro a b he
  apply Subtype.ext
  exact padRVTo_injective hdk (congrArg Subtype.val he)

structure RVCoordinatePiece (S : Set M) (n k : ℕ) where
  arity : ℕ
  bound : arity ≤ k
  select : Fin arity → Fin n
  relation : Fin n → RawClosure.Tuple.GoodRelation (n := arity) S

namespace RVCoordinatePiece

variable {S : Set M} {n k : ℕ} (D : RVCoordinatePiece (M := M) S n k)

def codeSet : Set (Fin n → M) :=
  {z | ∀ j, (z ∘ D.select, z j) ∈ (D.relation j).val}

theorem codeSet_definable : S.Definable LRV D.codeSet := by
  have h (j : Fin n) : S.Definable LRV
      {z : Fin n → M | (z ∘ D.select, z j) ∈ (D.relation j).val} :=
    (D.relation j).property.1.preimage_comp (Sum.elim D.select (fun _ => j))
  convert Set.definable_iInter_of_finite h using 1
  ext z
  simp only [codeSet, Set.mem_ofPred_eq, Set.mem_iInter]

def source : DefSet (rawRVSpace (M := M) n) S where
  carrier := {a | rvValues a ∈ D.codeSet}
  definable := by
    change S.Definable LRV _
    convert ((rawRVSpace (M := M) n).domain_definable.mono
      (Set.empty_subset S)).inter D.codeSet_definable using 1
    ext z
    constructor
    · rintro ⟨hz, hD⟩
      refine ⟨hz, ?_⟩
      change rvValues ((rawRVSpace (M := M) n).decode ⟨z, hz⟩) ∈ D.codeSet at hD
      rwa [rvValues_decode] at hD
    · rintro ⟨hz, hD⟩
      refine ⟨hz, ?_⟩
      change rvValues ((rawRVSpace (M := M) n).decode ⟨z, hz⟩) ∈ D.codeSet
      rwa [rvValues_decode]

def projection : Map D.source (DefSet.univ (rawRVSpace (M := M) D.arity) S) := by
  let F (z : Fin n → M) := z ∘ D.select
  have hcode (c : (rawRVSpace (M := M) n).domain) :
      rvValues ((rawRVSpace n).decode c ∘ D.select) = F c.val := by
    funext i
    exact congrFun (rvValues_decode c) (D.select i)
  refine Map.ofCodes _ (fun a => a ∘ D.select) F
    (fun _ => Set.DefinableFun.proj LRV)
    (fun c => ⟨(rawRVSpace n).decode c ∘ D.select, hcode c⟩) ?_
  intro c
  apply rvValues_injective
  exact (rvValues_decode _).trans (hcode c).symm

theorem projection_finite : D.projection.FiniteFibres := by
  intro b
  let H : Set (Fin n → M) := {x | ∀ j, (rvValues b.val, x j) ∈ (D.relation j).val}
  have hH : H.Finite := Set.Finite.pi' (fun j => (D.relation j).property.2 (rvValues b.val))
  have hinj : Function.Injective (fun a : D.source => rvValues a.val) :=
    fun _ _ he => Subtype.ext (rvValues_injective he)
  apply (hH.preimage hinj.injOn).subset
  intro a ha j
  have hv : a.val ∘ D.select = b.val := congrArg Subtype.val ha
  have hj := a.property j
  change (rvValues (a.val ∘ D.select), (a.val j).val) ∈ (D.relation j).val at hj
  rwa [hv] at hj

def paddedProjection : Map D.source (DefSet.univ (rawRVSpace (M := M) k) S) :=
  (rvPadTo D.bound S).comp D.projection

theorem paddedProjection_finite : D.paddedProjection.FiniteFibres :=
  (Map.finiteFibres_of_injective (rvPadTo_injective D.bound S)).comp D.projection_finite

end RVCoordinatePiece

end SpecialTransformations.Section4

end
