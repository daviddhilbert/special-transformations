module

public import Section3.SortedBoolean
public import Section3.BallFibreConstancy

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3.ProfileComposition
variable {M : Type} [sM : LRV.Structure M] {m : ℕ}

def domain (K : Set (Fin 2 → M)) : Set M := {x | ∃ c, ![x,c] ∈ K}

def compose (K : Set (Fin 2 → M)) (U : Set (Fin (m+1) → M)) : Set (Fin (m+1) → M) :=
  {z | (∃ c, ![z 0,c] ∈ K ∧ Fin.cons c (Fin.tail z) ∈ U) ∨ (z 0 ∉ domain K ∧ z ∈ U)}

theorem domain_raw_definable (S : Set M) (K : Set (Fin 2 → M))
    (hK : S.Definable LRV K) : S.Definable₁ LRV (domain K) := by
  let idx : Fin 2 → Fin 1 ⊕ Fin 1 := ![.inl 0, .inr 0]
  have h := (hK.preimage_comp idx).exists_of_finite
  change S.Definable LRV _
  convert h using 1
  ext z
  have he (u : Fin 1 → M) : Sum.elim z u ∘ idx = ![z 0,u 0] := by
    funext i; fin_cases i <;> rfl
  simp only [domain, Set.mem_ofPred_eq, Set.mem_preimage, he]
  change (∃ c, ![z 0,c] ∈ K) ↔ ∃ u : Fin 1 → M, ![z 0,u 0] ∈ K
  exact ⟨fun ⟨c,hc⟩ => ⟨![c],hc⟩, fun ⟨u,hu⟩ => ⟨u 0,hu⟩⟩

theorem compose_raw_definable (S : Set M) (K : Set (Fin 2 → M)) (U : Set (Fin (m+1) → M))
    (hK : S.Definable LRV K) (hU : S.Definable LRV U) : S.Definable LRV (compose K U) := by
  let idx : Fin 2 → Fin (m+1) ⊕ Fin 1 := ![.inl 0, .inr 0]
  let jdx : Fin (m+1) → Fin (m+1) ⊕ Fin 1 := Fin.cons (.inr 0) (fun i => .inl i.succ)
  have hk := hK.preimage_comp idx
  have hu := hU.preimage_comp jdx
  have hex := (hk.inter hu).exists_of_finite
  have hd := (domain_raw_definable S K hK).preimage_comp (fun _ : Fin 1 => (0 : Fin (m+1)))
  convert hex.union (hd.compl.inter hU) using 1
  ext z
  have heK (u : Fin 1 → M) : Sum.elim z u ∘ idx = ![z 0,u 0] := by
    funext i; fin_cases i <;> rfl
  have heU (u : Fin 1 → M) : Sum.elim z u ∘ jdx = Fin.cons (u 0) (Fin.tail z) := by
    funext i
    cases i using Fin.cases with
    | zero => rfl
    | succ j => rfl
  simp only [compose, Set.mem_ofPred_eq, Set.mem_union, Set.mem_inter_iff,
    Set.mem_compl_iff, Set.mem_preimage, heK, heU]
  change ((∃ c, ![z 0,c] ∈ K ∧ Fin.cons c (Fin.tail z) ∈ U) ∨ (z 0 ∉ domain K ∧ z ∈ U)) ↔
    (∃ u : Fin 1 → M, ![z 0,u 0] ∈ K ∧ Fin.cons (u 0) (Fin.tail z) ∈ U) ∨ (z 0 ∉ domain K ∧ z ∈ U)
  exact or_congr ⟨fun ⟨c,hc,hu⟩ => ⟨![c],hc,hu⟩, fun ⟨u,hu,hv⟩ => ⟨u 0,hu,hv⟩⟩ Iff.rfl

def profile (V : Set (Fin (m+1) → M)) (x : Transfer.VFType (M := M)) : Set (Fin m → M) :=
  {ys | Fin.cons x.val ys ∈ V}

theorem graph_profile (V : Set (Fin (m+1) → M))
    (hV : ∀ z ∈ V, iVF (z 0)) : BallFibreConstancy.graph (profile V) = V := by
  ext z
  constructor
  · rintro ⟨x,hx,ht⟩
    have he : Fin.cons x.val (Fin.tail z) = z := by rw [hx, Fin.cons_self_tail]
    exact he ▸ ht
  · intro hz
    let x : Transfer.VFType (M := M) := ⟨z 0,hV z hz⟩
    refine ⟨x,rfl,?_⟩
    change Fin.cons (z 0) (Fin.tail z) ∈ V
    rw [Fin.cons_self_tail]
    exact hz

theorem at_none (K : Set (Fin 2 → M)) (U : Set (Fin (m+1) → M))
    (x : Transfer.VFType (M := M)) (hn : ∀ c, ![x.val,c] ∉ K) :
    profile (compose K U) x = profile U x := by
  ext ys
  change ((∃ c, ![x.val,c] ∈ K ∧ Fin.cons c ys ∈ U) ∨
    (x.val ∉ domain K ∧ Fin.cons x.val ys ∈ U)) ↔ Fin.cons x.val ys ∈ U
  have he : ¬ ∃ c, ![x.val,c] ∈ K := by rintro ⟨c,hc⟩; exact hn c hc
  simp only [hn, false_and, exists_false, false_or, domain, Set.mem_ofPred_eq, he, not_false_eq_true, true_and]

theorem at_some (K : Set (Fin 2 → M)) (U : Set (Fin (m+1) → M))
    (x c : Transfer.VFType (M := M)) (hc : ![x.val,c.val] ∈ K)
    (hfun : ∀ d, ![x.val,d] ∈ K → d = c.val) :
    profile (compose K U) x = profile U c := by
  ext ys
  change ((∃ d, ![x.val,d] ∈ K ∧ Fin.cons d ys ∈ U) ∨
    (x.val ∉ domain K ∧ Fin.cons x.val ys ∈ U)) ↔ Fin.cons c.val ys ∈ U
  constructor
  · rintro (⟨d,hd,hu⟩ | ⟨hn,_⟩)
    · exact hfun d hd ▸ hu
    · exact False.elim (hn ⟨c.val,hc⟩)
  · intro h
    exact Or.inl ⟨c.val,hc,h⟩

variable [hM : M ⊨ Axioms.ACVF]

theorem compose_definable (S : Set M) (K : Set (Fin 2 → M)) (U : Set (Fin (m+1) → M))
    (hK : DefinableOver S (fun _ => .vf) K)
    (hU : DefinableOver S MixedPolynomialSyntax.contextSort U) :
    DefinableOver S MixedPolynomialSyntax.contextSort (compose K U) := by
  have hKN := (definableOver_iff_normalized_raw S (fun _ => .vf) K).mp hK
  have hUN := (definableOver_iff_normalized_raw S MixedPolynomialSyntax.contextSort U).mp hU
  apply (definableOver_iff_normalized_raw S MixedPolynomialSyntax.contextSort _).mpr
  constructor
  · exact @compose_raw_definable M (CanonicalStructure.normalize (M := M)) m S K U hKN.1 hUN.1
  · intro z hz i
    rcases hz with ⟨c,hc,hu⟩ | ⟨_,hu⟩
    · cases i using Fin.cases with
      | zero => exact hKN.2 _ hc 0
      | succ j => exact hUN.2 _ hu j.succ
    · exact hUN.2 z hu i

end SpecialTransformations.Section3.ProfileComposition
