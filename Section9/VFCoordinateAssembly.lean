import Section4.CodeMaps
import Section4.FunctionalRelations
import Section4.VFRealFibres

/-! A finite tuple of scalar VF maps is a definable VF tuple map. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M] {S : Set M} {m : ℕ}
variable {P : Space LRV M} {A : DefSet P S}

noncomputable def vfTupleMap (f : Fin m → Map A (DefSet.univ (rawVFSpace (M := M) 1) S)) :
    Map A (DefSet.univ (rawVFSpace (M := M) m) S) where
  toFun p := ⟨fun i => (f i p).val 0, Set.mem_univ _⟩
  graph_definable := by
    let Q := rawVFSpace (M := M) m
    let W := rawVFSpace (M := M) 1
    let pick (i : Fin m) : P.Index ⊕ W.Index → P.Index ⊕ Q.Index := Sum.elim Sum.inl (fun _ => .inr i)
    let C (i : Fin m) := (fun z => z ∘ pick i) ⁻¹' P.relation W (f i).graph
    have hC (i) : S.Definable LRV (C i) := (f i).graph_definable.preimage_comp (pick i)
    have hdom := (Q.domain_definable.mono (Set.empty_subset S)).preimage_comp
      (Sum.inr : Q.Index → P.Index ⊕ Q.Index)
    have hA := A.definable.preimage_comp (Sum.inl : P.Index → P.Index ⊕ Q.Index)
    have h := (hA.inter hdom).inter (Set.definable_iInter_of_finite hC)
    change S.Definable LRV (P.relation Q (fun x y => ∃ p : A, p.val = x ∧ (fun i => (f i p).val 0) = y))
    convert h using 1
    ext z
    have hleft (i : Fin m) : (z ∘ pick i) ∘ Sum.inl = z ∘ Sum.inl := rfl
    have hright (hy : z ∘ Sum.inr ∈ Q.domain) (i : Fin m) : (z ∘ pick i) ∘ Sum.inr =
        vfValues (fun _ : Fin 1 => (Q.decode ⟨z ∘ Sum.inr, hy⟩) i) := by
      funext j
      exact (congrFun (vfValues_decode ⟨z ∘ Sum.inr, hy⟩) i).symm
    have hi (hx : z ∘ Sum.inl ∈ P.domain) (hy : z ∘ Sum.inr ∈ Q.domain)
        (p : A) (hp : p.val = P.decode ⟨z ∘ Sum.inl, hx⟩) (i : Fin m) :
        z ∈ C i ↔ (f i p).val 0 = (Q.decode ⟨z ∘ Sum.inr, hy⟩) i := by
      change z ∘ pick i ∈ P.relation W (f i).graph ↔ _
      have hwd : (z ∘ pick i) ∘ Sum.inr ∈ W.domain := ⟨_, (hright hy i).symm⟩
      have hw : W.decode ⟨_, hwd⟩ = fun _ => (Q.decode ⟨z ∘ Sum.inr, hy⟩) i :=
        vfValues_injective ((vfValues_decode ⟨_, hwd⟩).trans (hright hy i))
      constructor
      · rintro ⟨hx', hy', p', hp', he⟩
        have hpp : p' = p := Subtype.ext (hp'.trans hp.symm)
        subst p'
        have hww : W.decode ⟨_, hy'⟩ = W.decode ⟨_, hwd⟩ := rfl
        rw [hww, hw] at he
        exact congrFun he 0
      · intro he
        refine ⟨hleft i ▸ hx, hwd, p, hp, ?_⟩
        rw [hw]
        funext j
        fin_cases j
        exact he
    constructor
    · rintro ⟨hx, hy, p, hp, he⟩
      refine ⟨⟨⟨hx, hp ▸ p.property⟩, hy⟩, Set.mem_iInter.mpr (fun i => ?_)⟩
      exact (hi hx hy p hp i).mpr (congrFun he i)
    · rintro ⟨⟨⟨hx, hp⟩, hy⟩, hz⟩
      let p : A := ⟨P.decode ⟨z ∘ Sum.inl, hx⟩, hp⟩
      exact ⟨hx, hy, p, rfl, funext fun i => (hi hx hy p rfl i).mp (Set.mem_iInter.mp hz i)⟩

@[simp] theorem vfTupleMap_apply (f : Fin m → Map A (DefSet.univ (rawVFSpace (M := M) 1) S))
    (p : A) (i : Fin m) : (vfTupleMap f p).val i = (f i p).val 0 := rfl

end SpecialTransformations.Section9
