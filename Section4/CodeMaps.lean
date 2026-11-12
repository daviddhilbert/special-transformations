module

public import Section4.Products

@[expose] public section

open Classical FirstOrder FirstOrder.Language

namespace SpecialTransformations.DefinableGeometry

variable {L : Language} {M : Type} [L.Structure M]

namespace Map

variable {P Q : Space L M} {S : Set M}

/-- A definable real-code map which descends to the presented values gives
a definable map. Its graph includes every target representative. -/
def ofCodes (A : DefSet P S) (f : P.Carrier → Q.Carrier)
    (F : (P.Index → M) → Q.Index → M) (hF : S.DefinableMap L F)
    (hdom : ∀ c : P.domain, F c.val ∈ Q.domain)
    (hdecode : ∀ c : P.domain, Q.decode ⟨F c.val, hdom c⟩ = f (P.decode c)) :
    Map A (DefSet.univ Q S) where
  toFun a := ⟨f a.val, Set.mem_univ _⟩
  graph_definable := by
    let T (z : P.Index ⊕ Q.Index → M) : Q.Index ⊕ Q.Index → M :=
      Sum.elim (F (z ∘ Sum.inl)) (z ∘ Sum.inr)
    have hT : S.DefinableMap L T := by
      intro i
      cases i with
      | inl i =>
        exact (hF i).comp (show S.DefinableMap L
          (fun z : P.Index ⊕ Q.Index → M => z ∘ Sum.inl) from
            fun _ => Set.DefinableFun.proj L)
      | inr i => exact Set.DefinableFun.proj L
    have hdiag := (Q.diagonal_definable.mono (Set.empty_subset S)).preimage_map hT
    have hA := A.definable.preimage_comp (Sum.inl : P.Index → P.Index ⊕ Q.Index)
    change S.Definable L _
    convert hA.inter hdiag using 1
    ext z
    constructor
    · rintro ⟨hc, hd, a, ha, he⟩
      have hmem : P.decode ⟨z ∘ Sum.inl, hc⟩ ∈ A.carrier := ha ▸ a.property
      refine ⟨⟨hc, hmem⟩, hdom ⟨z ∘ Sum.inl, hc⟩, hd, ?_⟩
      change Q.decode ⟨F (z ∘ Sum.inl), hdom ⟨z ∘ Sum.inl, hc⟩⟩ =
        Q.decode ⟨z ∘ Sum.inr, hd⟩
      rw [hdecode ⟨z ∘ Sum.inl, hc⟩]
      exact (congrArg f ha).symm.trans he
    · rintro ⟨⟨hc, ha⟩, hf, hd, he⟩
      refine ⟨hc, hd, ⟨P.decode ⟨z ∘ Sum.inl, hc⟩, ha⟩, rfl, ?_⟩
      change f (P.decode ⟨z ∘ Sum.inl, hc⟩) = Q.decode ⟨z ∘ Sum.inr, hd⟩
      rw [← hdecode ⟨z ∘ Sum.inl, hc⟩]
      exact he

@[simp] theorem ofCodes_apply (A : DefSet P S) (f : P.Carrier → Q.Carrier)
    (F : (P.Index → M) → Q.Index → M) (hF : S.DefinableMap L F)
    (hdom : ∀ c : P.domain, F c.val ∈ Q.domain)
    (hdecode : ∀ c : P.domain, Q.decode ⟨F c.val, hdom c⟩ = f (P.decode c)) (a : A) :
    (ofCodes A f F hF hdom hdecode a).val = f a.val := rfl

def fst (P Q : Space L M) (S : Set M) (A : DefSet (P.prod Q) S) :
    Map A (DefSet.univ P S) :=
  ofCodes A Prod.fst (fun z => z ∘ Sum.inl)
    (fun _ => Set.DefinableFun.proj L) (fun c => c.property.1) (fun _ => rfl)

def snd (P Q : Space L M) (S : Set M) (A : DefSet (P.prod Q) S) :
    Map A (DefSet.univ Q S) :=
  ofCodes A Prod.snd (fun z => z ∘ Sum.inr)
    (fun _ => Set.DefinableFun.proj L) (fun c => c.property.2) (fun _ => rfl)

@[simp] theorem fst_apply (P Q : Space L M) (S : Set M)
    (A : DefSet (P.prod Q) S) (a : A) : (fst P Q S A a).val = a.val.1 := rfl

@[simp] theorem snd_apply (P Q : Space L M) (S : Set M)
    (A : DefSet (P.prod Q) S) (a : A) : (snd P Q S A a).val = a.val.2 := rfl

end Map

end SpecialTransformations.DefinableGeometry
