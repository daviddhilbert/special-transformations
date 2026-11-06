import Section4.DefinableGeometry
import Mathlib.Data.Finite.Prod

open FirstOrder FirstOrder.Language

namespace SpecialTransformations.DefinableGeometry

variable {L : Language} {M : Type} [L.Structure M]

namespace Space

variable (P Q R : Space L M)

/-- A finite power retains all codes in every coordinate. -/
def power (ι : Type) [Finite ι] : Space L M where
  Carrier := ι → P.Carrier
  Index := ι × P.Index
  finiteIndex := inferInstance
  domain := {z | ∀ i, (fun j => z (i, j)) ∈ P.domain}
  domain_definable := by
    have h (i : ι) := P.domain_definable.preimage_comp (fun j => (i, j))
    convert Set.definable_iInter_of_finite h using 1
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage]
    rfl
  decode z i := P.decode ⟨fun j => z.val (i, j), z.property i⟩
  onto x := by
    choose c hc using fun i => P.onto (x i)
    exact ⟨⟨fun ij => (c ij.1).val ij.2, fun i => (c i).property⟩, funext hc⟩
  diagonal_definable := by
    have h (i : ι) := P.diagonal_definable.preimage_comp
      (Sum.elim (fun j => Sum.inl (i, j)) (fun j => Sum.inr (i, j)) :
        P.Index ⊕ P.Index → (ι × P.Index) ⊕ (ι × P.Index))
    have hall := Set.definable_iInter_of_finite h
    convert hall using 1
    ext z
    simp only [Set.mem_iInter, Set.mem_preimage]
    constructor
    · rintro ⟨hx, hy, he⟩ i
      exact ⟨hx i, hy i, congrFun he i⟩
    · intro h
      exact ⟨fun i => (h i).choose, fun i => (h i).choose_spec.choose,
        funext (fun i => (h i).choose_spec.choose_spec)⟩

theorem RelationDefinable.pair {S : Set M} {r : P.Carrier → Q.Carrier → Prop}
    {t : P.Carrier → R.Carrier → Prop}
    (hr : P.RelationDefinable Q S r) (ht : P.RelationDefinable R S t) :
    P.RelationDefinable (Q.prod R) S (fun x yz => r x yz.1 ∧ t x yz.2) := by
  let i₁ : P.Index ⊕ Q.Index → P.Index ⊕ (Q.Index ⊕ R.Index) := Sum.map id Sum.inl
  let i₂ : P.Index ⊕ R.Index → P.Index ⊕ (Q.Index ⊕ R.Index) := Sum.map id Sum.inr
  have he : P.relation (Q.prod R) (fun x yz => r x yz.1 ∧ t x yz.2) =
      ((fun z => z ∘ i₁) ⁻¹' P.relation Q r) ∩
      ((fun z => z ∘ i₂) ⁻¹' P.relation R t) := by
    ext z
    constructor
    · rintro ⟨hx, ⟨hy, hz⟩, hr, ht⟩
      exact ⟨⟨hx, hy, hr⟩, ⟨hx, hz, ht⟩⟩
    · rintro ⟨⟨hx, hy, hr⟩, ⟨_, hz, ht⟩⟩
      exact ⟨hx, ⟨hy, hz⟩, hr, ht⟩
  change S.Definable L _
  rw [he]
  exact (hr.preimage_comp i₁).inter (ht.preimage_comp i₂)

end Space

namespace Map

variable {P Q R : Space L M} {S : Set M}
variable {A : DefSet P S} {B : DefSet Q S} {C : DefSet R S}

def pair (f : Map A B) (g : Map A C) : Map A (B.prod C) where
  toFun a := ⟨((f a).val, (g a).val), (f a).property, (g a).property⟩
  graph_definable := (f.graph_definable.pair P Q R g.graph_definable).congr P (Q.prod R) (by
    intro x yz
    constructor
    · rintro ⟨⟨a, rfl, hf⟩, ⟨b, hb, hg⟩⟩
      have he : b = a := Subtype.ext hb
      subst b
      exact ⟨a, rfl, Prod.ext hf hg⟩
    · rintro ⟨a, rfl, he⟩
      exact ⟨⟨a, rfl, congrArg Prod.fst he⟩, ⟨a, rfl, congrArg Prod.snd he⟩⟩)

@[simp] theorem pair_apply (f : Map A B) (g : Map A C) (a : A) :
    (f.pair g a).val = ((f a).val, (g a).val) := rfl

theorem definable_preimage (f : Map A B) {T : Set Q.Carrier} (hT : Q.Definable S T) :
    P.Definable S {x | ∃ a : A, a.val = x ∧ (f a).val ∈ T} := by
  have h := (f.graph_definable.inter P Q (hT.right_relation P Q)).exists_right P Q
  have he : {x : P.Carrier | ∃ y, (∃ a : A, a.val = x ∧ (f a).val = y) ∧ y ∈ T} =
      {x : P.Carrier | ∃ a : A, a.val = x ∧ (f a).val ∈ T} := by
    ext x
    simp only [Set.mem_setOf_eq]
    aesop
  rwa [he] at h

def image (f : Map A B) : DefSet Q S :=
  ⟨Set.range (fun a => (f a).val), f.definable_image⟩

def toImage (f : Map A B) : Map A f.image where
  toFun a := ⟨(f a).val, Set.mem_range_self a⟩
  graph_definable := f.graph_definable

def toUniv (f : Map A B) : Map A (DefSet.univ Q S) where
  toFun a := ⟨(f a).val, Set.mem_univ _⟩
  graph_definable := f.graph_definable

@[simp] theorem toUniv_apply (f : Map A B) (a : A) : (f.toUniv a).val = (f a).val := rfl

theorem toUniv_injective {f : Map A B} (hf : Function.Injective f) :
    Function.Injective f.toUniv := by
  intro a b he
  apply hf
  apply Subtype.ext
  exact congrArg (fun z : DefSet.univ Q S => z.val) he

def restrict {A' : DefSet P S} (f : Map A B) (h : A'.carrier ⊆ A.carrier) : Map A' B :=
  f.comp (Map.inclusion h)

end Map

end SpecialTransformations.DefinableGeometry
