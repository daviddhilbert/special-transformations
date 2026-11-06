import Mathlib.ModelTheory.Definability
import Mathlib.Data.Finite.Sum

/-!
# Definable sets and maps on real and imaginary presentations

A presentation is a surjection from a definable set of finite real tuples,
with definable equality of the presented values. Definability always refers
to the full preimage. Thus quotient coordinates require no definable section.
The language and structure are parameters; Section4.Spaces specializes this
interface to the normalized released LRV structure.
-/

open FirstOrder FirstOrder.Language

namespace SpecialTransformations.DefinableGeometry

variable {L : Language} {M : Type} [L.Structure M]

structure Space (L : Language) (M : Type) [L.Structure M] where
  Carrier : Type
  Index : Type
  finiteIndex : Finite Index
  domain : Set (Index → M)
  domain_definable : (∅ : Set M).Definable L domain
  decode : domain → Carrier
  onto : Function.Surjective decode
  diagonal_definable : (∅ : Set M).Definable L
    {z : Index ⊕ Index → M | ∃ hx : z ∘ Sum.inl ∈ domain,
      ∃ hy : z ∘ Sum.inr ∈ domain, decode ⟨z ∘ Sum.inl, hx⟩ = decode ⟨z ∘ Sum.inr, hy⟩}

attribute [instance] Space.finiteIndex

namespace Space

variable (P Q R : Space L M)

def preimage (A : Set P.Carrier) : Set (P.Index → M) :=
  {z | ∃ hz : z ∈ P.domain, P.decode ⟨z, hz⟩ ∈ A}

def relation (r : P.Carrier → Q.Carrier → Prop) : Set (P.Index ⊕ Q.Index → M) :=
  {z | ∃ hx : z ∘ Sum.inl ∈ P.domain, ∃ hy : z ∘ Sum.inr ∈ Q.domain,
    r (P.decode ⟨z ∘ Sum.inl, hx⟩) (Q.decode ⟨z ∘ Sum.inr, hy⟩)}

@[simp] theorem preimage_decode (A : Set P.Carrier) (z : P.domain) :
    z.val ∈ P.preimage A ↔ P.decode z ∈ A := by
  simp [preimage]

@[simp] theorem relation_decode (r : P.Carrier → Q.Carrier → Prop)
    (x : P.domain) (y : Q.domain) :
    Sum.elim x.val y.val ∈ P.relation Q r ↔ r (P.decode x) (Q.decode y) := by
  simp [relation]

theorem preimage_injective : Function.Injective P.preimage := by
  intro A B h
  ext x
  obtain ⟨z, rfl⟩ := P.onto x
  exact (P.preimage_decode A z).symm.trans
    ((Set.ext_iff.mp h z.val).trans (P.preimage_decode B z))

def Definable (S : Set M) (A : Set P.Carrier) : Prop := S.Definable L (P.preimage A)

def RelationDefinable (S : Set M) (r : P.Carrier → Q.Carrier → Prop) : Prop :=
  S.Definable L (P.relation Q r)

theorem definable_domain (S : Set M) : S.Definable L P.domain :=
  P.domain_definable.mono (Set.empty_subset S)

theorem definable_empty (S : Set M) : P.Definable S ∅ := by
  change S.Definable L (P.preimage ∅)
  simpa [preimage] using (Set.definable_empty S L (α := P.Index))

theorem definable_univ (S : Set M) : P.Definable S Set.univ := by
  change S.Definable L (P.preimage Set.univ)
  simpa [preimage] using P.definable_domain S

theorem Definable.mono {S T : Set M} {A : Set P.Carrier}
    (hA : P.Definable S A) (hST : S ⊆ T) : P.Definable T A :=
  Set.Definable.mono hA hST

theorem Definable.inter {S : Set M} {A B : Set P.Carrier}
    (hA : P.Definable S A) (hB : P.Definable S B) : P.Definable S (A ∩ B) := by
  have he : P.preimage (A ∩ B) = P.preimage A ∩ P.preimage B := by
    ext z
    by_cases hz : z ∈ P.domain <;> simp [preimage, hz]
  change S.Definable L _
  rw [he]
  exact Set.Definable.inter hA hB

theorem Definable.union {S : Set M} {A B : Set P.Carrier}
    (hA : P.Definable S A) (hB : P.Definable S B) : P.Definable S (A ∪ B) := by
  have he : P.preimage (A ∪ B) = P.preimage A ∪ P.preimage B := by
    ext z
    by_cases hz : z ∈ P.domain <;> simp [preimage, hz]
  change S.Definable L _
  rw [he]
  exact Set.Definable.union hA hB

theorem Definable.compl {S : Set M} {A : Set P.Carrier}
    (hA : P.Definable S A) : P.Definable S Aᶜ := by
  have he : P.preimage Aᶜ = P.domain \ P.preimage A := by
    ext z
    by_cases hz : z ∈ P.domain <;> simp [preimage, hz]
  change S.Definable L _
  rw [he]
  exact (P.definable_domain S).sdiff hA

theorem Definable.sdiff {S : Set M} {A B : Set P.Carrier}
    (hA : P.Definable S A) (hB : P.Definable S B) : P.Definable S (A \ B) :=
  hA.inter P hB.compl

theorem relation_eq_definable (S : Set M) : P.RelationDefinable P S Eq :=
  P.diagonal_definable.mono (Set.empty_subset S)

theorem RelationDefinable.mono {S T : Set M} {r : P.Carrier → Q.Carrier → Prop}
    (hr : P.RelationDefinable Q S r) (hST : S ⊆ T) : P.RelationDefinable Q T r :=
  Set.Definable.mono hr hST

theorem RelationDefinable.congr {S : Set M} {r t : P.Carrier → Q.Carrier → Prop}
    (hr : P.RelationDefinable Q S r) (h : ∀ x y, r x y ↔ t x y) :
    P.RelationDefinable Q S t := by
  have he : r = t := funext (fun x => funext (fun y => propext (h x y)))
  rwa [← he]

theorem RelationDefinable.inter {S : Set M} {r t : P.Carrier → Q.Carrier → Prop}
    (hr : P.RelationDefinable Q S r) (ht : P.RelationDefinable Q S t) :
    P.RelationDefinable Q S (fun x y => r x y ∧ t x y) := by
  have he : P.relation Q (fun x y => r x y ∧ t x y) =
      P.relation Q r ∩ P.relation Q t := by
    ext z
    by_cases hx : z ∘ Sum.inl ∈ P.domain <;>
      by_cases hy : z ∘ Sum.inr ∈ Q.domain <;> simp [relation, hx, hy]
  change S.Definable L _
  rw [he]
  exact Set.Definable.inter hr ht

theorem RelationDefinable.union {S : Set M} {r t : P.Carrier → Q.Carrier → Prop}
    (hr : P.RelationDefinable Q S r) (ht : P.RelationDefinable Q S t) :
    P.RelationDefinable Q S (fun x y => r x y ∨ t x y) := by
  have he : P.relation Q (fun x y => r x y ∨ t x y) =
      P.relation Q r ∪ P.relation Q t := by
    ext z
    by_cases hx : z ∘ Sum.inl ∈ P.domain <;>
      by_cases hy : z ∘ Sum.inr ∈ Q.domain <;> simp [relation, hx, hy]
  change S.Definable L _
  rw [he]
  exact Set.Definable.union hr ht

theorem Definable.left_relation {S : Set M} {A : Set P.Carrier}
    (hA : P.Definable S A) : P.RelationDefinable Q S (fun x _ => x ∈ A) := by
  have he : P.relation Q (fun x _ => x ∈ A) =
      {z | z ∘ Sum.inl ∈ P.preimage A} ∩ {z | z ∘ Sum.inr ∈ Q.domain} := by
    ext z
    by_cases hx : z ∘ Sum.inl ∈ P.domain <;>
      by_cases hy : z ∘ Sum.inr ∈ Q.domain <;> simp [relation, preimage, hx, hy]
  change S.Definable L _
  rw [he]
  exact (hA.preimage_comp Sum.inl).inter ((Q.definable_domain S).preimage_comp Sum.inr)

theorem RelationDefinable.swap {S : Set M} {r : P.Carrier → Q.Carrier → Prop}
    (hr : P.RelationDefinable Q S r) : Q.RelationDefinable P S (fun y x => r x y) := by
  have h := hr.preimage_comp (Sum.swap : P.Index ⊕ Q.Index → Q.Index ⊕ P.Index)
  change S.Definable L _
  convert h using 1
  ext z
  simp only [relation, Set.mem_setOf_eq, Set.mem_preimage, Function.comp_def,
    Sum.swap_inl, Sum.swap_inr]
  constructor <;> rintro ⟨h₁, h₂, h⟩ <;> exact ⟨h₂, h₁, h⟩

theorem Definable.right_relation {S : Set M} {B : Set Q.Carrier}
    (hB : Q.Definable S B) : P.RelationDefinable Q S (fun _ y => y ∈ B) :=
  (hB.left_relation Q P).swap Q P

theorem RelationDefinable.exists_right {S : Set M} {r : P.Carrier → Q.Carrier → Prop}
    (hr : P.RelationDefinable Q S r) : P.Definable S {x | ∃ y, r x y} := by
  have h := hr.exists_of_finite
  change S.Definable L _
  convert h using 1
  ext z
  constructor
  · rintro ⟨hz, y, hy⟩
    obtain ⟨c, hc⟩ := Q.onto y
    exact ⟨c.val, hz, c.property, by simpa [hc] using hy⟩
  · rintro ⟨c, hz, hc, hr⟩
    exact ⟨hz, Q.decode ⟨c, hc⟩, hr⟩

theorem RelationDefinable.comp {S : Set M} {r : P.Carrier → Q.Carrier → Prop}
    {t : Q.Carrier → R.Carrier → Prop}
    (hr : P.RelationDefinable Q S r) (ht : Q.RelationDefinable R S t) :
    P.RelationDefinable R S (fun x z => ∃ y, r x y ∧ t y z) := by
  let i₁ : P.Index ⊕ Q.Index → (P.Index ⊕ R.Index) ⊕ Q.Index :=
    Sum.elim (fun i => Sum.inl (Sum.inl i)) Sum.inr
  let i₂ : Q.Index ⊕ R.Index → (P.Index ⊕ R.Index) ⊕ Q.Index :=
    Sum.elim Sum.inr (fun i => Sum.inl (Sum.inr i))
  have h := ((hr.preimage_comp i₁).inter (ht.preimage_comp i₂)).exists_of_finite
  change S.Definable L _
  convert h using 1
  ext z
  constructor
  · rintro ⟨hx, hz, y, hr, ht⟩
    obtain ⟨c, hc⟩ := Q.onto y
    refine ⟨c.val, ?_, ?_⟩
    · refine ⟨hx, c.property, ?_⟩
      change r (P.decode ⟨z ∘ Sum.inl, hx⟩) (Q.decode c)
      rwa [hc]
    · refine ⟨c.property, hz, ?_⟩
      change t (Q.decode c) (R.decode ⟨z ∘ Sum.inr, hz⟩)
      rwa [hc]
  · rintro ⟨c, ⟨hx, hc, hr⟩, ⟨_, hz, ht⟩⟩
    exact ⟨hx, hz, Q.decode ⟨c, hc⟩, hr, ht⟩

end Space

namespace Space

variable (P Q : Space L M)

/-- Product presentations use every pair of real codes. -/
def prod : Space L M where
  Carrier := P.Carrier × Q.Carrier
  Index := P.Index ⊕ Q.Index
  finiteIndex := inferInstance
  domain := {z | z ∘ Sum.inl ∈ P.domain ∧ z ∘ Sum.inr ∈ Q.domain}
  domain_definable := (P.domain_definable.preimage_comp Sum.inl).inter
    (Q.domain_definable.preimage_comp Sum.inr)
  decode z := (P.decode ⟨z.val ∘ Sum.inl, z.property.1⟩,
    Q.decode ⟨z.val ∘ Sum.inr, z.property.2⟩)
  onto := by
    rintro ⟨x, y⟩
    obtain ⟨c, rfl⟩ := P.onto x
    obtain ⟨d, rfl⟩ := Q.onto y
    exact ⟨⟨Sum.elim c.val d.val, c.property, d.property⟩, rfl⟩
  diagonal_definable := by
    have hp := P.diagonal_definable.preimage_comp
      (Sum.map (Sum.inl : P.Index → P.Index ⊕ Q.Index)
        (Sum.inl : P.Index → P.Index ⊕ Q.Index))
    have hq := Q.diagonal_definable.preimage_comp
      (Sum.map (Sum.inr : Q.Index → P.Index ⊕ Q.Index)
        (Sum.inr : Q.Index → P.Index ⊕ Q.Index))
    convert hp.inter hq using 1
    ext z
    constructor
    · rintro ⟨hx, hy, he⟩
      exact ⟨⟨hx.1, hy.1, congrArg Prod.fst he⟩,
        ⟨hx.2, hy.2, congrArg Prod.snd he⟩⟩
    · rintro ⟨⟨hx, hy, hp⟩, ⟨hx', hy', hq⟩⟩
      exact ⟨⟨hx, hx'⟩, ⟨hy, hy'⟩, Prod.ext hp hq⟩

theorem definable_prod_iff (S : Set M) (r : P.Carrier → Q.Carrier → Prop) :
    (P.prod Q).Definable S {p | r p.1 p.2} ↔ P.RelationDefinable Q S r := by
  have he : (P.prod Q).preimage {p | r p.1 p.2} = P.relation Q r := by
    ext z
    constructor
    · rintro ⟨⟨hx, hy⟩, hr⟩
      exact ⟨hx, hy, hr⟩
    · rintro ⟨hx, hy, hr⟩
      exact ⟨⟨hx, hy⟩, hr⟩
  exact congrArg (fun s => S.Definable L s) he |>.to_iff

theorem Definable.prod {S : Set M} {A : Set P.Carrier} {B : Set Q.Carrier}
    (hA : P.Definable S A) (hB : Q.Definable S B) :
    (P.prod Q).Definable S (A ×ˢ B) :=
  (P.definable_prod_iff Q S _).mpr
    ((hA.left_relation P Q).inter P Q (hB.right_relation P Q))

end Space

/-- A definable set retains its actual carrier and original parameter base. -/
structure DefSet (P : Space L M) (S : Set M) where
  carrier : Set P.Carrier
  definable : P.Definable S carrier

namespace DefSet

variable {P Q : Space L M} {S : Set M}

instance : CoeSort (DefSet P S) Type := ⟨fun A => A.carrier⟩

def univ (P : Space L M) (S : Set M) : DefSet P S :=
  ⟨Set.univ, P.definable_univ S⟩

def empty (P : Space L M) (S : Set M) : DefSet P S :=
  ⟨∅, P.definable_empty S⟩

def prod (A : DefSet P S) (B : DefSet Q S) : DefSet (P.prod Q) S :=
  ⟨A.carrier ×ˢ B.carrier, A.definable.prod P Q B.definable⟩

end DefSet

/-- A genuine function of subtypes, with its entire graph definable. -/
structure Map {P Q : Space L M} {S : Set M} (A : DefSet P S) (B : DefSet Q S) where
  toFun : A → B
  graph_definable : P.RelationDefinable Q S
    (fun x y => ∃ a : A, a.val = x ∧ (toFun a).val = y)

namespace Map

variable {P Q R : Space L M} {S : Set M}
variable {A : DefSet P S} {B : DefSet Q S} {C : DefSet R S}

instance : CoeFun (Map A B) (fun _ => A → B) := ⟨Map.toFun⟩

def graph (f : Map A B) (x : P.Carrier) (y : Q.Carrier) : Prop :=
  ∃ a : A, a.val = x ∧ (f a).val = y

@[simp] theorem graph_apply (f : Map A B) (a : A) (b : Q.Carrier) :
    f.graph a.val b ↔ (f a).val = b := by
  constructor
  · rintro ⟨a', ha, hf⟩
    have he : a' = a := Subtype.ext ha
    simpa [he] using hf
  · intro h
    exact ⟨a, rfl, h⟩

@[ext] theorem ext {f g : Map A B} (h : ∀ a, f a = g a) : f = g := by
  cases f
  cases g
  congr
  exact funext h

def id (A : DefSet P S) : Map A A where
  toFun := _root_.id
  graph_definable := ((A.definable.left_relation P P).inter P P
    (P.relation_eq_definable S)).congr P P (by
      intro x y
      constructor
      · rintro ⟨hx, rfl⟩
        exact ⟨⟨x, hx⟩, rfl, rfl⟩
      · rintro ⟨a, rfl, rfl⟩
        exact ⟨a.property, rfl⟩)

def comp (g : Map B C) (f : Map A B) : Map A C where
  toFun a := g (f a)
  graph_definable := (f.graph_definable.comp P Q R g.graph_definable).congr P R (by
    intro x z
    constructor
    · rintro ⟨y, ⟨a, rfl, rfl⟩, ⟨b, hb, hg⟩⟩
      have he : b = f a := Subtype.ext hb
      subst b
      exact ⟨a, rfl, hg⟩
    · rintro ⟨a, rfl, hg⟩
      exact ⟨(f a).val, ⟨a, rfl, rfl⟩, ⟨f a, rfl, hg⟩⟩)

@[simp] theorem comp_apply (g : Map B C) (f : Map A B) (a : A) :
    g.comp f a = g (f a) := rfl

@[simp] theorem id_apply (a : A) : Map.id A a = a := rfl

def inclusion {A' : DefSet P S} (h : A'.carrier ⊆ A.carrier) : Map A' A where
  toFun a := ⟨a.val, h a.property⟩
  graph_definable := ((A'.definable.left_relation P P).inter P P
    (P.relation_eq_definable S)).congr P P (by
      intro x y
      constructor
      · rintro ⟨hx, rfl⟩
        exact ⟨⟨x, hx⟩, rfl, rfl⟩
      · rintro ⟨a, rfl, rfl⟩
        exact ⟨a.property, rfl⟩)

theorem definable_image (f : Map A B) :
    Q.Definable S (Set.range (fun a => (f a).val)) := by
  have h := (f.graph_definable.swap P Q).exists_right Q P
  have he : {x : Q.Carrier | ∃ y, ∃ a : A, a.val = y ∧ (f a).val = x} =
      Set.range (fun a : A => (f a).val) := by
    ext y
    simp
  rwa [he] at h

end Map

end SpecialTransformations.DefinableGeometry
