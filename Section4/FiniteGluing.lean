import Section4.FiniteMaps

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language

noncomputable section

namespace SpecialTransformations.DefinableGeometry

variable {L : Language} {M : Type} [L.Structure M]
variable {P Q : Space L M} {S : Set M}

def DefSet.union (A B : DefSet P S) : DefSet P S :=
  ⟨A.carrier ∪ B.carrier, A.definable.union P B.definable⟩

namespace Map

def emptyTo (B : DefSet Q S) : Map (DefSet.empty P S) B where
  toFun a := False.elim a.property
  graph_definable := by
    change S.Definable L _
    convert (Set.definable_empty (A := S) (L := L) (α := P.Index ⊕ Q.Index)) using 1
    ext z
    constructor
    · rintro ⟨_, _, a, _, _⟩
      exact False.elim a.property
    · exact False.elim

variable {A A' : DefSet P S} {B : DefSet Q S}

/-- Choose the first branch on the overlap. The branch test is definable
over the same base, so the complete graph remains definable. -/
def union (f : Map A B) (g : Map A' B) : Map (A.union A') B where
  toFun a := if h : a.val ∈ A.carrier then f ⟨a.val, h⟩
    else g ⟨a.val, a.property.resolve_left h⟩
  graph_definable :=
    (f.graph_definable.union P Q
      ((A.definable.compl P).left_relation P Q |>.inter P Q g.graph_definable)).congr P Q (by
      intro x y
      constructor
      · rintro (⟨a, rfl, hf⟩ | ⟨hna, a, rfl, hg⟩)
        · refine ⟨⟨a.val, Or.inl a.property⟩, rfl, ?_⟩
          simpa [a.property] using hf
        · refine ⟨⟨a.val, Or.inr a.property⟩, rfl, ?_⟩
          have hn : a.val ∉ A.carrier := hna
          simpa [hn] using hg
      · rintro ⟨a, rfl, he⟩
        by_cases h : a.val ∈ A.carrier
        · exact Or.inl ⟨⟨a.val, h⟩, rfl, by simpa [h] using he⟩
        · exact Or.inr ⟨h, ⟨a.val, a.property.resolve_left h⟩, rfl,
            by simpa [h] using he⟩)

theorem FiniteFibres.union {f : Map A B} {g : Map A' B}
    (hf : f.FiniteFibres) (hg : g.FiniteFibres) : (f.union g).FiniteFibres := by
  intro b
  let l : A → A.union A' := fun a => ⟨a.val, Or.inl a.property⟩
  let r : A' → A.union A' := fun a => ⟨a.val, Or.inr a.property⟩
  apply ((hf b).image l |>.union ((hg b).image r)).subset
  intro a ha
  by_cases h : a.val ∈ A.carrier
  · exact Or.inl ⟨⟨a.val, h⟩, by simpa [Map.union, h] using ha, rfl⟩
  · exact Or.inr ⟨⟨a.val, a.property.resolve_left h⟩,
      by simpa [Map.union, h] using ha, rfl⟩

end Map

/-- A definable piece equipped with an actual finite-to-one map to a common
target. This is gluing data, rather than an assumption about dimension. -/
structure FiniteMapPiece (P : Space L M) {Q : Space L M} {S : Set M} (B : DefSet Q S) where
  source : DefSet P S
  map : Map source B
  finite : map.FiniteFibres

namespace FiniteMapPiece

variable {B : DefSet Q S}

def empty : FiniteMapPiece P B :=
  ⟨DefSet.empty P S, Map.emptyTo B, Map.finiteFibres_of_finite _ Set.finite_empty⟩

def union (p q : FiniteMapPiece P B) : FiniteMapPiece P B :=
  ⟨p.source.union q.source, p.map.union q.map, p.finite.union q.finite⟩

def glue : List (FiniteMapPiece P B) → FiniteMapPiece P B
  | [] => empty
  | p :: ps => p.union (glue ps)

@[simp] theorem mem_glue_source (ps : List (FiniteMapPiece P B)) (x : P.Carrier) :
    x ∈ (glue ps).source.carrier ↔ ∃ p ∈ ps, x ∈ p.source.carrier := by
  induction ps with
  | nil => simp [glue, empty, DefSet.empty]
  | cons p ps ih => simp [glue, union, DefSet.union, ih]

end FiniteMapPiece

/-- Finite gluing of finite-to-one maps to a common target. Images of
different branches may overlap; finiteness of fibres is preserved. -/
theorem finite_cover_finite_map {ι : Type} [Fintype ι] (A : DefSet P S) (B : DefSet Q S)
    (D : ι → DefSet P S) (f : ∀ i, Map (D i) B) (hf : ∀ i, (f i).FiniteFibres)
    (hcover : ∀ a : A, ∃ i, a.val ∈ (D i).carrier) :
    ∃ g : Map A B, g.FiniteFibres := by
  let pieces : List (FiniteMapPiece P B) :=
    (Finset.univ : Finset ι).toList.map (fun i => ⟨D i, f i, hf i⟩)
  let p := FiniteMapPiece.glue pieces
  have hsub : A.carrier ⊆ p.source.carrier := by
    intro a ha
    obtain ⟨i, hi⟩ := hcover ⟨a, ha⟩
    apply (FiniteMapPiece.mem_glue_source pieces a).mpr
    refine ⟨⟨D i, f i, hf i⟩, ?_, hi⟩
    exact List.mem_map.mpr ⟨i, by simp, rfl⟩
  let inc : Map A p.source := Map.inclusion hsub
  have hinc : Function.Injective inc := by
    intro a b he
    exact Subtype.ext (congrArg (fun x : p.source => x.val) he)
  exact ⟨p.map.comp inc, p.finite.comp (Map.finiteFibres_of_injective hinc)⟩

end SpecialTransformations.DefinableGeometry

end
