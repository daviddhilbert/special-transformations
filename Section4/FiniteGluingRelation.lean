module

public import Section4.FiniteGluing

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language

noncomputable section

namespace SpecialTransformations.DefinableGeometry

variable {L : Language} {M : Type} [L.Structure M]
variable {P Q : Space L M} {S : Set M} {B : DefSet Q S}
variable {R : P.Carrier → Q.Carrier → Prop}

namespace FiniteMapPiece

def Respects (p : FiniteMapPiece P B) (R : P.Carrier → Q.Carrier → Prop) : Prop :=
  ∀ a : p.source, R a.val (p.map a).val

theorem Respects.union {p q : FiniteMapPiece P B} (hp : p.Respects R) (hq : q.Respects R) :
    (p.union q).Respects R := by
  intro a
  by_cases ha : a.val ∈ p.source.carrier
  · simpa only [FiniteMapPiece.union, Map.union, dif_pos ha] using hp ⟨a.val, ha⟩
  · simpa only [FiniteMapPiece.union, Map.union, dif_neg ha] using
      hq ⟨a.val, a.property.resolve_left ha⟩

theorem glue_respects (ps : List (FiniteMapPiece P B))
    (h : ∀ p ∈ ps, p.Respects R) : (glue ps).Respects R := by
  induction ps with
  | nil =>
    intro a
    exact False.elim a.property
  | cons p ps ih =>
    exact (h p (List.mem_cons_self)).union (ih (fun q hq => h q (List.mem_cons_of_mem p hq)))

end FiniteMapPiece

/-- Finite definable gluing retains a pointwise relation satisfied by
every branch, in addition to definability and finite fibres. -/
theorem finite_cover_finite_map_respecting {ι : Type} [Fintype ι]
    (A : DefSet P S) (B : DefSet Q S) (D : ι → DefSet P S)
    (f : ∀ i, Map (D i) B) (hf : ∀ i, (f i).FiniteFibres)
    (hR : ∀ i, ∀ a : D i, R a.val (f i a).val)
    (hcover : ∀ a : A, ∃ i, a.val ∈ (D i).carrier) :
    ∃ g : Map A B, g.FiniteFibres ∧ ∀ a : A, R a.val (g a).val := by
  let pieces : List (FiniteMapPiece P B) :=
    (Finset.univ : Finset ι).toList.map (fun i => ⟨D i, f i, hf i⟩)
  let p := FiniteMapPiece.glue pieces
  have hsub : A.carrier ⊆ p.source.carrier := by
    intro a ha
    obtain ⟨i, hi⟩ := hcover ⟨a, ha⟩
    apply (FiniteMapPiece.mem_glue_source pieces a).mpr
    exact ⟨⟨D i, f i, hf i⟩, List.mem_map.mpr ⟨i, by simp, rfl⟩, hi⟩
  let inc : Map A p.source := Map.inclusion hsub
  have hinc : Function.Injective inc := by
    intro a b he
    exact Subtype.ext (congrArg (fun x : p.source => x.val) he)
  have hp : p.Respects R := by
    apply FiniteMapPiece.glue_respects
    intro q hq
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hq
    exact hR i
  exact ⟨p.map.comp inc, p.finite.comp (Map.finiteFibres_of_injective hinc),
    fun a => hp (inc a)⟩

end SpecialTransformations.DefinableGeometry

end
