module

public import Section6.PreparedDescent
public import Section6.RVFormula

@[expose] public section

/-!
Syntactic assembly from the actual prepared maps. The auxiliary formula
is interpreted on the substructure's RV carrier; its quantifiers are
never evaluated in the ACVF envelope. A graph formula must describe the
complete contraction graph, including its domain. Graph construction and
uniformity across ambient models are separate from this assembly theorem.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5

namespace SpecialTransformations.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S X : Set M} {n m l k : ℕ}

abbrev SubRV (X : Set M) := {t : RV (M := M) // t.val ∈ X}

def keyTuple (u : Key (M := M) n l) : Fin (n + l) → RV (M := M) :=
  Fin.append u.1 u.2

theorem keyTuple_mem {u : Key (M := M) n l} (hu : KeyIn X u) :
    ∀ i, (keyTuple u i).val ∈ X := by
  intro i
  cases i using Fin.addCases with
  | left i => simpa only [keyTuple, Fin.append_left] using hu.1 i
  | right j => simpa only [keyTuple, Fin.append_right] using hu.2 j

theorem keyIn_of_tuple {u : Key (M := M) n l} {y : Fin (n + l) → SubRV X}
    (hy : keyTuple u = fun i => (y i).val) : KeyIn X u := by
  constructor
  · intro i
    have he := congrFun hy (Fin.castAdd l i)
    simp only [keyTuple, Fin.append_left] at he
    rw [congrArg Subtype.val he]
    exact (y (Fin.castAdd l i)).property
  · intro j
    have he := congrFun hy (Fin.natAdd n j)
    simp only [keyTuple, Fin.append_right] at he
    rw [congrArg Subtype.val he]
    exact (y (Fin.natAdd n j)).property

variable {L : Language} [L.Structure (SubRV X)] {β : Type}
variable {A : DefSet (M := M) S n m} {B : DefSet (M := M) S n l}
variable {D : DefSet (M := M) S 0 k}

/-- Exact full graph semantics. In particular a key outside keyImage B
does not satisfy the graph, even if k=0. The additional RV structure is
arbitrary, and every free RV assignment is retained. -/
def ContractionGraphFormula (f : Map A D) (T : SpecialBijection A B)
    (graph : L.Formula (Fin (n + l) ⊕ Fin k ⊕ β)) : Prop :=
  ∀ (y : Fin (n + l) → SubRV X) (z : Fin k → SubRV X) (b : β → SubRV X),
    graph.Realize (Sum.elim y (Sum.elim z b)) ↔
      ∃ u : keyImage B, keyTuple u.val = (fun i => (y i).val) ∧
        (contractionFun (Map.comp f T.inverseMap) u).val.2 = fun i => (z i).val

/-- A genuine auxiliary-language output formula, with all binders ranging
over RV(X). The only syntactic input beyond the body is a complete graph
formula. The maps, their restriction and key realization are proved in
PreparedDescent; none is replaced by a semantic elimination assumption. -/
theorem prepared_formula_elimination
    (hX : NormalizedDclClosed X) (hSX : S ⊆ X)
    (hrv : ∀ a : VF (M := M), a.val ∈ X → (rv a).val ∈ X)
    (hRV : ∀ t : RV (M := M), t.val ∈ X →
      ∃ a : VF (M := M), a.val ∈ X ∧ rv a = t)
    (T : SpecialBijection A B) (hB : IsRVPullback (carrier B))
    (f : Map A D) (hf : Contractible (Map.comp f T.inverseMap))
    (graph : L.Formula (Fin (n + l) ⊕ Fin k ⊕ β))
    (hgraph : ContractionGraphFormula (X := X) f T graph)
    (body : L.Formula (Fin k ⊕ β)) (b : β → SubRV X) :
    (∃ a : A, PointIn X a.val ∧
      ∃ z : Fin k → SubRV X, (f a).val.2 = (fun i => (z i).val) ∧
        body.Realize (Sum.elim z b)) ↔
      (RVFormula.assemble graph body).Realize b := by
  let P : (Fin k → RV (M := M)) → Prop := fun w =>
    ∃ z : Fin k → SubRV X, w = (fun i => (z i).val) ∧ body.Realize (Sum.elim z b)
  have hd := prepared_exists_descends hX hSX hrv hRV T hB f hf P
  rw [RVFormula.assemble_realize]
  change (∃ a : A, PointIn X a.val ∧ P (f a).val.2) ↔ _
  rw [hd]
  constructor
  · rintro ⟨u, hu, _, z, hz, hb⟩
    let y : Fin (n + l) → SubRV X :=
      fun i => ⟨keyTuple u.val i, keyTuple_mem hu i⟩
    exact ⟨z, y, (hgraph y z b).mpr ⟨u, rfl, hz⟩, hb⟩
  · rintro ⟨z, y, hg, hb⟩
    obtain ⟨u, hy, hz⟩ := (hgraph y z b).mp hg
    refine ⟨u, keyIn_of_tuple hy, ?_, z, hz, hb⟩
    constructor
    · intro i
      exact i.elim0
    · intro i
      have he := congrFun hz i
      rw [congrArg Subtype.val he]
      exact (z i).property

end SpecialTransformations.Section6
