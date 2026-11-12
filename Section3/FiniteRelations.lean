module

public import Section3.RawAlgebraicity

@[expose] public section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
namespace SpecialTransformations.Section3.RawClosure
variable {M : Type} [LRV.Structure M]

def GoodRelation (S : Set M) := {R : Set (M × M) //
  S.Definable₂ LRV R ∧ ∀ a : M, {x | (a, x) ∈ R}.Finite}

theorem good_relation_of_algebraic (S : Set M) (a b : M)
    (hb : AlgebraicOver (insert a S) b) : ∃ R : GoodRelation S, (a, b) ∈ R.val := by
  classical
  obtain ⟨R, hR, hab, hfin⟩ := promote_parameter S a b hb
  let k := ({x | (a, x) ∈ R} : Set M).ncard
  let Q : Set (M × M) := {p | p ∈ R ∧ p.1 ∉ HasMore R k}
  have hnot := (hasMore_definable S R hR k).compl
  have hQ : S.Definable₂ LRV Q := by
    have hp := hnot.preimage_comp (fun _ : Fin 1 => (0 : Fin 2))
    change S.Definable LRV {x : Fin 2 → M | (x 0, x 1) ∈ R ∧ x 0 ∉ HasMore R k}
    exact hR.inter hp
  have ha : a ∉ HasMore R k :=
    (no_inj_iff_finite_ncard_le).mpr ⟨hfin, le_rfl⟩
  refine ⟨⟨Q, hQ, ?_⟩, hab, ha⟩
  intro c
  by_cases hc : c ∈ HasMore R k
  · have hempty : {x | (c, x) ∈ Q} = ∅ := by ext x; simp [Q, hc]
    rw [hempty]; exact Set.finite_empty
  · have hf := (no_inj_iff_finite_ncard_le (s := {x | (c, x) ∈ R}) (k := k)).mp hc
    exact hf.1.subset
      (by intro x hx; exact hx.1)

theorem slice_definable (S : Set M) (b : M) (R : GoodRelation S) :
    (insert b S).Definable₁ LRV {a | (a, b) ∈ R.val} := by
  have hR : (insert b S).Definable₂ LRV R.val := R.property.1.mono (Set.subset_insert b S)
  let F (x : Fin 1 → M) : Fin 2 → M := ![x 0, b]
  have hF : (insert b S).DefinableMap LRV F := by
    intro i
    fin_cases i
    · exact Set.DefinableFun.proj LRV
    · exact LRV.definableFun_const (Fin 1) (Set.mem_insert b S)
  exact hR.preimage_map hF

end SpecialTransformations.Section3.RawClosure