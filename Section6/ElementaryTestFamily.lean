import Mathlib.ModelTheory.ElementaryMaps
import Mathlib.ModelTheory.Bundled

/-! The precise generic model-theoretic test-family bridge. An elementary
cover contains an actual elementary copy of a test model through every
tuple under consideration. For finite tuples, the intended standard
source is downward Löwenheim–Skolem plus a sufficiently large universal
ACVF envelope over the named base (Marker, Model Theory: An Introduction,
the elementary-submodel and saturated-model embedding theorems), together
with the accepted earlier algebraic-envelope result. This definition makes
no saturation or elimination claim. Its construction is an explicit input
when used; it cannot be discharged by assuming a Section 6 conclusion.
-/

open FirstOrder FirstOrder.Language

namespace SpecialTransformations.Section6

variable {L : _root_.FirstOrder.Language.{0, 0}} {α I : Type}

def ElementaryCover (T : L.Theory) (N : I → Type)
    (sN : ∀ i, L.Structure (N i)) : Prop :=
  ∀ (M : T.ModelType.{0, 0, 0}) (v : α → M),
    ∃ i, ∃ j : @ElementaryEmbedding L (N i) M (sN i) inferInstance,
      ∃ u : α → N i, j ∘ u = v

/-- A formula chosen before the test model is also uniform over all
models covered by actual elementary maps. -/
theorem equivalent_of_elementary_cover (T : L.Theory) (N : I → Type)
    (sN : ∀ i, L.Structure (N i)) (hcover : ElementaryCover (α := α) T N sN)
    (φ ψ : L.Formula α)
    (hfamily : ∀ i, ∀ v : α → N i,
      @Formula.Realize L (N i) (sN i) α φ v ↔
        @Formula.Realize L (N i) (sN i) α ψ v) :
    ∀ (M : T.ModelType.{0, 0, 0}) (v : α → M), φ.Realize v ↔ ψ.Realize v := by
  intro M v
  obtain ⟨i, j, u, rfl⟩ := hcover M v
  letI := sN i
  exact (j.map_formula φ u).trans ((hfamily i u).trans (j.map_formula ψ u).symm)

end SpecialTransformations.Section6
