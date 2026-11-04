/-
# d6 — the reduction of the frozen Lemma 3.3 obligation to monomorphism extension

Companion of `D6_Hull.lean` (which proves `Standing (standingHull S)`, its minimality, and that every
substructure of a model of `ACVF` lies in a `Standing` one).  Here:

* `HullExtension` — every monomorphism `S ↪ N` extends to the *fixed* substructure `standingHull S`;
* `prepStepP_iff_hullExtension` — `Assembly.PrepStepP` at a pair is **equivalent** to
  `HullExtension` at that pair (`←` is the hull being `Standing`; `→` uses minimality);
* `PrepStepSize_iff_hullExtension`, `paper_theorem_2_3_sat_of_hullExtension` — the same at the
  size-bounded pairs of the live route, wired into `M7Paper.paper_theorem_2_3_sat`;
* `hullExtension_forces_unitsN_size` — the cardinality stress test: the reduction keeps the size
  obstruction exactly where `M6L33` locates it.

Verification (from the repository root `$R`), exit 0 / 0 errors / no `sorry`, axioms clean:

    cd $R/.ultramath/smw2ioy2w/m8
    LEAN_PATH=$R/.scratch2/sec3:$LEAN_PATH lean -o D6_Hull.olean D6_Hull.lean
    LEAN_PATH=$PWD:$R/.scratch2/sec3:$LEAN_PATH lean D6_route.lean
-/
import StandingHull
import Lemma33

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
open SpecialTransformations.Milestone0.LRV

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace SpecialTransformations
namespace Milestone0
namespace M8Hull

variable {M N : Type}

/-! ## 4. The reduction of the frozen Lemma 3.3 obligation -/

section Reduction

variable [LRV.Structure M] [LRV.Structure N] [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]

/-- **The monomorphism-extension obligation at the hull**: every monomorphism out of `S` extends to
the fixed substructure `standingHull S`.  This is Lemma 3.3 with the *substructure* part of the
construction deleted (`exists_standing_superset`, `standing_standingHull` prove it), leaving only the
extension of the map. -/
def HullExtension : Prop :=
  ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N),
    ∃ g : standingHull S ↪[LRV] N,
      ∀ x : S, g ⟨(x : M), le_standingHull S x.2⟩ = f x

/-- `HullExtension` gives the frozen `PrepStepP` — the hull is `Standing` and contains `S`. -/
theorem prepStepP_of_hullExtension (h : HullExtension (M := M) (N := N)) :
    Assembly.PrepStepP (M := M) (N := N) := by
  intro S f
  obtain ⟨g, hg⟩ := h S f
  exact ⟨standingHull S, g, le_standingHull S, hg, standing_standingHull S⟩

/-- **Conversely**, `PrepStepP` gives `HullExtension`: its witness `T` is `Standing` and contains
`S`, hence contains the hull (`standingHull_le`), and the extension restricts. -/
theorem hullExtension_of_prepStepP (h : Assembly.PrepStepP (M := M) (N := N)) :
    HullExtension (M := M) (N := N) := by
  intro S f
  obtain ⟨T, g, hST, hagree, hStand⟩ := h S f
  have hle : standingHull S ≤ T := standingHull_le hST hStand
  refine ⟨g.comp (Substructure.inclusion hle), ?_⟩
  intro x
  have h1 : (Substructure.inclusion hle) ⟨(x : M), le_standingHull S x.2⟩
      = ⟨(x : M), hST x.2⟩ := rfl
  show g ((Substructure.inclusion hle) ⟨(x : M), le_standingHull S x.2⟩) = f x
  rw [h1]
  exact hagree x

/-- **The frozen Lemma 3.3 obligation is exactly the monomorphism extension to the hull.** -/
theorem prepStepP_iff_hullExtension :
    Assembly.PrepStepP (M := M) (N := N) ↔ HullExtension (M := M) (N := N) :=
  ⟨hullExtension_of_prepStepP, prepStepP_of_hullExtension⟩

/-- The size-carrying form used by the route (`M7Paper.PrepStepSize`): the size hypothesis stays. -/
theorem PrepStepSize_iff_hullExtension :
    M7Paper.PrepStepSize ↔
      ∀ (P Q : Type) [LRV.Structure P] [LRV.Structure Q] [P ⊨ Axioms.ACVF] [Q ⊨ Axioms.ACVF],
        M7Paper.SizeHyp P Q → HullExtension (M := P) (N := Q) := by
  constructor
  · intro h P Q _ _ _ _ hSize
    exact hullExtension_of_prepStepP (h P Q hSize)
  · intro h P Q _ _ _ _ hSize
    exact prepStepP_of_hullExtension (h P Q hSize)

/-- **Theorem 2.3** with Lemma 3.3 replaced by "monomorphisms extend to the `Standing` hull at
size-bounded pairs": the only remaining inputs are the classical criterion (`ShoenfieldTestSat`,
Marker) and Lemmas 3.4–3.8 (`OneStepSizeFree`). -/
theorem paper_theorem_2_3_sat_of_hullExtension
    (hShoen : M7Paper.ShoenfieldTestSat)
    (hHull : ∀ (P Q : Type) [LRV.Structure P] [LRV.Structure Q] [P ⊨ Axioms.ACVF] [Q ⊨ Axioms.ACVF],
      M7Paper.SizeHyp P Q → HullExtension (M := P) (N := Q))
    (hOne : M7Paper.OneStepSizeFree) : HasQE Axioms.ACVF :=
  M7Paper.paper_theorem_2_3_sat hShoen (PrepStepSize_iff_hullExtension.mpr hHull) hOne

/-- **The cardinality stress test.**  `HullExtension` is not a way around the size obstruction: the
hull contains all units of `M` (`KEqTop`), so an extension of a monomorphism out of the hull embeds
`Kˣ(M)` into `N`, exactly as `M6L33.prepStepP_forces_unitsN_size` records for `PrepStepP`. -/
theorem hullExtension_forces_unitsN_size (h : HullExtension (M := M) (N := N))
    (S : LRV.Substructure M) (f : S ↪[LRV] N) : M6L33.ResidueSizeHyp M N :=
  M6L33.prepStepP_forces_unitsN_size (prepStepP_of_hullExtension h) S f

end Reduction

end M8Hull
end Milestone0
end SpecialTransformations

#print axioms SpecialTransformations.Milestone0.M8Hull.prepStepP_of_hullExtension
#print axioms SpecialTransformations.Milestone0.M8Hull.hullExtension_of_prepStepP
#print axioms SpecialTransformations.Milestone0.M8Hull.prepStepP_iff_hullExtension
#print axioms SpecialTransformations.Milestone0.M8Hull.PrepStepSize_iff_hullExtension
#print axioms SpecialTransformations.Milestone0.M8Hull.paper_theorem_2_3_sat_of_hullExtension
#print axioms SpecialTransformations.Milestone0.M8Hull.hullExtension_forces_unitsN_size
