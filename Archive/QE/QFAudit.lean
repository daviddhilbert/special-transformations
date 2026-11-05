/-
# Audit: the ledger's input 5 *is* Proposition 3.9's conclusion at the pair

`M5Ledger.paper_theorem_2_3_sat_of_ledger_paperHyp` derives `M7Paper.Prop39Sat` from `PrepStepP`
(= the five inputs) plus the frozen one-step.  The five inputs are meant to be weaker than the
conclusion.  This file machine-checks that **input 5 is not**: extending a monomorphism along every
inclusion `S ≤ T` of substructures and extending it to a monomorphism defined on all of `M` are the
same property (`T = ⊤` on one side, restriction on the other).  So at any pair

    M5Ledger.SaturationRealization (M := M) (N := N)
      ↔  ∀ (S) (f), ∃ g : M ↪[LRV] N, ∀ x : S, g ↑x = f x      ("Prop39Pair")

and, gated at `PaperHyp`, `LedgerInput5P ↔` (the conclusion of `M7Paper.Prop39Sat`).

Consequences for the §10b ledger, which this file records rather than assumes:

* inputs 3 and 4 are the only ones that carry construction content; input 5 already contains the
  paper's Proposition 3.9 at the pair, so the ledger's *conclusion* is not new information given
  input 5 (`prop39Pair_of_satReal`);
* the equivalence is what makes this member's reduction `input 5 ↔ qf-type realisation`
  (`M2Saturation.satReal_iff_qfsat`) an identification of the ledger's strongest input with the
  paper's one-element type-realisation problem, i.e. with Lemmas 3.2–3.8;
* it also explains why input 1 is redundant (`M2Residue.ledgerInput1P_of_ledgerInput5P`): input 5 is
  already strong enough to embed all of `M` into `N` over `f`, which is more than enough to get the
  residue-field map.
-/
import SatReal
import KOfBridge

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
open SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations
namespace Milestone0
namespace M2Audit

variable {M N : Type} [LRV.Structure M] [LRV.Structure N]

/-- "Proposition 3.9's conclusion at the pair": every monomorphism out of a substructure extends to a
monomorphism defined on all of `M`.  (This is `M7Paper.Prop39Sat`'s body without the `PaperHyp`
gate, and it is `Assembly.prop39P_noVFGen`'s conclusion.) -/
def Prop39Pair (M N : Type) [LRV.Structure M] [LRV.Structure N] : Prop :=
  ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N), ∃ g : M ↪[LRV] N, ∀ x : S, g (x : M) = f x

/-- The total-extension property gives the ledger's input 5 (restrict the total embedding to `T`). -/
theorem satReal_of_prop39Pair (h : Prop39Pair M N) :
    M5Ledger.SaturationRealization (M := M) (N := N) := by
  intro S T f hST
  obtain ⟨g, hg⟩ := h S f
  refine ⟨g.comp (Substructure.subtype T), ?_⟩
  intro x
  exact hg x

/-- The ledger's input 5 gives the total-extension property (take `T = ⊤`): this is the direction that
makes input 5 as strong as the conclusion at the pair. -/
theorem prop39Pair_of_satReal (h : M5Ledger.SaturationRealization (M := M) (N := N)) :
    Prop39Pair M N := by
  intro S f
  obtain ⟨g, hg⟩ := h S ⊤ f le_top
  refine ⟨g.comp (Substructure.topEquiv (L := LRV) (M := M)).symm.toEmbedding, ?_⟩
  intro x
  have h1 : (g.comp (Substructure.topEquiv (L := LRV) (M := M)).symm.toEmbedding) x
      = g ⟨(x : M), trivial⟩ := rfl
  rw [h1]
  exact hg x

/-- **Input 5 = Proposition 3.9's conclusion at the pair.** -/
theorem prop39Pair_iff_satReal :
    Prop39Pair M N ↔ M5Ledger.SaturationRealization (M := M) (N := N) :=
  ⟨satReal_of_prop39Pair, prop39Pair_of_satReal⟩

section PaperHyp

variable [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]

/-- **Gated at `PaperHyp`: `LedgerInput5P` is the conclusion of `M7Paper.Prop39Sat`.**  So the §10b
ledger's hypothesis list contains the conclusion of the theorem it proves, at the same pairs; the
non-trivial content is in inputs 2, 3, 4. -/
theorem ledgerInput5P_iff_prop39SatBody :
    M5Ledger.LedgerInput5P ↔
      ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
        M7Paper.PaperHyp M N → Prop39Pair M N := by
  constructor
  · intro h5 M N _ _ _ _ hP
    exact prop39Pair_of_satReal (h5 M N hP)
  · intro h39 M N _ _ _ _ hP
    exact satReal_of_prop39Pair (h39 M N hP)

/-- **The §10b ledger collapses to input 5.**  `M7Paper.ShoenfieldTestSat` consumes Proposition 3.9
at `PaperHyp` pairs, and `LedgerInput5P` *is* that (previous theorem), so inputs 1, 2, 3, 4 and the
frozen one-step play no role in the final derivation:

    ShoenfieldTestSat → LedgerInput5P → HasQE Axioms.ACVF

Compare `M5Ledger.paper_theorem_2_3_sat_of_ledger_paperHyp`, which routes the same conclusion through
all five inputs and the one-step.  Recorded, not assumed: the ledger's `PrepStepP` machinery is a way
of *proving* input 5 (via inputs 3/4), not an independent reduction of the target once input 5 is
granted. -/
theorem hasQE_of_ledgerInput5P (hShoen : M7Paper.ShoenfieldTestSat)
    (h5 : M5Ledger.LedgerInput5P) : HasQE Axioms.ACVF :=
  hShoen (fun M N _ _ _ _ hP S f => prop39Pair_of_satReal (h5 M N hP) S f)

end PaperHyp

end M2Audit
end Milestone0
end SpecialTransformations

#print axioms SpecialTransformations.Milestone0.M2Audit.satReal_of_prop39Pair
#print axioms SpecialTransformations.Milestone0.M2Audit.prop39Pair_of_satReal
#print axioms SpecialTransformations.Milestone0.M2Audit.prop39Pair_iff_satReal
#print axioms SpecialTransformations.Milestone0.M2Audit.ledgerInput5P_iff_prop39SatBody
#print axioms SpecialTransformations.Milestone0.M2Audit.hasQE_of_ledgerInput5P
