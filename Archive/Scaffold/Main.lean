import SpecialTransformations.VolumeForms

/-!
# Main statements

Reference: Yin, Sections 5, 7, 10.

This file is the target list for the formalization.  Each item records the
paper's numbering and the current formal status.

| Paper item | Informal statement | Lean status |
|---|---|---|
| Theorem 2.3 | ACVF admits quantifier elimination | **proved locally with no additional mathematical hypotheses**, in `QE/LocalQE/Theorem23.lean`, for the author-confirmed language with RV inversion; all 86 modules and a fresh combined audit passed; see `QE/LocalQE/STATUS.txt` |
| Theorem 2.8 | ACVF is C-minimal | **stated** (`Milestone0/Encoding.lean`, frozen with `sorry`); the C-relation and one auxiliary `sorry` are in `Milestone0/Balls.lean` |
| Theorem 5.4/5.5 | special bijections to RV-pullbacks | not started |
| Corollary 5.6 | every definable set is a deformed RV-pullback | not started |
| Corollary 5.7 | `L` is surjective on isomorphism classes | not started |
| Theorem 7.6 | lifts of isomorphic RV-objects are isomorphic | not started |
| Corollary 7.7 | `L` induces a surjective homomorphism of Grothendieck semigroups | not started |
| Theorem 9.16 | lifts with prescribed RV-Jacobian | not started |
| Theorem 10.4 | every `(A, ω)` is isomorphic to a lift | not started |
| Theorem 10.5 | measure-preserving lifts exist | not started |
| Corollary 10.6 | `L` induces surjective homomorphisms of volume-form Grothendieck semigroups | not started |
-/
namespace SpecialTransformations

-- TODO: replace this file with faithful Lean statements once the language,
-- definable sets, and categories are in place.

end SpecialTransformations
