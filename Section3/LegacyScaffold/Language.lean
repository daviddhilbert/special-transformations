module

public import Mathlib

@[expose] public section

/-!
# The language `L_RV` and the theory `ACVF_S(0, 0)`

Reference: Yin, Section 2, Definitions 2.1, 2.2, 2.4.

The paper uses a two-sorted language:

* `VF` — the valued field, with the language of rings;
* `RV` — the RV sort, with a multiplicative group structure, constants `0`, `∞`,
  a predicate for `Kˣ`, addition on `K = Kˣ ∪ {0}`, negation, and a preorder;
* a function `rv : VF → RV`.

Mathlib's first-order model theory is one-sorted, so this file will either:

1. use the many-sorted framework from
   <https://github.com/Mathias-Stout/Many-sorted-model-theory> (Apache-2.0), or
2. encode the sorts as a single sort with predicates and use the one-sorted
   language of Mathlib.

Decision pending; see `HANDOFF.md`.
-/
namespace SpecialTransformations

-- TODO: `inductive LRVSort | VF | RV`
-- TODO: `def LRV : FirstOrder.Language ...`
-- TODO: `def ACVF : LRV.Theory`
-- TODO: `def ACVF_S (S : Substructure ...) : LRV.Theory`

end SpecialTransformations
