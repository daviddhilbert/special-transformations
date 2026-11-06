# Section 6 module organization

The Denef-Pas continuation is consolidated into four coherent source
modules. Public namespaces and mathematical statements are retained. The
56 developed helper/proof bodies and the historical Library audit body are copied verbatim, with their original file
scopes closed explicitly; imports are collected at the module boundary.
This avoids repeating the pinned legacy dependency initialization for every
small helper file. It changes no dependency revision or earlier theorem.

| Module | Scope |
| --- | --- |
| DenefPasAlgebra | Actual RV pair codes, zero cases, equality and multiplication, inversion, residue operations, the DP signature and auxiliary syntax |
| DenefPasInterpretation | Trivial-valuation ac field equivalence, native model and sorting adapters, uniform forward/return dictionaries, polynomial and original-parameter codes, nontrivial henselian elimination |
| DenefPasTrivialBranch | Uniform trivial-valuation elimination branch |
| DenefPasConclusion | One formula for both valuation branches, arbitrary original free names, proper sort normalization and Corollary 6.5 |

The syntactic Lemma 6.3 and named-base Proposition 6.4 remain in their
existing modules. The active dependency closure has 78 modules including Library. All passed
the final pinned verification, including 444 headline audits and the combined
import. The 56 former helper paths are import-only compatibility files.

The exact fragment-to-module map, body offsets and SHA-256 identities are
in `.scratch/section6-bundle-map.json`. The previous assembled-source
certificate remains immutable under `.scratch/section6-assembled444/`.
The consolidated modules passed fresh source checks, the full headline
type/axiom audit and the affected import boundary. The final integrated
certificate is `.scratch/section6-final78-444/`.
