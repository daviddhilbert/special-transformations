# Agreed scope of Definition 2.4

On November 5, 2026, the author authorized **rational VF functions with
explicit domain guards** in the VF factors of the normal form in Definition
2.4. This supersedes the strict polynomial-only target for those factors.

The released language continues to name RV inversion and to leave VF
inversion unnamed. A rational VF factor is interpreted through numerator and
denominator polynomials; its pole conditions must be explicit. Residue sums
also retain the conditions that their summands belong to the residue subset,
including its absorbing zero. Clearing a denominator does not by itself
justify distributing a nonunit RV scalar through residue addition.

This records the author's chosen formalization scope. It does not assert a
Lean-proved counterexample to the printed polynomial-only formulation.
The revised theorem is now proved in [GuardedRationalNormalForm.lean](GuardedRationalNormalForm.lean).


The theorem constructs a finite disjunction of finite conjunctions in the
original language, over exactly the original VF and RV slots, uniformly
in every ACVF model. Both equality K factors are flat sums with at least
two summands; the left outer RV coefficient is one. Order comparisons
have no K factors. RV integer exponent words use the already named RV
inverse and retain zero branches. VF ring terms have proved multivariate
polynomial semantics. Every raw-true clause establishes every nonzero VF
denominator and every residue-summand domain. The DefinableOver wrapper
reuses the same finite parameter package. No characteristic, saturation
or assumed normalization premise is needed.

The four public modules passed pinned Lean compilation. The combined
certificate covers 197 modules, 1393 headline type/axiom checks, and a fresh
project-root import. Only propext, Classical.choice and Quot.sound occur; see the
[verification record](verification/LibraryAudit.json).
