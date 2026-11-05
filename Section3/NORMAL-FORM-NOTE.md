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
Lean-proved counterexample to the printed polynomial-only formulation, and
it does not certify the revised normal-form theorem. The normal-form proof
remains an open obligation, tracked in [STATUS.md](STATUS.md).
