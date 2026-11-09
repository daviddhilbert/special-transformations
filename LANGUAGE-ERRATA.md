# RV language and theory errata

## Named RV inversion

Author clarification, November 5, 2026 (America/Los_Angeles).

In *Special transformations in algebraically closed valued fields*, the
paragraph immediately before Convention 2.5 explicitly omits multiplicative
inverse symbols from both the VF and RV sorts. For the intended quantifier
elimination statement, the RV language must instead include a unary
multiplicative inverse function. This is a correction to the paper's language
specification, as confirmed by the author.

The corrected formalization names RV inversion and totalizes it at the
absorbing element by `0⁻¹ = 0`. It does not add a VF inverse symbol. The existing
Lean definitions and proofs already use this corrected RV language; this
clarification changes their documentation, not their implementation.

Requiring the nonzero RV elements to form a group is distinct from naming
inversion as a function in the first-order signature. Naming it ensures that
language substructures are closed under RV inversion. The group axiom alone
does not impose that closure on substructures in the inverse-free signature.

Accordingly, the formalized Theorem 2.3 proves QE for the **corrected language
with named RV inversion**. It is not a claim of QE for the literal inverse-free
signature printed in the paper. Pure ACF QE and ordinary valued-field QE keep
their existing language specifications.

## Scope for later sections

The correction concerns the QE formulation; it does not require changing the
later mathematics of definable sets. On the RV sort the totalized inverse
already has the definable graph

```text
y = x⁻¹  iff  (x = 0 and y = 0) or (x ≠ 0 and x * y = 1).
```

Existence and uniqueness follow from the RV group axioms. Naming this
definable function is a definitional expansion on the intended sorts: it does
not change the definable sets, or definable and algebraic closure, over the
same parameters. Occurrences of the inverse function can be replaced by its
graph, possibly introducing quantifiers. This is why definability of inverse
suffices for the later sections even though the literal QE formulation needs
the named symbol.

Subsequent work with definable sets may therefore use the inverse-free
signature or the named-inverse presentation interchangeably at the level of
definability. No new downstream hypothesis or change to a definable-set
statement is called for. Literal term-generated substructures must still be
distinguished from definable closure.

Earlier documentation saying that this omission occurred only in the Lean
transcription, or that adding RV inversion was not a correction to the paper,
was mistaken. This author clarification supersedes that attribution, including
older documentation at the pinned ACVF-QE revision.

Paper: [arXiv:1006.2467v1](https://arxiv.org/pdf/1006.2467v1), Section 2,
paragraph immediately preceding Convention 2.5.

## Kernel of the RV map in Definition 2.2

Author clarification, November 7, 2026 (America/Los_Angeles).

Clause (6) should state that the kernel of the surjective homomorphism
`rv : VFˣ → RVˣ` is `1 + 𝔪`, where `𝔪` is the maximal ideal of
the valuation ring. Equivalently, for nonzero `a` and `b`,
`rv(a) = rv(b)` exactly when `a / b ∈ 1 + 𝔪`. The first
isomorphism theorem recovers the quotient and quotient map used in
the introduction. [Paper introduction](https://arxiv.org/html/1006.2467v1#S1)
[Definition 2.2](https://arxiv.org/html/1006.2467v1#S2)

Surjectivity and the valuation property alone allow a larger kernel.
In pure characteristic zero, on the usual RV group replace the map
by `x ↦ rv(x)²` for nonzero `x`, retaining the same image of zero.
Divisibility gives surjectivity and the induced additive valuation is
doubled, with the same valuation ring and maximal ideal. The new
kernel contains `−1`, which lies outside `1 + 𝔪`.

The released Lean theory already imposes the leading-term equality
in `Axioms.rvEqLink`. Its instance with the second argument equal
to `1` is the kernel condition. The separate residue-operation
clauses require the map from the valuation ring to the residue field
to preserve addition and negation, with elements of the maximal
ideal sent to residue zero. These clauses are already present in
the released theory. [Released RV linkage axioms](https://github.com/daviddhilbert/ACVF-QE/blob/f3ef4ee679f921079aa8f742a2807a9cc724d2d6/Proofs/Enc.lean#L1448)

## Trivial valuations and QE

The author confirmed that the intended QE statement has separate
trivially valued and nontrivially valued cases. The nontrivial RV
theorem is `theorem_2_3_quantifier_elimination`. In the trivial case
with the intended quotient and residue operations, RV is the field in
a second copy and QE reduces to ACF. The QE dependency proves
`TrivialRV.canonical_trivial_rv_qe` for these canonical structures in every
characteristic and `TrivialRV.hasQE` for their common sentence theory.
[Released theory](https://github.com/daviddhilbert/ACVF-QE/blob/f3ef4ee679f921079aa8f742a2807a9cc724d2d6/Proofs/Enc.lean#L1478)

The two statements are separate. Uniform QE for their union would fail in the current language.
For example, extend the `t`-adic valuation of `ℚ̄((t))` to an algebraic
closure. The constant field `ℚ̄` has trivial valuation and its canonical
two-sorted structure embeds into the ambient canonical structure.
The sentence asserting that a nonzero element lies in the maximal ideal
distinguishes them. QE would make this embedding elementary.
