# Pointwise differentiation in Lemmas 9.11 and 9.12

The numbering follows [arXiv:1006.2467v1, pp. 24–25](https://arxiv.org/pdf/1006.2467v1#page=24).
The author approved these replacements on November 7, 2026. The Lean
headlines are `lemma_9_11_ae` in `SpecialJacobianAE.lean` and
`lemma_9_12_ae` in `MixedDifferentiationAE.lean`. See [STATUS.md](STATUS.md)
for their verification records.

## Approved replacement statements

Use the paper's standing pure-characteristic-zero setting and its
Definition 9.10 of the partial Jacobian. For a definable map between
mixed VF/RV sets, a local VF chart at `(a,t)` consists of an open
polydisc about `a` with input RV label fixed at `t`, contained in the
domain fibre, on which the output RV label is fixed at its value at
`(a,t)`. The VF map in that chart is the VF projection of the original
map. Differentiability below means the full linear approximation of
Definition 9.6 on such a polydisc. Write the exceptional-set bounds for
`n > 0`. In arity zero the identities hold everywhere, with the empty
determinant equal to one.

**Lemma 9.11.** Let `T : A → A♯` be a definable special bijection
between mixed sets of VF arity `n`. There exist definable subsets
`E ⊆ A` and `E♯ ⊆ A♯` of VF dimension `< n` such that `JcbVF T = 1`
on `A \ E` and `JcbVF T⁻¹ = 1` on `A♯ \ E♯`, with the Jacobians
defined on the indicated loci. There are no additional hypotheses for
this almost-everywhere assertion.

A pointwise sufficient condition is available. Fix a decomposition of
`T` into the elementary steps in Definition 5.1. At the successive
points of the decomposition, suppose each elementary step and its
inverse admit local VF charts on a fixed branch. For each active
centripetal step, suppose its focus with the RV labels fixed is defined
on an open neighbourhood of the complementary VF coordinates and is
fully differentiable at those coordinates. Then `JcbVF T(a,t) = 1` and
`JcbVF T⁻¹(T(a,t)) = 1`. Indeed the active step is a shear
`(x,z) ↦ (x − λ(z),z)` and its inverse uses `+ λ(z)`. The matrices
are triangular with unit diagonal. Canonical steps have identity VF
maps in these charts. The charts can be shrunk along the composition
by continuity.

**Lemma 9.12.** Let `f : A → B` and `g : B → C` be definable maps
between mixed sets of the same VF arity `n`. Let `p ∈ A` and `q = f(p)`.
Suppose `f` at `p` and `g` at `q` admit local VF charts and their VF
maps are fully differentiable at the corresponding points. Then all
three Jacobians are defined and

```
JcbVF (g ∘ f)(p) = JcbVF g(f(p)) · JcbVF f(p).
```

No bijectivity or nonsingular determinant is required pointwise. The
first chart can be shrunk to map into the second, since full
differentiability implies VF continuity and its output RV label is
fixed. Lemma 9.7 gives the composition derivative, whose determinant
equals the determinant of the partial derivative matrix.

**Almost-everywhere consequence.** If `f` is finite-to-one, there is a
definable `E ⊆ A` of VF dimension `< n` outside which the three
Jacobians are defined and the identity holds. Once generic full
differentiability in the fixed-label charts is proved, take the union of
the bad locus of `f` and the inverse image under `f` of the bad locus of
`g`. The restriction of `f` to that inverse image has finite fibres, so
the VF dimension of the inverse image is at most that of the bad locus
of `g`. This includes the composition of definable bijections used for
Section 10.

## Lemma 9.12 with the partial Jacobian of Definition 9.10

Let `f(x,y) = (x,x+y)`. Let `g(x,y) = (2x,2y)` when `x=y`, and let `g`
fix the complement of the diagonal. Both are definable bijections of
`VF²` in characteristic zero. Their four partial derivatives at the
origin are obtained by restricting to the two coordinate axes. The two
Jacobian matrices and the matrix for the composition are respectively

```
  [1 0]    [1 0]    [2 0]
  [1 1],   [0 1],   [2 1].
```

The first input axis maps to the diagonal under `f`, so `g` doubles the
first column of the derivative of the composition. All three partial
Jacobian determinants are defined, with values `1`, `1`, and `2`.
The pointwise statement of 9.12 thus fails for Definition 9.10.

## The everywhere clause of Lemma 9.11

Let `m` be the maximal ideal. On the nondegenerate pullback
`(1+m) × (1+m)` with constant RV tags, choose a nonzero `e ∈ m` as a
parameter. Use the focus `λ(y)=1+e` for `y=1` and `λ(y)=1` elsewhere.
Both centres lie in the correct RV ball. The single centripetal step
from [Definition 5.1](https://arxiv.org/pdf/1006.2467v1#page=13) is
`(x,y) ↦ (x−λ(y),y)`.

Choose `d` with `0 < v(d) < v(e)` and put `x=1+d`. At `y=1` the first
output is `d−e`, while at every sufficiently close distinct `y` it is
`d`. These two outputs have the same RV class. The calculation therefore
also works with the output RV label fixed and after adjoining canonical
tags. Along this axis the first difference quotient is `e/(y−1)` and
has no finite limit. Thus the Jacobian of Definition 9.10 can be undefined
at a point of a nondegenerate pullback.

For the almost-everywhere proof, generic VF interior and local
constancy of output RV labels give the charts for each elementary
step. On an active branch, the bad locus of the focus in its
complementary VF variables has dimension below `n − 1` when `n > 1`.
Allowing the translated coordinate adds at most one to the dimension.
When `n = 1`, the focus has no varying VF coordinate after the RV
labels have been fixed. Pull the exceptional sets for the finitely many
elementary steps back along the preceding definable bijections. The
same argument for the inverses gives the claimed bound on `A♯`.
