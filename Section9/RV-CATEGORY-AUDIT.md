# Finite-volume scope of Sections 9 and 10

The numbering is from [arXiv:1006.2467v1](https://arxiv.org/pdf/1006.2467v1).
The full subcategory `RV[n]` adds finite fibres of the volume map. It does
not bound the number of auxiliary RV coordinates or require them to match on
the two sides of an isomorphism.

The author approved `RV[n]` as the active scope for Section 9. The ambient
statements below explain which earlier results are available as inputs.

- Definition 9.13 and the paper's RV clause of 9.15 use the ambient
  `RV[n,·]` isomorphism. The active version keeps the same derivative and
  exceptional sets for every definable lift of an essential `RV[n]`
  isomorphism. Both projections of the volume correspondence are finite
  because the volume maps have finite fibres. `PaperLiftComparison.lean`
  proves the comparison using the graph-field construction in
  `GaussGraphConstruction.lean`.
- Theorem 9.16 already assumes finite-to-one volume maps. On a stratum of
  dimension `k < n`, the two head projections may use different coordinate
  subsets. Choose them on a finite definable refinement and keep the original
  label in both projected objects. If a head projection on the volume image
  has finite fibres, composing it with the original volume map has finite
  fibres. The induced head isomorphism belongs to `RV[k]`. A head exception
  of dimension `< k` pulls back to a label exception of dimension `< k` by
  the finite head map, as required by the induction.
- Section 4 already provides `rvLiftFiniteObject` and
  `rvLift_finite_rv_fibres`. Over an input VF tuple `a`, the auxiliary
  labels of its lift are in the volume-map fibre over `rv(a)`. Section 7
  gives the corresponding `gammaLiftVF_finite` in the actual Gamma-base
  presentation. Thus the lifts of essential `RV[n]` objects are in `VF[n]`.
  Degenerate coordinates are handled on the essential restrictions. Their
  omitted VF sets are covered by finitely many coordinate hyperplanes.
- Theorem 10.5 uses 9.16 with the ratio of the two RV volume forms. For the
  Gamma version, use the RV Jacobian on the good RV locus and the product of
  target coordinates divided by the product of source coordinates elsewhere.
  Both choices have the required Gamma value. Applying 9.16 and taking
  valuations gives the forward lift used by Corollary 10.6. The separate
  Gamma descent lemma is needed when deducing Gamma preservation on RV from
  a volume-preserving VF lift.

The real-parameter presentation of `RV[n]` is `RVFiniteObject`. Same-base
head selection and the tail centre construction preserve the original real
parameters of the `(VF, Γ)`-generated base of 9.16. The generated-base
hypothesis supplies algebraic VF representatives. Auxiliary parameters used
in the compactness argument are absent from the resulting choice graph.

## The affine correction in Theorem 9.16

The proof in the paper first normalizes both RV images into residue-field
units. For a single fibre this can be done with named VF representatives.
For a definable family with varying radii, it would require a uniform
argument over the original base. A definable choice of a VF scale for
each of infinitely many RV radii is ruled out by Corollary 3.5.

The construction can keep the original radii. On a nondegenerate stratum
with `k < n` head coordinates, choose the two finite head projections and
lift the induced head isomorphism using Section 7. The implicit derivative
of the chosen lift gives the value of the head determinant `D` on the good head
locus. For a fixed VF head input, the labels sharing that head RV tuple
form a finite family. Include both source and target tail balls and the
ball representing the prescribed `ω` in the finite family used for
Lemma 3.13. Its base is the original generated base enlarged by the VF
head. The centre choices must be made uniformly over that family by a
same-base definability argument. Let `aᵢ,bᵢ` be source and target centres
and `c` a representative of `ω(u)` in the chosen coordinate order.

Use `zᵢ ↦ bᵢ + λᵢ(zᵢ − aᵢ)` on each tail coordinate. Put
`λᵢ = bᵢ/aᵢ` for all but the last coordinate `j`, and set
`λⱼ = c/(D · ∏ᵢ≠ⱼ λᵢ)`. Condition (2) of 9.16 and the head comparison
give `v(λⱼ) = v(bⱼ) − v(aⱼ)`, so the last affine map sends precisely the
source RV ball onto the target ball. The block-triangular determinant
is `D · ∏ᵢ λᵢ = c`. Any source and target coordinate permutations require
their determinant signs in `c`. On the VF-small bad head locus use the
default slopes so that the lift remains a bijection. The cylinder above
the bad head locus is VF-small in the full fibre. At `k=0`, use the empty
head determinant `1` and the finite-family centre construction directly.

The head construction only needs the Gamma value of the head determinant.
The weighted polynomial lift provides this value on the VF-generic locus
over each head pair. Once that lift is checked, the tail construction need
not discard RV head labels or recurse on their RV dimension. The generic
residue comparison is still needed on the full RV-dimensional part, where
there is no tail coordinate. The same-base centre selection proceeds by
finite gluing of definable choices after fixing the VF head. The auxiliary
Gamma representatives used for compactness are absent from the resulting
choice graph.
