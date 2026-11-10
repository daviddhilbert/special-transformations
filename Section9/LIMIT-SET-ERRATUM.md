# Definition 9.1 limit-set correction

This corrects the covering clause of Definition 9.1 on page 22 of
[arXiv:1006.2467v1](https://arxiv.org/pdf/1006.2467v1#page=22).
For every $\epsilon\in\Gamma$ there is a $\delta\in\Gamma$ such that for
every $c\in\mathfrak o(a,\delta)\cap(A\setminus\{a\})$,

$$
f(c)\subseteq\bigcup_{b\in L}\mathfrak o(b,\epsilon).
$$

A cover indexed by $L'\subseteq L$ is contained in the cover indexed by
$L$. Conversely, the full cover gives the original condition with
$L'=L$. The same $\delta$ works in each direction. Minimality still
means that $L$ is a limit set and every proper subset fails to be one.

The clause is local, as clarified in the author's diamond-integral note
R038. If $L$ is finite and all its coordinates are affine, fix any
$\epsilon$. The ultrametric inequality and the finitely many centers
give one bound for the union of these polydiscs. The corresponding
$\delta$ thus gives boundedness on a punctured neighborhood. An
infinity-coordinate neighborhood is the complement of a bounded ball
in that coordinate, so the same argument yields no bound for a
limit set with points at infinity. Separate boundedness hypotheses
used in existence arguments retain their scope.

[Limits.lean](Limits.lean) already quantifies over the output radius,
chooses the input radius, and tests the punctured domain. For each
output tuple it chooses a center in the full set $L$, with membership
in the same center's polydisc in all coordinates.
`IsMinimalLimitSet` uses proper subsets, and `IsLimitSet` takes no
global range bound. The bounded-chart root estimate in
[LimitRootBound.lean](LimitRootBound.lean) keeps its integral-output
hypothesis. [Lemma 9.5](LimitDefinability.lean) retains definability and
finite fibers and permits extended limit points.

## Verification

The arXiv LaTeX source copy in `.scratch/definition-9-1/paper.tex`
changes only the covering clause. The local Lean 4.35.0 checks of
the covering equivalence, strict-subset minimality and the finite
affine cover bound passed. Their full types and axiom reports are in
`.scratch/definition-9-1/Verification.log`.

[GitHub Actions run #27](https://github.com/daviddhilbert/special-transformations/actions/runs/42807782183)
rebuilt the project with Lean 4.35.0. The Section 9 audit prints the
same limit-set and minimality predicates as the preceding run.
Lemmas 9.2–9.5 passed their type and axiom audits.
