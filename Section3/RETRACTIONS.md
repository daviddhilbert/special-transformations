# Retraction of Remark 3.19

On November 5, 2026, the author retracted Remark 3.19 of
*Special transformations in algebraically closed valued fields*,
[arXiv:1006.2467v1, printed page 7](https://arxiv.org/html/1006.2467v1#S3.Thmthm19).
The whole remark is withdrawn, including its proposed multiplicative
extension of Lemma 3.18. No replacement classification is asserted.

The printed classification fails for the parameter-free definable
multiplicative subgroup {1,-1}. The checked Lean module
[Remark319Audit.lean](Remark319Audit.lean) proves that its VF point set
is neither a ball nor the full valuation-unit group in ACVF(0,0).
Its compiler, headline types and permitted-axiom audit are retained in the
library verification record. The suggested addition of an infinitude
hypothesis was not adopted as a replacement statement.

The author made the retraction conditional on the remark not being used later.
The dependency check found no later citation or identified reliance on the
remark: the complete arXiv v1 HTML has just one visible occurrence of its
number, at the remark itself, no links to its anchor `S3.Thmthm19`, and no other
occurrence of the phrase “multiplicative subgroup.” A search of Sections 4–10
found no reference to its legacy label `fun:quo:rep:mult`, its legacy
`FunQuoRepMult` declarations, or `Remark319Audit`. No later section imports
`Sec3Tail` or `Sec3TailGamma`. These checks establish the citation and formal
import status; they do not claim that every later proof has been formalized.

Lemma 3.18 and its additive conclusions remain active targets. Historical
snapshots are preserved as history and are not evidence for the withdrawn
remark. Retraction is distinct from a proof: Remark 3.19 is excluded from the
remaining formalization obligations, not counted as a proved result.
