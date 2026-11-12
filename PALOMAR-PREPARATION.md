# Palomar preparation

Author and responsible maintainer: Yimu Yin.

This isolated candidate starts from released source
f76d100e07c0a791259244fc7fdf06f4dfaaf8ae. It does not incorporate unrelated
uncommitted work from the author's original checkout. Existing releases remain
unchanged.

The initial module migration follows Lean 4.35.0's documented recipe:
module headers, public imports, and exposed public definitions. Existing proof
expressions are retained. Source scanners now recognize public imports.
ACVF-QE is pinned to its corresponding module migration at
1d7396d7e23c34dc23d19214e510e63e1ec1fe03; the old proof release is not compatible
with importing those sources as Lean modules.

Fresh compilation and headline audits remain required. No Palomar submission
has been sent. Independent Challenge/Solution packaging is still outstanding.
The proposed central targets and all their explicit reference hypotheses must
be reviewed independently of this mechanical source migration.
