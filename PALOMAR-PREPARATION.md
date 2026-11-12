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
8f90dfd22de9f2c821382830eee326d1f0cf4990; the old proof release is not compatible
with importing those sources as Lean modules.

Fresh compilation and headline audits remain required. No Palomar submission
has been sent. Independent Challenge/Solution packaging is still outstanding.
The proposed central targets and all their explicit reference hypotheses must
be reviewed independently of this mechanical source migration.

The migration exposes helpers needed by exported definition bodies and adds
the exact Mathlib imports identified by the compiler. It does not supply new
mathematical hypotheses or replace the completed arguments.

For independent statement packaging, the existing released language remains
the common source. A November 12 pathname survey of Tau Ceti at
5b875ab7c67d980ab0da982df4faa8db09a877b4 found general model-theory and
henselization developments, but no directly identified replacement for this
VF/RV statement interface. This was a discovery survey, not a compatibility or
proof audit; no new Tau Ceti dependency was added. Existing attributed ports and
their licenses/provenance remain in place. Reuse the existing checked results
rather than restarting their proof campaigns.

Further compiler-directed preparation exposes helpers used by public
declarations. The ordinary nontriviality formula uses an explicit finite index
in both statement and library to avoid elaboration-dependent auxiliary proofs.
Fresh checks are pending for these changes.

A conservative lexical dependency survey identified further private helpers
used in exposed definitions or public declaration types, including transitive
helper dependencies. Their visibility was promoted without changing bodies,
hypotheses or theorem statements. This is a preparation aid, not compiler
evidence; the complete pinned build and headline checks remain required.

The next compiler pass found the short helper 	erm in the affine-head
formula interface. Its visibility is now public as well. The dependency
is updated to the mechanically passing ACVF-QE snapshot above; integration
requires fresh compilation against this exact pin.

The next full build reached the final Section 10 modules. Four additional
helper declarations used by exposed measured-category constructions are
now public; their statements and proof bodies are unchanged.

Full library compilation and all headline audits passed at f2fbe2e in
GitHub Actions run 43274534495. The optional dependency inventory failed
on the obsolete `liftIO` name and now uses the generic `liftM`. Its log
and generated source are retained. A GitHub-only compiled cache is keyed
by production Lean sources, toolchain, manifest and Lake configuration;
cache reuse is not a new source-compilation receipt. The independent
statement modules are excluded from that production cache key and are
compiled separately. Palomar full preflight discards submitted build state
and remains mandatory for the exact final package.

The corrected compiled inventory succeeded at c5d190d (run 43280416384):
667 custom declarations in the statement dependency closure. Source ranges
are now recorded to support extraction of exact declaration boundaries,
including anonymous instances and generated declarations. Inventory data
are navigation evidence and do not replace independent compilation or
Comparator checks.
