# Prepare a Lean project for publication

Start from the requested target and existing authorization. Preparing a release
does not by itself authorize changing visibility or publishing private material.
If publication is already authorized, complete the checks and proceed within that
scope without inventing another approval gate.

## Define what ships

Record the source revision, included modules, public documentation, verification
scripts, dependencies, licenses and unfinished results. For private-to-public
exports, use an allowlist and inspect a trial tree. Preserve attribution and
copyright notices. Exclude credentials, private paths, internal records and
unpublished material outside the release scope. Fresh history is an option only
when requested; establish how future updates will be synchronized.

## Verify the public tree

- Preserve statements and definition meaning across renames and moves.
- Check advertised results for proof holes and extra axioms; disclose accepted
  trust assumptions and incomplete results.
- Remove unintended private path dependencies and hidden build inputs.
- Test documented builds and shipped checks in a fresh checkout with pinned
  dependencies. Cache initialization is distinct from a project-only benchmark.
- Document setup, build commands, source correspondence, gaps, licenses and citations.

## Destination-specific requirements

For a registry, archive or comparator challenge, read its current requirements.
Apply its module, size, metadata and challenge/solution rules to the submitted
surface. Do not add comparator CI to releases that do not need it. Distinguish a
challenge's deliberate proof hole from its solution; verify the exact statement
under the allowed dependency and trust boundary.

Use CI appropriate to shipped checks. Read failing logs rather than assuming a
resource limit or statement mismatch. Provision resources for the actual runner
and workload; do not blindly delete SDKs or assume historical free-space figures.
Verify the exact release revision.

For `lake comparator` on GitHub-hosted Ubuntu 24.04, the upstream procedure
requires `bubblewrap` and a user-namespace configuration that permits its sandbox.
Check the actual runner first. On an authorized disposable CI runner, the upstream
setup is:

```yaml
- name: Install the comparator sandbox
  run: |
    sudo apt-get update -qq >/dev/null
    sudo apt-get install -y -qq bubblewrap >/dev/null
    sudo sysctl -w kernel.apparmor_restrict_unprivileged_userns=0
```

This is comparator-specific CI configuration, not a default change to a user's
workstation or shared host. Prefer a runner policy that permits the sandbox
without changing unrelated host protections when available.

## Reader-facing evidence

For a release formalizing published sources, prepare `docs/ERRATA-AND-DEVIATIONS.md`
and a linked README summary with counts per source. Follow the bundled
[errata procedure](../orchestration/references/errata-and-deviations.md), including
independent checks against the pinned source. Keep this record through code-comment
scrubbing; distinguish source defects from repairs to the formalization itself.

README Lean blocks quoting statements must be complete and verbatim. Do not cut
at the first `:=`: a binder may contain `let x := ...` or `by have := ...`.
Use a proof-region marker or the actual declaration-body boundary, then verify
the quoted statement against its source file after the final rename or rewrite.

Check README math on GitHub itself. Use `\lt` and `\gt` where raw angle brackets
would be treated as HTML, and escape literal dollar signs outside code. The
upstream GitHub rendering guidance uses `\mathrm{Im}` or
`\mathop{\mathrm{Res}}` instead of `\operatorname`, `\DeclareMathOperator`,
`\newcommand` or `\def`; scan shipped Markdown for these macros and inspect the
rendered result rather than trusting a local renderer.

Deliver the public tree, validation evidence and limitations. Use independent
review when required by the release process; do not call a self-review independent.
Publish only authorized content and destinations, preserving the agreed history.
