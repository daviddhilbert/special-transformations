# Current handoff

The formalization is closed out for the agreed scope of Sections 2–10; see
[README.md](README.md) and the [blueprint](blueprint/README.md). The items recorded
in the provider audit of November 18, 2026 now stand as follows (release
v1.2, [release record](docs/RELEASE-v1.2.md)):

- Input-free Theorems 5.4/5.5 with named Gamma parameters are in
  `Section5/GammaPaper.lean` (both base conventions, author-approved
  November 18, 2026). The v1.2 blueprint links them, together with the
  Gamma lift layer through Gamma Theorem 9.16.
- The trivial-valuation case of Theorem 2.8 is out of scope (author
  confirmation, November 18, 2026).
- Downstream, integration-in-ACVF's Gamma-named Section 7 uses the
  additive Gamma lift layer (`Section9/Gamma*.lean`) without `hNames`.

The earlier per-section handoffs (for example `Section3/HANDOFF.md`) are
historical records of the proof campaign.
