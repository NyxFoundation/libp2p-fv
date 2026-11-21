# libp2p-fv

Veil/Lean reference safety models for a libp2p GossipSub v1.3 receiver.
**This is not a completed verification of the entire libp2p inventory.**
The models have explicit authentication, parser, validation, timer and score
interfaces; they are not verified production implementations.

## Run the verification

Prerequisites: [Elan](https://github.com/leanprover/elan), Python 3.10+,
Git, and the [Veil system dependencies](https://github.com/verse-lab/veil/tree/578ec0b77a0936cb502e15bdb468047211abd6b9#build)
(Clang/LLD and libc++ development libraries on Linux).
The checked-in toolchain selects Lean 4.35.0. First use downloads and builds
the pinned dependencies; network access is required.

```sh
python3 scripts/verify.py
```

The command builds the project, reruns finite model checks and certification,
tests policy boundaries, audits every project theorem's axioms, and runs
negative controls that remove validation, live-session and deduplication guards.
It also checks that the audit rejects an added axiom, `sorry`, and a
`native_decide` compiler oracle.
Logs go to ignored `verification-output/`. A command failure, missing
certificate, or nonstandard proof axiom fails the gate. GitHub Actions uploads
these logs as `veil-verification-logs`, including when verification fails.

```sh
python3 scripts/check_coverage.py
python3 scripts/check_coverage.py --require-complete
```

The second command intentionally fails while unmodeled or test-only obligations
remain. Passing that bookkeeping check would still require reviewing the
model-to-specification mappings. A successful artifact verification is **not**
a claim that all 160 inventory obligations are discharged.

## Artifacts

| Path | Purpose |
| --- | --- |
| `Libp2p/Pipeline.lean` | Session/stream authentication gates, per-task verdict ownership, cancellation, delivery/forwarding and scoped deduplication |
| `Libp2p/Routing.lean` | Abstract membership, explicit peers, local/remote forwarding and PX gates |
| `Libp2p/Cache.lean` | Cache identity, IHAVE/IWANT and tracked-promise attribution |
| `Libp2p/Policies.lean` | Check conjunctions, encoding-boundary lemmas and exact-integer reference policy functions |
| `Libp2p/PipelineSafety.lean` | Unbounded reachability proof over Pipeline's generated transition system |
| `Libp2p/Proof.lean` | Typed bridge from Veil WP proofs to its relational semantics; used by Pipeline's reachability proof |
| `Tests/` | Axiom audit, policy boundary tests and coverage-ledger checks |
| [Profile](docs/veil-profile.md) | Fixed source, feature choices, ownership and external contracts |
| [Coverage ledger](verification/coverage.json) | All 160 child IDs, model projections, assumptions, omissions and exclusions |
| [Tool decision](docs/verification-tool-selection.md) | Veil adoption and evidence-class distinctions |

## Research context

Ethereum consensus clients rely on GossipSub to disseminate consensus objects,
but safe reception depends on the composition of transport authentication,
stream negotiation, framing, decompression, decoding, and application validation.
Existing ACL2s research formalizes GossipSub and exposes scoring vulnerabilities;
subsequent work proves Floodsub refinement to an abstract broadcast model. These
results motivate a complementary cross-layer investigation, not a claim to the
first formal verification of libp2p.

This project aims to specify the safety of Ethereum GossipSub over QUIC, from
TLS 1.3 certificate-to-Peer-ID binding through Snappy/SSZ processing to the checks
that gate gossip acceptance. Its intended contribution is a hierarchy of
independently checkable obligations connecting authenticated transport to validated
message delivery. Each obligation records premises, event, conclusion,
specification clause, and dependencies before verification tools are selected.
Normative requirements are distinguished from additional design contracts and
conditional cryptographic claims. Availability, dissemination guarantees, DoS
resistance, global memory/CPU bounds, Req/Resp, discovery internals, TCP fallback,
full block validation, fork choice, and execution validity are excluded. Local
input-bound checks, required object signatures/proofs, and stale-session safety
remain in the research scope. The Veil artifacts cover a narrower libp2p
reference profile, not this entire Ethereum path or a production implementation.
Intended novelty requires further literature review.

## Research artifact

[**Property inventory**](inventory.md) indexes the safety-only scope, assumptions,
parent contracts, atomic obligations, exclusions, and four layer-specific documents.
The inventory's original obligations are not collectively discharged. The
coverage ledger distinguishes model-level evidence from external contracts,
unmodeled requirements, tested policies and exclusions. In particular, the
libp2p-scoped Pipeline theorem is not the original Ethereum E2E theorem.

## Prior work

- Kumar et al., [*Verification of GossipSub in ACL2s*](https://arxiv.org/abs/2311.08859)
  (ACL2 2023), and [*Formal Model-Driven Analysis of Resilience of GossipSub to
  Attacks from Misbehaving Peers*](https://arxiv.org/abs/2212.05197)
  (IEEE S&P 2024): executable GossipSub models, scoring properties, and attack
  synthesis. [Artifacts](https://github.com/gossipsubfm/gossipsubfm).
- Kumar and Manolios, [*A Formalization of the Correctness of the Floodsub
  Protocol*](https://arxiv.org/abs/2507.19013) (ACL2 2025): mechanized simulation
  refinement to Broadcastsub, not a QUIC-to-Ethereum stack proof.
  [Artifacts](https://github.com/ankitku/FloodsubRef).
- Crochet et al., [*Verifying QUIC implementations using Ivy*](https://arxiv.org/abs/2503.01374)
  (Workshop on Evolution, Performance and Interoperability of QUIC, 2021;
  [DOI](https://doi.org/10.1145/3488660.3493803)): draft-29 modeling and
  model-derived client/server tests against seven implementations, not a proof of
  the Ethereum GossipSub path. The arXiv deposit is from 2025, the workshop paper
  from 2021. [Artifacts](https://github.com/AnonyQUIC/QUIC-Ivy).
