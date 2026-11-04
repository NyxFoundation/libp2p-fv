# libp2p-fv

## Abstract

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
remain in scope. This is a research proposal, not a verified implementation or a
completed end-to-end theorem; intended novelty requires further literature review.

## Research artifact

[**Property inventory**](inventory.md) indexes the safety-only scope, assumptions,
parent contracts, atomic obligations, exclusions, and four layer-specific documents.
All obligations are **proposed**, not proved or model-checked.

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
