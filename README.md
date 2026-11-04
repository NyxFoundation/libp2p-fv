# libp2p-fv

## Abstract

Ethereum consensus clients rely on GossipSub to disseminate time-critical consensus
objects, but the security of this communication path depends on more than the
broadcast protocol alone. Correct peer authentication, stream negotiation,
message framing, Snappy block decompression, SSZ decoding, and application
validation must compose
without allowing invalid data, identity confusion, or unbounded resource use.
Existing ACL2s research formalizes GossipSub and exposes scoring vulnerabilities;
subsequent work proves a refinement relationship between Floodsub and an abstract
broadcast specification. These results motivate a complementary, cross-layer
investigation rather than a claim to the first formal verification of libp2p.

This project aims to specify and verify the Ethereum GossipSub communication path
over QUIC, from TLS 1.3 certificate-to-Peer-ID binding through stream negotiation
and GossipSub routing to the topic- and fork-specific checks that gate gossip
acceptance, including required object signatures and proofs but not full block or
execution validation. The intended
contribution is an explicit set of layer contracts and composition obligations
connecting authenticated transport to validated message delivery, together with
assumption-sensitive resource and dissemination properties. We begin by
cataloguing these obligations before selecting verification tools. Safety,
liveness, and probabilistic security claims will be separated, with protocol
versions, configurations, attacker capabilities, and implementation boundaries
made explicit. The initial scope excludes Req/Resp, discovery internals, TCP
fallback, full block validation, fork choice, and the execution layer. This is a
research proposal: no end-to-end theorem, verified implementation, or unconditional
availability guarantee is claimed.

## Research artifact

[**Property inventory**](inventory.md) defines the scope, assumptions, per-layer
properties, end-to-end obligations, and adversarial scenarios. Every property is
currently **proposed**, not proved or model-checked. The intended contribution is
a research direction, not an established novelty or priority claim.
[Resource obligations](inventory.md#59-resource-bounds-and-cleanup) cover message
and decompression sizes, connections/streams, memberships, caches, queues, and
validation work. Their concrete bounds belong to the result-specific profile.

## Prior work

- Kumar et al., [*Verification of GossipSub in ACL2s*](https://arxiv.org/abs/2311.08859)
  (ACL2 2023), and [*Formal Model-Driven Analysis of Resilience of GossipSub to
  Attacks from Misbehaving Peers*](https://arxiv.org/abs/2212.05197)
  (IEEE S&P 2024): executable GossipSub models, scoring properties, and attack
  synthesis. [Public artifacts](https://github.com/gossipsubfm/gossipsubfm).
- Kumar and Manolios, [*A Formalization of the Correctness of the Floodsub
  Protocol*](https://arxiv.org/abs/2507.19013) (ACL2 2025): mechanized simulation
  refinement of Floodsub to Broadcastsub, not a QUIC-to-Ethereum stack proof.
  [Public artifacts](https://github.com/ankitku/FloodsubRef).
- Crochet et al., [*Verifying QUIC implementations using Ivy*](https://arxiv.org/abs/2503.01374)
  (Workshop on Evolution, Performance and Interoperability of QUIC, 2021;
  [DOI](https://doi.org/10.1145/3488660.3493803)): QUIC draft-29 modeling and
  model-derived client/server tests against seven implementations, not a proof of
  the current Ethereum GossipSub path. [Artifacts](https://github.com/AnonyQUIC/QUIC-Ivy).
