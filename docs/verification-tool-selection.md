---
title: Verification Tool Selection
last_updated: 2026-11-05
tags:
  - formal-verification
  - libp2p
  - tooling
---
# Verification Tool Selection

## Decision and scope

Use **Quint** for executable state-machine specifications, **TLC** and
**Apalache** for model checking, **Lean 4** for deductive proofs and contract
composition, and **Tamarin** for symbolic security protocol analysis. Examine
existing **ACL2s** GossipSub artifacts as prior work, not as evidence that this
inventory has been verified.

The selection covers the libp2p-related obligations in the
[property inventory](../inventory.md), not all of libp2p/specs. It excludes
Ethereum-specific rules, Snappy/SSZ, Ethereum validation, and verification of a
particular implementation. QUIC/TLS RFCs and multistream-select are external
specifications needed by the inventoried libp2p path; their treatment below is
conditional and does not expand this into a complete proof of those protocols.
The inventory's immutable source snapshots are the starting point, not a claim
about the current master branch. Fix a profile and source commits before reporting
any verification result.

## Responsibilities

| Tool | Selected role | Evidence and limits |
| --- | --- | --- |
| [Quint](https://quint.sh/) | Describe executable state machines and properties; simulate representative traces. | Simulation samples executions and is not exhaustive proof. Quint is a specification language; its model checkers are separate tools. |
| [TLC](https://docs.tlapl.us/using:tlc:start) | Explore finite Quint models via Quint's [TLC backend](https://quint.sh/docs/model-checkers), especially interleavings and failure transitions. | Exhaustive only over the configured finite reachable state space of the translated model when exploration completes. Translation correctness, unbounded state, state-space explosion or incomplete exploration limits the result. |
| [Apalache](https://apalache-mc.org/) | Use Quint's [Apalache backend](https://quint.sh/docs/model-checkers) to symbolically check bounded traces or candidate inductive invariants where supported. | A bounded check covers only its stated bound. An inductiveness result depends on its initiation and preservation checks, model, assumptions, and supported encoding; it is not automatically a proof of a different model. |
| [Lean 4](https://lean-lang.org/doc/reference/latest/) | Prove selected general invariants, data and arithmetic properties, and composition theorems from explicit contracts. | A theorem establishes only its formal statement and assumptions. It does not automatically establish correspondence with a Quint or Tamarin model. |
| [Tamarin](https://tamarin-prover.com/manual/master/book/001_introduction.html) | Analyze symbolic authentication, identity binding, and replay across adversarial sessions. | Results depend on the symbolic model and crypto equations; proof search may not terminate. Symbolic security is not a computational security bound or a proof of certificate parsing. |
| [ACL2s GossipSub artifacts](https://github.com/gossipsubfm/gossipsubfm) | Compare and assess reuse of existing executable models and scoring analyses. | Check the exact versions, assumptions, properties, and artifacts before citing or adapting a result. Prior work does not discharge an inventory obligation by itself. |

## Mapping to the inventory

The mappings below select a primary approach, not a claim that all children in a
family are applicable or already formalized. Preserve each child's S, D, or K
classification and its normative strength. Restrict mixed families to their
libp2p-relevant children and explicitly record omitted or unresolved dependencies.

| Inventory area | Approach |
| --- | --- |
| Q-01–Q-06, transport and authentication boundary | State applicable QUIC/TLS guarantees as external contracts unless independently established, citing the exact RFC clauses, assumptions, and any abstraction used. Use Tamarin for selected symbolic authentication and replay questions; use Quint for admission, session and stream interactions, and Lean for contracts and composition. Q-01's computational confidentiality/integrity bounds are not proved by symbolic analysis. |
| A-01–A-05, certificate and Peer ID binding | Use Lean for certificate-check, encoding, and identity-derivation contracts; use Tamarin for the modeled signature/identity/session correspondence. Treat parser correctness and crypto primitives as explicit assumptions unless separately established. |
| N-01–N-05, stream negotiation | Use Quint and model checking for negotiation, handoff, failure and session isolation; Lean can prove general framing and contract properties. N-03.01 is Ethereum-specific and excluded; do not import exact matching as a generic libp2p rule. |
| F-01–F-05, libp2p-relevant framing and envelopes | Use Lean for selected encoding, decoding, boundary and message-identity properties; use Quint where sequencing or ownership matters. The inventory identifies an unresolved outer framing contract: do not invent it or claim it is proved. Ethereum-specific constraints are excluded. |
| G-01–G-07 and M-01, M-03–M-06, M-08, GossipSub | Use Quint/TLC to explore validation, duplicate handling, control and scoring transitions; use Apalache where appropriate and Lean for selected general invariants. Compare ACL2s prior work before deciding whether a result or model can be adapted. Application validation is an explicit interface, not Ethereum validation. |
| R-03–R-04, cancellation and ownership | Use Quint to explore stale completions and session ownership; prove selected abstract invariants in Lean. Buffer ownership in a model is not evidence of memory safety in an implementation. |
| E-01–E-03, E-06, E-07 | Define a **new libp2p-scoped** composition statement in Lean; do not reuse Ethereum-dependent E2E statements unchanged. Record excluded dependencies, evidence class and assumptions. Implementation correspondence in E-07.02 is out of scope, not established. |

The [excluded inventory families](../inventory.md#excluded-families), including
M-02, M-07, E-04 and E-05, remain excluded. In particular, this selection does
not claim delivery, liveness, DoS resistance, global resource bounds, or full
implementation correctness.

## Cross-tool evidence boundary

Quint, TLC, Apalache, Lean, and Tamarin do not share a theorem automatically.
Record the model-checker backend and translation assumptions. Define the peer,
session, stream, message and event identities and the abstraction or refinement
relations needed between models. Show that each imported result's assumptions
and event meanings discharge the receiving contract; otherwise list the relevant
contract as an unverified assumption. A finite TLC result, bounded Apalache check,
symbolic Tamarin result, inherited result, and Lean theorem must remain distinct
in reports. Do not convert one into another by naming the same property.

Separate symbolic security from computational claims, and record algorithm,
key-compromise, adversary, replay and trust assumptions. Record exact source and
model revisions, profile, tool versions, configurations, bounds, proof artifacts,
and any failed or incomplete checks. Satisfying a derived design obligation is
not evidence that it is a normative libp2p requirement.

## Initial sequence

1. Select immutable specification revisions, GossipSub versions and options,
   authentication and replay policy, and concrete message/state semantics. Resolve
   applicable inventory ambiguities before presenting an obligation as checked.
2. Compare the ACL2s GossipSub artifacts with the selected profile. Build a small
   Quint state machine for authentication, negotiation, validation and stale
   callbacks; exercise scenarios and explore finite instances with TLC.
3. Formulate the libp2p-scoped composition and its interface contracts in Lean;
   prove selected general invariants, recording remaining assumptions. Apply
   Apalache to suitable checks without conflating bounded and inductive results.
4. Model the selected identity-binding and replay questions in Tamarin. Define
   and justify cross-model correspondences before using those results in a Lean
   composition claim.

All of these are proposed activities. No model checking, proof, or cross-tool
correspondence is claimed by this document.
