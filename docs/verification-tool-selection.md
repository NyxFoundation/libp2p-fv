---
title: Verification Tool Selection
last_updated: 2026-11-22
tags:
  - formal-verification
  - libp2p
  - tooling
  - veil
---
# Verification Tool Selection

## Decision

This branch uses **Veil**, embedded in Lean, instead of the former
Quint/TLC/Apalache/Lean/Tamarin plan. There is no second protocol model to keep
in sync. Veil extracts executable transitions and verification conditions from
the same action definitions.

The dependency is pinned to Veil commit
`578ec0b77a0936cb502e15bdb468047211abd6b9`, with Lean 4.35.0 and transitive
revisions in `lake-manifest.json`. This revision includes upstream SMT
reconstruction fixes after the v4.35.0 release. It may build from source instead
of using that release's prebuilt artifacts.

## Evidence classes

| Artifact | What it establishes |
| --- | --- |
| `#model_check interpreted` | Exploration of the particular finite instance and theory recorded in the source. It does not enumerate all theories or establish an unbounded theorem. |
| `sat trace` | A symbolic witness for an explicit scenario, including reachability of delivery. It is a non-vacuity check, not a safety proof. |
| `#check_invariants` and `#gen_theorems` | Kernel-checked initialization and action-preservation verification conditions, with `veil.smt.trust false`. |
| `#updr … certify` and `ic3_safe` | Routing/Cache reachability theorems for the Veil relational transition systems, subject to the axiom audit. Solver success alone is not sufficient. |
| `Pipeline.pipelineSafety` | Direct Lean induction using the checked per-action VCs, Veil's WP-to-transition correspondence and `invariant_of_inductive`. No second transition model is introduced. |
| Pure Lean policy theorems | Only the stated properties of the reference functions, not correctness of a production parser, crypto library or scorer. |

The verification gate must reject nonstandard theorem axioms, including
`sorryAx`. Upstream Veil's default is to trust SMT; this project explicitly
disables it. Certification can still report a trusted fallback, so the separate
axiom audit is mandatory. Injected fixtures check that the audit rejects an
added axiom, `sorry` and a `native_decide` compiler oracle.

Pipeline's IC3 experiment encountered an upstream SMT sort-translation error
(`Expected SMT-LIBv2 sort constructor`). Its reachability result instead uses
an explicit Lean proof from the already checked VCs. The proof uses Veil's own
relational transition system, not a hand-copied interpretation of the actions.

## Model boundaries

- `Libp2p/Pipeline.lean`: one receiver's session/stream/task state machine,
  negotiated admission, verdict ownership, cancellation, delivery and forwarding
  authorization. Its receiver-side reachability proof is in
  `Libp2p/PipelineSafety.lean`.
- `Libp2p/Routing.lean`: abstract membership and routing gates. Validation,
  score classes and timer expiration are input interfaces.
- `Libp2p/Cache.lean`: cache lookup identity, IHAVE requests and tracked promises.
- `Libp2p/Policies.lean`: authentication check conjunction, envelope policy,
  negotiation boundary lemmas and exact-integer reference arithmetic.

These are not four interchangeable proofs of the same implementation.
The routing and cache models have abstract validation inputs; no refinement
theorem connects their complete reachable states to Pipeline. Their results
must not be imported into Pipeline merely because both use the word ACCEPT.
The [profile](veil-profile.md) identifies these interfaces and the
[coverage ledger](../verification/coverage.json) records per-obligation limits.
A `kernel-model` ledger entry points into a kernel-checked artifact; it does not
mean that the complete original obligation has been proved.

## Scope

The target is the inventory's **libp2p subset**, not all of libp2p/specs.
Ethereum gossip predicates, Snappy/SSZ, Ethereum message IDs, full consensus
validity, availability, aggregate resources and implementation correspondence
are excluded. QUIC/TLS and cryptographic primitives are external contracts;
there is no symbolic or computational cryptographic proof in this artifact.

The source inventory and its S/D/K classifications remain authoritative.
A profile choice is not a new MUST in the wire specification. Existing ACL2s
GossipSub and Floodsub work remains prior work, not a proof dependency.
