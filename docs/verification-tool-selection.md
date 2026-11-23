---
title: Verification Tool Selection
last_updated: 2026-11-23
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
| `#updr … certify` | Optional IC3 reachability certificate for a specific relational system, subject to the axiom audit. The current reference models use handwritten parameterized inductions (`pipelineSafety`, `routingSafety`, `cacheSafety`, `coreSafety`, `TemporalSafety.*`) instead; `#check_invariants` still supplies the checked per-action VCs for those proofs. |
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
- `Libp2p/Cache.lean`: cache lookup identity, bounded history buckets,
  retransmission limits, IHAVE/IWANT correspondence, tracked promise intervals
  with timer ticks, and deduplication. Reachability proof in `CacheSafety.lean`;
  acceptance/seen effect lemmas in `CacheFacts.lean`.
- `Libp2p/Routing.lean`: dynamic-score membership and forwarding with score
  snapshots, duplicate-free capacity admission, ID-keyed suppression and
  session-policy controls. Reachability/event proofs in `RoutingSafety.lean`;
  the interface contract is recorded in the composition handoff.
- `Libp2p/Core.lean`: the labelled Core product of Pipeline and Cache with
  shared seen synchronization, task/local validation authority and expiry;
  coupled safety in `CoreSafety.lean`, reusable transaction lemmas in
  `CompositionSupport.lean`.
- `Libp2p/Network*.lean`: labelled Core/Routing transactions with reachability
  projections, shared validation authority and publication IDs, authenticated
  session attribution, threshold classification and selection effects. Outputs
  are observations of enabled labels, not re-emission of persistent event flags.
- `Libp2p/Selection.lean`: checked survivor/median selection relations over
  actual peer lists and current Rat scores with cardinality theorems.
- `Libp2p/Score*.lean`: exact-rational score parameters, counters, updates,
  configuration and threshold refinement.
- `Libp2p/Temporal*.lean`: backoff extension, IDONTWANT limit counting,
  first-arrival credit ownership, peer-wide retained history and global
  causal order, as specification components with explicit boundaries.
- `Libp2p/Policies.lean`: authentication check conjunction, envelope policy,
  negotiation boundary lemmas and reference functions; certificate-field and
  protocol-selection projections in `Handshake.lean`.

Standalone Routing and Cache still have abstract validation inputs. Core and
Network restrict those inputs and prove projections of their actual transactions
into the component systems, including validation-authority bindings. This does
not imply that every standalone component execution is a composed execution.
Network still receives arbitrary rational score snapshots: ScoreHistory and the
causal-permission components have not been coupled into that transition system.
There is no whole-inventory composition theorem or exhaustive finite Network
exploration; its integration scenarios are kernel-checked traces.
The [profile](veil-profile.md) identifies these interfaces, the
[verification results](verification-results.md) record checks and review limits,
and the [coverage ledger](../verification/coverage.json) records per-obligation limits.
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
