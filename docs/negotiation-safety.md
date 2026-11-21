---
title: Negotiation Failure Safety Checks
last_updated: 2026-11-21
tags:
  - formal-verification
  - libp2p
  - model-checking
  - quint
---
# Negotiation Failure Safety Checks

`abstract-negotiation-v1` satisfies the two [N-05](properties/transport-and-authentication.md#n-05)
monitors in four finite Quint/TLC instances. These are derived design
obligations, not new multistream-select wire requirements.
The [specification audit](specification-safety-audit.md) checks which conditions
come from the sources rather than added local contracts. In this model, `Reset`
means an application-visible terminating outcome, not every received QUIC
RESET_STREAM frame. RFC 9000 section 3.2 also permits delivering fully buffered
data while suppressing the reset notification; the audit models that alternative.
The original model and evidence below are preserved as the terminating-policy
profile, not promoted to a proof of all permitted transport behaviors.

## Model and contracts

The [model](../models/negotiation-safety/negotiation.qnt) uses the session
authority model's `init`, `open`, `authenticate`, and `close` transitions, with
no lifecycle operation slots. Only one generation per peer can be current.
A stream slot has one immutable origin generation and is never reused.

- An authenticated current generation can begin a stream. `propose` makes a
  selection outstanding. `Selected` represents a complete, matching success
  outcome from an abstract parser and matcher. It emits a selection only while
  a proposal is outstanding on a live stream. `NotAvailable` (`na`) returns to
  waiting for an alternate proposal, without emitting a selection.
- A truncated selection outcome, reset, or timeout can terminate negotiation
  without agreement. Session close also terminates any unfinished negotiation on
  that generation. A reset can invalidate an agreed stream before handoff; the
  negotiation timeout itself stops applying once agreement has occurred.
- A completion callback carries the original stream slot. It can run late, but
  installation requires prior agreement, a live stream, and the authenticated
  current origin generation at the point of installation. The callback never
  resolves a destination stream from the current generation of the peer.

| Obligation | Monitor |
| --- | --- |
| N-05.01 | `selectionSafe`: streams terminated before agreement never appear in the selection history. |
| N-05.02 | `installationSafe`: each recorded installation has a selection and observed agreement on its own stream, on its authenticated current origin generation. |

Termination history uses the phase before the transition, not the selection
record. Installation observations capture the phase and generation authority at
the event. A later reset or close does not retroactively invalidate earlier
success. Histories record occurrence, not multiplicity or handler teardown.

Provenance: [multistream-select protocol](https://github.com/multiformats/multistream-select/blob/9a1fbe8edadebea223f47102f1913b8026c23a1c/README.md#protocol)
and [libp2p connection lifecycle](https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/connections/README.md#connection-lifecycle-events).
The installation guard enforces N-02.01's no-dispatch-without-selection
condition at this abstract boundary. It does not discharge N-02 for concrete
negotiation or dispatch.
N-05.02 checks origin-generation authority at installation directly; it does
not import a theorem from the separate R-04.01 finite checks.

## Evidence

TLC exhausted the reachable graph in each instance with no violated invariant
and zero states queued. The [instances](../models/negotiation-safety/instances.qnt)
bound total lifetime allocations, not concurrent capacity. No trace-length
bound or cutoff is used.

| Instance | Peers | Generations | Streams | Distinct states | Depth |
| --- | ---: | ---: | ---: | ---: | ---: |
| `singleStream` | 1 | 1 | 1 | 18 | 9 |
| `concurrentStreams` | 1 | 1 | 2 | 130 | 14 |
| `reconnectingPeer` | 1 | 2 | 2 | 1,062 | 17 |
| `independentPeers` | 2 | 2 | 2 | 4,437 | 17 |

All 18 [deterministic scenarios](../models/negotiation-safety/scenarios.qnt)
passed. They include successful handoff, retry after `na`, close/reset between
agreement and handoff, late outcomes or callbacks, and independent streams and
peers. The [recorded report](../evidence/negotiation-safety/summary.json) identifies
the run by input hashes because it was captured before commit.

Quint 0.33.1 and Apalache 0.62.4 (build `7954daf`) are pinned. Apalache translates
to TLA+; TLC checks the result. This evidence trusts the translation and JVM
and is subject to TLC fingerprint collisions. It does not cover byte framing,
matching rules, protocol versions, parser correctness, cryptographic
authentication, reused slots, concurrent sessions for one peer, or code
refinement. No unbounded proof or liveness claim follows.

## Reproduce

Use Linux with Git, Node.js 24, Java 21+, `unshare`, and `ip`. Prepare the
pinned tool distribution before entering a fresh loopback-only network
namespace. The pinned translator has an upstream protobuf warning; do not
expose it to untrusted network traffic.

```sh
npm ci
node scripts/prepare-apalache.mjs
unshare --user --map-root-user --net sh -ec '
  ip link set lo up
  exec node scripts/verify-negotiation-safety.mjs
'
```

This command requires unprivileged user namespaces. On the hosted Ubuntu
runner, [the workflow](../.github/workflows/negotiation-safety.yml) creates the
network namespace with `sudo` and runs the verifier as the normal runner user.
The verifier checks the launcher and JAR hashes before launch. It records
source hashes, versions, commands, and tool logs in the printed directory
under `.artifacts/negotiation-safety/`. CI checks runner failure paths and the
80% coverage thresholds, and uploads a report and logs for the model check.

The next milestone is GossipSub validation and deduplication. Control and
scoring require separate models and evidence.
