---
title: Specification Safety Audit of Session and Negotiation Models
last_updated: 2026-11-21
tags:
  - formal-verification
  - libp2p
  - specification-audit
  - model-checking
---
# Specification Safety Audit of Session and Negotiation Models

## Conclusion

The checks in PRs #4 and #5 establish conditional properties of their finite
models, not that the libp2p specifications imply all four design obligations.
This audit establishes **no normative specification contradiction or concrete
implementation vulnerability**. It finds a transport-to-application mapping that
must not be assumed: receiving QUIC `RESET_STREAM` does not necessarily terminate
application negotiation. RFC 9000 explicitly permits delivering buffered data.

The result for the scoped sources is:

| Obligation | Source-level assessment | Model evidence and remaining contract |
| --- | --- | --- |
| R-03.01 | The cited lifecycle section does not define operation cancellation or its point of effect. The session-scoped safety goal remains D, not a wire rule. | Guarded model satisfies the monitor; disabling its cancellation guard produces a design-counterexample. A local cancellation/effect contract is still needed. |
| R-04.01 | Connection/stream identity is meaningful in the sources, but the cited clauses do not define ownership and publication of asynchronous application results. No generation-token algorithm is mandated. | Removing the generation gate produces a counterexample in the abstract model, not a demonstrated specification-conforming execution. The concrete callback-to-session mapping remains unproved. |
| N-05.01 | Complete matching acknowledgement is the source basis for agreement. Neither a truncated message nor `na` is an acknowledgement. Wire reset alone is **not** application termination; negotiation timeout is a local policy. | Both RFC-permitted buffered-reset policies satisfy the conditional goal under the modeled local termination contract. The stronger claim that wire reset forbids later selection has a source-supported counterexample. |
| N-05.02 | Negotiated protocol belongs to its stream. The sources do not supply the atomic local handler-installation/cancellation interface assumed by #5. | Unguarded local installation can occur after close while the model's selection boundary still holds. This is a local-contract probe, not proof that installing a usable handler on a different stream is specification-conforming. |

None of these findings changes the inventory's D classifications or marks a full
parent family discharged. The authenticated transport, parser, and implementation
correspondence dependencies remain open. In particular, retained peer-wide score
is not session authority: these probes do not disallow legitimate retained score.

## Sources and normative strength

The libp2p and multistream-select commits below are the inventory's immutable
snapshots, not current branch heads. RFC 9000 is the May 2021 published RFC; this
slice does not claim to incorporate every later erratum or extension.

| Source | Relevant contract and strength |
| --- | --- |
| [Connection definitions][definitions] | Connections provide security and logically independent streams. This supplies context identity, not a callback API or a single-current-connection-per-peer requirement. |
| [Connection lifecycle events][lifecycle] | Event notification is recommended. The text states: "The full set of lifecycle events is not currently specified". The listed events describe connection/stream opening and closure, not cancellation linearization. |
| [Connection protocol negotiation][negotiation] | The responder echoes a supported protocol ID to signal agreement; `na` permits another proposal or closing the channel. These are protocol semantics, not invented uppercase MUSTs. |
| [Opening new streams][opening] | Handlers are selected for the requested stream. Custom match predicates are allowed; exact string matching is the default, not a universal requirement. |
| [Supported protocols][supported] | Connection-scoped support is SHOULD; support MAY change at any time. The models do not check dynamic protocol-support changes. |
| [Multistream-select protocol][mss] | Notes 1 and 2 specify length prefix and terminating newline. Note 3 allows simultaneous headers; implementation recommendations use SHOULD for batching. The audit starts after the MSS header exchange and assumes a correct reply recognizer. |
| [TLS peer authentication][tls] | Certificate failures require aborting the attempt; the server must not process client data when verification fails. This does not define cancellation of already-authenticated application work. Authentication is an external contract here. |
| [GossipSub retained score][score] | Peer score survives disconnect for a configured time. This does not make all old application results invalid, nor define the session-scoped callback events in R-03/R-04. |
| [RFC 9000 §2.4][quic-api] | Defines stream operations that an application can rely on, but explicitly does not define a QUIC API. |
| [RFC 9000 §3.2][quic-receive] | An implementation MAY interrupt delivery, discard unread data, and signal reset. With all stream data received and buffered, it may suppress reset and remain in `Data Recvd`. No rule requires that data not be delivered after reset receipt. |
| [RFC 9000 §3.3][quic-transitions] | The sender MUST NOT send STREAM after sending RESET_STREAM. Already-sent packets may arrive late. The new model emits no new bytes after reset. |

The absence assessments above concern these cited interfaces. They are not a
repository-wide theorem that no implementation or other specification can impose
a stronger contract. A mutation is not evidence of conformance to all these
sources: that requires an event/refinement mapping, not just a missing MUST.

## Audit of the existing guards

The model revisions examined are #4 at
`20416b0a97f168bfecf68201e6ae7f616c7c37c4` and #5 at
`15e2b383eceb3bf7b256026c599e14dc8bf513fa`. Their model files and captured evidence
are preserved; this audit does not relabel their results as specification proofs.

| Model condition | Origin | Assessment |
| --- | --- | --- |
| `lifecycle.authorized`: current session is authenticated and result is `accept` | External authentication/validation interfaces | No crypto, parser, or application-validator proof is supplied by the lifecycle model. |
| `not(o.cancelled)` | Additional local contract | Defines cancellation as revoking future session-scoped effects; it is not established by the lifecycle event recommendation. |
| `current == o.session` | Additional ownership mechanism | One way to prevent stale authority. Immutable ownership or other mechanisms could satisfy the goal without generation counters. |
| `use` checks authority and emits in one transition | Additional atomicity contract | No interleaving between check and effect is modeled. A concrete check-then-use race is outside the old result. |
| One current session per peer; fresh, unrecycled slots | Profile bounds/design choices | Not a general libp2p topology requirement or a cutoff argument. |
| `negotiation.receive`: `Offered` plus complete matching `Selected` | Protocol semantics plus trusted parser/matcher | No selection from `na` or a partial acknowledgement; concrete framing and matching remain assumptions. |
| `receive(Reset)` immediately ends negotiation | Selected application boundary/policy | Valid as an application-visible termination signal, or a chosen discard-and-notify policy. Not every raw QUIC RESET_STREAM maps to this event. |
| `Timeout` ends unfinished negotiation | Local termination policy | No universal deadline or callback-cancellation API is specified by the cited MSS text. |
| `callback`: agreement, live origin, immutable stream identity, atomic check/install | Source stream association plus additional local contracts | The association is source-grounded; the exact terminal-state gate, publication point, and API are design conditions, not a proved refinement. |
| Histories record earlier successful effects | Model observation choice | Later close/cancel must not retroactively invalidate a previously authorized event. Multiplicity and teardown are not established. |

## Executable contrast checks

[reset-boundary.qnt](../models/specification-safety/reset-boundary.qnt) models a
small receiving-side boundary, not QUIC or MSS in full. It begins with one
already-authenticated connection, one stream, an exchanged MSS header, and an
outstanding proposal. `MatchingEcho` abstracts a complete matching response and
all receive-side stream data, including FIN. `NotAvailable` permits one further
proposal; `Truncated` represents an incomplete response at end of input.

The peer can send each of those outcomes. The scheduler can interleave reading,
reset receipt, local timeout, close, one authenticated reconnect, and a local
callback. `wireReset(true)` retains a fully buffered matching response and
suppresses the reset notification. `wireReset(false)` discards and notifies.
The `discard`, `deliver`, and `either` profiles choose between these policies;
`deliver` still discards when no complete reply is buffered.

This is a **restricted source-supported slice**, not an overapproximation of all
specification executions. It omits partial reassembly followed by late remaining
bytes, repeated reset frames, arbitrary protocols, framing bytes, dynamic support,
simultaneous open, other streams, and other peers. It does not impose these
restrictions as new wire rules. There is no fairness or progress assumption.

Local timeout/close discard pending input and commit termination in this profile.
That is an explicit local contract, not a deduction from wire reset. The guarded
callback requires an agreed, unterminated original stream on current generation
1. A successor uses generation 2; the old stream is never rebound to it. The
unguarded variant installs local bookkeeping on the old stream after close. It
sends no bytes and does not claim a live transport or a conforming production API.

| Check | Expected result | Meaning |
| --- | --- | --- |
| `sessionProtected` | Complete exploration | R-03.01/R-04.01 hold with the existing design guards in a one-peer/two-generation/one-operation instance. |
| `cancellationGap`, `generationGap` | Counterexamples | Existing lifecycle transitions with one design guard disabled. No specification-conformance conclusion. |
| `discardReset`, `deliverBufferedReset`, `eitherReset` | Complete exploration | Conditional selection and local-installation safety hold in both buffered-reset interpretations. Only `discardReset` also requires the stronger wire-reset hypothesis. |
| `handoffBoundary` | Complete exploration | Correct acknowledgement and local selection termination do not alone establish the omitted installation contract. |
| `wireResetNotCancellation` | Counterexample | The stronger wire-reset hypothesis fails under an explicitly permitted transport choice. This is not a violation of N-05.01's premise. |
| `terminalHandoffGap` | Counterexample | The local installation goal fails after a signalled reset or close without its terminal-origin contract; not a demonstrated wire violation or exploit. |

The reset counterexample has this source correspondence:

1. A proposal is outstanding after the MSS header exchange.
2. The receiver buffers a complete matching echo and FIN. The sender can have
   sent FIN without yet receiving its acknowledgement.
3. RESET_STREAM arrives. Under §3.2, the receiver retains fully received data and
   suppresses the notification; negotiation has **not** been terminated locally.
4. The application reads the matching response and records selection on the same
   stream. No post-reset STREAM send or cross-stream byte substitution occurs.

This rejects `wire reset received => no later selection`, not
`negotiation terminated without agreement => no selection`. In the final state,
`resetSelectionViolation` is true, but `endedWithoutAgreement` and `terminal` are
false and both actual safety monitors hold. The direct scenario for this trace
first failed under the old immediate-termination abstraction and passed after
adding the source-permitted buffered-delivery branch.

All five positive finite explorations and four expected probes are recorded in
[evidence](../evidence/specification-safety/summary.json), with full normalized
TLC logs alongside it. Twenty deterministic scenarios include normal success,
`na` retry, incomplete replies, both reset policies, local timeout, stale
installation, reconnect, and preservation of earlier success. The probe flags
observe the pre-effect state independently of the optional installation guard.
Overall `passed` means the expected positive and negative results were observed,
not that every tested variant satisfies safety.

Bounds are total lifetime allocations, not concurrent capacities. The lifecycle
instances allocate one operation and one or two session generations. The new
boundary allocates one peer, two generations, one stream, at most two proposals,
and one reset receipt. TLC exhausts positive reachable graphs without a
trace-length bound; there is no cutoff or unbounded theorem. The report gives
state counts, graph depths or witness lengths, tools, commands, and source hashes.
Quint translation, Apalache, TLC/JVM, and TLC fingerprinting remain trusted;
collision estimates and warnings are retained in the logs.

## Reproduce

Use Linux, Node.js 24, Java 21+, Git, `unshare`, and `ip`. From this branch:

```sh
npm ci
npm run test:coverage
node scripts/prepare-apalache.mjs
unshare --user --map-root-user --net sh -ec '
  ip link set lo up
  exec node scripts/verify-specification-safety.mjs
'
```

The pinned Apalache distribution must be prepared before isolation. Its known
protobuf warning is not fixed here; the verifier refuses any network interface
other than loopback, checks launcher/JAR integrity before execution, and bounds
subprocess time and log reads. On hosts that disable unprivileged namespaces,
use the isolated [CI workflow](../.github/workflows/specification-safety.yml).

The output is a fresh directory under `.artifacts/specification-safety/`; no old
artifact directory is reused. Run `node --test tests/specification-audit-runner.mjs`
in the same isolated environment for end-to-end and failure-path tests. Captured
reports identify exact tested inputs by SHA-256 because runs precede commits.
To refresh the checked-in snapshot, copy the new run's `summary.json` and `.log`
files into `evidence/specification-safety/`, then run `npm run test:coverage` to
check every input hash and reclassify each published TLC result. These are
synthetic model traces, not production traffic or credentials.

The next inventory slice must repeat the clause/guard/assumption distinction
before model checking. These findings do not expand the selected libp2p scope
into Ethereum validation, full QUIC verification, or implementation correctness.

[definitions]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/connections/README.md#definitions
[lifecycle]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/connections/README.md#connection-lifecycle-events
[negotiation]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/connections/README.md#multistream-select
[opening]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/connections/README.md#opening-new-streams-over-a-connection
[supported]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/connections/README.md#supported-protocols
[mss]: https://github.com/multiformats/multistream-select/blob/9a1fbe8edadebea223f47102f1913b8026c23a1c/README.md#protocol
[tls]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/tls/tls.md#peer-authentication
[score]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/pubsub/gossipsub/gossipsub-v1.1.md#peer-scoring
[quic-api]: https://www.rfc-editor.org/rfc/rfc9000#section-2.4
[quic-receive]: https://www.rfc-editor.org/rfc/rfc9000#section-3.2
[quic-transitions]: https://www.rfc-editor.org/rfc/rfc9000#section-3.3
