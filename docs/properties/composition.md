---
title: Lifecycle and End-to-End Safety Properties
last_updated: 2026-11-06
tags:
  - formal-verification
  - libp2p
  - security
  - composition
---
# Lifecycle and End-to-End Safety Properties

[Inventory and conventions](../../inventory.md). All rows are **derived
obligations (D)**, not additional libp2p wire requirements. R-03.01 and R-04.01
have [finite-model evidence](../session-safety.md) for an abstract lifecycle
profile; all other rows remain proposed. No unbounded or implementation proof
is claimed, and those checks do not establish either entire parent family.
Sources supply component
contracts; the cross-layer implications still require proof. `P` is the selected
profile and `s` a local session generation. A parent dependency means all its
applicable children. Assumptions and unverified dependencies remain explicit.

`DeliverValidated(p,t,x,k)` is an application-visible validated-delivery event,
not a raw read or entry into a validator callback. `ForwardAuthorized(t,x,k)` is
payload authorization, not permission to emit a control message. Object/context
identity may use a proved encoding equivalence, not arbitrary byte equality.

Availability, global memory/CPU bounds, eventual cleanup/progress, and DoS
resistance are excluded. Cleanup remains here only where ownership and stale
work affect authenticated identity or the object delivered.

## R-03

**Cancellation and ownership safety.**

| ID | Premise | Event | Required conclusion | Basis | Depends on |
| --- | --- | --- | --- | --- | --- |
| R-03.01 | P cancels a session-scoped operation | Its cancellation takes effect | The operation no longer has authority to create a new session-scoped delivery/credit event. | D [Lifecycle events][lifecycle] | — |
| R-03.02 | Buffer/operation ownership is released or transferred | A reference is subsequently used | It cannot expose recycled bytes as the old operation's validated payload. | D [Streams][streams] | F-05.02 |

## R-04

**Stale callbacks versus retained peer state.** A callback generation token is
one possible implementation, not a mandated representation. RetainScore is not
mistakenly removed just because a transport disconnects.

| ID | Premise | Event | Required conclusion | Basis | Depends on |
| --- | --- | --- | --- | --- | --- |
| R-04.01 | Callback belongs to terminated session s | It tries to install a handler or emit delivery/credit | It cannot act with a successor session's authority. | D [Lifecycle events][lifecycle] | R-03.01 |
| R-04.02 | P permits retained peer-wide score/metadata | A new session uses retained state | Retention does not import an old session's incomplete authentication or validation result as the new session's success. | D [Peer scoring][peer-scoring] | A-05.01, R-04.01 |

## E-01

**No bypass of the validated remote-delivery path.** Each child is a necessary
projection of the full proposed E2E statement. Local publication has a separate
trusted/validated input contract; this statement does not invent a remote sender.

| ID | Premise | Event | Required conclusion | Basis | Depends on |
| --- | --- | --- | --- | --- | --- |
| E-01.01 | A remote message is delivered as validated | Delivery provenance is inspected | A corresponding locally authenticated session for forwarding peer p exists in the trace. | D [TLS binding][tls-extension] | Q-01, Q-02, A-01, A-02, A-03, A-04, A-05, R-04 |
| E-01.02 | Same validated delivery | Protocol/byte provenance is inspected | The message came through the acknowledged GossipSub stream and well-formed RPC under P, not another stream/version. | D [Opening streams][opening], [RPC][rpc] | N-01, N-02, N-03, N-04, N-05, F-01, F-02, F-03, F-04, F-05 |
| E-01.03 | Same validated delivery | Object/context provenance is inspected | Bounded decode and the required ordered gossip checks produced ACCEPT for that object/context. | D [Ethereum topics][eth-topics], [Validators][validators] | C-01, C-02, C-04, C-06, G-01, V-01, V-02, V-03, V-04, V-05, V-06 |

## E-02

**What was validated is what is used.**

| ID | Premise | Event | Required conclusion | Basis | Depends on |
| --- | --- | --- | --- | --- | --- |
| E-02.01 | ACCEPT was produced for x/k | Validated application delivery occurs | The delivered object/context is x/k or its proved encoding-equivalent representation. | D [Validators][validators] | C-03, C-06, G-03, V-05 |
| E-02.02 | ACCEPT authorized payload forwarding for x/k | Outbound RPC is serialized | That payload/context and its policy-required envelope/size constraints are preserved. | D [Processing][processing], [Ethereum size limits][eth-limits] | E-02.01, F-04, C-01, G-06 |

## E-03

**Failure does not manufacture success.** Scope is the failing candidate or
operation, not every other valid operation sharing a peer or message ID.

| ID | Premise | Event | Required conclusion | Basis | Depends on |
| --- | --- | --- | --- | --- | --- |
| E-03.01 | Candidate failed auth, negotiation, parse, decode, or validation; or its operation was canceled | A completion tries to emit success | No validated delivery is justified by that failing candidate/operation. | D [TLS][tls-peer], [Validators][validators] | A-01, A-02, A-03, A-04, N-05, F-02, C-02, G-01, R-03, R-04 |
| E-03.02 | Rejected/ignored/canceled work contributes a scoring event | Credit/penalty is applied | Credit and penalties have the independently valid cause required by P, not the mere existence of that failed work. | D [Extended validators][extended] | G-02, M-06, R-04 |

## E-06

**Replay is interpreted at the correct layer.**

| ID | Premise | Event | Required conclusion | Basis | Depends on |
| --- | --- | --- | --- | --- | --- |
| E-06.01 | Packet data is duplicated or reordered | Remote application receipt is derived | Packet duplication alone cannot manufacture extra stream bytes/application input. | D [Stream ordering][stream-order] | Q-03, N-01 |
| E-06.02 | An authentic object is replayed within or after the deduplication interval | It is considered for validated delivery | Current object-level validation and the scoped deduplication rule apply, not a claim that valid signatures imply freshness. | D [Message cache][cache], [Ethereum validation][eth-topics] | C-05, G-03, G-04, V-03, V-04 |
| E-06.03 | Early data or reconnection replays an earlier request/control | Its effect is considered | Only the profile-authorized replay semantics apply; a new connection does not silently grant fresh object authority. | D [0-RTT replay][early-replay] | Q-05, A-05, R-04 |

## E-07

**Evidence and implementation correspondence.** This is an evidence obligation,
not an on-wire protocol rule. It is required before applying a model theorem to
a production implementation.

| ID | Premise | Event | Required conclusion | Basis | Depends on |
| --- | --- | --- | --- | --- | --- |
| E-07.01 | A result is reported for a parent/child ID | Its profile and assumptions are recorded | Fork, versions, options, arithmetic, cryptographic assumptions, and exact artifacts are identified. | D [Inventory profile](../../inventory.md#verification-profile) | — |
| E-07.02 | A model result is claimed for implementation I | Simulation/refinement mapping is supplied | I's auth, parser, callback, state, and observable-event semantics satisfy the model contract used by that result. | D [Inventory composition](../../inventory.md#composition-rule) | E-07.01 |
| E-07.03 | A proof or exploration result is published | Evidence class is stated | Finite/bounded checks, randomized tests, inherited assumptions, and unbounded proofs are distinguished without silent promotion. | D [Evidence status](../../inventory.md#evidence-status) | E-07.01 |

## Proposed composition statement

```text
For every DeliverValidated(p, t, x, k):
  there exists a corresponding local trace witnessing
  authenticated receipt -> negotiated GossipSub handling -> bounded decode
  -> GossipAccept(t, x, k), with the same object and context at use.
```

E-01.01 through E-01.03 supply the provenance projections; E-02 supplies identity
preservation; E-03 and R-04 rule out failed/stale-work substitutions. Cryptographic
claims retain their explicit probability bounds or symbolic assumptions. This
statement does not imply delivery, original-publisher attribution, full consensus
validity, or end-to-end confidentiality from intermediate gossip peers.

## Counterexample scenarios

- A valid signature check succeeds, but the handler uses a recycled payload or
  another fork's decoder result.
- A connection fails after bytes were buffered; an unrelated valid operation
  completed earlier and must not be retroactively classified as invalid.
- Callback from session s fires after s+1 authenticates as the same or another
  peer; retained score is legitimate, retained authentication authority is not.
- Several independently verified layers disagree on what their `accepted` event
  means; the composition premise is then not discharged.

[lifecycle]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/connections/README.md#connection-lifecycle-events
[streams]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/connections/README.md#definitions
[opening]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/connections/README.md#opening-new-streams-over-a-connection
[tls-peer]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/tls/tls.md#peer-authentication
[tls-extension]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/tls/tls.md#libp2p-public-key-extension
[rpc]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/pubsub/README.md#the-rpc
[validators]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/pubsub/README.md#topic-validation
[processing]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/pubsub/gossipsub/gossipsub-v1.0.md#message-processing
[cache]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/pubsub/gossipsub/gossipsub-v1.0.md#message-cache
[peer-scoring]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/pubsub/gossipsub/gossipsub-v1.1.md#peer-scoring
[extended]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/pubsub/gossipsub/gossipsub-v1.1.md#extended-validators
[eth-topics]: https://github.com/ethereum/consensus-specs/blob/204fb4a19774eabb7a2e91505365deed6b8afef8/specs/phase0/p2p-interface.md#topics-and-messages
[eth-limits]: https://github.com/ethereum/consensus-specs/blob/204fb4a19774eabb7a2e91505365deed6b8afef8/specs/phase0/p2p-interface.md#gossipsub-size-limits
[stream-order]: https://www.rfc-editor.org/rfc/rfc9000#section-2.2
[early-replay]: https://www.rfc-editor.org/rfc/rfc9001#section-9.2
