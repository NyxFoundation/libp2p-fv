---
title: Veil Reference Profile
last_updated: 2026-11-22
tags:
  - formal-verification
  - libp2p
  - veil
---
# Veil Reference Profile

## Scope and source

Profile ID: **libp2p-veil-v13-reference**. This is an implementation-independent
reference model, not an Ethereum client configuration.

Normative source: libp2p/specs at
[`c750236de43cd8b246a824b377dfdb26bae686db`](https://github.com/libp2p/specs/tree/c750236de43cd8b246a824b377dfdb26bae686db).
The inventory links the applicable clauses. QUIC v1 and TLS 1.3 use RFC 9000
and RFC 9001. No claim about a later specification revision is made.

| Choice | Selected meaning |
| --- | --- |
| GossipSub | v1.3, with inherited v1.0/v1.1/v1.2 rules; no mixed-version interoperability claim |
| Protocol matching | Exact `/meshsub/1.3.0` for this profile; custom libp2p matchers are not prohibited |
| Envelope | StrictNoSign; a present empty forbidden field is rejected |
| Local publication | Flood publishing, with a trusted/validated local-input interface |
| Explicit peers / PX / IDONTWANT | Enabled; IDONTWANT is honored for mesh forwarding |
| 0-RTT / TLS resumption | Disabled; no security result for enabled behavior |
| QUIC migration / key updates | Transport contracts; they cannot change the application session's identity |
| Authentication | Expected Peer ID is required in this reference profile; local mutual-auth checks, TLS 1.3 and ALPN `libp2p` |
| Numerical reference | Unbounded integers/naturals; decay uses rational numerator/denominator with floor rounding |
| PX equality | Strict `score > AcceptPXThreshold`; equality is rejected |
| P3b trigger | Negative-score prune AND active squared deficit; an explicit choice at the source ambiguity |

PX equality and P3b are selected interpretations, not resolutions claimed for
every conforming implementation. Integer/floor arithmetic is a reference design
choice. IEEE-754 correspondence and comparison tolerances are not proved.

## Ownership and observable events

Session, stream and task tokens are fresh and never reused. Reconnection
allocates a new session token even for the same Peer ID. Each stream has an
immutable session owner. Each task has an immutable source stream, payload,
context and lookup ID. Arbitrary ID collisions are permitted; IDs do not imply
object equality. These are allocation/ownership contracts, not a proof of a
buffer allocator.

The receiver stores authentication and validation history monotonically.
Disconnect does not erase the fact that a past delivery was authenticated.
New effects additionally require a live owning session, an unreset stream and
an uncanceled task. `emitted/lastTask` record the most recent delivery,
forwarding or scoring event; other actions clear this event pulse. The
`no_stale_effect` invariant concerns the event's commit point, not a promise
that its session remains alive forever.

Concurrent tasks are **not coalesced by lookup ID**. Each completes independently.
`seen` suppresses delivery by ID until explicit expiration. `inWindow` tracks
which task delivered during that interval. Expiration permits a new decision;
permanent exactly-once delivery is not promised. Forwarding authorization does
not imply network transmission or dissemination.

The forwarding identity is `identity (owner (source task))`. No field equates
it with an object signer or original publisher. Payload/context coordinates are
immutable; a theorem about them does not establish real byte-buffer immutability.

## External contracts

1. **Transport:** packet integrity, ordered byte streams, offsets, flow-control
   credit, stream limits and migration/key-update correctness. The model does
   not reimplement QUIC.
2. **Authentication:** `checksPassed` must equal the conjunction specified by
   `AuthChecks.accept` for this session's actual certificate and key. ASN.1,
   X.509 time interpretation, signature verification, deterministic PublicKey
   encoding and multihashes are not implemented. Unknown noncritical extensions
   do not add a rejection predicate; sender deprecated-field omission is not
   modeled.
3. **Decoding:** `wellFormed` must mean a complete, locally bounded, schema-valid
   RPC satisfying StrictNoSign, with the task's actual immutable coordinates.
   There is no chosen concrete outer length-prefix decoder and no byte-level
   framing proof. The inventory's F-01 boundary remains open; Req/Resp rules
   have not been imported.
4. **Validation:** `complete` receives the validator's verdict for that exact
   task/context. Routing's `validatedRemote/validatedLocal` and Cache's
   `validate` are separate abstract input events, not implementations of
   that validator.
5. **Timers and scores:** expiration events are issued at permitted profile
   boundaries. Routing's score-class predicates are immutable snapshots.
   No theorem connects changing scores, retained history or numerical policy
   functions to the router transitions.

These premises are deliberately visible. They are not discharged by giving an
action a name such as `authenticate` or `validate`.

## Checks and proof limits

The source files contain the exact finite instance and immutable theory for each
model-checking run. Small finite instances test only those configurations.
No fairness or successful delivery assumption is needed by the safety theorems.
A satisfiable delivery trace checks that the model admits useful behavior.
The mutation gate also explores two tasks with different payloads/contexts but
one shared lookup ID. Removing each of three guards must produce a concrete
safety counterexample; an elaboration error is not accepted as a passing mutation.

The parameterized `Pipeline.pipelineSafety` and Routing/Cache `ic3_safe` theorems
concern arbitrary inhabitants of the model's
sorts and arbitrarily many finite transitions. They do not remove the listed
external contracts. All proof dependencies must pass `Tests/Axioms.lean`.
Coverage of the original 160 obligations is recorded separately, including
unmodeled behavior and excluded Ethereum dependencies.
