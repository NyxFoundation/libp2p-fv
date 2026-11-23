---
title: Veil Reference Profile
last_updated: 2026-11-23
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
| Numerical reference | Exact rational scores/counters/decay (`Libp2p/ScoreState.lean`); floor/integer or IEEE variants are excluded |
| PX equality | Strict `score > AcceptPXThreshold`; equality is rejected |
| P3b trigger | Negative-score prune AND active squared deficit; an explicit choice at the source ambiguity |
| P7 | A penalty event records the raw counter increment; the weight applies the square |
| Score state | Exact Rat per-peer history (`ScoreConfig`/`ScoreState`); configured topics only |
| Time | Specification relations with serial/timestamp ordering; no wall-clock algorithm |

PX equality, P3b and the P7 event counting are selected interpretations, not
resolutions claimed for every conforming implementation. Rational arithmetic is
a reference design choice; IEEE-754 correspondence and comparison tolerances
are not proved and are excluded from the reference profile.

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
   do not add a rejection predicate. `Handshake.localCertificate` omits deprecated
   unique-ID fields, while the receiver's MAY-reject choice is explicit;
   correspondence of the field record to serialized ASN.1 remains external.
3. **Decoding:** `wellFormed` must mean a complete, locally bounded, schema-valid
   RPC satisfying StrictNoSign, with the task's actual immutable coordinates.
   There is no chosen concrete outer length-prefix decoder and no byte-level
   framing proof. The inventory's F-01 boundary remains open; Req/Resp rules
   have not been imported.
4. **Validation:** `finishValidation` receives the validator's verdict for that
   exact task/context; it does not implement that validator. In the standalone
   models, Routing's `validatedRemote/validatedLocal` and Cache's `validate` are
   abstract inputs. Core and Network restrict those actions to transactions
   authorized by the same Pipeline task or trusted local-publication input;
   their `validation_binding` theorems prove that connection.
5. **Timers and scores:** expiration events are issued at permitted profile
   boundaries. Network classifies each current rational score snapshot through
   `ScoreThresholds`; `refreshScores` accepts an externally supplied snapshot.
   `ScoreHistory` separately connects exact numeric updates to real
   TemporalRetention transitions. No theorem binds those histories to Network's
   refresh inputs or binds the separate temporal components to Network events.

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

The parameterized `Pipeline.pipelineSafety`, `Routing.routingSafety`,
`Cache.cacheSafety` and `Core.coreSafety` theorems, plus the five
`TemporalSafety` components, concern arbitrary inhabitants of the models' sorts
and arbitrarily many finite transitions. They reuse the kernel-checked per-action
verification conditions and Veil's WP-to-transition correspondence; the earlier
`ic3_safe` certificates were replaced by these handwritten inductions when the
models grew, and `#check_invariants` still runs the per-action VCs with
`veil.smt.trust false`. All proof dependencies must pass `Tests/Axioms.lean`.
Core and Network use labelled transactions over the actual component transition
systems. Their reachability projections allow stuttering, and Network additionally
binds validation authority, authenticated input/output sessions, peer selection,
publication IDs and expiration. `Tests/Network.lean` supplies kernel-checked
reachable traces and negative scenarios; it is not exhaustive finite exploration
of the coupled Network system. Component finite checks do not fill that gap.

TemporalKnowledge's permission relation characterizes the selected observation
projection, not an implementable receiver detector. It and ScoreHistory remain
separate from Network. There is no single theorem composing all these components
or establishing implementation-wide or inventory-wide safety.

Every inventory child points to a kernel-checked artifact or a recorded
external/excluded boundary; `scripts/check_coverage.py --require-complete` is a
bookkeeping gate, not a discharge of the listed boundary conditions.
