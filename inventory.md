# Property Inventory

## 1. Purpose and evidence status

This inventory turns the research objective into explicit verification
obligations. It is not a list of properties already satisfied by libp2p,
Ethereum clients, or any particular implementation. **All entries are proposed**;
there are currently no models, completed proofs, model-checking results, or
implementation-conformance results in this repository.

Each eventual result must identify its assumptions, specification profile,
formal statement, artifact, and evidence boundary. A counterexample is a useful
research result, not a reason to silently weaken the original claim.

Property kinds:

- **S**: specification-derived obligation, to be traced to an exact clause in the
  selected profile; a paraphrase here is not itself a normative specification.
- **D**: defensive design or composition goal that may require implementation
  choices beyond the wire specification.
- **H**: hypothesis to prove, qualify, or refute; not an assumed protocol guarantee.

Evidence classes must remain separate: a mathematical proof under stated
assumptions, exhaustive exploration of a stated finite model, bounded exploration,
randomized simulation, and implementation testing support different claims.
A finite search with no counterexample is not an unbounded proof.

## 2. Scope and communication path

```text
Untrusted candidate address / expected Peer ID (external discovery input)
  -> IP / UDP / QUIC v1
     [TLS 1.3 + libp2p certificate identity binding]
  -> QUIC stream
  -> multistream-select protocol negotiation
  -> GossipSub RPC framing / Protobuf
  -> GossipSub routing, control messages, caches, scoring
  -> Snappy block decompression / SSZ decoding
  -> fork-specific Ethereum gossip validation
  -> validated delivery event / authorized forwarding
```

The diagram describes dependencies, not a mandatory implementation scheduling
order. Size checks, message-ID computation, duplicate filtering, and validation
may be interleaved; that interleaving is itself part of the verification target.

Included: inbound and outbound communication, remote-message forwarding, local
publication, connection/stream lifecycle, supported gossip topics, validation
callbacks, heartbeat/timers, and resource accounting at their boundaries.

Excluded initially: Req/Resp; discv5/ENR internals and discovery algorithms;
TCP/Noise/Yamux/mplex fallback; relays and NAT traversal; full block import,
consensus state transition, fork choice, execution validity, and Engine API;
application-level end-to-end confidentiality; side channels and OS/kernel
correctness. Discovery and membership selection still appear as adversarial
inputs. Exclusion is not a claim that these components are safe.

Ethereum gossip acceptance is not equivalent to full consensus validity.
Transport Peer IDs, immediate forwarding peers, object signers, validators, and
original publishers are distinct identities. Ethereum uses StrictNoSign for the
GossipSub envelope; object-level authentication must not be inferred from an
absent pubsub signature.

Terminology used below:

- **StrictNoSign**: the unsigned GossipSub envelope policy; it does not remove
  signatures or proofs required inside Ethereum objects.
- **IDONTWANT**: an optional GossipSub v1.2+ control message asking a peer not to
  send specified message IDs; it is not an application validity verdict.
- **GRAFT / PRUNE**: mesh membership control messages; **PX** means peer exchange,
  which supplies candidate peers rather than trusted membership evidence.

## 3. Specification profile and reproducibility

The following are immutable **reference snapshots**, inspected when establishing
this inventory. They are not a selected deployment profile or proof coverage:

| Reference | Snapshot / entry point |
| --- | --- |
| libp2p specifications | [`c750236de43cd8b246a824b377dfdb26bae686db`](https://github.com/libp2p/specs/tree/c750236de43cd8b246a824b377dfdb26bae686db) |
| Ethereum consensus specifications | [`204fb4a19774eabb7a2e91505365deed6b8afef8`](https://github.com/ethereum/consensus-specs/tree/204fb4a19774eabb7a2e91505365deed6b8afef8) |
| multistream-select | [`9a1fbe8edadebea223f47102f1913b8026c23a1c`](https://github.com/multiformats/multistream-select/tree/9a1fbe8edadebea223f47102f1913b8026c23a1c) |
| QUIC transport / TLS integration | [RFC 9000](https://www.rfc-editor.org/rfc/rfc9000), [RFC 9001](https://www.rfc-editor.org/rfc/rfc9001), [TLS 1.3 / RFC 8446](https://www.rfc-editor.org/rfc/rfc8446) |

Before verification, a result-specific profile must fix:

1. Ethereum network, genesis context, fork schedule, targeted fork(s), and all
   inherited networking amendments. Phase 0 alone is not a current-fork profile.
2. GossipSub protocol IDs, negotiated version pairs, enabled extensions, and
   compatibility behavior. IDONTWANT obligations apply only if enabled.
3. Topic schemas, subnet mapping, message-ID rules, StrictNoSign policy,
   validation order, and ACCEPT/REJECT/IGNORE behavior for each topic.
4. Scoring weights, thresholds, caps, decays, mesh parameters, explicit peers,
   PX policy, heartbeat, cache lifetimes, and all input/resource limits.
5. QUIC/TLS version and algorithms; certificate policy; resumption, 0-RTT,
   migration, Retry, and key-update support. Disabled features are explicit
   exclusions, not vacuously established security results.
6. Clock and scheduler semantics, arithmetic representation, and attacker powers.
7. Model and implementation commits, if applicable; exploration bounds, seeds,
   fairness assumptions, and proof dependencies. Implementation selection and
   verification tools remain open at this inventory stage.

## 4. Assumptions and attacker model

These assumptions are to be attached selectively to claims, not silently granted
as a single trusted network abstraction.

| ID | Assumption or parameter to make explicit |
| --- | --- |
| A-CRYPTO | Exact signature, hash, AEAD, key-exchange, BLS, and KZG security assumptions for the selected claim; random generation and key storage requirements. Record whether each primitive is abstracted, proved, or inherited from external work. |
| A-KEYS | Which honest transport and validator keys remain uncompromised, when compromise is allowed, and which forward-secrecy guarantees are sought. |
| A-ADV | A network attacker may observe, inject, replay, drop, delay, reorder, or duplicate packets and control Byzantine peers, their keys, subscriptions, and control messages. Packet modification is constrained only by the cryptographic model, not excluded by assumption. |
| A-MEMBER | No default honest-majority or Sybil-cost assumption. Any bound on Byzantine identities, adversarial connections, or dishonest mesh neighbors must be stated. Candidate addresses and PX records are untrusted. |
| A-TIME | Monotonic timer behavior, wall-clock skew, heartbeat scheduling, validation progress, and link-delay/loss bounds where required. Arbitrary packet loss is permitted for safety, but rules out unconditional delivery. |
| A-CACHE | For delivery claims, specify how long every required message, advertisement, duplicate entry, and pending request remains available relative to forwarding/validation delays. |
| A-TOPO | For dissemination claims, characterize the maintained topic-specific honest forwarding paths, subscription stability/churn, and sampling distribution. Merely having an honest peer somewhere in the network is insufficient. |
| A-VALID | Topic-specific application validity predicates and available chain context, including how unknown dependencies and temporarily unverifiable objects are handled. The predicate is not full block validity. |
| A-LIMITS | Concrete global and per-peer/topic limits, queue admission/eviction policies, message size bounds, and processing budgets. Resource safety does not imply availability under saturation. |
| A-REFINE | Exact correspondence between mathematical/model state and implementation events, arithmetic, parsers, cryptographic APIs, callbacks, and scheduling. This is an obligation to establish, not a blanket assumption of correct implementation. |

Safety claims should tolerate arbitrary scheduling and hostile peers except where
an explicit precondition is essential. Progress and probabilistic claims require
additional assumptions and must expose them in the statement.

## 5. Layer properties

All rows have evidence status **proposed**. The source labels refer to Section 10.
Version-specific MUST/SHOULD distinctions, exceptions, and operational preconditions
must be preserved when translating these candidates into formal statements.

### 5.1 QUIC and TLS security / lifecycle

Sources: QUIC, TLS, libp2p-QUIC, libp2p-TLS. Scope: one transport connection and its
mapping to a libp2p session; composition obligations are intentionally included.

| ID | Kind | Candidate property and qualification |
| --- | --- | --- |
| Q-01 | S | Under A-CRYPTO and A-KEYS, application traffic has the confidentiality/integrity guarantees of the selected QUIC/TLS mode. State adversarial advantage or symbolic assumptions; do not claim Initial packets are confidential or all metadata is hidden. |
| Q-02 | D | Bytes may be buffered during the handshake, but no application event treats them as peer-authenticated before the local required peer-authentication checks succeed. |
| Q-03 | S | Packet replay, loss, duplication, and reordering do not manufacture additional ordered stream bytes or cause cross-stream data delivery. A stream reset may expose only a partial prefix. |
| Q-04 | D | Connection-ID changes, migration, key updates, resumption, and reconnects do not substitute one authenticated Peer ID/session generation for another. Only selected features are covered. |
| Q-05 | D | If 0-RTT is enabled, replayable early data cannot trigger an effect that requires fresh peer authentication or replay resistance; otherwise early application data is rejected. Ordinary 1-RTT assumptions must not be applied to 0-RTT. |
| Q-06 | S | QUIC transport validation, flow-control, stream-limit, and amplification rules are respected for the selected feature set. Connection closure cancels or invalidates dependent application work. |

### 5.2 libp2p peer authentication

Sources: libp2p-TLS, libp2p-QUIC. These are protocol-authentication obligations,
not merely the security of the underlying signature algorithm.

| ID | Kind | Candidate property and qualification |
| --- | --- | --- |
| A-01 | S | Certificate structure, validity, self-signature, required libp2p extension, and unsupported critical extensions are checked as required; failure never yields authenticated success. |
| A-02 | S | The host-key signature binds the prescribed domain-separated encoding of the certificate public key to the libp2p identity key; a valid signature on different bytes is insufficient. |
| A-03 | S | Peer ID derivation uses the authenticated host public key. If an expected Peer ID is supplied, a mismatch aborts the connection. |
| A-04 | S | Mutual authentication and the required TLS version/ALPN are enforced. A compatible cipher suite alone does not establish a libp2p identity. |
| A-05 | D | The authenticated identity is immutable within a session generation, and stored metadata, caches, scores, and deferred callbacks are associated with the correct identity and lifetime. Peer-wide state retained across reconnects follows an explicit policy. |

### 5.3 Streams and protocol negotiation

Sources: Connections, MSS, libp2p-QUIC.

| ID | Kind | Candidate property and qualification |
| --- | --- | --- |
| N-01 | S | Stream bytes retain order and remain isolated across connections, stream IDs, and session generations, including reset and half-close transitions. |
| N-02 | S | A GossipSub handler starts only after the required successful protocol negotiation. The dispatched protocol ID/version equals the negotiated value. |
| N-03 | S | Protocol-ID matching follows exact supported-ID rules; unsupported or malformed negotiations do not fall through to a different handler. |
| N-04 | D | Negotiation consumes exactly its own framing. Remaining application bytes are neither lost, duplicated, nor reinterpreted as negotiation state. |
| N-05 | D | Truncation, reset, timeout, or connection failure cannot produce a successful negotiation or revive a terminated handler through a late callback. |

### 5.4 GossipSub framing and envelope parsing

Sources: Pubsub, GS10, GS11; GS12 and GS13 only where selected.

| ID | Kind | Candidate property and qualification |
| --- | --- | --- |
| F-01 | D | Incremental parsing is invariant under arbitrary partitioning/coalescing of the same ordered byte sequence, with the same complete frames and terminal incomplete/error outcome. |
| F-02 | S | Length varints, frame sizes, truncation, and type/range limits are checked before the corresponding unbounded allocation or processing. Incomplete input is never accepted as a complete RPC. |
| F-03 | S | Protobuf repeated, unknown, duplicate singular, and missing fields have the selected schema semantics. Do not impose a canonical Protobuf byte encoding where the specification permits alternatives. |
| F-04 | S | StrictNoSign envelope requirements and control-message version rules are enforced. An authenticated forwarding peer is not interpreted as the object signer or original publisher. |
| F-05 | D | Mixed control/data RPCs and asynchronous parsing preserve the correspondence among sender, topic, message ID, payload, and negotiated protocol version. |

### 5.5 Compression, SSZ, topic and fork context

Sources: ETH0 and the selected fork amendments. Gossip payloads use Snappy block
compression, not the Snappy framing used by Ethereum Req/Resp.

| ID | Kind | Candidate property and qualification |
| --- | --- | --- |
| C-01 | S | Compressed and decompressed size/type bounds are enforced, including hostile length declarations and compression bombs. Limits cover temporary buffers, not just the final object. |
| C-02 | S | Malformed Snappy or invalid SSZ is not exposed as a valid typed object; offsets, lengths, list bounds, and trailing data follow the selected specification. |
| C-03 | D | For values valid for a selected SSZ schema, decoding their encoded form returns the same value. Any reverse/canonicality statement applies only to encodings the schema defines as canonical. |
| C-04 | S | Topic, subnet, fork context, schema, and encoding are interpreted together. Unknown or mismatched contexts cannot be silently decoded and accepted under another schema. |
| C-05 | S | Message-ID computation uses the exact selected Ethereum rule, including valid/invalid compression domains and topic context where prescribed. Deduplication equivalence follows that rule, not compressed-byte equality by assumption. |
| C-06 | D | The validated payload/context and the delivered or forwarded payload/context are equal or related by an explicitly justified encoding equivalence; mutable buffers cannot change them after validation. |

### 5.6 Message routing, validation, and duplicate handling

Sources: Pubsub, GS10, GS11, ETH0 and fork amendments.

| ID | Kind | Candidate property and qualification |
| --- | --- | --- |
| G-01 | S | A newly received remote object is not exposed as validated or forwarded as valid until the required application result is ACCEPT. IGNORE and REJECT do not authorize forwarding that object. This does not prohibit permitted pre-validation control messages. |
| G-02 | S | IGNORE is distinguished from REJECT and does not incur the invalid-message penalty reserved for REJECT. Other independently justified penalties remain possible. |
| G-03 | D | Concurrent duplicate arrivals obey a specified validation/coalescing policy. Completion cannot accidentally authorize a different payload, fork context, or message ID. |
| G-04 | D | At-most-once validated application delivery is scoped to an explicit deduplication key, retention/admission policy, and session-independent cache lifetime; it is not a forever exactly-once guarantee. |
| G-05 | S | IHAVE/IWANT promises, cache availability, response limits, expiration, and penalties correspond to actual advertisement/request history and the selected rules. |
| G-06 | S | Mesh forwarding, gossip, fanout, flood publishing, and explicit-peer behavior follow their separate eligibility and scoring rules. Locally published objects satisfy an explicit input-validity contract. |
| G-07 | D | If IDONTWANT is enabled, suppression/cancellation is bounded, version-correct, and peer-scoped; an attacker cannot mutate another peer's suppression state. Verify any enabled lifetime/limit policy explicitly. |
| G-08 | H | Under A-TOPO, A-TIME, A-CACHE, A-VALID, and adequate admitted processing capacity, publication reaches the intended honest subscribers. Define deterministic reachability or a delivery probability/deadline, not an unsupported unconditional eventual-delivery claim. |

### 5.7 Mesh control, peer exchange, and scoring

Sources: GS10, GS11; ETH0 and fork-specific scoring configuration.

| ID | Kind | Candidate property and qualification |
| --- | --- | --- |
| M-01 | S | GRAFT/PRUNE, backoff creation/extension/expiry, disconnect, subscribe/unsubscribe, and heartbeat transitions respect eligibility and explicit-peer exceptions. |
| M-02 | H | Given enough eligible peers and a stable scheduling/topology interval, maintenance restores the selected mesh targets. Degree bounds are phase-specific postconditions, not invariants after every incoming GRAFT. |
| M-03 | S | Inbound/outbound selection quotas, opportunistic grafting, and peer sampling follow the selected algorithm. Any security claim states the sampling distribution and adversarial membership control. |
| M-04 | S | Scoring counters, caps, weights, thresholds, activation windows, and decays implement the selected equations, including global versus per-topic contributions. |
| M-05 | D | Finite-precision arithmetic does not silently change required threshold decisions or create NaN, infinity, or overflow; exact-rational proofs require a separate numerical correspondence argument. |
| M-06 | D | Rewards and penalties have a causal event and are attributed to the correct forwarding peer/topic. An invalid object cannot poison unrelated objects' validation state or earn valid-delivery credit. |
| M-07 | H | A precisely defined observable misbehavior drives score below a specified threshold within stated time/traffic bounds. Cross-topic reward compensation and configured weights must be considered; this hypothesis is known to fail for some historical configurations. |
| M-08 | D | PX input cannot bypass authentication, address-validation/admission limits, or alter the meaning of existing authenticated identities. No honest topology is inferred from an untrusted PX recommendation. |

### 5.8 Ethereum gossip validation

Sources: ETH0 and selected fork amendments. Instantiate these obligations for
each included topic, rather than treating all Ethereum objects identically.

| ID | Kind | Candidate property and qualification |
| --- | --- | --- |
| V-01 | S | The exact ordered topic-specific checks determine ACCEPT, REJECT, or IGNORE. Reordering checks must preserve the specified observable result and state effects, not just the final Boolean validity. |
| V-02 | S | Required BLS signatures, aggregation/membership checks, and applicable KZG/Merkle proofs are checked against the correct message, domain, keys, and chain context before ACCEPT. No universal BLS/KZG requirement is imposed on every topic. |
| V-03 | S | Slot/epoch windows, proposer/committee/subnet rules, duplicate rules, and fork applicability follow the selected topic specification and clock assumptions. |
| V-04 | D | Unknown dependencies and temporary lack of validation context are not confused with cryptographic invalidity. Seen-state mutation follows the specified successful-check point, so invalid arrivals cannot preempt a later valid object. |
| V-05 | D | Validation has an identified context snapshot or revalidation rule when clock, fork, subscription, or chain context changes during asynchronous work. ACCEPT is not silently reused under an incompatible context. |
| V-06 | S | Gossip ACCEPT establishes only the selected gossip predicate. It is never labeled as full block, execution, consensus-state-transition, or finality validity. |

### 5.9 Resource bounds and cleanup

Sources: QUIC, GS11, enabled extensions, ETH0; additional global policy is a design
obligation, not an automatic guarantee supplied by these specifications.

| ID | Kind | Candidate property and qualification |
| --- | --- | --- |
| R-01 | D | Connections, streams, subscriptions, mesh entries, backoff/PX state, message/seen caches, suppression sets, queues, and in-flight validations have explicit global as well as local bounds. |
| R-02 | D | New Peer IDs, reconnects, topic churn, or many small inputs cannot evade the stated global memory/work-admission bounds. Per-peer limits alone are insufficient. |
| R-03 | D | Rejection, timeout, cancellation, reset, and disconnect release or transfer ownership of resources exactly as policy requires. Retained peer-scoring state has an explicit bound and lifetime. |
| R-04 | D | No terminated session's deferred completion can recreate state or produce delivery/credit in another session. Legitimate peer-wide retained state follows its own lifecycle. |
| R-05 | H | Under a stated attacker budget and fair admitted scheduling, legitimate work still progresses. Queue safety alone does not prove this availability property or eliminate all CPU/bandwidth denial of service. |

## 6. End-to-end composition obligations

Define an external event `DeliverValidated(peer, topic, object, context)` distinct
from raw receipt, entry into a validation callback, or preliminary decoding.
`ForwardAuthorized` means forwarding an object under the selected validity and
routing policy, not merely sending a control message.

| ID | Kind | Candidate end-to-end claim | Principal dependencies |
| --- | --- | --- | --- |
| E-01 | D | Every validated remote delivery has a trace through the correct locally authenticated session and negotiated protocol, successful bounded parsing/decoding, and ACCEPT under the recorded topic/fork context. | Q-02, A-01 through A-05, N-01 through N-05, F-01 through F-05, C-01 through C-06, G-01, V-01 through V-06 |
| E-02 | D | The object and context that justify ACCEPT are the ones delivered/forwarded. A message ID or mutable-buffer alias cannot substitute a different object after validation. | C-05, C-06, G-03, V-05 |
| E-03 | D | Authentication failure, malformed/truncated input, negotiation failure, IGNORE/REJECT, cancellation, and reset cannot manufacture a successful delivery or unjustified score credit. Processing an independently completed valid event is not retroactively forbidden by a later disconnect. | A-01 through A-05, N-02 through N-05, F-02, G-01, G-02, M-06, R-03, R-04 |
| E-04 | D | The resource-accounted composition respects global caps even when every layer is concurrently at its local limit. Include framing/decompression temporaries, shared buffers, timers, and deferred callbacks. | Q-06, F-02, C-01, R-01 through R-04, A-LIMITS |
| E-05 | H | A valid, admitted publication reaches a specified set of honest subscribers under explicit topology, loss/delay, cache, validation-context, and scheduling assumptions; quantify sampling failure where applicable. | G-05 through G-08, M-01 through M-03, R-05, A-TOPO, A-TIME, A-CACHE, A-VALID |
| E-06 | D | Replay and duplication at packet, RPC, object, and reconnect boundaries have the distinct effects permitted by each layer. Deduplication is retained only for its specified key/window; cryptographic authenticity does not imply freshness. | Q-03, Q-05, C-05, G-03, G-04, V-03, V-04 |
| E-07 | D | Each advertised model-level guarantee transfers only to implementations shown to refine its events/state and assumptions. Parser tests or interoperability tests alone do not establish this transfer. | A-REFINE and the implementation correspondence for every layer used by the claim |

An illustrative safety statement is:

```text
DeliverValidated(p, t, x, k)
  => exists a corresponding trace of locally authenticated receipt,
     negotiated GossipSub handling, successful bounded decode,
     and GossipAccept(t, x, k).
```

This is a proposed theorem shape, not a proved theorem. It intentionally does not
claim that `p` authored `x`, that `x` is fully consensus-valid, or that original
publisher-to-subscriber communication is confidential. Re-publication by an
honest node needs its own validated local-publication trace.

A composition argument must show that each layer's guarantees discharge the
next layer's assumptions. Individually verified components are not sufficient
when their identity, byte-stream, timing, validity, or resource abstractions differ.

## 7. Candidate proof obligations and state-exploration targets

These are method-neutral categories, not commitments to a particular tool.

### General proof candidates

- Authentication/key-binding security under named cryptographic assumptions,
  with an explicit distinction between symbolic and computational conclusions.
- Incremental parser correctness, encoding/decoding laws, context preservation,
  and validation-to-delivery object identity.
- Inductive state/ownership/resource invariants and numerical correspondence.
- Layer-contract composition yielding E-01 through E-04 and E-06.
- Implementation refinement needed for E-07; cryptographic assumptions and
  third-party components remain explicitly in the trusted boundary.

### Finite or bounded state-exploration scenarios

| Scenario | Properties primarily exercised |
| --- | --- |
| Handshake failure with already buffered data; optional replayed 0-RTT | Q-02, Q-05, A-01 through A-04, E-01, E-03 |
| Reconnect or enabled migration/key update with late stream callbacks | Q-04, A-05, N-01, R-04 |
| Negotiation rejection/truncation, with application bytes in the same read | N-02 through N-05, F-01 |
| Every fragmentation/coalescing pattern within a stated message-size bound | F-01, F-02, C-02 |
| Concurrent copies of one ID with different bytes or validation outcomes | C-05, C-06, G-03, G-04, V-04 |
| Invalid object arriving before a valid object for the same proposer/slot | M-06, V-01, V-04 |
| GRAFT/PRUNE crossing, backoff expiry, disconnect, and subscribe/unsubscribe | M-01 through M-03 |
| IHAVE/IWANT, eviction, heartbeat, and validation completion crossing | G-05, G-08, E-05 |
| Enabled IDONTWANT suppression/cancellation racing with delivery | G-07, G-08, E-05 |
| Topic-specific bad behavior compensated by rewards on other topics | M-04 through M-07 |
| Fork/clock/context transition while messages await validation | C-04, V-01, V-03 through V-05 |
| Many peers/topics saturating local limits concurrently | C-01, R-01 through R-05, E-04 |

Every exploration report must state state-space bounds, abstracted behaviors,
initial states, fairness, cache/timer abstractions, arithmetic, and covered
versions. Lossy abstraction needs a justification for the type of claim made.
Random simulations and bounded checks must not be reported as exhaustive checks
of an unbounded implementation.

## 8. Hypotheses and non-goals that must not become assumptions

- Arbitrary Byzantine membership or total packet loss precludes unconditional
  dissemination or Eclipse resistance.
- Positive scores do not imply honest behavior. M-07 needs a precise behavior,
  parameter configuration, and proof; earlier GossipSub research provides
  counterexamples for historical Ethereum settings.
- Mesh degree targets need not hold after every event, and cannot be achieved
  without enough eligible peers. Honest mesh edges need not be symmetric at
  every intermediate point.
- Finite caches do not establish permanent exactly-once delivery. An authenticated
  peer may replay a previously valid object after transport-level replay checks.
- QUIC protects adjacent connections, not the entire multi-hop gossip path from
  intermediate peers. Object signatures/proofs and transport authentication are
  different guarantees; StrictNoSign does not authenticate the original publisher.
- Fork-specific GossipSub validation is not proof of execution validity,
  availability of all required data, consensus safety, or finality.
- TCP fallback, discovery, and excluded QUIC features cannot inherit coverage
  from results for the selected QUIC-only path.

## 9. Relation to prior work and intended contribution

The ACL2s GossipSub studies [PW1, PW2] establish direct prior art: executable
models, proofs of selected scoring properties, counterexamples, and attack
synthesis. Their results are not end-to-end verification of QUIC, libp2p identity
binding, parsing/decompression, and Ethereum gossip validation in composition.
The Floodsub study [PW3] provides mechanized simulation refinement to an abstract
Broadcastsub model; it should not be characterized as unconditional all-subscriber
delivery or as a proof of existing client implementations. QUIC modeling and
model-derived testing [PW4] are additional relevant foundations, not proof that
the selected Ethereum integration is correct.

The intended contribution here is an assumption-explicit contract and composition
framework for the QUIC-to-Ethereum-GossipSub path, supported eventually by formal
results, counterexamples, and a clearly stated connection to implementations.
This is a proposed direction, not a verified result or an established priority
claim. A broader literature review is required before asserting novelty in
a paper. No verification-tool choice itself constitutes the research contribution.

## 10. Sources

Specification links below are pinned to the reference snapshots in Section 3.
Fork amendments inherit earlier networking specifications; ETH-Fulu is an example
of why topic/proof obligations cannot be instantiated from ETH0 alone.

- **QUIC**: [RFC 9000](https://www.rfc-editor.org/rfc/rfc9000) and [RFC 9001](https://www.rfc-editor.org/rfc/rfc9001).
- **TLS**: [RFC 8446](https://www.rfc-editor.org/rfc/rfc8446).
- **libp2p-QUIC**: [QUIC in libp2p](https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/quic/README.md).
- **libp2p-TLS**: [libp2p TLS Handshake](https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/tls/tls.md).
- **Connections**: [Connections and Upgrading](https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/connections/README.md).
- **MSS**: [multistream-select](https://github.com/multiformats/multistream-select/tree/9a1fbe8edadebea223f47102f1913b8026c23a1c).
- **Pubsub**: [libp2p pubsub](https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/pubsub/README.md).
- **GS10**: [GossipSub v1.0](https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/pubsub/gossipsub/gossipsub-v1.0.md).
- **GS11**: [GossipSub v1.1](https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/pubsub/gossipsub/gossipsub-v1.1.md).
- **GS12**: [GossipSub v1.2](https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/pubsub/gossipsub/gossipsub-v1.2.md).
- **GS13**: [GossipSub v1.3](https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/pubsub/gossipsub/gossipsub-v1.3.md).
- **ETH0**: [Phase 0 networking](https://github.com/ethereum/consensus-specs/blob/204fb4a19774eabb7a2e91505365deed6b8afef8/specs/phase0/p2p-interface.md).
- **ETH-Fulu**: [Fulu networking amendments](https://github.com/ethereum/consensus-specs/blob/204fb4a19774eabb7a2e91505365deed6b8afef8/specs/fulu/p2p-interface.md).
- **PW1**: Kumar et al., [Verification of GossipSub in ACL2s](https://arxiv.org/abs/2311.08859), ACL2 2023. [Artifacts](https://github.com/gossipsubfm/gossipsubfm).
- **PW2**: Kumar et al., [Formal Model-Driven Analysis of Resilience of GossipSub to Attacks from Misbehaving Peers](https://arxiv.org/abs/2212.05197), IEEE S&P 2024.
- **PW3**: Kumar and Manolios, [A Formalization of the Correctness of the Floodsub Protocol](https://arxiv.org/abs/2507.19013), ACL2 2025. [Artifacts](https://github.com/ankitku/FloodsubRef).
- **PW4**: Crochet et al., [Verifying QUIC implementations using Ivy](https://arxiv.org/abs/2503.01374), Workshop on Evolution, Performance and Interoperability of QUIC, 2021 ([DOI](https://doi.org/10.1145/3488660.3493803)). QUIC draft-29 modeling and model-derived client/server tests against seven implementations. [Artifacts](https://github.com/AnonyQUIC/QUIC-Ivy).
