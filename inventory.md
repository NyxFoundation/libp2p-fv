# Property Inventory

## Evidence status

All obligations are **proposed**, not proved or model-checked. The original 61
candidates are tracked as **53 active parent families and 8 excluded families**.
Active parents have 160 child obligations in the four linked documents. Excluded
IDs retain traceability, not coverage. The
[tool selection](docs/verification-tool-selection.md) proposes approaches for
the libp2p-related subset; no obligation is thereby established and no
implementation has been selected. A selected deployment profile and
complete per-topic/fork instantiation are required before any result; these
parameterized obligations are not that result.

## Scope

```text
Untrusted candidate address / expected Peer ID
  -> UDP / QUIC v1 + TLS 1.3 libp2p identity binding
  -> QUIC stream + multistream-select
  -> GossipSub RPC / Protobuf / routing and scoring
  -> Snappy block / SSZ / topic and fork context
  -> Ethereum gossip validation
  -> validated delivery or payload-forwarding authorization
```

This is a dependency path, not a prescribed scheduling order. ID computation,
deduplication, decompression, and validation can interleave. Local publication
has a separate validated/trusted input contract. Pubsub's inbound/outbound streams
are treated as unidirectional; QUIC unidirectional wire streams are not mandated.

**Included:** authentication, conditional crypto integrity/confidentiality,
stream/negotiation isolation, correct decoding/rejection, object/context identity,
causal control/scoring transitions, and stale-session/ownership safety.

**Excluded:** availability, delivery success/probability/deadlines, mesh recovery,
eventual attacker removal, global memory/CPU bounds, DoS/Eclipse resistance,
discovery internals, Req/Resp, TCP/Noise/Yamux/mplex, relays, full block import,
fork choice, execution validity, Engine API, OS correctness, and side channels.

Local length/type checks and stale-callback safety remain. Global boundedness is
itself a mathematical safety property but is **explicitly excluded**, not
reclassified as liveness. Exhaustion/crash behavior must be modeled or an explicit
fail-stop boundary recorded; it must not silently become successful processing.

Forwarding Peer ID, object signer, and original publisher are distinct identities.
StrictNoSign omits envelope author/signature fields, not required object signatures.
Gossip ACCEPT is not full consensus validity. QUIC protects adjacent connections,
not confidentiality from intermediate gossip peers.

## Obligation format

Hierarchy: **E2E claim -> layer contract -> child obligation -> lemma/invariant**.
IDs are stable: `A-01` is a parent, `A-01.01` a child. Every child supplies:

| Field | Meaning |
| --- | --- |
| ID | Tool-independent reference |
| Premise | Applicable input/profile/state conditions |
| Event | Transition, API result, or observable trigger |
| Required conclusion | Independently falsifiable result |
| Basis | Exact source section, normative qualification, or explicit derivation |
| Depends on | Required child/parent contracts |

**S** = specification-derived; MUST/SHOULD/MAY, recommendations, version gates,
and exceptions retain their strength. **D** = additional design/composition goal,
not a wire requirement. **K** = conditional cryptographic claim. A source is not a
proof. A bare parent dependency means all applicable children conjunctively; a
dash means no inventory dependency, not no external assumptions. Counterexample
scenarios are separate from propositions. Dependencies form a proposed proof graph.

## Active layer contracts

Open a group document and find the parent-ID heading for its child obligations
and separate counterexample scenarios.

| Detailed document | Active parent families |
| --- | --- |
| [Transport/authentication](docs/properties/transport-and-authentication.md) | Q-01, Q-02, Q-03, Q-04, Q-05, Q-06; A-01, A-02, A-03, A-04, A-05; N-01, N-02, N-03, N-04, N-05 |
| [Encoding/validation](docs/properties/encoding-and-validation.md) | F-01, F-02, F-03, F-04, F-05; C-01, C-02, C-03, C-04, C-05, C-06; V-01, V-02, V-03, V-04, V-05, V-06 |
| [GossipSub](docs/properties/gossipsub.md) | G-01, G-02, G-03, G-04, G-05, G-06, G-07; M-01, M-03, M-04, M-05, M-06, M-08 |
| [Lifecycle/E2E](docs/properties/composition.md) | R-03, R-04; E-01, E-02, E-03, E-06, E-07 |

## Excluded families

These IDs have no active children and cannot silently become theorem assumptions.

| Parent | Original subject | Reason excluded |
| --- | --- | --- |
| G-08 | GossipSub dissemination | Delivery/progress |
| M-02 | Mesh recovery | Convergence; individual transitions remain |
| M-07 | Misbehavior eventually lowers score sufficiently | Temporal attacker-removal guarantee; equations remain |
| R-01 | Global/local state resource bounds | Process-wide resource proof |
| R-02 | Prevent bypassing global admission budgets | Aggregate resource/DoS guarantee |
| R-05 | Legitimate work progresses under load | Availability |
| E-04 | Whole-stack aggregate resource cap | Global memory/CPU accounting |
| E-05 | E2E dissemination | Delivery success/probability/deadline |

## Verification profile

A proof/checking result must fix:

1. Immutable spec commits, network/genesis/fork schedule, inherited amendments,
   and every ordered validation check for each included topic.
2. GossipSub version pairs and options: explicit peers, flood publishing, PX,
   IDONTWANT, and v1.3 extensions.
3. Score/decay/activation parameters and exact comparisons; message-ID rules,
   duplicate coalescing, retention/eviction, and reconnect policies.
4. Concrete local byte/type bounds; RPC framing, Protobuf, Snappy block, SSZ,
   integer-overflow, and numerical semantics.
5. QUIC/TLS algorithms and enabled resumption/0-RTT/migration/key-update features.
   Disabled features have no coverage, not vacuous security results.
6. Clock/timer rules and async validation/cancellation linearization points.
7. Formal/implementation commits, crypto assumptions, event refinement,
   exploration bounds, trusted dependencies, and evidence class.

### Assumptions

| ID | Record explicitly |
| --- | --- |
| A-CRYPTO | Security games/bounds or symbolic models for signatures, hashes, AEAD, key exchange, BLS/KZG; randomness and inherited evidence. |
| A-KEYS | Uncompromised transport/validator keys, compromise model, forward-secrecy scope. |
| A-ADV | Packet injection/replay/loss/reordering and Byzantine peers/identities/controls. Authenticated does not mean honest. |
| A-MEMBER | Addresses/PX are untrusted; no default honest-majority, Sybil-cost, or honest-topology premise. |
| A-TIME | Monotonic timers and validation wall-clock rules; no fairness, bounded link delay, or progress premise for safety. |
| A-CACHE | Key equivalence, retention/eviction, ownership; no permanent exactly-once promise. |
| A-VALID | Selected gossip predicates, available chain context, signature/proof interfaces; not full block validity. |
| A-LIMITS | Local byte/type bounds and explicit failure/crash semantics, not aggregate capacity or availability. |
| A-REFINE | Parser/auth/arithmetic/callback/event correspondence to an implementation, to establish rather than assume wholesale. |

## Composition rule

Establish each child or identify it as an unverified/inherited assumption. Show
that lower-layer guarantees discharge upper-layer premises while preserving
peer/session, stream, protocol, topic/fork, payload, and verdict identity.

```text
DeliverValidated(p, topic, object, context)
  => a corresponding trace of local authentication, negotiated GossipSub,
     admissible decoding, and GossipAccept(topic, object, context).
```

The trace need not occur for any message. This implies neither publisher
attribution, freshness merely from signatures, delivery/availability, nor full
consensus validity. E-02 also binds the validated representation to the one used.
Crypto bounds/symbolic assumptions remain explicit. Finite/bounded exploration,
simulation, tests, inherited assumptions, and unbounded proofs are distinct evidence.

## Specification fidelity and unresolved boundaries

- **TLS:** self-signature and host-key binding signature are separate checks.
  Unknown non-critical extensions MUST be ignored. Deprecated certificate fields
  are a sender MUST-omit, receiver MAY-reject.
- **Matching:** generic libp2p permits custom predicates; Ethereum requires exact
  version equality. N-03 is profile-specific, not an invented base restriction.
- **Framing:** inspected pubsub/GS10 documents supply schemas, not a full outer
  length-prefix parser. F-01/F-02 need that contract; Req/Resp limits are not imported.
- **Optionality:** IDONTWANT can be ignored; pruning policy is implementation-defined
  and its limit has no fixed default here. v1.3 unknown extensions MUST be ignored.
- **Versions:** v1.1 changes unknown-topic GRAFT handling; do not reuse v1.0 blindly.
- **PX equality:** prose says AcceptPXThreshold "exceeds", its table says ignore
  "below". Resolve the equality case against the selected authoritative profile.
- **P3b:** narrative mentions negative-score pruning, while pseudocode only tests
  active deficit. M-04.04 requires a resolved trigger, not silent equivalence.
- **Ethereum:** Phase 0 IDs/validators are reference instances, not all later
  forks. Full per-topic/fork instantiation and codec/crypto interfaces are required.

## Source snapshots and prior work

These immutable references establish provenance, not deployed-version coverage.
Child rows reference their exact sections.

| Source | Reference |
| --- | --- |
| libp2p/specs | [`c750236de43cd8b246a824b377dfdb26bae686db`](https://github.com/libp2p/specs/tree/c750236de43cd8b246a824b377dfdb26bae686db) |
| Ethereum consensus-specs | [`204fb4a19774eabb7a2e91505365deed6b8afef8`](https://github.com/ethereum/consensus-specs/tree/204fb4a19774eabb7a2e91505365deed6b8afef8) |
| multistream-select | [`9a1fbe8edadebea223f47102f1913b8026c23a1c`](https://github.com/multiformats/multistream-select/tree/9a1fbe8edadebea223f47102f1913b8026c23a1c) |
| QUIC/TLS | [RFC 9000](https://www.rfc-editor.org/rfc/rfc9000), [RFC 9001](https://www.rfc-editor.org/rfc/rfc9001), [RFC 8446](https://www.rfc-editor.org/rfc/rfc8446) |

[README prior work](README.md#prior-work) records the ACL2s GossipSub analyses,
Floodsub refinement, and QUIC/Ivy modeling/testing. The intended contribution is
safety-contract decomposition and composition for the selected Ethereum path,
not the first formal verification of libp2p. Novelty remains to establish through
broader literature review; no proof or model-checking result is claimed.
