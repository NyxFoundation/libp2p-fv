---
title: Transport and Authentication Properties
last_updated: 2026-11-05
tags:
  - formal-verification
  - libp2p
  - security
  - quic
---
# Transport and Authentication Properties

[Inventory and conventions](../../inventory.md). All obligations are **proposed**.
S means specification-derived, D a derived design obligation, and K a conditional
cryptographic claim. Source references name exact sections, not proof artifacts.
A bare parent ID in dependencies means all its applicable children. A dash means
no inventory dependency, not that external assumptions disappear.

`P` is the selected profile; `s` is a local session generation. Authentication is
local: a client finishing TLS does not imply the server has verified that client.
QUIC security properties below require a QUIC/TLS contract or proof; they are not
a claim to have re-proved the complete RFCs. Disabled features have no coverage.

## Q-01

**Application-traffic confidentiality and integrity.** Assumptions: A-CRYPTO,
A-KEYS, selected algorithms and key-usage bounds. Initial packets and exposed
metadata are not covered by the confidentiality claim.

| ID | Premise | Event | Required conclusion | Basis | Depends on |
| --- | --- | --- | --- | --- | --- |
| Q-01.01 | Uncompromised application keys; P's security game | Adversary observes protected traffic | Plaintext distinguishing advantage satisfies the stated computational bound, or the explicitly chosen symbolic secrecy predicate. | K [Packet protection][packet] | — |
| Q-01.02 | Same key/algorithm assumptions | Receiver accepts protected application bytes | Forged-content acceptance satisfies P's integrity bound; ciphertext validity alone does not authenticate a libp2p Peer ID. | K [AEAD][aead] | — |

## Q-02

**Authentication barrier.**

| ID | Premise | Event | Required conclusion | Basis | Depends on |
| --- | --- | --- | --- | --- | --- |
| Q-02.01 | Local required peer checks have not succeeded | Application dispatch attempts to read buffered bytes | No event labels those bytes as belonging to an authenticated libp2p peer. | D [TLS peer authentication][tls-peer] | — |
| Q-02.02 | Server certificate verification fails after client Finished | Server processes connection result | Client-sent application data is not processed as authenticated data. | S [TLS peer authentication][tls-peer] | A-01, A-02 |

## Q-03

**Replay, ordering, and stream isolation.** Assumption: Q-01's protected transport
contract. Prefix correspondence assumes a well-defined conforming sender byte
stream; a Byzantine peer can send arbitrary content, which still needs application
validation. This states what accepted bytes mean, not that any bytes arrive.

| ID | Premise | Event | Required conclusion | Basis | Depends on |
| --- | --- | --- | --- | --- | --- |
| Q-03.01 | A conforming sender's protected stream has accepted offsets | Duplicate/reordered STREAM data is processed | Delivered bytes are a single ordered prefix of that stream's sent bytes, without duplicated offsets. | S [Stream ordering][stream-order] | Q-01.02 |
| Q-03.02 | Different stream IDs or session generations | Packet loss, reset, or retransmission occurs | A partial prefix is never completed using bytes from another stream/session. | D [Streams][streams] | Q-03.01 |

## Q-04

**Identity preservation across transport changes.**

| ID | Premise | Event | Required conclusion | Basis | Depends on |
| --- | --- | --- | --- | --- | --- |
| Q-04.01 | Authenticated s; migration/CID rotation enabled | Accepted path or connection ID changes | The associated Peer ID remains s's authenticated Peer ID. | D [Migration][migration] | A-05.01 |
| Q-04.02 | Key update, resumption, or reconnection enabled | Transport installs new keys or creates a new session | Key changes do not silently transfer another session's authentication result. | D [Key update][key-update], [Resumption][resumption] | A-05.01, R-04 |

## Q-05

**Early-data replay policy.** P must choose a reject/quarantine/replay-safe policy
before this family can be verified. A read-only operation is not automatically
replay-safe; no application state transition is assumed safe by default.

| ID | Premise | Event | Required conclusion | Basis | Depends on |
| --- | --- | --- | --- | --- | --- |
| Q-05.01 | P disables early application data | 0-RTT application bytes arrive | They produce no GossipSub/application effect. | D [0-RTT replay][early-replay] | — |
| Q-05.02 | P enables early data with an enumerated effect policy | An early-data effect is requested | The effect is authorized only by that policy and the local authentication barrier, without assuming 1-RTT freshness. | D [0-RTT replay][early-replay] | Q-02.01 |

## Q-06

**Protocol admission and closure rules.**

| ID | Premise | Event | Required conclusion | Basis | Depends on |
| --- | --- | --- | --- | --- | --- |
| Q-06.01 | Advertised stream/connection flow-control credit | STREAM data is admitted | Offsets beyond the selected RFC credit are handled as a violation, not valid admitted bytes. | S [Flow control][flow] | — |
| Q-06.02 | Peer-advertised stream count limit | Local endpoint opens a stream | The stream identifier respects the permitted stream count. | S [Stream limits][stream-limits] | — |
| Q-06.03 | A session enters its terminal application state | Deferred application work completes | No new session-scoped authenticated event is created by that completion. | D [Lifecycle events][lifecycle] | R-04.01 |

## A-01

**Certificate checks.** Preconditions: the certificate chain and receiver's
validation time are fixed for this check. Each rejection is an independent
negative obligation; acceptance requires the applicable checks conjunctively.

| ID | Premise | Event | Required conclusion | Basis | Depends on |
| --- | --- | --- | --- | --- | --- |
| A-01.01 | Chain contains more than one certificate | Receiver checks chain | Connection attempt aborts. | S [TLS peer authentication][tls-peer], MUST | — |
| A-01.02 | Certificate is not yet valid | Receiver checks NotBefore | Connection attempt aborts. | S [TLS peer authentication][tls-peer], MUST | — |
| A-01.03 | Certificate is expired | Receiver checks NotAfter | Connection attempt aborts. | S [TLS peer authentication][tls-peer], MUST | — |
| A-01.04 | Certificate self-signature is invalid | Receiver verifies self-signature | Connection attempt aborts. | S [TLS peer authentication][tls-peer], MUST | — |
| A-01.05 | Required libp2p public-key extension is absent | Receiver checks extensions | Connection attempt aborts. | S [TLS peer authentication][tls-peer], MUST | — |
| A-01.06 | A critical extension has an unknown OID | Receiver checks extensions | Connection attempt aborts. | S [TLS peer authentication][tls-peer], MUST | — |
| A-01.07 | A non-critical extension has an unknown OID | Receiver checks that extension | The unknown extension is ignored, not made a new mandatory rejection. | S [TLS peer authentication][tls-peer], MUST | — |
| A-01.08 | Local endpoint constructs a certificate | Certificate is serialized | Deprecated subjectUniqueId/issuerUniqueId fields are omitted; receiving them permits, but does not require, rejection. | S [TLS peer authentication][tls-peer], MUST/MAY | — |

## A-02

**Certificate-to-identity-key binding.**

| ID | Premise | Event | Required conclusion | Basis | Depends on |
| --- | --- | --- | --- | --- | --- |
| A-02.01 | Sender prepares the host-key signature | Signed input is constructed | Input is exactly `libp2p-tls-handshake:` followed by the certificate key's prescribed SubjectPublicKeyInfo encoding. | S [Public-key extension][tls-extension] | — |
| A-02.02 | Receiver decodes SignedKey | Host key is extracted | ASN.1 SignedKey and embedded PublicKey Type/Data use the prescribed key encoding; malformed data cannot yield an authenticated key. | S [Public-key extension][tls-extension], [Keys][peer-keys] | — |
| A-02.03 | Host-key signature fails for the certificate's actual key | Receiver verifies the extension | Connection attempt aborts; another certificate key's valid signature cannot substitute. | S [Public-key extension][tls-extension], MUST | A-02.01, A-02.02 |

## A-03

**Peer ID derivation and expected-peer matching.**

| ID | Premise | Event | Required conclusion | Basis | Depends on |
| --- | --- | --- | --- | --- | --- |
| A-03.01 | Authenticated host public key is available | Peer ID is derived | Deterministic key serialization uses identity multihash at at most 42 bytes and SHA256 multihash above 42 bytes. | S [Peer IDs][peer-ids], [Keys][peer-keys] | A-02.02, A-02.03 |
| A-03.02 | Dialer supplied an expected Peer ID | Derived identity is compared | Mismatch aborts the connection attempt. | S [Public-key extension][tls-extension], MUST | A-03.01 |

## A-04

**Handshake profile and mutual authentication.**

| ID | Premise | Event | Required conclusion | Basis | Depends on |
| --- | --- | --- | --- | --- | --- |
| A-04.01 | QUIC v1 is selected | TLS version is negotiated | QUIC uses its TLS 1.3 integration; no older TLS version establishes this session. | S [TLS version][tls-version], [Handshake][tls-handshake] | — |
| A-04.02 | Local endpoint is server | Client authentication is requested/checked | Missing requested client authentication aborts the attempt. | S [Handshake][tls-handshake], MUST | — |
| A-04.03 | ALPN is negotiated for libp2p QUIC | Handshake succeeds | The agreed application protocol is `libp2p`; no common supported ALPN means handshake failure. | S [QUIC ALPN][quic-alpn] | — |

## A-05

**Identity and state lifetime.**

| ID | Premise | Event | Required conclusion | Basis | Depends on |
| --- | --- | --- | --- | --- | --- |
| A-05.01 | All applicable local authentication checks succeeded for p | Authenticated session s is installed | Every later authenticated event attributed to s names p, never an address- or metadata-substituted identity. | D [TLS identity][tls-extension] | A-01, A-02, A-03, A-04 |
| A-05.02 | P defines peer-wide retained score and session-local state | Disconnect/reconnect occurs | Retained state is keyed to the authenticated peer under P; old session callbacks do not acquire the new session's authority. | D [Peer scoring][scoring] | A-05.01, R-04 |

## N-01

**Stream identity, direction, and ordering.** Pubsub uses separately negotiated
inbound and outbound streams treated as unidirectional at the pubsub interface.
This is not a requirement to use QUIC's unidirectional wire stream type.

| ID | Premise | Event | Required conclusion | Basis | Depends on |
| --- | --- | --- | --- | --- | --- |
| N-01.01 | Stream belongs to authenticated s | Read completes | The returned prefix belongs to that stream and session generation. | D [Streams][streams] | Q-03, A-05.01 |
| N-01.02 | A stream is half-closed or reset | Another stream/session receives data | Its bytes cannot complete the terminated stream's pending message. | D [Streams][streams] | N-01.01 |
| N-01.03 | P follows the pubsub directional-stream arrangement | Pubsub reads/writes data | Only the inbound stream supplies reads and only the outbound stream supplies writes. | S [Stream management][pubsub-streams], prose recommendation | N-02 |

## N-02

**Negotiation-to-handler binding.**

| ID | Premise | Event | Required conclusion | Basis | Depends on |
| --- | --- | --- | --- | --- | --- |
| N-02.01 | Incoming stream has no successful protocol selection | GossipSub dispatch is attempted | The stream is not delivered to a GossipSub handler as negotiated. | D [Opening streams][opening], [MSS protocol][mss] | — |
| N-02.02 | Proposal was successfully acknowledged | Handler is dispatched | Its protocol ID/version is the one acknowledged on this stream. | S [Opening streams][opening], [MSS protocol][mss] | N-01.01 |

## N-03

**Ethereum's exact protocol matching.** Generic libp2p permits custom match
predicates; exact equality here is an Ethereum-profile obligation, not a universal
restriction on all libp2p applications.

| ID | Premise | Event | Required conclusion | Basis | Depends on |
| --- | --- | --- | --- | --- | --- |
| N-03.01 | Ethereum profile; remote proposes an ID | Supported versions are compared | Acceptance uses exact equality, not substring/prefix compatibility. | S [Ethereum protocol negotiation][eth-negotiation], MUST | — |
| N-03.02 | No supported handler matches the proposal | Responder handles selection | It responds `na`, without selecting a different handler implicitly. | S [Opening streams][opening], [MSS protocol][mss] | N-03.01 |

## N-04

**Negotiation framing and handoff.**

| ID | Premise | Event | Required conclusion | Basis | Depends on |
| --- | --- | --- | --- | --- | --- |
| N-04.01 | A multistream message is encoded/parsed | Its boundary is determined | The varint length includes the terminating newline. | S [MSS protocol][mss], notes 1-2 | — |
| N-04.02 | Final negotiation and payload bytes share a read | Handler receives remaining bytes | Exactly the negotiation prefix is consumed; the payload suffix is unchanged. | D [MSS protocol][mss] | N-04.01, N-02.02 |

## N-05

**Negotiation failure cannot manufacture success.** Rejecting one proposal does
not necessarily terminate negotiation: a supported alternative can still be proposed.

| ID | Premise | Event | Required conclusion | Basis | Depends on |
| --- | --- | --- | --- | --- | --- |
| N-05.01 | Truncated selection, reset, or policy timeout | Negotiation terminates without agreement | No successful selection event is emitted. | D [MSS protocol][mss] | N-02.01 |
| N-05.02 | Negotiation/session is terminal | A stale completion callback fires | It cannot install a negotiated handler in that session or its replacement. | D [Lifecycle events][lifecycle] | R-04.01 |

## Counterexample scenarios

These are tests of obligations, not additional normative rules:

- Invalid self-signature with a valid identity-key signature; A-01.04 still fails.
- Valid signature over a different SPKI/domain prefix; A-02.03 must fail.
- Exactly 42 versus 43 serialized key bytes; A-03.01 selects different codecs.
- Empty client authentication, expired certificate, unknown critical extension,
  and unknown non-critical extension exercise distinct verdicts.
- Client Finished followed by application bytes while server verification fails.
- Wrong ALPN, prefix-only protocol match, batched MSS/payload, concurrent streams,
  and callbacks completing after reconnect.

[packet]: https://www.rfc-editor.org/rfc/rfc9001#section-5
[aead]: https://www.rfc-editor.org/rfc/rfc9001#section-5.3
[stream-order]: https://www.rfc-editor.org/rfc/rfc9000#section-2.2
[migration]: https://www.rfc-editor.org/rfc/rfc9000#section-9
[key-update]: https://www.rfc-editor.org/rfc/rfc9001#section-6
[resumption]: https://www.rfc-editor.org/rfc/rfc9001#section-4.5
[early-replay]: https://www.rfc-editor.org/rfc/rfc9001#section-9.2
[flow]: https://www.rfc-editor.org/rfc/rfc9000#section-4.1
[stream-limits]: https://www.rfc-editor.org/rfc/rfc9000#section-4.6
[tls-version]: https://www.rfc-editor.org/rfc/rfc9001#section-4.2
[tls-handshake]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/tls/tls.md#handshake-protocol
[tls-peer]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/tls/tls.md#peer-authentication
[tls-extension]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/tls/tls.md#libp2p-public-key-extension
[quic-alpn]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/quic/README.md#alpn
[streams]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/connections/README.md#definitions
[opening]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/connections/README.md#opening-new-streams-over-a-connection
[lifecycle]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/connections/README.md#connection-lifecycle-events
[peer-keys]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/peer-ids/peer-ids.md#keys
[peer-ids]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/peer-ids/peer-ids.md#peer-ids
[scoring]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/pubsub/gossipsub/gossipsub-v1.1.md#peer-scoring
[mss]: https://github.com/multiformats/multistream-select/blob/9a1fbe8edadebea223f47102f1913b8026c23a1c/README.md#protocol
[pubsub-streams]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/pubsub/README.md#stream-management
[eth-negotiation]: https://github.com/ethereum/consensus-specs/blob/204fb4a19774eabb7a2e91505365deed6b8afef8/specs/phase0/p2p-interface.md#protocol-negotiation
