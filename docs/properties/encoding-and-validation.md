---
title: Encoding and Validation Properties
last_updated: 2026-11-05
tags:
  - formal-verification
  - libp2p
  - ethereum
  - security
---
# Encoding and Validation Properties

[Inventory and conventions](../../inventory.md). All obligations are **proposed**.
S = specification-derived; D = derived design obligation. Each row supplies a
premise, trigger, conclusion, clause reference, and dependencies. A bare parent
dependency means all its applicable children, not an external proof already obtained.

`P` fixes the fork, schema, topic, codec, decoder contract, and size parameters.
The Ethereum source is an application profile on libp2p, not a universal libp2p
requirement. Fork amendments inherit earlier networking specifications. V-families
are parameterized contracts: a verification result must instantiate the complete
ordered check list for each selected topic/fork, not claim that the examples here
are a complete Ethereum validation implementation.

## F-01

**Incremental framing equivalence.** The cited pubsub documents define Protobuf
RPCs but do not fully specify an outer length-prefix decoder. P must identify the
framing contract before these derived parser obligations become concrete. Do not
borrow Req/Resp varint rules or a default maximum from an unrelated protocol.

| ID | Premise | Event | Required conclusion | Basis | Depends on |
| --- | --- | --- | --- | --- | --- |
| F-01.01 | Same complete RPC byte sequence under P | Input is partitioned/coalesced differently | The sequence of decoded complete RPCs is identical. | D [RPC schema][rpc] | N-04.02 |
| F-01.02 | Same incomplete or malformed suffix | Parser reaches EOF or error | No partitioning turns that suffix into a complete valid RPC. | D [RPC schema][rpc] | — |

## F-02

**Boundary and length checks.**

| ID | Premise | Event | Required conclusion | Basis | Depends on |
| --- | --- | --- | --- | --- | --- |
| F-02.01 | P specifies the RPC length encoding and representable range | Length bytes are decoded | Overlong/out-of-range or overflowing lengths cannot wrap into an admitted smaller length. | D [RPC schema][rpc] | — |
| F-02.02 | Encoded RPC exceeds P's `max_message_size()` | Inbound/outbound RPC is considered | It is neither accepted as valid nor emitted/propagated. | S [Gossipsub size limits][eth-limits], MUST/MUST NOT | — |
| F-02.03 | EOF/reset occurs before the declared RPC completes | Parsing terminates | No complete-RPC success is emitted for the prefix. | D [RPC schema][rpc] | F-01.02 |

## F-03

**Consistent Protobuf semantics.** The source supplies proto2 schemas, not every
implementation detail of unknown/duplicate-field parsing. Decoder behavior must
be fixed in P; canonical pubsub Protobuf serialization is not assumed. This is
different from the deterministic PublicKey encoding required by the Peer ID spec.

| ID | Premise | Event | Required conclusion | Basis | Depends on |
| --- | --- | --- | --- | --- | --- |
| F-03.01 | RPC contains repeated subscriptions/messages/control entries | Parser constructs the logical RPC | Their logical values follow P's selected proto2/schema semantics without silently substituting another topic/payload. | D [RPC][rpc], [GossipSub Protobuf][gs-protobuf] | — |
| F-03.02 | Unknown or duplicate singular fields appear | Validation and use decode the RPC | Both observe the same schema-resolved value; unknown fields do not dispatch an unregistered handler. | D [RPC schema][rpc] | F-03.01 |
| F-03.03 | Required `Message.topic` or another required field is absent | Decoder finalizes the selected schema | It does not return a well-formed Message for acceptance. | S [Message schema][message] | — |

## F-04

**Signature-policy and version checks.** StrictNoSign is selected by Ethereum;
other libp2p applications may choose another policy. Present-but-empty fields are
not absent. Extension rows apply only to a profile including v1.3 semantics.

| ID | Premise | Event | Required conclusion | Basis | Depends on |
| --- | --- | --- | --- | --- | --- |
| F-04.01 | StrictNoSign is selected | Local envelope is serialized | `from`, `seqno`, `signature`, and `key` wire pairs are absent, not merely empty. | S [Signature policies][signature-policy] | — |
| F-04.02 | Any forbidden field is present, even empty | Receiver validates the envelope | The envelope is rejected and not propagated. | S [Signature policies][signature-policy] | — |
| F-04.03 | Unsigned envelope arrived from authenticated p | Authorship is interpreted | p is only the forwarding identity; object signer/original publisher is not inferred from p. | D [Message][message], [Ethereum topics][eth-topics] | A-05.01 |
| F-04.04 | v1.3 sender supports an extension | First outbound stream message is formed | Its Extensions control message is present. | S [Extensions][extensions], MUST | N-02.02 |
| F-04.05 | v1.3 sender already sent Extensions on this stream | Another message is formed | It does not send Extensions a second time. | S [Extensions][extensions], MUST NOT | — |
| F-04.06 | v1.3 receiver sees an unknown extension | Extension is processed | The unknown extension is ignored. | S [Extensions][extensions], MUST | — |

## F-05

**Envelope-to-event association.**

| ID | Premise | Event | Required conclusion | Basis | Depends on |
| --- | --- | --- | --- | --- | --- |
| F-05.01 | RPC mixes subscriptions, publications, and controls | Items are dispatched | Each event retains its sender, topic, ID, and negotiated version association. | D [RPC][rpc], [Piggybacking][piggyback] | N-02.02, F-03.01 |
| F-05.02 | Parsing/validation continues asynchronously | Deferred event consumes payload bytes | The payload is the one associated with that event, not a recycled buffer's new contents. | D [RPC schema][rpc] | F-05.01 |

## C-01

**Local encoded/decoded size admissibility.**

| ID | Premise | Event | Required conclusion | Basis | Depends on |
| --- | --- | --- | --- | --- | --- |
| C-01.01 | Compressed `Message.data` exceeds `max_compressed_len(MAX_PAYLOAD_SIZE)` | Input/output payload is admitted | It is rejected or not emitted/propagated. | S [Gossipsub size limits][eth-limits], MUST/MUST NOT | — |
| C-01.02 | Decompressed bytes exceed min(global payload bound, SSZ type bound) | Decompression/validation runs | The object cannot be accepted or propagated. | S [Gossipsub size limits][eth-limits], MUST/MUST NOT | — |
| C-01.03 | Hostile declared size or expanding Snappy block | Decoder allocates/produces bytes | Checks enforce P's local bound before committing an oversized output, including temporary and ID-computation paths. | D [Size functions][eth-sizes] | C-01.01, C-01.02 |

## C-02

**Malformed encoding cannot become a valid typed object.**

| ID | Premise | Event | Required conclusion | Basis | Depends on |
| --- | --- | --- | --- | --- | --- |
| C-02.01 | Snappy block decompression fails | Payload decoding completes | No valid SSZ object is returned from that payload. | S [Encodings][eth-encodings] | C-01 |
| C-02.02 | SSZ offsets, lengths, bounds, or trailing bytes violate the selected schema | SSZ decoding completes | No well-formed object of the expected topic type is returned. | S [Ethereum topics][eth-topics], [Encodings][eth-encodings] | — |

## C-03

**Codec correspondence lemmas.**

| ID | Premise | Event | Required conclusion | Basis | Depends on |
| --- | --- | --- | --- | --- | --- |
| C-03.01 | x is valid for P's SSZ schema | Decode its SSZ encoding | The result equals x. | D [Encodings][eth-encodings] | — |
| C-03.02 | b is a canonical SSZ encoding under that schema | Encode the decoded value | The result equals b; no canonicality is imposed on arbitrary Protobuf or Snappy bytes. | D [Encodings][eth-encodings] | C-03.01 |

## C-04

**Topic/schema/fork binding.** Fork transitions and intentional overlap windows
must be defined by P; not every cross-fork object is invalid by definition.

| ID | Premise | Event | Required conclusion | Basis | Depends on |
| --- | --- | --- | --- | --- | --- |
| C-04.01 | A message names an unknown topic | Topic validation runs | The message is rejected. | S [Ethereum topics][eth-topics], MUST | — |
| C-04.02 | Topic specifies fork, name/subnet, and encoding | Decoder/validator is chosen | It uses that profile-defined schema/context tuple without a silent fallback. | S [Ethereum topics][eth-topics] | — |
| C-04.03 | Topic and decoded object type disagree | Payload type is checked | The object fails validation. | S [Ethereum topics][eth-topics], MUST | C-04.02 |

## C-05

**Ethereum message-ID rules.** The Phase 0 rule below is a reference instance.
Later forks may amend ID inputs: P must resolve those amendments before reusing
these obligations. Valid compression does not imply a valid Ethereum object.

| ID | Premise | Event | Required conclusion | Basis | Depends on |
| --- | --- | --- | --- | --- | --- |
| C-05.01 | Phase 0 ID rule; data decompresses within admissible bounds | ID is computed | ID is SHA256(valid-Snappy domain + decompressed data) truncated to 20 bytes. | S [Ethereum topics][eth-topics], MUST | C-01 |
| C-05.02 | Phase 0 ID rule; Snappy decompression fails | ID is computed | ID uses the invalid-Snappy domain and raw data, truncated to 20 bytes; that ID does not authorize acceptance. | S [Ethereum topics][eth-topics], MUST | — |
| C-05.03 | A context requires received message IDs | ID length is validated | An ID with size other than 20 bytes is rejected where prescribed. | S [Ethereum topics][eth-topics], MUST | — |
| C-05.04 | P adds topic/fork-specific ID inputs | ID is computed or looked up | All uses apply P's amended rule, not a mixture of Phase 0 and later rules. | D [Ethereum topics][eth-topics], [Fork amendments][fulu] | C-04.02 |

## C-06

**Validation-to-use immutability.**

| ID | Premise | Event | Required conclusion | Basis | Depends on |
| --- | --- | --- | --- | --- | --- |
| C-06.01 | Validator approved x in context k | Application receives the result | Delivered object/context equals x/k or a proven schema-equivalent encoding. | D [Topic validation][topic-validation] | F-05.02, V-01 |
| C-06.02 | A buffer/cache entry changes while validation is pending | Completion authorizes forwarding | The authorization still refers to the validated object, never replacement bytes with the same lookup key. | D [Topic validation][topic-validation] | C-06.01 |

## V-01

**Ordered verdict semantics.**

| ID | Premise | Event | Required conclusion | Basis | Depends on |
| --- | --- | --- | --- | --- | --- |
| V-01.01 | A check is reached and fails | Validator chooses a verdict | It returns the specified REJECT or IGNORE for that check. | S [Ethereum topics][eth-topics] | C-04.02 |
| V-01.02 | All applicable ordered checks succeed | Validator completes | Its verdict is ACCEPT for that object/context. | S [Ethereum topics][eth-topics] | V-01.01 |
| V-01.03 | Implementation reorders/parallelizes checks | Observable verdict/state effects are compared | They refine the ordered specification, including which failure wins. | D [Ethereum topics][eth-topics] | V-01.01, V-01.02 |

## V-02

**Object-level authentication.**

| ID | Premise | Event | Required conclusion | Basis | Depends on |
| --- | --- | --- | --- | --- | --- |
| V-02.01 | Required BLS check is reached | Signature/aggregate is verified | Verification uses the prescribed object, signing domain, keys, and membership context; failure cannot lead to ACCEPT. | S [Ethereum topics][eth-topics] | C-04.02, V-01.01 |
| V-02.02 | Selected Fulu data-column KZG check is reached | Cell proof batch is verified | Commitments, column index, cells, and proofs have the specified correspondence; failure cannot lead to ACCEPT. | S [KZG helper][fulu-kzg] | V-01.01 |
| V-02.03 | Required inclusion check is reached | Merkle branch is verified | Leaf, index, depth, and root come from the specified object/context; failure cannot lead to ACCEPT. | S [Inclusion helper][fulu-inclusion] | V-01.01 |

## V-03

**Topic-specific contextual checks.**

| ID | Premise | Event | Required conclusion | Basis | Depends on |
| --- | --- | --- | --- | --- | --- |
| V-03.01 | Topic requires a slot/epoch/time-window check | That check executes | The exact selected boundaries and verdict are used, including allowed clock disparity. | S [Ethereum topics][eth-topics] | V-01.01 |
| V-03.02 | Topic requires proposer/committee/subnet/duplicate eligibility | That check executes | Eligibility is tested against the correct topic and chain context, not the forwarding Peer ID. | S [Ethereum topics][eth-topics] | C-04.02, V-01.01 |
| V-03.03 | Selected Fulu sidecar has index at least NUMBER_OF_COLUMNS | Structural helper checks the index | It returns false. | S [Sidecar helper][fulu-structure] | C-04.02 |
| V-03.04 | Selected Fulu sidecar has no commitments | Structural helper checks the count | It returns false. | S [Sidecar helper][fulu-structure] | C-04.02 |
| V-03.05 | Selected Fulu sidecar exceeds its epoch's blob limit | Structural helper checks the count | It returns false. | S [Sidecar helper][fulu-structure] | C-04.02 |
| V-03.06 | Selected Fulu column and commitment counts differ | Structural helper checks their lengths | It returns false. | S [Sidecar helper][fulu-structure] | C-04.02 |
| V-03.07 | Selected Fulu column and proof counts differ | Structural helper checks their lengths | It returns false. | S [Sidecar helper][fulu-structure] | C-04.02 |

## V-04

**Unknown context and seen-state poisoning.**

| ID | Premise | Event | Required conclusion | Basis | Depends on |
| --- | --- | --- | --- | --- | --- |
| V-04.01 | Required chain context is unavailable | Its ordered check is reached | The specified unknown-context verdict is used, not an invented signature-failure verdict. | S [Ethereum topics][eth-topics] | V-01.01 |
| V-04.02 | Invalid object arrives before a valid object sharing a topic-specific seen key | Seen state is mutated | Mutation occurs only at the specification's permitted point, so the invalid object cannot claim a successful-validation key prematurely. | D [Ethereum validation][eth-topics] | V-01.03 |

## V-05

**Asynchronous context stability.**

| ID | Premise | Event | Required conclusion | Basis | Depends on |
| --- | --- | --- | --- | --- | --- |
| V-05.01 | Clock/fork/chain context changes during validation | Result is committed | The result names a specified context snapshot, or is revalidated under P's rule. | D [Ethereum validation][eth-topics] | V-01.03 |
| V-05.02 | Pending result was for an incompatible topic/fork context | Delivery/forwarding is requested | The old ACCEPT is not reused as approval for the new context. | D [Ethereum topics][eth-topics] | V-05.01, C-04.02 |

## V-06

**Do not overstate ACCEPT.**

| ID | Premise | Event | Required conclusion | Basis | Depends on |
| --- | --- | --- | --- | --- | --- |
| V-06.01 | Gossip validator returns ACCEPT | Validated event is labeled | The claim is only P's gossip predicate, not full block/execution validity or finality. | D [Ethereum gossip validation][eth-topics] | V-01 |
| V-06.02 | No validator signature/publication-author proof was established | Application interprets receipt | It does not infer that the transport peer authored the Ethereum object. | D [Message authorship][message] | F-04.03 |

## Counterexample scenarios

- Split a frame at every boundary, join multiple frames in one read, and terminate
  before completion. Wrong parse outcomes must be separate from network delay.
- Forbidden envelope field absent versus present with zero-length bytes.
- Oversized compressed data, valid expansion exceeding the type bound, and
  malformed Snappy taking the invalid-domain ID branch without becoming valid.
- Different compressed encodings of the same object; same bytes on different
  topics/forks; old ID rule used after a fork amendment.
- Invalid object first for a proposer/slot; missing parent; future slot; a context
  change between signature verification and seen-state update.

[rpc]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/pubsub/README.md#the-rpc
[message]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/pubsub/README.md#the-message
[signature-policy]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/pubsub/README.md#signature-policy-options
[topic-validation]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/pubsub/README.md#topic-validation
[gs-protobuf]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/pubsub/gossipsub/gossipsub-v1.0.md#protobuf
[piggyback]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/pubsub/gossipsub/gossipsub-v1.0.md#control-message-piggybacking
[extensions]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/pubsub/gossipsub/gossipsub-v1.3.md#the-extensions-control-message
[eth-topics]: https://github.com/ethereum/consensus-specs/blob/204fb4a19774eabb7a2e91505365deed6b8afef8/specs/phase0/p2p-interface.md#topics-and-messages
[eth-encodings]: https://github.com/ethereum/consensus-specs/blob/204fb4a19774eabb7a2e91505365deed6b8afef8/specs/phase0/p2p-interface.md#encodings
[eth-sizes]: https://github.com/ethereum/consensus-specs/blob/204fb4a19774eabb7a2e91505365deed6b8afef8/specs/phase0/p2p-interface.md#maximum-message-sizes
[eth-limits]: https://github.com/ethereum/consensus-specs/blob/204fb4a19774eabb7a2e91505365deed6b8afef8/specs/phase0/p2p-interface.md#gossipsub-size-limits
[fulu]: https://github.com/ethereum/consensus-specs/blob/204fb4a19774eabb7a2e91505365deed6b8afef8/specs/fulu/p2p-interface.md#the-gossip-domain-gossipsub
[fulu-kzg]: https://github.com/ethereum/consensus-specs/blob/204fb4a19774eabb7a2e91505365deed6b8afef8/specs/fulu/p2p-interface.md#new-verify_data_column_sidecar_kzg_proofs
[fulu-inclusion]: https://github.com/ethereum/consensus-specs/blob/204fb4a19774eabb7a2e91505365deed6b8afef8/specs/fulu/p2p-interface.md#new-verify_data_column_sidecar_inclusion_proof
[fulu-structure]: https://github.com/ethereum/consensus-specs/blob/204fb4a19774eabb7a2e91505365deed6b8afef8/specs/fulu/p2p-interface.md#new-verify_data_column_sidecar
