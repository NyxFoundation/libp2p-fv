---
title: GossipSub Safety Properties
last_updated: 2026-11-05
tags:
  - formal-verification
  - libp2p
  - gossipsub
  - security
---
# GossipSub Safety Properties

[Inventory and conventions](../../inventory.md). All obligations are **proposed**.
S = specification-derived; D = derived safety/design obligation. `P` selects the
version, signature policy, score parameters, optional features, and peer-state
policies. A parent dependency means all applicable children. No row establishes
delivery, mesh recovery, eventual pruning, or service under attack.

v1.1 amends v1.0: unknown-topic GRAFT is ignored rather than always answered with
PRUNE; explicit peers are outside the mesh. v1.2 IDONTWANT is optional even for a
receiver. v1.3 extension advertisements are descriptions, not a new mandatory
negotiation round. These distinctions must survive formalization.

## G-01

**Validation gates remote-object acceptance and forwarding.**

| ID | Premise | Event | Required conclusion | Basis | Depends on |
| --- | --- | --- | --- | --- | --- |
| G-01.01 | A remote object has not completed all required validators | Validated application delivery is attempted | No validated delivery event is emitted. | S [Topic validation][validators], [Extended validators][extended] | — |
| G-01.02 | The same remote object lacks ACCEPT | Payload forwarding is attempted | It is not forwarded as valid, including to explicit peers. | S [Topic validation][validators], [Explicit peers][explicit] | — |
| G-01.03 | Application returned ACCEPT for object/context x/k | Routing is authorized | The authorization attaches to x/k, not merely a reused ID or another validation task. | D [Extended validators][extended] | C-06, V-01 |

## G-02

**IGNORE and REJECT remain distinct.**

| ID | Premise | Event | Required conclusion | Basis | Depends on |
| --- | --- | --- | --- | --- | --- |
| G-02.01 | Verdict is IGNORE | Result is applied | No P4 invalid-delivery increment is caused by that verdict. | S [Extended validators][extended] | V-01.01 |
| G-02.02 | Verdict is REJECT for a received object | Result is applied | The selected invalid-message rejection/P4 behavior applies to the corresponding sender/topic, not another peer. | S [Extended validators][extended] | F-05.01 |

## G-03

**Concurrent duplicate-validation policy.** P must choose and describe coalescing
and ownership rules; the spec does not prescribe a universal first-valid-wins
implementation algorithm.

| ID | Premise | Event | Required conclusion | Basis | Depends on |
| --- | --- | --- | --- | --- | --- |
| G-03.01 | Concurrent candidates share a lookup ID | Work is merged or one candidate is selected | The selected candidate's bytes/context and contributing sender records are retained without substitution. | D [Message identification][ids], [Validation][validators] | F-05.01, C-05 |
| G-03.02 | One candidate's validation completes | Waiting duplicate tasks are completed | No different object/context inherits that candidate's ACCEPT. | D [Validation][validators] | G-03.01, C-06 |

## G-04

**Scoped duplicate suppression.** The key and retention/eviction interval are
explicit in P. Permanent exactly-once delivery is not claimed.

| ID | Premise | Event | Required conclusion | Basis | Depends on |
| --- | --- | --- | --- | --- | --- |
| G-04.01 | A deduplication key remains in the specified suppression interval | Another accepted copy arrives | No second validated application event for that key is emitted under P's at-most-once policy. | D [Message cache][cache] | C-05, G-03 |
| G-04.02 | Suppression entry expires or is evicted under P | Old bytes reappear | A new processing decision is not mislabeled as a violation of permanent exactly-once delivery; all current validation gates still apply. | D [Message cache][cache] | G-01, V-03 |

## G-05

**IHAVE/IWANT and cached-message correspondence.**

| ID | Premise | Event | Required conclusion | Basis | Depends on |
| --- | --- | --- | --- | --- | --- |
| G-05.01 | IHAVE names an ID already in seen state | Router considers requesting it | That advertisement does not cause an IWANT for the already-seen ID. | S [Message processing][processing] | C-05 |
| G-05.02 | IWANT names an ID with a cached message | Router responds under its selected retransmission policy | The response is the cached message for that ID, not another cache entry. | S [Message processing][processing], [Spam rules][spam] | C-05 |
| G-05.03 | Cache query names topic t and a selected history window | Gossip IDs are emitted | IDs correspond to messages in t and that window, not another topic/window. | S [Message cache][cache] | C-04.02 |
| G-05.04 | A probabilistically tracked IHAVE promise is assessed | Its timeout penalty decision runs | P7 attribution follows the tracked advertiser/ID and does not punish non-delivery when the message arrived from any peer within the required interval. | S [Spam protection][spam] | C-05, M-06.01 |

## G-06

**Forwarding eligibility and local-publication assumptions.**

| ID | Premise | Event | Required conclusion | Basis | Depends on |
| --- | --- | --- | --- | --- | --- |
| G-06.01 | A valid new remote message is eligible to forward | Recipient set is selected | P's mesh/floodsub/explicit-peer eligibility is used without treating a locally published message as the same routing case. | S [Message processing][processing], [Explicit peers][explicit] | G-01.03 |
| G-06.02 | P enables flood publishing, or uses the fanout alternative | Local message recipient set is selected | Flood-publish score/subscription conditions or the selected fanout conditions apply, respectively. | S [Flood publishing][flood], [Message processing][processing] | — |
| G-06.03 | Local input is not an already trusted valid publication | Local publication is authorized | P's local validation/input contract is satisfied before it is forwarded as valid. | D [Topic validation][validators] | C-01, C-04, V-01 |
| G-06.04 | P identifies a received object as a locally published message | Router considers forwarding that echo | It does not forward the self-published echo again under the message-processing rule. | S [Message processing][processing] | C-05 |

## G-07

**Optional IDONTWANT semantics.** Receiver choice to honor, ignore, or send the
control is explicit. No universal suppression TTL is supplied by the source.

| ID | Premise | Event | Required conclusion | Basis | Depends on |
| --- | --- | --- | --- | --- | --- |
| G-07.01 | P honors IDONTWANT from p for ID i | Mesh forwarding of i is considered | p is skipped as specified; another peer's suppression set is not mutated. | S [IDONTWANT][idontwant], conditional MUST | C-05 |
| G-07.02 | Peer sends a message after receiving IDONTWANT | Router considers a penalty for that fact alone | No penalty is imposed merely for ignoring the optional control. | S [IDONTWANT][idontwant] | — |
| G-07.03 | P supplies suppression-aging/reconnect policy | Entry is expired or a session is replaced | Old suppression authority does not leak beyond P's defined peer/context lifetime. | D [IDONTWANT][idontwant], aging policy explicitly implementation-defined | R-04 |
| G-07.04 | Received IDONTWANT count exceeds a local limit | Router considers the extension's limit-based penalty | Such downscoring requires the limit to be agreed across the network; disagreement alone does not justify punishment. | S [IDONTWANT][idontwant], SHOULD qualification | — |

## M-01

**Membership-control safety, not mesh convergence.**

| ID | Premise | Event | Required conclusion | Basis | Depends on |
| --- | --- | --- | --- | --- | --- |
| M-01.01 | v1.1+; GRAFT names an unknown topic | Router processes GRAFT | It ignores the unknown-topic GRAFT rather than applying v1.0's unconditional PRUNE response. | S [Spam protection][spam] | — |
| M-01.02 | GRAFT sender is an explicit peer | Router processes GRAFT | It rejects with PRUNE rather than adding the explicit peer to the mesh. | S [Explicit peering][explicit] | — |
| M-01.03 | PRUNE is received for an existing topic link | Router updates membership | The sending peer is removed from that topic mesh and applicable backoff is recorded. | S [Message processing][processing], [Backoff][backoff] | — |
| M-01.04 | GRAFT arrives within the active backoff interval | Router processes GRAFT | It is pruned and the backoff extended under the selected rules. | S [Backoff][backoff] | — |
| M-01.05 | Application JOINs topic t | Fanout is promoted/mesh initialized | Membership is selected for t without importing another topic's fanout peers as t members. | S [Topic membership][membership] | C-04.02 |
| M-01.06 | Application LEAVEs topic t | Mesh state is deleted | Removal and PRUNE target t's mesh, not an unrelated topic. | S [Topic membership][membership] | — |

## M-03

**Selection constraints.**

| ID | Premise | Event | Required conclusion | Basis | Depends on |
| --- | --- | --- | --- | --- | --- |
| M-03.01 | Outbound mesh quotas are selected | Configuration is admitted | D_out is below D_low and at most D/2 as specified. | S [Outbound quotas][quotas] | — |
| M-03.02 | Mesh is at D_high or above | Incoming GRAFT is considered | An inbound connection is not accepted by the outbound-only oversubscription exception. | S [Outbound quotas][quotas] | M-03.01 |
| M-03.03 | Oversubscription pruning runs with eligible survivors | Survivor set is chosen | The specified score/random selection respects D_out rather than discarding that constraint. | S [Heartbeat maintenance][maintenance] | M-03.01, M-04 |
| M-03.04 | Selected opportunistic-graft branch runs | New peers are chosen | Their scores satisfy the specified above-median selection predicate. | S [Opportunistic grafting][opportunistic] | M-04 |

## M-04

**Score equations and state updates.**

| ID | Premise | Event | Required conclusion | Basis | Depends on |
| --- | --- | --- | --- | --- | --- |
| M-04.01 | Mesh entry time, quantum and cap are defined | P1 is computed | Time-in-mesh division and cap follow the specified equation. | S [Topic parameters][topic-params] | — |
| M-04.02 | A valid first delivery is credited | P2 counter is updated | Increment and configured cap follow the prescribed update. | S [Topic parameters][topic-params] | G-01.03 |
| M-04.03 | P3 is evaluated | Activation/deficit are computed | It is zero when mesh time is at most activation or deliveries meet/exceed threshold, and the squared deficit otherwise. | S [Topic parameters][topic-params] | — |
| M-04.04 | A prune satisfies P's resolved P3b trigger | P3b is updated | The specified squared deficit is added only for that trigger, not every prune. | S [Topic parameters][topic-params], trigger ambiguity noted below | M-04.03 |
| M-04.05 | Invalid-delivery counter n is selected | P4 is computed | The contribution parameter is n squared, with its configured negative weight applied by the score equation. | S [Score function][score] | G-02.02 |
| M-04.06 | All configured topic/global parameters are fixed | Total score is computed | Topic weighting/cap and global P5/P6/P7 contributions follow the selected equation; unconfigured topics do not contribute. | S [Score function][score], [Parameters][params] | — |
| M-04.07 | IP-colocation count/threshold are fixed | P6 is computed | It is zero at or below threshold and the squared surplus above it. | S [Score function][score] | — |
| M-04.08 | Behavioral counter n is selected | P7 is computed | The parameter is n squared, mixed with its specified negative weight. | S [Score function][score] | — |
| M-04.09 | A decay update is scheduled under P | A selected counter decays | Its own factor and DecayToZero rule apply, not another counter's parameters. | S [Topic parameters][topic-params], [Parameters][params] | — |
| M-04.10 | Peer disconnects and reconnects within retained-score lifetime | Peer-wide score is restored | P's RetainScore semantics preserve the correct peer's history, not a different identity's score. | S [Peer scoring][peer-scoring], [Parameters][params] | A-05.02 |

## M-05

**Numerical correspondence.**

| ID | Premise | Event | Required conclusion | Basis | Depends on |
| --- | --- | --- | --- | --- | --- |
| M-05.01 | P fixes finite-precision arithmetic and legal parameter ranges | Score/decay arithmetic executes | No NaN, infinity, wraparound, or exceptional value silently becomes a valid score decision. | D [Score function][score] | — |
| M-05.02 | P defines the numerical reference and permitted rounding | A threshold comparison controls routing | Implementation comparison refines that reference; equality/rounding cases are explicit. | D [Thresholds][thresholds] | M-05.01 |

## M-06

**Causal scoring.**

| ID | Premise | Event | Required conclusion | Basis | Depends on |
| --- | --- | --- | --- | --- | --- |
| M-06.01 | A scoring update is applied | Its cause is inspected | Sender/topic/ID and the cause event are correctly associated, not borrowed from an unrelated RPC. | D [Peer scoring][peer-scoring] | F-05.01 |
| M-06.02 | Object fails validation | Delivery-credit state is updated | It does not retain valid-delivery credit solely from an unvalidated arrival. | D [Extended validators][extended], [Topic parameters][topic-params] | G-01, G-02 |
| M-06.03 | Near-first delivery credit is considered | P3 delivery counter increments | Sender was eligible under the selected mesh/time window, including the specified validation interval. | S [Topic parameters][topic-params] | M-06.01 |
| M-06.04 | v1.3 message could predate processing of the latest subscription change | Router considers downscoring for that message | No downscore is attributed to that causally permitted old subscription state. | S [v1.3 violation scoring][violation-scoring], MUST NOT | M-06.01 |

## M-08

**PX does not authenticate its referrals.** The backoff specification permits
omitting a signed record when unavailable; omission is not automatically an
invalid PX message. Discovery internals remain out of scope.

| ID | Premise | Event | Required conclusion | Basis | Depends on |
| --- | --- | --- | --- | --- | --- |
| M-08.01 | PRUNE contains a referred Peer ID without a signed record | Referral is processed | It remains a discovery candidate, not an authenticated connection identity. | D [PX/backoff][backoff] | — |
| M-08.02 | Sender score does not satisfy P's resolved AcceptPXThreshold rule | PX referrals are considered for use | Those referrals are not accepted under that gate. | S [Thresholds][thresholds] | M-04, M-05 |
| M-08.03 | A referred address is dialed | Peer authentication completes | The normal certificate/expected-Peer-ID checks still apply. | D [PX/backoff][backoff] | A-01, A-02, A-03, A-04 |

The source's threshold prose says "exceeds" while the parameter table describes
ignoring peers "below" the threshold. Equality must be resolved in P against the
chosen authoritative profile; this inventory does not silently choose one.
For P3b, narrative mentions negative-score pruning while the update pseudocode
checks active deficit without that score guard. P must resolve the trigger before
M-04.04 is instantiated; no silent equivalence between those statements is assumed.

## Counterexample scenarios

- Direct/explicit peer sends invalid content: bypassing score gates is not
  bypassing validators. IGNORE must not increment P4.
- Concurrent copies with different bytes, ID collision assumptions, first-invalid
  then valid payload, and a cache expiring between ID lookup and completion.
- IWANT after cache expiry; tracked IHAVE ID supplied by a different peer before
  timeout; one IDONTWANT control erroneously suppressing every neighbor.
- v1.1 unknown-topic GRAFT versus the v1.0 response, explicit-peer GRAFT,
  PRUNE/GRAFT crossing, and JOIN/LEAVE of unrelated topics.
- Exact threshold/activation/window equality; cross-topic rewards masking bad
  behavior; stale callbacks assigning credit after a session is replaced.
- v1.3 subscription change races: newly changed local state alone does not prove
  that the remote peer already processed it.

[validators]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/pubsub/README.md#topic-validation
[ids]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/pubsub/README.md#message-identification
[cache]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/pubsub/gossipsub/gossipsub-v1.0.md#message-cache
[processing]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/pubsub/gossipsub/gossipsub-v1.0.md#message-processing
[membership]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/pubsub/gossipsub/gossipsub-v1.0.md#topic-membership
[extended]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/pubsub/gossipsub/gossipsub-v1.1.md#extended-validators
[explicit]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/pubsub/gossipsub/gossipsub-v1.1.md#explicit-peering-agreements
[backoff]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/pubsub/gossipsub/gossipsub-v1.1.md#prune-backoff-and-peer-exchange
[flood]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/pubsub/gossipsub/gossipsub-v1.1.md#flood-publishing
[spam]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/pubsub/gossipsub/gossipsub-v1.1.md#spam-protection-measures
[quotas]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/pubsub/gossipsub/gossipsub-v1.1.md#outbound-mesh-quotas
[maintenance]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/pubsub/gossipsub/gossipsub-v1.1.md#heartbeat-maintenance
[opportunistic]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/pubsub/gossipsub/gossipsub-v1.1.md#opportunistic-grafting
[peer-scoring]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/pubsub/gossipsub/gossipsub-v1.1.md#peer-scoring
[score]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/pubsub/gossipsub/gossipsub-v1.1.md#the-score-function
[topic-params]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/pubsub/gossipsub/gossipsub-v1.1.md#topic-parameter-calculation-and-decay
[thresholds]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/pubsub/gossipsub/gossipsub-v1.1.md#score-thresholds
[params]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/pubsub/gossipsub/gossipsub-v1.1.md#overview-of-new-parameters
[idontwant]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/pubsub/gossipsub/gossipsub-v1.2.md#idontwant-message
[violation-scoring]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/pubsub/gossipsub/gossipsub-v1.3.md#peer-scoring-on-protocol-violations
