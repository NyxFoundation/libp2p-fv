module

public import Veil

set_option veil.smt.trust false
set_option veil.solver "grind"

/-! Cache ownership, bounded history buckets, retransmission limits and repeated
IHAVE tracking intervals. Timer callbacks represent the configured interval;
wall-clock scheduling is an external contract. Message IDs need not be injective. -/
veil module Libp2p.Cache

type peer
type message
type messageId
type topic

immutable function key : message → messageId
immutable function topicOf : message → topic
immutable individual historyLength : Nat
immutable individual gossipLength : Nat
immutable individual retransmissionLimit : Nat
immutable individual followupTicks : Nat

function age : messageId → Nat
function replies : peer → messageId → Nat
function remaining : peer → messageId → Nat
relation present : messageId → Bool
function cached : messageId → message
relation seen : messageId → Bool
relation accepted : message → Bool
relation promised : peer → messageId → Bool
relation advertised : peer → messageId → Bool
relation arrived : messageId → Bool
individual requestEmitted : Bool
individual replyEmitted : Bool
individual gossipEmitted : Bool
individual penaltyEmitted : Bool
individual lastId : messageId
individual lastMessage : message
individual lastPeer : peer
individual lastTopic : topic

#gen_state

assumption [history_configuration] 0 < gossipLength ∧ gossipLength ≤ historyLength
assumption [followup_configuration] 0 < followupTicks

after_init {
  age K := 0
  replies P K := 0
  remaining P K := 0
  present K := false
  seen K := false
  accepted M := false
  promised P K := false
  advertised P K := false
  arrived K := false
  requestEmitted := false
  replyEmitted := false
  gossipEmitted := false
  penaltyEmitted := false
}

procedure clearEvents {
  requestEmitted := false
  replyEmitted := false
  gossipEmitted := false
  penaltyEmitted := false
}

action validate (m : message) {
  accepted m := true
  clearEvents
}

action store (m : message) {
  require accepted m
  if ¬ present (key m) then
    replies P (key m) := 0
  age (key m) := 0
  cached (key m) := m
  present (key m) := true
  seen (key m) := true
  clearEvents
}

action ihave (p : peer) (k : messageId) (track : Bool) {
  clearEvents
  if ¬ seen k then
    lastId := k
    requestEmitted := true
    if track ∧ ¬ promised p k then
      remaining p k := followupTicks
      promised p k := true
      advertised p k := true
}

action received (_p : peer) (k : messageId) {
  arrived k := true
  clearEvents
}

action iwant (p : peer) (k : messageId) {
  require present k ∧ replies p k < retransmissionLimit
  clearEvents
  replies p k := replies p k + 1
  lastMessage := cached k
  lastId := k
  lastPeer := p
  replyEmitted := true
}

action gossip (k : messageId) (t : topic) {
  require present k ∧ topicOf (cached k) = t ∧ age k < gossipLength
  clearEvents
  lastId := k
  lastMessage := cached k
  lastTopic := t
  gossipEmitted := true
}

action assessPromise (p : peer) (k : messageId) {
  require promised p k ∧ remaining p k = 0
  clearEvents
  promised p k := false
  if ¬ arrived k then
    lastPeer := p
    lastId := k
    penaltyEmitted := true
}

action tickHistory {
  age K := if present K ∧ age K < historyLength then age K + 1 else age K
  present K := present K && decide (age K < historyLength)
  clearEvents
}

-- One callback per configured promise-timer tick, independent of cache buckets.
action tickPromises {
  remaining P K := remaining P K - 1
  clearEvents
}

action evict (k : messageId) {
  present k := false
  clearEvents
}

action expireSeen (k : messageId) {
  seen k := false
  clearEvents
}

action newTrackingInterval (k : messageId) {
  promised P k := false
  remaining P k := 0
  advertised P k := false
  arrived k := false
  clearEvents
}

safety [no_iwant_for_seen] requestEmitted → ¬ seen lastId
safety [reply_correspondence]
  replyEmitted → present lastId ∧ lastMessage = cached lastId ∧ key lastMessage = lastId
safety [gossip_topic]
  gossipEmitted → present lastId ∧ key lastMessage = lastId ∧
    topicOf lastMessage = lastTopic ∧ age lastId < gossipLength
safety [promise_attribution]
  penaltyEmitted → advertised lastPeer lastId ∧ ¬ arrived lastId ∧ remaining lastPeer lastId = 0
safety [bounded_retransmissions]
  ∀ p k, replies p k ≤ retransmissionLimit
safety [bounded_history] ∀ k, present k → age k < historyLength
invariant [cache_key] ∀ k, present k → key (cached k) = k ∧ accepted (cached k)
invariant [promise_was_advertised] ∀ p k, promised p k → advertised p k

#gen_spec
#check_invariants
#gen_theorems

#model_check interpreted
  { peer := Fin 1, message := Fin 1, messageId := Fin 1, topic := Fin 1 }
  { key := fun _ => 0, topicOf := fun _ => 0,
    historyLength := 2, gossipLength := 1, retransmissionLimit := 1, followupTicks := 1 }
  (sequential := true)

sat trace [any_peer_fulfills_promise] {
  ihave
  received
  tickPromises
  assessPromise
  assert ¬ penaltyEmitted
}

sat trace [gossip_window_ages_out] {
  validate
  store
  gossip
  tickHistory
  assert (∃ k, present k ∧ ¬ age k < gossipLength)
}

sat trace [history_expires] {
  validate
  store
  tickHistory
  tickHistory
  assert (∀ k, ¬ present k)
}

end Libp2p.Cache
