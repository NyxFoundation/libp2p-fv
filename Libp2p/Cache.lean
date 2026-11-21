module

public import Veil

set_option veil.smt.trust false
set_option veil.solver "grind"

/-! Cache ownership and one IHAVE tracking interval. Timer expiration and history
window selection are explicit inputs. Message IDs need not be injective. -/
veil module Libp2p.Cache

type peer
type message
type messageId
type topic

immutable function key : message → messageId
immutable function topicOf : message → topic
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

after_init {
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
    if track then
      promised p k := true
      advertised p k := true
}

action received (_p : peer) (k : messageId) {
  arrived k := true
  clearEvents
}

action iwant (p : peer) (k : messageId) {
  require present k
  clearEvents
  lastMessage := cached k
  lastId := k
  lastPeer := p
  replyEmitted := true
}

action gossip (k : messageId) (t : topic) {
  require present k ∧ topicOf (cached k) = t
  clearEvents
  lastId := k
  lastMessage := cached k
  lastTopic := t
  gossipEmitted := true
}

action assessPromise (p : peer) (k : messageId) {
  require promised p k
  clearEvents
  promised p k := false
  if ¬ arrived k then
    lastPeer := p
    lastId := k
    penaltyEmitted := true
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
  advertised P k := false
  arrived k := false
  clearEvents
}

safety [no_iwant_for_seen] requestEmitted → ¬ seen lastId
safety [reply_correspondence]
  replyEmitted → present lastId ∧ lastMessage = cached lastId ∧ key lastMessage = lastId
safety [gossip_topic]
  gossipEmitted → present lastId ∧ key lastMessage = lastId ∧ topicOf lastMessage = lastTopic
safety [promise_attribution]
  penaltyEmitted → advertised lastPeer lastId ∧ ¬ arrived lastId
invariant [cache_key] ∀ k, present k → key (cached k) = k ∧ accepted (cached k)
invariant [promise_was_advertised] ∀ p k, promised p k → advertised p k

#gen_spec
#check_invariants
#gen_theorems

#updr (fuel := 500) (expect := invariant) certify
#gen_theorems

#model_check interpreted
  { peer := Fin 1, message := Fin 1, messageId := Fin 1, topic := Fin 1 }
  { key := fun _ => 0, topicOf := fun _ => 0 }
  (sequential := true)

sat trace [any_peer_fulfills_promise] {
  ihave
  received
  assessPromise
  assert ¬ penaltyEmitted
}

end Libp2p.Cache
