module

public import Veil

set_option veil.smt.trust false
set_option veil.solver "grind"

/-!
M-06.04 actual-order auxiliary relation, NOT the full epistemic permission rule.
Source: libp2p/specs c750236de43cd8b246a824b377dfdb26bae686db,
gossipsub-v1.3.md, "Peer Scoring on Protocol Violations".

The model observes global subscription-change, remote-processing, and message-
send events. Serial numbers order these events even when physical clocks would
be equal. `considerViolation` is an externally justified, independently
checkable violation request. Its actual-order filter is necessary but is NOT
sufficient to establish that an earlier send was observationally impossible.
TemporalKnowledge adds that specification-only condition over compatible real
histories. Neither module implements a detector or a subscription penalty
heuristic. The latest-change restriction is receiver-wide, including changes
to a topic unrelated to the message; per-topic fields are auxiliary bookkeeping.
-/
veil module Libp2p.TemporalCausality

type peer
type topic
type task
type object
type context
type messageId
type subscription

immutable function sender : task → peer
immutable function payload : task → object
immutable function scope : task → context
immutable function key : task → messageId
immutable function channel : context → topic
immutable function changedTopic : subscription → topic
immutable relation wantsTopic : subscription → Bool

individual serial : Nat
relation changed : subscription → Bool
function changedAt : subscription → Nat
relation hasChange : topic → Bool
function latest : topic → subscription
individual receiverHasChange : Bool
individual receiverLatest : subscription
relation subscribed : topic → Bool
relation processed : peer → subscription → Bool
function processedAt : peer → subscription → Nat
relation sent : task → Bool
function sentAt : task → Nat
relation received : task → Bool
relation assessed : task → Bool
individual penaltyEmitted : Bool
individual cause : task
individual causeObject : object
individual causeContext : context

#gen_state

after_init {
  serial := 0
  changed E := false
  changedAt E := 0
  hasChange T := false
  receiverHasChange := false
  subscribed T := false
  processed P E := false
  processedAt P E := 0
  sent J := false
  sentAt J := 0
  received J := false
  assessed J := false
  penaltyEmitted := false
}

action changeSubscription (e : subscription) {
  require ¬ changed e
  serial := serial + 1
  changed e := true
  changedAt e := serial
  hasChange (changedTopic e) := true
  latest (changedTopic e) := e
  receiverHasChange := true
  receiverLatest := e
  subscribed (changedTopic e) := wantsTopic e
  penaltyEmitted := false
}

action remoteProcesses (p : peer) (e : subscription) {
  require changed e ∧ ¬ processed p e
  serial := serial + 1
  processed p e := true
  processedAt p e := serial
  penaltyEmitted := false
}

action send (j : task) {
  require ¬ sent j
  serial := serial + 1
  sent j := true
  sentAt j := serial
  penaltyEmitted := false
}

action receive (j : task) {
  require sent j ∧ ¬ received j
  received j := true
  penaltyEmitted := false
}

action considerViolation (j : task) (applyPenalty : Bool) {
  require received j ∧ ¬ assessed j
  assessed j := true
  cause := j
  causeObject := payload j
  causeContext := scope j
  penaltyEmitted := false
  if applyPenalty ∧ (¬ receiverHasChange ∨
      (processed (sender j) receiverLatest ∧
       processedAt (sender j) receiverLatest < sentAt j)) then
    penaltyEmitted := true
}

safety [no_penalty_for_causally_old_message]
  penaltyEmitted ∧ receiverHasChange →
    processed (sender cause) receiverLatest ∧
    processedAt (sender cause) receiverLatest < sentAt cause
safety [penalty_cause_coordinates]
  penaltyEmitted → received cause ∧ assessed cause ∧
    causeObject = payload cause ∧ causeContext = scope cause
invariant [received_was_sent] ∀ j, received j → sent j
invariant [sent_before_serial] ∀ j, sent j → sentAt j ≤ serial
invariant [changed_before_serial] ∀ e, changed e → changedAt e ≤ serial
invariant [processing_after_change]
  ∀ p e, processed p e → changed e ∧ changedAt e < processedAt p e ∧ processedAt p e ≤ serial
invariant [latest_topic]
  ∀ t, hasChange t → changed (latest t) ∧ changedTopic (latest t) = t
invariant [receiver_latest_changed]
  receiverHasChange → changed receiverLatest

#gen_spec
#check_invariants
#gen_theorems

#model_check interpreted
  { peer := Fin 1, topic := Fin 1, task := Fin 1, object := Fin 1,
    context := Fin 1, messageId := Fin 1, subscription := Fin 1 }
  { sender := fun _ => 0, payload := fun _ => 0, scope := fun _ => 0,
    key := fun _ => 0, channel := fun _ => 0, changedTopic := fun _ => 0,
    wantsTopic := fun _ => false }
  (sequential := true)

#model_check interpreted
  { peer := Fin 1, topic := Fin 2, task := Fin 1, object := Fin 1,
    context := Fin 1, messageId := Fin 1, subscription := Fin 1 }
  { sender := fun _ => 0, payload := fun _ => 0, scope := fun _ => 0,
    key := fun _ => 0, channel := fun _ => 0, changedTopic := fun _ => 1,
    wantsTopic := fun _ => false }
  (sequential := true)

sat trace [old_message_is_not_penalized] {
  changeSubscription
  send
  remoteProcesses
  receive
  considerViolation
  assert ((∃ j, assessed j) ∧ ¬ penaltyEmitted)
}

sat trace [actual_order_filter_allows_later_message] {
  changeSubscription
  remoteProcesses
  send
  receive
  considerViolation
  assert penaltyEmitted
}

sat trace [unrelated_topic_change_also_matters] {
  changeSubscription
  send
  receive
  considerViolation
  assert (receiverHasChange ∧ ¬ hasChange (channel (scope cause)) ∧
    assessed cause ∧ ¬ processed (sender cause) receiverLatest ∧ ¬ penaltyEmitted)
}

end Libp2p.TemporalCausality
