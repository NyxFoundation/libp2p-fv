module

public import Veil

set_option veil.smt.trust false
set_option veil.solver "grind"

/-! A single receiver's reference pipeline. Immutable coordinates are allocated
with fresh session/stream/task tokens. Parser and validator results are external
contracts; an ACCEPT says nothing about consensus validity or publisher identity. -/
veil module Libp2p.Pipeline

type session
type peer
type stream
type task
type object
type context
type messageId

enum Verdict = {accept, ignore, reject}

immutable function expected : session → peer
immutable function owner : stream → session
immutable relation inbound : stream → Bool
immutable function source : task → stream
immutable function payload : task → object
immutable function scope : task → context
immutable function key : task → messageId

relation allocated : session → Bool
relation live : session → Bool
relation authenticated : session → Bool
function identity : session → peer
relation failed : session → Bool
relation opened : stream → Bool
relation negotiated : stream → Bool
relation reset : stream → Bool
relation dispatched : stream → Bool
relation written : stream → Bool
relation extensionsSent : stream → Bool
relation submitted : task → Bool
relation parseFailed : task → Bool
relation pending : task → Bool
relation accepted : task → Bool
relation ignored : task → Bool
relation rejected : task → Bool
relation canceled : task → Bool
relation delivered : task → Bool
relation forwarded : task → Bool
relation credited : task → Bool
relation penalized : task → Bool
relation seen : messageId → Bool
relation inWindow : task → Bool
individual emitted : Bool
individual lastTask : task
function usedPayload : task → object
function usedContext : task → context

#gen_state



after_init {
  allocated S := false
  live S := false
  authenticated S := false
  identity S := expected S
  failed S := false
  opened I := false
  negotiated I := false
  reset I := false
  dispatched I := false
  written I := false
  extensionsSent I := false
  submitted J := false
  parseFailed J := false
  pending J := false
  accepted J := false
  ignored J := false
  rejected J := false
  canceled J := false
  delivered J := false
  forwarded J := false
  credited J := false
  penalized J := false
  seen K := false
  inWindow J := false
  emitted := false
  usedPayload J := payload J
  usedContext J := scope J
}

action connect (s : session) {
  require ¬ allocated s
  allocated s := true
  live s := true
  emitted := false
}

action authenticate (s : session) (p : peer) (checksPassed : Bool) {
  require live s ∧ ¬ authenticated s
  if checksPassed ∧ p = expected s then
    authenticated s := true
    identity s := p
  else
    live s := false
    failed s := true
  emitted := false
}

action close (s : session) {
  live s := false
  emitted := false
}

action openStream (i : stream) {
  require live (owner i) ∧ authenticated (owner i) ∧ ¬ opened i
  opened i := true
  emitted := false
}

-- This profile selects exact v1.3 matching, not a universal libp2p restriction.
action propose (i : stream) (exactV13 complete : Bool) {
  require live (owner i) ∧ opened i ∧ ¬ reset i ∧ ¬ negotiated i
  if exactV13 ∧ complete then
    negotiated i := true
  emitted := false
}

action terminateStream (i : stream) {
  reset i := true
  emitted := false
}

action dispatch (i : stream) (earlyData : Bool) {
  require live (owner i) ∧ ¬ reset i ∧ inbound i ∧ ¬ earlyData
  require negotiated i
  dispatched i := true
  emitted := false
}

action writeEnvelope (i : stream) (extensionsAttached : Bool) {
  require live (owner i) ∧ ¬ reset i ∧ ¬ inbound i ∧ negotiated i
  if written i then
    require ¬ extensionsAttached
  else
    require extensionsAttached
    extensionsSent i := true
  written i := true
  emitted := false
}

-- `wellFormed` is the selected framing/Protobuf/StrictNoSign decoder contract.
action receive (w : task) (wellFormed : Bool) {
  require live (owner (source w)) ∧ ¬ reset (source w) ∧ dispatched (source w)
  require ¬ submitted w
  submitted w := true
  if wellFormed then
    pending w := true
  else
    parseFailed w := true
  emitted := false
}

action cancel (w : task) {
  canceled w := true
  pending w := false
  emitted := false
}

-- Duplicate lookup IDs do not merge tasks or transfer their validation results.
action finishValidation (w : task) (v : Verdict) {
  require pending w ∧ ¬ canceled w ∧ live (owner (source w)) ∧ ¬ reset (source w)
  pending w := false
  if v = accept then
    accepted w := true
  else if v = ignore then
    ignored w := true
  else
    rejected w := true
  emitted := false
}

action deliver (w : task) {
  require accepted w ∧ ¬ canceled w ∧ live (owner (source w)) ∧ ¬ reset (source w)
  require ¬ seen (key w)
  delivered w := true
  inWindow w := true
  seen (key w) := true
  usedPayload w := payload w
  usedContext w := scope w
  lastTask := w
  emitted := true
}

action forward (w : task) {
  require accepted w ∧ ¬ canceled w ∧ live (owner (source w)) ∧ ¬ reset (source w)
  forwarded w := true
  usedPayload w := payload w
  usedContext w := scope w
  lastTask := w
  emitted := true
}

action credit (w : task) {
  require ¬ credited w
  require accepted w ∧ ¬ canceled w ∧ live (owner (source w)) ∧ ¬ reset (source w)
  credited w := true
  lastTask := w
  emitted := true
}

action penalize (w : task) {
  require ¬ penalized w
  require rejected w ∧ ¬ canceled w ∧ live (owner (source w)) ∧ ¬ reset (source w)
  penalized w := true
  lastTask := w
  emitted := true
}

action expire (k : messageId) {
  seen k := false
  inWindow J := inWindow J && decide (key J ≠ k)
  emitted := false
}

safety [authenticated_identity] ∀ s, authenticated s → identity s = expected s
safety [no_failed_authentication] ∀ s, failed s → ¬ authenticated s ∧ ¬ live s
safety [dispatch_provenance]
  ∀ i, dispatched i → negotiated i ∧ authenticated (owner i) ∧ inbound i
safety [extension_advertisement] ∀ i, written i → extensionsSent i ∧ ¬ inbound i
safety [validated_delivery] ∀ w, delivered w ∨ forwarded w → accepted w
safety [failed_parse_cannot_succeed] ∀ w, parseFailed w → ¬ accepted w
safety [delivery_provenance]
  ∀ w, delivered w ∨ forwarded w →
    authenticated (owner (source w)) ∧ negotiated (source w) ∧ submitted w
safety [validation_to_use]
  ∀ w, delivered w ∨ forwarded w → usedPayload w = payload w ∧ usedContext w = scope w
safety [no_stale_effect]
  emitted → live (owner (source lastTask)) ∧ ¬ canceled lastTask ∧ ¬ reset (source lastTask)
safety [verdict_attribution]
  ∀ w, (credited w → accepted w) ∧ (penalized w → rejected w ∧ ¬ ignored w)
safety [window_at_most_once]
  ∀ w v, inWindow w ∧ inWindow v ∧ key w = key v → w = v

invariant [live_allocated] ∀ s, live s → allocated s
invariant [failure_allocated] ∀ s, failed s → allocated s
invariant [opened_authenticated] ∀ i, opened i → authenticated (owner i)
invariant [selection_opened] ∀ i, negotiated i → opened i
invariant [submission_dispatched] ∀ w, submitted w → dispatched (source w)
invariant [work_submitted]
  ∀ w, pending w ∨ accepted w ∨ ignored w ∨ rejected w → submitted w
invariant [parse_failure_terminal] ∀ w, parseFailed w → submitted w ∧ ¬ pending w
invariant [single_completion]
  ∀ w, (pending w → ¬ accepted w ∧ ¬ ignored w ∧ ¬ rejected w) ∧
    (accepted w → ¬ ignored w ∧ ¬ rejected w) ∧ (ignored w → ¬ rejected w)
invariant [window_seen] ∀ w, inWindow w → seen (key w)

#gen_spec
#check_invariants
#gen_theorems

#model_check interpreted
  { session := Fin 1, peer := Fin 1, stream := Fin 1, task := Fin 1,
    object := Fin 1, context := Fin 1, messageId := Fin 1 }
  { expected := fun _ => 0, owner := fun _ => 0, inbound := fun _ => true,
    source := fun _ => 0, payload := fun _ => 0, scope := fun _ => 0, key := fun _ => 0 }
  (sequential := true)

sat trace [validated_delivery_is_reachable] {
  connect
  authenticate
  openStream
  propose
  dispatch
  receive
  finishValidation
  deliver
  assert (∃ w, delivered w)
}

end Libp2p.Pipeline
