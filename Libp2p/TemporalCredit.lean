module

public import Veil

set_option veil.smt.trust false
set_option veil.solver "grind"

/-!
M-06.03 specification component. Source: libp2p/specs
c750236de43cd8b246a824b377dfdb26bae686db, gossipsub-v1.1.md,
"Topic Parameter Calculation and Decay", P3/P3b.

Each task is a fresh arrival occurrence with immutable peer/object/context/ID
coordinates. First-arrival grouping uses the actual object AND context, never the
lookup ID. Each task additionally needs its own external ACCEPT verdict; a
first task's validation cannot authenticate a different candidate. `duringValidation` is captured from the actual pending state at
arrival, so equal clock timestamps do not erase event order.

The window covers arrival during first validation and the strict post-validation
interior; the unspecified final equality permits either choice. `creditEvents`
counts authorized increments, not the capped/decayed numerical P3 parameter;
composition with the separate numeric policy remains required.
-/
veil module Libp2p.TemporalCredit

type peer
type topic
type task
type object
type context
type messageId
type moment

immutable function sender : task → peer
immutable function payload : task → object
immutable function scope : task → context
immutable function key : task → messageId
immutable function channel : context → topic
immutable function timestamp : moment → Nat
immutable function window : topic → Nat

individual now : Nat
relation mesh : peer → topic → Bool
relation received : task → Bool
function arrival : task → Nat
relation meshAtArrival : task → Bool
relation duringValidation : task → Bool
relation started : object → context → Bool
function firstArrival : object → context → Nat
function firstTask : object → context → task
relation completed : task → Bool
relation taskAccepted : task → Bool
relation resolved : object → context → Bool
relation accepted : object → context → Bool
function validationTime : object → context → Nat
relation credited : task → Bool
relation peerCredited : peer → object → context → Bool
function creditOwner : peer → object → context → task
function creditEvents : peer → topic → Nat
individual creditEmitted : Bool
individual cause : task
individual previousCount : Nat
function usedObject : task → object
function usedContext : task → context

#gen_state

after_init {
  now := 0
  mesh P T := false
  received J := false
  arrival J := 0
  meshAtArrival J := false
  duringValidation J := false
  started O C := false
  firstArrival O C := 0
  completed J := false
  taskAccepted J := false
  resolved O C := false
  accepted O C := false
  validationTime O C := 0
  credited J := false
  peerCredited P O C := false
  creditEvents P T := 0
  creditEmitted := false
  previousCount := 0
  usedObject J := payload J
  usedContext J := scope J
}

action advance (m : moment) {
  require now ≤ timestamp m
  now := timestamp m
  creditEmitted := false
}

action setMesh (p : peer) (t : topic) (joined : Bool) {
  mesh p t := joined
  creditEmitted := false
}

action arrive (j : task) {
  require ¬ received j
  received j := true
  arrival j := now
  meshAtArrival j := mesh (sender j) (channel (scope j))
  duringValidation j := ¬ resolved (payload j) (scope j)
  if ¬ started (payload j) (scope j) then
    started (payload j) (scope j) := true
    firstArrival (payload j) (scope j) := now
    firstTask (payload j) (scope j) := j
  creditEmitted := false
}

action finishValidation (j : task) (valid : Bool) {
  require received j ∧ ¬ completed j
  completed j := true
  taskAccepted j := valid
  if j = firstTask (payload j) (scope j) then
    resolved (payload j) (scope j) := true
    accepted (payload j) (scope j) := valid
    validationTime (payload j) (scope j) := now
  creditEmitted := false
}

action credit (j : task) (countEndpoint : Bool) {
  require received j ∧ ¬ credited j ∧ meshAtArrival j ∧ taskAccepted j
  require accepted (payload j) (scope j)
  require ¬ peerCredited (sender j) (payload j) (scope j)
  require duringValidation j ∨
    arrival j < validationTime (payload j) (scope j) + window (channel (scope j)) ∨
    (arrival j = validationTime (payload j) (scope j) + window (channel (scope j)) ∧
      countEndpoint)
  previousCount := creditEvents (sender j) (channel (scope j))
  creditEvents (sender j) (channel (scope j)) := previousCount + 1
  credited j := true
  peerCredited (sender j) (payload j) (scope j) := true
  creditOwner (sender j) (payload j) (scope j) := j
  usedObject j := payload j
  usedContext j := scope j
  cause := j
  creditEmitted := true
}

safety [credit_has_valid_cause]
  ∀ j, credited j → received j ∧ meshAtArrival j ∧ taskAccepted j ∧ accepted (payload j) (scope j) ∧
    usedObject j = payload j ∧ usedContext j = scope j ∧
    (duringValidation j ∨
      arrival j ≤ validationTime (payload j) (scope j) + window (channel (scope j)))
safety [credit_counted_once_per_action]
  creditEmitted → credited cause ∧
    creditEvents (sender cause) (channel (scope cause)) = previousCount + 1
safety [one_credit_per_peer_object_context]
  ∀ a b, credited a ∧ credited b ∧ sender a = sender b ∧
    payload a = payload b ∧ scope a = scope b → a = b
invariant [credit_owner]
  ∀ j, credited j → peerCredited (sender j) (payload j) (scope j) ∧
    creditOwner (sender j) (payload j) (scope j) = j
invariant [first_task_coordinates]
  ∀ o c, started o c → received (firstTask o c) ∧ payload (firstTask o c) = o ∧
    scope (firstTask o c) = c ∧ arrival (firstTask o c) = firstArrival o c
invariant [completion_received] ∀ j, completed j → received j
invariant [task_accept_completed] ∀ j, taskAccepted j → completed j
invariant [first_completion]
  ∀ o c, resolved o c ↔ started o c ∧ completed (firstTask o c)
invariant [validation_started] ∀ o c, resolved o c → started o c
invariant [accepted_resolved] ∀ o c, accepted o c → resolved o c
invariant [first_before_now] ∀ o c, started o c → firstArrival o c ≤ now
invariant [validation_after_first]
  ∀ o c, resolved o c → firstArrival o c ≤ validationTime o c ∧ validationTime o c ≤ now
invariant [arrival_started]
  ∀ j, received j → started (payload j) (scope j) ∧
    firstArrival (payload j) (scope j) ≤ arrival j ∧ arrival j ≤ now
invariant [pending_arrival_order]
  ∀ j, received j ∧ duringValidation j ∧ resolved (payload j) (scope j) →
    arrival j ≤ validationTime (payload j) (scope j)
invariant [completed_arrival_order]
  ∀ j, received j ∧ ¬ duringValidation j → resolved (payload j) (scope j) ∧
    validationTime (payload j) (scope j) ≤ arrival j

#gen_spec
#check_invariants
#gen_theorems

#model_check interpreted
  { peer := Fin 1, topic := Fin 1, task := Fin 2, object := Fin 1,
    context := Fin 1, messageId := Fin 1, moment := Fin 2 }
  { sender := fun _ => 0, payload := fun _ => 0, scope := fun _ => 0,
    key := fun _ => 0, channel := fun _ => 0, timestamp := fun m => m.val,
    window := fun _ => 1 }
  (sequential := true)

#model_check interpreted
  { peer := Fin 1, topic := Fin 1, task := Fin 2, object := Fin 2,
    context := Fin 2, messageId := Fin 1, moment := Fin 1 }
  { sender := fun _ => 0, payload := fun j => j, scope := fun j => j,
    key := fun _ => 0, channel := fun _ => 0, timestamp := fun _ => 0,
    window := fun _ => 1 }
  (sequential := true)

sat trace [arrival_during_first_validation] {
  setMesh
  arrive
  arrive
  finishValidation
  finishValidation
  credit
  assert (creditEmitted ∧ duringValidation cause ∧
    cause ≠ firstTask (payload cause) (scope cause))
}

sat trace [arrival_after_validation_same_clock_tick] {
  setMesh
  arrive
  finishValidation
  arrive
  finishValidation
  credit
  assert (creditEmitted ∧ ¬ duringValidation cause ∧
    arrival cause = validationTime (payload cause) (scope cause))
}

sat trace [arrival_inside_post_validation_window] {
  setMesh
  arrive
  finishValidation
  advance
  arrive
  finishValidation
  credit
  assert (creditEmitted ∧ ¬ duringValidation cause ∧
    validationTime (payload cause) (scope cause) < arrival cause ∧
    arrival cause < validationTime (payload cause) (scope cause) + window (channel (scope cause)))
}

end Libp2p.TemporalCredit
