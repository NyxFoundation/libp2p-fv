module

public import Veil

set_option veil.smt.trust false
set_option veil.solver "grind"

/-!
G-07.04: count IDONTWANT control occurrences per peer per heartbeat, not the
number of lookup IDs carried by a control. Source: libp2p/specs
c750236de43cd8b246a824b377dfdb26bae686db, gossipsub-v1.2.md,
"IDONTWANT Message". The network sort denotes all participants in the assumed
configuration snapshot; agreement is computed from their actual limits.
The SHOULD penalty is optional, never required by this transition relation.
Heartbeat scheduling and dissemination of configuration are external.
-/
veil module Libp2p.TemporalLimits

type peer
type occurrence
type moment

immutable function sender : occurrence → peer
immutable function timestamp : moment → Nat
immutable function configuredLimit : peer → Nat
immutable individual localLimit : Nat

individual now : Nat
relation consumed : occurrence → Bool
function receivedCount : peer → Nat
individual penaltyEmitted : Bool
individual cause : occurrence
individual countAtPenalty : Nat

#gen_state

after_init {
  now := 0
  consumed C := false
  receivedCount P := 0
  penaltyEmitted := false
  countAtPenalty := 0
}

action heartbeat (m : moment) {
  require now < timestamp m
  now := timestamp m
  receivedCount P := 0
  penaltyEmitted := false
}

action receiveIDontWant (c : occurrence) (applyPenalty : Bool) {
  require ¬ consumed c
  consumed c := true
  receivedCount (sender c) := receivedCount (sender c) + 1
  penaltyEmitted := false
  if localLimit < receivedCount (sender c) ∧
      (∀ p, configuredLimit p = localLimit) ∧ applyPenalty then
    cause := c
    countAtPenalty := receivedCount (sender c)
    penaltyEmitted := true
}

safety [penalty_requires_network_agreement]
  penaltyEmitted → (∀ p, configuredLimit p = localLimit) ∧
    consumed cause ∧ localLimit < countAtPenalty ∧
    countAtPenalty = receivedCount (sender cause)

#gen_spec
#check_invariants
#gen_theorems

#model_check interpreted
  { peer := Fin 1, occurrence := Fin 2, moment := Fin 1 }
  { sender := fun _ => 0, timestamp := fun _ => 1,
    configuredLimit := fun _ => 1, localLimit := 1 }
  (sequential := true)

#model_check interpreted
  { peer := Fin 2, occurrence := Fin 2, moment := Fin 1 }
  { sender := fun _ => 0, timestamp := fun _ => 1,
    configuredLimit := fun p => p.val + 1, localLimit := 1 }
  (sequential := true)

sat trace [agreed_limit_can_penalize] {
  assert (localLimit = 1 ∧ ∀ p, configuredLimit p = localLimit)
  receiveIDontWant
  assert (¬ penaltyEmitted ∧ ∃ p, receivedCount p = 1)
  receiveIDontWant
  assert (penaltyEmitted ∧ countAtPenalty = 2)
}

sat trace [excess_does_not_require_penalty] {
  assert (localLimit = 1 ∧ ∀ p, configuredLimit p = localLimit)
  receiveIDontWant
  receiveIDontWant
  assert ((∃ p, localLimit < receivedCount p) ∧ ¬ penaltyEmitted)
}

sat trace [disagreement_does_not_justify_penalty] {
  assert (localLimit = 0 ∧ ∃ p, configuredLimit p ≠ localLimit)
  receiveIDontWant
  assert (¬ penaltyEmitted ∧ ∃ p, localLimit < receivedCount p)
}

end Libp2p.TemporalLimits
