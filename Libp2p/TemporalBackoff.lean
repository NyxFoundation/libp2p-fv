module

public import Veil

set_option veil.smt.trust false
set_option veil.solver "grind"

/-!
M-01.04 specification relation, not a choice of an extension algorithm.
Source: libp2p/specs c750236de43cd8b246a824b377dfdb26bae686db,
gossipsub-v1.1.md, "PRUNE Backoff and Peer Exchange".
A GRAFT strictly inside backoff emits PRUNE and chooses any strictly later
deadline. Equality/expiry scheduling and the optional P7 penalty are outside
this component. Occurrences are fresh control tokens, not message IDs.
-/
veil module Libp2p.TemporalBackoff

type peer
type topic
type occurrence
type moment

enum Control = {prune, graft}

immutable function sender : occurrence → peer
immutable function channel : occurrence → topic
immutable function kind : occurrence → Control
immutable function timestamp : moment → Nat

individual now : Nat
relation consumed : occurrence → Bool
relation backedOff : peer → topic → Bool
function deadline : peer → topic → Nat
individual pruneEmitted : Bool
individual cause : occurrence
individual previousDeadline : Nat

#gen_state

after_init {
  now := 0
  consumed C := false
  backedOff P T := false
  deadline P T := 0
  pruneEmitted := false
  previousDeadline := 0
}

action advance (m : moment) {
  require now ≤ timestamp m
  now := timestamp m
  pruneEmitted := false
}

action receivePrune (c : occurrence) (endTime : moment) {
  require ¬ consumed c ∧ kind c = prune ∧ now < timestamp endTime
  consumed c := true
  backedOff (sender c) (channel c) := true
  deadline (sender c) (channel c) := timestamp endTime
  pruneEmitted := false
}

action receiveActiveGraft (c : occurrence) (endTime : moment) {
  require ¬ consumed c ∧ kind c = graft
  require backedOff (sender c) (channel c)
  require now < deadline (sender c) (channel c)
  require deadline (sender c) (channel c) < timestamp endTime
  previousDeadline := deadline (sender c) (channel c)
  deadline (sender c) (channel c) := timestamp endTime
  consumed c := true
  cause := c
  pruneEmitted := true
}

safety [prune_extends_active_backoff]
  pruneEmitted → consumed cause ∧ kind cause = graft ∧
    backedOff (sender cause) (channel cause) ∧ now < previousDeadline ∧
    previousDeadline < deadline (sender cause) (channel cause)

#gen_spec
#check_invariants
#gen_theorems

#model_check interpreted
  { peer := Fin 1, topic := Fin 1, occurrence := Fin 2, moment := Fin 3 }
  { sender := fun _ => 0, channel := fun _ => 0,
    kind := fun c => if c.val = 0 then prune else graft,
    timestamp := fun m => m.val + 1 }
  (sequential := true)

sat trace [active_graft_extends] {
  receivePrune
  receiveActiveGraft
  assert (pruneEmitted ∧ previousDeadline < deadline (sender cause) (channel cause))
}

end Libp2p.TemporalBackoff
