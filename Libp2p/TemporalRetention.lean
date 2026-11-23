module

public import Veil

set_option veil.smt.trust false
set_option veil.solver "grind"

/-!
M-04.10 component. Source: libp2p/specs
c750236de43cd8b246a824b377dfdb26bae686db, gossipsub-v1.1.md,
"Peer Scoring" and the RetainScore parameter.

`session` is a fresh peer-online scoring generation, not a claim that a peer
has only one transport connection. The current retained value can evolve under
an externally specified lawful decay function. Reconnection strictly within
RetainScore MUST restore that value for the same PeerID. At/after the endpoint,
restore/discard is nondeterministic: no expiry scheduling algorithm is asserted.
History has no authentication or callback authority fields. Those authorities
are session-local and require separate transitions after each fresh connection.
-/
veil module Libp2p.TemporalRetention

type peer
type session
type history
type moment

immutable function peerOf : session → peer
immutable function timestamp : moment → Nat
immutable function decayHistory : history → history
immutable individual initialHistory : history
immutable individual retainScore : Nat

individual now : Nat
relation allocated : session → Bool
relation live : session → Bool
relation online : peer → Bool
relation authenticated : session → Bool
relation callbackAuthority : session → Bool
function currentHistory : session → history
relation retained : peer → Bool
function retainedHistory : peer → history
function retainedFrom : peer → session
function expires : peer → Nat
individual connectEmitted : Bool
individual restored : Bool
individual lastSession : session
individual lastOrigin : session
individual historyAtConnect : history
individual deadlineAtConnect : Nat
individual existedAtConnect : Bool

#gen_state

after_init {
  now := 0
  allocated S := false
  live S := false
  online P := false
  authenticated S := false
  callbackAuthority S := false
  currentHistory S := initialHistory
  retained P := false
  retainedHistory P := initialHistory
  expires P := 0
  connectEmitted := false
  restored := false
  historyAtConnect := initialHistory
  deadlineAtConnect := 0
  existedAtConnect := false
}

action advance (m : moment) {
  require now ≤ timestamp m
  now := timestamp m
  connectEmitted := false
}

action connect (s : session) (keepAfterLifetime : Bool) {
  require ¬ allocated s ∧ ¬ online (peerOf s)
  allocated s := true
  live s := true
  online (peerOf s) := true
  authenticated s := false
  callbackAuthority s := false
  currentHistory s := initialHistory
  lastSession := s
  lastOrigin := retainedFrom (peerOf s)
  historyAtConnect := retainedHistory (peerOf s)
  deadlineAtConnect := expires (peerOf s)
  existedAtConnect := retained (peerOf s)
  restored := false
  if retained (peerOf s) ∧ (now < expires (peerOf s) ∨ keepAfterLifetime) then
    currentHistory s := retainedHistory (peerOf s)
    restored := true
  retained (peerOf s) := false
  connectEmitted := true
}

-- External numerical update for this live scoring owner, not a retention restore.
action updateLiveHistory (s : session) (h : history) {
  require live s
  currentHistory s := h
  connectEmitted := false
}

action authenticate (s : session) {
  require live s
  authenticated s := true
  connectEmitted := false
}

action authorizeCallbacks (s : session) {
  require live s ∧ authenticated s
  callbackAuthority s := true
  connectEmitted := false
}

action disconnect (s : session) {
  require live s
  retained (peerOf s) := true
  retainedHistory (peerOf s) := currentHistory s
  retainedFrom (peerOf s) := s
  expires (peerOf s) := now + retainScore
  live s := false
  online (peerOf s) := false
  authenticated s := false
  callbackAuthority s := false
  connectEmitted := false
}

action decayRetained (p : peer) {
  require retained p
  retainedHistory p := decayHistory (retainedHistory p)
  connectEmitted := false
}

safety [restore_current_same_peer_history]
  connectEmitted ∧ restored → existedAtConnect ∧
    peerOf lastOrigin = peerOf lastSession ∧
    currentHistory lastSession = historyAtConnect ∧ ¬ live lastOrigin
safety [unexpired_history_must_restore]
  connectEmitted ∧ existedAtConnect ∧ now < deadlineAtConnect → restored
safety [reconnect_without_authority]
  connectEmitted → ¬ authenticated lastSession ∧ ¬ callbackAuthority lastSession
safety [dead_session_without_authority]
  ∀ s, ¬ live s → ¬ authenticated s ∧ ¬ callbackAuthority s
invariant [live_allocated] ∀ s, live s → allocated s ∧ online (peerOf s)
invariant [one_scoring_owner]
  ∀ a b, live a ∧ live b ∧ peerOf a = peerOf b → a = b
invariant [retention_origin]
  ∀ p, retained p → allocated (retainedFrom p) ∧ peerOf (retainedFrom p) = p ∧
    ¬ live (retainedFrom p)
invariant [restored_origin_allocated]
  connectEmitted ∧ restored → allocated lastOrigin

#gen_spec
#check_invariants
#gen_theorems

#model_check interpreted
  { peer := Fin 1, session := Fin 2, history := Fin 2, moment := Fin 2 }
  { peerOf := fun _ => 0, timestamp := fun m => m.val,
    decayHistory := fun h => if h.val = 0 then 1 else 0,
    initialHistory := 0, retainScore := 1 }
  (sequential := true)

#model_check interpreted
  { peer := Fin 2, session := Fin 2, history := Fin 2, moment := Fin 1 }
  { peerOf := fun s => s, timestamp := fun _ => 0,
    decayHistory := fun h => h, initialHistory := 0, retainScore := 1 }
  (sequential := true)

sat trace [restore_after_decay_without_authority] {
  connect
  updateLiveHistory
  assert (∃ s, live s ∧ decayHistory (currentHistory s) ≠ currentHistory s)
  authenticate
  authorizeCallbacks
  disconnect
  decayRetained
  connect
  assert (connectEmitted ∧ restored ∧ now < deadlineAtConnect ∧
    currentHistory lastSession = historyAtConnect ∧
    currentHistory lastSession ≠ currentHistory lastOrigin ∧
    ¬ authenticated lastSession ∧ ¬ callbackAuthority lastSession)
}

sat trace [different_peer_does_not_inherit_history] {
  connect
  updateLiveHistory
  assert (∃ s, live s ∧ currentHistory s ≠ initialHistory)
  disconnect
  connect
  assert (connectEmitted ∧ ¬ existedAtConnect ∧ ¬ restored ∧
    currentHistory lastSession = initialHistory ∧
    ∃ s, allocated s ∧ peerOf s ≠ peerOf lastSession)
}

end Libp2p.TemporalRetention
