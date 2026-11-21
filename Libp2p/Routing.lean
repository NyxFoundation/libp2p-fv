module

public import Veil

set_option veil.smt.trust false
set_option veil.solver "grind"

/-! Membership and forwarding at one router. Score classes and timer expiration
are interface inputs, not a model of floating-point scoring or wall-clock time. -/
veil module Libp2p.Routing

type peer
type topic
type message

immutable relation explicitPeer : peer → Bool
immutable relation nonnegative : peer → Bool
immutable relation publishEligible : peer → Bool
immutable relation pxEligible : peer → Bool
immutable relation messageTopic : message → topic → Bool

relation joined : topic → Bool
relation subscribed : peer → topic → Bool
relation mesh : peer → topic → Bool
relation fanout : peer → topic → Bool
relation backoff : peer → topic → Bool
relation pruned : peer → topic → Bool
relation suppressed : peer → message → Bool
relation valid : message → Bool
relation localPublication : message → Bool
relation sentRemote : peer → message → Bool
relation sentLocal : peer → message → Bool
relation pxCandidate : peer → Bool
relation pxAuthenticated : peer → Bool

#gen_state

after_init {
  joined T := false
  subscribed P T := false
  mesh P T := false
  fanout P T := false
  backoff P T := false
  pruned P T := false
  suppressed P M := false
  valid M := false
  localPublication M := false
  sentRemote P M := false
  sentLocal P M := false
  pxCandidate P := false
  pxAuthenticated P := false
}

action subscribe (p : peer) (t : topic) {
  subscribed p t := true
}

action addFanout (p : peer) (t : topic) {
  require subscribed p t ∧ nonnegative p ∧ ¬ explicitPeer p ∧ ¬ joined t
  fanout p t := true
}

action join (t : topic) {
  require ¬ joined t
  joined t := true
  mesh P t := fanout P t && !backoff P t
  fanout P t := false
}

action leave (t : topic) {
  pruned P t := pruned P t || mesh P t
  mesh P t := false
  joined t := false
}

action graft (p : peer) (t : topic) {
  if joined t then
    if explicitPeer p ∨ backoff p t ∨ ¬ nonnegative p then
      pruned p t := true
    else
      mesh p t := true
}

action prune (p : peer) (t : topic) {
  mesh p t := false
  backoff p t := true
}

-- Expiration is supplied only by the profile's monotonic timer interface.
action expireBackoff (p : peer) (t : topic) {
  backoff p t := false
}

action idontwant (p : peer) (m : message) {
  suppressed p m := true
}

action expireSuppression (p : peer) (m : message) {
  suppressed p m := false
}

action validatedRemote (m : message) {
  require ¬ localPublication m
  valid m := true
}

action validatedLocal (m : message) {
  require ¬ valid m
  valid m := true
  localPublication m := true
}

action forwardRemote (p : peer) (t : topic) (m : message) {
  require valid m ∧ ¬ localPublication m ∧ messageTopic m t
  require explicitPeer p ∨ (mesh p t ∧ ¬ suppressed p m)
  sentRemote p m := true
}

action publish (p : peer) (t : topic) (m : message) {
  require valid m ∧ localPublication m ∧ messageTopic m t ∧ subscribed p t
  require explicitPeer p ∨ publishEligible p
  sentLocal p m := true
}

action referral (sender referred : peer) {
  require pxEligible sender
  pxCandidate referred := true
}

action authenticateReferral (p : peer) (normalChecksPassed : Bool) {
  require pxCandidate p ∧ normalChecksPassed
  pxAuthenticated p := true
}

safety [no_explicit_mesh] ∀ p t, mesh p t → ¬ explicitPeer p
safety [no_negative_mesh] ∀ p t, mesh p t → nonnegative p
safety [mesh_is_joined] ∀ p t, mesh p t → joined t
safety [remote_requires_validation]
  ∀ p m, sentRemote p m → valid m ∧ ¬ localPublication m
safety [local_requires_validation]
  ∀ p m, sentLocal p m → valid m ∧ localPublication m
safety [referral_is_not_authentication]
  ∀ p, pxAuthenticated p → pxCandidate p
invariant [fanout_eligible]
  ∀ p t, fanout p t → ¬ explicitPeer p ∧ nonnegative p

#gen_spec
#check_invariants
#gen_theorems

#updr (fuel := 500) (expect := invariant) certify
#gen_theorems

#model_check interpreted
  { peer := Fin 1, topic := Fin 1, message := Fin 1 }
  { explicitPeer := fun _ => false, nonnegative := fun _ => true,
    publishEligible := fun _ => true, pxEligible := fun _ => true,
    messageTopic := fun _ _ => true }
  (sequential := true)

sat trace [remote_forwarding_is_reachable] {
  join
  graft
  validatedRemote
  forwardRemote
  assert (∃ p m, sentRemote p m)
}

end Libp2p.Routing
