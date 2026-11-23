module

public import Veil

set_option veil.smt.trust false
set_option veil.solver "grind"

/-! GossipSub v1.3 routing with v1.1 score/mesh rules and optional v1.2
IDONTWANT. Snapshot classifiers are interpreted by the composing score model;
they do not implement score arithmetic. Score refresh does not prune the mesh.
`knownPeers` enumerates the modeled population, not a count supplied by an oracle.
Timer deadlines, connection generations and validator results remain interfaces. -/
veil module Libp2p.Routing

type peer
type topic
type message
type messageId
type snapshot

immutable individual initialSnapshot : snapshot
immutable relation explicitPeer : peer → Bool
immutable relation nonnegative : snapshot → peer → Bool
immutable relation publishEligible : snapshot → peer → Bool
immutable relation pxEligible : snapshot → peer → Bool
immutable relation messageTopic : message → topic → Bool
immutable function key : message → messageId
immutable individual knownPeers : List peer
immutable individual highDegree : Nat

individual currentSnapshot : snapshot
relation joined : topic → Bool
relation subscribed : peer → topic → Bool
relation mesh : peer → topic → Bool
relation fanout : peer → topic → Bool
relation backoff : peer → topic → Bool
relation pruned : peer → topic → Bool
relation suppressed : peer → messageId → Bool
relation valid : message → Bool
relation localPublication : message → Bool
relation publishedId : messageId → Bool
relation sentRemote : peer → message → Bool
relation sentLocal : peer → message → Bool
relation pxCandidate : peer → Bool
relation pxAuthenticated : peer → Bool
function meshSnapshot : peer → topic → snapshot
function fanoutSnapshot : peer → topic → snapshot
function publishSnapshot : peer → message → snapshot
function pxSnapshot : peer → snapshot
function pxSource : peer → peer
individual heartbeatClean : Bool
individual graftRecorded : Bool
individual graftPeer : peer
individual graftTopic : topic
individual graftSnapshot : snapshot
individual graftDegree : Nat
individual graftOutbound : Bool

#gen_state

-- This is the actual duplicate-free mesh count, not an unconstrained capacity flag.
ghost function meshDegree (t : topic) : Nat :=
  (knownPeers.eraseDups.filter (fun p => mesh p t)).length

after_init {
  currentSnapshot := initialSnapshot
  joined T := false
  subscribed P T := false
  mesh P T := false
  fanout P T := false
  backoff P T := false
  pruned P T := false
  suppressed P K := false
  valid M := false
  localPublication M := false
  publishedId K := false
  sentRemote P M := false
  sentLocal P M := false
  pxCandidate P := false
  pxAuthenticated P := false
  heartbeatClean := true
  graftRecorded := false
  graftDegree := 0
  graftOutbound := false
}

action refreshScores (s : snapshot) {
  currentSnapshot := s
  heartbeatClean := false
}

action subscribe (p : peer) (t : topic) {
  subscribed p t := true
}

action addFanout (p : peer) (t : topic) {
  require p ∈ knownPeers
  require subscribed p t ∧ nonnegative currentSnapshot p ∧ ¬ explicitPeer p ∧ ¬ joined t
  fanout p t := true
  fanoutSnapshot p t := currentSnapshot
}

action join (t : topic) {
  require ¬ joined t
  joined t := true
  mesh P t := fanout P t && nonnegative currentSnapshot P && !backoff P t
  meshSnapshot P t := currentSnapshot
  fanout P t := false
}

action leave (t : topic) {
  pruned P t := pruned P t || mesh P t
  backoff P t := backoff P t || mesh P t
  mesh P t := false
  joined t := false
}

action graft (p : peer) (t : topic) (outboundConnection : Bool) {
  if joined t then
    if explicitPeer p ∨ backoff p t ∨ ¬ nonnegative currentSnapshot p then
      mesh p t := false
      pruned p t := true
      backoff p t := true
    else if ¬ mesh p t then
      -- The composed receive interface supplies a peer in the modeled population.
      require p ∈ knownPeers
      let degree := meshDegree t
      if degree ≥ highDegree ∧ ¬ outboundConnection then
        pruned p t := true
        backoff p t := true
      else
        graftRecorded := true
        graftPeer := p
        graftTopic := t
        graftSnapshot := currentSnapshot
        graftDegree := degree
        graftOutbound := outboundConnection
        mesh p t := true
        meshSnapshot p t := currentSnapshot
}

-- Local selection (including opportunistic grafting) is not incoming GRAFT admission.
-- The parent Selection model supplies the survivor/above-median selection proof.
action localGraft (p : peer) (t : topic) {
  require p ∈ knownPeers
  require joined t ∧ subscribed p t ∧ ¬ mesh p t
  require nonnegative currentSnapshot p ∧ ¬ explicitPeer p ∧ ¬ backoff p t
  mesh p t := true
  meshSnapshot p t := currentSnapshot
}

-- v1.1 removes negative peers from all meshes at the heartbeat, not at refresh.
action heartbeat {
  pruned P T := pruned P T || (mesh P T && !nonnegative currentSnapshot P)
  backoff P T := backoff P T || (mesh P T && !nonnegative currentSnapshot P)
  mesh P T := mesh P T && nonnegative currentSnapshot P
  heartbeatClean := true
}

action prune (p : peer) (t : topic) {
  mesh p t := false
  backoff p t := true
}

-- The composing timer supplies permitted expiration and backoff-extension events.
action expireBackoff (p : peer) (t : topic) {
  backoff p t := false
}

action idontwant (p : peer) (k : messageId) (honor : Bool) {
  if honor then
    suppressed p k := true
}

action expireSuppression (p : peer) (k : messageId) {
  suppressed p k := false
}

-- Clearing on replacement is a selected lifetime policy, not a wire requirement.
action replaceSession (p : peer) (clearSuppression : Bool) {
  if clearSuppression then
    suppressed p K := false
}

-- Receiving payload despite an earlier optional control is not a penalty cause.
-- The whole-system coordinator must also frame its Score component for this event.
action ignoredIdontwant (_p : peer) (_k : messageId) {
  pure ()
}

action validatedRemote (m : message) {
  require ¬ localPublication m
  valid m := true
}

action validatedLocal (m : message) {
  require ¬ valid m
  valid m := true
  localPublication m := true
  publishedId (key m) := true
}

-- The composing seen-window policy supplies expiration; no permanent echo ban.
action expirePublication (k : messageId) {
  publishedId k := false
}

action forwardRemote (p : peer) (t : topic) (m : message) {
  require valid m ∧ ¬ localPublication m ∧ ¬ publishedId (key m) ∧ messageTopic m t
  require explicitPeer p ∨ (mesh p t ∧ ¬ suppressed p (key m))
  sentRemote p m := true
}

action publish (p : peer) (t : topic) (m : message) {
  require valid m ∧ localPublication m ∧ messageTopic m t ∧ subscribed p t
  require explicitPeer p ∨ publishEligible currentSnapshot p
  publishSnapshot p m := currentSnapshot
  publishedId (key m) := true
  sentLocal p m := true
}

action referral (sender referred : peer) {
  require pxEligible currentSnapshot sender
  pxSnapshot referred := currentSnapshot
  pxSource referred := sender
  pxCandidate referred := true
}

action authenticateReferral (p : peer) (normalChecksPassed : Bool) {
  require pxCandidate p ∧ normalChecksPassed
  pxAuthenticated p := true
}

safety [no_explicit_mesh] ∀ p t, mesh p t → ¬ explicitPeer p
safety [mesh_is_joined] ∀ p t, mesh p t → joined t
safety [mesh_admission_score] ∀ p t, mesh p t → nonnegative (meshSnapshot p t) p
safety [heartbeat_removes_negative]
  heartbeatClean → ∀ p t, mesh p t → nonnegative currentSnapshot p
safety [graft_admission_score] graftRecorded → nonnegative graftSnapshot graftPeer
safety [graft_capacity] graftRecorded → graftDegree < highDegree ∨ graftOutbound
safety [remote_requires_validation]
  ∀ p m, sentRemote p m → valid m ∧ ¬ localPublication m
safety [local_requires_validation]
  ∀ p m, sentLocal p m → valid m ∧ localPublication m
safety [publish_decision_score]
  ∀ p m, sentLocal p m → explicitPeer p ∨ publishEligible (publishSnapshot p m) p
safety [px_decision_score]
  ∀ p, pxCandidate p → pxEligible (pxSnapshot p) (pxSource p)
safety [referral_is_not_authentication]
  ∀ p, pxAuthenticated p → pxCandidate p
invariant [mesh_known] ∀ p t, mesh p t → p ∈ knownPeers
invariant [fanout_known] ∀ p t, fanout p t → p ∈ knownPeers
invariant [fanout_eligible]
  ∀ p t, fanout p t → ¬ explicitPeer p ∧ nonnegative (fanoutSnapshot p t) p

#gen_spec
#check_invariants
#gen_theorems

-- Arbitrary snapshots are covered by routingSafety; dynamic examples are in Tests/Routing.
#model_check interpreted
  { peer := Fin 1, topic := Fin 1, message := Fin 1, messageId := Fin 1, snapshot := Fin 1 }
  { initialSnapshot := 0, explicitPeer := fun _ => false, nonnegative := fun _ _ => true,
    publishEligible := fun _ _ => true, pxEligible := fun _ _ => true,
    messageTopic := fun _ _ => true, key := fun _ => 0,
    knownPeers := [0], highDegree := 1 }
  (sequential := true)

end Libp2p.Routing
