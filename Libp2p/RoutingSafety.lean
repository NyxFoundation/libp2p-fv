module

public import Libp2p.Routing
public import Libp2p.Proof

public section
namespace Libp2p.Routing
open Classical

variable (peer topic message messageId snapshot : Type)
variable [Inhabited peer] [Inhabited topic] [Inhabited message]
variable [Inhabited messageId] [Inhabited snapshot]

local notation "RS" => State (FieldAbstractType peer topic message messageId snapshot)
local notation "RT" => Theory peer topic message messageId snapshot
local notation "sys" => relationalTransitionSystem peer topic message messageId snapshot

theorem routingSafety (th : RT) (st : RS) (reachable : (sys).reachable th st) :
    Invariants _ _ peer topic message messageId snapshot
      (FieldAbstractType peer topic message messageId snapshot) th st := by
  refine Veil.RelationalTransitionSystem.invariant_of_inductive
    («sys» := sys) ?_ ?_ th st reachable
  · intro th st ha ht
    dsimp only [relationalTransitionSystem, Init] at ht
    rw [← initializer.ext.derived_eq] at ht
    discharge_vcs initializer using ha, True.intro, ht
  · intro th st label next ha hi ht
    cases label <;> dsimp only [relationalTransitionSystem, Next, NextAct] at ht
    case refreshScores s => discharge_vcs refreshScores using ha, hi, ht
    case subscribe p t => discharge_vcs subscribe using ha, hi, ht
    case addFanout p t => discharge_vcs addFanout using ha, hi, ht
    case join t => discharge_vcs join using ha, hi, ht
    case leave t => discharge_vcs leave using ha, hi, ht
    case graft p t outbound => discharge_vcs graft using ha, hi, ht
    case localGraft p t => discharge_vcs localGraft using ha, hi, ht
    case heartbeat => discharge_vcs heartbeat using ha, hi, ht
    case prune p t => discharge_vcs prune using ha, hi, ht
    case expireBackoff p t => discharge_vcs expireBackoff using ha, hi, ht
    case idontwant p k honor => discharge_vcs idontwant using ha, hi, ht
    case expireSuppression p k => discharge_vcs expireSuppression using ha, hi, ht
    case replaceSession p clear => discharge_vcs replaceSession using ha, hi, ht
    case ignoredIdontwant p k => discharge_vcs ignoredIdontwant using ha, hi, ht
    case validatedRemote m => discharge_vcs validatedRemote using ha, hi, ht
    case validatedLocal m => discharge_vcs validatedLocal using ha, hi, ht
    case expirePublication k => discharge_vcs expirePublication using ha, hi, ht
    case forwardRemote p t m => discharge_vcs forwardRemote using ha, hi, ht
    case publish p t m => discharge_vcs publish using ha, hi, ht
    case referral sender referred => discharge_vcs referral using ha, hi, ht
    case authenticateReferral p checks => discharge_vcs authenticateReferral using ha, hi, ht

theorem initial_snapshot_coherent (th : RT) (st : RS) (h : (sys).init th st) :
    st.currentSnapshot = th.initialSnapshot := by
  simp only [relationalTransitionSystem, Init, nextSimp, IsSubStateOf.setIn,
    IsSubStateOf.getFrom, IsSubReaderOf.readFrom, State.ext_iff] at h
  grind

/-- Score changes preserve membership until a routing action, including heartbeat, acts. -/
theorem refresh_preserves_mesh (th : RT) (st next : RS) (s : snapshot)
    (h : (sys).tr th st (.refreshScores s) next) :
    next.mesh = st.mesh ∧ next.currentSnapshot = s ∧ next.heartbeatClean = false := by
  simp only [relationalTransitionSystem, Next, NextAct, nextSimp, State.ext_iff] at h
  grind

theorem graft_unknown_topic_noop (th : RT) (st next : RS) (p : peer) (t : topic)
    (outbound : Bool) (unknown : st.joined t = false)
    (h : (sys).tr th st (.graft p t outbound) next) : next = st := by
  simp only [relationalTransitionSystem, Next, NextAct, nextSimp] at h
  simp only [unknown, Bool.false_eq_true] at h
  exact h.symm

theorem ignored_idontwant_no_effect (th : RT) (st next : RS) (p : peer) (k : messageId)
    (h : (sys).tr th st (.ignoredIdontwant p k) next) : next = st := by
  simp only [relationalTransitionSystem, Next, NextAct, nextSimp] at h
  exact h.symm

theorem heartbeat_prunes_all_negative (th : RT) (st next : RS)
    (h : (sys).tr th st .heartbeat next) (p : peer) (t : topic) :
    next.mesh p t = (st.mesh p t && th.nonnegative st.currentSnapshot p) ∧
    (st.mesh p t = true → th.nonnegative st.currentSnapshot p = false →
      next.pruned p t = true ∧ next.backoff p t = true) := by
  simp only [relationalTransitionSystem, Next, NextAct, nextSimp, State.ext_iff, funext_iff] at h
  grind

theorem idontwant_peer_frame (th : RT) (st next : RS) (p other : peer) (k : messageId)
    (honor : Bool) (distinct : p ≠ other)
    (h : (sys).tr th st (.idontwant p k honor) next) (id : messageId) :
    next.suppressed other id = st.suppressed other id := by
  simp only [relationalTransitionSystem, Next, NextAct, nextSimp, State.ext_iff, funext_iff] at h
  grind

theorem idontwant_honored (th : RT) (st next : RS) (p : peer) (k : messageId)
    (h : (sys).tr th st (.idontwant p k true) next) : next.suppressed p k = true := by
  simp only [relationalTransitionSystem, Next, NextAct, nextSimp, State.ext_iff, funext_iff] at h
  grind

theorem suppression_blocks_colliding_candidate (th : RT) (st : RS) (p : peer)
    (t : topic) (first second : message) (sameId : th.key first = th.key second)
    (suppressed : st.suppressed p (th.key first) = true) (notExplicit : th.explicitPeer p = false) :
    ¬ ∃ next, (sys).tr th st (.forwardRemote p t second) next := by
  intro ⟨next, h⟩
  simp only [relationalTransitionSystem, Next, NextAct, nextSimp] at h
  grind

theorem session_replacement_clears_only_peer (th : RT) (st next : RS) (p : peer)
    (h : (sys).tr th st (.replaceSession p true) next) :
    (∀ k, next.suppressed p k = false) ∧
    (∀ other k, other ≠ p → next.suppressed other k = st.suppressed other k) := by
  simp only [relationalTransitionSystem, Next, NextAct, nextSimp, State.ext_iff, funext_iff] at h
  grind

theorem session_replacement_retention_noop (th : RT) (st next : RS) (p : peer)
    (h : (sys).tr th st (.replaceSession p false) next) : next = st := by
  simp only [relationalTransitionSystem, Next, NextAct, nextSimp] at h
  exact h.symm

theorem local_publication_remembers_id (th : RT) (st next : RS) (m : message)
    (h : (sys).tr th st (.validatedLocal m) next) : next.publishedId (th.key m) = true := by
  simp only [relationalTransitionSystem, Next, NextAct, nextSimp, State.ext_iff, funext_iff] at h
  grind

theorem local_echo_blocks_colliding_candidate (th : RT) (st : RS) (p : peer)
    (t : topic) (localMsg remoteMsg : message) (sameId : th.key localMsg = th.key remoteMsg)
    (published : st.publishedId (th.key localMsg) = true) :
    ¬ ∃ next, (sys).tr th st (.forwardRemote p t remoteMsg) next := by
  intro ⟨next, h⟩
  simp only [relationalTransitionSystem, Next, NextAct, nextSimp] at h
  grind

theorem publication_expiry_clears_id (th : RT) (st next : RS) (k : messageId)
    (h : (sys).tr th st (.expirePublication k) next) : next.publishedId k = false := by
  simp only [relationalTransitionSystem, Next, NextAct, nextSimp, State.ext_iff, funext_iff] at h
  grind

theorem publish_uses_current_score (th : RT) (st next : RS) (p : peer) (t : topic) (m : message)
    (h : (sys).tr th st (.publish p t m) next) :
    (th.explicitPeer p = true ∨ th.publishEligible st.currentSnapshot p = true) ∧
    next.publishSnapshot p m = st.currentSnapshot ∧ next.publishedId (th.key m) = true := by
  simp only [relationalTransitionSystem, Next, NextAct, nextSimp, State.ext_iff, funext_iff] at h
  grind

theorem px_uses_current_score (th : RT) (st next : RS) (sender referred : peer)
    (h : (sys).tr th st (.referral sender referred) next) :
    th.pxEligible st.currentSnapshot sender = true ∧ next.pxSource referred = sender ∧
    next.pxSnapshot referred = st.currentSnapshot := by
  simp only [relationalTransitionSystem, Next, NextAct, nextSimp, State.ext_iff, funext_iff] at h
  grind

theorem mesh_roster_exact (th : RT) (st : RS) (reachable : (sys).reachable th st)
    (t : topic) (p : peer) :
    p ∈ th.knownPeers.eraseDups.filter (fun q => st.mesh q t) ↔ st.mesh p t = true := by
  have safe := routingSafety peer topic message messageId snapshot th st reachable
  veil_simp +instances only [Invariants, invSimp, substateSimp, dsimpFieldRepresentationGet] at safe
  simp only [List.mem_filter, List.mem_eraseDups]
  constructor
  · exact And.right
  · intro member
    exact ⟨by grind, member⟩

theorem graft_new_member_gate (th : RT) (st next : RS) (p : peer) (t : topic)
    (outbound : Bool) (absent : st.mesh p t = false) (present : next.mesh p t = true)
    (h : (sys).tr th st (.graft p t outbound) next) :
    st.joined t = true ∧ th.explicitPeer p = false ∧ st.backoff p t = false ∧
    th.nonnegative st.currentSnapshot p = true ∧
    ((th.knownPeers.eraseDups.filter (fun q => st.mesh q t)).length < th.highDegree ∨ outbound = true) := by
  veil_simp +instances only [relationalTransitionSystem, Next, NextAct, nextSimp,
    meshDegree, substateSimp, dsimpFieldRepresentationGet, State.ext_iff, funext_iff] at h
  grind

theorem local_graft_uses_current_score (th : RT) (st next : RS) (p : peer) (t : topic)
    (h : (sys).tr th st (.localGraft p t) next) :
    st.joined t = true ∧ st.subscribed p t = true ∧ th.nonnegative st.currentSnapshot p = true ∧
    th.explicitPeer p = false ∧ st.backoff p t = false ∧ next.mesh p t = true := by
  simp only [relationalTransitionSystem, Next, NextAct, nextSimp, State.ext_iff, funext_iff] at h
  grind

theorem graft_rejects_ineligible (th : RT) (st next : RS) (p : peer) (t : topic)
    (outbound : Bool) (joined : st.joined t = true)
    (ineligible : th.explicitPeer p = true ∨ st.backoff p t = true ∨
      th.nonnegative st.currentSnapshot p = false)
    (h : (sys).tr th st (.graft p t outbound) next) :
    next.mesh p t = false ∧ next.pruned p t = true := by
  simp only [relationalTransitionSystem, Next, NextAct, nextSimp, State.ext_iff, funext_iff] at h
  grind

theorem join_promotes_current_eligible_fanout (th : RT) (st next : RS) (t : topic)
    (h : (sys).tr th st (.join t) next) (p : peer) :
    next.mesh p t = (st.fanout p t && th.nonnegative st.currentSnapshot p && !st.backoff p t) ∧
    next.fanout p t = false ∧
    (∀ other, other ≠ t → next.mesh p other = st.mesh p other) := by
  simp only [relationalTransitionSystem, Next, NextAct, nextSimp, State.ext_iff, funext_iff] at h
  grind

theorem leave_is_topic_scoped (th : RT) (st next : RS) (t : topic)
    (h : (sys).tr th st (.leave t) next) (p : peer) :
    next.mesh p t = false ∧ (st.mesh p t = true → next.pruned p t = true) ∧
    (∀ other, other ≠ t → next.mesh p other = st.mesh p other) := by
  simp only [relationalTransitionSystem, Next, NextAct, nextSimp, State.ext_iff, funext_iff] at h
  grind

#print axioms routingSafety
end Libp2p.Routing
