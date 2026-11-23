module

public import Libp2p.ScoreHistory
public import Libp2p.TemporalSafety
public import Libp2p.Proof

/-!
Safety obligations of `Libp2p.ScoreHistory`, proved against the actual
`Libp2p.TemporalRetention` reachable states and the verified numerical score
operations. Nothing here claims causal network authorization, first/near-first
eligibility, mesh-time measurement, clock scheduling, or a per-peer connection
limit.
-/

@[expose] public section

@[expose] public section

namespace Libp2p.ScoreHistory

open Libp2p.TemporalRetention

variable {Peer Generation Topic : Type}

/-! ## Initialization -/

section Init

variable
  [Inhabited Peer] [Inhabited Generation] [Inhabited (ScoreState Topic)] [DecidableEq Topic]
  (t : Theory Peer Generation Topic)

/-- Wrapper initialization is exactly Retention initialization. -/
theorem init_facts {st : RState Peer Generation Topic}
    (h : (system t).init t st) :
    st.now = 0 ∧ (∀ g, st.currentHistory g = ScoreState.initial) ∧
    (∀ g, st.live g = false ∧ st.allocated g = false ∧ st.authenticated g = false ∧
      st.callbackAuthority g = false ∧ st.online (t.peerOf g) = false) ∧
    (∀ p, st.retained p = false ∧ st.retainedHistory p = ScoreState.initial ∧
      st.expires p = 0) ∧
    st.connectEmitted = false ∧ st.restored = false := by
  unfold system retSystem at h
  simp only [relationalTransitionSystem, Init, nextSimp, IsSubStateOf.setIn, IsSubStateOf.getFrom,
    IsSubReaderOf.readFrom, State.ext_iff, funext_iff, toRetention] at h
  have hi : (toRetention t).initialHistory = ScoreState.initial := rfl
  grind

end Init

/-! ## Exact per-effect characterizations -/

section Effects

variable
  [Inhabited Peer] [Inhabited Generation] [Inhabited (ScoreState Topic)] [DecidableEq Topic]
  {t : Theory Peer Generation Topic} {st next : RState Peer Generation Topic}

/-- Exact effect of the real `updateLiveHistory` transition. -/
theorem retention_updateLiveHistory_effect {g : Generation} {history : ScoreState Topic}
    (h : (retSystem t).tr (toRetention t) st (.updateLiveHistory g history) next) :
    st.live g = true ∧ next.currentHistory g = history ∧ next.now = st.now ∧
    next.connectEmitted = false ∧ next.restored = st.restored ∧ next.allocated = st.allocated ∧
    next.live = st.live ∧ next.online = st.online ∧ next.authenticated = st.authenticated ∧
    next.callbackAuthority = st.callbackAuthority ∧ next.retained = st.retained ∧
    next.retainedHistory = st.retainedHistory ∧ next.expires = st.expires ∧
    (∀ x, x = g ∨ next.currentHistory x = st.currentHistory x) := by
  simp only [retSystem, relationalTransitionSystem, Next, NextAct, nextSimp, State.ext_iff,
    funext_iff] at h
  grind

/-- Wrapper topic updates compute the exact fold over the real owner history. -/
theorem updateTopics_effect {g : Generation} {topic : Topic} {updates : List TopicScoreUpdate}
    (h : Tr t st next (.updateTopics g topic updates)) :
    st.live g = true ∧
    next.currentHistory g = updateTopicsScore (st.currentHistory g) t.config topic updates ∧
    next.now = st.now ∧ next.connectEmitted = false ∧ next.restored = st.restored ∧
    next.allocated = st.allocated ∧ next.live = st.live ∧ next.online = st.online ∧
    next.authenticated = st.authenticated ∧ next.callbackAuthority = st.callbackAuthority ∧
    next.retained = st.retained ∧ next.retainedHistory = st.retainedHistory ∧
    next.expires = st.expires ∧
    (∀ x, x = g ∨ next.currentHistory x = st.currentHistory x) :=
  retention_updateLiveHistory_effect h

/-- Live decay is the verified exact `ScoreState.decay` of the owner history. -/
theorem decayLive_effect {g : Generation} (h : Tr t st next (.decayLive g)) :
    st.live g = true ∧
    next.currentHistory g = ScoreState.decay (st.currentHistory g) t.config ∧
    next.now = st.now ∧ next.connectEmitted = false ∧ next.restored = st.restored ∧
    next.allocated = st.allocated ∧ next.live = st.live ∧ next.online = st.online ∧
    next.authenticated = st.authenticated ∧ next.callbackAuthority = st.callbackAuthority ∧
    next.retained = st.retained ∧ next.retainedHistory = st.retainedHistory ∧
    next.expires = st.expires ∧
    (∀ x, x = g ∨ next.currentHistory x = st.currentHistory x) :=
  retention_updateLiveHistory_effect h

/-- Application-supplied scores keep their sign freedom; nothing is clipped. -/
theorem setApplication_effect {g : Generation} {value : Rat}
    (h : Tr t st next (.setApplication g value)) :
    st.live g = true ∧
    next.currentHistory g = applicationScored (st.currentHistory g) value ∧
    next.now = st.now ∧ next.connectEmitted = false ∧ next.restored = st.restored ∧
    next.allocated = st.allocated ∧ next.live = st.live ∧ next.online = st.online ∧
    next.authenticated = st.authenticated ∧ next.callbackAuthority = st.callbackAuthority ∧
    next.retained = st.retained ∧ next.retainedHistory = st.retainedHistory ∧
    next.expires = st.expires ∧
    (∀ x, x = g ∨ next.currentHistory x = st.currentHistory x) :=
  retention_updateLiveHistory_effect h

/-- IP colocation counts are natural numbers updated exactly. -/
theorem setIPCount_effect {g : Generation} {count : Nat}
    (h : Tr t st next (.setIPCount g count)) :
    st.live g = true ∧
    next.currentHistory g = ipCounted (st.currentHistory g) count ∧
    next.now = st.now ∧ next.connectEmitted = false ∧ next.restored = st.restored ∧
    next.allocated = st.allocated ∧ next.live = st.live ∧ next.online = st.online ∧
    next.authenticated = st.authenticated ∧ next.callbackAuthority = st.callbackAuthority ∧
    next.retained = st.retained ∧ next.retainedHistory = st.retainedHistory ∧
    next.expires = st.expires ∧
    (∀ x, x = g ∨ next.currentHistory x = st.currentHistory x) :=
  retention_updateLiveHistory_effect h

/--
An authorized P7 cause is exactly one unit increment of the raw behavioral
counter; an unauthorized cause changes no state at all.
-/
theorem penalize_effect {g : Generation} {authorized : Bool}
    (h : Tr t st next (.penalize g authorized)) :
    (authorized = true →
      st.live g = true ∧ next.currentHistory g = penalized (st.currentHistory g) ∧
      next.now = st.now ∧ next.connectEmitted = false ∧ next.restored = st.restored ∧
      next.allocated = st.allocated ∧ next.live = st.live ∧ next.online = st.online ∧
      next.authenticated = st.authenticated ∧ next.callbackAuthority = st.callbackAuthority ∧
      next.retained = st.retained ∧ next.retainedHistory = st.retainedHistory ∧
      next.expires = st.expires ∧
      (∀ x, x = g ∨ next.currentHistory x = st.currentHistory x)) ∧
    (authorized = false → next = st) := by
  unfold Tr at h
  cases authorized with
  | true => exact ⟨fun _ => retention_updateLiveHistory_effect h,
      fun hf => Bool.noConfusion hf⟩
  | false => exact ⟨fun hf => Bool.noConfusion hf, fun _ => h⟩

/-- Exact decayed field values of a live-decayed score state. -/
theorem scoreState_decay_fields (s : ScoreState Topic) (c : ScoreConfig Topic) (u : Topic) :
    (ScoreState.decay s c).topics u =
      { s.topics u with
        first := Libp2p.decay (s.topics u).first (c.topicParams u).firstDecay
          c.globalParams.decayCutoff
        mesh := Libp2p.decay (s.topics u).mesh (c.topicParams u).meshDecay
          c.globalParams.decayCutoff
        failure := Libp2p.decay (s.topics u).failure (c.topicParams u).failureDecay
          c.globalParams.decayCutoff
        invalid := Libp2p.decay (s.topics u).invalid (c.topicParams u).invalidDecay
          c.globalParams.decayCutoff } ∧
    (ScoreState.decay s c).peer.behavior =
      Libp2p.decay s.peer.behavior c.globalParams.behaviorDecay c.globalParams.decayCutoff ∧
    (ScoreState.decay s c).peer.appScore = s.peer.appScore ∧
    (ScoreState.decay s c).peer.ipCount = s.peer.ipCount ∧
    ((ScoreState.decay s c).topics u).meshTime = (s.topics u).meshTime :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem applicationScored_fields (s : ScoreState Topic) (value : Rat) :
    (applicationScored s value).peer.appScore = value ∧
    (applicationScored s value).peer.behavior = s.peer.behavior ∧
    (applicationScored s value).peer.ipCount = s.peer.ipCount ∧
    (applicationScored s value).topics = s.topics :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem ipCounted_fields (s : ScoreState Topic) (count : Nat) :
    (ipCounted s count).peer.ipCount = count ∧
    (ipCounted s count).peer.appScore = s.peer.appScore ∧
    (ipCounted s count).peer.behavior = s.peer.behavior ∧
    (ipCounted s count).topics = s.topics :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem penalized_fields (s : ScoreState Topic) :
    (penalized s).peer.behavior = s.peer.behavior + 1 ∧
    (penalized s).peer.appScore = s.peer.appScore ∧
    (penalized s).peer.ipCount = s.peer.ipCount ∧
    (penalized s).topics = s.topics :=
  ⟨rfl, rfl, rfl, rfl⟩

/--
The P7 parameter exposure: after one authorized cause the raw counter is the
old value plus one, so its squared-weight contribution is exactly
`behaviorWeight * squaredPenalty (old + 1)`, positioned in `totalScore` by the
existing `PeerCounters` encoding.
-/
theorem penalized_p7_parameter (s : ScoreState Topic) :
    (penalized s).peer.behavior = s.peer.behavior + 1 ∧
    Libp2p.squaredPenalty (penalized s).peer.behavior =
      (s.peer.behavior + 1) * (s.peer.behavior + 1) :=
  ⟨rfl, by rw [show (penalized s).peer.behavior = s.peer.behavior + 1 from rfl,
    Libp2p.squaredPenalty_eq_mul]⟩

theorem advance_effect {m : Nat} (h : Tr t st next (.advance m)) :
    next.now = m ∧ next.connectEmitted = false ∧ next.restored = st.restored ∧
    next.allocated = st.allocated ∧ next.live = st.live ∧ next.online = st.online ∧
    next.authenticated = st.authenticated ∧ next.callbackAuthority = st.callbackAuthority ∧
    next.retained = st.retained ∧ next.retainedHistory = st.retainedHistory ∧
    next.expires = st.expires ∧ next.currentHistory = st.currentHistory := by
  unfold Tr at h
  simp only [retSystem, relationalTransitionSystem, Next, NextAct, nextSimp, State.ext_iff,
    funext_iff, toRetention] at h
  grind

theorem authenticate_effect {g : Generation} (h : Tr t st next (.authenticate g)) :
    st.live g = true ∧ next.authenticated g = true ∧ next.now = st.now ∧
    next.connectEmitted = false ∧ next.restored = st.restored ∧ next.allocated = st.allocated ∧
    next.live = st.live ∧ next.online = st.online ∧
    next.callbackAuthority = st.callbackAuthority ∧ next.retained = st.retained ∧
    next.retainedHistory = st.retainedHistory ∧ next.expires = st.expires ∧
    next.currentHistory = st.currentHistory ∧
    (∀ x, x = g ∨ next.authenticated x = st.authenticated x) := by
  unfold Tr at h
  simp only [retSystem, relationalTransitionSystem, Next, NextAct, nextSimp, State.ext_iff,
    funext_iff] at h
  grind

theorem authorizeCallbacks_effect {g : Generation} (h : Tr t st next (.authorizeCallbacks g)) :
    st.live g = true ∧ st.authenticated g = true ∧ next.callbackAuthority g = true ∧
    next.now = st.now ∧ next.connectEmitted = false ∧ next.restored = st.restored ∧
    next.allocated = st.allocated ∧ next.live = st.live ∧ next.online = st.online ∧
    next.retained = st.retained ∧ next.retainedHistory = st.retainedHistory ∧
    next.expires = st.expires ∧ next.currentHistory = st.currentHistory ∧
    (∀ x, x = g ∨ next.authenticated x = st.authenticated x) ∧
    (∀ x, x = g ∨ next.callbackAuthority x = st.callbackAuthority x) := by
  unfold Tr at h
  simp only [retSystem, relationalTransitionSystem, Next, NextAct, nextSimp, State.ext_iff,
    funext_iff] at h
  grind

/--
Incoming connection of a listed generation through the real `connect`: exact
freshness preconditions, resulting fields, frames, and both restore branches.
-/
theorem connect_effect {g : Generation} {keep : Bool}
    (h : Tr t st next (.connect g keep)) :
    (st.allocated g = false ∧ st.online (t.peerOf g) = false) ∧
    (next.allocated g = true ∧ next.live g = true ∧ next.online (t.peerOf g) = true ∧
      next.authenticated g = false ∧ next.callbackAuthority g = false ∧
      next.connectEmitted = true ∧ next.retained (t.peerOf g) = false ∧
      next.lastSession = g ∧ next.lastOrigin = st.retainedFrom (t.peerOf g) ∧
      next.historyAtConnect = st.retainedHistory (t.peerOf g) ∧
      next.deadlineAtConnect = st.expires (t.peerOf g) ∧
      next.existedAtConnect = st.retained (t.peerOf g) ∧ next.now = st.now) ∧
    ((∀ x, x = g ∨ next.live x = st.live x) ∧
     (∀ p, p = t.peerOf g ∨ next.online p = st.online p) ∧
     (∀ p, p = t.peerOf g ∨ next.retained p = st.retained p) ∧
     next.retainedHistory = st.retainedHistory ∧ next.retainedFrom = st.retainedFrom ∧
     next.expires = st.expires ∧
     (∀ x, x = g ∨ next.currentHistory x = st.currentHistory x) ∧
     (∀ x, x = g ∨ next.authenticated x = st.authenticated x) ∧
     (∀ x, x = g ∨ next.callbackAuthority x = st.callbackAuthority x)) ∧
    ((st.retained (t.peerOf g) = true ∧ (st.now < st.expires (t.peerOf g) ∨ keep = true) →
       next.currentHistory g = st.retainedHistory (t.peerOf g) ∧ next.restored = true) ∧
     (¬(st.retained (t.peerOf g) = true ∧ (st.now < st.expires (t.peerOf g) ∨ keep = true)) →
       next.currentHistory g = ScoreState.initial ∧ next.restored = false)) := by
  unfold Tr at h
  obtain ⟨_, step⟩ := h
  simp only [retSystem, relationalTransitionSystem, Next, NextAct, nextSimp, State.ext_iff,
    funext_iff] at step
  have hi : (toRetention t).initialHistory = ScoreState.initial := rfl
  have hpe : (toRetention t).peerOf = t.peerOf := rfl
  rcases step with ⟨pre1, pre2, branch⟩
  split at branch
  · grind
  · grind

/--
Within the retained lifetime the current same-peer history must be restored,
through the actual `connect` action.
-/
theorem connect_restores_within_lifetime {g : Generation} {keep : Bool}
    (h : Tr t st next (.connect g keep)) (held : st.retained (t.peerOf g) = true)
    (within : st.now < st.expires (t.peerOf g)) :
    next.restored = true ∧ next.currentHistory g = st.retainedHistory (t.peerOf g) ∧
    next.live g = true ∧ next.authenticated g = false ∧ next.callbackAuthority g = false ∧
    next.connectEmitted = true := by
  obtain ⟨_, core, _, branches⟩ := connect_effect h
  have branch := branches.1 ⟨held, Or.inl within⟩
  exact ⟨branch.2, branch.1, core.2.1, core.2.2.2.1, core.2.2.2.2.1, core.2.2.2.2.2.1⟩

/--
A reconnecting peer inherits no authentication or callback authority, whatever
history is restored.
-/
theorem connect_no_inherited_authority {g : Generation} {keep : Bool}
    (h : Tr t st next (.connect g keep)) :
    next.authenticated g = false ∧ next.callbackAuthority g = false :=
  ⟨(connect_effect h).2.1.2.2.2.1, (connect_effect h).2.1.2.2.2.2.1⟩

/--
Outgoing disconnection stores the exact current owner history with a deadline
in the same natural duration unit as `config.globalParams.retainScore`.
-/
theorem disconnect_effect {g : Generation} (h : Tr t st next (.disconnect g)) :
    st.live g = true ∧
    (next.retained (t.peerOf g) = true ∧ next.retainedHistory (t.peerOf g) = st.currentHistory g ∧
      next.retainedFrom (t.peerOf g) = g ∧
      next.expires (t.peerOf g) = st.now + t.config.globalParams.retainScore) ∧
    (next.live g = false ∧ next.online (t.peerOf g) = false ∧
      next.authenticated g = false ∧ next.callbackAuthority g = false ∧
      next.connectEmitted = false ∧ next.restored = st.restored ∧ next.now = st.now ∧
      next.allocated = st.allocated ∧ next.currentHistory = st.currentHistory) ∧
    ((∀ x, x = g ∨ next.live x = st.live x) ∧
     (∀ x, x = g ∨ next.authenticated x = st.authenticated x) ∧
     (∀ x, x = g ∨ next.callbackAuthority x = st.callbackAuthority x) ∧
     (∀ p, p = t.peerOf g ∨ (next.online p = st.online p ∧ next.retained p = st.retained p ∧
        next.retainedHistory p = st.retainedHistory p ∧ next.expires p = st.expires p))) := by
  unfold Tr at h
  simp only [retSystem, relationalTransitionSystem, Next, NextAct, nextSimp, State.ext_iff,
    funext_iff, toRetention] at h
  grind

/-- The exact RetainScore unit correspondence at disconnection. -/
theorem disconnect_retain_score_correspondence {g : Generation}
    (h : Tr t st next (.disconnect g)) :
    next.expires (t.peerOf g) = st.now + t.config.globalParams.retainScore :=
  (disconnect_effect h).2.1.2.2.2

/-- Exact retained decay through the verified decay function. -/
theorem decayRetained_effect {p : Peer} (h : Tr t st next (.decayRetained p)) :
    st.retained p = true ∧
    next.retainedHistory p = ScoreState.decay (st.retainedHistory p) t.config ∧
    (next.now = st.now ∧ next.connectEmitted = false ∧ next.restored = st.restored ∧
      next.allocated = st.allocated ∧ next.live = st.live ∧ next.online = st.online ∧
      next.authenticated = st.authenticated ∧ next.callbackAuthority = st.callbackAuthority ∧
      next.retained = st.retained ∧ next.retainedFrom = st.retainedFrom ∧
      next.expires = st.expires ∧ next.currentHistory = st.currentHistory) ∧
    (∀ x, x = p ∨ next.retainedHistory x = st.retainedHistory x) := by
  unfold Tr at h
  simp only [retSystem, relationalTransitionSystem, Next, NextAct, nextSimp, State.ext_iff,
    funext_iff, toRetention] at h
  grind

/--
Post-expiry reconnect choice stays with the real model: with the peer's
history retained past its deadline, `keepAfterLifetime = true` restores the
stored history while `keepAfterLifetime = false` starts from the initial
score state, with no invented discard policy.
-/
theorem connect_post_expiry_choices {g : Generation} {n1 n2 : RState Peer Generation Topic}
    (h1 : Tr t st n1 (.connect g true)) (h2 : Tr t st n2 (.connect g false))
    (held : st.retained (t.peerOf g) = true) (expired : ¬ st.now < st.expires (t.peerOf g)) :
    (n1.restored = true ∧ n1.currentHistory g = st.retainedHistory (t.peerOf g)) ∧
    (n2.restored = false ∧ n2.currentHistory g = ScoreState.initial) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨_, _, _, branches⟩ := connect_effect h1
    exact ⟨(branches.1 ⟨held, Or.inr rfl⟩).2, (branches.1 ⟨held, Or.inr rfl⟩).1⟩
  · obtain ⟨_, _, _, branches⟩ := connect_effect h2
    exact ⟨(branches.2 (fun hcon => expired (hcon.2.resolve_right (by decide)))).2,
      (branches.2 (fun hcon => expired (hcon.2.resolve_right (by decide)))).1⟩

end Effects

/-! ## Numerical operation validity and frames -/

section ScoreOps

theorem updateTopicsScore_valid {Topic : Type} [DecidableEq Topic] (c : ScoreConfig Topic)
    (hc : c.Valid) (t0 : Topic) : ∀ (updates : List TopicScoreUpdate) (s : ScoreState Topic),
    s.Valid c → (updateTopicsScore s c t0 updates).Valid c := by
  intro updates
  induction updates with
  | nil => intro s hs; exact hs
  | cons update updates ih =>
    intro s hs
    simp only [updateTopicsScore, List.foldl_cons]
    exact ih (Libp2p.ScoreState.updateTopic s c t0 update)
      (Libp2p.ScoreState.updateTopic_valid s c t0 update hs hc)

theorem updateTopicsScore_frame {Topic : Type} [DecidableEq Topic] (c : ScoreConfig Topic)
    (t0 other : Topic) (hne : other ≠ t0) : ∀ (updates : List TopicScoreUpdate)
    (s : ScoreState Topic),
    (updateTopicsScore s c t0 updates).topics other = s.topics other ∧
    (updateTopicsScore s c t0 updates).peer = s.peer := by
  intro updates
  induction updates with
  | nil => intro s; exact ⟨rfl, rfl⟩
  | cons update updates ih =>
    intro s
    have hs := Libp2p.ScoreState.updateTopic_frame s c t0 other update hne
    obtain ⟨hist', peer'⟩ := ih (Libp2p.ScoreState.updateTopic s c t0 update)
    simp only [updateTopicsScore, List.foldl_cons]
    exact ⟨hist' ▸ hs.1, peer' ▸ hs.2⟩

theorem applicationScored_valid {Topic : Type} (c : ScoreConfig Topic) (s : ScoreState Topic)
    (value : Rat) (hs : s.Valid c) : (applicationScored s value).Valid c :=
  ⟨hs.topics, hs.peer⟩

theorem ipCounted_valid {Topic : Type} (c : ScoreConfig Topic) (s : ScoreState Topic)
    (count : Nat) (hs : s.Valid c) : (ipCounted s count).Valid c :=
  ⟨hs.topics, hs.peer⟩

theorem penalized_valid {Topic : Type} (c : ScoreConfig Topic) (s : ScoreState Topic)
    (hs : s.Valid c) : (penalized s).Valid c := by
  exact ⟨hs.topics, Libp2p.PeerCounters.penalize_valid s.peer 1 hs.peer (by decide)⟩

theorem scoreState_decay_valid {Topic : Type} (c : ScoreConfig Topic) (hc : c.Valid)
    (s : ScoreState Topic) (hs : s.Valid c) : (ScoreState.decay s c).Valid c :=
  Libp2p.ScoreState.decay_valid s c hs hc

end ScoreOps


end Libp2p.ScoreHistory
