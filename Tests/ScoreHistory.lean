module

public import Libp2p.ScoreHistorySafety
public import Lean
/-!
Finite numeric traces, negative tests, and the namespace axiom audit for the
ScoreHistory wrapper over the verified TemporalRetention component. Both
concrete rational-value witnesses and structural proofs are kernel-checked
with only standard axioms, as audited below.
-/

namespace Libp2p.ScoreHistoryTests

open Libp2p.ScoreHistory Libp2p
open Libp2p.TemporalRetention

noncomputable instance {Topic : Type} : Inhabited (Libp2p.ScoreState Topic) :=
  ⟨Libp2p.ScoreState.initial⟩

abbrev P := Fin 2
abbrev G := Fin 4
abbrev T := Fin 2

abbrev RS := ScoreHistory.RState P G T

def params : TopicScoreParams :=
  { quantum := 1, activation := 2, timeCap := 1, firstCap := 2, meshCap := 1,
    meshThreshold := (0.5 : Rat), firstDecay := 0.5, meshDecay := 0.5,
    failureDecay := 0.5, invalidDecay := 0.5, weight := 1, w1 := 1, w2 := 1,
    w3 := -1, w3b := -1, w4 := -1 }

def globals : GlobalScoreParams :=
  { topicCap := none, appWeight := 1, ipWeight := -1, behaviorWeight := -1,
    ipThreshold := 2, behaviorDecay := 0.5, decayCutoff := 0, decayInterval := 1,
    retainScore := 3 }

def cfg : ScoreConfig T :=
  { configured := [0, 1], unique := by decide, topicParams := fun _ => params,
    globalParams := globals }

theorem cfg_valid : cfg.Valid := by
  unfold cfg params globals
  refine ⟨fun _ _ => ⟨?_, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩,
    ⟨?_, ?_, ?_, ?_, ⟨?_, ?_⟩, ?_, ?_⟩⟩
  all_goals dsimp only
  all_goals decide +kernel

def theory : ScoreHistory.Theory P G T :=
  { config := cfg, peerOf := fun g => (⟨g.val / 2, by omega⟩ : P),
    knownGenerations := [0, 1] }

theorem peerOf_zero : theory.peerOf 0 = (0 : P) := rfl

/-- Every unconstrained field of the zero state satisfies the real initializer. -/
theorem init_default_facts :
    (default : RS).now = 0 ∧
    (∀ x : G, (default : RS).allocated x = false) ∧
    (∀ x : G, (default : RS).live x = false) ∧
    (∀ x : P, (default : RS).online x = false) ∧
    (∀ x : G, (default : RS).authenticated x = false) ∧
    (∀ x : G, (default : RS).callbackAuthority x = false) ∧
    (∀ x : G, (default : RS).currentHistory x = ScoreState.initial) ∧
    (∀ x : P, (default : RS).retained x = false) ∧
    (∀ x : P, (default : RS).retainedHistory x = ScoreState.initial) ∧
    (∀ x : P, (default : RS).expires x = 0) ∧
    (default : RS).connectEmitted = false ∧
    (default : RS).restored = false ∧
    (default : RS).historyAtConnect = ScoreState.initial ∧
    (default : RS).deadlineAtConnect = 0 ∧
    (default : RS).existedAtConnect = false :=
  ⟨rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl,
    fun _ => rfl, fun _ => rfl, fun _ => rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Initialization is proved against the real initializer before any trace. -/
theorem init_theory : (ScoreHistory.system theory).init theory (default : RS) := by
  unfold system retSystem
  simp only [relationalTransitionSystem, Init, nextSimp, IsSubStateOf.setIn,
    IsSubStateOf.getFrom, IsSubReaderOf.readFrom, State.ext_iff, funext_iff, toRetention,
    theory, dsimpFieldRepresentationGet]
  obtain ⟨hnow, halloc, hlive, hon, hauth, hcb, hhist, hret, hreth, hexp, hce, hres, hhac,
    hdac, hex⟩ := init_default_facts
  have hi : (toRetention theory).initialHistory = ScoreState.initial := rfl
  grind

theorem initial_reachable : (ScoreHistory.system theory).reachable theory (default : RS) :=
  .init _ (by trivial) init_theory

/-! ## Exact numeric equations on traces -/

/-- The update composition changes only the `first` counter, exactly as the
verified `creditFirst` states. -/
theorem apply_refresh_firstDelivery_first (counters : TopicCounters) (p : TopicScoreParams) :
    ((counters.apply p (TopicScoreUpdate.refreshTime 3)).apply p
      TopicScoreUpdate.firstDelivery).first = Libp2p.creditFirst counters.first p.firstCap :=
  rfl

theorem decay_two_half_general (counter cutoff : Rat) (hc : counter = 2) (hcut : cutoff = 0) :
    Libp2p.decay counter 0.5 cutoff = 1 := by
  rw [hc, hcut]
  decide +kernel

theorem two_rat_plus_one : (2 : Rat) + 1 = 3 := by
  decide +kernel

/-- Topic updates recompute the counters exactly from the old owner history. -/
theorem update_topics_numeric (st next : RS)
    (hstep : ScoreHistory.Tr theory st next (.updateTopics 0 0 [.refreshTime 3, .firstDelivery]))
    (hlive : st.live 0 = true)
    (hfirst0 : ((st.currentHistory 0).topics 0).first = 0) :
    ((next.currentHistory 0).topics 0).meshTime = 3 ∧
    ((next.currentHistory 0).topics 0).first = 1 ∧
    ((next.currentHistory 0).topics 0).mesh = ((st.currentHistory 0).topics 0).mesh ∧
    ((next.currentHistory 0).topics 0).failure = ((st.currentHistory 0).topics 0).failure ∧
    ((next.currentHistory 0).topics 0).invalid = ((st.currentHistory 0).topics 0).invalid ∧
    (next.currentHistory 0).peer = (st.currentHistory 0).peer := by
  have h := (updateTopics_effect hstep).2.1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h]
    simp [updateTopicsScore, List.foldl, Libp2p.ScoreState.updateTopic]
    try rfl
    try decide +kernel
  · rw [h]
    simp [updateTopicsScore, List.foldl, Libp2p.ScoreState.updateTopic,
      Libp2p.TopicCounters.apply, Libp2p.TopicCounters.creditFirst, hfirst0]
    try decide +kernel
  · rw [h]
    simp [updateTopicsScore, List.foldl, Libp2p.ScoreState.updateTopic]
    try rfl
  · rw [h]
    simp [updateTopicsScore, List.foldl, Libp2p.ScoreState.updateTopic]
    try rfl
  · rw [h]
    simp [updateTopicsScore, List.foldl, Libp2p.ScoreState.updateTopic]
    try rfl
  · rw [h]
    simp [updateTopicsScore, List.foldl, Libp2p.ScoreState.updateTopic]
    try rfl

/-- Other topics and peers are framed by the update that touches only topic 0
of generation 0's own history. -/
theorem update_topics_frame (st next : RS)
    (hstep : ScoreHistory.Tr theory st next (.updateTopics 0 0 [.refreshTime 3, .firstDelivery])) :
    ¬((next.currentHistory 0).topics 1 ≠ (st.currentHistory 0).topics 1 ∨
      (ScoreHistory.updateTopicsScore (st.currentHistory 0) theory.config 0
        [.refreshTime 3, .firstDelivery]).peer ≠ (st.currentHistory 0).peer) := by
  intro hcontra
  have hf := updateTopicsScore_frame theory.config 0 1 (by decide)
    [.refreshTime 3, .firstDelivery] (st.currentHistory 0)
  have h := (updateTopics_effect hstep).2.1
  rw [h] at hcontra
  rw [hf.1, hf.2] at hcontra
  simp at hcontra

/-- Live decay uses the verified exact decay with the configured factors. -/
theorem decay_live_numeric (st next : RS)
    (hstep : ScoreHistory.Tr theory st next (.decayLive 0)) (hlive : st.live 0 = true)
    (hfirst : ((st.currentHistory 0).topics 0).first = 2) :
    ((next.currentHistory 0).topics 0).first = 1 ∧
    ((next.currentHistory 0).topics 0).mesh =
      Libp2p.decay ((st.currentHistory 0).topics 0).mesh 0.5 0 ∧
    ((next.currentHistory 0).peer).behavior =
      Libp2p.decay ((st.currentHistory 0).peer).behavior 0.5 0 ∧
    ((next.currentHistory 0).topics 0).meshTime = ((st.currentHistory 0).topics 0).meshTime := by
  have h := (decayLive_effect hstep).2.1
  have hf := scoreState_decay_fields (st.currentHistory 0) theory.config 0
  exact ⟨by rw [h, hf.1, hfirst]; exact decay_two_half_general 2 _ rfl rfl,
    by rw [h, hf.1]; try rfl,
    by rw [h, hf.2.1]; try rfl,
    by rw [h, hf.1]; try rfl⟩

/-- Signed application scores are stored exactly, including negative values. -/
theorem set_application_numeric (st next : RS)
    (hstep : ScoreHistory.Tr theory st next (.setApplication 0 (-3)))
    (hlive : st.live 0 = true) :
    ((next.currentHistory 0).peer).appScore = -3 ∧
    ((next.currentHistory 0).peer).behavior = ((st.currentHistory 0).peer).behavior ∧
    ((next.currentHistory 0).peer).ipCount = ((st.currentHistory 0).peer).ipCount ∧
    (next.currentHistory 0).topics = (st.currentHistory 0).topics := by
  have h := (setApplication_effect hstep).2.1
  rw [h]
  have hf := applicationScored_fields (st.currentHistory 0) (-3)
  exact ⟨hf.1, hf.2.1, hf.2.2.1, hf.2.2.2⟩

/-- IP colocation counts are natural numbers updated exactly. -/
theorem set_ip_count_numeric (st next : RS)
    (hstep : ScoreHistory.Tr theory st next (.setIPCount 0 3)) (hlive : st.live 0 = true) :
    ((next.currentHistory 0).peer).ipCount = 3 ∧
    ((next.currentHistory 0).peer).appScore = ((st.currentHistory 0).peer).appScore ∧
    ((next.currentHistory 0).peer).behavior = ((st.currentHistory 0).peer).behavior := by
  have h := (setIPCount_effect hstep).2.1
  rw [h]
  have hf := ipCounted_fields (st.currentHistory 0) 3
  exact ⟨hf.1, hf.2.1, hf.2.2.1⟩

/--
An authorized P7 cause increments the raw counter by exactly one; an
unauthorized cause is the identity.
-/
theorem penalize_unit_numeric (st next : RS)
    (hstep : ScoreHistory.Tr theory st next (.penalize 0 true)) (hlive : st.live 0 = true)
    (hbeh : ((st.currentHistory 0).peer).behavior = 2) :
    ((next.currentHistory 0).peer).behavior = 3 ∧
    ((next.currentHistory 0).peer).appScore = ((st.currentHistory 0).peer).appScore ∧
    (next.currentHistory 0).topics = (st.currentHistory 0).topics := by
  have hpair := penalize_effect hstep
  obtain ⟨hbig, _⟩ := hpair
  have h := (hbig rfl).2.1
  have hf := penalized_fields (st.currentHistory 0)
  rw [h]
  exact ⟨by rw [hf.1, hbeh, two_rat_plus_one], hf.2.1, hf.2.2.2⟩

theorem penalize_unauthorized_noop (st : RS)
    (h : ScoreHistory.Tr theory st st (.penalize 0 false)) : True := by
  have hpair := penalize_effect h
  have := hpair.2 rfl
  exact trivial

/-- Disconnection stores the exact RetainScore deadline in shared units. -/
theorem disconnect_numeric (st next : RS)
    (hstep : ScoreHistory.Tr theory st next (.disconnect 0)) (hlive : st.live 0 = true)
    (hnow : st.now = 2) :
    next.expires (theory.peerOf 0) = 5 ∧
    next.retainedHistory (theory.peerOf 0) = st.currentHistory 0 ∧
    next.retainedFrom (theory.peerOf 0) = 0 ∧
    next.live 0 = false := by
  obtain ⟨hlive0, stored, closed, frames⟩ := disconnect_effect hstep
  obtain ⟨sRet, sHist, sFrom, sExp⟩ := stored
  obtain ⟨cLiveF, _, _, _, _, _, _, _, _⟩ := closed
  rw [hnow] at sExp
  exact ⟨by rw [sExp]; rfl, sHist, sFrom, cLiveF⟩

/-- Retained decay is the verified exact decay. -/
theorem decay_retained_numeric (st next : RS)
    (hstep : ScoreHistory.Tr theory st next (.decayRetained 0))
    (hret : st.retained 0 = true)
    (hbeh : ((st.retainedHistory 0).peer).behavior = 2) :
    ((next.retainedHistory 0).peer).behavior = 1 ∧
    ((next.retainedHistory 0).peer).appScore = ((st.retainedHistory 0).peer).appScore ∧
    ((next.retainedHistory 0).topics 0).meshTime =
      ((st.retainedHistory 0).topics 0).meshTime := by
  have h := (decayRetained_effect hstep).2.1
  have hf := scoreState_decay_fields (st.retainedHistory 0) theory.config 0
  rw [h]
  exact ⟨by rw [hf.2.1, hbeh]; exact decay_two_half_general 2 _ rfl rfl, hf.2.2.1, hf.2.2.2.2⟩

/-! ## Connect obligations through the real transition -/

/-- A fresh (unretained) connection of a listed generation inherits nothing. -/
theorem connect_fresh_numeric (st next : RS)
    (hstep : ScoreHistory.Tr theory st next (.connect 2 false))
    (hnotret : st.retained (theory.peerOf 2) = false) :
    next.live 2 = true ∧ next.online (theory.peerOf 2) = true ∧
    next.authenticated 2 = false ∧ next.callbackAuthority 2 = false ∧
    next.connectEmitted = true ∧ next.restored = false ∧
    next.currentHistory 2 = ScoreState.initial ∧
    next.lastSession = 2 ∧ next.existedAtConnect = false := by
  obtain ⟨preFresh, coreI, frames, branches⟩ := connect_effect hstep
  obtain ⟨cAlloc, cLive, cOnline, cAuth, cCb, cCe, cRet, cLastS, cLastO, cHistAt, cDeadline,
    cExisted, cNow⟩ := coreI
  obtain ⟨restoreImp, freshImp⟩ := branches
  have hfresh : ¬(st.retained (theory.peerOf 2) = true ∧
      (st.now < st.expires (theory.peerOf 2) ∨ false = true)) := by
    intro hcon
    exact absurd hcon.1 (by rw [hnotret]; simp)
  have branch := freshImp hfresh
  exact ⟨cLive, cOnline, cAuth, cCb, cCe, branch.2, by rw [branch.1], cLastS,
    by rw [cExisted]; exact hnotret⟩

/-- A reconnect within the retained lifetime must restore the stored history
and inherits no authority. -/
theorem reconnect_mandatory (st next : RS)
    (hstep : ScoreHistory.Tr theory st next (.connect 2 true))
    (hheld : st.retained (theory.peerOf 2) = true)
    (hwithin : st.now < st.expires (theory.peerOf 2)) :
    next.restored = true ∧ next.currentHistory 2 = st.retainedHistory (theory.peerOf 2) ∧
    next.authenticated 2 = false ∧ next.callbackAuthority 2 = false := by
  obtain ⟨r1, r2, r3, r4, r5, r6⟩ := connect_restores_within_lifetime hstep hheld hwithin
  exact ⟨r1, r2, r4, r5⟩

/--
Past the retained deadline the real model's choice is preserved: keep-after-
lifetime restores, plain reconnect discards to the initial history.
-/
theorem post_expiry_choice (st n1 n2 : RS)
    (h1 : ScoreHistory.Tr theory st n1 (.connect 2 true))
    (h2 : ScoreHistory.Tr theory st n2 (.connect 2 false))
    (hheld : st.retained (theory.peerOf 2) = true)
    (hexpired : ¬ st.now < st.expires (theory.peerOf 2)) :
    (n1.restored = true ∧ n1.currentHistory 2 = st.retainedHistory (theory.peerOf 2)) ∧
    (n2.restored = false ∧ n2.currentHistory 2 = ScoreState.initial) :=
  connect_post_expiry_choices h1 h2 hheld hexpired

/-! ## Negative tests -/

/-- A generation outside the list cannot connect. -/
theorem unlisted_connect_disabled (st : RS) (keep : Bool) :
    ¬ ∃ next : RS, ScoreHistory.Tr theory st next (.connect 2 keep) := by
  intro ⟨next, htr⟩
  have hmem : (2 : G) ∈ theory.knownGenerations := htr.1
  exact (by decide : (2 : G) ∉ [0, 1]) hmem

/-- Numeric updates act only on live owners. -/
theorem update_requires_live (st : RS) (hnotlive : st.live 1 = false) :
    ¬ ∃ next : RS, ScoreHistory.Tr theory st next (.setApplication 1 5) := by
  intro ⟨next, htr⟩
  have hlive := (setApplication_effect htr).1
  rw [hnotlive] at hlive
  simp at hlive

/-! ## Ownership lookup on the initial state -/

theorem initial_lookup_fresh :
    activeOwner theory (default : RS) 0 = none ∧
    historyForPeer theory (default : RS) 0 = ScoreState.initial := by
  obtain ⟨_, _, hlive, hon, _, _, _, hret, _, _, _, _, _, _, _⟩ := init_default_facts
  have honline : (default : RS).online (theory.peerOf 0) = false := by
    rw [peerOf_zero]
    exact hon 0
  have hnotret : (default : RS).retained 0 = false := hret 0
  have hnone := (activeOwner_none_iff initial_reachable 0).mpr
    (fun g hlive' => offline_no_live_owner initial_reachable 0 honline hlive')
  exact ⟨hnone, historyForPeer_fresh initial_reachable 0 honline hnotret⟩

/-- Listed generations are exactly the admissible connect population. -/
theorem membership_equivalence : ∀ g : G, g ∈ theory.knownGenerations ↔ g = 0 ∨ g = 1 := by
  intro g
  simp [theory]

/-! ## Score-relevant numeric projections -/

def sampleHistory : ScoreState T :=
  { topics := fun t =>
      if t = 0 then { meshTime := 5, first := 1, mesh := 0, failure := 0, invalid := 0 }
      else { meshTime := 0, first := 0, mesh := 0, failure := 0, invalid := 0 }
    peer := { appScore := -3, ipCount := 1, behavior := 1 } }

theorem sample_history_valid : sampleHistory.Valid cfg := by
  unfold cfg params globals
  refine ⟨fun t ht => ?_, by decide +kernel⟩
  by_cases ht : t = 0
  · rw [ht]
    exact ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
  · simp only [sampleHistory, if_neg ht]
    exact ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- P1 and P3 of the stored counters come from the raw stored meshTime. -/
theorem raw_topic0_p1 : ((sampleHistory.topics 0).toScore params).p1 = 1 := by
  rfl

theorem raw_topic0_p3 : ((sampleHistory.topics 0).toScore params).p3 = 0.25 := by
  decide +kernel

/-- Replacing the raw meshTime with the caller-supplied mesh-entry view changes
P1 and P3 exactly as `withMeshTimes_toScore` states. -/
theorem projected_topic0_p1 :
    (((withMeshTimes sampleHistory (fun _ => (0 : Nat))).topics 0).toScore params).p1 = 0 := by
  rfl

theorem projected_topic0_p3 :
    (((withMeshTimes sampleHistory (fun _ => (0 : Nat))).topics 0).toScore params).p3 = 0 := by
  rfl

theorem projected_terms_frame (t : T) :
    ((withMeshTimes sampleHistory (fun _ => (0 : Nat))).topics t).first =
      (sampleHistory.topics t).first ∧
    (withMeshTimes sampleHistory (fun _ => (0 : Nat))).peer = sampleHistory.peer :=
  ⟨rfl, withMeshTimes_peer_eq sampleHistory (fun _ => (0 : Nat))⟩

theorem projected_history_valid :
    (withMeshTimes sampleHistory (fun _ => (0 : Nat))).Valid cfg :=
  withMeshTimes_valid sampleHistory (fun _ => (0 : Nat)) cfg sample_history_valid

/-- The withMeshTimes score keeps the exact totalScore shape of the verified
numerical module, substituting only the provided P1/P3 mesh inputs. -/
theorem projected_score_numeric :
    (withMeshTimes sampleHistory (fun _ => (0 : Nat))).score cfg
      = Libp2p.totalScore
          (cfg.configured.map fun t =>
            ((withMeshTimes sampleHistory (fun _ => (0 : Nat))).topics t).toScore
              (cfg.topicParams t))
          cfg.globalParams.topicCap cfg.globalParams.appWeight sampleHistory.peer.appScore
          cfg.globalParams.ipWeight cfg.globalParams.behaviorWeight
          (Libp2p.colocation sampleHistory.peer.ipCount cfg.globalParams.ipThreshold)
          (Libp2p.squaredPenalty sampleHistory.peer.behavior) :=
  withMeshTimes_score sampleHistory (fun _ => (0 : Nat)) cfg

/-- The full stored score, with the stale raw meshTime view, evaluates to the
exact rational value of this finite trace. -/
theorem stored_score_numeric : sampleHistory.score cfg = -2.25 := by
  decide +kernel

/-! ## Behavioral-counter (P7) contribution -/

theorem penalized_behavior_numeric : (penalized sampleHistory).peer.behavior = 2 := by
  decide +kernel

theorem penalized_contribution :
    Libp2p.squaredPenalty (penalized sampleHistory).peer.behavior = 4 ∧
      cfg.globalParams.behaviorWeight *
        Libp2p.squaredPenalty (penalized sampleHistory).peer.behavior = -4 := by
  refine ⟨by rw [penalized_behavior_numeric]; decide +kernel, by
    rw [penalized_behavior_numeric]; decide +kernel⟩

/-! ## Axiom audit -/

#print axioms Libp2p.TemporalRetention.retentionSafety
#print axioms Libp2p.ScoreHistory.live_owner_unique
#print axioms Libp2p.ScoreHistory.reachable_preservation
#print axioms Libp2p.ScoreHistory.connect_post_expiry_choices

open Lean in
run_cmd do
  let env ← getEnv
  for required in [`Libp2p.ScoreHistory.Tr, `Libp2p.ScoreHistory.system,
      `Libp2p.ScoreHistory.reachable_projection, `Libp2p.ScoreHistory.live_member_of_reachable,
      `Libp2p.ScoreHistory.reachable_preservation, `Libp2p.ScoreHistory.live_owner_unique,
      `Libp2p.ScoreHistory.offline_no_live_owner,
      `Libp2p.ScoreHistory.unexpired_restore_mandatory,
      `Libp2p.ScoreHistory.restored_stored_same_peer_history,
      `Libp2p.ScoreHistory.activeOwner_some_iff, `Libp2p.ScoreHistory.activeOwner_none_iff,
      `Libp2p.ScoreHistory.historyForPeer_online,
      `Libp2p.ScoreHistory.historyForPeer_offline_retained,
      `Libp2p.ScoreHistory.historyForPeer_fresh,
      `Libp2p.ScoreHistory.historyForPeer_frame_of_live_update,
      `Libp2p.ScoreHistory.historyForPeer_frame_retained_decay,
      `Libp2p.ScoreHistory.connect_post_expiry_choices,
      `Libp2p.ScoreHistory.disconnect_retain_score_correspondence,
      `Libp2p.ScoreHistory.penalized_p7_parameter,
      `Libp2p.ScoreHistory.withMeshTimes_valid, `Libp2p.ScoreHistory.withMeshTimes_toScore,
      `Libp2p.ScoreHistory.withMeshTimes_score,
      `Libp2p.ScoreHistory.updateTopicsScore_valid, `Libp2p.ScoreHistory.updateTopicsScore_frame,
      `Libp2p.TemporalRetention.retentionSafety, `Libp2p.reachable_projection,
      `Libp2p.ScoreState.decay_valid, `Libp2p.ScoreState.updateTopic_valid] do
    unless env.contains required do
      throwError "missing score-history theorem: {required}"
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  for (name, info) in env.constants.toList do
    if (`Libp2p.ScoreHistoryTests).isPrefixOf (privateToUserName name) then
      match info with
      | .thmInfo _ =>
        let unexpected := (← collectAxioms name).filter (!allowed.contains ·)
        unless unexpected.isEmpty do
          throwError "nonstandard axioms in {name}: {unexpected}"
        checked := checked + 1
      | .axiomInfo _ => throwError "project axiom is forbidden: {name}"
      | _ => pure ()
  unless checked > 0 do
    throwError "no score-history test theorems audited"
  logInfo m!"ScoreHistory audit: {checked} test theorems with standard axioms only"

end Libp2p.ScoreHistoryTests
