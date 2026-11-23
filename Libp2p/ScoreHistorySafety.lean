module

public import Libp2p.ScoreHistoryEffects

/-!
Reachability obligations, inherited Retention safety properties, constructive
owner lookup, effective-history frames, and the `withMeshTimes` projection for
`Libp2p.ScoreHistory`. Nothing here claims causal network authorization,
first/near-first eligibility, mesh-time measurement, clock scheduling, or a
per-peer connection limit.
-/

@[expose] public section

namespace Libp2p.ScoreHistory

open Libp2p.TemporalRetention

variable {Peer Generation Topic : Type}

/-! ## Reachable-state membership and stored-history validity -/

section Reachable

variable
  [Inhabited Peer] [Inhabited Generation] [Inhabited (ScoreState Topic)] [DecidableEq Topic]
  {t : Theory Peer Generation Topic} {st next : RState Peer Generation Topic}

/--
Every live generation was admitted through the wrapper's listed-generation
guard, so it belongs to `knownGenerations`.
-/
theorem live_member_of_reachable {st0 : RState Peer Generation Topic}
    (h : (system t).reachable t st0) :
    ∀ g, st0.live g = true → g ∈ t.knownGenerations := by
  induction h with
  | init state ha hinit =>
    obtain ⟨_, _, hlive, _, _, _⟩ := init_facts t hinit
    intro g hg
    rw [(hlive g).1] at hg
    simp at hg
  | step before after hreach hnext ih =>
    obtain ⟨label, htr⟩ := hnext
    cases label with
    | connect g keep =>
      have hstep : Tr t before after (.connect g keep) := htr
      obtain ⟨hmember, step⟩ := id hstep
      obtain ⟨_, core, frames, branches⟩ := connect_effect hstep
      intro g' hg'
      rcases frames.1 g' with heq | hframe
      · rw [heq]
        exact hmember
      · exact ih g' (by rw [← hframe]; exact hg')
    | disconnect g =>
      have hstep : Tr t before after (.disconnect g) := htr
      obtain ⟨hlive0, stored, closed, frames⟩ := disconnect_effect hstep
      intro g' hg'
      rcases frames.1 g' with heq | hframe
      · rw [heq, closed.1] at hg'
        simp at hg'
      · exact ih g' (by rw [← hframe]; exact hg')
    | updateTopics g topic updates =>
      obtain ⟨_, _, _, _, _, _, liveFn, _, _, _, _, _, _, _⟩ := updateTopics_effect htr
      intro g' hg'
      exact ih g' (by rw [← liveFn]; exact hg')
    | decayLive g =>
      obtain ⟨_, _, _, _, _, _, liveFn, _, _, _, _, _, _, _⟩ := decayLive_effect htr
      intro g' hg'
      exact ih g' (by rw [← liveFn]; exact hg')
    | setApplication g value =>
      obtain ⟨_, _, _, _, _, _, liveFn, _, _, _, _, _, _, _⟩ := setApplication_effect htr
      intro g' hg'
      exact ih g' (by rw [← liveFn]; exact hg')
    | setIPCount g count =>
      obtain ⟨_, _, _, _, _, _, liveFn, _, _, _, _, _, _, _⟩ := setIPCount_effect htr
      intro g' hg'
      exact ih g' (by rw [← liveFn]; exact hg')
    | penalize g authorized =>
      cases authorized with
      | true =>
        obtain ⟨_, _, _, _, _, _, liveFn, _, _, _, _, _, _, _⟩ :=
          retention_updateLiveHistory_effect htr
        intro g' hg'
        exact ih g' (by rw [← liveFn]; exact hg')
      | false =>
        have heq : after = before := htr
        subst heq
        exact ih
    | advance m =>
      obtain ⟨_, _, _, _, liveFn, _, _, _, _, _, _, _⟩ := advance_effect htr
      intro g' hg'
      exact ih g' (by rw [← liveFn]; exact hg')
    | authenticate g =>
      obtain ⟨_, _, _, _, _, _, liveFn, _, _, _, _, _, _, _⟩ := authenticate_effect htr
      intro g' hg'
      exact ih g' (by rw [← liveFn]; exact hg')
    | authorizeCallbacks g =>
      obtain ⟨_, _, _, _, _, _, _, liveFn, _, _, _, _, _, _, _⟩ := authorizeCallbacks_effect htr
      intro g' hg'
      exact ih g' (by rw [← liveFn]; exact hg')
    | decayRetained p =>
      obtain ⟨_, _, closed, _⟩ := decayRetained_effect htr
      obtain ⟨_, _, _, _, hliveFn, _, _, _, _, _, _, _⟩ := closed
      intro g' hg'
      exact ih g' (by rw [← hliveFn]; exact hg')

/--
Wrapper reachability preserves: every live generation is listed, every live
owner history satisfies `ScoreConfig.Valid`, and every stored retained history
satisfies `ScoreConfig.Valid`, assuming only that the configuration is legal.
-/
theorem reachable_preservation (hc : t.config.Valid) {st0 : RState Peer Generation Topic}
    (h : (system t).reachable t st0) :
    (∀ g, st0.live g = true → g ∈ t.knownGenerations) ∧
    (∀ g, st0.live g = true → (st0.currentHistory g).Valid t.config) ∧
    (∀ p, st0.retained p = true → (st0.retainedHistory p).Valid t.config) := by
  induction h with
  | init state ha hinit =>
    obtain ⟨_, hcur, hlive, hret, _, _⟩ := init_facts t hinit
    exact ⟨fun g hg => by rw [(hlive g).1] at hg; simp at hg,
      fun g hg => by rw [(hlive g).1] at hg; simp at hg,
      fun p hr => by rw [(hret p).1] at hr; simp at hr⟩
  | step before after hreach hnext ih =>
    obtain ⟨label, htr⟩ := hnext
    cases label with
    | connect g keep =>
      have hstep : Tr t before after (.connect g keep) := htr
      obtain ⟨hmember, step⟩ := id hstep
      obtain ⟨preFresh, core, frames, branches⟩ := connect_effect hstep
      obtain ⟨_, liveNow, _, _, _, ceNow, retReset, _, _, _, _, _, _⟩ := core
      obtain ⟨liveFrame, _, retainedFrame, retainedHistFn, _, _, histFrame, _, _⟩ := frames
      obtain ⟨restoreImp, freshImp⟩ := branches
      refine ⟨?_, ?_, ?_⟩
      · intro g' hg'
        rcases liveFrame g' with heq | hframe
        · rw [heq]
          exact hmember
        · exact ih.1 g' (by rw [← hframe]; exact hg')
      · intro g' hg'
        by_cases hx : g' = g
        · rw [hx]
          by_cases hbr : before.retained (t.peerOf g) = true ∧
            (before.now < before.expires (t.peerOf g) ∨ keep = true)
          · obtain ⟨hcur, _⟩ := restoreImp hbr
            rw [hcur]
            exact ih.2.2 (t.peerOf g) hbr.1
          · obtain ⟨hcur, _⟩ := freshImp hbr
            rw [hcur]
            exact Libp2p.ScoreState.initial_valid t.config hc
        · have hl : before.live g' = true := by
            rcases liveFrame g' with heq2 | hf
            · exact absurd heq2 hx
            · rw [← hf]; exact hg'
          rcases histFrame g' with heq3 | hfr
          · exact absurd heq3 hx
          · rw [hfr]
            exact ih.2.1 g' hl
      · intro p' hp'
        rcases retainedFrame p' with heq | hframe
        · rw [heq, retReset] at hp'
          simp at hp'
        · have hret : before.retained p' = true := by rw [← hframe]; exact hp'
          rw [retainedHistFn]
          exact ih.2.2 p' hret
    | disconnect g =>
      have hstep : Tr t before after (.disconnect g) := htr
      obtain ⟨hlive0, stored, closed, frames⟩ := disconnect_effect hstep
      obtain ⟨hliveG, _, _, _, _, _, _, _, hhistFn⟩ := closed
      refine ⟨?_, ?_, ?_⟩
      · intro g' hg'
        rcases frames.1 g' with heq | hframe
        · rw [heq, hliveG] at hg'
          simp at hg'
        · exact ih.1 g' (by rw [← hframe]; exact hg')
      · intro g' hg'
        rcases frames.1 g' with heq | hframe
        · rw [heq, hliveG] at hg'
          simp at hg'
        · rw [hhistFn]
          exact ih.2.1 g' (by rw [← hframe]; exact hg')
      · intro p' hp'
        rcases frames.2.2.2 p' with heq | hframe
        · rw [heq, stored.2.1]
          exact ih.2.1 g hlive0
        · rw [hframe.2.2.1]
          exact ih.2.2 p' (by rw [← hframe.2.1]; exact hp')
    | updateTopics g topic updates =>
      have hstep : Tr t before after (.updateTopics g topic updates) := htr
      obtain ⟨hlive0, hcur, _, _, _, _, liveFn, _, _, _, retainedFn, retainedHistFn, _,
        histFrame⟩ := updateTopics_effect hstep
      refine ⟨?_, ?_, ?_⟩
      · intro g' hg'
        exact ih.1 g' (by rw [← liveFn]; exact hg')
      · intro g' hg'
        by_cases hx : g' = g
        · rw [hx, hcur]
          exact updateTopicsScore_valid t.config hc topic updates (before.currentHistory g)
            (ih.2.1 g hlive0)
        · rcases histFrame g' with heq2 | hframe'
          · exact absurd heq2 hx
          · rw [hframe']
            exact ih.2.1 g' (by rw [← liveFn]; exact hg')
      · intro p' hp'
        rw [retainedHistFn]
        exact ih.2.2 p' (by rw [← retainedFn]; exact hp')
    | decayLive g =>
      have hstep : Tr t before after (.decayLive g) := htr
      obtain ⟨hlive0, hcur, _, _, _, _, liveFn, _, _, _, retainedFn, retainedHistFn, _,
        histFrame⟩ := decayLive_effect hstep
      refine ⟨?_, ?_, ?_⟩
      · intro g' hg'
        exact ih.1 g' (by rw [← liveFn]; exact hg')
      · intro g' hg'
        by_cases hx : g' = g
        · rw [hx, hcur]
          exact scoreState_decay_valid t.config hc (before.currentHistory g) (ih.2.1 g hlive0)
        · rcases histFrame g' with heq2 | hframe'
          · exact absurd heq2 hx
          · rw [hframe']
            exact ih.2.1 g' (by rw [← liveFn]; exact hg')
      · intro p' hp'
        rw [retainedHistFn]
        exact ih.2.2 p' (by rw [← retainedFn]; exact hp')
    | setApplication g value =>
      have hstep : Tr t before after (.setApplication g value) := htr
      obtain ⟨hlive0, hcur, _, _, _, _, liveFn, _, _, _, retainedFn, retainedHistFn, _,
        histFrame⟩ := setApplication_effect hstep
      refine ⟨?_, ?_, ?_⟩
      · intro g' hg'
        exact ih.1 g' (by rw [← liveFn]; exact hg')
      · intro g' hg'
        by_cases hx : g' = g
        · rw [hx, hcur]
          exact applicationScored_valid t.config (before.currentHistory g) value
            (ih.2.1 g hlive0)
        · rcases histFrame g' with heq2 | hframe'
          · exact absurd heq2 hx
          · rw [hframe']
            exact ih.2.1 g' (by rw [← liveFn]; exact hg')
      · intro p' hp'
        rw [retainedHistFn]
        exact ih.2.2 p' (by rw [← retainedFn]; exact hp')
    | setIPCount g count =>
      have hstep : Tr t before after (.setIPCount g count) := htr
      obtain ⟨hlive0, hcur, _, _, _, _, liveFn, _, _, _, retainedFn, retainedHistFn, _,
        histFrame⟩ := setIPCount_effect hstep
      refine ⟨?_, ?_, ?_⟩
      · intro g' hg'
        exact ih.1 g' (by rw [← liveFn]; exact hg')
      · intro g' hg'
        by_cases hx : g' = g
        · rw [hx, hcur]
          exact ipCounted_valid t.config (before.currentHistory g) count (ih.2.1 g hlive0)
        · rcases histFrame g' with heq2 | hframe'
          · exact absurd heq2 hx
          · rw [hframe']
            exact ih.2.1 g' (by rw [← liveFn]; exact hg')
      · intro p' hp'
        rw [retainedHistFn]
        exact ih.2.2 p' (by rw [← retainedFn]; exact hp')
    | penalize g authorized =>
      cases authorized with
      | true =>
        have hstep : Tr t before after (.penalize g true) := htr
        obtain ⟨hbig, _⟩ := penalize_effect hstep
        obtain ⟨hlive0, hcur, _, _, _, _, liveFn, _, _, _, retainedFn, retainedHistFn, _,
          histFrame⟩ := hbig rfl
        refine ⟨?_, ?_, ?_⟩
        · intro g' hg'
          exact ih.1 g' (by rw [← liveFn]; exact hg')
        · intro g' hg'
          by_cases hx : g' = g
          · rw [hx, hcur]
            exact penalized_valid t.config (before.currentHistory g) (ih.2.1 g hlive0)
          · rcases histFrame g' with heq2 | hframe'
            · exact absurd heq2 hx
            · rw [hframe']
              exact ih.2.1 g' (by rw [← liveFn]; exact hg')
        · intro p' hp'
          rw [retainedHistFn]
          exact ih.2.2 p' (by rw [← retainedFn]; exact hp')
      | false =>
        have heq : after = before := htr
        subst heq
        exact ih
    | advance m =>
      have hstep : Tr t before after (.advance m) := htr
      obtain ⟨_, _, _, _, liveFn, _, _, _, retainedFn, retainedHistFn, _, histFn⟩ :=
        advance_effect hstep
      refine ⟨?_, ?_, ?_⟩
      · intro g' hg'
        exact ih.1 g' (by rw [← liveFn]; exact hg')
      · intro g' hg'
        rw [histFn]
        exact ih.2.1 g' (by rw [← liveFn]; exact hg')
      · intro p' hp'
        rw [retainedHistFn]
        exact ih.2.2 p' (by rw [← retainedFn]; exact hp')
    | authenticate g =>
      have hstep : Tr t before after (.authenticate g) := htr
      obtain ⟨_, _, _, _, _, _, liveFn, _, _, retainedFn, retainedHistFn, _, histFn, _⟩ :=
        authenticate_effect hstep
      refine ⟨?_, ?_, ?_⟩
      · intro g' hg'
        exact ih.1 g' (by rw [← liveFn]; exact hg')
      · intro g' hg'
        rw [histFn]
        exact ih.2.1 g' (by rw [← liveFn]; exact hg')
      · intro p' hp'
        rw [retainedHistFn]
        exact ih.2.2 p' (by rw [← retainedFn]; exact hp')
    | authorizeCallbacks g =>
      have hstep : Tr t before after (.authorizeCallbacks g) := htr
      obtain ⟨_, _, _, _, _, _, _, liveFn, _, retainedFn, retainedHistFn, _, histFn, _, _⟩ :=
        authorizeCallbacks_effect hstep
      refine ⟨?_, ?_, ?_⟩
      · intro g' hg'
        exact ih.1 g' (by rw [← liveFn]; exact hg')
      · intro g' hg'
        rw [histFn]
        exact ih.2.1 g' (by rw [← liveFn]; exact hg')
      · intro p' hp'
        rw [retainedHistFn]
        exact ih.2.2 p' (by rw [← retainedFn]; exact hp')
    | decayRetained p =>
      have hstep : Tr t before after (.decayRetained p) := htr
      obtain ⟨hret0, hcur, closed, frames⟩ := decayRetained_effect hstep
      obtain ⟨_, _, _, _, hliveFn, _, _, _, hretFn, _, _, hhistFn⟩ := closed
      refine ⟨?_, ?_, ?_⟩
      · intro g' hg'
        exact ih.1 g' (by rw [← hliveFn]; exact hg')
      · intro g' hg'
        rw [hhistFn]
        exact ih.2.1 g' (by rw [← hliveFn]; exact hg')
      · intro p' hp'
        rcases frames p' with heq | hframe
        · rw [heq, hcur]
          exact scoreState_decay_valid t.config hc (before.retainedHistory p) (ih.2.2 p hret0)
        · rw [hframe]
          exact ih.2.2 p' (by rw [← hretFn]; exact hp')

end Reachable

/-! ## Inherited Retention safety obligations -/

section RetentionSafety

variable
  [Inhabited Peer] [Inhabited Generation] [Inhabited (ScoreState Topic)] [DecidableEq Topic]
  {t : Theory Peer Generation Topic} {st : RState Peer Generation Topic}

/-- At most one live scoring generation exists per peer, via the real invariant. -/
theorem live_owner_unique (h : (system t).reachable t st) {a b : Generation}
    (ha : st.live a = true) (hb : st.live b = true) (hp : t.peerOf a = t.peerOf b) : a = b := by
  have safe := Libp2p.TemporalRetention.retentionSafety Peer Generation (ScoreState Topic) Nat
    (toRetention t) st (reachable_projection h)
  veil_simp +instances only [Libp2p.TemporalRetention.Invariants, invSimp,
    dsimpFieldRepresentationGet] at safe
  have hpe : (toRetention t).peerOf = t.peerOf := rfl
  rw [hpe] at safe
  grind

/-- A peer that is not online owns no live generation, via the real invariant. -/
theorem offline_no_live_owner (h : (system t).reachable t st) (p : Peer)
    (hoffline : st.online p = false) {g : Generation} (hlive : st.live g = true) :
    t.peerOf g ≠ p := by
  have safe := Libp2p.TemporalRetention.retentionSafety Peer Generation (ScoreState Topic) Nat
    (toRetention t) st (reachable_projection h)
  veil_simp +instances only [Libp2p.TemporalRetention.Invariants, invSimp,
    dsimpFieldRepresentationGet] at safe
  have hpe : (toRetention t).peerOf = t.peerOf := rfl
  rw [hpe] at safe
  grind

/-- Restore is mandatory while the stored deadline is unexpired. -/
theorem unexpired_restore_mandatory (h : (system t).reachable t st)
    (hce : st.connectEmitted = true) (held : st.existedAtConnect = true)
    (hwithin : st.now < st.deadlineAtConnect) : st.restored = true := by
  have safe := Libp2p.TemporalRetention.retentionSafety Peer Generation (ScoreState Topic) Nat
    (toRetention t) st (reachable_projection h)
  veil_simp +instances only [Libp2p.TemporalRetention.Invariants, invSimp,
    dsimpFieldRepresentationGet] at safe
  have hpe : (toRetention t).peerOf = t.peerOf := rfl
  rw [hpe] at safe
  grind

/--
A restored connection carries the stored history of the same peer, through the
actual connect bookkeeping.
-/
theorem restored_stored_same_peer_history (h : (system t).reachable t st)
    (hce : st.connectEmitted = true) (hr : st.restored = true) :
    st.existedAtConnect = true ∧ t.peerOf st.lastOrigin = t.peerOf st.lastSession ∧
    st.currentHistory st.lastSession = st.historyAtConnect ∧
    st.live st.lastOrigin = false := by
  have safe := Libp2p.TemporalRetention.retentionSafety Peer Generation (ScoreState Topic) Nat
    (toRetention t) st (reachable_projection h)
  veil_simp +instances only [Libp2p.TemporalRetention.Invariants, invSimp,
    dsimpFieldRepresentationGet] at safe
  have hpe : (toRetention t).peerOf = t.peerOf := rfl
  rw [hpe] at safe
  grind

end RetentionSafety

/-! ## Constructive owner lookup and the effective history -/

section Lookup

variable
  [Inhabited Peer] [Inhabited Generation] [Inhabited (ScoreState Topic)] [DecidableEq Peer]
  [DecidableEq Topic]
  {t : Theory Peer Generation Topic} {st : RState Peer Generation Topic}

theorem find?_eq_some_mem {α : Type} {l : List α} {p : α → Bool} {b : α}
    (h : l.find? p = some b) : b ∈ l ∧ p b = true := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    by_cases hp : p a = true
    · rw [List.find?_cons_of_pos hp] at h
      have hab : a = b := by simpa using h
      subst hab
      exact ⟨by simp, hp⟩
    · rw [List.find?_cons_of_neg hp] at h
      obtain ⟨hmem, hpb⟩ := ih h
      exact ⟨List.mem_cons_of_mem a hmem, hpb⟩

theorem find?_eq_some_of_unique {α : Type} (p : α → Bool) : ∀ {l : List α} {b : α},
    b ∈ l → p b = true → (∀ a ∈ l, p a = true → a = b) → l.find? p = some b := by
  intro l b
  induction l with
  | nil => intro hmem _ _; simp at hmem
  | cons a l ih =>
    intro hmem hpb huniq
    by_cases hp : p a = true
    · have hab : a = b := huniq a (by simp) hp
      subst hab
      exact List.find?_cons_of_pos hpb
    · rw [List.find?_cons_of_neg hp]
      rcases List.mem_cons.mp hmem with hba | hin
      · rw [hba] at hpb
        exact absurd hpb hp
      · exact ih hin hpb (fun x hx hpx => huniq x (List.mem_cons_of_mem a hx) hpx)

theorem find?_congr {α : Type} (p q : α → Bool) : ∀ (l : List α),
    (∀ x ∈ l, p x = q x) → l.find? p = l.find? q := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a l ih =>
    intro h
    have hq := h a (by simp)
    cases hp : p a with
    | true =>
      have hq' : q a = true := by rw [← hq]; exact hp
      rw [List.find?_cons_of_pos hp, List.find?_cons_of_pos hq']
    | false =>
      have hq' : q a = false := by rw [← hq]; exact hp
      rw [List.find?_cons_of_neg (by simp [hp]), List.find?_cons_of_neg (by simp [hq'])]
      exact ih (fun x hx => h x (List.mem_cons_of_mem a hx))

/--
The constructive lookup is exact: it selects a generation iff that generation
is the unique live owner of the peer, using the real one-owner invariant.
-/
theorem activeOwner_some_iff (h : (system t).reachable t st) (p : Peer) (g : Generation) :
    activeOwner t st p = some g ↔ st.live g = true ∧ t.peerOf g = p := by
  constructor
  · intro hsome
    obtain ⟨hmem, hpred⟩ := find?_eq_some_mem hsome
    have hpair : st.live g = true ∧ t.peerOf g = p := by
      simpa [Bool.and_eq_true] using hpred
    exact hpair
  · intro hpair
    refine find?_eq_some_of_unique _ (live_member_of_reachable h g hpair.1) ?_ ?_
    · rw [Bool.and_eq_true]
      exact ⟨hpair.1, by simp [hpair.2]⟩
    · intro a ha hpa
      have hpairA : st.live a = true ∧ t.peerOf a = p := by
        simpa [Bool.and_eq_true] using hpa
      exact live_owner_unique h hpairA.1 hpair.1 (hpairA.2.trans hpair.2.symm)

/--
An offline peer has no constructive owner, again through the real invariants.
-/
theorem activeOwner_none_iff (h : (system t).reachable t st) (p : Peer) :
    activeOwner t st p = none ↔ ∀ g, st.live g = true → t.peerOf g ≠ p := by
  constructor
  · intro hnone g hlive hp
    have hmem := live_member_of_reachable h g hlive
    have hno := (List.find?_eq_none (p := fun x => st.live x && Decidable.decide (t.peerOf x = p))
      (l := t.knownGenerations)).mp hnone g hmem
    rw [hlive, hp] at hno
    simp at hno
  · intro hall
    unfold activeOwner
    rw [List.find?_eq_none]
    intro x hx hpx
    obtain ⟨hlive, hp⟩ : st.live x = true ∧ t.peerOf x = p := by simpa using hpx
    exact hall x hlive hp

/-- Effective history of a live peer is exactly its owner's current history. -/
theorem historyForPeer_online (h : (system t).reachable t st) (p : Peer) {g : Generation}
    (hlive : st.live g = true) (hp : t.peerOf g = p) :
    historyForPeer t st p = st.currentHistory g := by
  have howner := (activeOwner_some_iff h p g).mpr ⟨hlive, hp⟩
  rw [historyForPeer, howner]

/-- Effective history of an offline retained peer is the stored retained history. -/
theorem historyForPeer_offline_retained (h : (system t).reachable t st) (p : Peer)
    (hoffline : st.online p = false) (hret : st.retained p = true) :
    historyForPeer t st p = st.retainedHistory p := by
  have hnone := (activeOwner_none_iff h p).mpr
    (fun g hlive => offline_no_live_owner h p hoffline hlive)
  rw [historyForPeer, hnone, if_pos hret]

/-- Effective history of a fresh offline peer is the initial score state. -/
theorem historyForPeer_fresh (h : (system t).reachable t st) (p : Peer)
    (hoffline : st.online p = false) (hnotret : st.retained p = false) :
    historyForPeer t st p = ScoreState.initial := by
  have hnone := (activeOwner_none_iff h p).mpr
    (fun g hlive => offline_no_live_owner h p hoffline hlive)
  rw [historyForPeer, hnone, if_neg (by rw [hnotret]; simp)]

theorem historyForPeer_some {p : Peer} {g : Generation}
    (hown : activeOwner t st p = some g) : historyForPeer t st p = st.currentHistory g := by
  rw [historyForPeer, hown]

theorem historyForPeer_none {p : Peer} (hnone : activeOwner t st p = none)
    (hret : st.retained p = true) : historyForPeer t st p = st.retainedHistory p := by
  rw [historyForPeer, hnone, if_pos hret]

theorem historyForPeer_none_fresh {p : Peer} (hnone : activeOwner t st p = none)
    (hnotret : st.retained p = false) : historyForPeer t st p = ScoreState.initial := by
  rw [historyForPeer, hnone, if_neg (by rw [hnotret]; simp)]

/--
Numeric updates preserve the effective history of every other peer: the owner
lookup agrees because live sets are pointwise unchanged, and any other owner's
current history is framed.
-/
theorem historyForPeer_frame_of_live_update {next : RState Peer Generation Topic}
    {g : Generation} {history : ScoreState Topic}
    (hstep : (retSystem t).tr (toRetention t) st (.updateLiveHistory g history) next)
    (p : Peer) (hown : ∀ g', st.live g' = true → t.peerOf g' = p → g' ≠ g) :
    historyForPeer t next p = historyForPeer t st p := by
  obtain ⟨hliveG, _, _, _, _, _, liveFn, _, _, _, retainedFn, retainedHistFn, _, histFrame⟩ :=
    retention_updateLiveHistory_effect hstep
  have hownerEq : activeOwner t next p = activeOwner t st p := by
    unfold activeOwner
    exact find?_congr _ _ _ (fun x _ => by rw [liveFn])
  cases hv : activeOwner t st p with
  | some g' =>
    have hnext : activeOwner t next p = some g' := by rw [hownerEq]; exact hv
    calc historyForPeer t next p = next.currentHistory g' :=
        historyForPeer_some hnext
      _ = st.currentHistory g' := by
          rcases histFrame g' with heq | hf
          · obtain ⟨_, hpred⟩ := find?_eq_some_mem hv
            have hpair' : st.live g' = true ∧ t.peerOf g' = p := by
              simpa [Bool.and_eq_true] using hpred
            rw [show g' = g from heq] at hpair'
            exact absurd rfl (hown g hpair'.1 hpair'.2)
          · exact hf
      _ = historyForPeer t st p := (historyForPeer_some hv).symm
  | none =>
    have hnext : activeOwner t next p = none := by rw [hownerEq]; exact hv
    calc historyForPeer t next p =
        if next.retained p = true then next.retainedHistory p else ScoreState.initial :=
        by simp only [historyForPeer, hnext]
      _ = if st.retained p = true then st.retainedHistory p else ScoreState.initial := by
          rw [retainedFn, retainedHistFn]
      _ = historyForPeer t st p := by simp only [historyForPeer, hv]

theorem historyForPeer_frame_retained_decay {next : RState Peer Generation Topic}
    {p0 : Peer}
    (hstep : (retSystem t).tr (toRetention t) st (.decayRetained p0) next) (p : Peer)
    (hne : p ≠ p0) :
    historyForPeer t next p = historyForPeer t st p := by
  obtain ⟨_, _, closed, frames⟩ := decayRetained_effect hstep
  obtain ⟨_, _, _, _, hliveFn, _, _, _, hretFn, _, _, hhistFn⟩ := closed
  have hownerEq : activeOwner t next p = activeOwner t st p := by
    unfold activeOwner
    exact find?_congr _ _ _ (fun x _ => by rw [hliveFn])
  cases hv : activeOwner t st p with
  | some g' =>
    have hnext : activeOwner t next p = some g' := by rw [hownerEq]; exact hv
    calc historyForPeer t next p = next.currentHistory g' :=
        historyForPeer_some hnext
      _ = st.currentHistory g' := by rw [hhistFn]
      _ = historyForPeer t st p := (historyForPeer_some hv).symm
  | none =>
    have hnext : activeOwner t next p = none := by rw [hownerEq]; exact hv
    have hdirect : next.retainedHistory p = st.retainedHistory p :=
      (frames p).resolve_left hne
    calc historyForPeer t next p =
        if next.retained p = true then next.retainedHistory p else ScoreState.initial :=
        by simp only [historyForPeer, hnext]
      _ = if st.retained p = true then st.retainedHistory p else ScoreState.initial := by
          rw [hretFn, hdirect]
      _ = historyForPeer t st p := by simp only [historyForPeer, hv]

end Lookup

/-! ## withMeshTimes: pure projection onto an actual mesh-entry view -/

section WithMeshTimes

/-- The projection only replaces each topic's raw `meshTime` counter. -/
theorem withMeshTimes_topics_eq {Topic : Type} (s : ScoreState Topic) (e : Topic → Nat)
    (t : Topic) :
    (withMeshTimes s e).topics t = { s.topics t with meshTime := e t } :=
  rfl

theorem withMeshTimes_peer_eq {Topic : Type} (s : ScoreState Topic) (e : Topic → Nat) :
    (withMeshTimes s e).peer = s.peer :=
  rfl

/-- Validity is unaffected because `meshTime` carries no policy constraint. -/
theorem withMeshTimes_valid {Topic : Type} (s : ScoreState Topic) (e : Topic → Nat)
    (c : ScoreConfig Topic) (hs : s.Valid c) : (withMeshTimes s e).Valid c := by
  refine ⟨fun t ht => ?_, hs.peer⟩
  rw [withMeshTimes_topics_eq]
  have ht := hs.topics t ht
  exact ⟨ht.first_nonnegative, ht.first_capped, ht.mesh_nonnegative, ht.mesh_capped,
    ht.failure_nonnegative, ht.invalid_nonnegative⟩

/--
P1 and P3 under the projection are exactly the terms recomputed from the
supplied mesh-entry/clock view; every other term is framed.
-/
theorem withMeshTimes_toScore {Topic : Type} (s : ScoreState Topic) (e : Topic → Nat)
    (t : Topic) (params : TopicScoreParams) :
    ((withMeshTimes s e).topics t).toScore params =
      { (s.topics t).toScore params with
        p1 := Libp2p.p1 (e t) params.quantum params.timeCap
        p3 := Libp2p.deficit (e t) params.activation (s.topics t).mesh params.meshThreshold } :=
  rfl

/--
The score of the projection is the same `totalScore` shape as
`Libp2p.ScoreState.score`, so the parent instantiates P1/P3 purely from its
Network mesh-entry/clock view via `withMeshTimes_toScore`.
-/
theorem withMeshTimes_score {Topic : Type} (s : ScoreState Topic) (e : Topic → Nat)
    (c : ScoreConfig Topic) :
    (withMeshTimes s e).score c =
      Libp2p.totalScore
        (c.configured.map fun t => ((withMeshTimes s e).topics t).toScore (c.topicParams t))
        c.globalParams.topicCap c.globalParams.appWeight s.peer.appScore
        c.globalParams.ipWeight c.globalParams.behaviorWeight
        (Libp2p.colocation s.peer.ipCount c.globalParams.ipThreshold)
        (Libp2p.squaredPenalty s.peer.behavior) :=
  rfl

end WithMeshTimes


end Libp2p.ScoreHistory
