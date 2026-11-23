module

public import Libp2p.ScoreConfig
public import Libp2p.CompositionSupport
public import Libp2p.TemporalRetention

/-!
Exact-rational score history over the verified TemporalRetention component.

`Theory` instantiates `Libp2p.TemporalRetention` with `history = ScoreState Topic`
and `moment = Nat`, so retained values are actual score states updated by the
verified numerical operations. `decayHistory = ScoreState.decay config` and
`initialHistory = ScoreState.initial`; `retainScore` is exactly
`config.globalParams.retainScore`, and timestamps are natural numbers in the
same duration unit as `retainScore` (the expiry equation
`expires = now + retainScore` is a proved exact correspondence).

A `Generation` is one peer-online scoring episode, not a transport connection
limit, so there is deliberately no invented per-peer connection cap. Every
wrapper label projects to a single real `TemporalRetention` transition (an
empty run only for the unauthorized-penalty no-op); this module adds no causal
authorization, first/near-first eligibility, mesh-time measurement, or clock
scheduling, and keeps the real post-expiry restore/discard nondeterminism.
-/

@[expose] public section

namespace Libp2p.ScoreHistory

variable {Peer Generation Topic : Type}

structure Theory (Peer Generation Topic : Type) where
  config : ScoreConfig Topic
  peerOf : Generation → Peer
  knownGenerations : List Generation

/-- The exact Retention theory instantiation used by every wrapper transition. -/
def toRetention {Peer Generation Topic : Type} (t : Theory Peer Generation Topic) :
    Libp2p.TemporalRetention.Theory Peer Generation (ScoreState Topic) Nat where
  peerOf := t.peerOf
  timestamp := id
  decayHistory := fun h => Libp2p.ScoreState.decay h t.config
  initialHistory := Libp2p.ScoreState.initial
  retainScore := t.config.globalParams.retainScore

/-- A fresh peer-online scoring generation, independent of transport sessions. -/
inductive Label (Peer Generation Topic : Type) where
  | connect (g : Generation) (keepAfterLifetime : Bool)
  | advance (m : Nat)
  | authenticate (g : Generation)
  | authorizeCallbacks (g : Generation)
  | disconnect (g : Generation)
  | decayRetained (p : Peer)
  | updateTopics (g : Generation) (t : Topic) (updates : List TopicScoreUpdate)
  | decayLive (g : Generation)
  | setApplication (g : Generation) (value : Rat)
  | setIPCount (g : Generation) (count : Nat)
  | penalize (g : Generation) (authorized : Bool)

/-- Applies a full update list to one topic of an actual score state. -/
def updateTopicsScore {Topic : Type} [DecidableEq Topic] (s : ScoreState Topic)
    (c : ScoreConfig Topic) (t : Topic) (updates : List TopicScoreUpdate) : ScoreState Topic :=
  updates.foldl (fun state update => state.updateTopic c t update) s

/-- Signed application-supplied score; the sign is unconstrained by policy. -/
def applicationScored (s : ScoreState Topic) (value : Rat) : ScoreState Topic :=
  { s with peer := { s.peer with appScore := value } }

/-- Natural IP-count update. -/
def ipCounted (s : ScoreState Topic) (count : Nat) : ScoreState Topic :=
  { s with peer := { s.peer with ipCount := count } }

/-- One authorized P7 cause increments the raw behavioral counter exactly once. -/
def penalized (s : ScoreState Topic) : ScoreState Topic :=
  { s with peer := s.peer.penalize 1 }

abbrev RState (Peer Generation Topic : Type) :=
  Libp2p.TemporalRetention.State (Libp2p.TemporalRetention.FieldAbstractType Peer Generation
    (ScoreState Topic) Nat)

/-- The actual Retention transition system this wrapper reuses. -/
noncomputable def retSystem {Peer Generation Topic : Type}
    [Inhabited Peer] [Inhabited Generation] [Inhabited (ScoreState Topic)]
    (_t : Theory Peer Generation Topic) :
    Veil.RelationalTransitionSystem (Libp2p.TemporalRetention.Theory Peer Generation (ScoreState Topic) Nat)
      (RState Peer Generation Topic)
      (Libp2p.TemporalRetention.Label Peer Generation (ScoreState Topic) Nat) :=
  Libp2p.TemporalRetention.relationalTransitionSystem Peer Generation (ScoreState Topic) Nat

/--
The wrapper transition relation. `connect` additionally requires a listed
generation; every other clause is exactly one actual Retention transition, so
the wrapper invents no retention semantics of its own.
-/
def Tr {Peer Generation Topic : Type}
    [Inhabited Peer] [Inhabited Generation] [Inhabited (ScoreState Topic)] [DecidableEq Topic]
    (t : Theory Peer Generation Topic) (st next : RState Peer Generation Topic) :
    Label Peer Generation Topic → Prop
  | .connect g keep =>
      g ∈ t.knownGenerations ∧
        (retSystem t).tr (toRetention t) st (.connect g keep) next
  | .advance m => (retSystem t).tr (toRetention t) st (.advance m) next
  | .authenticate g => (retSystem t).tr (toRetention t) st (.authenticate g) next
  | .authorizeCallbacks g => (retSystem t).tr (toRetention t) st (.authorizeCallbacks g) next
  | .disconnect g => (retSystem t).tr (toRetention t) st (.disconnect g) next
  | .decayRetained p => (retSystem t).tr (toRetention t) st (.decayRetained p) next
  | .updateTopics g topic updates =>
      (retSystem t).tr (toRetention t) st
        (.updateLiveHistory g (updateTopicsScore (st.currentHistory g) t.config topic updates)) next
  | .decayLive g =>
      (retSystem t).tr (toRetention t) st
        (.updateLiveHistory g (Libp2p.ScoreState.decay (st.currentHistory g) t.config)) next
  | .setApplication g value =>
      (retSystem t).tr (toRetention t) st
        (.updateLiveHistory g (applicationScored (st.currentHistory g) value)) next
  | .setIPCount g count =>
      (retSystem t).tr (toRetention t) st
        (.updateLiveHistory g (ipCounted (st.currentHistory g) count)) next
  | .penalize g true =>
      (retSystem t).tr (toRetention t) st
        (.updateLiveHistory g (penalized (st.currentHistory g))) next
  | .penalize _ false => next = st

/--
The wrapper system. It never accepts an arbitrary history value: numeric labels
compute the next `ScoreState` from the pre-state's actual owner history.
-/
noncomputable def system {Peer Generation Topic : Type}
    [Inhabited Peer] [Inhabited Generation] [Inhabited (ScoreState Topic)] [DecidableEq Topic]
    (t : Theory Peer Generation Topic) :
    Veil.RelationalTransitionSystem (Theory Peer Generation Topic) (RState Peer Generation Topic)
      (Label Peer Generation Topic) where
  assumptions := fun _ => True
  init := fun t' st => (retSystem t').init (toRetention t') st
  tr := fun t' st label next => Tr t' st next label

/-- Per-label projection onto real Retention labels (empty only for the no-op). -/
def project {Peer Generation Topic : Type}
    [Inhabited Peer] [Inhabited Generation] [Inhabited (ScoreState Topic)] [DecidableEq Topic]
    (t : Theory Peer Generation Topic) (st : RState Peer Generation Topic)
    : Label Peer Generation Topic →
      List (Libp2p.TemporalRetention.Label Peer Generation (ScoreState Topic) Nat)
  | .connect g keep => [.connect g keep]
  | .advance m => [.advance m]
  | .authenticate g => [.authenticate g]
  | .authorizeCallbacks g => [.authorizeCallbacks g]
  | .disconnect g => [.disconnect g]
  | .decayRetained p => [.decayRetained p]
  | .updateTopics g topic updates =>
      [.updateLiveHistory g (updateTopicsScore (st.currentHistory g) t.config topic updates)]
  | .decayLive g =>
      [.updateLiveHistory g (Libp2p.ScoreState.decay (st.currentHistory g) t.config)]
  | .setApplication g value =>
      [.updateLiveHistory g (applicationScored (st.currentHistory g) value)]
  | .setIPCount g count => [.updateLiveHistory g (ipCounted (st.currentHistory g) count)]
  | .penalize g true => [.updateLiveHistory g (penalized (st.currentHistory g))]
  | .penalize _ false => []

/-- Concatenation of real-system runs. -/
theorem runs_append {ρ σ l} {system : Veil.RelationalTransitionSystem ρ σ l} {theory : ρ} :
    ∀ {a b c : σ} {labels₁ : List l},
      Libp2p.Runs system theory a labels₁ b →
      ∀ (labels₂ : List l),
        Libp2p.Runs system theory b labels₂ c →
        Libp2p.Runs system theory a (labels₁ ++ labels₂) c := by
  intro a b c labels₁ left
  induction left with
  | nil state =>
    intro labels₂ right
    simpa [List.nil_append] using right
  | cons step rest ih =>
    intro labels₂ right
    exact .cons step (ih labels₂ right)

/-- Each wrapper step is one real Retention run over exactly its projection. -/
theorem step_projection {Peer Generation Topic : Type}
    [Inhabited Peer] [Inhabited Generation] [Inhabited (ScoreState Topic)] [DecidableEq Topic]
    {t : Theory Peer Generation Topic} {st next : RState Peer Generation Topic}
    {label : Label Peer Generation Topic} (h : Tr t st next label) :
    Libp2p.Runs (retSystem t) (toRetention t) st (project t st label) next := by
  unfold Tr at h
  cases label with
  | connect g keep => exact Runs.single_iff.mpr h.2
  | advance m => exact Runs.single_iff.mpr h
  | authenticate g => exact Runs.single_iff.mpr h
  | authorizeCallbacks g => exact Runs.single_iff.mpr h
  | disconnect g => exact Runs.single_iff.mpr h
  | decayRetained p => exact Runs.single_iff.mpr h
  | updateTopics g topic updates => exact Runs.single_iff.mpr h
  | decayLive g => exact Runs.single_iff.mpr h
  | setApplication g value => exact Runs.single_iff.mpr h
  | setIPCount g count => exact Runs.single_iff.mpr h
  | penalize g authorized => cases authorized with
    | true => exact Runs.single_iff.mpr h
    | false => exact Runs.nil_iff.mpr h

/--
Every finite wrapper trace is a trace of the real Retention system: the
flattened label list runs through `retSystem` with the same endpoints.
-/
theorem trace_projection {Peer Generation Topic : Type}
    [Inhabited Peer] [Inhabited Generation] [Inhabited (ScoreState Topic)] [DecidableEq Topic]
    {t : Theory Peer Generation Topic} {before after : RState Peer Generation Topic}
    {labels : List (Label Peer Generation Topic)}
    (run : Libp2p.Runs (system t) t before labels after) :
    ∃ labels', Libp2p.Runs (retSystem t) (toRetention t) before labels' after := by
  unfold system at run
  induction run with
  | nil state => exact ⟨[], .nil state⟩
  | cons step rest ih =>
    rename_i before middle _ label _
    obtain ⟨labels', run'⟩ := ih
    exact ⟨project t before label ++ labels', runs_append (step_projection step) labels' run'⟩

/-- Wrapper-reachable states are reachable in the actual Retention system. -/
theorem reachable_projection {Peer Generation Topic : Type}
    [Inhabited Peer] [Inhabited Generation] [Inhabited (ScoreState Topic)] [DecidableEq Topic]
    {t : Theory Peer Generation Topic} {st : RState Peer Generation Topic}
    (reachable : (system t).reachable t st) :
    (retSystem t).reachable (toRetention t) st := by
  exact Libp2p.reachable_projection (system t) (retSystem t) toRetention (fun st => st)
    (fun _ _ => trivial) (fun _ _ h => h)
    (fun th' st label next h => ⟨project th' st label, step_projection h⟩) reachable

/-- Constructive active-owner lookup over the listed generations. -/
def activeOwner {Peer Generation Topic : Type}
    [Inhabited Peer] [Inhabited Generation] [Inhabited (ScoreState Topic)] [DecidableEq Peer]
    (t : Theory Peer Generation Topic) (st : RState Peer Generation Topic) (p : Peer) :
    Option Generation :=
  t.knownGenerations.find? (fun g => st.live g && Decidable.decide (t.peerOf g = p))

/--
History actually in force for a peer: the unique live owner's current history,
else the retained history when one is stored, else the initial score state.
-/
def historyForPeer {Peer Generation Topic : Type}
    [Inhabited Peer] [Inhabited Generation] [Inhabited (ScoreState Topic)] [DecidableEq Peer]
    (t : Theory Peer Generation Topic) (st : RState Peer Generation Topic) (p : Peer) :
    ScoreState Topic :=
  match activeOwner t st p with
  | some g => st.currentHistory g
  | none => if st.retained p = true then st.retainedHistory p else Libp2p.ScoreState.initial

/--
Pure projection replacing the raw stored `meshTime` counters with an actual
Network mesh-entry/clock view supplied by the caller. It changes only the
`meshTime` inputs of `toScore` (P1 and P3) and never authorizes by itself.
-/
def withMeshTimes {Topic : Type} (s : ScoreState Topic) (meshEntry : Topic → Nat) :
    ScoreState Topic :=
  { s with topics := fun topic => { s.topics topic with meshTime := meshEntry topic } }

end Libp2p.ScoreHistory
