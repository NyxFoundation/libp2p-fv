module

public import Libp2p.ScoreState

@[expose] public section
namespace Libp2p

structure ScoreConfig (Topic : Type) where
  configured : List Topic
  unique : configured.Nodup
  topicParams : Topic → TopicScoreParams
  globalParams : GlobalScoreParams

structure ScoreConfig.Valid {Topic : Type} (c : ScoreConfig Topic) : Prop where
  topics : ∀ t ∈ c.configured, (c.topicParams t).Valid
  global : c.globalParams.Valid

structure ScoreState (Topic : Type) where
  topics : Topic → TopicCounters
  peer : PeerCounters

structure ScoreState.Valid {Topic : Type} (s : ScoreState Topic) (c : ScoreConfig Topic) : Prop where
  topics : ∀ t ∈ c.configured, (s.topics t).Valid (c.topicParams t)
  peer : s.peer.Valid

def ScoreState.initial {Topic : Type} : ScoreState Topic :=
  ⟨fun _ => TopicCounters.initial, {}⟩

def ScoreState.score {Topic : Type} (s : ScoreState Topic) (c : ScoreConfig Topic) : Rat :=
  totalScore (c.configured.map fun t => (s.topics t).toScore (c.topicParams t)) c.globalParams.topicCap
    c.globalParams.appWeight s.peer.appScore c.globalParams.ipWeight c.globalParams.behaviorWeight
    (colocation s.peer.ipCount c.globalParams.ipThreshold) (squaredPenalty s.peer.behavior)

def ScoreState.updateTopic {Topic : Type} [DecidableEq Topic] (s : ScoreState Topic)
    (c : ScoreConfig Topic) (topic : Topic) (update : TopicScoreUpdate) : ScoreState Topic :=
  { s with topics := fun t => if t = topic then (s.topics t).apply (c.topicParams t) update else s.topics t }

def ScoreState.decay {Topic : Type} (s : ScoreState Topic) (c : ScoreConfig Topic) : ScoreState Topic :=
  { topics := fun t => (s.topics t).decay (c.topicParams t) c.globalParams.decayCutoff
    peer := s.peer.decay c.globalParams }

theorem ScoreState.initial_valid {Topic : Type} (c : ScoreConfig Topic) (hc : c.Valid) :
    (initial : ScoreState Topic).Valid c :=
  ⟨fun t ht => TopicCounters.initial_valid _ (hc.topics t ht), PeerCounters.initial_valid⟩

theorem ScoreState.updateTopic_valid {Topic : Type} [DecidableEq Topic] (s : ScoreState Topic)
    (c : ScoreConfig Topic) (topic : Topic) (update : TopicScoreUpdate) (hs : s.Valid c) (hc : c.Valid) :
    (s.updateTopic c topic update).Valid c := by
  constructor
  · intro t ht
    dsimp only [updateTopic]
    split
    · exact (s.topics t).apply_valid _ update (hs.topics t ht) (hc.topics t ht)
    · exact hs.topics t ht
  · exact hs.peer

theorem ScoreState.decay_valid {Topic : Type} (s : ScoreState Topic) (c : ScoreConfig Topic)
    (hs : s.Valid c) (hc : c.Valid) : (s.decay c).Valid c :=
  ⟨fun t ht => (s.topics t).decay_valid _ _ (hs.topics t ht) (hc.topics t ht),
    s.peer.decay_valid _ hs.peer hc.global⟩

theorem ScoreState.score_congr_on_configured {Topic : Type} (a b : ScoreState Topic)
    (c : ScoreConfig Topic) (ht : ∀ t ∈ c.configured, a.topics t = b.topics t) (hp : a.peer = b.peer) :
    a.score c = b.score c := by
  have hm : c.configured.map (fun t => (a.topics t).toScore (c.topicParams t)) =
      c.configured.map (fun t => (b.topics t).toScore (c.topicParams t)) :=
    List.map_congr_left (fun t h => congrArg (fun s => s.toScore (c.topicParams t)) (ht t h))
  simp only [score, hm, hp]

theorem ScoreState.unconfigured_update_excluded {Topic : Type} [DecidableEq Topic]
    (s : ScoreState Topic) (c : ScoreConfig Topic) (topic : Topic) (update : TopicScoreUpdate)
    (h : topic ∉ c.configured) : (s.updateTopic c topic update).score c = s.score c := by
  apply score_congr_on_configured (s.updateTopic c topic update) s c _ rfl
  intro t ht
  have hne : t ≠ topic := by intro he; subst t; exact h ht
  simp only [updateTopic, hne, ite_eq_right, not_false_eq_true]

theorem ScoreState.updateTopic_frame {Topic : Type} [DecidableEq Topic]
    (s : ScoreState Topic) (c : ScoreConfig Topic) (topic other : Topic) (update : TopicScoreUpdate)
    (h : other ≠ topic) :
    (s.updateTopic c topic update).topics other = s.topics other ∧
    (s.updateTopic c topic update).peer = s.peer := by
  simp [updateTopic, h]

end Libp2p
