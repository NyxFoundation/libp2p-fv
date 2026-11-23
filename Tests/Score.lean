import Libp2p.ScoreConfig
import Libp2p.ScoreThresholds

open Libp2p

private def topicParams : TopicScoreParams :=
  { quantum := 10, activation := 10, timeCap := 3 / 2
    firstCap := 5 / 2, meshCap := 5, meshThreshold := 3
    firstDecay := 9 / 10, meshDecay := 1 / 2, failureDecay := 1 / 4, invalidDecay := 3 / 4
    weight := 2, w1 := 1 / 10, w2 := 1 / 2, w3 := -1, w3b := -2, w4 := -3 }

private theorem topicParams_valid : topicParams.Valid := by constructor <;> decide +kernel

example : ¬validDecayFactor 0 := by decide +kernel
example : ¬validDecayFactor 1 := by decide +kernel
example : ¬validDecayFactor (-1 / 2) := by decide +kernel
example : ¬validDecayFactor (3 / 2) := by decide +kernel
example : ¬({ topicParams with quantum := 0 } : TopicScoreParams).Valid := by
  intro h
  exact Nat.lt_irrefl 0 h.quantum_positive

private def globalParams : GlobalScoreParams :=
  { topicCap := some 2, appWeight := 2, ipWeight := -1 / 2, behaviorWeight := -2
    ipThreshold := 2, behaviorDecay := 2 / 3, decayCutoff := 1 / 10, decayInterval := 1, retainScore := 60 }

private theorem globalParams_valid : globalParams.Valid := by constructor <;> decide +kernel

private def counters : TopicCounters :=
  { meshTime := 11, first := 9 / 10, mesh := 3 / 2, failure := 1 / 2, invalid := 2 }

private theorem counters_valid : counters.Valid topicParams := by constructor <;> decide +kernel

#guard (counters.toScore topicParams).p1 == 1
#guard (counters.toScore topicParams).p2 == 9 / 10
#guard (counters.toScore topicParams).p3 == 9 / 4
#guard (counters.toScore topicParams).p3b == 1 / 2
#guard (counters.toScore topicParams).p4 == 4
#guard (counters.toScore topicParams).value == -147 / 5
#guard (counters.creditFirst topicParams).first == 19 / 10
#guard ((counters.creditFirst topicParams).creditFirst topicParams).first == 5 / 2
#guard (counters.creditMesh topicParams).mesh == 5 / 2
#guard counters.reject.first == counters.first
#guard counters.reject.mesh == counters.mesh
#guard counters.reject.invalid == 3
#guard (counters.prune topicParams false).failure == 1 / 2
#guard (counters.prune topicParams true).failure == 11 / 4
#guard ({ counters with meshTime := 10 }.prune topicParams true).failure == 1 / 2
#guard ({ counters with mesh := 7 / 2 }.prune topicParams true).failure == 1 / 2

private def decayed : TopicCounters := counters.decay topicParams (1 / 10)
#guard decayed.first == 81 / 100
#guard decayed.mesh == 3 / 4
#guard decayed.failure == 1 / 8
#guard decayed.invalid == 3 / 2
#guard decayed.meshTime == 11
#guard (decayed.toScore topicParams).p4 == 9 / 4
#guard (counters.decay topicParams (1 / 5)).failure == 0
#guard (counters.decay topicParams (3 / 2)).invalid == 3 / 2

example : decayed.Valid topicParams := counters.decay_valid _ _ counters_valid topicParams_valid
example (updates : List TopicScoreUpdate) :
    (updates.foldl (fun s u => s.apply topicParams u) TopicCounters.initial).Valid topicParams :=
  TopicCounters.updates_valid _ _ updates (TopicCounters.initial_valid _ topicParams_valid) topicParams_valid

private def peer : PeerCounters := { appScore := -3 / 4, ipCount := 4, behavior := 3 / 2 }
example : ¬({ peer with behavior := -1 } : PeerCounters).Valid := by decide +kernel
#guard (peer.decay globalParams).behavior == 1
#guard (peer.decay globalParams).appScore == -3 / 4
#guard (peer.decay globalParams).ipCount == 4
#guard squaredPenalty (peer.decay globalParams).behavior == 1
#guard (peer.penalize (1 / 4)).behavior == 7 / 4

private def config : ScoreConfig Bool :=
  { configured := [true], unique := by decide, topicParams := fun _ => topicParams
    globalParams := globalParams }

private theorem config_valid : config.Valid := ⟨fun _ _ => topicParams_valid, globalParams_valid⟩

private def state : ScoreState Bool :=
  { topics := fun t => if t then counters else { invalid := 1000000 }
    peer := peer }

private theorem state_valid : state.Valid config := by
  constructor
  · intro t ht
    have : t = true := by simpa [config] using ht
    subst t
    exact counters_valid
  · decide +kernel

#guard state.score config == -187 / 5
#guard (state.updateTopic config false .invalidDelivery).score config == state.score config
example (u : TopicScoreUpdate) : (state.updateTopic config false u).score config = state.score config :=
  state.unconfigured_update_excluded config false u (by decide)
example : (state.decay config).Valid config := state.decay_valid config state_valid config_valid
example (topic : Bool) (u : TopicScoreUpdate) : (state.updateTopic config topic u).Valid config :=
  state.updateTopic_valid config topic u state_valid config_valid

private def fractionalTopic : TopicScore := ⟨3 / 2, 0, 1 / 2, 0, 0, 0, 0, 3 / 2, 0, 0, 0⟩
#guard fractionalTopic.value == 9 / 8
#guard totalScore [fractionalTopic] (some 1) 2 3 0 0 0 0 == 7
#guard totalScore [fractionalTopic] none 2 3 0 0 0 0 == 57 / 8
#guard capScore (-3 / 2) (some 1) == -3 / 2
#guard capScore (3 / 2) (some (3 / 2)) == 3 / 2
#guard totalScore [] none 2 (-3 / 4) 0 0 0 0 == -3 / 2

private def thresholds : ScoreThresholds :=
  { gossip := -1 / 2, publish := -3 / 4, graylist := -1, acceptPX := 1 / 2, opportunistic := 1 / 4 }

example : thresholds.Valid := by constructor <;> decide +kernel
#guard (thresholds.classify 0).nonnegative
#guard (thresholds.classify (-1 / 2)).gossip
#guard !(thresholds.classify (-3 / 4)).gossip
#guard (thresholds.classify (-3 / 4)).publish
#guard (thresholds.classify (-1)).rpc
#guard !(thresholds.classify (-11 / 10)).rpc
#guard !(thresholds.classify (1 / 2)).px
#guard (thresholds.classify (3 / 4)).px
#guard !thresholds.opportunisticTrigger (1 / 4)
#guard thresholds.opportunisticTrigger (1 / 8)
#guard !opportunisticCandidate (1 / 2) (1 / 2)
#guard opportunisticCandidate (3 / 4) (1 / 2)
#guard validQuotas 5 3 2
#guard !validQuotas 5 4 3
#guard validQuotas 6 4 3
#guard !validQuotas 6 3 3
