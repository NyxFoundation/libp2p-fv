module

public import Libp2p.ScoreLemmas

@[expose] public section
namespace Libp2p

def validDecayFactor (factor : Rat) : Prop := 0 < factor ∧ factor < 1

instance (factor : Rat) : Decidable (validDecayFactor factor) :=
  inferInstanceAs (Decidable (0 < factor ∧ factor < 1))

structure TopicScoreParams where
  quantum : Nat
  activation : Nat
  timeCap : Rat
  firstCap : Rat
  meshCap : Rat
  meshThreshold : Rat
  firstDecay : Rat
  meshDecay : Rat
  failureDecay : Rat
  invalidDecay : Rat
  weight : Rat
  w1 : Rat
  w2 : Rat
  w3 : Rat
  w3b : Rat
  w4 : Rat
  deriving Repr

structure TopicScoreParams.Valid (p : TopicScoreParams) : Prop where
  quantum_positive : 0 < p.quantum
  timeCap_nonnegative : 0 ≤ p.timeCap
  firstCap_nonnegative : 0 ≤ p.firstCap
  threshold_positive : 0 < p.meshThreshold
  threshold_le_cap : p.meshThreshold ≤ p.meshCap
  first_decay : validDecayFactor p.firstDecay
  mesh_decay : validDecayFactor p.meshDecay
  failure_decay : validDecayFactor p.failureDecay
  invalid_decay : validDecayFactor p.invalidDecay

-- Topic sign recommendations are separate from the numerical domain constraints.
def TopicScoreParams.RecommendedSigns (p : TopicScoreParams) : Prop :=
  0 < p.w1 ∧ 0 < p.w2 ∧ p.w3 < 0 ∧ p.w3b < 0 ∧ p.w4 < 0

theorem TopicScoreParams.Valid.meshCap_nonnegative {p : TopicScoreParams} (h : p.Valid) :
    0 ≤ p.meshCap := Rat.le_trans (Rat.le_of_lt h.threshold_positive) h.threshold_le_cap

structure TopicCounters where
  meshTime : Nat := 0
  first : Rat := 0
  mesh : Rat := 0
  failure : Rat := 0
  invalid : Rat := 0
  deriving DecidableEq, Repr

structure TopicCounters.Valid (s : TopicCounters) (p : TopicScoreParams) : Prop where
  first_nonnegative : 0 ≤ s.first
  first_capped : s.first ≤ p.firstCap
  mesh_nonnegative : 0 ≤ s.mesh
  mesh_capped : s.mesh ≤ p.meshCap
  failure_nonnegative : 0 ≤ s.failure
  invalid_nonnegative : 0 ≤ s.invalid

def TopicCounters.initial : TopicCounters := {}

def TopicCounters.creditFirst (s : TopicCounters) (p : TopicScoreParams) : TopicCounters :=
  { s with first := Libp2p.creditFirst s.first p.firstCap }

def TopicCounters.creditMesh (s : TopicCounters) (p : TopicScoreParams) : TopicCounters :=
  { s with mesh := Libp2p.creditFirst s.mesh p.meshCap }

def TopicCounters.reject (s : TopicCounters) : TopicCounters :=
  { s with invalid := s.invalid + 1 }

def TopicCounters.prune (s : TopicCounters) (p : TopicScoreParams)
    (negativeScorePrune : Bool) : TopicCounters :=
  { s with failure := p3b s.failure s.meshTime p.activation s.mesh p.meshThreshold negativeScorePrune }

def TopicCounters.decay (s : TopicCounters) (p : TopicScoreParams) (cutoff : Rat) : TopicCounters :=
  { s with
    first := Libp2p.decay s.first p.firstDecay cutoff
    mesh := Libp2p.decay s.mesh p.meshDecay cutoff
    failure := Libp2p.decay s.failure p.failureDecay cutoff
    invalid := Libp2p.decay s.invalid p.invalidDecay cutoff }

-- meshTime comes from the monotonic timer interface; these functions do not authorize events.
def TopicCounters.toScore (s : TopicCounters) (p : TopicScoreParams) : TopicScore :=
  { weight := p.weight, w1 := p.w1, w2 := p.w2, w3 := p.w3, w3b := p.w3b, w4 := p.w4
    p1 := Libp2p.p1 s.meshTime p.quantum p.timeCap
    p2 := s.first
    p3 := deficit s.meshTime p.activation s.mesh p.meshThreshold
    p3b := s.failure
    p4 := squaredPenalty s.invalid }

theorem TopicCounters.initial_valid (p : TopicScoreParams) (hp : p.Valid) : initial.Valid p := by
  exact ⟨Rat.le_refl, hp.firstCap_nonnegative, Rat.le_refl,
    hp.meshCap_nonnegative, Rat.le_refl, Rat.le_refl⟩

theorem TopicCounters.creditFirst_valid (s : TopicCounters) (p : TopicScoreParams)
    (hs : s.Valid p) (hp : p.Valid) : (s.creditFirst p).Valid p := by
  exact { hs with
    first_nonnegative := creditFirst_nonnegative _ _ hs.first_nonnegative hp.firstCap_nonnegative
    first_capped := creditFirst_capped _ _ }

theorem TopicCounters.creditMesh_valid (s : TopicCounters) (p : TopicScoreParams)
    (hs : s.Valid p) (hp : p.Valid) : (s.creditMesh p).Valid p := by
  exact { hs with
    mesh_nonnegative := creditFirst_nonnegative _ _ hs.mesh_nonnegative hp.meshCap_nonnegative
    mesh_capped := creditFirst_capped _ _ }

theorem TopicCounters.reject_valid (s : TopicCounters) (p : TopicScoreParams)
    (hs : s.Valid p) : s.reject.Valid p := by
  exact { hs with invalid_nonnegative := Rat.add_nonneg hs.invalid_nonnegative (by decide) }

theorem TopicCounters.prune_valid (s : TopicCounters) (p : TopicScoreParams)
    (prune : Bool) (hs : s.Valid p) : (s.prune p prune).Valid p := by
  exact { hs with failure_nonnegative := p3b_nonnegative _ _ _ _ _ _ hs.failure_nonnegative }

theorem TopicCounters.decay_valid (s : TopicCounters) (p : TopicScoreParams) (cutoff : Rat)
    (hs : s.Valid p) (hp : p.Valid) : (s.decay p cutoff).Valid p := by
  exact {
    first_nonnegative := decay_nonnegative _ _ _ hs.first_nonnegative (Rat.le_of_lt hp.first_decay.1)
    first_capped := Rat.le_trans
      (decay_nonincreasing _ _ _ hs.first_nonnegative (Rat.le_of_lt hp.first_decay.2)) hs.first_capped
    mesh_nonnegative := decay_nonnegative _ _ _ hs.mesh_nonnegative (Rat.le_of_lt hp.mesh_decay.1)
    mesh_capped := Rat.le_trans
      (decay_nonincreasing _ _ _ hs.mesh_nonnegative (Rat.le_of_lt hp.mesh_decay.2)) hs.mesh_capped
    failure_nonnegative := decay_nonnegative _ _ _ hs.failure_nonnegative (Rat.le_of_lt hp.failure_decay.1)
    invalid_nonnegative := decay_nonnegative _ _ _ hs.invalid_nonnegative (Rat.le_of_lt hp.invalid_decay.1) }

theorem TopicCounters.toScore_nonnegative (s : TopicCounters) (p : TopicScoreParams)
    (hs : s.Valid p) (hp : p.Valid) :
    0 ≤ (s.toScore p).p1 ∧ 0 ≤ (s.toScore p).p2 ∧ 0 ≤ (s.toScore p).p3 ∧
    0 ≤ (s.toScore p).p3b ∧ 0 ≤ (s.toScore p).p4 :=
  ⟨(p1_bounds _ _ _ hp.timeCap_nonnegative).1, hs.first_nonnegative,
    deficit_nonnegative .., hs.failure_nonnegative, squaredPenalty_nonnegative _ hs.invalid_nonnegative⟩

theorem TopicCounters.penalty_terms_nonpositive (s : TopicCounters) (p : TopicScoreParams)
    (hs : s.Valid p) (hw : p.RecommendedSigns) :
    p.w3 * (s.toScore p).p3 ≤ 0 ∧ p.w3b * (s.toScore p).p3b ≤ 0 ∧
    p.w4 * (s.toScore p).p4 ≤ 0 := by
  refine ⟨?_, ?_, weightedSquared_nonpositive _ _ (Rat.le_of_lt hw.2.2.2.2) hs.invalid_nonnegative⟩
  · simpa only [Rat.zero_mul, toScore] using Rat.mul_le_mul_of_nonneg_right
      (Rat.le_of_lt hw.2.2.1) (deficit_nonnegative s.meshTime p.activation s.mesh p.meshThreshold)
  · simpa only [Rat.zero_mul, toScore] using
      Rat.mul_le_mul_of_nonneg_right (Rat.le_of_lt hw.2.2.2.1) hs.failure_nonnegative

theorem TopicCounters.reward_terms_nonnegative (s : TopicCounters) (p : TopicScoreParams)
    (hs : s.Valid p) (hp : p.Valid) (hw : p.RecommendedSigns) :
    0 ≤ p.w1 * (s.toScore p).p1 ∧ 0 ≤ p.w2 * (s.toScore p).p2 :=
  ⟨Rat.mul_nonneg (Rat.le_of_lt hw.1) (p1_bounds _ _ _ hp.timeCap_nonnegative).1,
    Rat.mul_nonneg (Rat.le_of_lt hw.2.1) hs.first_nonnegative⟩

theorem TopicCounters.toScore_value (s : TopicCounters) (p : TopicScoreParams) :
    (s.toScore p).value = p.weight *
      (p.w1 * Libp2p.p1 s.meshTime p.quantum p.timeCap + p.w2 * s.first +
        p.w3 * deficit s.meshTime p.activation s.mesh p.meshThreshold +
        p.w3b * s.failure + p.w4 * (s.invalid * s.invalid)) := by
  simp only [toScore, TopicScore.value, squaredPenalty_eq_mul]

theorem TopicCounters.decay_factors (s : TopicCounters) (p : TopicScoreParams) (cutoff : Rat) :
    (s.decay p cutoff).first = Libp2p.decay s.first p.firstDecay cutoff ∧
    (s.decay p cutoff).mesh = Libp2p.decay s.mesh p.meshDecay cutoff ∧
    (s.decay p cutoff).failure = Libp2p.decay s.failure p.failureDecay cutoff ∧
    (s.decay p cutoff).invalid = Libp2p.decay s.invalid p.invalidDecay cutoff ∧
    (s.decay p cutoff).meshTime = s.meshTime := ⟨rfl, rfl, rfl, rfl, rfl⟩

inductive TopicScoreUpdate where
  | firstDelivery
  | meshDelivery
  | invalidDelivery
  | prune (negativeScorePrune : Bool)
  | decay (cutoff : Rat)
  | refreshTime (elapsed : Nat)
  deriving Repr

def TopicCounters.apply (s : TopicCounters) (p : TopicScoreParams) : TopicScoreUpdate → TopicCounters
  | .firstDelivery => s.creditFirst p
  | .meshDelivery => s.creditMesh p
  | .invalidDelivery => s.reject
  | .prune negative => s.prune p negative
  | .decay cutoff => s.decay p cutoff
  | .refreshTime elapsed => { s with meshTime := elapsed }

theorem TopicCounters.apply_valid (s : TopicCounters) (p : TopicScoreParams) (update : TopicScoreUpdate)
    (hs : s.Valid p) (hp : p.Valid) : (s.apply p update).Valid p := by
  cases update with
  | firstDelivery => exact s.creditFirst_valid p hs hp
  | meshDelivery => exact s.creditMesh_valid p hs hp
  | invalidDelivery => exact s.reject_valid p hs
  | prune negative => exact s.prune_valid p negative hs
  | decay cutoff => exact s.decay_valid p cutoff hs hp
  | refreshTime elapsed =>
    exact ⟨hs.first_nonnegative, hs.first_capped, hs.mesh_nonnegative,
      hs.mesh_capped, hs.failure_nonnegative, hs.invalid_nonnegative⟩

theorem TopicCounters.updates_valid (s : TopicCounters) (p : TopicScoreParams)
    (updates : List TopicScoreUpdate) (hs : s.Valid p) (hp : p.Valid) :
    (updates.foldl (fun state update => state.apply p update) s).Valid p := by
  induction updates generalizing s with
  | nil => exact hs
  | cons update updates ih => exact ih (s.apply p update) (s.apply_valid p update hs hp)

structure GlobalScoreParams where
  topicCap : Option Rat
  appWeight : Rat
  ipWeight : Rat
  behaviorWeight : Rat
  ipThreshold : Nat
  behaviorDecay : Rat
  decayCutoff : Rat
  decayInterval : Nat
  retainScore : Nat
  deriving Repr

structure GlobalScoreParams.Valid (p : GlobalScoreParams) : Prop where
  appWeight_positive : 0 < p.appWeight
  ipWeight_negative : p.ipWeight < 0
  behaviorWeight_negative : p.behaviorWeight < 0
  ipThreshold_positive : 1 ≤ p.ipThreshold
  behavior_decay : validDecayFactor p.behaviorDecay
  cutoff_nonnegative : 0 ≤ p.decayCutoff
  interval_positive : 0 < p.decayInterval

structure PeerCounters where
  appScore : Rat := 0
  ipCount : Nat := 0
  behavior : Rat := 0
  deriving DecidableEq, Repr

def PeerCounters.Valid (s : PeerCounters) : Prop := 0 ≤ s.behavior

instance (s : PeerCounters) : Decidable s.Valid := inferInstanceAs (Decidable (0 ≤ s.behavior))

def PeerCounters.penalize (s : PeerCounters) (amount : Rat) : PeerCounters :=
  { s with behavior := s.behavior + amount }

-- The selected reference applies DecayToZero to the raw P7 counter as well.
def PeerCounters.decay (s : PeerCounters) (p : GlobalScoreParams) : PeerCounters :=
  { s with behavior := Libp2p.decay s.behavior p.behaviorDecay p.decayCutoff }

theorem PeerCounters.initial_valid : ({} : PeerCounters).Valid := Rat.le_refl

theorem PeerCounters.penalize_valid (s : PeerCounters) (amount : Rat)
    (hs : s.Valid) (ha : 0 ≤ amount) : (s.penalize amount).Valid := Rat.add_nonneg hs ha

theorem PeerCounters.decay_valid (s : PeerCounters) (p : GlobalScoreParams)
    (hs : s.Valid) (hp : p.Valid) : (s.decay p).Valid :=
  decay_nonnegative _ _ _ hs (Rat.le_of_lt hp.behavior_decay.1)

theorem PeerCounters.decay_fields (s : PeerCounters) (p : GlobalScoreParams) :
    (s.decay p).behavior = Libp2p.decay s.behavior p.behaviorDecay p.decayCutoff ∧
    (s.decay p).appScore = s.appScore ∧ (s.decay p).ipCount = s.ipCount := ⟨rfl, rfl, rfl⟩

theorem PeerCounters.penalties_nonnegative (s : PeerCounters) (p : GlobalScoreParams) (hs : s.Valid) :
    0 ≤ colocation s.ipCount p.ipThreshold ∧ 0 ≤ squaredPenalty s.behavior :=
  ⟨colocation_nonnegative .., squaredPenalty_nonnegative _ hs⟩

theorem PeerCounters.weighted_penalties_nonpositive (s : PeerCounters) (p : GlobalScoreParams)
    (hs : s.Valid) (hp : p.Valid) :
    p.ipWeight * colocation s.ipCount p.ipThreshold ≤ 0 ∧
    p.behaviorWeight * squaredPenalty s.behavior ≤ 0 := by
  refine ⟨?_, weightedSquared_nonpositive _ _ (Rat.le_of_lt hp.behaviorWeight_negative) hs⟩
  simpa only [Rat.zero_mul] using Rat.mul_le_mul_of_nonneg_right
    (Rat.le_of_lt hp.ipWeight_negative) (colocation_nonnegative s.ipCount p.ipThreshold)

end Libp2p
