module

public import Libp2p.ScoreLemmas

@[expose] public section
namespace Libp2p

structure ScoreThresholds where
  gossip : Rat
  publish : Rat
  graylist : Rat
  acceptPX : Rat
  opportunistic : Rat
  deriving Repr

structure ScoreThresholds.Valid (t : ScoreThresholds) : Prop where
  gossip_negative : t.gossip < 0
  publish_le_gossip : t.publish ≤ t.gossip
  graylist_lt_publish : t.graylist < t.publish
  px_nonnegative : 0 ≤ t.acceptPX
  opportunistic_nonnegative : 0 ≤ t.opportunistic

structure ScoreEligibility where
  nonnegative : Bool
  gossip : Bool
  publish : Bool
  rpc : Bool
  px : Bool
  deriving DecidableEq, Repr

def ScoreThresholds.classify (t : ScoreThresholds) (score : Rat) : ScoreEligibility :=
  { nonnegative := atLeastThreshold score 0
    gossip := atLeastThreshold score t.gossip
    publish := atLeastThreshold score t.publish
    rpc := atLeastThreshold score t.graylist
    px := Libp2p.acceptPX score t.acceptPX }

def ScoreThresholds.opportunisticTrigger (t : ScoreThresholds) (median : Rat) : Bool :=
  aboveThreshold t.opportunistic median

def opportunisticCandidate (score median : Rat) : Bool := aboveThreshold score median

theorem ScoreThresholds.classify_refines (t : ScoreThresholds) (score : Rat) :
    ((t.classify score).nonnegative = true ↔ 0 ≤ score) ∧
    ((t.classify score).gossip = true ↔ t.gossip ≤ score) ∧
    ((t.classify score).publish = true ↔ t.publish ≤ score) ∧
    ((t.classify score).rpc = true ↔ t.graylist ≤ score) ∧
    ((t.classify score).px = true ↔ t.acceptPX < score) := by
  simp [classify, atLeastThreshold, Libp2p.acceptPX, aboveThreshold]

theorem ScoreThresholds.boundary_equalities (t : ScoreThresholds) :
    (t.classify 0).nonnegative = true ∧
    (t.classify t.gossip).gossip = true ∧
    (t.classify t.publish).publish = true ∧
    (t.classify t.graylist).rpc = true ∧
    (t.classify t.acceptPX).px = false ∧
    t.opportunisticTrigger t.opportunistic = false := by
  simp [classify, atLeastThreshold, Libp2p.acceptPX, aboveThreshold,
    opportunisticTrigger, Rat.lt_irrefl]

theorem ScoreThresholds.gossip_implies_publish (t : ScoreThresholds) (score : Rat)
    (ht : t.Valid) (h : (t.classify score).gossip = true) :
    (t.classify score).publish = true :=
  (atLeastThreshold_iff ..).mpr (Rat.le_trans ht.publish_le_gossip ((atLeastThreshold_iff ..).mp h))

theorem ScoreThresholds.publish_implies_rpc (t : ScoreThresholds) (score : Rat)
    (ht : t.Valid) (h : (t.classify score).publish = true) :
    (t.classify score).rpc = true :=
  (atLeastThreshold_iff ..).mpr
    (Rat.le_trans (Rat.le_of_lt ht.graylist_lt_publish) ((atLeastThreshold_iff ..).mp h))

theorem ScoreThresholds.px_implies_nonnegative (t : ScoreThresholds) (score : Rat)
    (ht : t.Valid) (h : (t.classify score).px = true) :
    (t.classify score).nonnegative = true :=
  (atLeastThreshold_iff ..).mpr
    (Rat.le_trans ht.px_nonnegative (Rat.le_of_lt ((aboveThreshold_iff ..).mp h)))

theorem ScoreThresholds.opportunisticTrigger_iff (t : ScoreThresholds) (median : Rat) :
    t.opportunisticTrigger median = true ↔ median < t.opportunistic := aboveThreshold_iff ..

theorem opportunisticCandidate_iff (score median : Rat) :
    opportunisticCandidate score median = true ↔ median < score := aboveThreshold_iff ..

theorem opportunisticCandidate_equality (median : Rat) : opportunisticCandidate median median = false := by
  simp [opportunisticCandidate, aboveThreshold, Rat.lt_irrefl]

end Libp2p
