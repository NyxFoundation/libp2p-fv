module

public import Libp2p.Policies

@[expose] public section
namespace Libp2p

theorem scoreMin_nonnegative {a b : Rat} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ min a b := by
  rw [Rat.min_def]
  split <;> assumption

theorem scoreMin_le_left (a b : Rat) : min a b ≤ a := by
  rw [Rat.min_def]
  split
  · exact Rat.le_refl
  · exact Rat.le_of_lt (Rat.not_le.mp ‹_›)

theorem scoreMin_le_right (a b : Rat) : min a b ≤ b := by
  rw [Rat.min_def]
  split
  · assumption
  · exact Rat.le_refl

theorem p1_bounds (time quantum : Nat) (cap : Rat) (hc : 0 ≤ cap) :
    0 ≤ p1 time quantum cap ∧ p1 time quantum cap ≤ cap :=
  ⟨scoreMin_nonnegative Rat.natCast_nonneg hc, scoreMin_le_right _ _⟩

theorem p1_quotient (time quantum : Nat) (cap : Rat)
    (h : (time / quantum : Nat) ≤ (cap : Rat)) :
    p1 time quantum cap = (time / quantum : Nat) := by
  simp [p1, Rat.min_def, h]

theorem p1_cap (time quantum : Nat) (cap : Rat)
    (h : cap ≤ (time / quantum : Nat)) : p1 time quantum cap = cap := by
  simp only [p1, Rat.min_def]
  split
  · exact Rat.le_antisymm ‹_› h
  · rfl

theorem creditFirst_nonnegative (n cap : Rat) (hn : 0 ≤ n) (hc : 0 ≤ cap) :
    0 ≤ creditFirst n cap :=
  scoreMin_nonnegative (Rat.add_nonneg hn (by decide)) hc

theorem creditFirst_increment (n cap : Rat) (h : n + 1 ≤ cap) :
    creditFirst n cap = n + 1 := by simp [creditFirst, Rat.min_def, h]

theorem creditFirst_at_cap (n cap : Rat) (h : cap ≤ n + 1) :
    creditFirst n cap = cap := by
  simp only [creditFirst, Rat.min_def]
  split
  · exact Rat.le_antisymm ‹_› h
  · rfl

theorem deficit_active (time activation : Nat) (deliveries threshold : Rat)
    (ht : activation < time) (hd : deliveries < threshold) :
    deficit time activation deliveries threshold = (threshold - deliveries) ^ 2 := by
  simp [deficit, Nat.not_le.mpr ht, Rat.not_le.mpr hd]

theorem deficit_nonnegative (time activation : Nat) (deliveries threshold : Rat) :
    0 ≤ deficit time activation deliveries threshold := by
  unfold deficit
  split
  · exact Rat.le_refl
  · apply Rat.pow_nonneg
    exact Rat.le_of_lt ((Rat.lt_iff_sub_pos _ _).mp (Rat.not_le.mp (not_or.mp ‹_›).2))

theorem p3b_nonnegative (old : Rat) (time activation : Nat) (deliveries threshold : Rat)
    (prune : Bool) (ho : 0 ≤ old) : 0 ≤ p3b old time activation deliveries threshold prune := by
  unfold p3b
  split
  · exact Rat.add_nonneg ho (deficit_nonnegative ..)
  · exact ho

theorem p3b_trigger (old : Rat) (time activation : Nat) (deliveries threshold : Rat)
    (ht : activation < time) (hd : deliveries < threshold) :
    p3b old time activation deliveries threshold true = old + (threshold - deliveries) ^ 2 := by
  simp [p3b, deficit_active _ _ _ _ ht hd]

theorem p3b_inactive (old : Rat) (time activation : Nat) (deliveries threshold : Rat)
    (prune : Bool) (h : time ≤ activation ∨ threshold ≤ deliveries) :
    p3b old time activation deliveries threshold prune = old := by
  simp [p3b, deficit, h, Rat.add_zero]

theorem squaredPenalty_nonnegative (counter : Rat) (hc : 0 ≤ counter) :
    0 ≤ squaredPenalty counter := Rat.pow_nonneg hc

theorem squaredPenalty_eq_mul (counter : Rat) : squaredPenalty counter = counter * counter := by
  simp [squaredPenalty, Rat.pow_succ]

theorem weightedSquared_nonpositive (weight counter : Rat) (hw : weight ≤ 0) (hc : 0 ≤ counter) :
    weight * squaredPenalty counter ≤ 0 := by
  simpa only [Rat.zero_mul] using
    Rat.mul_le_mul_of_nonneg_right hw (squaredPenalty_nonnegative counter hc)

theorem colocation_nonnegative (count threshold : Nat) : 0 ≤ colocation count threshold :=
  Rat.natCast_nonneg

theorem colocation_above_threshold (count threshold : Nat) (h : threshold < count) :
    colocation count threshold = ((count : Rat) - (threshold : Rat)) ^ 2 := by
  have hc : threshold ≤ count := Nat.le_of_lt h
  have he : ((count - threshold : Nat) : Rat) = (count : Rat) - (threshold : Rat) := by
    rw [← Rat.intCast_natCast, Int.ofNat_sub hc, Rat.intCast_sub]
    rfl
  rw [colocation, Rat.natCast_pow, he]

theorem decay_nonnegative (counter factor cutoff : Rat)
    (hc : 0 ≤ counter) (hf : 0 ≤ factor) : 0 ≤ decay counter factor cutoff := by
  dsimp only [decay]
  split
  · exact Rat.le_refl
  · exact Rat.mul_nonneg hc hf

theorem decay_strict (counter factor cutoff : Rat) (hc : 0 < counter) (hf : factor < 1) :
    decay counter factor cutoff < counter := by
  dsimp only [decay]
  split
  · exact hc
  · simpa using Rat.mul_lt_mul_of_pos_left hf hc

theorem decay_below_cutoff (counter factor cutoff : Rat) (h : counter * factor < cutoff) :
    decay counter factor cutoff = 0 := by simp [decay, h]

theorem decay_retains (counter factor cutoff : Rat) (h : cutoff ≤ counter * factor) :
    decay counter factor cutoff = counter * factor := ite_eq_right (Rat.not_lt.mpr h)

theorem decay_at_cutoff (counter factor cutoff : Rat) (h : counter * factor = cutoff) :
    decay counter factor cutoff = cutoff := by simp [decay, h, Rat.lt_irrefl]

theorem decay_zero (factor cutoff : Rat) : decay 0 factor cutoff = 0 := by simp [decay]

theorem squaredPenalty_after_decay (counter factor cutoff : Rat) (h : cutoff ≤ counter * factor) :
    squaredPenalty (decay counter factor cutoff) = squaredPenalty counter * (factor * factor) := by
  rw [decay_retains _ _ _ h, squaredPenalty_eq_mul, squaredPenalty_eq_mul]
  rw [Rat.mul_assoc counter factor (counter * factor), ← Rat.mul_assoc factor counter factor,
    Rat.mul_comm factor counter, Rat.mul_assoc counter factor factor,
    ← Rat.mul_assoc counter counter (factor * factor)]

theorem capScore_none (score : Rat) : capScore score none = score := rfl

theorem capScore_uncapped (score cap : Rat) (h : score ≤ cap) :
    capScore score (some cap) = score := by simp [capScore, Rat.min_def, h]

theorem capScore_capped (score cap : Rat) (h : cap ≤ score) :
    capScore score (some cap) = cap := by
  simp only [capScore, Rat.min_def]
  split
  · exact Rat.le_antisymm ‹_› h
  · rfl

theorem topicScoreSum_cons (topic : TopicScore) (topics : List TopicScore) :
    topicScoreSum (topic :: topics) = topic.value + topicScoreSum topics := rfl

theorem topicScoreSum_append (a b : List TopicScore) :
    topicScoreSum (a ++ b) = topicScoreSum a + topicScoreSum b := by
  induction a with
  | nil => simp [topicScoreSum, Rat.zero_add]
  | cons t ts ih => simp only [List.cons_append, topicScoreSum_cons, ih, Rat.add_assoc]

theorem totalScore_equation (topics : List TopicScore) (cap : Option Rat)
    (w5 p5 w6 w7 p6 p7 : Rat) :
    totalScore topics cap w5 p5 w6 w7 p6 p7 =
      capScore (topicScoreSum topics) cap + w5 * p5 + w6 * p6 + w7 * p7 := rfl

theorem totalScore_cap_bound (topics : List TopicScore) (cap w5 p5 w6 w7 p6 p7 : Rat) :
    totalScore topics (some cap) w5 p5 w6 w7 p6 p7 ≤
      cap + w5 * p5 + w6 * p6 + w7 * p7 := by
  exact Rat.add_le_add_right.mpr (Rat.add_le_add_right.mpr
    (Rat.add_le_add_right.mpr (scoreMin_le_right _ _)))

theorem atLeastThreshold_iff (score threshold : Rat) :
    atLeastThreshold score threshold = true ↔ threshold ≤ score := by simp [atLeastThreshold]

theorem belowThreshold_iff (score threshold : Rat) :
    atLeastThreshold score threshold = false ↔ score < threshold := by
  simp [atLeastThreshold, Rat.not_le]

theorem aboveThreshold_iff (score threshold : Rat) :
    aboveThreshold score threshold = true ↔ threshold < score := by simp [aboveThreshold]

theorem atLeastThreshold_equality (score : Rat) : atLeastThreshold score score = true := by
  simp [atLeastThreshold]

theorem atLeastThreshold_cross_product (score threshold : Rat) :
    atLeastThreshold score threshold = true ↔
      threshold.num * score.den ≤ score.num * threshold.den := by
  rw [atLeastThreshold_iff, Rat.le_iff]

theorem acceptPX_cross_product (score threshold : Rat) :
    acceptPX score threshold = true ↔
      threshold.num * score.den < score.num * threshold.den := by
  simp only [acceptPX, aboveThreshold_iff, Rat.lt_iff]

theorem score_equality_cross_product (a b : Rat) :
    a = b ↔ a.num * b.den = b.num * a.den := Rat.eq_iff_mul_eq_mul

theorem eligibleGraft_iff (score : Rat) (explicit backoff full outbound : Bool) :
    eligibleGraft score explicit backoff full outbound = true ↔
      0 ≤ score ∧ explicit = false ∧ backoff = false ∧ (full = false ∨ outbound = true) := by
  simp [eligibleGraft, atLeastThreshold, and_assoc]

theorem validQuotas_iff (d low outbound : Nat) :
    validQuotas d low outbound = true ↔ outbound < low ∧ outbound ≤ d / 2 := by
  simp only [validQuotas, decide_eq_true_eq]
  omega

end Libp2p
