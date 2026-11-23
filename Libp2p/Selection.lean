module

public import Libp2p.ScoreThresholds

@[expose] public section
namespace Libp2p.Selection

structure DegreeParams where
  target : Nat
  low : Nat
  high : Nat
  score : Nat
  outbound : Nat
  deriving Repr

-- Enabled-mesh parameters. A mesh-disabled bootstrapper is a separate mode.
def DegreeParams.Valid (p : DegreeParams) : Prop :=
  p.low ≤ p.target ∧ p.target ≤ p.high ∧ p.score ≤ p.target ∧
    p.outbound < p.low ∧ 2 * p.outbound ≤ p.target

instance (p : DegreeParams) : Decidable p.Valid := by unfold DegreeParams.Valid; infer_instance

theorem DegreeParams.validQuotas (p : DegreeParams) (h : p.Valid) :
    Libp2p.validQuotas p.target p.low p.outbound = true := by
  simp only [Libp2p.validQuotas, decide_eq_true_eq]
  exact h.2.2.2

def outboundCount {Peer : Type} (outbound : Peer → Bool) (peers : List Peer) : Nat :=
  peers.countP outbound

-- This is the mesh after negative-score pruning, not an unrelated candidate universe.
def Oversubscribed {Peer : Type} (p : DegreeParams) (mesh : List Peer)
    (score : Peer → Rat) (outbound : Peer → Bool) : Prop :=
  p.Valid ∧ mesh.Nodup ∧ p.high < mesh.length ∧
    (∀ peer ∈ mesh, 0 ≤ score peer) ∧ p.outbound ≤ outboundCount outbound mesh

instance {Peer : Type} [DecidableEq Peer] (p : DegreeParams) (mesh : List Peer)
    (score : Peer → Rat) (outbound : Peer → Bool) : Decidable (Oversubscribed p mesh score outbound) := by
  unfold Oversubscribed; infer_instance

structure SurvivorPlan (Peer : Type) where
  best : List Peer
  random : List Peer
  kept : List Peer
  removed : List Peer
  added : List Peer
  deriving Repr

def SurvivorPlan.initial {Peer : Type} (plan : SurvivorPlan Peer) : List Peer := plan.best ++ plan.random
def SurvivorPlan.survivors {Peer : Type} (plan : SurvivorPlan Peer) : List Peer := plan.kept ++ plan.added

-- "random" denotes nondeterministic choices; no distribution or RNG is specified here.
def InitialSelection {Peer : Type} (p : DegreeParams) (mesh : List Peer)
    (score : Peer → Rat) (plan : SurvivorPlan Peer) : Prop :=
  plan.best.length = p.score ∧ plan.random.length = p.target - p.score ∧
    plan.initial.Nodup ∧ plan.initial ⊆ mesh ∧
    (∀ best ∈ plan.best, ∀ other ∈ mesh, other ∉ plan.best → score other ≤ score best)

instance {Peer : Type} [DecidableEq Peer] (p : DegreeParams) (mesh : List Peer)
    (score : Peer → Rat) (plan : SurvivorPlan Peer) : Decidable (InitialSelection p mesh score plan) := by
  unfold InitialSelection; infer_instance

-- Repair only a deficient selection, adding outbound peers. Victims need not be inbound.
-- A protected victim cannot outrank retained inbound peers; outbound slots may be quota-critical.
-- The source fixes neither the ordering nor a minimal number of replacements.
def QuotaRepair {Peer : Type} (p : DegreeParams) (mesh : List Peer)
    (score : Peer → Rat) (outbound : Peer → Bool) (plan : SurvivorPlan Peer) : Prop :=
  plan.initial.Perm (plan.kept ++ plan.removed) ∧
    (∀ peer ∈ plan.added, peer ∈ mesh ∧ outbound peer = true ∧ peer ∉ plan.initial) ∧
    plan.added.Nodup ∧ plan.added.length = plan.removed.length ∧
    p.outbound + outboundCount outbound plan.removed ≤ outboundCount outbound plan.initial + plan.added.length ∧
    (p.outbound ≤ outboundCount outbound plan.initial → plan.removed = []) ∧
    (∀ removed ∈ plan.removed, removed ∈ plan.random ∨
      ∀ retained ∈ plan.kept, outbound retained = false → score removed ≤ score retained)

instance {Peer : Type} [DecidableEq Peer] (p : DegreeParams) (mesh : List Peer)
    (score : Peer → Rat) (outbound : Peer → Bool) (plan : SurvivorPlan Peer) :
    Decidable (QuotaRepair p mesh score outbound plan) := by
  unfold QuotaRepair; infer_instance

def SurvivorPlan.Valid {Peer : Type} (plan : SurvivorPlan Peer) (p : DegreeParams)
    (mesh : List Peer) (score : Peer → Rat) (outbound : Peer → Bool) : Prop :=
  Oversubscribed p mesh score outbound ∧ InitialSelection p mesh score plan ∧
    QuotaRepair p mesh score outbound plan

instance {Peer : Type} [DecidableEq Peer] (plan : SurvivorPlan Peer) (p : DegreeParams)
    (mesh : List Peer) (score : Peer → Rat) (outbound : Peer → Bool) :
    Decidable (plan.Valid p mesh score outbound) := by unfold SurvivorPlan.Valid; infer_instance

def checkOversubscription {Peer : Type} [DecidableEq Peer] (p : DegreeParams)
    (mesh : List Peer) (score : Peer → Rat) (outbound : Peer → Bool) (plan : SurvivorPlan Peer) : Bool :=
  decide (plan.Valid p mesh score outbound)

theorem checkOversubscription_iff {Peer : Type} [DecidableEq Peer] (p : DegreeParams)
    (mesh : List Peer) (score : Peer → Rat) (outbound : Peer → Bool) (plan : SurvivorPlan Peer) :
    checkOversubscription p mesh score outbound plan = true ↔ plan.Valid p mesh score outbound := by
  simp [checkOversubscription]

theorem SurvivorPlan.initial_cardinality {Peer : Type} (plan : SurvivorPlan Peer)
    (p : DegreeParams) (mesh : List Peer) (score : Peer → Rat) (outbound : Peer → Bool)
    (h : plan.Valid p mesh score outbound) : plan.initial.length = p.target := by
  have hscore := h.1.1.2.2.1
  have hbest := h.2.1.1
  have hrandom := h.2.1.2.1
  simp only [initial, List.length_append]
  omega

theorem SurvivorPlan.survivors_cardinality {Peer : Type} (plan : SurvivorPlan Peer)
    (p : DegreeParams) (mesh : List Peer) (score : Peer → Rat) (outbound : Peer → Bool)
    (h : plan.Valid p mesh score outbound) : plan.survivors.length = p.target := by
  have hlen := h.2.2.1.length_eq
  have heq := h.2.2.2.2.2.1
  have hi := plan.initial_cardinality p mesh score outbound h
  simp only [survivors, List.length_append] at *
  omega

theorem SurvivorPlan.kept_subset_initial {Peer : Type} (plan : SurvivorPlan Peer)
    (p : DegreeParams) (mesh : List Peer) (score : Peer → Rat) (outbound : Peer → Bool)
    (h : plan.Valid p mesh score outbound) : plan.kept ⊆ plan.initial := by
  intro peer hp
  exact h.2.2.1.symm.subset (List.mem_append_left _ hp)

theorem SurvivorPlan.survivors_subset {Peer : Type} (plan : SurvivorPlan Peer)
    (p : DegreeParams) (mesh : List Peer) (score : Peer → Rat) (outbound : Peer → Bool)
    (h : plan.Valid p mesh score outbound) : plan.survivors ⊆ mesh := by
  intro peer hp
  rcases List.mem_append.mp hp with kept | added
  · exact h.2.1.2.2.2.1 (plan.kept_subset_initial p mesh score outbound h kept)
  · exact (h.2.2.2.1 peer added).1

theorem SurvivorPlan.survivors_nodup {Peer : Type} (plan : SurvivorPlan Peer)
    (p : DegreeParams) (mesh : List Peer) (score : Peer → Rat) (outbound : Peer → Bool)
    (h : plan.Valid p mesh score outbound) : plan.survivors.Nodup := by
  have hp := h.2.2.1.nodup h.2.1.2.2.1
  have hk := (List.nodup_append.mp hp).1
  apply List.nodup_append.mpr
  refine ⟨hk, h.2.2.2.2.1, ?_⟩
  intro kept hkept added hadded heq
  have hin := plan.kept_subset_initial p mesh score outbound h hkept
  exact (h.2.2.2.1 added hadded).2.2 (heq ▸ hin)

theorem SurvivorPlan.outbound_count {Peer : Type} (plan : SurvivorPlan Peer)
    (p : DegreeParams) (mesh : List Peer) (score : Peer → Rat) (outbound : Peer → Bool)
    (h : plan.Valid p mesh score outbound) :
    outboundCount outbound plan.survivors + outboundCount outbound plan.removed =
      outboundCount outbound plan.initial + plan.added.length := by
  have ha : plan.added.countP outbound = plan.added.length :=
    List.countP_eq_length.mpr (fun peer hp => (h.2.2.2.1 peer hp).2.1)
  have hp := h.2.2.1.countP_eq outbound
  simp only [List.countP_append] at hp
  simp only [outboundCount, survivors, List.countP_append, ha]
  omega

theorem SurvivorPlan.quota_preserved {Peer : Type} (plan : SurvivorPlan Peer)
    (p : DegreeParams) (mesh : List Peer) (score : Peer → Rat) (outbound : Peer → Bool)
    (h : plan.Valid p mesh score outbound) : p.outbound ≤ outboundCount outbound plan.survivors := by
  have hb := plan.outbound_count p mesh score outbound h
  have hq := h.2.2.2.2.2.2.1
  omega

theorem SurvivorPlan.removed_protected_score_le {Peer : Type} (plan : SurvivorPlan Peer)
    (p : DegreeParams) (mesh : List Peer) (score : Peer → Rat) (outbound : Peer → Bool)
    (h : plan.Valid p mesh score outbound) (removed retained : Peer)
    (hr : removed ∈ plan.removed) (hrb : removed ∈ plan.best)
    (hk : retained ∈ plan.kept) (hin : outbound retained = false) : score removed ≤ score retained := by
  rcases h.2.2.2.2.2.2.2.2 removed hr with random | lower
  · have hd := (List.nodup_append.mp h.2.1.2.2.1).2.2
    exact False.elim (hd removed hrb removed random rfl)
  · exact lower retained hk hin

theorem SurvivorPlan.no_unnecessary_repair {Peer : Type} (plan : SurvivorPlan Peer)
    (p : DegreeParams) (mesh : List Peer) (score : Peer → Rat) (outbound : Peer → Bool)
    (h : plan.Valid p mesh score outbound) (hq : p.outbound ≤ outboundCount outbound plan.initial) :
    plan.initial.Perm plan.survivors := by
  have hr : plan.removed = [] := h.2.2.2.2.2.2.2.1 hq
  have ha : plan.added = [] := List.eq_nil_of_length_eq_zero (by simpa [hr] using h.2.2.2.2.2.1)
  simpa [survivors, hr, ha] using h.2.2.1

theorem oversubscription_sound {Peer : Type} [DecidableEq Peer] (p : DegreeParams)
    (mesh : List Peer) (score : Peer → Rat) (outbound : Peer → Bool) (plan : SurvivorPlan Peer)
    (h : checkOversubscription p mesh score outbound plan = true) :
    plan.survivors.Nodup ∧ plan.survivors ⊆ mesh ∧ plan.survivors.length = p.target ∧
    p.outbound ≤ outboundCount outbound plan.survivors ∧
    (∀ peer ∈ plan.survivors, 0 ≤ score peer) ∧
    (∀ best ∈ plan.best, ∀ other ∈ mesh, other ∉ plan.best → score other ≤ score best) := by
  have hv := (checkOversubscription_iff ..).mp h
  have hsub := plan.survivors_subset p mesh score outbound hv
  exact ⟨plan.survivors_nodup p mesh score outbound hv, hsub,
    plan.survivors_cardinality p mesh score outbound hv, plan.quota_preserved p mesh score outbound hv,
    fun peer hp => hv.1.2.2.2.1 peer (hsub hp), hv.2.1.2.2.2.2⟩

def prunedPeers {Peer : Type} [DecidableEq Peer] (mesh survivors : List Peer) : List Peer :=
  mesh.filter fun peer => decide (peer ∉ survivors)

theorem SurvivorPlan.prune_partition {Peer : Type} [DecidableEq Peer] (plan : SurvivorPlan Peer)
    (p : DegreeParams) (mesh : List Peer) (score : Peer → Rat) (outbound : Peer → Bool)
    (h : plan.Valid p mesh score outbound) :
    (plan.survivors ++ prunedPeers mesh plan.survivors).Perm mesh := by
  have hs := plan.survivors_subset p mesh score outbound h
  have hn := plan.survivors_nodup p mesh score outbound h
  have hf : (mesh.filter fun peer => decide (peer ∈ plan.survivors)).Perm plan.survivors := by
    apply (List.perm_ext_iff_of_nodup (h.1.2.1.filter _) hn).mpr
    intro peer
    simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨And.right, fun hp => ⟨hs hp, hp⟩⟩
  have hp : ((mesh.filter fun peer => decide (peer ∈ plan.survivors)) ++
      prunedPeers mesh plan.survivors).Perm mesh := by
    simpa [prunedPeers] using List.filter_append_perm (fun peer => decide (peer ∈ plan.survivors)) mesh
  exact (hf.symm.append_right _).trans hp

theorem SurvivorPlan.pruned_cardinality {Peer : Type} [DecidableEq Peer] (plan : SurvivorPlan Peer)
    (p : DegreeParams) (mesh : List Peer) (score : Peer → Rat) (outbound : Peer → Bool)
    (h : plan.Valid p mesh score outbound) :
    (prunedPeers mesh plan.survivors).length = mesh.length - p.target := by
  have hp := (plan.prune_partition p mesh score outbound h).length_eq
  rw [List.length_append, plan.survivors_cardinality p mesh score outbound h] at hp
  omega

theorem checkOversubscription_not_high {Peer : Type} [DecidableEq Peer] (p : DegreeParams)
    (mesh : List Peer) (score : Peer → Rat) (outbound : Peer → Bool) (plan : SurvivorPlan Peer)
    (hd : mesh.length ≤ p.high) : checkOversubscription p mesh score outbound plan = false := by
  cases he : checkOversubscription p mesh score outbound plan with
  | false => rfl
  | true => exact False.elim (Nat.not_lt_of_ge hd ((checkOversubscription_iff ..).mp he).1.2.2.1)

-- Rank relation: odd size pins the middle score; even size permits the closed middle interval.
-- No average/lower/upper convention is chosen. Callers must supply a checked witness.
def IsMedian {Peer : Type} (mesh : List Peer) (score : Peer → Rat) (median : Rat) : Prop :=
  mesh.Nodup ∧ mesh ≠ [] ∧
    (mesh.countP fun peer => decide (score peer < median)) ≤ mesh.length / 2 ∧
    (mesh.countP fun peer => decide (median < score peer)) ≤ mesh.length / 2

instance {Peer : Type} [DecidableEq Peer] (mesh : List Peer) (score : Peer → Rat) (median : Rat) :
    Decidable (IsMedian mesh score median) := by unfold IsMedian; infer_instance

def checkMedian {Peer : Type} [DecidableEq Peer] (mesh : List Peer)
    (score : Peer → Rat) (median : Rat) : Bool := decide (IsMedian mesh score median)

theorem checkMedian_iff {Peer : Type} [DecidableEq Peer] (mesh : List Peer)
    (score : Peer → Rat) (median : Rat) : checkMedian mesh score median = true ↔ IsMedian mesh score median := by
  simp [checkMedian]

theorem IsMedian.odd_attained {Peer : Type} (mesh : List Peer) (score : Peer → Rat) (median : Rat)
    (h : IsMedian mesh score median) (hodd : mesh.length % 2 = 1) :
    ∃ peer ∈ mesh, score peer = median := by
  classical
  by_cases he : ∃ peer ∈ mesh, score peer = median
  · exact he
  · have hne : ∀ peer ∈ mesh, median ≠ score peer := fun peer hp heq => he ⟨peer, hp, heq.symm⟩
    have hc : mesh.countP (fun peer => decide (¬score peer < median)) =
        mesh.countP (fun peer => decide (median < score peer)) := by
      apply List.countP_congr
      intro peer hp
      simp [Rat.not_lt, Rat.le_iff_eq_or_lt, hne peer hp]
    have hlen := List.length_eq_countP_add_countP (fun peer => decide (score peer < median)) (l := mesh)
    simp only [decide_eq_true_eq] at hlen
    rw [hc] at hlen
    have hlo := h.2.2.1
    have hhi := h.2.2.2
    omega

theorem IsMedian.permutation {Peer : Type} (mesh reordered : List Peer) (score : Peer → Rat)
    (median : Rat) (hp : mesh.Perm reordered) (h : IsMedian mesh score median) :
    IsMedian reordered score median := by
  refine ⟨hp.nodup h.1, ?_, ?_, ?_⟩
  · intro he
    exact h.2.1 ((hp.trans (he ▸ List.Perm.refl [])).eq_nil)
  · rw [← hp.countP_eq, ← hp.length_eq]
    exact h.2.2.1
  · rw [← hp.countP_eq, ← hp.length_eq]
    exact h.2.2.2

theorem IsMedian.between {Peer : Type} (mesh : List Peer) (score : Peer → Rat) (lower median upper : Rat)
    (hl : IsMedian mesh score lower) (hu : IsMedian mesh score upper)
    (hlm : lower ≤ median) (hmu : median ≤ upper) : IsMedian mesh score median := by
  refine ⟨hl.1, hl.2.1, ?_, ?_⟩
  · apply Nat.le_trans (List.countP_mono_left (p := fun peer => decide (score peer < median))
      (q := fun peer => decide (score peer < upper)) ?_) hu.2.2.1
    intro peer _ hp
    apply decide_eq_true ((Rat.not_le).mp ?_)
    intro hn
    exact (Rat.not_le.mpr (of_decide_eq_true hp)) (Rat.le_trans hmu hn)
  · apply Nat.le_trans (List.countP_mono_left (p := fun peer => decide (median < score peer))
      (q := fun peer => decide (lower < score peer)) ?_) hl.2.2.2
    intro peer _ hp
    apply decide_eq_true ((Rat.not_le).mp ?_)
    intro hn
    exact (Rat.not_le.mpr (of_decide_eq_true hp)) (Rat.le_trans hn hlm)

def opportunisticPool {Peer : Type} [DecidableEq Peer] (mesh candidates : List Peer)
    (score : Peer → Rat) (median : Rat) : List Peer :=
  candidates.filter fun peer => decide (peer ∉ mesh ∧ 0 ≤ score peer ∧ median < score peer)

theorem mem_opportunisticPool {Peer : Type} [DecidableEq Peer] (mesh candidates : List Peer)
    (score : Peer → Rat) (median : Rat) (peer : Peer) :
    peer ∈ opportunisticPool mesh candidates score median ↔
      peer ∈ candidates ∧ peer ∉ mesh ∧ 0 ≤ score peer ∧ median < score peer := by
  simp [opportunisticPool]

def OpportunisticSelection {Peer : Type} [DecidableEq Peer] (mesh candidates : List Peer)
    (score : Peer → Rat) (threshold median : Rat) (requested : Nat) (chosen : List Peer) : Prop :=
  0 ≤ threshold ∧ mesh.Nodup ∧ candidates.Nodup ∧ IsMedian mesh score median ∧ median < threshold ∧
    2 ≤ requested ∧ chosen.Nodup ∧ chosen.length = requested ∧
    chosen ⊆ opportunisticPool mesh candidates score median

instance {Peer : Type} [DecidableEq Peer] (mesh candidates : List Peer)
    (score : Peer → Rat) (threshold median : Rat) (requested : Nat) (chosen : List Peer) :
    Decidable (OpportunisticSelection mesh candidates score threshold median requested chosen) := by
  unfold OpportunisticSelection; infer_instance

def checkOpportunistic {Peer : Type} [DecidableEq Peer] (mesh candidates : List Peer)
    (score : Peer → Rat) (threshold median : Rat) (requested : Nat) (chosen : List Peer) : Bool :=
  decide (OpportunisticSelection mesh candidates score threshold median requested chosen)

theorem checkOpportunistic_iff {Peer : Type} [DecidableEq Peer] (mesh candidates : List Peer)
    (score : Peer → Rat) (threshold median : Rat) (requested : Nat) (chosen : List Peer) :
    checkOpportunistic mesh candidates score threshold median requested chosen = true ↔
      OpportunisticSelection mesh candidates score threshold median requested chosen := by
  simp [checkOpportunistic]

theorem opportunistic_sound {Peer : Type} [DecidableEq Peer] (mesh candidates : List Peer)
    (score : Peer → Rat) (threshold median : Rat) (requested : Nat) (chosen : List Peer)
    (h : checkOpportunistic mesh candidates score threshold median requested chosen = true) :
    IsMedian mesh score median ∧ median < threshold ∧ 2 ≤ requested ∧ chosen.length = requested ∧
      chosen.Nodup ∧ (∀ peer ∈ chosen, peer ∈ candidates ∧ peer ∉ mesh ∧
        0 ≤ score peer ∧ median < score peer) := by
  rcases (checkOpportunistic_iff ..).mp h with ⟨_, _, _, hm, ht, hn, hc, hlen, hsub⟩
  refine ⟨hm, ht, hn, hlen, hc, ?_⟩
  intro peer hp
  exact (mem_opportunisticPool ..).mp (hsub hp)

theorem opportunistic_capacity {Peer : Type} [DecidableEq Peer] (mesh candidates : List Peer)
    (score : Peer → Rat) (threshold median : Rat) (requested : Nat) (chosen : List Peer)
    (h : checkOpportunistic mesh candidates score threshold median requested chosen = true) :
    requested ≤ (opportunisticPool mesh candidates score median).length := by
  rcases (checkOpportunistic_iff ..).mp h with ⟨_, _, _, _, _, _, hc, hlen, hsub⟩
  rw [← hlen]
  exact hc.length_le_of_subset hsub

theorem opportunistic_new_mesh {Peer : Type} [DecidableEq Peer] (mesh candidates : List Peer)
    (score : Peer → Rat) (threshold median : Rat) (requested : Nat) (chosen : List Peer)
    (h : checkOpportunistic mesh candidates score threshold median requested chosen = true) :
    (mesh ++ chosen).Nodup ∧ (mesh ++ chosen).length = mesh.length + requested := by
  have hv := (checkOpportunistic_iff ..).mp h
  have hs := opportunistic_sound mesh candidates score threshold median requested chosen h
  refine ⟨List.nodup_append.mpr ⟨hv.2.1, hs.2.2.2.2.1, ?_⟩, ?_⟩
  · intro old hold added hadd heq
    exact (hs.2.2.2.2.2 added hadd).2.1 (heq ▸ hold)
  · simp [hs.2.2.2.1]

theorem checkOpportunistic_insufficient {Peer : Type} [DecidableEq Peer] (mesh candidates : List Peer)
    (score : Peer → Rat) (threshold median : Rat) (requested : Nat) (chosen : List Peer)
    (hc : (opportunisticPool mesh candidates score median).length < requested) :
    checkOpportunistic mesh candidates score threshold median requested chosen = false := by
  cases he : checkOpportunistic mesh candidates score threshold median requested chosen with
  | false => rfl
  | true =>
    exact False.elim (Nat.not_lt_of_ge
      (opportunistic_capacity mesh candidates score threshold median requested chosen he) hc)

end Libp2p.Selection
