module

public import Libp2p.NetworkSafety

public section
namespace Libp2p.Network
open Classical

 theorem erase_dups_nodup {A : Type} [DecidableEq A] (peers : List A) : peers.eraseDups.Nodup := by
  cases peers with
  | nil => simp
  | cons p peers =>
    rw [List.eraseDups_cons, List.nodup_cons]
    exact ⟨by simp, erase_dups_nodup (peers.filter fun q => !q == p)⟩
termination_by peers.length
 decreasing_by
  have h := List.length_filter_le (fun q => !q == p) peers
  simp only [List.length_cons]
  omega

variable (S P I W O C ID Protocol V T : Type)
variable [Inhabited S] [Inhabited P] [Inhabited I] [Inhabited W]
variable [Inhabited O] [Inhabited C] [Inhabited ID] [Inhabited Protocol]
variable [Inhabited V] [Inhabited T] [Pipeline.Verdict_EnumClass V]
local notation "Th" => Theory S P I W O C ID Protocol T
local notation "St" => State S P I W O C ID Protocol V T
local notation "sys" => system S P I W O C ID Protocol V T
local notation "rt" => routingTheory S P I W O C ID Protocol T
local notation "roster" => meshRoster S P I W O C ID Protocol V T
local notation "candidates" => candidateRoster S P I W O C ID Protocol V T
local notation "outbound" => outboundPeer S P I W O C ID Protocol V T

 theorem mesh_roster_exact {th : Th} {st : St} (reachable : (sys).reachable th st) (t : T) (p : P) :
    p ∈ roster th st t ↔ st.routing.mesh p t = true :=
  Routing.mesh_roster_exact P T W ID (P → Rat) (rt th) st.routing
    (routing_reachable S P I W O C ID Protocol V T reachable) t p

 theorem mesh_roster_nodup (th : Th) (st : St) (t : T) : (roster th st t).Nodup := by
  exact (erase_dups_nodup th.knownPeers).filter _

 theorem candidate_roster_iff (th : Th) (st : St) (t : T) (p : P) :
    p ∈ candidates th st t ↔ p ∈ th.knownPeers ∧ st.routing.subscribed p t = true ∧
      connected S P I W O C ID Protocol V T th st p = true ∧ th.explicitPeer p = false ∧
      st.routing.backoff p t = false ∧ 0 ≤ st.routing.currentSnapshot p ∧ st.routing.mesh p t = false := by
  simp [candidateRoster, ScoreThresholds.classify, atLeastThreshold, and_assoc]

 theorem oversubscription_membership {th : Th} {st : St} (reachable : (sys).reachable th st)
    (next : St) (t : T) (plan : Selection.SurvivorPlan P)
    (step : (sys).tr th st (.oversubscribe t plan) next) :
    (roster th next t).Perm plan.survivors := by
  have checked := step.1
  have sound := Selection.oversubscription_sound th.degree (roster th st t)
    st.routing.currentSnapshot (outbound th st) plan checked
  have reached : (sys).reachable th next := .step _ _ reachable ⟨_, step⟩
  apply (List.perm_ext_iff_of_nodup (mesh_roster_nodup S P I W O C ID Protocol V T th next t) sound.1).mpr
  intro p
  rw [mesh_roster_exact S P I W O C ID Protocol V T reached t p,
    NetworkRoutingFacts.prune_transaction P T W ID (P → Rat) (rt th) _ _ _ t step.2.2 p,
    ← mesh_roster_exact S P I W O C ID Protocol V T reachable t p]
  simp only [Selection.prunedPeers, List.mem_filter, decide_eq_true_eq]
  constructor
  · intro h
    by_contra missing
    exact h.2 ⟨h.1, missing⟩
  · intro member
    exact ⟨sound.2.1 member, fun h => h.2 member⟩

 theorem oversubscription_result {th : Th} {st : St} (reachable : (sys).reachable th st)
    (next : St) (t : T) (plan : Selection.SurvivorPlan P)
    (step : (sys).tr th st (.oversubscribe t plan) next) :
    (roster th next t).Perm plan.survivors ∧ (roster th next t).length = th.degree.target ∧
    th.degree.outbound ≤ Selection.outboundCount (outbound th next) (roster th next t) ∧
    (∀ p ∈ Selection.prunedPeers (roster th st t) plan.survivors, next.routing.backoff p t = true) := by
  have membership := oversubscription_membership S P I W O C ID Protocol V T reachable next t plan step
  have sound := Selection.oversubscription_sound th.degree (roster th st t)
    st.routing.currentSnapshot (outbound th st) plan step.1
  have coreFrame := Runs.nil_iff.mp step.2.1
  have outboundFrame : outbound th next = outbound th st := by
    funext p
    simp only [outboundPeer, coreFrame]
  refine ⟨membership, membership.length_eq.trans sound.2.2.1, ?_, ?_⟩
  · rw [outboundFrame, Selection.outboundCount, membership.countP_eq]
    exact sound.2.2.2.1
  · intro p removed
    exact (NetworkRoutingFacts.prune_backoff_transaction P T W ID (P → Rat) (rt th) _ _ _ t
      step.2.2 p).mpr (Or.inr removed)

 theorem opportunistic_membership {th : Th} {st : St} (reachable : (sys).reachable th st)
    (next : St) (t : T) (median : Rat) (requested : Nat) (chosen : List P)
    (step : (sys).tr th st (.opportunistic t median requested chosen) next) :
    (roster th next t).Perm (roster th st t ++ chosen) := by
  have expected := Selection.opportunistic_new_mesh (roster th st t) (candidates th st t)
    st.routing.currentSnapshot th.thresholds.opportunistic median requested chosen step.1.2
  have reached : (sys).reachable th next := .step _ _ reachable ⟨_, step⟩
  apply (List.perm_ext_iff_of_nodup (mesh_roster_nodup S P I W O C ID Protocol V T th next t) expected.1).mpr
  intro p
  rw [mesh_roster_exact S P I W O C ID Protocol V T reached t p,
    NetworkRoutingFacts.local_graft_transaction P T W ID (P → Rat) (rt th) _ _ chosen t step.2.2 p,
    List.mem_append, mesh_roster_exact S P I W O C ID Protocol V T reachable t p]

 theorem opportunistic_result {th : Th} {st : St} (reachable : (sys).reachable th st)
    (next : St) (t : T) (median : Rat) (requested : Nat) (chosen : List P)
    (step : (sys).tr th st (.opportunistic t median requested chosen) next) :
    (roster th next t).Perm (roster th st t ++ chosen) ∧
    (roster th next t).length = (roster th st t).length + requested ∧
    Selection.IsMedian (roster th st t) st.routing.currentSnapshot median ∧
    median < th.thresholds.opportunistic ∧ 2 ≤ requested ∧
    (∀ p ∈ chosen, next.routing.mesh p t = true ∧ p ∈ candidates th st t ∧
      median < st.routing.currentSnapshot p) := by
  have membership := opportunistic_membership S P I W O C ID Protocol V T
    reachable next t median requested chosen step
  have sound := Selection.opportunistic_sound (roster th st t) (candidates th st t)
    st.routing.currentSnapshot th.thresholds.opportunistic median requested chosen step.1.2
  have expected := Selection.opportunistic_new_mesh (roster th st t) (candidates th st t)
    st.routing.currentSnapshot th.thresholds.opportunistic median requested chosen step.1.2
  refine ⟨membership, membership.length_eq.trans expected.2, sound.1, sound.2.1, sound.2.2.1, ?_⟩
  intro p selected
  have admissible := sound.2.2.2.2.2 p selected
  exact ⟨(NetworkRoutingFacts.local_graft_transaction P T W ID (P → Rat) (rt th) _ _ chosen t
      step.2.2 p).mpr (Or.inr selected), admissible.1, admissible.2.2.2⟩

end Libp2p.Network
