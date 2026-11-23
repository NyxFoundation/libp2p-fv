module

public import Libp2p.Network

@[expose] public section
namespace Libp2p.NetworkRoutingFacts
open Classical

variable (P T W ID Snapshot : Type)
variable [Inhabited P] [Inhabited T] [Inhabited W] [Inhabited ID] [Inhabited Snapshot]
local notation "RT" => Routing.Theory P T W ID Snapshot
local notation "RS" => Routing.State (Routing.FieldAbstractType P T W ID Snapshot)
local notation "RL" => Routing.Label P T W ID Snapshot
local notation "sys" => Routing.relationalTransitionSystem P T W ID Snapshot

def ValidationGate (authorized : W → Prop) (localInput : W → Bool) : RL → Prop
  | .validatedRemote w => authorized w ∧ localInput w = false
  | .validatedLocal w => authorized w ∧ localInput w = true
  | _ => True

theorem validation_bound (th : RT) (st next : RS) (label : RL)
    (authorized : W → Prop) (localInput : W → Bool)
    (step : (sys).tr th st label next)
    (gate : ValidationGate P T W ID Snapshot authorized localInput label)
    (bound : ∀ w, st.valid w = true → authorized w ∧ st.localPublication w = localInput w) :
    ∀ w, next.valid w = true → authorized w ∧ next.localPublication w = localInput w := by
  intro w valid
  cases label <;>
    simp only [Routing.relationalTransitionSystem, Routing.Next, Routing.NextAct, nextSimp,
      Routing.State.ext_iff, funext_iff] at step <;>
    simp only [ValidationGate] at gate <;> grind

theorem transaction_validation_bound (th : RT) (st next : RS) (labels : List RL)
    (authorized : W → Prop) (localInput : W → Bool) (run : Runs sys th st labels next)
    (gate : ∀ label ∈ labels, ValidationGate P T W ID Snapshot authorized localInput label)
    (bound : ∀ w, st.valid w = true → authorized w ∧ st.localPublication w = localInput w) :
    ∀ w, next.valid w = true → authorized w ∧ next.localPublication w = localInput w := by
  induction run with
  | nil => exact bound
  | @cons before middle after label labels step rest ih =>
    apply ih
    · intro action member
      exact gate action (List.mem_cons_of_mem label member)
    · exact validation_bound P T W ID Snapshot th before middle label authorized localInput step
        (gate label List.mem_cons_self) bound

theorem prune_effect (th : RT) (st next : RS) (p : P) (t : T)
    (step : (sys).tr th st (.prune p t) next) (q : P) :
    next.mesh q t = (if q = p then false else st.mesh q t) := by
  simp only [Routing.relationalTransitionSystem, Routing.Next, Routing.NextAct, nextSimp,
    Routing.State.ext_iff, funext_iff] at step
  grind

theorem prune_transaction (th : RT) (st next : RS) (peers : List P) (t : T)
    (run : Runs sys th st (peers.map fun p => .prune p t) next) (q : P) :
    next.mesh q t = true ↔ st.mesh q t = true ∧ q ∉ peers := by
  induction peers generalizing st with
  | nil =>
    have same := Runs.nil_iff.mp run
    subst next
    simp
  | cons p peers ih =>
    obtain ⟨middle, step, rest⟩ := Runs.cons_iff.mp run
    rw [ih middle rest, prune_effect P T W ID Snapshot th st middle p t step q]
    by_cases same : q = p <;> simp [same, and_assoc]

theorem prune_backoff_effect (th : RT) (st next : RS) (p : P) (t : T)
    (step : (sys).tr th st (.prune p t) next) (q : P) :
    next.backoff q t = (if q = p then true else st.backoff q t) := by
  simp only [Routing.relationalTransitionSystem, Routing.Next, Routing.NextAct, nextSimp,
    Routing.State.ext_iff, funext_iff] at step
  grind

theorem prune_backoff_transaction (th : RT) (st next : RS) (peers : List P) (t : T)
    (run : Runs sys th st (peers.map fun p => .prune p t) next) (q : P) :
    next.backoff q t = true ↔ st.backoff q t = true ∨ q ∈ peers := by
  induction peers generalizing st with
  | nil =>
    have same := Runs.nil_iff.mp run
    subst next
    simp
  | cons p peers ih =>
    obtain ⟨middle, step, rest⟩ := Runs.cons_iff.mp run
    rw [ih middle rest, prune_backoff_effect P T W ID Snapshot th st middle p t step q]
    by_cases same : q = p <;> simp [same, or_assoc]

theorem local_graft_effect (th : RT) (st next : RS) (p : P) (t : T)
    (step : (sys).tr th st (.localGraft p t) next) (q : P) :
    next.mesh q t = (if q = p then true else st.mesh q t) := by
  simp only [Routing.relationalTransitionSystem, Routing.Next, Routing.NextAct, nextSimp,
    Routing.State.ext_iff, funext_iff] at step
  grind

theorem local_graft_transaction (th : RT) (st next : RS) (peers : List P) (t : T)
    (run : Runs sys th st (peers.map fun p => .localGraft p t) next) (q : P) :
    next.mesh q t = true ↔ st.mesh q t = true ∨ q ∈ peers := by
  induction peers generalizing st with
  | nil =>
    have same := Runs.nil_iff.mp run
    subst next
    simp
  | cons p peers ih =>
    obtain ⟨middle, step, rest⟩ := Runs.cons_iff.mp run
    rw [ih middle rest, local_graft_effect P T W ID Snapshot th st middle p t step q]
    by_cases same : q = p <;> simp [same, or_assoc]

noncomputable def publishedEffect (th : RT) (published : ID → Bool) : RL → ID → Bool
  | .validatedLocal w | .publish _ _ w => fun k => if k = th.key w then true else published k
  | .expirePublication id => fun k => if k = id then false else published k
  | _ => published

theorem published_effect (th : RT) (st next : RS) (label : RL)
    (step : (sys).tr th st label next) :
    next.publishedId = publishedEffect P T W ID Snapshot th st.publishedId label := by
  funext k
  cases label <;>
    simp only [Routing.relationalTransitionSystem, Routing.Next, Routing.NextAct, nextSimp,
      Routing.State.ext_iff, funext_iff] at step <;>
    simp only [publishedEffect] <;> grind

theorem published_transaction (th : RT) (st next : RS) (labels : List RL)
    (run : Runs sys th st labels next) :
    next.publishedId = labels.foldl (publishedEffect P T W ID Snapshot th) st.publishedId := by
  induction run with
  | nil => rfl
  | cons step rest ih =>
    simpa only [List.foldl_cons, published_effect P T W ID Snapshot _ _ _ _ step] using ih

end Libp2p.NetworkRoutingFacts
