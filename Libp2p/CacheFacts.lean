module

public import Libp2p.CacheSafety
public import Libp2p.CompositionSupport

@[expose] public section
namespace Libp2p.Cache

open Classical
open scoped Libp2p.Cache

variable (P W ID T : Type)
variable [Inhabited P] [Inhabited W] [Inhabited ID] [Inhabited T]

local notation "CT" => Theory P W ID T
local notation "CS" => State (FieldAbstractType P W ID T)
local notation "CL" => Label P W ID T
local notation "sys" => relationalTransitionSystem P W ID T

def ValidationGate (authorized : W → Prop) : CL → Prop
  | .validate w => authorized w
  | _ => True

theorem acceptance_bound (th : CT) (st next : CS) (label : CL) (authorized : W → Prop)
    (step : (sys).tr th st label next) (gate : ValidationGate P W ID T authorized label)
    (bound : ∀ w, st.accepted w = true → authorized w) :
    ∀ w, next.accepted w = true → authorized w := by
  intro w accepted
  cases label <;>
    simp only [relationalTransitionSystem, Next, NextAct, nextSimp,
      State.ext_iff, funext_iff] at step <;>
    simp only [ValidationGate] at gate <;> grind

theorem transaction_acceptance_bound (th : CT) (st next : CS) (labels : List CL)
    (authorized : W → Prop) (run : Runs sys th st labels next)
    (gate : ∀ label ∈ labels, ValidationGate P W ID T authorized label)
    (bound : ∀ w, st.accepted w = true → authorized w) :
    ∀ w, next.accepted w = true → authorized w := by
  induction run with
  | nil => exact bound
  | @cons before middle after label labels step rest ih =>
    apply ih
    · intro action member
      exact gate action (List.mem_cons_of_mem label member)
    · exact acceptance_bound P W ID T th before middle label authorized step
        (gate label (List.mem_cons_self)) bound

noncomputable def seenEffect (th : CT) (seen : ID → Bool) : CL → ID → Bool
  | .store w => fun k => if k = th.key w then true else seen k
  | .expireSeen id => fun k => if k = id then false else seen k
  | _ => seen

theorem seen_effect (th : CT) (st next : CS) (label : CL)
    (step : (sys).tr th st label next) :
    next.seen = seenEffect P W ID T th st.seen label := by
  funext k
  cases label <;>
    simp only [relationalTransitionSystem, Next, NextAct, nextSimp,
      State.ext_iff, funext_iff] at step <;>
    simp only [seenEffect] <;> grind

theorem seen_transaction (th : CT) (st next : CS) (labels : List CL)
    (run : Runs sys th st labels next) :
    next.seen = labels.foldl (seenEffect P W ID T th) st.seen := by
  induction run with
  | nil => rfl
  | cons step rest ih =>
    simpa only [List.foldl_cons, seen_effect P W ID T _ _ _ _ step] using ih

end Libp2p.Cache
