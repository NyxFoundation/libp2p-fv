module

public import Libp2p.Cache
public import Libp2p.Proof

public section

namespace Libp2p.Cache

open Classical in
theorem cacheSafety (peer message messageId topic : Type)
    [Inhabited peer] [Inhabited message] [Inhabited messageId] [Inhabited topic]
    (th : Theory peer message messageId topic)
    (st : State (FieldAbstractType peer message messageId topic))
    (reachable : (relationalTransitionSystem peer message messageId topic).reachable th st) :
    Invariants _ _ peer message messageId topic (FieldAbstractType peer message messageId topic)
      th st := by
  refine Veil.RelationalTransitionSystem.invariant_of_inductive
    (sys := relationalTransitionSystem peer message messageId topic) ?_ ?_ th st reachable
  · intro th st ha ht
    dsimp only [relationalTransitionSystem, Init] at ht
    rw [← initializer.ext.derived_eq] at ht
    discharge_vcs initializer using ha, True.intro, ht
  · intro th st label next ha hi ht
    cases label <;> dsimp only [relationalTransitionSystem, Next, NextAct] at ht
    case validate m => discharge_vcs validate using ha, hi, ht
    case store m => discharge_vcs store using ha, hi, ht
    case ihave p k track => discharge_vcs ihave using ha, hi, ht
    case received p k => discharge_vcs received using ha, hi, ht
    case iwant p k => discharge_vcs iwant using ha, hi, ht
    case gossip k t => discharge_vcs gossip using ha, hi, ht
    case assessPromise p k => discharge_vcs assessPromise using ha, hi, ht
    case tickHistory => discharge_vcs tickHistory using ha, hi, ht
    case tickPromises => discharge_vcs tickPromises using ha, hi, ht
    case evict k => discharge_vcs evict using ha, hi, ht
    case expireSeen k => discharge_vcs expireSeen using ha, hi, ht
    case newTrackingInterval k => discharge_vcs newTrackingInterval using ha, hi, ht

#print axioms cacheSafety

end Libp2p.Cache
