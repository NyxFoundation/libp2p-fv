module

public import Libp2p.Temporal
public import Libp2p.Proof

public section

namespace Libp2p.TemporalBackoff

open Classical in
theorem backoffSafety (peer topic occurrence moment Control : Type)
    [Inhabited peer]
    [Inhabited topic]
    [Inhabited occurrence]
    [Inhabited moment]
    [Inhabited Control]
    [Control_EnumClass Control]
    (th : Theory peer topic occurrence moment Control)
    (st : State (FieldAbstractType peer topic occurrence moment Control))
    (reachable : (relationalTransitionSystem peer topic occurrence moment Control).reachable th st) :
    Invariants _ _ peer topic occurrence moment Control
      (FieldAbstractType peer topic occurrence moment Control) th st := by
  refine Veil.RelationalTransitionSystem.invariant_of_inductive
    (sys := relationalTransitionSystem peer topic occurrence moment Control) ?_ ?_ th st reachable
  · intro th st ha ht
    dsimp only [relationalTransitionSystem, Init] at ht
    rw [← initializer.ext.derived_eq] at ht
    discharge_vcs initializer using ha, True.intro, ht
  · intro th st label next ha hi ht
    cases label <;> dsimp only [relationalTransitionSystem, Next, NextAct] at ht
    case advance m => discharge_vcs advance using ha, hi, ht
    case receivePrune c endTime => discharge_vcs receivePrune using ha, hi, ht
    case receiveActiveGraft c endTime => discharge_vcs receiveActiveGraft using ha, hi, ht

open Classical in
theorem activeGraft_effect (peer topic occurrence moment Control : Type)
    [Inhabited peer] [Inhabited topic] [Inhabited occurrence] [Inhabited moment]
    [Inhabited Control] [Control_EnumClass Control]
    (th : Theory peer topic occurrence moment Control)
    (st next : State (FieldAbstractType peer topic occurrence moment Control))
    (c : occurrence) (endTime : moment)
    (step : (relationalTransitionSystem peer topic occurrence moment Control).tr
      th st (.receiveActiveGraft c endTime) next) :
    next.pruneEmitted = true ∧ next.cause = c ∧
      st.deadline (th.sender c) (th.channel c) < next.deadline (th.sender c) (th.channel c) := by
  dsimp only [relationalTransitionSystem, Next, NextAct] at step
  rw [receiveActiveGraft.ext.derived_eq] at step
  simp only [receiveActiveGraft.ext.tr] at step
  rcases step with ⟨_, _, _, _, extended, update⟩
  cases update
  simp_all [setIn, getFrom, readFrom, Veil.FieldRepresentation.setSingle,
    Veil.FieldRepresentation.get, Veil.CanonicalField.set,
    Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry, Veil.FieldUpdatePat.match,
    Veil.IteratedProd.patCmp]

#print axioms activeGraft_effect
#print axioms backoffSafety

end Libp2p.TemporalBackoff

namespace Libp2p.TemporalLimits

open Classical in
theorem limitsSafety (peer occurrence moment : Type)
    [Inhabited peer]
    [Inhabited occurrence]
    [Inhabited moment]
    (th : Theory peer occurrence moment)
    (st : State (FieldAbstractType peer occurrence moment))
    (reachable : (relationalTransitionSystem peer occurrence moment).reachable th st) :
    Invariants _ _ peer occurrence moment
      (FieldAbstractType peer occurrence moment) th st := by
  refine Veil.RelationalTransitionSystem.invariant_of_inductive
    (sys := relationalTransitionSystem peer occurrence moment) ?_ ?_ th st reachable
  · intro th st ha ht
    dsimp only [relationalTransitionSystem, Init] at ht
    rw [← initializer.ext.derived_eq] at ht
    discharge_vcs initializer using ha, True.intro, ht
  · intro th st label next ha hi ht
    cases label <;> dsimp only [relationalTransitionSystem, Next, NextAct] at ht
    case heartbeat m => discharge_vcs heartbeat using ha, hi, ht
    case receiveIDontWant c applyPenalty => discharge_vcs receiveIDontWant using ha, hi, ht

#print axioms limitsSafety

end Libp2p.TemporalLimits

namespace Libp2p.TemporalCredit

open Classical in
theorem creditSafety (peer topic task object context messageId moment : Type)
    [Inhabited peer]
    [Inhabited topic]
    [Inhabited task]
    [Inhabited object]
    [Inhabited context]
    [Inhabited messageId]
    [Inhabited moment]
    (th : Theory peer topic task object context messageId moment)
    (st : State (FieldAbstractType peer topic task object context messageId moment))
    (reachable : (relationalTransitionSystem peer topic task object context messageId moment).reachable th st) :
    Invariants _ _ peer topic task object context messageId moment
      (FieldAbstractType peer topic task object context messageId moment) th st := by
  refine Veil.RelationalTransitionSystem.invariant_of_inductive
    (sys := relationalTransitionSystem peer topic task object context messageId moment) ?_ ?_ th st reachable
  · intro th st ha ht
    dsimp only [relationalTransitionSystem, Init] at ht
    rw [← initializer.ext.derived_eq] at ht
    discharge_vcs initializer using ha, True.intro, ht
  · intro th st label next ha hi ht
    cases label <;> dsimp only [relationalTransitionSystem, Next, NextAct] at ht
    case advance m => discharge_vcs advance using ha, hi, ht
    case setMesh p t joined => discharge_vcs setMesh using ha, hi, ht
    case arrive j => discharge_vcs arrive using ha, hi, ht
    case finishValidation j valid => discharge_vcs finishValidation using ha, hi, ht
    case credit j countEndpoint => discharge_vcs credit using ha, hi, ht

open Classical in
theorem credit_effect (peer topic task object context messageId moment : Type)
    [Inhabited peer] [Inhabited topic] [Inhabited task] [Inhabited object]
    [Inhabited context] [Inhabited messageId] [Inhabited moment]
    (th : Theory peer topic task object context messageId moment)
    (st next : State (FieldAbstractType peer topic task object context messageId moment))
    (j : task) (countEndpoint : Bool)
    (step : (relationalTransitionSystem peer topic task object context messageId moment).tr
      th st (.credit j countEndpoint) next) :
    next.creditEmitted = true ∧ next.cause = j ∧
      next.creditEvents (th.sender j) (th.channel (th.scope j)) =
        st.creditEvents (th.sender j) (th.channel (th.scope j)) + 1 := by
  dsimp only [relationalTransitionSystem, Next, NextAct] at step
  rw [credit.ext.derived_eq] at step
  simp only [credit.ext.tr] at step
  rcases step with ⟨_, _, _, _, _, _, _, update⟩
  cases update
  simp [setIn, getFrom, readFrom, Veil.FieldRepresentation.setSingle,
    Veil.FieldRepresentation.get, Veil.CanonicalField.set,
    Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry, Veil.FieldUpdatePat.match,
    Veil.IteratedProd.patCmp]

#print axioms creditSafety

end Libp2p.TemporalCredit

namespace Libp2p.TemporalRetention

open Classical in
theorem retentionSafety (peer session history moment : Type)
    [Inhabited peer]
    [Inhabited session]
    [Inhabited history]
    [Inhabited moment]
    (th : Theory peer session history moment)
    (st : State (FieldAbstractType peer session history moment))
    (reachable : (relationalTransitionSystem peer session history moment).reachable th st) :
    Invariants _ _ peer session history moment
      (FieldAbstractType peer session history moment) th st := by
  refine Veil.RelationalTransitionSystem.invariant_of_inductive
    (sys := relationalTransitionSystem peer session history moment) ?_ ?_ th st reachable
  · intro th st ha ht
    dsimp only [relationalTransitionSystem, Init] at ht
    rw [← initializer.ext.derived_eq] at ht
    discharge_vcs initializer using ha, True.intro, ht
  · intro th st label next ha hi ht
    cases label <;> dsimp only [relationalTransitionSystem, Next, NextAct] at ht
    case advance m => discharge_vcs advance using ha, hi, ht
    case connect s keepAfterLifetime => discharge_vcs connect using ha, hi, ht
    case updateLiveHistory s h => discharge_vcs updateLiveHistory using ha, hi, ht
    case authenticate s => discharge_vcs authenticate using ha, hi, ht
    case authorizeCallbacks s => discharge_vcs authorizeCallbacks using ha, hi, ht
    case disconnect s => discharge_vcs disconnect using ha, hi, ht
    case decayRetained p => discharge_vcs decayRetained using ha, hi, ht

open Classical in
theorem reconnect_within_lifetime_effect (peer session history moment : Type)
    [Inhabited peer] [Inhabited session] [Inhabited history] [Inhabited moment]
    (th : Theory peer session history moment)
    (st next : State (FieldAbstractType peer session history moment))
    (s : session) (keepAfterLifetime : Bool)
    (held : st.retained (th.peerOf s) = true)
    (within : st.now < st.expires (th.peerOf s))
    (step : (relationalTransitionSystem peer session history moment).tr
      th st (.connect s keepAfterLifetime) next) :
    next.connectEmitted = true ∧ next.restored = true ∧
      next.currentHistory s = st.retainedHistory (th.peerOf s) ∧
      next.authenticated s = false ∧ next.callbackAuthority s = false := by
  dsimp only [relationalTransitionSystem, Next, NextAct] at step
  rw [connect.ext.derived_eq] at step
  simp only [connect.ext.tr, getFrom, readFrom, Veil.FieldRepresentation.get] at step
  rcases step with ⟨_, _, update⟩
  rw [ite_eq_left ⟨held, Or.inl within⟩] at update
  cases update
  simp [setIn, Veil.FieldRepresentation.setSingle, Veil.CanonicalField.set,
    Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry, Veil.FieldUpdatePat.match,
    Veil.IteratedProd.patCmp]

#print axioms retentionSafety

end Libp2p.TemporalRetention

namespace Libp2p.TemporalCausality

open Classical in
theorem causalitySafety (peer topic task object context messageId subscription : Type)
    [Inhabited peer]
    [Inhabited topic]
    [Inhabited task]
    [Inhabited object]
    [Inhabited context]
    [Inhabited messageId]
    [Inhabited subscription]
    (th : Theory peer topic task object context messageId subscription)
    (st : State (FieldAbstractType peer topic task object context messageId subscription))
    (reachable : (relationalTransitionSystem peer topic task object context messageId subscription).reachable th st) :
    Invariants _ _ peer topic task object context messageId subscription
      (FieldAbstractType peer topic task object context messageId subscription) th st := by
  refine Veil.RelationalTransitionSystem.invariant_of_inductive
    (sys := relationalTransitionSystem peer topic task object context messageId subscription) ?_ ?_ th st reachable
  · intro th st ha ht
    dsimp only [relationalTransitionSystem, Init] at ht
    rw [← initializer.ext.derived_eq] at ht
    discharge_vcs initializer using ha, True.intro, ht
  · intro th st label next ha hi ht
    cases label <;> dsimp only [relationalTransitionSystem, Next, NextAct] at ht
    case changeSubscription e => discharge_vcs changeSubscription using ha, hi, ht
    case remoteProcesses p e => discharge_vcs remoteProcesses using ha, hi, ht
    case send j => discharge_vcs send using ha, hi, ht
    case receive j => discharge_vcs receive using ha, hi, ht
    case considerViolation j applyPenalty => discharge_vcs considerViolation using ha, hi, ht

#print axioms causalitySafety

end Libp2p.TemporalCausality
