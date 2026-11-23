module

public import Libp2p.TemporalCausality

@[expose] public section
namespace Libp2p.TemporalKnowledge

open Libp2p.TemporalCausality

/-!
Specification-only permission for the v1.3 MUST NOT in libp2p/specs
c750236de43cd8b246a824b377dfdb26bae686db, gossipsub-v1.3.md,
"Peer Scoring on Protocol Violations".

Admissible histories are finite executions of the actual Veil causal system,
including earlier assessments. Observations retain local subscription changes
and received occurrences. The fixed theory binds those receiver-known tokens
to actual peers, objects, contexts, IDs, topics, and subscription values.
Remote processing, send order, the synthetic global serial, and earlier penalty
outputs are NOT evidence in this projection. The latest change is receiver-wide.

The permission relation universally rules out observation-compatible old-send
histories before a requested penalty. It is neither a receiver detector nor an
exact characterization of all extension-specific observations. It does not
assert that an independently checkable violation occurred, nor make a SHOULD
penalty mandatory.
-/

-- Receiver-visible event record, independent of theory instances.
inductive Observation (task subscription : Type) where
  | subscriptionChanged (change : subscription)
  | received (message : task)
  deriving DecidableEq, Repr

variable {peer topic task object context messageId subscription : Type}
variable [DecidableEq peer] [DecidableEq topic] [DecidableEq task] [DecidableEq object]
variable [DecidableEq context] [DecidableEq messageId] [DecidableEq subscription]
variable [Inhabited peer] [Inhabited topic] [Inhabited task] [Inhabited object]
variable [Inhabited context] [Inhabited messageId] [Inhabited subscription]

local notation "CState" => State (FieldAbstractType peer topic task object context messageId subscription)
local notation "CEvent" => Label peer topic task object context messageId subscription
local notation "CTheory" => Theory peer topic task object context messageId subscription
noncomputable abbrev Sys : Veil.RelationalTransitionSystem CTheory CState CEvent :=
  relationalTransitionSystem peer topic task object context messageId subscription

def eventObservation : CEvent → Option (Observation task subscription)
  | .changeSubscription e => some (.subscriptionChanged e)
  | .receive j => some (.received j)
  | .remoteProcesses _ _ | .send _ | .considerViolation _ _ => none

def observe (events : List CEvent) : List (Observation task subscription) :=
  events.filterMap eventObservation

/-- Every edge is the existing Veil relational semantics, not a second model. -/
inductive Runs (th : CTheory) : CState → List CEvent → CState → Prop where
  | nil (st : CState) : Runs th st [] st
  | cons {st middle last : CState} {event : CEvent} {rest : List CEvent} :
      Sys.tr th st event middle → Runs th middle rest last → Runs th st (event :: rest) last

structure History (th : CTheory) where
  initial : CState
  last : CState
  events : List CEvent
  initialized : Sys.init th initial
  execution : Runs th initial events last

theorem Runs.reachable {th : CTheory} {st last : CState} {events : List CEvent}
    (run : Runs th st events last) : Sys.reachable th st → Sys.reachable th last := by
  induction run with
  | nil => exact id
  | @cons st middle last event rest step _ ih =>
    intro reachable
    exact ih (Veil.RelationalTransitionSystem.reachable.step st middle reachable ⟨event, step⟩)

theorem History.reachable {th : CTheory} (h : History th) : Sys.reachable th h.last := by
  have initial : Sys.reachable th h.initial :=
    Veil.RelationalTransitionSystem.reachable.init h.initial (by trivial) h.initialized
  exact h.execution.reachable initial

theorem Runs.snoc {th : CTheory} {st next : CState} {event : CEvent} {last : CState}
    {events : List CEvent} (run : Runs th st events last)
    (step : Sys.tr th last event next) : Runs th st (events ++ [event]) next := by
  revert step
  induction run with
  | nil st => intro tail; exact .cons tail (.nil next)
  | @cons st middle last seen rest first _ ih =>
    intro tail
    exact .cons first (ih tail)

def History.extend {th : CTheory} (h : History th) (event : CEvent) (next : CState)
    (step : Sys.tr th h.last event next) : History th :=
  { h with last := next, events := h.events ++ [event], execution := h.execution.snoc step }

/-- Every real finite execution, including previous assessments, has an admitted history. -/
theorem every_reachable_has_history {th : CTheory} {st : CState}
    (reachable : Sys.reachable th st) : ∃ h : History th, h.last = st := by
  induction reachable with
  | init st _ initialized => exact ⟨⟨st, st, [], initialized, .nil st⟩, rfl⟩
  | step st next _ transition ih =>
    obtain ⟨h, rfl⟩ := ih
    obtain ⟨event, step⟩ := transition
    exact ⟨h.extend event next step, rfl⟩

theorem assessment_adds_no_observation {th : CTheory} (h : History th)
    (j : task) (requested : Bool) (next : CState)
    (step : Sys.tr th h.last (.considerViolation j requested) next) :
    observe (h.extend (.considerViolation j requested) next step).events = observe h.events := by
  simp [History.extend, observe, eventObservation, List.filterMap_append]

/-- An old send relative to the receiver's latest change, regardless of message topic. -/
def ActualOld (th : CTheory) (st : CState) (j : task) : Prop :=
  st.receiverHasChange = true ∧
    ¬ (st.processed (th.sender j) st.receiverLatest = true ∧
      st.processedAt (th.sender j) st.receiverLatest < st.sentAt j)

def PossiblyOld (th : CTheory) (observations : List (Observation task subscription))
    (j : task) : Prop :=
  ∃ alternative : History th, observe alternative.events = observations ∧
    alternative.last.received j = true ∧ ActualOld th alternative.last j

def Permission {th : CTheory} (h : History th) (j : task) : Prop :=
  ¬ PossiblyOld th (observe h.events) j

/-- A restriction of the real decision edge, with no executable knowledge oracle. -/
def KnowledgeStep {th : CTheory} (h : History th) (j : task)
    (requested : Bool) (next : CState) : Prop :=
  Sys.tr th h.last (.considerViolation j requested) next ∧
    (requested = true → Permission h j)

theorem KnowledgeStep.refines {th : CTheory} {h : History th} {j : task}
    {requested : Bool} {next : CState} (step : KnowledgeStep h j requested next) :
    Sys.tr th h.last (.considerViolation j requested) next := step.1

theorem permission_same_observations {th : CTheory} (a b : History th) (j : task)
    (same : observe a.events = observe b.events) : Permission a j ↔ Permission b j := by
  simp only [Permission, same]

theorem permission_implies_actual_order {th : CTheory} {h : History th} {j : task}
    (permitted : Permission h j) (received : h.last.received j = true)
    (changed : h.last.receiverHasChange = true) :
    h.last.processed (th.sender j) h.last.receiverLatest = true ∧
      h.last.processedAt (th.sender j) h.last.receiverLatest < h.last.sentAt j := by
  by_contra old
  exact permitted ⟨h, rfl, received, changed, old⟩

open Classical in
theorem emitted_requires_requested {th : CTheory} {st next : CState} {j : task}
    {requested : Bool} (step : Sys.tr th st (.considerViolation j requested) next)
    (emitted : next.penaltyEmitted = true) : requested = true := by
  dsimp only [Sys, relationalTransitionSystem, Next, NextAct] at step
  rw [considerViolation.ext.derived_eq] at step
  simp only [considerViolation.ext.tr] at step
  rcases step with ⟨_, _, update⟩
  split at update
  · cases update
    rename_i condition
    exact condition.1
  · cases update
    simp [setIn, getFrom, readFrom, Veil.FieldRepresentation.setSingle,
      Veil.FieldRepresentation.get, Veil.CanonicalField.set,
      Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry, Veil.FieldUpdatePat.match,
      Veil.IteratedProd.patCmp] at emitted

/-- The normative exclusion ranges over other admissible histories, not just this run. -/
theorem no_penalty_for_compatible_old {th : CTheory} {h : History th} {j : task}
    {requested : Bool} {next : CState} (step : KnowledgeStep h j requested next)
    (alternative : History th) (same : observe alternative.events = observe h.events)
    (received : alternative.last.received j = true)
    (old : ActualOld th alternative.last j) : next.penaltyEmitted = false := by
  apply Bool.eq_false_iff.mpr
  intro emitted
  exact step.2 (emitted_requires_requested step.1 emitted) ⟨alternative, same, received, old⟩

/-- Declining an optional penalty needs no absence-of-alternatives premise. -/
theorem unrequested_step_allowed {th : CTheory} {h : History th} {j : task} {next : CState}
    (step : Sys.tr th h.last (.considerViolation j false) next) :
    KnowledgeStep h j false next := by
  exact ⟨step, by simp⟩

def Observation.isChange : Observation task subscription → Bool
  | .subscriptionChanged _ => true
  | .received _ => false

def eventIsChange : CEvent → Bool
  | .changeSubscription _ => true
  | _ => false

theorem change_flag_step {th : CTheory} {st next : CState} {event : CEvent}
    (step : Sys.tr th st event next) :
    next.receiverHasChange = (st.receiverHasChange || eventIsChange event) := by
  cases event with
  | changeSubscription e =>
    dsimp only [Sys, relationalTransitionSystem, Next, NextAct] at step
    rw [changeSubscription.ext.derived_eq] at step
    simp only [changeSubscription.ext.tr] at step
    rcases step with ⟨_, update⟩
    cases update
    simp [eventIsChange, setIn, getFrom, readFrom, Veil.FieldRepresentation.setSingle,
      Veil.FieldRepresentation.get, Veil.CanonicalField.set,
      Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry, Veil.FieldUpdatePat.match,
      Veil.IteratedProd.patCmp]
  | remoteProcesses p e =>
    dsimp only [Sys, relationalTransitionSystem, Next, NextAct] at step
    rw [remoteProcesses.ext.derived_eq] at step
    simp only [remoteProcesses.ext.tr] at step
    rcases step with ⟨_, _, update⟩
    cases update
    simp [eventIsChange, Bool.or_false, setIn, getFrom, readFrom,
      Veil.FieldRepresentation.setSingle, Veil.FieldRepresentation.get,
      Veil.CanonicalField.set, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
      Veil.FieldUpdatePat.match, Veil.IteratedProd.patCmp]
  | send j =>
    dsimp only [Sys, relationalTransitionSystem, Next, NextAct] at step
    rw [send.ext.derived_eq] at step
    simp only [send.ext.tr] at step
    rcases step with ⟨_, update⟩
    cases update
    simp [eventIsChange, Bool.or_false, setIn, getFrom, readFrom,
      Veil.FieldRepresentation.setSingle, Veil.FieldRepresentation.get,
      Veil.CanonicalField.set, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
      Veil.FieldUpdatePat.match, Veil.IteratedProd.patCmp]
  | receive j =>
    dsimp only [Sys, relationalTransitionSystem, Next, NextAct] at step
    rw [receive.ext.derived_eq] at step
    simp only [receive.ext.tr] at step
    rcases step with ⟨_, _, update⟩
    cases update
    simp [eventIsChange, Bool.or_false, setIn, getFrom, readFrom,
      Veil.FieldRepresentation.setSingle, Veil.FieldRepresentation.get,
      Veil.CanonicalField.set, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
      Veil.FieldUpdatePat.match, Veil.IteratedProd.patCmp]
  | considerViolation j requested =>
    dsimp only [Sys, relationalTransitionSystem, Next, NextAct] at step
    rw [considerViolation.ext.derived_eq] at step
    simp only [considerViolation.ext.tr] at step
    rcases step with ⟨_, _, update⟩
    split at update <;> cases update <;>
      simp [eventIsChange, Bool.or_false, setIn, getFrom, readFrom,
        Veil.FieldRepresentation.setSingle, Veil.FieldRepresentation.get,
        Veil.CanonicalField.set, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
        Veil.FieldUpdatePat.match, Veil.IteratedProd.patCmp]

theorem initial_has_no_change {th : CTheory} {st : CState}
    (initialized : Sys.init th st) : st.receiverHasChange = false := by
  dsimp only [Sys, relationalTransitionSystem, Init, initializer.ext.tr] at initialized
  cases initialized
  rfl

theorem Runs.change_flag {th : CTheory} {st last : CState} {events : List CEvent}
    (run : Runs th st events last) :
    last.receiverHasChange = (st.receiverHasChange || (observe events).any Observation.isChange) := by
  induction run with
  | nil => simp [observe, eventObservation, List.filterMap_nil, List.any_nil]
  | @cons st middle last event rest step _ ih =>
    cases event <;>
      simp [change_flag_step step, ih, observe, eventObservation, eventIsChange,
        Observation.isChange, Bool.or_assoc, Bool.or_true, Bool.or_false]

theorem History.change_flag {th : CTheory} (h : History th) :
    h.last.receiverHasChange = (observe h.events).any Observation.isChange := by
  rw [h.execution.change_flag, initial_has_no_change h.initialized]
  rfl

local macro "kb" : tactic =>
  `(tactic| simp [setIn, getFrom, readFrom, Veil.FieldRepresentation.setSingle,
      Veil.FieldRepresentation.get, Veil.CanonicalField.set, Veil.IteratedArrow.curry,
      Veil.IteratedArrow.uncurry, Veil.FieldUpdatePat.match, Veil.IteratedProd.patCmp])

/-- Mapping of one original causal event to its replacement block, dropping
receiver-invisible events and inserting the replacement send before the
corresponding receive. -/
def eventBlock : CEvent -> List CEvent
  | .changeSubscription e => [.changeSubscription e]
  | .receive j => [.send j, .receive j]
  | .remoteProcesses _ _ | .send _ | .considerViolation _ _ => []

theorem observation_oldify (events : List CEvent) :
    observe (events.flatMap eventBlock) = observe events := by
  induction events with
  | nil => rfl
  | cons event rest ih =>
    rw [observe] at ih
    cases event with
    | changeSubscription e =>
      simp only [observe, eventBlock, List.flatMap_cons, List.cons_append,
        List.filterMap_cons, eventObservation]
      exact congrArg (List.cons (Observation.subscriptionChanged e)) ih
    | receive j =>
      simp only [observe, eventBlock, List.flatMap_cons, List.cons_append,
        List.filterMap_cons, eventObservation]
      exact congrArg (List.cons (Observation.received j)) ih
    | remoteProcesses p e =>
      simp only [observe, eventBlock, List.flatMap_cons, List.cons_append, List.nil_append,
        List.filterMap_cons, eventObservation]
      exact ih
    | send j =>
      simp only [observe, eventBlock, List.flatMap_cons, List.cons_append, List.nil_append,
        List.filterMap_cons, eventObservation]
      exact ih
    | considerViolation j requested =>
      simp only [observe, eventBlock, List.flatMap_cons, List.cons_append, List.nil_append,
        List.filterMap_cons, eventObservation]
      exact ih

/-- Real change edge, with the field facts the reconstruction needs. -/
theorem change_step (th : CTheory) (st : CState) (e : subscription)
    (fresh : st.changed e = false) :
    ∃ s1, Sys.tr th st (.changeSubscription e) s1 ∧
      s1.receiverHasChange = true ∧ s1.receiverLatest = e ∧
      (∀ e', s1.changed e' = (st.changed e' || decide (e = e'))) ∧
      (∀ j, s1.received j = st.received j) ∧
      (∀ j, s1.sent j = st.sent j) ∧
      (∀ p ctx, s1.processed p ctx = st.processed p ctx) ∧
      s1.serial = st.serial + 1 := by
  dsimp only [Sys, relationalTransitionSystem, Next, NextAct]
  rw [changeSubscription.ext.derived_eq]
  simp only [changeSubscription.ext.tr]
  refine ⟨?w, ?body⟩
  case body =>
    refine ⟨?edge, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · refine ⟨by simpa [getFrom, Veil.FieldRepresentation.get] using fresh, ?_⟩
      rfl
    · rfl
    · rfl
    · intro e'
      by_cases h : e = e' <;>
        simp [h, setIn, getFrom, readFrom, Veil.FieldRepresentation.setSingle,
          Veil.FieldRepresentation.get, Veil.CanonicalField.set, Veil.IteratedArrow.curry,
          Veil.IteratedArrow.uncurry, Veil.FieldUpdatePat.match, Veil.IteratedProd.patCmp]
    · intro j; rfl
    · intro j; rfl
    · intro p ctx; rfl
    · rfl
theorem change_edge_recv {th : CTheory} {st mid : CState} {e : subscription}
    (step : Sys.tr th st (.changeSubscription e) mid) :
    (∀ j, mid.received j = st.received j) ∧
      (∀ e', mid.changed e' = (st.changed e' || decide (e = e'))) ∧
      mid.receiverHasChange = true := by
  dsimp only [Sys, relationalTransitionSystem, Next, NextAct] at step
  rw [changeSubscription.ext.derived_eq] at step
  simp only [changeSubscription.ext.tr] at step
  obtain ⟨_, hEq⟩ := step
  refine ⟨?_, ?_, ?_⟩
  · intro j
    rw [← hEq]
    rfl
  · intro e'
    rw [← hEq]
    by_cases h : e = e' <;>
      simp [h, setIn, getFrom, readFrom, Veil.FieldRepresentation.setSingle,
        Veil.FieldRepresentation.get, Veil.CanonicalField.set, Veil.IteratedArrow.curry,
        Veil.IteratedArrow.uncurry, Veil.FieldUpdatePat.match, Veil.IteratedProd.patCmp]
  · rw [← hEq]
    rfl

/-- Real send edge, with the field facts the reconstruction needs. -/
theorem send_step (th : CTheory) (st : CState) (j : task)
    (fresh : st.sent j = false) :
    ∃ s1, Sys.tr th st (.send j) s1 ∧
      (∀ j', s1.received j' = st.received j') ∧
      (∀ e', s1.changed e' = st.changed e') ∧
      s1.receiverHasChange = st.receiverHasChange ∧
      s1.receiverLatest = st.receiverLatest ∧
      s1.sent j = true ∧
      (∀ j', s1.sent j' = (st.sent j' || decide (j = j'))) ∧
      s1.sentAt j = st.serial + 1 ∧
      s1.serial = st.serial + 1 ∧
      (∀ p ctx, s1.processed p ctx = st.processed p ctx) ∧
      (∀ p ctx, s1.processedAt p ctx = st.processedAt p ctx) := by
  dsimp only [Sys, relationalTransitionSystem, Next, NextAct]
  rw [send.ext.derived_eq]
  simp only [send.ext.tr]
  refine ⟨?w, ?body⟩
  case body =>
    refine ⟨?edge, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · refine ⟨by simpa [getFrom, Veil.FieldRepresentation.get] using fresh, ?_⟩
      rfl
    · intro j'; rfl
    · intro e'; rfl
    · rfl
    · rfl
    · simp [setIn, getFrom, readFrom, Veil.FieldRepresentation.setSingle,
          Veil.FieldRepresentation.get, Veil.CanonicalField.set, Veil.IteratedArrow.curry,
          Veil.IteratedArrow.uncurry, Veil.FieldUpdatePat.match, Veil.IteratedProd.patCmp]
    · intro j'
      by_cases h : j = j'
      · simp [h, setIn, getFrom, readFrom, Veil.FieldRepresentation.setSingle,
          Veil.FieldRepresentation.get, Veil.CanonicalField.set, Veil.IteratedArrow.curry,
          Veil.IteratedArrow.uncurry, Veil.FieldUpdatePat.match, Veil.IteratedProd.patCmp]
      · simp [(decide_eq_false_iff_not).mpr h, setIn, getFrom, readFrom, Veil.FieldRepresentation.setSingle,
        Veil.FieldRepresentation.get, Veil.CanonicalField.set, Veil.IteratedArrow.curry,
        Veil.IteratedArrow.uncurry, Veil.FieldUpdatePat.match, Veil.IteratedProd.patCmp]
    · simp [setIn, getFrom, readFrom, Veil.FieldRepresentation.setSingle,
          Veil.FieldRepresentation.get, Veil.CanonicalField.set, Veil.IteratedArrow.curry,
          Veil.IteratedArrow.uncurry, Veil.FieldUpdatePat.match, Veil.IteratedProd.patCmp]
    · rfl
    · intro p ctx; rfl
    · intro p ctx; rfl

theorem send_edge_recv {th : CTheory} {st mid : CState} {j : task}
    (step : Sys.tr th st (.send j) mid) : ∀ j', mid.received j' = st.received j' := by
  dsimp only [Sys, relationalTransitionSystem, Next, NextAct] at step
  rw [send.ext.derived_eq] at step
  simp only [send.ext.tr] at step
  obtain ⟨_, hEq⟩ := step
  intro j'
  rw [← hEq]
  rfl

theorem send_edge_copies {th : CTheory} {st mid : CState} {j : task}
    (step : Sys.tr th st (.send j) mid) :
    (∀ e', mid.changed e' = st.changed e') ∧ (∀ j', mid.received j' = st.received j') ∧
      mid.receiverHasChange = st.receiverHasChange ∧ mid.receiverLatest = st.receiverLatest := by
  dsimp only [Sys, relationalTransitionSystem, Next, NextAct] at step
  rw [send.ext.derived_eq] at step
  simp only [send.ext.tr] at step
  obtain ⟨_, hEq⟩ := step
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro e'
    rw [← hEq]
    rfl
  · intro j'
    rw [← hEq]
    rfl
  · rw [← hEq]
    rfl
  · rw [← hEq]
    rfl

/-- Real remote-processing edge, with the field facts the witness needs. -/
theorem process_step (th : CTheory) (st : CState) (p : peer) (e : subscription)
    (fresh : st.processed p e = false) (changed : st.changed e = true) :
    ∃ s1, Sys.tr th st (.remoteProcesses p e) s1 ∧
      s1.processed p e = true ∧
      (∀ j', s1.received j' = st.received j') ∧
      (∀ e', s1.changed e' = st.changed e') ∧
      s1.receiverHasChange = st.receiverHasChange ∧
      s1.receiverLatest = st.receiverLatest ∧
      (∀ j', s1.sent j' = st.sent j') ∧
      (∀ j', s1.sentAt j' = st.sentAt j') ∧
      s1.processedAt p e = st.serial + 1 ∧
      s1.serial = st.serial + 1 := by
  dsimp only [Sys, relationalTransitionSystem, Next, NextAct]
  rw [remoteProcesses.ext.derived_eq]
  simp only [remoteProcesses.ext.tr]
  refine ⟨?w, ?body⟩
  case body =>
    refine ⟨?edge, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · refine ⟨by simpa [getFrom, Veil.FieldRepresentation.get] using changed,
        by simpa [getFrom, Veil.FieldRepresentation.get] using fresh, ?_⟩
      rfl
    · simp [setIn, getFrom, readFrom, Veil.FieldRepresentation.setSingle,
          Veil.FieldRepresentation.get, Veil.CanonicalField.set, Veil.IteratedArrow.curry,
          Veil.IteratedArrow.uncurry, Veil.FieldUpdatePat.match, Veil.IteratedProd.patCmp]
    · intro j'; rfl
    · intro e'; rfl
    · rfl
    · rfl
    · intro j'; rfl
    · intro j'; rfl
    · simp [setIn, getFrom, readFrom, Veil.FieldRepresentation.setSingle,
          Veil.FieldRepresentation.get, Veil.CanonicalField.set, Veil.IteratedArrow.curry,
          Veil.IteratedArrow.uncurry, Veil.FieldUpdatePat.match, Veil.IteratedProd.patCmp]
    · rfl
theorem process_edge_recv {th : CTheory} {st mid : CState} {p : peer} {e : subscription}
    (step : Sys.tr th st (.remoteProcesses p e) mid) : ∀ j', mid.received j' = st.received j' := by
  dsimp only [Sys, relationalTransitionSystem, Next, NextAct] at step
  rw [remoteProcesses.ext.derived_eq] at step
  simp only [remoteProcesses.ext.tr] at step
  obtain ⟨_, _, hEq⟩ := step
  intro j'
  rw [← hEq]
  rfl

theorem process_edge_copies {th : CTheory} {st mid : CState} {p : peer} {e : subscription}
    (step : Sys.tr th st (.remoteProcesses p e) mid) :
    (∀ e', mid.changed e' = st.changed e') ∧ (∀ j', mid.received j' = st.received j') ∧
      mid.receiverHasChange = st.receiverHasChange ∧ mid.receiverLatest = st.receiverLatest := by
  dsimp only [Sys, relationalTransitionSystem, Next, NextAct] at step
  rw [remoteProcesses.ext.derived_eq] at step
  simp only [remoteProcesses.ext.tr] at step
  obtain ⟨_, _, hEq⟩ := step
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro e'
    rw [← hEq]
    rfl
  · intro j'
    rw [← hEq]
    rfl
  · rw [← hEq]
    rfl
  · rw [← hEq]
    rfl

/-- Real receive edge, with the field facts the reconstruction needs. -/
theorem receive_step (th : CTheory) (st : CState) (j : task)
    (sent : st.sent j = true) (fresh : st.received j = false) :
    ∃ s1, Sys.tr th st (.receive j) s1 ∧
      s1.received j = true ∧
      (∀ j', s1.received j' = (st.received j' || decide (j = j'))) ∧
      (∀ e', s1.changed e' = st.changed e') ∧
      s1.receiverHasChange = st.receiverHasChange ∧
      s1.receiverLatest = st.receiverLatest ∧
      (∀ j', s1.sent j' = st.sent j') ∧
      (∀ j', s1.sentAt j' = st.sentAt j') ∧
      (∀ p ctx, s1.processed p ctx = st.processed p ctx) ∧
      (∀ p ctx, s1.processedAt p ctx = st.processedAt p ctx) := by
  dsimp only [Sys, relationalTransitionSystem, Next, NextAct]
  rw [receive.ext.derived_eq]
  simp only [receive.ext.tr]
  refine ⟨?w, ?body⟩
  case body =>
    refine ⟨?edge, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · refine ⟨by simpa [getFrom, Veil.FieldRepresentation.get] using sent,
        by simpa [getFrom, Veil.FieldRepresentation.get] using fresh, ?_⟩
      rfl
    · simp [setIn, getFrom, readFrom, Veil.FieldRepresentation.setSingle,
          Veil.FieldRepresentation.get, Veil.CanonicalField.set, Veil.IteratedArrow.curry,
          Veil.IteratedArrow.uncurry, Veil.FieldUpdatePat.match, Veil.IteratedProd.patCmp]
    · intro j'
      by_cases h : j = j' <;>
        simp [h, setIn, getFrom, readFrom, Veil.FieldRepresentation.setSingle,
          Veil.FieldRepresentation.get, Veil.CanonicalField.set, Veil.IteratedArrow.curry,
          Veil.IteratedArrow.uncurry, Veil.FieldUpdatePat.match, Veil.IteratedProd.patCmp]
    · intro e'; rfl
    · rfl
    · rfl
    · intro j'; rfl
    · intro j'; rfl
    · intro p ctx; rfl
    · intro p ctx; rfl
theorem receive_edge_recv {th : CTheory} {st mid : CState} {j : task}
    (step : Sys.tr th st (.receive j) mid) :
    (∀ j', mid.received j' = (st.received j' || decide (j = j'))) ∧
      (∀ e', mid.changed e' = st.changed e') ∧
      mid.receiverHasChange = st.receiverHasChange ∧ mid.receiverLatest = st.receiverLatest ∧
      (∀ p ctx, mid.processed p ctx = st.processed p ctx) ∧
      (∀ p ctx, mid.processedAt p ctx = st.processedAt p ctx) := by
  dsimp only [Sys, relationalTransitionSystem, Next, NextAct] at step
  rw [receive.ext.derived_eq] at step
  simp only [receive.ext.tr] at step
  obtain ⟨_, _, hEq⟩ := step
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j'
    rw [← hEq]
    by_cases h : j = j'
    · subst h
      simp [Bool.or_true, setIn, getFrom, readFrom, Veil.FieldRepresentation.setSingle,
        Veil.FieldRepresentation.get, Veil.CanonicalField.set, Veil.IteratedArrow.curry,
        Veil.IteratedArrow.uncurry, Veil.FieldUpdatePat.match, Veil.IteratedProd.patCmp]
    · simp [(decide_eq_false_iff_not).mpr h, setIn, getFrom, readFrom,
        Veil.FieldRepresentation.setSingle, Veil.FieldRepresentation.get,
        Veil.CanonicalField.set, Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry,
        Veil.FieldUpdatePat.match, Veil.IteratedProd.patCmp]
  · intro e'
    rw [← hEq]
    rfl
  · rw [← hEq]
    rfl
  · rw [← hEq]
    rfl
  · intro p ctx
    rw [← hEq]
    rfl
  · intro p ctx
    rw [← hEq]
    rfl

theorem assess_edge_recv {th : CTheory} {st mid : CState} {j : task} {requested : Bool}
    (step : Sys.tr th st (.considerViolation j requested) mid) :
    (∀ j', mid.received j' = st.received j') ∧ (∀ e', mid.changed e' = st.changed e') ∧
      mid.receiverHasChange = st.receiverHasChange ∧ mid.receiverLatest = st.receiverLatest := by
  dsimp only [Sys, relationalTransitionSystem, Next, NextAct] at step
  rw [considerViolation.ext.derived_eq] at step
  simp only [considerViolation.ext.tr] at step
  obtain ⟨_, _, update⟩ := step
  split at update <;> cases update
  all_goals
    refine ⟨fun x => ?_, fun e' => ?_, ?_, ?_⟩ <;> rfl

/-- Boundary relation between an original run's current state and the
old-send candidate run's current state: identical change and receipt facts,
no pending unreceived replacement send, and never any remote processing. -/
def OldifyInvariant (orig rebuilt : CState) : Prop :=
  (∀ e, orig.changed e = rebuilt.changed e) ∧
    (∀ j, orig.received j = rebuilt.received j) ∧
    (∀ j, rebuilt.received j = true ∨ rebuilt.sent j = false) ∧
    (∀ p ctx, rebuilt.processed p ctx = false)

/-- Every real run admits an observation-equivalent admissible run whose
receiver-invisible events are dropped and whose received occurrences are sent
exactly before their receive: an old-send candidate history. -/
theorem Runs.oldify {th : CTheory} {st fin : CState} {events : List CEvent}
    (run : Runs th st events fin) :
    ∀ r0, OldifyInvariant st r0 →
      ∃ fin', Runs th r0 (events.flatMap eventBlock) fin' ∧ OldifyInvariant fin fin' ∧
        observe (events.flatMap eventBlock) = observe events := by
  induction run with
  | nil st =>
    intro r0 inv
    exact ⟨r0, .nil r0, inv, rfl⟩
  | @cons st middle last event rest step tail ih =>
    intro r0 inv
    obtain ⟨hchg, hrecv, hsentKeep, hprocFalse⟩ := inv
    cases event with
    | changeSubscription e =>
      have hcopies := change_edge_recv step
      obtain ⟨hmrecv, hmchg, _⟩ := hcopies
      dsimp only [Sys, relationalTransitionSystem, Next, NextAct] at step
      rw [changeSubscription.ext.derived_eq] at step
      simp only [changeSubscription.ext.tr] at step
      obtain ⟨hguard, _⟩ := step
      have hstChanged : st.changed e = false := by
        simpa [getFrom, Veil.FieldRepresentation.get] using hguard
      obtain ⟨r1, step1, f1flag, f1latest, f1chg, f1recv, f1sent, f1proc, _⟩ :=
        change_step th r0 e (by rw [← hchg e]; exact hstChanged)
      have hmchg' : ∀ x, middle.changed x = (r0.changed x || decide (e = x)) := by
        intro x
        rw [hmchg x, hchg x]
      obtain ⟨fin', stepRest, finv, hobs⟩ := ih r1
        (by
          refine ⟨?_, ?_, ?_, ?_⟩
          · intro x; rw [hmchg' x, f1chg x]
          · intro j; rw [hmrecv j, f1recv j, hrecv j]
          · intro j; rw [f1recv j, f1sent j]; exact hsentKeep j
          · intro p ctx; rw [f1proc p ctx]; exact hprocFalse p ctx)
      exact ⟨fin', Runs.cons step1 stepRest, finv, by rw [observation_oldify]⟩
    | remoteProcesses p e =>
      have hcopies := process_edge_copies step
      obtain ⟨hmchg, hmrecv, _, _⟩ := hcopies
      obtain ⟨fin', stepRest, finv, hobs⟩ := ih r0
        (by
          refine ⟨?_, ?_, ?_, ?_⟩
          · intro x; rw [hmchg x, hchg x]
          · intro j; rw [hmrecv j, hrecv j]
          · exact hsentKeep
          · exact hprocFalse)
      exact ⟨fin', stepRest, finv, by rw [observation_oldify]⟩
    | send j =>
      have hcopies := send_edge_copies step
      obtain ⟨hmchg, hmrecv, _, _⟩ := hcopies
      obtain ⟨fin', stepRest, finv, hobs⟩ := ih r0
        (by
          refine ⟨?_, ?_, ?_, ?_⟩
          · intro x; rw [hmchg x, hchg x]
          · intro j; rw [hmrecv j, hrecv j]
          · exact hsentKeep
          · exact hprocFalse)
      exact ⟨fin', stepRest, finv, by rw [observation_oldify]⟩
    | considerViolation j requested =>
      have hcopies := assess_edge_recv step
      obtain ⟨hmrecv, hmchg, _, _⟩ := hcopies
      obtain ⟨fin', stepRest, finv, hobs⟩ := ih r0
        (by
          refine ⟨?_, ?_, ?_, ?_⟩
          · intro x; rw [hmchg x, hchg x]
          · intro j; rw [hmrecv j, hrecv j]
          · exact hsentKeep
          · exact hprocFalse)
      exact ⟨fin', stepRest, finv, by rw [observation_oldify]⟩
    | receive j =>
      have hrcv := receive_edge_recv step
      dsimp only [Sys, relationalTransitionSystem, Next, NextAct] at step
      rw [receive.ext.derived_eq] at step
      simp only [receive.ext.tr] at step
      obtain ⟨_, hguardRecv, _⟩ := step
      have hstRecv : st.received j = false := by
        simpa [getFrom, Veil.FieldRepresentation.get] using hguardRecv
      have r0sent : r0.sent j = false := by
        rcases hsentKeep j with h | h
        · rw [← hrecv j, hstRecv] at h
          exact absurd h (by simp)
        · exact h
      obtain ⟨r1, stepS, f1recv, f1chg, f1flag, f1latest, f1sentJ, f1sent, f1sentAt, f1serial,
        f1proc, f1procAt⟩ := send_step th r0 j r0sent
      obtain ⟨r2, stepR, f2recvJ, f2recv, f2chg, f2flag, f2latest, f2sent, f2sentAt, f2proc,
        f2procAt⟩ :=
        receive_step th r1 j f1sentJ (by rw [f1recv j, ← hrecv j]; exact hstRecv)
      have hmid2 : ∀ x, middle.changed x = r0.changed x := by
        intro x
        rw [hrcv.2.1 x, hchg x]
      obtain ⟨fin', stepRest, finv, hobs⟩ := ih r2
        (by
          refine ⟨?_, ?_, ?_, ?_⟩
          · intro x
            rw [hmid2 x, f2chg x, f1chg x]
          · intro j'
            rw [hrcv.1 j', f2recv j', f1recv j', hrecv j']
          · intro j'
            by_cases hjc : j = j'
            · subst hjc
              exact Or.inl f2recvJ
            · have h2r : r2.received j' = st.received j' := by
                rw [f2recv j', f1recv j', hrecv j']
                simp [hjc]
              have h2s : r2.sent j' = r0.sent j' := by
                rw [f2sent j', f1sent j']
                simp [hjc]
              rcases hsentKeep j' with hT | hF
              · exact Or.inl (by rw [h2r, hrecv j']; exact hT)
              · exact Or.inr (by rw [h2s]; exact hF)
          · intro p ctx
            rw [f2proc p ctx, f1proc p ctx]
            exact hprocFalse p ctx)
      exact ⟨fin', Runs.cons stepS (Runs.cons stepR stepRest), finv, by rw [observation_oldify]⟩

/-- An initial causal state has empty default bookkeeping. -/
theorem initial_defaults {th : CTheory} {st : CState}
    (initialized : Sys.init th st) :
    (∀ j, st.received j = false) ∧ (∀ j, st.sent j = false) ∧
      (∀ p ctx, st.processed p ctx = false) := by
  dsimp only [Sys, relationalTransitionSystem, Init, initializer.ext.tr] at initialized
  cases initialized
  refine ⟨?_, ?_, ?_⟩
  · intro j; rfl
  · intro j; rfl
  · intro p ctx; rfl

theorem no_change_permission {th : CTheory} (h : History th) (j : task)
    (noChange : (observe h.events).any Observation.isChange = false) : Permission h j := by
  rintro ⟨alternative, same, _, changed, _⟩
  have absent := alternative.change_flag
  rw [same, noChange] at absent
  simp [absent] at changed

/-- A subscription change observed together with the message's own receipt
always admits an observation-equivalent old-send run: the replacement run
drops receiver-invisible events, replays the changes, and sends exactly
before the receive. -/
theorem possibly_old_of_change {th : CTheory} {h : History th} {j : task}
    (received : h.last.received j = true)
    (changed : (observe h.events).any Observation.isChange = true) :
    PossiblyOld th (observe h.events) j := by
  obtain ⟨fin', run', finv, hobs⟩ := h.execution.oldify h.initial
    (by
      obtain ⟨_, hsent, hproc⟩ := initial_defaults h.initialized
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro x; rfl
      · intro x; rfl
      · intro j; exact Or.inr (hsent j)
      · intro p ctx; exact hproc p ctx)
  refine ⟨⟨h.initial, fin', h.events.flatMap eventBlock, h.initialized, run'⟩, hobs,
    by rw [← finv.2.1 j]; exact received, ?_⟩
  refine ⟨?_, ?_⟩
  · rw [Runs.change_flag run', initial_has_no_change h.initialized, hobs, changed]
    rfl
  · rw [finv.2.2.2 (th.sender j) fin'.receiverLatest]
    simp

theorem permission_never_after_observed_change {th : CTheory} {h : History th} {j : task}
    (received : h.last.received j = true)
    (changed : (observe h.events).any Observation.isChange = true) : ¬ Permission h j :=
  fun hp => hp (possibly_old_of_change received changed)

end Libp2p.TemporalKnowledge
