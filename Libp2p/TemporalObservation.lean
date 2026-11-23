module

public import Libp2p.TemporalKnowledge

@[expose] public section
namespace Libp2p.TemporalObservation

open Libp2p.TemporalCausality

variable {peer topic task object context messageId subscription : Type}
variable [DecidableEq peer] [DecidableEq topic] [DecidableEq task] [DecidableEq object]
variable [DecidableEq context] [DecidableEq messageId] [DecidableEq subscription]
variable [Inhabited peer] [Inhabited topic] [Inhabited task] [Inhabited object]
variable [Inhabited context] [Inhabited messageId] [Inhabited subscription]

local notation "CState" => State (FieldAbstractType peer topic task object context messageId subscription)
local notation "CTheory" => Theory peer topic task object context messageId subscription
local notation "CEvent" => Label peer topic task object context messageId subscription
noncomputable abbrev Sys : Veil.RelationalTransitionSystem CTheory CState
    (Label peer topic task object context messageId subscription) :=
  relationalTransitionSystem peer topic task object context messageId subscription

open Libp2p.TemporalKnowledge

/-- Receiver-visible subscription-change heads are preserved in the
observation sequence. -/
theorem observe_cons_change {e : subscription} :
    ∀ rest : List CEvent,
      observe ((Label.changeSubscription e :: rest : List CEvent)) =
        Observation.subscriptionChanged e :: observe rest := by
  intro rest
  induction rest with
  | nil => rfl
  | cons event rest ih =>
    cases event <;> rfl

/-- Receiver-invisible send heads contribute nothing. -/
theorem observe_drop_send {j : task} :
    ∀ rest : List CEvent, observe ((Label.send j :: rest : List CEvent)) = observe rest := by
  intro rest
  induction rest with
  | nil => rfl
  | cons event rest ih =>
    cases event <;> rfl

/-- Receiver-invisible remote-processing heads contribute nothing. -/
theorem observe_drop_process {p : peer} {e : subscription} :
    ∀ rest : List CEvent, observe ((Label.remoteProcesses p e :: rest : List CEvent)) = observe rest := by
  intro rest
  induction rest with
  | nil => rfl
  | cons event rest ih =>
    cases event <;> rfl

/-- Receiver-invisible assessment heads contribute nothing. -/
theorem observe_drop_assess {j : task} {requested : Bool} :
    ∀ rest : List CEvent,
      observe ((Label.considerViolation j requested :: rest : List CEvent)) = observe rest := by
  intro rest
  induction rest with
  | nil => rfl
  | cons event rest ih =>
    cases event <;> rfl

/-- Receiver-visible receipt heads are preserved. -/
theorem observe_head_receive {j' : task} :
    ∀ rest : List CEvent,
      observe ((Label.receive j' :: rest : List CEvent)) = (Observation.received j' :: observe rest : List (Observation task subscription)) := by
  intro rest
  induction rest with
  | nil => rfl
  | cons event rest ih =>
    cases event <;> rfl

/-- A receipt is observed at most once: if the message was already received
or its receipt is observed, the run ends with it received. -/
theorem Runs.received_join {th : CTheory} {j : task} :
    ∀ {st last : CState} {events : List CEvent},
      Runs th st events last →
        (st.received j = true ∨ (Observation.received j) ∈ observe events) →
        last.received j = true := by
  intro st last events run
  induction run with
  | nil st =>
    intro h
    cases h with
    | inl h => exact h
    | inr mem => simp [observe, eventObservation] at mem
  | @cons st middle last event rest step tail ih =>
    intro h
    cases event with
    | changeSubscription e =>
      rcases h with h0 | mem0
      · exact ih (Or.inl (by rw [change_edge_recv step |>.1 j]; exact h0))
      · rw [observe_cons_change] at mem0
        rcases List.mem_cons.mp mem0 with heq | hmem
        · exact absurd heq (by simp)
        · exact ih (Or.inr hmem)
    | send j' =>
      rcases h with h0 | mem0
      · exact ih (Or.inl (by rw [send_edge_recv step j]; exact h0))
      · rw [observe_drop_send] at mem0
        exact ih (Or.inr mem0)
    | remoteProcesses p e =>
      rcases h with h0 | mem0
      · exact ih (Or.inl (by rw [process_edge_recv step j]; exact h0))
      · rw [observe_drop_process] at mem0
        exact ih (Or.inr mem0)
    | considerViolation j' requested =>
      rcases h with h0 | mem0
      · exact ih (Or.inl (by rw [assess_edge_recv step |>.1 j]; exact h0))
      · rw [observe_drop_assess] at mem0
        exact ih (Or.inr mem0)
    | receive j' =>
      rcases h with h0 | mem0
      · exact ih (Or.inl (by rw [receive_edge_recv step |>.1 j]; simp [h0]))
      · by_cases hjc : j = j'
        · refine ih (Or.inl ?_)
          rw [receive_edge_recv step |>.1 j]
          simp [hjc]
        · have hcons : observe ((Label.receive j' :: rest : List CEvent)) =
            Observation.received j' :: observe rest := observe_head_receive rest
          rw [hcons] at mem0
          rcases List.mem_cons.mp mem0 with heq | hmem
          · exact absurd heq (by simp [hjc])
          · exact ih (Or.inr hmem)

/-- A receipt that was not already held is visible in the observation
sequence. -/
theorem Runs.received_observable {th : CTheory} {j : task} :
    ∀ {st last : CState} {events : List CEvent},
      Runs th st events last →
        st.received j = false → last.received j = true →
        (Observation.received j) ∈ observe events := by
  intro st last events run
  induction run with
  | nil st =>
    intro h0 h1
    simp [h0] at h1
  | @cons st middle last event rest step tail ih =>
    intro h0 h1
    cases event with
    | changeSubscription e =>
      rw [observe_cons_change]
      exact List.mem_cons_of_mem _ (ih (by rw [change_edge_recv step |>.1 j]; exact h0) h1)
    | send j' =>
      rw [observe_drop_send]
      exact ih (by rw [send_edge_recv step j]; exact h0) h1
    | remoteProcesses p e =>
      rw [observe_drop_process]
      exact ih (by rw [process_edge_recv step j]; exact h0) h1
    | considerViolation j' requested =>
      rw [observe_drop_assess]
      exact ih (by rw [assess_edge_recv step |>.1 j]; exact h0) h1
    | receive j' =>
      by_cases hjc : j = j'
      · rw [observe_head_receive]
        refine List.mem_cons.mpr (Or.inl ?_)
        rw [hjc]
      · have hcons : observe ((Label.receive j' :: rest : List CEvent)) =
          Observation.received j' :: observe rest := observe_head_receive rest
        rw [hcons]
        refine List.mem_cons_of_mem _ (ih ?_ h1)
        rw [receive_edge_recv step |>.1 j]
        simp [h0, (decide_eq_false_iff_not).mpr (Ne.symm hjc)]

/-- History level form: an unexplained receipt is visible in the observed
event sequence. -/
theorem History.received_observable {th : CTheory} {j : task} (h : History th)
    (hrecv : h.last.received j = true) : (Observation.received j) ∈ observe h.events :=
  Runs.received_observable h.execution ((initial_defaults h.initialized).1 j) hrecv

end Libp2p.TemporalObservation
