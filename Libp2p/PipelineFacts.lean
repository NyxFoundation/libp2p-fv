module

public import Libp2p.Interfaces
public import Libp2p.CompositionSupport

@[expose] public section
namespace Libp2p.Pipeline

open Classical
open scoped Libp2p.Pipeline

variable (S P I W O C ID Protocol V : Type)
variable [Inhabited S] [Inhabited P] [Inhabited I] [Inhabited W]
variable [Inhabited O] [Inhabited C] [Inhabited ID] [Inhabited Protocol] [Inhabited V]
variable [Verdict_EnumClass V]

local notation "PT" => Theory S P I W O C ID Protocol V
local notation "PS" => State (FieldAbstractType S P I W O C ID Protocol V)
local notation "PL" => Label S P I W O C ID Protocol V
local notation "sys" => relationalTransitionSystem S P I W O C ID Protocol V

theorem acceptance_monotone (th : PT) (st next : PS) (label : PL)
    (step : (sys).tr th st label next) (w : W) (accepted : st.accepted w = true) :
    next.accepted w = true := by
  cases label <;>
    simp only [relationalTransitionSystem, Next, NextAct, nextSimp,
      State.ext_iff, funext_iff] at step <;> grind

theorem acceptance_persists (th : PT) (st next : PS) (labels : List PL)
    (run : Runs sys th st labels next) (w : W) (accepted : st.accepted w = true) :
    next.accepted w = true := by
  exact run.preserve (fun state => state.accepted w = true)
    (fun _ _ _ ha ht => acceptance_monotone S P I W O C ID Protocol V _ _ _ _ ht w ha) accepted

theorem accepted_provenance (th : PT) (st : PS) (reachable : (sys).reachable th st)
    (w : W) (accepted : st.accepted w = true) :
    st.submitted w = true ∧ st.dispatched (th.source w) = true ∧
    st.negotiated (th.source w) = true ∧
    st.authenticated (th.owner (th.source w)) = true ∧
    st.identity (th.owner (th.source w)) = th.expected (th.owner (th.source w)) := by
  have safe := pipelineSafety S P I W O C ID Protocol V th st reachable
  veil_simp +instances only [Invariants, invSimp, substateSimp, dsimpFieldRepresentationGet] at safe
  grind

theorem authentication_contract (input : ProfileInputs S P I W O C ID Protocol) (st : PS)
    (reachable : (sys).reachable input.pipelineTheory st) (s : S)
    (authenticated : st.authenticated s = true) :
    (input.checks s).accept = true ∧
    Handshake.deprecatedFieldsAllowed (input.deprecatedPolicy s) (input.certificate s) = true ∧
    st.identity s = input.certificatePeer s ∧ st.identity s = input.expected s := by
  have safe := pipelineSafety S P I W O C ID Protocol V input.pipelineTheory st reachable
  veil_simp +instances only [Invariants, invSimp, substateSimp, dsimpFieldRepresentationGet] at safe
  have checked : (input.pipelineTheory (V := V)).certificateChecks s = true := by grind
  obtain ⟨checks, fields⟩ := input.certificate_checks s checked
  refine ⟨checks, fields, ?_, ?_⟩ <;> grind [ProfileInputs.pipelineTheory]

noncomputable def seenEffect (th : PT) (seen : ID → Bool) : PL → ID → Bool
  | .deliver w => fun k => if k = th.key w then true else seen k
  | .rememberKey id => fun k => if k = id then true else seen k
  | .expire id => fun k => if k = id then false else seen k
  | _ => seen

theorem seen_effect (th : PT) (st next : PS) (label : PL)
    (step : (sys).tr th st label next) :
    next.seen = seenEffect S P I W O C ID Protocol V th st.seen label := by
  funext k
  cases label <;>
    simp only [relationalTransitionSystem, Next, NextAct, nextSimp,
      State.ext_iff, funext_iff] at step <;>
    simp only [seenEffect] <;> grind

theorem seen_transaction (th : PT) (st next : PS) (labels : List PL)
    (run : Runs sys th st labels next) :
    next.seen = labels.foldl (seenEffect S P I W O C ID Protocol V th) st.seen := by
  induction run with
  | nil => rfl
  | cons step rest ih =>
    simpa only [List.foldl_cons, seen_effect S P I W O C ID Protocol V _ _ _ _ step] using ih

end Libp2p.Pipeline
