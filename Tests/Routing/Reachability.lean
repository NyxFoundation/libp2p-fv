import Libp2p.RoutingSafety
import Lean

open scoped Libp2p.Routing

namespace Libp2p.Routing.Witness
abbrev F := Fin 1
abbrev Snapshot := Fin 2
abbrev RS := State (FieldAbstractType F F F F Snapshot)
def th : Theory F F F F Snapshot :=
  { initialSnapshot := 0, explicitPeer := fun _ => false, nonnegative := fun s _ => s == 0,
    publishEligible := fun s _ => s == 0, pxEligible := fun s _ => s == 0,
    messageTopic := fun _ _ => true, key := fun _ => 0, knownPeers := [0], highDegree := 1 }
noncomputable abbrev sys := relationalTransitionSystem F F F F Snapshot

def initial : RS := { (default : RS) with heartbeatClean := true }
def joinedState : RS := { initial with joined := fun _ => true }
def admittedState : RS :=
  { joinedState with mesh := fun _ _ => true, graftRecorded := true }
def negativeState : RS :=
  { admittedState with currentSnapshot := 1, heartbeatClean := false }
def heartbeatState : RS :=
  { negativeState with
    mesh := fun _ _ => false
    pruned := fun _ _ => true
    backoff := fun _ _ => true
    heartbeatClean := true }

macro "check_routing_fixture" : tactic => `(tactic|
  simp [relationalTransitionSystem, Init, Next, NextAct, nextSimp, meshDegree,
    IsSubStateOf.setIn, IsSubStateOf.getFrom, IsSubReaderOf.readFrom,
    instIsSubStateOfRefl, instIsSubReaderOfRefl, dsimpFieldRepresentationGet,
    th, initial, joinedState, admittedState, negativeState, heartbeatState,
    State.ext_iff, funext_iff] <;> decide)

theorem negative_mesh_is_reachable : sys.reachable th negativeState := by
  have h0 : sys.reachable th initial := .init _ (by check_routing_fixture) (by check_routing_fixture)
  have h1 : sys.reachable th joinedState := .step _ _ h0 ⟨.join 0, by check_routing_fixture⟩
  have h2 : sys.reachable th admittedState := .step _ _ h1 ⟨.graft 0 0 false, by check_routing_fixture⟩
  exact .step _ _ h2 ⟨.refreshScores 1, by check_routing_fixture⟩

theorem score_change_precedes_pruning :
    sys.reachable th negativeState ∧ negativeState.mesh 0 0 = true ∧
    th.nonnegative negativeState.currentSnapshot 0 = false :=
  ⟨negative_mesh_is_reachable, by decide, by decide⟩

theorem heartbeat_pruning_is_reachable :
    sys.reachable th heartbeatState ∧ heartbeatState.mesh 0 0 = false ∧
    heartbeatState.pruned 0 0 = true ∧ heartbeatState.backoff 0 0 = true := by
  refine ⟨.step _ _ negative_mesh_is_reachable ⟨.heartbeat, by check_routing_fixture⟩, ?_⟩
  decide

#print axioms negative_mesh_is_reachable
#print axioms score_change_precedes_pruning
#print axioms heartbeat_pruning_is_reachable
end Libp2p.Routing.Witness

open Lean in
run_cmd do
  let env ← getEnv
  for required in [`Libp2p.Routing.routingSafety, `Libp2p.Routing.graft_new_member_gate,
      `Libp2p.Routing.mesh_roster_exact, `Libp2p.Routing.suppression_blocks_colliding_candidate,
      `Libp2p.Routing.local_echo_blocks_colliding_candidate,
      `Libp2p.Routing.Witness.score_change_precedes_pruning] do
    unless env.contains required do throwError "missing routing theorem: {required}"
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  for (name, info) in env.constants.toList do
    if (`Libp2p).isPrefixOf (privateToUserName name) then
      match info with
      | .thmInfo _ =>
        let unexpected := (← collectAxioms name).filter (!allowed.contains ·)
        unless unexpected.isEmpty do throwError "nonstandard axioms in {name}: {unexpected}"
        checked := checked + 1
      | .axiomInfo _ => throwError "project axiom is forbidden: {name}"
      | _ => pure ()
  unless checked > 0 do throwError "no project theorems audited"
  logInfo m!"Routing namespace audit passed: {checked} imported project theorems, standard axioms only"

#print axioms Libp2p.Routing.routingSafety
#print axioms Libp2p.Routing.graft_new_member_gate
#print axioms Libp2p.Routing.suppression_blocks_colliding_candidate
#print axioms Libp2p.Routing.local_echo_blocks_colliding_candidate
