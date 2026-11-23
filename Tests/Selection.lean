import Libp2p.Selection
import Lean

open Libp2p.Selection

private def params : DegreeParams := ⟨4, 3, 5, 2, 2⟩
private def mesh : List Nat := [0, 1, 2, 3, 4, 5, 6]
private def scores (peer : Nat) : Rat := 10 - (peer : Rat)
private def outbound (peer : Nat) : Bool := decide (4 ≤ peer)

private def repaired : SurvivorPlan Nat :=
  { best := [0, 1], random := [2, 3], kept := [0, 1], removed := [2, 3], added := [4, 5] }

#guard checkOversubscription params mesh scores outbound repaired
#guard repaired.survivors == [0, 1, 4, 5]
#guard outboundCount outbound repaired.survivors == 2
#guard prunedPeers mesh repaired.survivors == [2, 3, 6]

example : repaired.Valid params mesh scores outbound := by decide +kernel
example : (prunedPeers mesh repaired.survivors).length = mesh.length - params.target :=
  repaired.pruned_cardinality params mesh scores outbound (by decide +kernel)

private def repairProtected : SurvivorPlan Nat :=
  { best := [0, 1, 2], random := [3], kept := [0, 1], removed := [2, 3], added := [4, 5] }

#guard checkOversubscription { params with score := 3 } mesh scores outbound repairProtected
#guard !checkOversubscription { params with score := 3 } mesh scores outbound
  { repairProtected with kept := [1, 2], removed := [0, 3] }

private def enoughOutbound : SurvivorPlan Nat :=
  { best := [0, 1], random := [4, 5], kept := [4, 0, 5, 1], removed := [], added := [] }

private def repairOutboundVictim : SurvivorPlan Nat :=
  { best := [0, 1], random := [2, 4], kept := [0, 1], removed := [2, 4], added := [5, 6] }

#guard checkOversubscription params mesh scores outbound repairOutboundVictim
#guard !checkOversubscription params mesh scores outbound
  { repairOutboundVictim with kept := [0, 1, 2], removed := [4], added := [5] }

#guard checkOversubscription params mesh scores outbound enoughOutbound
#guard !checkOversubscription params mesh scores outbound
  { enoughOutbound with kept := [0, 4, 5], removed := [1], added := [6] }
#guard !checkOversubscription params mesh scores outbound
  { repaired with kept := [2, 3], removed := [0, 1] }

private def preserveProtectedOutbound : SurvivorPlan Nat :=
  { best := [0, 1, 2, 3, 4], random := [5], kept := [0, 1, 2, 4], removed := [3, 5], added := [6, 7] }

#guard checkOversubscription ⟨6, 4, 7, 5, 3⟩ (List.range 9) scores
  (fun peer => peer == 4 || decide (6 ≤ peer)) preserveProtectedOutbound

#guard !checkOversubscription params mesh scores outbound { repaired with added := [4, 4] }
#guard !checkOversubscription params mesh scores outbound { repaired with added := [4, 7] }
#guard !checkOversubscription params mesh scores outbound { repaired with added := [4] }
#guard !checkOversubscription params mesh scores outbound { repaired with added := [4, 2] }
#guard !checkOversubscription params mesh scores outbound
  { repaired with best := [0, 2], random := [1, 3], kept := [0, 2], removed := [1, 3] }
#guard !checkOversubscription params mesh (fun peer => if peer == 6 then 100 else scores peer) outbound repaired
#guard !checkOversubscription params mesh (fun peer => if peer == 6 then -1 else scores peer) outbound repaired
#guard !checkOversubscription params mesh scores (fun peer => peer == 4) repaired
#guard !checkOversubscription params (0 :: mesh) scores outbound repaired
#guard !checkOversubscription { params with high := mesh.length } mesh scores outbound repaired
#guard !checkOversubscription { params with low := 2 } mesh scores outbound repaired
#guard !checkOversubscription { params with score := 5 } mesh scores outbound repaired

private def tiedChoice : SurvivorPlan Nat :=
  { best := [2, 3], random := [0, 1], kept := [2, 3], removed := [0, 1], added := [4, 5] }

#guard checkOversubscription params mesh (fun _ => 1) outbound repaired
#guard checkOversubscription params mesh (fun _ => 1) outbound tiedChoice

private def rising (peer : Nat) : Rat := (peer : Rat) / 2

#guard checkMedian [0, 1, 2] rising (1 / 2)
#guard !checkMedian [0, 1, 2] rising (3 / 4)
#guard !checkMedian ([] : List Nat) rising 0
#guard !checkMedian [0, 0, 2] rising 0
#guard checkMedian [2, 0] rising 0
#guard checkMedian [2, 0] rising 1
#guard checkMedian [2, 0] rising (1 / 2)
#guard checkMedian [2, 0] rising (3 / 4)
#guard !checkMedian [2, 0] rising (-1 / 2)
#guard !checkMedian [2, 0] rising (3 / 2)
#guard checkMedian [0, 1, 2, 3] (fun _ => 1 / 2) (1 / 2)

example (median : Rat) (h : IsMedian [0, 1, 2] rising median) :
    ∃ peer ∈ [0, 1, 2], rising peer = median :=
  IsMedian.odd_attained _ _ _ h (by decide)

example (median : Rat) (hl : 0 ≤ median) (hu : median ≤ 1) : IsMedian [0, 2] rising median :=
  IsMedian.between _ _ 0 median 1 (by decide +kernel) (by decide +kernel) hl hu

#guard checkOpportunistic [0, 1, 2] [2, 3, 4, 5] rising 1 (1 / 2) 2 [3, 4]
#guard !checkOpportunistic [0, 1, 2] [2, 3, 4, 5] rising (1 / 2) (1 / 2) 2 [3, 4]
#guard !checkOpportunistic [0, 1, 2] [2, 3, 4, 5] rising 1 (3 / 4) 2 [3, 4]
#guard !checkOpportunistic [0, 1, 2] [2, 3, 4, 5] rising 1 (1 / 2) 2 [2, 4]
#guard !checkOpportunistic [0, 1, 2] [2, 3, 4, 5] rising 1 (1 / 2) 2 [3, 3]
#guard !checkOpportunistic [0, 1, 2] [2, 3, 4, 5] rising 1 (1 / 2) 2 [3, 6]
#guard !checkOpportunistic [0, 1, 2] [2, 3, 4, 5] rising 1 (1 / 2) 1 [3]
#guard !checkOpportunistic [0, 1, 2] [2, 3, 4, 5] rising 1 (1 / 2) 2 [3]
#guard !checkOpportunistic [0, 1, 2] [3] rising 1 (1 / 2) 2 [3, 4]
#guard !checkOpportunistic [0, 1, 2] [3, 3, 4] rising 1 (1 / 2) 2 [3, 4]
#guard !checkOpportunistic [0, 1, 2] [3, 4]
  (fun peer => if peer == 3 then 1 / 2 else rising peer) 1 (1 / 2) 2 [3, 4]
#guard !checkOpportunistic [0, 1, 2] [3, 4]
  (fun peer => if peer == 3 then -1 else rising peer) 1 (1 / 2) 2 [3, 4]
#guard !checkOpportunistic [0, 1, 2] [3, 4] rising (-1) (1 / 2) 2 [3, 4]
#guard checkOpportunistic [0, 2] [3, 4] rising 2 0 2 [3, 4]
#guard checkOpportunistic [0, 2] [3, 4] rising 2 1 2 [3, 4]
#guard checkOpportunistic [0, 2] [3, 4] rising 2 (3 / 4) 2 [3, 4]

example : ([0, 1, 2] ++ [3, 4]).Nodup ∧ ([0, 1, 2] ++ [3, 4]).length = [0, 1, 2].length + 2 :=
  opportunistic_new_mesh [0, 1, 2] [2, 3, 4, 5] rising 1 (1 / 2) 2 [3, 4] (by decide +kernel)

open Lean in
run_cmd do
  let env ← getEnv
  for required in [`Libp2p.Selection.oversubscription_sound,
      `Libp2p.Selection.SurvivorPlan.pruned_cardinality, `Libp2p.Selection.opportunistic_sound,
      `Libp2p.Selection.opportunistic_new_mesh, `Libp2p.Selection.IsMedian.odd_attained,
      `Libp2p.Selection.checkOversubscription_iff, `Libp2p.Selection.checkOpportunistic_iff] do
    unless env.contains required do
      throwError "missing required theorem: {required}"
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  for (name, info) in env.constants.toList do
    if (`Libp2p.Selection).isPrefixOf (privateToUserName name) then
      match info with
      | .thmInfo _ =>
        let axioms ← collectAxioms name
        let unexpected := axioms.filter (!allowed.contains ·)
        unless unexpected.isEmpty do
          throwError "nonstandard axioms in {name}: {unexpected}"
        checked := checked + 1
      | .axiomInfo _ => throwError "project axiom is forbidden: {name}"
      | _ => pure ()
  logInfo m!"Selection axiom audit passed: {checked} theorems; only propext, Classical.choice, Quot.sound allowed"

#print axioms Libp2p.Selection.oversubscription_sound
#print axioms Libp2p.Selection.SurvivorPlan.prune_partition
#print axioms Libp2p.Selection.opportunistic_sound
#print axioms Libp2p.Selection.opportunistic_new_mesh
#print axioms Libp2p.Selection.IsMedian.odd_attained
#print axioms Libp2p.Selection.IsMedian.between
