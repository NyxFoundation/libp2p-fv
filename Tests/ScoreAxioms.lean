import Libp2p.ScoreConfig
import Libp2p.ScoreThresholds
import Lean

open Lean in
run_cmd do
  let env ← getEnv
  for required in [`Libp2p.TopicCounters.updates_valid, `Libp2p.ScoreState.decay_valid,
      `Libp2p.ScoreState.unconfigured_update_excluded, `Libp2p.ScoreThresholds.classify_refines,
      `Libp2p.validQuotas_iff, `Libp2p.totalScore_cap_bound, `Libp2p.squaredPenalty_after_decay] do
    unless env.contains required do
      throwError "missing required theorem: {required}"
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  for (name, info) in env.constants.toList do
    if (`Libp2p).isPrefixOf (privateToUserName name) then
      match info with
      | .thmInfo _ =>
        let axioms ← collectAxioms name
        let unexpected := axioms.filter (!allowed.contains ·)
        unless unexpected.isEmpty do
          throwError "nonstandard axioms in {name}: {unexpected}"
        checked := checked + 1
      | .axiomInfo _ => throwError "project axiom is forbidden: {name}"
      | _ => pure ()
  unless checked > 0 do
    throwError "no project theorems were audited"
  logInfo m!"Score axiom audit passed: {checked} project theorems; only propext, Classical.choice, Quot.sound allowed"

#print axioms Libp2p.TopicCounters.updates_valid
#print axioms Libp2p.ScoreState.decay_valid
#print axioms Libp2p.ScoreState.unconfigured_update_excluded
#print axioms Libp2p.ScoreThresholds.classify_refines
#print axioms Libp2p.validQuotas_iff
#print axioms Libp2p.totalScore_cap_bound
#print axioms Libp2p.squaredPenalty_after_decay
