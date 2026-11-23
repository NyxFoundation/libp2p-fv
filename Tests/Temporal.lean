import Libp2p.TemporalSafety
import Libp2p.TemporalKnowledge
import Libp2p.TemporalWitness
import Lean

-- Finite exploration and symbolic non-vacuity traces run in each source module.
-- This gate checks the proof dependencies of all generated and handwritten results.
open Lean in
run_cmd do
  let env ← getEnv
  let required := [
    ``Libp2p.TemporalBackoff.backoffSafety,
    ``Libp2p.TemporalBackoff.activeGraft_effect,
    ``Libp2p.TemporalLimits.limitsSafety,
    ``Libp2p.TemporalCredit.creditSafety,
    ``Libp2p.TemporalCredit.credit_effect,
    ``Libp2p.TemporalRetention.retentionSafety,
    ``Libp2p.TemporalRetention.reconnect_within_lifetime_effect,
    ``Libp2p.TemporalCausality.causalitySafety,
    ``Libp2p.TemporalKnowledge.Runs.oldify,
    ``Libp2p.TemporalKnowledge.possibly_old_of_change,
    ``Libp2p.TemporalKnowledge.permission_never_after_observed_change,
    ``Libp2p.TemporalWitness.possibly_old_iff,
    ``Libp2p.TemporalWitness.order_check_not_observation_determined]
  let prefixes := [`Libp2p.TemporalBackoff, `Libp2p.TemporalLimits,
    `Libp2p.TemporalCredit, `Libp2p.TemporalRetention, `Libp2p.TemporalCausality,
    `Libp2p.TemporalKnowledge, `Libp2p.TemporalObservation, `Libp2p.TemporalWitness]
  for name in required do
    unless env.contains name do
      throwError "missing temporal theorem: {name}"
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  for (name, info) in env.constants.toList do
    if prefixes.any (·.isPrefixOf (privateToUserName name)) then
      match info with
      | .thmInfo _ =>
        let axioms ← collectAxioms name
        let unexpected := axioms.filter (!allowed.contains ·)
        unless unexpected.isEmpty do
          throwError "nonstandard axioms in {name}: {unexpected}"
        checked := checked + 1
      | .axiomInfo _ => throwError "temporal axiom is forbidden: {name}"
      | _ => pure ()
  unless checked ≥ required.length do
    throwError "temporal audit did not cover the required theorems"
  logInfo m!"Temporal axiom audit passed: {checked} theorems"

#print axioms Libp2p.TemporalBackoff.backoffSafety
#print axioms Libp2p.TemporalBackoff.activeGraft_effect
#print axioms Libp2p.TemporalLimits.limitsSafety
#print axioms Libp2p.TemporalCredit.creditSafety
#print axioms Libp2p.TemporalCredit.credit_effect
#print axioms Libp2p.TemporalRetention.retentionSafety
#print axioms Libp2p.TemporalRetention.reconnect_within_lifetime_effect
#print axioms Libp2p.TemporalCausality.causalitySafety
#print axioms Libp2p.TemporalKnowledge.Runs.oldify
#print axioms Libp2p.TemporalKnowledge.possibly_old_of_change
#print axioms Libp2p.TemporalKnowledge.permission_never_after_observed_change
#print axioms Libp2p.TemporalWitness.possibly_old_iff
#print axioms Libp2p.TemporalWitness.order_check_not_observation_determined
