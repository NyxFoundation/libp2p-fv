import Libp2p.PipelineSafety
import Libp2p.Routing
import Libp2p.CacheSafety
import Libp2p.RoutingSafety
import Libp2p.CoreSafety
import Libp2p.NetworkSelection
import Libp2p.NetworkPublication
import Libp2p.ScoreConfig
import Libp2p.ScoreThresholds
import Libp2p.ScoreHistorySafety
import Libp2p.Selection
import Libp2p.TemporalWitness
import Libp2p.Policies
import Libp2p.Handshake
import Lean

open Lean in
run_cmd do
  let env ← getEnv
  for required in [`Libp2p.Pipeline.pipelineSafety,
      `Libp2p.Cache.cacheSafety, `Libp2p.Routing.routingSafety, `Libp2p.Core.coreSafety,
      `Libp2p.Network.core_reachable, `Libp2p.Network.routing_reachable,
      `Libp2p.Network.validation_binding, `Libp2p.Network.remote_send_correspondence,
      `Libp2p.Network.cached_reply_correspondence,
      `Libp2p.Network.referral_authentication_bound,
      `Libp2p.Network.oversubscription_result, `Libp2p.Network.opportunistic_result,
      `Libp2p.Network.publish_remembers_shared_id,
      `Libp2p.Network.expiry_synchronized,
      `Libp2p.ScoreState.decay_valid, `Libp2p.ScoreThresholds.classify_refines,
      `Libp2p.ScoreHistory.live_owner_unique, `Libp2p.ScoreHistory.reachable_preservation,
      `Libp2p.Selection.oversubscription_sound, `Libp2p.Selection.opportunistic_new_mesh,
      `Libp2p.TemporalWitness.possibly_old_iff,
      `Libp2p.TemporalWitness.order_check_not_observation_determined,
      `Libp2p.AuthChecks.accept_iff,
      `Libp2p.Handshake.serialized_localCertificate_omits_uniqueIds,
      `Libp2p.Handshake.unsupported_proposal_na] do
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
  logInfo m!"Axiom audit passed: {checked} project theorems; only propext, Classical.choice, Quot.sound allowed"

#print axioms Libp2p.Pipeline.pipelineSafety
#print axioms Libp2p.Cache.cacheSafety
#print axioms Libp2p.Routing.routingSafety
#print axioms Libp2p.Core.coreSafety
#print axioms Libp2p.Network.validation_binding
#print axioms Libp2p.Network.remote_send_correspondence
#print axioms Libp2p.Network.expiry_synchronized
#print axioms Libp2p.ScoreHistory.live_owner_unique
#print axioms Libp2p.ScoreHistory.reachable_preservation
#print axioms Libp2p.TemporalWitness.possibly_old_iff
#print axioms Libp2p.TemporalWitness.order_check_not_observation_determined
