import Libp2p.PipelineSafety
import Libp2p.Routing
import Libp2p.Cache
import Libp2p.Policies
import Lean

open Lean in
run_cmd do
  let env ← getEnv
  for required in [`Libp2p.Pipeline.pipelineSafety, `Libp2p.Routing.ic3_safe,
      `Libp2p.Cache.ic3_safe, `Libp2p.AuthChecks.accept_iff] do
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
#print axioms Libp2p.Routing.ic3_safe
#print axioms Libp2p.Cache.ic3_safe
