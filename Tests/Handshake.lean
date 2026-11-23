import Libp2p.Handshake
import Lean

open Libp2p.Handshake

private def cleanCertificate : CertificateFields Nat := localCertificate 42
private def subjectOnly : CertificateFields Nat :=
  { cleanCertificate with subjectUniqueId := some [] }
private def issuerOnly : CertificateFields Nat :=
  { cleanCertificate with issuerUniqueId := some [false] }
private def bothUniqueIds : CertificateFields Nat :=
  { subjectOnly with issuerUniqueId := some [true, false] }

-- A present empty BIT STRING is not an absent field.
#guard cleanCertificate.subjectUniqueId == none
#guard cleanCertificate.issuerUniqueId == none
#guard cleanCertificate.core == 42
#guard acceptCertificate true .allow subjectOnly
#guard !acceptCertificate true .reject subjectOnly
#guard acceptCertificate true .allow issuerOnly
#guard !acceptCertificate true .reject issuerOnly
#guard acceptCertificate true .allow bothUniqueIds
#guard !acceptCertificate true .reject bothUniqueIds
#guard acceptCertificate true .allow cleanCertificate
#guard acceptCertificate true .reject cleanCertificate
#guard !acceptCertificate false .allow cleanCertificate
#guard !acceptCertificate false .allow bothUniqueIds

private def uniqueIdCases : List (Option (List Bool)) :=
  [none, some [], some [false], some [true, false]]

-- Exhaust all presence/value samples, both policies, and both external-check outcomes.
#guard uniqueIdCases.all fun subject => uniqueIdCases.all fun issuer =>
  [DeprecatedFieldPolicy.allow, .reject].all fun policy =>
    [false, true].all fun checks =>
      let certificate : CertificateFields Nat := ⟨42, subject, issuer⟩
      acceptCertificate checks policy certificate ==
        (checks && (policy == .allow || (subject.isNone && issuer.isNone)))

example : ¬ (∀ policy, acceptCertificate true policy subjectOnly = false) ∧
    ¬ (∀ policy, acceptCertificate true policy subjectOnly = true) :=
  receiver_neither_mandatory_reject_nor_accept subjectOnly (by decide)

example (core : Nat) (policy : DeprecatedFieldPolicy) (checks : Bool) :
    acceptCertificate checks policy (localCertificate core) = checks :=
  localCertificate_receiver_check core policy checks

private def supported : List String := ["/meshsub/1.3.0"]

#guard selectProtocol supported "/meshsub/1.3.0" == .selected "/meshsub/1.3.0"
#guard selectProtocol supported "/meshsub/1.2.0" == .na
#guard selectProtocol supported "/meshsub/1.3" == .na
#guard selectProtocol supported "/meshsub/1.3.0/extra" == .na
#guard selectProtocol supported "prefix/meshsub/1.3.0" == .na
#guard selectProtocol supported "" == .na
#guard selectProtocol [] "/meshsub/1.3.0" == .na
#guard (selectProtocol supported "/meshsub/1.2.0").handlerProtocol == none
#guard (selectProtocol supported "/meshsub/1.3.0").handlerProtocol == some "/meshsub/1.3.0"
#guard selectProtocol ["/meshsub/1.2.0", "/meshsub/1.3.0"] "/meshsub/1.3.0" ==
  .selected "/meshsub/1.3.0"
#guard selectProtocol ["/meshsub/1.3.0", "/meshsub/1.3.0"] "/meshsub/1.3.0" ==
  .selected "/meshsub/1.3.0"

example : selectProtocol supported "/meshsub/1.2.0" = .na ∧
    selectProtocol supported "/meshsub/1.3.0" = .selected "/meshsub/1.3.0" := by decide

example (ids : List String) (proposal handler : String) (different : handler ≠ proposal) :
    (selectProtocol ids proposal).handlerProtocol ≠ some handler :=
  no_substituted_handler ids proposal handler different

-- Audit this standalone module without depending on the Veil integration gate.
open Lean in
run_cmd do
  let env ← getEnv
  let required := [``localCertificate_omits_uniqueIds,
    ``serialized_localCertificate_omits_uniqueIds,
    ``receiver_neither_mandatory_reject_nor_accept,
    ``unsupported_proposal_na, ``selected_iff, ``no_substituted_handler]
  for name in required do
    unless env.contains name do
      throwError "missing required theorem: {name}"
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  for (name, info) in env.constants.toList do
    if (`Libp2p.Handshake).isPrefixOf (privateToUserName name) then
      match info with
      | .thmInfo _ =>
        let axioms ← collectAxioms name
        let unexpected := axioms.filter (!allowed.contains ·)
        unless unexpected.isEmpty do
          throwError "nonstandard axioms in {name}: {unexpected}"
        checked := checked + 1
      | .axiomInfo _ => throwError "project axiom is forbidden: {name}"
      | _ => pure ()
  unless checked ≥ required.length do
    throwError "handshake theorem audit was incomplete"
  logInfo m!"Handshake axiom audit passed: {checked} theorems"

#print axioms localCertificate_omits_uniqueIds
#print axioms serialized_localCertificate_omits_uniqueIds
#print axioms receiver_neither_mandatory_reject_nor_accept
#print axioms acceptCertificate_requires_other_checks
#print axioms unsupported_proposal_na
#print axioms selected_iff
#print axioms no_substituted_handler
