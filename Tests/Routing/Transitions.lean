import Libp2p.RoutingSafety
import Veil.Core.Tools.ModelChecker.Concrete.Sequential

open Veil Veil.ModelChecker Veil.ModelChecker.Concrete
open scoped Libp2p.Routing

namespace Libp2p.RoutingTests

abbrev Peer := Fin 4
abbrev Topic := Fin 2
abbrev Message := Fin 3
abbrev Id := Fin 2
abbrev Snapshot := Fin 2
abbrev RT := Routing.Theory Peer Topic Message Id Snapshot
abbrev RS := Routing.State (Routing.FieldConcreteType Peer Topic Message Id Snapshot)
abbrev Label := Routing.Label Peer Topic Message Id Snapshot

-- Candidates 0 and 1 collide; peer 3 is explicit; snapshot 1 makes peer 0 negative.
def fixture : RT :=
  { initialSnapshot := 0
    explicitPeer := fun p => p == 3
    nonnegative := fun s p => s == 0 || p != 0
    publishEligible := fun s p => s == 0 || p == 1
    pxEligible := fun s p => s == 0 || p == 1
    messageTopic := fun _ _ => true
    key := fun m => if m == 2 then 1 else 0
    knownPeers := [0, 0, 1, 2, 3]
    highDegree := 2 }

instance : LogSwitch := ⟨false⟩
def system (th : RT) := Routing.enumerableTransitionSystem Peer Topic Message Id Snapshot th

def readField (label : Routing.State.Label)
    (value : Routing.FieldConcreteType Peer Topic Message Id Snapshot label) :=
  @FieldRepresentation.get _ _ _
    (Routing.instFieldRepresentation Peer Topic Message Id Snapshot label) value

def ensure (condition : Bool) (reason : String) : IO Unit :=
  unless condition do throw <| IO.userError reason

def take (th : RT) (st : RS) (label : Label) : IO RS := do
  let result := (system th).tr th st
  ensure result.failures.isEmpty "unexpected assertion failure"
  match result.successes.find? (fun edge => edge.1 == label) with
  | some (_, next) => pure next
  | none => throw <| IO.userError s!"expected enabled transition: {repr label}"

def disabled (th : RT) (st : RS) (label : Label) : IO Unit := do
  let result := (system th).tr th st
  ensure result.failures.isEmpty "unexpected assertion failure"
  ensure (!result.successes.any (fun edge => edge.1 == label)) s!"unexpected enabled transition: {repr label}"

def runSteps (labels : List Label) (th : RT := fixture) : IO RS :=
  labels.foldlM (take th) (system th).initStates.head!

def shouldUseTheConfiguredInitialSnapshot : IO Unit := do
  let th := { fixture with initialSnapshot := 1 }
  let st ← runSteps [.join 0, .graft 0 0 false] th
  ensure (st.currentSnapshot == 1) "initializer substituted the snapshot sort's default"
  ensure (!readField .mesh st.mesh 0 0 && readField .pruned st.pruned 0 0) "initial negative score bypassed admission"

def shouldRetainNegativeMeshUntilHeartbeat : IO Unit := do
  let st ← runSteps [.join 0, .join 1, .graft 0 0 false, .graft 0 1 false,
    .graft 1 0 false, .validatedRemote 0, .refreshScores 1]
  ensure (readField .mesh st.mesh 0 0 && readField .mesh st.mesh 0 1) "refresh pruned atomically"
  ensure (!st.heartbeatClean && readField .meshSnapshot st.meshSnapshot 0 0 == 0) "lost admission snapshot"
  let st ← take fixture st (.forwardRemote 0 0 0)
  let st ← take fixture st .heartbeat
  ensure (!readField .mesh st.mesh 0 0 && !readField .mesh st.mesh 0 1) "heartbeat retained negative peer"
  ensure (readField .mesh st.mesh 1 0) "heartbeat removed nonnegative peer"
  ensure (readField .pruned st.pruned 0 0 && readField .backoff st.backoff 0 0) "heartbeat omitted prune/backoff"
  disabled fixture st (.forwardRemote 0 0 0)

def shouldFilterFanoutAtJoinAndKeepOtherTopics : IO Unit := do
  let st ← runSteps [.subscribe 0 0, .addFanout 0 0, .subscribe 1 1, .addFanout 1 1, .refreshScores 1, .join 0]
  ensure (!readField .mesh st.mesh 0 0) "JOIN promoted stale negative fanout"
  ensure (readField .fanout st.fanout 1 1) "JOIN changed another topic"
  let st ← take fixture st (.join 1)
  ensure (readField .mesh st.mesh 1 1) "JOIN failed to promote eligible topic member"
  let st ← take fixture st (.leave 0)
  ensure (readField .mesh st.mesh 1 1) "LEAVE removed another topic"
  let st ← take fixture st (.leave 1)
  ensure (!readField .mesh st.mesh 1 1 && readField .pruned st.pruned 1 1) "LEAVE omitted removal/PRUNE"

def shouldSuppressCollidingIdsOnlyForTheRequestingMeshPeer : IO Unit := do
  let st ← runSteps [.join 0, .graft 0 0 false, .graft 1 0 false, .validatedRemote 1, .idontwant 0 0 true]
  disabled fixture st (.forwardRemote 0 0 1)
  ensure (!readField .suppressed st.suppressed 1 0) "IDONTWANT changed another peer"
  let st ← take fixture st (.forwardRemote 1 0 1)
  let st ← take fixture st (.idontwant 3 0 true)
  let _ ← take fixture st (.forwardRemote 3 0 1)
  let st ← take fixture st (.expireSuppression 0 0)
  let _ ← take fixture st (.forwardRemote 0 0 1)
  disabled fixture st (.forwardRemote 3 0 2)

def shouldHonorOptionalControlAndReplacementPolicy : IO Unit := do
  let st ← runSteps [.idontwant 0 0 false]
  ensure (!readField .suppressed st.suppressed 0 0) "ignored control mutated suppression"
  let next ← take fixture st (.ignoredIdontwant 0 0)
  ensure (next == st) "ignoring optional control produced an effect"
  let st ← take fixture st (.idontwant 0 0 true)
  let st ← take fixture st (.idontwant 0 1 true)
  let st ← take fixture st (.idontwant 1 0 true)
  let retained ← take fixture st (.replaceSession 0 false)
  ensure (retained == st) "retention policy was not respected"
  let cleared ← take fixture st (.replaceSession 0 true)
  ensure (!readField .suppressed cleared.suppressed 0 0 && !readField .suppressed cleared.suppressed 0 1)
    "replacement failed to clear all of the peer's IDs"
  ensure (readField .suppressed cleared.suppressed 1 0) "replacement cleared another peer"

def shouldExpireLocalEchoWithoutTransferringAcceptance : IO Unit := do
  let st ← runSteps [.join 0, .graft 0 0 false, .validatedLocal 0]
  ensure (!readField .valid st.valid 1) "ID collision transferred acceptance"
  disabled fixture st (.forwardRemote 0 0 1)
  let st ← take fixture st (.validatedRemote 1)
  disabled fixture st (.forwardRemote 0 0 1)
  disabled fixture st (.forwardRemote 3 0 1)
  let st ← take fixture st (.expirePublication 0)
  let _ ← take fixture st (.forwardRemote 0 0 1)
  disabled fixture st (.forwardRemote 0 0 0)
  disabled fixture st (.forwardRemote 0 0 2)
  let st ← take fixture st (.subscribe 0 0)
  let st ← take fixture st (.publish 0 0 0)
  disabled fixture st (.forwardRemote 0 0 1)

def shouldGatePublicationAtUseTime : IO Unit := do
  let st ← runSteps [.subscribe 0 0, .subscribe 3 0, .validatedLocal 0, .publish 0 0 0, .refreshScores 1]
  ensure (readField .publishSnapshot st.publishSnapshot 0 0 == 0) "refresh rewrote publication evidence"
  disabled fixture st (.publish 0 0 0)
  let _ ← take fixture st (.publish 3 0 0)
  disabled fixture st (.publish 3 0 1)

def shouldGatePxWithoutAuthenticatingReferrals : IO Unit := do
  let st ← runSteps [.referral 0 1]
  ensure (readField .pxCandidate st.pxCandidate 1 && !readField .pxAuthenticated st.pxAuthenticated 1)
    "PX manufactured authentication"
  disabled fixture st (.authenticateReferral 1 false)
  let st ← take fixture st (.authenticateReferral 1 true)
  let st ← take fixture st (.refreshScores 1)
  disabled fixture st (.referral 0 2)
  let st ← take fixture st (.referral 1 2)
  ensure (readField .pxSource st.pxSource 2 == 1 && readField .pxSnapshot st.pxSnapshot 2 == 1)
    "PX lost source/snapshot binding"

def shouldUseActualCapacityAndConnectionDirection : IO Unit := do
  let st ← runSteps [.join 0, .graft 0 0 false, .graft 1 0 false]
  ensure (st.graftDegree == 1) "duplicate knownPeer was counted twice"
  let rejected ← take fixture st (.graft 2 0 false)
  ensure (!readField .mesh rejected.mesh 2 0 && readField .pruned rejected.pruned 2 0)
    "oversubscribed inbound GRAFT was accepted"
  let accepted ← take fixture st (.graft 2 0 true)
  ensure (readField .mesh accepted.mesh 2 0 && accepted.graftOutbound && accepted.graftDegree == 2)
    "outbound exception did not use the actual request's role"
  let subscribed ← take fixture st (.subscribe 2 0)
  let selected ← take fixture subscribed (.localGraft 2 0)
  ensure (readField .mesh selected.mesh 2 0) "local selection inherited incoming GRAFT capacity restriction"

def shouldRejectExplicitBackoffNegativeAndIgnoreUnknownTopic : IO Unit := do
  let st ← runSteps [.join 0, .graft 0 0 false, .prune 0 0]
  let unknown ← take fixture st (.graft 1 1 false)
  ensure (unknown == st) "unknown-topic GRAFT was not a no-op"
  let explicit ← take fixture st (.graft 3 0 true)
  ensure (!readField .mesh explicit.mesh 3 0 && readField .pruned explicit.pruned 3 0) "explicit GRAFT accepted"
  ensure (explicit.currentSnapshot == st.currentSnapshot) "PRUNE changed the score"
  let validated ← take fixture explicit (.validatedRemote 1)
  let _ ← take fixture validated (.forwardRemote 3 0 1)
  let blocked ← take fixture st (.graft 0 0 true)
  ensure (!readField .mesh blocked.mesh 0 0) "backoff GRAFT accepted"
  let st ← take fixture st (.expireBackoff 0 0)
  let st ← take fixture st (.refreshScores 1)
  let rejected ← take fixture st (.graft 0 0 true)
  ensure (!readField .mesh rejected.mesh 0 0 && readField .pruned rejected.pruned 0 0) "negative GRAFT accepted"

def shouldRejectUntrackedMeshMembers : IO Unit := do
  let th := { fixture with knownPeers := [0] }
  let st ← runSteps [.join 0] th
  disabled th st (.graft 1 0 true)
  let st ← take th st (.subscribe 1 0)
  disabled th st (.localGraft 1 0)

def run : IO Unit := do
  shouldUseTheConfiguredInitialSnapshot
  shouldRetainNegativeMeshUntilHeartbeat
  shouldFilterFanoutAtJoinAndKeepOtherTopics
  shouldSuppressCollidingIdsOnlyForTheRequestingMeshPeer
  shouldHonorOptionalControlAndReplacementPolicy
  shouldExpireLocalEchoWithoutTransferringAcceptance
  shouldGatePublicationAtUseTime
  shouldGatePxWithoutAuthenticatingReferrals
  shouldUseActualCapacityAndConnectionDirection
  shouldRejectExplicitBackoffNegativeAndIgnoreUnknownTopic
  shouldRejectUntrackedMeshMembers
  IO.println "Routing: 11 executable transition scenarios passed"

#eval run

-- A complete finite exploration of the admission/score/heartbeat slice, not the entire model.
def dynamicLabels : List Label := [.join 0, .graft 0 0 false, .graft 0 0 true,
  .refreshScores 0, .refreshScores 1, .heartbeat, .prune 0 0, .expireBackoff 0 0]

def dynamicSystem : EnumerableTransitionSystem RT (List RT) RS (List RS)
    Int Label (Transitions Label Int RS) fixture :=
  { system fixture with
    tr := fun th st =>
      let result := (system fixture).tr th st
      { successes := result.successes.filter (fun edge => dynamicLabels.contains edge.1)
        failures := result.failures.filter (fun edge => dynamicLabels.contains edge.label) } }

def dynamicParameters : SearchParameters RT RS where
  invariants := [⟨`heartbeat_gate, fun _ st =>
    (st.heartbeatClean && readField .mesh st.mesh 0 0) = true → st.currentSnapshot = 0⟩,
    ⟨`admission_gate, fun _ st => readField .mesh st.mesh 0 0 = true →
      readField .meshSnapshot st.meshSnapshot 0 0 = 0⟩]
  earlyTerminationConditions := [.foundViolatingState, .assertionFailed, .deadlockOccurred]

#eval show IO Unit from do
  let (id, token) ← allocProgressInstance (.modelCheck {})
  let result ← breadthFirstSearchSequential (σₕ := UInt64) (T := LabelVector Label)
    dynamicParameters dynamicSystem 60000 id token
  let st := result.val.val
  match st.base.finished with
  | some .exploredAllReachableStates =>
    IO.println s!"Dynamic routing slice: {st.log.size} hash-view states, completed without violation"
  | _ => throw <| IO.userError "dynamic routing exploration failed or incomplete"

end Libp2p.RoutingTests
