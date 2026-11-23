module

public import Libp2p.CoreSafety
public import Libp2p.RoutingSafety
public import Libp2p.Selection

@[expose] public section
namespace Libp2p.Network

open Classical
open scoped Libp2p.Pipeline Libp2p.Cache Libp2p.Routing

variable (S P I W O C ID Protocol V T : Type)
variable [Inhabited S] [Inhabited P] [Inhabited I] [Inhabited W]
variable [Inhabited O] [Inhabited C] [Inhabited ID] [Inhabited Protocol]
variable [Inhabited V] [Inhabited T] [Pipeline.Verdict_EnumClass V]

local notation "CS" => Core.State S P I W O C ID Protocol V T
local notation "RS" => Routing.State (Routing.FieldAbstractType P T W ID (P → Rat))
local notation "CL" => Core.Label S P I W O C ID Protocol V T
local notation "PL" => Pipeline.Label S P I W O C ID Protocol V
local notation "RL" => Routing.Label P T W ID (P → Rat)
local notation "cSys" => Core.system S P I W O C ID Protocol V T
local notation "rSys" => Routing.relationalTransitionSystem P T W ID (P → Rat)

structure Theory where
  core : Core.Theory S P I W O C ID Protocol T
  explicitPeer : P → Bool
  knownPeers : List P
  knownSessions : List S
  degree : Selection.DegreeParams
  thresholds : ScoreThresholds
  initialScores : P → Rat
  outbound : S → Bool

structure State where
  core : CS
  routing : RS

inductive Label where
  | pipeline (action : PL)
  | receive (task : W)
  | commitRemote (task : W) (deliverToApplication : Bool)
  | commitLocal (task : W)
  | expire (id : ID)
  | refreshScores (actualSnapshot : P → Rat)
  | routing (action : RL)
  | subscribe (request : I) (topic : T)
  | graft (request : I) (topic : T)
  | prune (request : I) (topic : T)
  | idontwant (request : I) (id : ID) (honor : Bool)
  | ignoredIdontwant (request : I) (id : ID)
  | referral (request : I) (referred : P)
  | authenticateReferral (session : S)
  | ihave (request : I) (id : ID) (track : Bool)
  | cacheMaintenance (action : Cache.Label P W ID T)
  | sendRemote (task : W) (peer : P) (destination : I) (extensionsAttached : Bool)
  | publish (task : W) (peer : P) (destination : I) (extensionsAttached : Bool)
  | replyCached (request : I) (id : ID) (destination : I) (extensionsAttached : Bool)
  | gossip (id : ID) (topic : T) (peer : P) (destination : I) (extensionsAttached : Bool)
  | oversubscribe (topic : T) (plan : Selection.SurvivorPlan P)
  | opportunistic (topic : T) (median : Rat) (requested : Nat) (chosen : List P)

local notation "Th" => Theory S P I W O C ID Protocol T
local notation "St" => State S P I W O C ID Protocol V T
local notation "L" => Label S P I W O C ID Protocol V T

noncomputable def routingTheory (th : Th) : Routing.Theory P T W ID (P → Rat) where
  initialSnapshot := th.initialScores
  explicitPeer := th.explicitPeer
  nonnegative := fun snapshot p => (th.thresholds.classify (snapshot p)).nonnegative
  publishEligible := fun snapshot p => (th.thresholds.classify (snapshot p)).publish
  pxEligible := fun snapshot p => (th.thresholds.classify (snapshot p)).px
  messageTopic := fun w t => decide (th.core.topic w = t)
  key := th.core.input.key
  knownPeers := th.knownPeers
  highDegree := th.degree.high

def requestPeer (th : Th) (i : I) : P := th.core.input.expected (th.core.input.owner i)

def Inbound (th : Th) (st : St) (i : I) : Prop :=
  st.core.pipeline.live (th.core.input.owner i) = true ∧
  st.core.pipeline.authenticated (th.core.input.owner i) = true ∧
  st.core.pipeline.reset i = false ∧ st.core.pipeline.dispatched i = true ∧
  th.core.input.inbound i = true

def Request (th : Th) (st : St) (i : I) : Prop :=
  Inbound S P I W O C ID Protocol V T th st i ∧
    (th.explicitPeer (requestPeer S P I W O C ID Protocol T th i) = true ∨
      (th.thresholds.classify (st.routing.currentSnapshot
        (requestPeer S P I W O C ID Protocol T th i))).rpc = true)

def OutboundStream (th : Th) (st : St) (p : P) (i : I) : Prop :=
  st.core.pipeline.live (th.core.input.owner i) = true ∧
  st.core.pipeline.authenticated (th.core.input.owner i) = true ∧
  st.core.pipeline.reset i = false ∧ st.core.pipeline.negotiated i = true ∧
  th.core.input.inbound i = false ∧ requestPeer S P I W O C ID Protocol T th i = p

noncomputable def connected (th : Th) (st : St) (p : P) : Bool :=
  th.knownSessions.any fun s => st.core.pipeline.live s && st.core.pipeline.authenticated s &&
    decide (th.core.input.expected s = p)

noncomputable def outboundPeer (th : Th) (st : St) (p : P) : Bool :=
  th.knownSessions.any fun s => st.core.pipeline.live s && st.core.pipeline.authenticated s &&
    decide (th.core.input.expected s = p) && th.outbound s

noncomputable def meshRoster (th : Th) (st : St) (t : T) : List P :=
  th.knownPeers.eraseDups.filter fun p => st.routing.mesh p t

noncomputable def candidateRoster (th : Th) (st : St) (t : T) : List P :=
  th.knownPeers.eraseDups.filter fun p => st.routing.subscribed p t &&
    connected S P I W O C ID Protocol V T th st p && !th.explicitPeer p &&
    !st.routing.backoff p t && (th.thresholds.classify (st.routing.currentSnapshot p)).nonnegative &&
    !st.routing.mesh p t

/-- Raw actions cannot bypass composed publication, forwarding, or input attribution. -/
def pipelineAllowed (th : Th) : PL → Prop
  | .connect s => s ∈ th.knownSessions ∧ th.core.input.expected s ∈ th.knownPeers
  | .authenticate .. | .close .. | .openStream .. | .propose .. | .terminateStream ..
    | .dispatch .. | .cancel .. | .finishValidation .. | .credit .. | .penalize .. => True
  | _ => False

noncomputable def routingAllowed (th : Th) (st : St) : RL → Prop
  | .join .. | .leave .. | .heartbeat | .expireBackoff .. | .expireSuppression ..
    | .replaceSession .. => True
  | .addFanout p _ => connected S P I W O C ID Protocol V T th st p = true
  | _ => False

def maintenanceAllowed : Cache.Label P W ID T → Prop
  | .tickHistory | .tickPromises | .evict .. | .newTrackingInterval .. | .assessPromise .. => True
  | _ => False

noncomputable def Gate (th : Th) (st : St) : L → Prop
  | .pipeline a => pipelineAllowed S P I W O C ID Protocol V T th a
  | .routing a => routingAllowed S P I W O C ID Protocol V T th st a
  | .receive w => Request S P I W O C ID Protocol V T th st (th.core.input.source w)
  | .subscribe i _ | .graft i _ | .prune i _ | .idontwant i _ _
    | .ignoredIdontwant i _ | .referral i _ => Request S P I W O C ID Protocol V T th st i
  | .ihave i _ _ => Request S P I W O C ID Protocol V T th st i ∧
      (th.explicitPeer (requestPeer S P I W O C ID Protocol T th i) = true ∨
        (th.thresholds.classify (st.routing.currentSnapshot
          (requestPeer S P I W O C ID Protocol T th i))).gossip = true)
  | .cacheMaintenance a => maintenanceAllowed P W ID T a
  | .sendRemote w p i _ => Inbound S P I W O C ID Protocol V T th st (th.core.input.source w) ∧
      OutboundStream S P I W O C ID Protocol V T th st p i
  | .publish _ p i _ => OutboundStream S P I W O C ID Protocol V T th st p i
  | .replyCached req _ i _ => Request S P I W O C ID Protocol V T th st req ∧
      OutboundStream S P I W O C ID Protocol V T th st
        (requestPeer S P I W O C ID Protocol T th req) i
  | .gossip _ _ p i _ => OutboundStream S P I W O C ID Protocol V T th st p i ∧
      (th.explicitPeer p = true ∨ (th.thresholds.classify (st.routing.currentSnapshot p)).gossip = true)
  | .oversubscribe t plan => Selection.checkOversubscription th.degree
      (meshRoster S P I W O C ID Protocol V T th st t) st.routing.currentSnapshot
      (outboundPeer S P I W O C ID Protocol V T th st) plan = true
  | .opportunistic t median requested chosen => st.routing.joined t = true ∧
      Selection.checkOpportunistic (meshRoster S P I W O C ID Protocol V T th st t)
        (candidateRoster S P I W O C ID Protocol V T th st t) st.routing.currentSnapshot
        th.thresholds.opportunistic median requested chosen = true
  | _ => True

noncomputable def coreLabels (th : Th) : L → List CL
  | .pipeline a => [.pipeline a]
  | .receive w => [.receive w]
  | .commitRemote w deliver => [.commitRemote w deliver]
  | .commitLocal w => [.commitLocal w]
  | .expire k => [.expire k]
  | .authenticateReferral s => [.pipeline (.authenticate s)]
  | .ihave i k track => [.cache (.ihave (requestPeer S P I W O C ID Protocol T th i) k track)]
  | .cacheMaintenance a => [.cache a]
  | .sendRemote w _ i ext => [.pipeline (.forward w), .pipeline (.writeEnvelope i ext)]
  | .publish w _ i ext => [.commitLocal w, .pipeline (.writeEnvelope i ext)]
  | .replyCached req k i ext =>
      [.cache (.iwant (requestPeer S P I W O C ID Protocol T th req) k), .pipeline (.writeEnvelope i ext)]
  | .gossip k t _ i ext => [.cache (.gossip k t), .pipeline (.writeEnvelope i ext)]
  | _ => []

noncomputable def routingLabels (th : Th) (st : St) (afterCore : CS) : L → List RL
  | .routing a => [a]
  | .refreshScores scores => [.refreshScores scores]
  | .commitRemote w _ => [.validatedRemote w]
  | .commitLocal w => [.validatedLocal w]
  | .expire k => [.expirePublication k]
  | .subscribe i t => [.subscribe (requestPeer S P I W O C ID Protocol T th i) t]
  | .graft i t => [.graft (requestPeer S P I W O C ID Protocol T th i) t
      (th.outbound (th.core.input.owner i))]
  | .prune i t => [.prune (requestPeer S P I W O C ID Protocol T th i) t]
  | .idontwant i k honor => [.idontwant (requestPeer S P I W O C ID Protocol T th i) k honor]
  | .ignoredIdontwant i k => [.ignoredIdontwant (requestPeer S P I W O C ID Protocol T th i) k]
  | .referral i p => [.referral (requestPeer S P I W O C ID Protocol T th i) p]
  | .authenticateReferral s =>
      [.authenticateReferral (th.core.input.expected s) (afterCore.pipeline.authenticated s)]
  | .sendRemote w p _ _ => [.forwardRemote p (th.core.topic w) w]
  | .publish w p _ _ => [.publish p (th.core.topic w) w]
  | .oversubscribe t plan =>
      (Selection.prunedPeers (meshRoster S P I W O C ID Protocol V T th st t) plan.survivors).map
        fun p => .prune p t
  | .opportunistic t _ _ chosen => chosen.map fun p => .localGraft p t
  | _ => []

/-- Scores are exact snapshots supplied by the numeric composition, not counters proved here. -/
noncomputable def system : Veil.RelationalTransitionSystem Th St L where
  assumptions th := (cSys).assumptions th.core ∧
    (rSys).assumptions (routingTheory S P I W O C ID Protocol T th) ∧
    th.thresholds.Valid ∧ th.degree.Valid
  init th st := (cSys).init th.core st.core ∧
    (rSys).init (routingTheory S P I W O C ID Protocol T th) st.routing
  tr th st label next := Gate S P I W O C ID Protocol V T th st label ∧
    Runs cSys th.core st.core (coreLabels S P I W O C ID Protocol V T th label) next.core ∧
    Runs rSys (routingTheory S P I W O C ID Protocol T th) st.routing
      (routingLabels S P I W O C ID Protocol V T th st next.core label) next.routing

/-- A structured payload observation, not a serialization or wire-byte proof. -/
structure PayloadOutput where
  candidate : W
  destinationPeer : P
  destinationStream : I
  payload : O
  context : C
  key : ID
  topic : T
  envelope : Envelope

def payloadOutput (th : Th) (w : W) (p : P) (i : I) : PayloadOutput P I W O C ID T where
  candidate := w
  destinationPeer := p
  destinationStream := i
  payload := th.core.input.payload w
  context := th.core.input.scope w
  key := th.core.input.key w
  topic := th.core.topic w
  envelope := ⟨none, none, none, none⟩

/-- Labels, not persistent component pulses, define new global outputs. -/
def output (th : Th) (st : St) : L → Option (PayloadOutput P I W O C ID T)
  | .sendRemote w p i _ | .publish w p i _ => some (payloadOutput S P I W O C ID Protocol T th w p i)
  | .replyCached req k i _ => some (payloadOutput S P I W O C ID Protocol T th (st.core.cache.cached k)
      (requestPeer S P I W O C ID Protocol T th req) i)
  | _ => none

end Libp2p.Network
