import Libp2p.NetworkSelection
import Libp2p.NetworkPublication

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

namespace Libp2p.NetworkTests
open scoped Libp2p.Pipeline Libp2p.Cache Libp2p.Routing

abbrev S := Fin 6
abbrev P := Fin 5
abbrev I := Fin 12
abbrev W := Fin 3
abbrev ID := Fin 1
abbrev T := Fin 1
abbrev Protocol := Fin 2
abbrev V := Pipeline.Verdict_IndT
abbrev PS := Pipeline.State (Pipeline.FieldAbstractType S P I W W W ID Protocol V)
abbrev CS := Cache.State (Cache.FieldAbstractType P W ID T)
abbrev RS := Routing.State (Routing.FieldAbstractType P T W ID (P → Rat))
abbrev St := Network.State S P I W W W ID Protocol V T
noncomputable abbrev sys := Network.system S P I W W W ID Protocol V T

def put {A B : Type} [DecidableEq A] (f : A → B) (a : A) (b : B) : A → B :=
  fun x => if a = x then b else f x

def put2 {A B C : Type} [DecidableEq A] [DecidableEq B] (f : A → B → C) (a : A) (b : B) (c : C) : A → B → C :=
  fun x y => if a = x ∧ b = y then c else f x y

def expected (s : S) : P :=
  if s = 0 then 0 else if s = 1 then 0 else if s = 2 then 1 else if s = 3 then 2 else if s = 4 then 3 else 4

def owner (i : I) : S :=
  if i < 2 then 0 else if i < 4 then 1 else if i < 6 then 2 else if i < 8 then 3 else if i < 10 then 4 else 5

def source (w : W) : I := if w = 0 then 0 else if w = 1 then 2 else 1

def scores (p : P) : Rat := if p = 3 ∨ p = 4 then 10 else 1

def checks : AuthChecks := ⟨true, true, true, true, true, true, true, true, true, true, true⟩

def input : ProfileInputs S P I W W W ID Protocol where
  expected := expected
  certificatePeer := expected
  checks := fun _ => checks
  certificate := fun _ => Handshake.localCertificate []
  deprecatedPolicy := fun _ => .reject
  supportedProtocol := 0
  owner := owner
  inbound := fun i => decide (i = 0 ∨ i = 2 ∨ i = 4 ∨ i = 6 ∨ i = 8 ∨ i = 10)
  supportsExtensions := fun _ => false
  source := source
  payload := id
  scope := id
  key := fun _ => 0
  decoded := fun _ => ⟨1, 1, true, true, true, ⟨none, none, none, none⟩⟩

def th : Network.Theory S P I W W W ID Protocol T where
  core := ⟨input, fun _ => 0, fun w => decide (w = 2), fun w => decide (w = 2), 2, 1, 2, 1⟩
  explicitPeer := fun _ => false
  knownPeers := [0, 1, 2, 3, 4, 1]
  knownSessions := [0, 1, 2, 3, 4, 5, 2]
  degree := ⟨2, 2, 2, 1, 1⟩
  thresholds := ⟨-1, -2, -3, 0, 5⟩
  initialScores := scores
  outbound := fun s => decide (s = 2 ∨ s = 4)

def withPipeline (st : St) (ps : PS) : St := { st with core := { st.core with pipeline := ps } }
def connectState (st : St) (s : S) : St := withPipeline st { st.core.pipeline with allocated := put st.core.pipeline.allocated s true, live := put st.core.pipeline.live s true, emitted := false }
def authState (st : St) (s : S) : St := withPipeline st { st.core.pipeline with authenticated := put st.core.pipeline.authenticated s true, emitted := false }
def openState (st : St) (i : I) : St := withPipeline st { st.core.pipeline with opened := put st.core.pipeline.opened i true, emitted := false }
def proposeState (st : St) (i : I) : St := withPipeline st { st.core.pipeline with negotiated := put st.core.pipeline.negotiated i true, proposalComplete := put st.core.pipeline.proposalComplete i true, emitted := false }
def dispatchState (st : St) (i : I) : St := withPipeline st { st.core.pipeline with dispatched := put st.core.pipeline.dispatched i true, emitted := false }
def subscribeState (st : St) (p : P) : St := { st with routing := { st.routing with subscribed := put2 st.routing.subscribed p 0 true } }
def fanoutState (st : St) (p : P) : St := { st with routing := { st.routing with fanout := put2 st.routing.fanout p 0 true, fanoutSnapshot := put2 st.routing.fanoutSnapshot p 0 st.routing.currentSnapshot } }
def localGraftState (st : St) (p : P) : St := { st with routing := { st.routing with mesh := put2 st.routing.mesh p 0 true, meshSnapshot := put2 st.routing.meshSnapshot p 0 st.routing.currentSnapshot } }
def receiveState (st : St) (w : W) : St := { st with core := { pipeline := { st.core.pipeline with submitted := put st.core.pipeline.submitted w true, pending := put st.core.pipeline.pending w true, emitted := false }, cache := { st.core.cache with arrived := fun k => if k = th.core.input.key w then true else st.core.cache.arrived k, requestEmitted := false, replyEmitted := false, gossipEmitted := false, penaltyEmitted := false } } }
def acceptState (st : St) (w : W) : St := withPipeline st { st.core.pipeline with pending := put st.core.pipeline.pending w false, accepted := put st.core.pipeline.accepted w true, emitted := false }
def rejectState (st : St) (w : W) : St := withPipeline st { st.core.pipeline with pending := put st.core.pipeline.pending w false, rejected := put st.core.pipeline.rejected w true, emitted := false }
def validatedCache (cache : CS) (w : W) : CS := { cache with accepted := put cache.accepted w true, requestEmitted := false, replyEmitted := false, gossipEmitted := false, penaltyEmitted := false }
def storedCache (cache : CS) (w : W) : CS := { cache with cached := fun k => if k = th.core.input.key w then w else cache.cached k, present := fun k => if k = th.core.input.key w then true else cache.present k, seen := fun k => if k = th.core.input.key w then true else cache.seen k, age := fun k => if k = th.core.input.key w then 0 else cache.age k }
def forwardState (st : St) (w : W) : St := withPipeline st { st.core.pipeline with forwarded := put st.core.pipeline.forwarded w true, lastTask := w, emitted := true }
def writeState (st : St) (i : I) : St := withPipeline st { st.core.pipeline with written := put st.core.pipeline.written i true, emitted := false }
def closeState (st : St) (s : S) : St := withPipeline st { st.core.pipeline with live := put st.core.pipeline.live s false, emitted := false }
def expireState (st : St) : St := { core := { pipeline := { st.core.pipeline with seen := fun _ => false, inWindow := fun _ => false, emitted := false }, cache := { st.core.cache with seen := fun _ => false, requestEmitted := false, replyEmitted := false, gossipEmitted := false, penaltyEmitted := false } }, routing := { st.routing with publishedId := fun _ => false } }
def recommitState (st : St) : St := { st with core := { pipeline := { st.core.pipeline with seen := fun k => if k = 0 then true else st.core.pipeline.seen k, emitted := false }, cache := storedCache (validatedCache st.core.cache 2) 2 } }
def publishState (st : St) : St := { (writeState (recommitState st) 5) with routing := { st.routing with publishedId := fun k => if k = 0 then true else st.routing.publishedId k, sentLocal := put2 st.routing.sentLocal 1 2 true, publishSnapshot := put2 st.routing.publishSnapshot 1 2 st.routing.currentSnapshot } }

def initial : St := { core := { pipeline := { (default : PS) with identity := expected, usedPayload := id, usedContext := id }, cache := default }, routing := { (default : RS) with currentSnapshot := scores, heartbeatClean := true } }
def plan : Selection.SurvivorPlan P := ⟨[0], [1], [0, 1], [], []⟩
def p0 : PS := { (default : PS) with identity := expected, usedPayload := id, usedContext := id }

def connected0 : St := connectState initial 0
def authenticated0 : St := authState connected0 0
def opened0 : St := openState authenticated0 0
def negotiated0 : St := proposeState opened0 0
def dispatched0 : St := dispatchState negotiated0 0
def connected2 : St := connectState dispatched0 2
def authenticated2 : St := authState connected2 2
def opened2 : St := openState authenticated2 4
def negotiated2 : St := proposeState opened2 4
def dispatched2 : St := dispatchState negotiated2 4
def connected3 : St := connectState dispatched2 3
def authenticated3 : St := authState connected3 3
def opened3 : St := openState authenticated3 6
def negotiated3 : St := proposeState opened3 6
def dispatched3 : St := dispatchState negotiated3 6
def connected4 : St := connectState dispatched3 4
def authenticated4 : St := authState connected4 4
def opened4 : St := openState authenticated4 8
def negotiated4 : St := proposeState opened4 8
def dispatched4 : St := dispatchState negotiated4 8
def connected5 : St := connectState dispatched4 5
def authenticated5 : St := authState connected5 5
def opened5 : St := openState authenticated5 10
def negotiated5 : St := proposeState opened5 10
def dispatched5 : St := dispatchState negotiated5 10

def sub0 : St := subscribeState dispatched5 0
def sub1 : St := subscribeState sub0 1
def sub2 : St := subscribeState sub1 2
def sub3 : St := subscribeState sub2 3
def sub4 : St := subscribeState sub3 4
def fanout0 : St := fanoutState sub4 0
def fanout1 : St := fanoutState fanout0 1
def fanout2 : St := fanoutState fanout1 2
def joined0 : St := { fanout2 with routing := { fanout2.routing with joined := fun t => if t = 0 then true else fanout2.routing.joined t, mesh := fun p t => if t = 0 then ((decide (2 = p) || (decide (1 = p) || decide (0 = p))) && decide (0 ≤ if p = 3 ∨ p = 4 then 10 else 1)) else fanout2.routing.mesh p t, meshSnapshot := fun p t => if t = 0 then scores else fanout2.routing.meshSnapshot p t, fanout := fun p t => if t = 0 then false else fanout2.routing.fanout p t } }
def arrival0 : St := receiveState joined0 0
def validated0 : St := acceptState arrival0 0
def committed0 : St := { core := { pipeline := { validated0.core.pipeline with delivered := put validated0.core.pipeline.delivered 0 true, inWindow := put validated0.core.pipeline.inWindow 0 true, seen := fun k => if k = 0 then true else validated0.core.pipeline.seen k, lastTask := 0, emitted := true }, cache := storedCache (validatedCache validated0.core.cache 0) 0 }, routing := { validated0.routing with valid := put validated0.routing.valid 0 true } }
def destinationOpened : St := openState committed0 5
def destinationReady : St := proposeState destinationOpened 5
def sentRemote0 : St := { (writeState (forwardState destinationReady 0) 5) with routing := { destinationReady.routing with sentRemote := fun x y => (decide (1 = x) && decide (0 = y)) || destinationReady.routing.sentRemote x y } }
def closed0 : St := closeState sentRemote0 0
def iwantApplied : St := { closed0 with core := { closed0.core with cache := { closed0.core.cache with replyEmitted := true, lastPeer := 1, lastId := 0, lastMessage := closed0.core.cache.cached 0, replies := put2 closed0.core.cache.replies 1 0 1 } } }
def replied0 : St := writeState iwantApplied 5
def referred0 : St := { replied0 with routing := { replied0.routing with pxCandidate := put replied0.routing.pxCandidate 0 true, pxSource := put replied0.routing.pxSource 0 1, pxSnapshot := put replied0.routing.pxSnapshot 0 scores } }
def replacementConnected : St := connectState referred0 1
def replacementAuthenticated : St := { (authState replacementConnected 1) with routing := { replacementConnected.routing with pxAuthenticated := put replacementConnected.routing.pxAuthenticated 0 true } }
def replacementOpened : St := openState replacementAuthenticated 2
def replacementNegotiated : St := proposeState replacementOpened 2
def replacementDispatched : St := dispatchState replacementNegotiated 2
def arrival1 : St := receiveState replacementDispatched 1
def rejected1 : St := rejectState arrival1 1
def expired0 : St := expireState rejected1
def localCommitted0 : St := { (recommitState expired0) with routing := { expired0.routing with valid := put expired0.routing.valid 2 true, localPublication := put expired0.routing.localPublication 2 true, publishedId := fun k => if k = 0 then true else expired0.routing.publishedId k } }
def published0 : St := publishState localCommitted0
def publicationExpired : St := expireState published0
def republished0 : St := publishState publicationExpired
def negative0 : St := { republished0 with routing := { republished0.routing with currentSnapshot := fun p => if p = 1 then -10 else if p = 0 then 0 else scores p, heartbeatClean := false } }
def pruned0 : St := { negative0 with routing := { negative0.routing with mesh := fun p t => if t = 0 then decide (p = 0 ∨ p = 2) else negative0.routing.mesh p t, pruned := fun p t => if t = 0 then decide (p = 1) else negative0.routing.pruned p t, backoff := fun p t => if t = 0 then decide (p = 1) else negative0.routing.backoff p t, heartbeatClean := true } }

theorem put_unused : True := .intro

theorem put_true {A : Type} [DecidableEq A] {f : A → Bool} {a : A} :
    put f a true = fun x => decide (a = x) || f x := by
  funext x; simp [put]

theorem put_false {A : Type} [DecidableEq A] {f : A → Bool} {a : A} :
    put f a false = fun x => !decide (a = x) && f x := by
  funext x; simp [put]


theorem default_fun {A B : Type} [Inhabited B] : (default : A → B) = fun _ => (default : B) := rfl

theorem default_bool : (default : Bool) = false := rfl
theorem default_nat : (default : Nat) = 0 := rfl
theorem rat_inhabited : (default : Rat) = 0 := rfl
theorem default_finP : (default : P) = 0 := rfl
theorem default_finS : (default : S) = 0 := rfl
theorem default_finI : (default : I) = 0 := rfl
theorem default_finW : (default : W) = 0 := rfl
theorem default_finT : (default : T) = 0 := rfl
theorem default_finID : (default : ID) = 0 := rfl
theorem default_protocol : (default : Protocol) = 0 := rfl


theorem bool_default_inst : instInhabitedBool.default = false := rfl


theorem rat_le_3_1 : ((-3 : Rat) ≤ (1 : Rat)) := by decide +kernel
theorem rat_le_3_10 : ((-3 : Rat) ≤ 10) := by decide +kernel
theorem rat_le_2_10 : ((-2 : Rat) ≤ 10) := by decide +kernel
theorem rat_le_2_1 : ((-2 : Rat) ≤ (1 : Rat)) := by decide +kernel
theorem rat_le_1_1 : ((-1 : Rat) ≤ (1 : Rat)) := by decide +kernel
theorem rat_le_1_10 : ((-1 : Rat) ≤ 10) := by decide +kernel
theorem rat_ge_0_1 : ((0 : Rat) ≤ (1 : Rat)) := by decide +kernel
theorem rat_ge_0_10 : ((0 : Rat) ≤ 10) := by decide +kernel
theorem rat_lt_0_1 : ((0 : Rat) < (1 : Rat)) := by decide +kernel
theorem rat_lt_0_10 : ((0 : Rat) < 10) := by decide +kernel
theorem rat_lt_1_5 : ((1 : Rat) < 5) := by decide +kernel
theorem rat_notle_0_neg10 : ¬ ((0 : Rat) ≤ (-10 : Rat)) := by decide +kernel

theorem mesh_factor (p : P) : (2 = p ∨ 1 = p ∨ 0 = p) →
    decide ((0 : Rat) ≤ if p = 3 ∨ p = 4 then 10 else 1) = true := by
  intro h
  rcases h with h | h | h
  · subst h; decide +kernel
  · subst h; decide +kernel
  · subst h; decide +kernel

theorem rat_eq_le_1_1 : ((1 : Rat) ≤ (1 : Rat)) := by decide +kernel

theorem knownPeersDedup : th.knownPeers.eraseDups = [0, 1, 2, 3, 4] := by rfl

macro "fixture" : tactic => `(tactic|
  simp [Network.system, Network.Gate, Network.pipelineAllowed, Network.routingAllowed, Network.maintenanceAllowed,
  Network.coreLabels, Network.routingLabels, Network.routingTheory, Network.Inbound, Network.Request,
  Network.OutboundStream, Network.requestPeer, Network.connected, Network.outboundPeer, Network.meshRoster, Network.candidateRoster,
  Core.system, Core.Gate, Core.pipelineIndependent, Core.cacheIndependent, Core.pipelineLabels, Core.cacheLabels,
  Core.cacheTheory, Core.CurrentTask, Runs.single_iff, Runs.nil_iff,
  Pipeline.relationalTransitionSystem, Cache.relationalTransitionSystem, Routing.relationalTransitionSystem,
  Pipeline.Init, Cache.Init, Routing.Init, Pipeline.Assumptions, Cache.Assumptions, Routing.Assumptions,
  Pipeline.Next, Cache.Next, Routing.Next, Pipeline.NextAct, Cache.NextAct, Routing.NextAct, nextSimp,
  IsSubStateOf.setIn, IsSubStateOf.getFrom, instIsSubStateOfRefl,
  Pipeline.State.ext_iff, Cache.State.ext_iff, Routing.State.ext_iff, funext_iff,
  th, input, checks, expected, owner, source, scores, put, put2, put_true, put_false, bool_default_inst, Inhabited.default, default_fun,
  default_bool, default_nat, rat_inhabited, default_finP, default_finS, default_finI, default_finW, default_finT,
  default_finID, default_protocol, Pipeline.instInhabitedStateFieldConcreteType, Cache.instInhabitedStateFieldConcreteType,
  Routing.instInhabitedStateFieldConcreteType, ProfileInputs.pipelineTheory,
  Handshake.acceptCertificate, Handshake.deprecatedFieldsAllowed, Handshake.localCertificate, AuthChecks.accept,
  DecodedRPC.wellFormed, lengthAdmissible, Envelope.strictNoSign, ScoreThresholds.classify, atLeastThreshold,
  Libp2p.acceptPX, aboveThreshold, Selection.DegreeParams.Valid,
  Pipeline.Verdict_EnumClass.accept, Pipeline.Verdict_EnumClass.ignore, Pipeline.instVerdict_EnumClassVerdict_IndT,
  withPipeline, connectState, authState, openState, proposeState, dispatchState, subscribeState, fanoutState,
  localGraftState, receiveState, acceptState, rejectState, validatedCache, storedCache, forwardState, writeState,
  mesh_factor, rat_le_3_1, rat_le_3_10, rat_le_2_10, rat_le_2_1, rat_le_1_1, rat_le_1_10, rat_eq_le_1_1, rat_ge_0_1,
  rat_ge_0_10, rat_lt_0_1, rat_lt_0_10, rat_lt_1_5, rat_notle_0_neg10,
  knownPeersDedup,
  closeState, expireState, recommitState, publishState, initial, plan, connected0, connected2, connected3, connected4, connected5, authenticated0, authenticated2, authenticated3, authenticated4, authenticated5, opened0, opened2, opened3, opened4, opened5, negotiated0, negotiated2, negotiated3, negotiated4, negotiated5, dispatched0, dispatched2, dispatched3, dispatched4, dispatched5, sub0, sub1, sub2, sub3, sub4, fanout0, fanout1, fanout2, joined0, arrival0, validated0, committed0, destinationOpened, destinationReady, sentRemote0, closed0, iwantApplied, replied0, referred0, replacementConnected, replacementAuthenticated, replacementOpened, replacementNegotiated, replacementDispatched, arrival1, rejected1, expired0, localCommitted0, published0, publicationExpired, republished0, negative0, pruned0]
  <;> (repeat' (first | constructor | decide +kernel | simp)))

theorem cfg_valid : th.thresholds.Valid ∧ th.degree.Valid := by
  constructor <;> constructor <;> decide +kernel

theorem reach_initial : sys.reachable th initial := by
  apply Veil.RelationalTransitionSystem.reachable.init
  · exact ⟨by fixture, by fixture, cfg_valid.1, by decide +kernel⟩
  · fixture

theorem step_connected0 : sys.tr th initial ((.pipeline (.connect 0))) connected0 := by
  fixture

theorem reach_connected0 : sys.reachable th connected0 :=
  .step _ _ reach_initial ⟨_, step_connected0⟩

theorem step_authenticated0 : sys.tr th connected0 (.pipeline (.authenticate 0)) authenticated0 := by
  fixture

theorem reach_authenticated0 : sys.reachable th authenticated0 :=
  .step _ _ reach_connected0 ⟨_, step_authenticated0⟩

theorem step_opened0 : sys.tr th authenticated0 (.pipeline (.openStream 0)) opened0 := by
  fixture

theorem reach_opened0 : sys.reachable th opened0 :=
  .step _ _ reach_authenticated0 ⟨_, step_opened0⟩

theorem step_negotiated0 : sys.tr th opened0 (.pipeline (.propose 0 0 true)) negotiated0 := by
  fixture

theorem reach_negotiated0 : sys.reachable th negotiated0 :=
  .step _ _ reach_opened0 ⟨_, step_negotiated0⟩

theorem step_dispatched0 : sys.tr th negotiated0 (.pipeline (.dispatch 0 false)) dispatched0 := by
  fixture

theorem reach_dispatched0 : sys.reachable th dispatched0 :=
  .step _ _ reach_negotiated0 ⟨_, step_dispatched0⟩

theorem step_connected2 : sys.tr th dispatched0 (.pipeline (.connect 2)) connected2 := by
  fixture

theorem reach_connected2 : sys.reachable th connected2 :=
  .step _ _ reach_dispatched0 ⟨_, step_connected2⟩

theorem step_authenticated2 : sys.tr th connected2 (.pipeline (.authenticate 2)) authenticated2 := by
  fixture

theorem reach_authenticated2 : sys.reachable th authenticated2 :=
  .step _ _ reach_connected2 ⟨_, step_authenticated2⟩

theorem step_opened2 : sys.tr th authenticated2 (.pipeline (.openStream 4)) opened2 := by
  fixture

theorem reach_opened2 : sys.reachable th opened2 :=
  .step _ _ reach_authenticated2 ⟨_, step_opened2⟩

theorem step_negotiated2 : sys.tr th opened2 (.pipeline (.propose 4 0 true)) negotiated2 := by
  fixture

theorem reach_negotiated2 : sys.reachable th negotiated2 :=
  .step _ _ reach_opened2 ⟨_, step_negotiated2⟩

theorem step_dispatched2 : sys.tr th negotiated2 (.pipeline (.dispatch 4 false)) dispatched2 := by
  fixture

theorem reach_dispatched2 : sys.reachable th dispatched2 :=
  .step _ _ reach_negotiated2 ⟨_, step_dispatched2⟩

theorem step_connected3 : sys.tr th dispatched2 (.pipeline (.connect 3)) connected3 := by
  fixture

theorem reach_connected3 : sys.reachable th connected3 :=
  .step _ _ reach_dispatched2 ⟨_, step_connected3⟩

theorem step_authenticated3 : sys.tr th connected3 (.pipeline (.authenticate 3)) authenticated3 := by
  fixture

theorem reach_authenticated3 : sys.reachable th authenticated3 :=
  .step _ _ reach_connected3 ⟨_, step_authenticated3⟩

theorem step_opened3 : sys.tr th authenticated3 (.pipeline (.openStream 6)) opened3 := by
  fixture

theorem reach_opened3 : sys.reachable th opened3 :=
  .step _ _ reach_authenticated3 ⟨_, step_opened3⟩

theorem step_negotiated3 : sys.tr th opened3 (.pipeline (.propose 6 0 true)) negotiated3 := by
  fixture

theorem reach_negotiated3 : sys.reachable th negotiated3 :=
  .step _ _ reach_opened3 ⟨_, step_negotiated3⟩

theorem step_dispatched3 : sys.tr th negotiated3 (.pipeline (.dispatch 6 false)) dispatched3 := by
  fixture

theorem reach_dispatched3 : sys.reachable th dispatched3 :=
  .step _ _ reach_negotiated3 ⟨_, step_dispatched3⟩

theorem step_connected4 : sys.tr th dispatched3 (.pipeline (.connect 4)) connected4 := by
  fixture

theorem reach_connected4 : sys.reachable th connected4 :=
  .step _ _ reach_dispatched3 ⟨_, step_connected4⟩

theorem step_authenticated4 : sys.tr th connected4 (.pipeline (.authenticate 4)) authenticated4 := by
  fixture

theorem reach_authenticated4 : sys.reachable th authenticated4 :=
  .step _ _ reach_connected4 ⟨_, step_authenticated4⟩

theorem step_opened4 : sys.tr th authenticated4 (.pipeline (.openStream 8)) opened4 := by
  fixture

theorem reach_opened4 : sys.reachable th opened4 :=
  .step _ _ reach_authenticated4 ⟨_, step_opened4⟩

theorem step_negotiated4 : sys.tr th opened4 (.pipeline (.propose 8 0 true)) negotiated4 := by
  fixture

theorem reach_negotiated4 : sys.reachable th negotiated4 :=
  .step _ _ reach_opened4 ⟨_, step_negotiated4⟩

theorem step_dispatched4 : sys.tr th negotiated4 (.pipeline (.dispatch 8 false)) dispatched4 := by
  fixture

theorem reach_dispatched4 : sys.reachable th dispatched4 :=
  .step _ _ reach_negotiated4 ⟨_, step_dispatched4⟩

theorem step_connected5 : sys.tr th dispatched4 (.pipeline (.connect 5)) connected5 := by
  fixture

theorem reach_connected5 : sys.reachable th connected5 :=
  .step _ _ reach_dispatched4 ⟨_, step_connected5⟩

theorem step_authenticated5 : sys.tr th connected5 (.pipeline (.authenticate 5)) authenticated5 := by
  fixture

theorem reach_authenticated5 : sys.reachable th authenticated5 :=
  .step _ _ reach_connected5 ⟨_, step_authenticated5⟩

theorem step_opened5 : sys.tr th authenticated5 (.pipeline (.openStream 10)) opened5 := by
  fixture

theorem reach_opened5 : sys.reachable th opened5 :=
  .step _ _ reach_authenticated5 ⟨_, step_opened5⟩

theorem step_negotiated5 : sys.tr th opened5 (.pipeline (.propose 10 0 true)) negotiated5 := by
  fixture

theorem reach_negotiated5 : sys.reachable th negotiated5 :=
  .step _ _ reach_opened5 ⟨_, step_negotiated5⟩

theorem step_dispatched5 : sys.tr th negotiated5 (.pipeline (.dispatch 10 false)) dispatched5 := by
  fixture

theorem reach_dispatched5 : sys.reachable th dispatched5 :=
  .step _ _ reach_negotiated5 ⟨_, step_dispatched5⟩

theorem step_sub0 : sys.tr th dispatched5 (.subscribe 0 0) sub0 := by
  fixture

theorem reach_sub0 : sys.reachable th sub0 :=
  .step _ _ reach_dispatched5 ⟨_, step_sub0⟩

theorem step_sub1 : sys.tr th sub0 (.subscribe 4 0) sub1 := by
  fixture

theorem reach_sub1 : sys.reachable th sub1 :=
  .step _ _ reach_sub0 ⟨_, step_sub1⟩

theorem step_sub2 : sys.tr th sub1 (.subscribe 6 0) sub2 := by
  fixture

theorem reach_sub2 : sys.reachable th sub2 :=
  .step _ _ reach_sub1 ⟨_, step_sub2⟩

theorem step_sub3 : sys.tr th sub2 (.subscribe 8 0) sub3 := by
  fixture

theorem reach_sub3 : sys.reachable th sub3 :=
  .step _ _ reach_sub2 ⟨_, step_sub3⟩

theorem step_sub4 : sys.tr th sub3 (.subscribe 10 0) sub4 := by
  fixture

theorem reach_sub4 : sys.reachable th sub4 :=
  .step _ _ reach_sub3 ⟨_, step_sub4⟩

theorem step_fanout0 : sys.tr th sub4 (.routing (.addFanout 0 0)) fanout0 := by
  fixture

theorem reach_fanout0 : sys.reachable th fanout0 :=
  .step _ _ reach_sub4 ⟨_, step_fanout0⟩

theorem step_fanout1 : sys.tr th fanout0 (.routing (.addFanout 1 0)) fanout1 := by
  fixture

theorem reach_fanout1 : sys.reachable th fanout1 :=
  .step _ _ reach_fanout0 ⟨_, step_fanout1⟩

theorem step_fanout2 : sys.tr th fanout1 (.routing (.addFanout 2 0)) fanout2 := by
  fixture

theorem reach_fanout2 : sys.reachable th fanout2 :=
  .step _ _ reach_fanout1 ⟨_, step_fanout2⟩

theorem step_joined0 : sys.tr th fanout2 (.routing (.join 0)) joined0 := by
  fixture

theorem reach_joined0 : sys.reachable th joined0 :=
  .step _ _ reach_fanout2 ⟨_, step_joined0⟩

theorem step_arrival0 : sys.tr th joined0 (.receive 0) arrival0 := by
  exact ⟨by fixture, Runs.single_iff.mpr ⟨by fixture, Runs.single_iff.mpr (by fixture), Runs.single_iff.mpr (by fixture)⟩, Runs.nil_iff.mpr rfl⟩

theorem reach_arrival0 : sys.reachable th arrival0 :=
  .step _ _ reach_joined0 ⟨_, step_arrival0⟩

theorem should_mark_arrival_without_caching :
    arrival0.core.cache.arrived 0 = true ∧
      arrival0.core.cache.cached = joined0.core.cache.cached ∧
      arrival0.core.cache.present = joined0.core.cache.present ∧
      arrival0.core.cache.seen = joined0.core.cache.seen := by
  have coreStep := Runs.single_iff.mp step_arrival0.2.1
  have cacheStep := Runs.single_iff.mp coreStep.2.2
  have seen := Cache.seen_effect P W ID T _ _ _ _ cacheStep
  change arrival0.core.cache.seen = joined0.core.cache.seen at seen
  refine ⟨?_, ?_, ?_, seen⟩ <;>
    simp only [Cache.relationalTransitionSystem, Cache.Next, Cache.NextAct, nextSimp,
      Cache.State.ext_iff, funext_iff] at cacheStep <;> grind

theorem should_preserve_publication_on_arrival :
    arrival0.routing.publishedId = joined0.routing.publishedId := by
  exact NetworkRoutingFacts.published_transaction P T W ID (P → Rat)
    _ _ _ _ step_arrival0.2.2

theorem step_validated0 : sys.tr th arrival0 (.pipeline (.finishValidation 0 .accept)) validated0 := by
  fixture

theorem reach_validated0 : sys.reachable th validated0 :=
  .step _ _ reach_arrival0 ⟨_, step_validated0⟩

theorem step_committed0 : sys.tr th validated0 (.commitRemote 0 true) committed0 := by
  refine ⟨by fixture, ?_, Runs.single_iff.mpr (by fixture)⟩
  apply Runs.single_iff.mpr
  refine ⟨by fixture, Runs.single_iff.mpr (by fixture), ?_⟩
  · apply Runs.cons (middle := validatedCache validated0.core.cache 0)
    · fixture
    · exact Runs.single_iff.mpr (by fixture)

theorem reach_committed0 : sys.reachable th committed0 :=
  .step _ _ reach_validated0 ⟨_, step_committed0⟩

theorem step_destinationOpened : sys.tr th committed0 (.pipeline (.openStream 5)) destinationOpened := by
  fixture

theorem reach_destinationOpened : sys.reachable th destinationOpened :=
  .step _ _ reach_committed0 ⟨_, step_destinationOpened⟩

theorem step_destinationReady : sys.tr th destinationOpened (.pipeline (.propose 5 0 true)) destinationReady := by
  fixture

theorem reach_destinationReady : sys.reachable th destinationReady :=
  .step _ _ reach_destinationOpened ⟨_, step_destinationReady⟩

theorem step_sentRemote0 : sys.tr th destinationReady (.sendRemote 0 1 5 false) sentRemote0 := by
  refine ⟨by fixture, ?_, Runs.single_iff.mpr (by fixture)⟩
  apply Runs.cons (middle := (forwardState destinationReady 0).core)
  · fixture
  · exact Runs.single_iff.mpr (by fixture)

theorem reach_sentRemote0 : sys.reachable th sentRemote0 :=
  .step _ _ reach_destinationReady ⟨_, step_sentRemote0⟩

theorem step_closed0 : sys.tr th sentRemote0 (.pipeline (.close 0)) closed0 := by
  fixture

theorem reach_closed0 : sys.reachable th closed0 :=
  .step _ _ reach_sentRemote0 ⟨_, step_closed0⟩

theorem step_replied0 : sys.tr th closed0 (.replyCached 4 0 5 false) replied0 := by
  refine ⟨by fixture, ?_, Runs.nil_iff.mpr rfl⟩
  apply Runs.cons (middle := iwantApplied.core)
  · fixture
  · exact Runs.single_iff.mpr (by fixture)

theorem reach_replied0 : sys.reachable th replied0 :=
  .step _ _ reach_closed0 ⟨_, step_replied0⟩

theorem step_referred0 : sys.tr th replied0 (.referral 4 0) referred0 := by
  exact ⟨by fixture, Runs.nil_iff.mpr rfl, Runs.single_iff.mpr (by fixture)⟩

theorem reach_referred0 : sys.reachable th referred0 :=
  .step _ _ reach_replied0 ⟨_, step_referred0⟩

theorem step_replacementConnected : sys.tr th referred0 (.pipeline (.connect 1)) replacementConnected := by
  fixture

theorem reach_replacementConnected : sys.reachable th replacementConnected :=
  .step _ _ reach_referred0 ⟨_, step_replacementConnected⟩

theorem step_replacementAuthenticated : sys.tr th replacementConnected (.authenticateReferral 1) replacementAuthenticated := by
  exact ⟨by fixture, Runs.single_iff.mpr (by fixture), Runs.single_iff.mpr (by fixture)⟩

theorem reach_replacementAuthenticated : sys.reachable th replacementAuthenticated :=
  .step _ _ reach_replacementConnected ⟨_, step_replacementAuthenticated⟩

theorem step_replacementOpened : sys.tr th replacementAuthenticated (.pipeline (.openStream 2)) replacementOpened := by
  fixture

theorem reach_replacementOpened : sys.reachable th replacementOpened :=
  .step _ _ reach_replacementAuthenticated ⟨_, step_replacementOpened⟩

theorem step_replacementNegotiated : sys.tr th replacementOpened (.pipeline (.propose 2 0 true)) replacementNegotiated := by
  fixture

theorem reach_replacementNegotiated : sys.reachable th replacementNegotiated :=
  .step _ _ reach_replacementOpened ⟨_, step_replacementNegotiated⟩

theorem step_replacementDispatched : sys.tr th replacementNegotiated (.pipeline (.dispatch 2 false)) replacementDispatched := by
  fixture

theorem reach_replacementDispatched : sys.reachable th replacementDispatched :=
  .step _ _ reach_replacementNegotiated ⟨_, step_replacementDispatched⟩

theorem should_not_receive_before_dispatch (next : St) :
    ¬ sys.tr th replacementAuthenticated (.receive 1) next := by
  rintro ⟨gate, _, _⟩
  have dispatched := gate.1.2.2.2.1
  have notDispatched : replacementAuthenticated.core.pipeline.dispatched 2 = false := by fixture
  exact Bool.noConfusion (notDispatched.symm.trans dispatched)

theorem step_arrival1 : sys.tr th replacementDispatched (.receive 1) arrival1 := by
  exact ⟨by fixture, Runs.single_iff.mpr ⟨by fixture, Runs.single_iff.mpr (by fixture), Runs.single_iff.mpr (by fixture)⟩, Runs.nil_iff.mpr rfl⟩

theorem reach_arrival1 : sys.reachable th arrival1 :=
  .step _ _ reach_replacementDispatched ⟨_, step_arrival1⟩

theorem step_rejected1 : sys.tr th arrival1 (.pipeline (.finishValidation 1 .reject)) rejected1 := by
  fixture

theorem reach_rejected1 : sys.reachable th rejected1 :=
  .step _ _ reach_arrival1 ⟨_, step_rejected1⟩

theorem step_expired0 : sys.tr th rejected1 (.expire 0) expired0 := by
  exact ⟨by fixture, Runs.single_iff.mpr ⟨by fixture, Runs.single_iff.mpr (by fixture), Runs.single_iff.mpr (by fixture)⟩, Runs.single_iff.mpr (by fixture)⟩

theorem reach_expired0 : sys.reachable th expired0 :=
  .step _ _ reach_rejected1 ⟨_, step_expired0⟩

theorem step_localCommitted0 : sys.tr th expired0 (.commitLocal 2) localCommitted0 := by
  refine ⟨by fixture, Runs.single_iff.mpr ⟨by fixture, Runs.single_iff.mpr (by fixture), ?_⟩, Runs.single_iff.mpr (by fixture)⟩
  apply Runs.cons (middle := validatedCache expired0.core.cache 2)
  · fixture
  · exact Runs.single_iff.mpr (by fixture)

theorem reach_localCommitted0 : sys.reachable th localCommitted0 :=
  .step _ _ reach_expired0 ⟨_, step_localCommitted0⟩

theorem step_published0 : sys.tr th localCommitted0 (.publish 2 1 5 false) published0 := by
  refine ⟨by fixture, ?_, Runs.single_iff.mpr (by fixture)⟩
  apply Runs.cons (middle := (recommitState localCommitted0).core)
  · refine ⟨by fixture, Runs.single_iff.mpr (by fixture), ?_⟩
    apply Runs.cons (middle := validatedCache localCommitted0.core.cache 2)
    · fixture
    · exact Runs.single_iff.mpr (by fixture)
  · exact Runs.single_iff.mpr (by fixture)

theorem reach_published0 : sys.reachable th published0 :=
  .step _ _ reach_localCommitted0 ⟨_, step_published0⟩

theorem step_publicationExpired : sys.tr th published0 (.expire 0) publicationExpired := by
  exact ⟨by fixture, Runs.single_iff.mpr ⟨by fixture, Runs.single_iff.mpr (by fixture), Runs.single_iff.mpr (by fixture)⟩, Runs.single_iff.mpr (by fixture)⟩

theorem reach_publicationExpired : sys.reachable th publicationExpired :=
  .step _ _ reach_published0 ⟨_, step_publicationExpired⟩

theorem step_republished0 : sys.tr th publicationExpired (.publish 2 1 5 false) republished0 := by
  refine ⟨by fixture, ?_, Runs.single_iff.mpr (by fixture)⟩
  apply Runs.cons (middle := (recommitState publicationExpired).core)
  · refine ⟨by fixture, Runs.single_iff.mpr (by fixture), ?_⟩
    apply Runs.cons (middle := validatedCache publicationExpired.core.cache 2)
    · fixture
    · exact Runs.single_iff.mpr (by fixture)
  · exact Runs.single_iff.mpr (by fixture)

theorem reach_republished0 : sys.reachable th republished0 :=
  .step _ _ reach_publicationExpired ⟨_, step_republished0⟩

theorem step_negative0 : sys.tr th republished0 (.refreshScores (fun p => if p = 1 then -10 else if p = 0 then 0 else scores p)) negative0 := by
  fixture

theorem reach_negative0 : sys.reachable th negative0 :=
  .step _ _ reach_republished0 ⟨_, step_negative0⟩

theorem step_pruned0 : sys.tr th negative0 (.routing .heartbeat) pruned0 := by
  fixture

theorem reach_pruned0 : sys.reachable th pruned0 :=
  .step _ _ reach_negative0 ⟨_, step_pruned0⟩


theorem composed_reach : sys.reachable th pruned0 := reach_pruned0

theorem composed_core_reachable :
    (Core.system S P I W W W ID Protocol V T).reachable th.core pruned0.core :=
  Network.core_reachable S P I W W W ID Protocol V T composed_reach

theorem composed_seen_alignment :
    pruned0.core.pipeline.seen = pruned0.core.cache.seen :=
  Core.seen_alignment S P I W W W ID Protocol V T composed_core_reachable

theorem composed_validation_binding :
    ∀ w, pruned0.routing.valid w = true →
      (Core.Authority S P I W W W ID Protocol V T) th.core pruned0.core w ∧
        pruned0.routing.localPublication w = th.core.isLocal w :=
  Network.validation_binding S P I W W W ID Protocol V T composed_reach

theorem composed_validation_gate :
    ∀ action ∈ Network.routingLabels S P I W W W ID Protocol V T th
        localCommitted0 published0.core (.publish 2 1 5 false),
      NetworkRoutingFacts.ValidationGate P T W ID (P → Rat)
        (Core.Authority S P I W W W ID Protocol V T th.core published0.core) th.core.isLocal action := by
  have step := step_published0
  exact Network.validation_gate S P I W W W ID Protocol V T th localCommitted0
    published0 (.publish 2 1 5 false) step

theorem should_not_remote_send_after_source_disconnect (next : St) :
    ¬ sys.tr th closed0 (.sendRemote 0 1 5 false) next := by
  rintro ⟨gate, _, _⟩
  have live := gate.1.1
  have zero : closed0.core.pipeline.live 0 = false := by fixture
  exact Bool.noConfusion (zero.symm.trans live)

theorem should_not_forward_rejected_task (next : St) :
    ¬ sys.tr th rejected1 (.sendRemote 1 1 5 false) next := by
  rintro ⟨_, coreRun, _⟩
  obtain ⟨_, firstStep, _⟩ := Runs.cons_iff.mp coreRun
  have fwd := Runs.single_iff.mp firstStep.2.1
  have notAccepted : rejected1.core.pipeline.accepted 1 = false := by fixture
  simp only [Pipeline.relationalTransitionSystem, Pipeline.Next, Pipeline.NextAct, nextSimp,
    notAccepted, Bool.false_eq_true, false_and] at fwd

theorem should_not_remote_forward_published_candidate (next : St) :
    ¬ sys.tr th localCommitted0 (.sendRemote 2 1 5 false) next := by
  rintro ⟨_, step⟩
  have routed := Runs.single_iff.mp step.2
  simp [Routing.relationalTransitionSystem, Routing.Next, Routing.NextAct, nextSimp,
    th, input, put, localCommitted0] at routed

open Lean in
run_cmd do
  let env ← getEnv
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  for (name, info) in env.constants.toList do
    if (`Libp2p.NetworkTests).isPrefixOf (privateToUserName name) then
      match info with
      | .thmInfo _ =>
        let axioms ← collectAxioms name
        let unexpected := axioms.filter (!allowed.contains ·)
        unless unexpected.isEmpty do
          throwError "nonstandard axioms in {name}: {unexpected}"
        checked := checked + 1
      | .axiomInfo _ => throwError "test axiom is forbidden: {name}"
      | _ => pure ()
  unless checked > 0 do
    throwError "no Network test theorems were audited"
  logInfo m!"Network test axiom audit passed: {checked} theorems"

#print axioms composed_reach
#print axioms composed_validation_binding
#print axioms should_not_remote_send_after_source_disconnect
#print axioms should_not_forward_rejected_task
#print axioms should_not_remote_forward_published_candidate

end Libp2p.NetworkTests
