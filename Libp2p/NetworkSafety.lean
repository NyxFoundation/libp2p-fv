module

public import Libp2p.NetworkRoutingFacts

public section
namespace Libp2p.Network
open Classical
open scoped Libp2p.Pipeline Libp2p.Cache Libp2p.Routing

variable (S P I W O C ID Protocol V T : Type)
variable [Inhabited S] [Inhabited P] [Inhabited I] [Inhabited W]
variable [Inhabited O] [Inhabited C] [Inhabited ID] [Inhabited Protocol]
variable [Inhabited V] [Inhabited T] [Pipeline.Verdict_EnumClass V]
local notation "CS" => Core.State S P I W O C ID Protocol V T
local notation "Th" => Theory S P I W O C ID Protocol T
local notation "St" => State S P I W O C ID Protocol V T
local notation "L" => Label S P I W O C ID Protocol V T
local notation "cSys" => Core.system S P I W O C ID Protocol V T
local notation "rSys" => Routing.relationalTransitionSystem P T W ID (P → Rat)
local notation "sys" => system S P I W O C ID Protocol V T
local notation "rt" => routingTheory S P I W O C ID Protocol T
local notation "Auth" => Core.Authority S P I W O C ID Protocol V T

 theorem core_reachable {th : Th} {st : St} (reachable : (sys).reachable th st) :
    (cSys).reachable th.core st.core := by
  exact Libp2p.reachable_projection sys cSys Theory.core State.core
    (fun _ h => h.1) (fun _ _ h => h.1) (fun _ _ _ _ h => ⟨_, h.2.1⟩) reachable

 theorem routing_reachable {th : Th} {st : St} (reachable : (sys).reachable th st) :
    (rSys).reachable (rt th) st.routing := by
  exact Libp2p.reachable_projection sys rSys rt State.routing
    (fun _ h => h.2.1) (fun _ _ h => h.2) (fun _ _ _ _ h => ⟨_, h.2.2⟩) reachable

 theorem core_authority_run (th : Th) (st next : CS) (labels)
    (run : Runs cSys th.core st labels next) (w : W) (authorized : Auth th.core st w) :
    Auth th.core next w := by
  exact run.preserve (fun state => Auth th.core state w)
    (fun s label n h step => Core.authority_persists S P I W O C ID Protocol V T
      th.core s n label step w h) authorized

 theorem validation_gate (th : Th) (st next : St) (label : L)
    (step : (sys).tr th st label next) :
    ∀ action ∈ routingLabels S P I W O C ID Protocol V T th st next.core label,
      NetworkRoutingFacts.ValidationGate P T W ID (P → Rat) (Auth th.core next.core)
        th.core.isLocal action := by
  have gate := step.1
  have run := step.2.1
  cases label with
  | commitRemote w deliver =>
    have coreStep := Runs.single_iff.mp run
    have remote := coreStep.1.1
    have accepted := coreStep.1.2.1
    have authorized := core_authority_run S P I W O C ID Protocol V T th _ _ _ run w
      (Or.inl ⟨remote, accepted⟩)
    simpa [routingLabels, NetworkRoutingFacts.ValidationGate] using And.intro authorized remote
  | commitLocal w =>
    have coreStep := Runs.single_iff.mp run
    have authorized := core_authority_run S P I W O C ID Protocol V T th _ _ _ run w
      (Or.inr coreStep.1)
    simpa [routingLabels, NetworkRoutingFacts.ValidationGate] using And.intro authorized coreStep.1.1
  | routing action =>
    cases action <;> simp_all [Gate, routingAllowed, routingLabels, NetworkRoutingFacts.ValidationGate]
  | oversubscribe t plan =>
    simp [routingLabels, NetworkRoutingFacts.ValidationGate]
  | opportunistic t median requested chosen =>
    simp [routingLabels, NetworkRoutingFacts.ValidationGate]
  | _ => simp [routingLabels, NetworkRoutingFacts.ValidationGate]

 theorem validation_binding {th : Th} {st : St} (reachable : (sys).reachable th st) :
    ∀ w, st.routing.valid w = true →
      Auth th.core st.core w ∧ st.routing.localPublication w = th.core.isLocal w := by
  induction reachable with
  | init st assumptions initial =>
    have h := initial.2
    simp only [Routing.relationalTransitionSystem, Routing.Init, nextSimp,
      IsSubStateOf.setIn, IsSubStateOf.getFrom, Routing.State.ext_iff, funext_iff] at h
    intro w valid
    grind
  | step st next previous edge ih =>
    obtain ⟨label, step⟩ := edge
    apply NetworkRoutingFacts.transaction_validation_bound P T W ID (P → Rat)
      (rt th) st.routing next.routing _ (Auth th.core next.core) th.core.isLocal step.2.2
    · exact validation_gate S P I W O C ID Protocol V T th st next label step
    · intro w valid
      exact ⟨core_authority_run S P I W O C ID Protocol V T th _ _ _ step.2.1 w (ih w valid).1,
        (ih w valid).2⟩

 theorem initial_snapshot {th : Th} {st : St} (initial : (sys).init th st) :
    st.routing.currentSnapshot = th.initialScores :=
  Routing.initial_snapshot_coherent P T W ID (P → Rat) (rt th) st.routing initial.2

 theorem threshold_correspondence (th : Th) (st : St) (p : P) :
    ((rt th).nonnegative st.routing.currentSnapshot p = true ↔ 0 ≤ st.routing.currentSnapshot p) ∧
    ((rt th).publishEligible st.routing.currentSnapshot p = true ↔
      th.thresholds.publish ≤ st.routing.currentSnapshot p) ∧
    ((rt th).pxEligible st.routing.currentSnapshot p = true ↔
      th.thresholds.acceptPX < st.routing.currentSnapshot p) := by
  have h := th.thresholds.classify_refines (st.routing.currentSnapshot p)
  exact ⟨h.1, h.2.2.1, h.2.2.2.2⟩

 theorem fixed_degree (th : Th) : (rt th).highDegree = th.degree.high := rfl

 theorem connection_allocation_gate (th : Th) (st next : St) (s : S)
    (step : (sys).tr th st (.pipeline (.connect s)) next) :
    s ∈ th.knownSessions ∧ th.core.input.expected s ∈ th.knownPeers := step.1

 theorem outbound_peer_iff (th : Th) (st : St) (p : P) :
    outboundPeer S P I W O C ID Protocol V T th st p = true ↔
      ∃ s ∈ th.knownSessions, st.core.pipeline.live s = true ∧
        st.core.pipeline.authenticated s = true ∧ th.core.input.expected s = p ∧ th.outbound s = true := by
  simp [outboundPeer, and_assoc]

 theorem inbound_identity {th : Th} {st : St} (reachable : (sys).reachable th st)
    (i : I) (current : Inbound S P I W O C ID Protocol V T th st i) :
    st.core.pipeline.identity (th.core.input.owner i) = requestPeer S P I W O C ID Protocol T th i ∧
    (th.core.input.checks (th.core.input.owner i)).accept = true := by
  have h := Pipeline.authentication_contract S P I W O C ID Protocol V th.core.input _
    (Core.pipeline_reachable S P I W O C ID Protocol V T
      (core_reachable S P I W O C ID Protocol V T reachable)) _ current.2.1
  exact ⟨h.2.2.2, h.1⟩

 theorem ignored_control_frame (th : Th) (st next : St) (i : I) (k : ID)
    (step : (sys).tr th st (.ignoredIdontwant i k) next) : next = st := by
  have hc := Runs.nil_iff.mp step.2.1
  have hr := Routing.ignored_idontwant_no_effect P T W ID (P → Rat) (rt th) _ _ _ k
    (Runs.single_iff.mp step.2.2)
  cases st; cases next
  simp_all

 theorem refresh_scores (th : Th) (st next : St) (scores : P → Rat)
    (step : (sys).tr th st (.refreshScores scores) next) :
    next.core = st.core ∧ next.routing.currentSnapshot = scores ∧ next.routing.mesh = st.routing.mesh := by
  have h := Routing.refresh_preserves_mesh P T W ID (P → Rat) (rt th) _ _ scores
    (Runs.single_iff.mp step.2.2)
  exact ⟨Runs.nil_iff.mp step.2.1, h.2.1, h.1⟩

 theorem output_fields (th : Th) (st : St) (label : L) (out : PayloadOutput P I W O C ID T)
    (emitted : output S P I W O C ID Protocol V T th st label = some out) :
    out.payload = th.core.input.payload out.candidate ∧
    out.context = th.core.input.scope out.candidate ∧ out.key = th.core.input.key out.candidate ∧
    out.topic = th.core.topic out.candidate ∧ out.envelope = ⟨none, none, none, none⟩ ∧
    out.envelope.strictNoSign = true := by
  cases label <;> simp_all [output, payloadOutput, Envelope.strictNoSign] <;>
    subst out <;> simp

 theorem remote_send_correspondence {th : Th} {st : St} (reachable : (sys).reachable th st)
    (next : St) (w : W) (p : P) (i : I) (ext : Bool)
    (step : (sys).tr th st (.sendRemote w p i ext) next) :
    th.core.isLocal w = false ∧ st.core.pipeline.accepted w = true ∧
    Core.CurrentTask S P I W O C ID Protocol V T th.core st.core w ∧
    Inbound S P I W O C ID Protocol V T th st (th.core.input.source w) ∧
    OutboundStream S P I W O C ID Protocol V T th st p i ∧
    next.routing.sentRemote p w = true ∧ next.core.pipeline.forwarded w = true ∧
    next.core.pipeline.usedPayload w = th.core.input.payload w ∧
    next.core.pipeline.usedContext w = th.core.input.scope w := by
  obtain ⟨middle, forward, rest⟩ := Runs.cons_iff.mp step.2.1
  have wrote := Runs.single_iff.mp (Runs.single_iff.mp rest).2.1
  have forwarded := Runs.single_iff.mp forward.2.1
  have routed := Runs.single_iff.mp step.2.2
  simp only [Routing.relationalTransitionSystem, Routing.Next, Routing.NextAct, nextSimp,
    Routing.State.ext_iff, funext_iff] at routed
  have valid : st.routing.valid w = true := by grind
  have binding := validation_binding S P I W O C ID Protocol V T reachable w valid
  simp only [Pipeline.relationalTransitionSystem, Pipeline.Next, Pipeline.NextAct, nextSimp,
    Pipeline.State.ext_iff, funext_iff, ProfileInputs.pipelineTheory] at forwarded wrote
  have input := step.1
  change Inbound S P I W O C ID Protocol V T th st (th.core.input.source w) ∧
    OutboundStream S P I W O C ID Protocol V T th st p i at input
  simp only [Core.CurrentTask]
  grind

 theorem cached_reply_correspondence {th : Th} {st : St} (reachable : (sys).reachable th st)
    (next : St) (req : I) (k : ID) (i : I) (ext : Bool)
    (step : (sys).tr th st (.replyCached req k i ext) next) :
    Request S P I W O C ID Protocol V T th st req ∧
    OutboundStream S P I W O C ID Protocol V T th st (requestPeer S P I W O C ID Protocol T th req) i ∧
    next.core.cache.replyEmitted = true ∧
    next.core.cache.lastPeer = requestPeer S P I W O C ID Protocol T th req ∧
    next.core.cache.lastId = k ∧ next.core.cache.lastMessage = st.core.cache.cached k ∧
    next.core.cache.cached k = st.core.cache.cached k ∧
    th.core.input.key (st.core.cache.cached k) = k ∧ Auth th.core st.core (st.core.cache.cached k) := by
  obtain ⟨middle, reply, rest⟩ := Runs.cons_iff.mp step.2.1
  have replied := Runs.single_iff.mp reply.2.2
  have cacheFrame := Runs.nil_iff.mp (Runs.single_iff.mp rest).2.2
  simp only [Cache.relationalTransitionSystem, Cache.Next, Cache.NextAct, nextSimp,
    Cache.State.ext_iff, funext_iff] at replied
  have present : st.core.cache.present k = true := by grind
  have authority := Core.cached_authority S P I W O C ID Protocol V T
    (core_reachable S P I W O C ID Protocol V T reachable) k present
  refine ⟨step.1.1, step.1.2, ?_⟩
  rw [cacheFrame]
  grind

 theorem publish_current_threshold (th : Th) (st next : St) (w : W) (p : P) (i : I) (ext : Bool)
    (step : (sys).tr th st (.publish w p i ext) next) :
    th.core.isLocal w = true ∧ th.core.localAccepted w = true ∧
    (th.explicitPeer p = true ∨ th.thresholds.publish ≤ st.routing.currentSnapshot p) ∧
    next.routing.publishSnapshot p w = st.routing.currentSnapshot ∧
    next.routing.publishedId (th.core.input.key w) = true := by
  obtain ⟨middle, committed, rest⟩ := Runs.cons_iff.mp step.2.1
  have h := Routing.publish_uses_current_score P T W ID (P → Rat) (rt th) _ _ p _ w
    (Runs.single_iff.mp step.2.2)
  have correspondence := (threshold_correspondence S P I W O C ID Protocol V T th st p).2.1
  exact ⟨committed.1.1, committed.1.2, h.1.imp id correspondence.mp, h.2⟩

 theorem referral_current_threshold (th : Th) (st next : St) (i : I) (p : P)
    (step : (sys).tr th st (.referral i p) next) :
    Request S P I W O C ID Protocol V T th st i ∧
    th.thresholds.acceptPX < st.routing.currentSnapshot (requestPeer S P I W O C ID Protocol T th i) ∧
    next.routing.pxSource p = requestPeer S P I W O C ID Protocol T th i := by
  have h := Routing.px_uses_current_score P T W ID (P → Rat) (rt th) _ _ _ p
    (Runs.single_iff.mp step.2.2)
  exact ⟨step.1, (threshold_correspondence S P I W O C ID Protocol V T th st _).2.2.mp h.1, h.2.1⟩

 theorem referral_authentication_bound {th : Th} {st : St} (reachable : (sys).reachable th st)
    (next : St) (s : S) (step : (sys).tr th st (.authenticateReferral s) next) :
    next.core.pipeline.authenticated s = true ∧
    next.core.pipeline.identity s = th.core.input.expected s ∧
    (th.core.input.checks s).accept = true ∧
    Handshake.deprecatedFieldsAllowed (th.core.input.deprecatedPolicy s) (th.core.input.certificate s) = true ∧
    next.routing.pxAuthenticated (th.core.input.expected s) = true := by
  have routed := Runs.single_iff.mp step.2.2
  simp only [Routing.relationalTransitionSystem, Routing.Next, Routing.NextAct, nextSimp,
    Routing.State.ext_iff, funext_iff] at routed
  have authenticated : next.core.pipeline.authenticated s = true := by grind
  have h := Pipeline.authentication_contract S P I W O C ID Protocol V th.core.input _
    (Core.pipeline_reachable S P I W O C ID Protocol V T
      (core_reachable S P I W O C ID Protocol V T (.step _ _ reachable ⟨_, step⟩))) s authenticated
  exact ⟨authenticated, h.2.2.2, h.1, h.2.1, by grind⟩

 theorem graft_connection_role (th : Th) (st next : St) (i : I) (t : T)
    (step : (sys).tr th st (.graft i t) next)
    (absent : st.routing.mesh (requestPeer S P I W O C ID Protocol T th i) t = false)
    (present : next.routing.mesh (requestPeer S P I W O C ID Protocol T th i) t = true) :
    (meshRoster S P I W O C ID Protocol V T th st t).length < th.degree.high ∨
      th.outbound (th.core.input.owner i) = true := by
  exact (Routing.graft_new_member_gate P T W ID (P → Rat) (rt th) _ _ _ t _ absent present
    (Runs.single_iff.mp step.2.2)).2.2.2.2

end Libp2p.Network
