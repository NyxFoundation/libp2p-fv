import Libp2p.CoreSafety

namespace Libp2p.CoreTests
open scoped Libp2p.Pipeline Libp2p.Cache

abbrev S := Fin 3
abbrev P := Fin 2
abbrev W := Fin 3
abbrev ID := Fin 1
abbrev Protocol := Fin 2
abbrev T := Fin 1
abbrev V := Pipeline.Verdict_IndT
abbrev PS := Pipeline.State (Pipeline.FieldAbstractType S P S W W W ID Protocol V)
abbrev CS := Cache.State (Cache.FieldAbstractType P W ID T)
abbrev St := Core.State S P S W W W ID Protocol V T

private def checks : AuthChecks :=
  ⟨true, true, true, true, true, true, true, true, true, true, true⟩
private def emptyEnvelope : Envelope := ⟨none, none, none, none⟩
private def expected (s : S) : P := if s = 2 then 1 else 0

def input : ProfileInputs S P S W W W ID Protocol where
  expected := expected
  certificatePeer := expected
  checks := fun _ => checks
  certificate := fun _ => Handshake.localCertificate []
  deprecatedPolicy := fun _ => .reject
  supportedProtocol := 0
  owner := id
  inbound := fun s => decide (s ≠ 2)
  supportsExtensions := fun _ => true
  source := id
  payload := id
  scope := id
  key := fun _ => 0
  decoded := fun _ => ⟨1, 1, true, true, true, emptyEnvelope⟩

def th : Core.Theory S P S W W W ID Protocol T where
  input := input
  topic := fun _ => 0
  isLocal := fun w => decide (w = 2)
  localAccepted := fun w => decide (w = 2)
  historyLength := 2
  gossipLength := 1
  retransmissionLimit := 1
  followupTicks := 1

noncomputable abbrev sys := Core.system S P S W W W ID Protocol V T

private def zeroOnly {n : Nat} : Fin (n + 1) → Bool := fun n => decide (n = 0)

def p0 : PS := { (default : PS) with identity := expected, usedPayload := id, usedContext := id }
def c0 : CS := default
def p1 : PS := { p0 with allocated := zeroOnly, live := zeroOnly }
def p2 : PS := { p1 with authenticated := zeroOnly }
def p3 : PS := { p2 with opened := zeroOnly }
def p4 : PS := { p3 with negotiated := zeroOnly, proposalComplete := zeroOnly }
def p5 : PS := { p4 with dispatched := zeroOnly }
def p6 : PS := { p5 with submitted := zeroOnly, pending := zeroOnly }
def cArrival : CS := { c0 with arrived := fun _ => true }
def p7 : PS := { p6 with pending := fun _ => false, accepted := zeroOnly }
def p8 : PS :=
  { p7 with
    delivered := zeroOnly
    inWindow := zeroOnly
    seen := fun _ => true
    emitted := true }
def cValidated : CS := { cArrival with accepted := zeroOnly }
def cStored : CS := { cValidated with present := fun _ => true, seen := fun _ => true }
def cReplied : CS := { cStored with replyEmitted := true, replies := fun p _ => if p = 0 then 1 else 0 }
def pClosed : PS := { p8 with live := fun _ => false, emitted := false }
def pExpired : PS := { pClosed with seen := fun _ => false, inWindow := fun _ => false }
def cExpired : CS := { cReplied with seen := fun _ => false, replyEmitted := false }

def p9 : PS := { pExpired with allocated := fun s => decide (s ≠ 2), live := fun s => decide (s = 1) }
def p10 : PS := { p9 with authenticated := fun s => decide (s ≠ 2) }
def p11 : PS := { p10 with opened := fun i => decide (i ≠ 2) }
def p12 : PS :=
  { p11 with negotiated := fun i => decide (i ≠ 2), proposalComplete := fun i => decide (i ≠ 2) }
def p13 : PS := { p12 with dispatched := fun i => decide (i ≠ 2) }
def p14 : PS :=
  { p13 with submitted := fun w => decide (w ≠ 2), pending := fun w => decide (w = 1) }
def p15 : PS := { p14 with pending := fun _ => false, rejected := fun w => decide (w = 1) }

macro "fixture" : tactic => `(tactic|
  simp [Core.system, Core.Gate, Core.pipelineIndependent, Core.cacheIndependent,
    Core.pipelineLabels, Core.cacheLabels, Core.cacheTheory, Core.CurrentTask,
    Runs.single_iff, Runs.nil_iff, Pipeline.relationalTransitionSystem, Cache.relationalTransitionSystem,
    Pipeline.Init, Cache.Init, Pipeline.Assumptions, Cache.Assumptions,
    Pipeline.Next, Cache.Next, Pipeline.NextAct, Cache.NextAct, nextSimp,
    IsSubStateOf.setIn, IsSubStateOf.getFrom, instIsSubStateOfRefl,
    Pipeline.State.ext_iff, Cache.State.ext_iff, funext_iff,
    th, input, checks, expected, emptyEnvelope, ProfileInputs.pipelineTheory,
    Handshake.acceptCertificate, Handshake.deprecatedFieldsAllowed, Handshake.localCertificate,
    AuthChecks.accept, DecodedRPC.wellFormed, lengthAdmissible, Envelope.strictNoSign,
    p0, p1, p2, p3, p4, p5, p6, p7, p8, pClosed, pExpired,
    p9, p10, p11, p12, p13, p14, p15,
    c0, cArrival, cValidated, cStored, cReplied, cExpired, zeroOnly,
    Pipeline.Verdict_EnumClass.accept, Pipeline.Verdict_EnumClass.ignore,
    Pipeline.instVerdict_EnumClassVerdict_IndT] <;> decide +kernel)

theorem accepted_trace : sys.reachable th ⟨p7, cArrival⟩ := by
  have h0 : sys.reachable th ⟨p0, c0⟩ := .init _ (by fixture) (by fixture)
  have h1 : sys.reachable th ⟨p1, c0⟩ := .step _ _ h0 ⟨.pipeline (.connect 0), by fixture⟩
  have h2 : sys.reachable th ⟨p2, c0⟩ := .step _ _ h1 ⟨.pipeline (.authenticate 0), by fixture⟩
  have h3 : sys.reachable th ⟨p3, c0⟩ := .step _ _ h2 ⟨.pipeline (.openStream 0), by fixture⟩
  have h4 : sys.reachable th ⟨p4, c0⟩ := .step _ _ h3 ⟨.pipeline (.propose 0 0 true), by fixture⟩
  have h5 : sys.reachable th ⟨p5, c0⟩ := .step _ _ h4 ⟨.pipeline (.dispatch 0 false), by fixture⟩
  have h6 : sys.reachable th ⟨p6, cArrival⟩ := .step _ _ h5 ⟨.receive 0, by fixture⟩
  exact .step _ _ h6 ⟨.pipeline (.finishValidation 0 .accept), by fixture⟩

theorem delivered_trace : sys.reachable th ⟨p8, cStored⟩ := by
  apply Veil.RelationalTransitionSystem.reachable.step _ _ accepted_trace
  refine ⟨.commitRemote 0 true, ?_⟩
  refine ⟨by fixture, ?_, ?_⟩
  · fixture
  · apply Runs.cons (middle := cValidated)
    · fixture
    · apply Runs.cons (middle := cStored)
      · fixture
      · exact .nil _

theorem replied_trace : sys.reachable th ⟨p8, cReplied⟩ :=
  .step _ _ delivered_trace ⟨.cache (.iwant 0 0), by fixture⟩

theorem closed_trace : sys.reachable th ⟨pClosed, cReplied⟩ :=
  .step _ _ replied_trace ⟨.pipeline (.close 0), by fixture⟩

theorem expired_trace : sys.reachable th ⟨pExpired, cExpired⟩ :=
  .step _ _ closed_trace ⟨.expire 0, by fixture⟩

theorem reconnected_collision_trace : sys.reachable th ⟨p15, cExpired⟩ := by
  have h9 : sys.reachable th ⟨p9, cExpired⟩ :=
    .step _ _ expired_trace ⟨.pipeline (.connect 1), by fixture⟩
  have h10 : sys.reachable th ⟨p10, cExpired⟩ :=
    .step _ _ h9 ⟨.pipeline (.authenticate 1), by fixture⟩
  have h11 : sys.reachable th ⟨p11, cExpired⟩ :=
    .step _ _ h10 ⟨.pipeline (.openStream 1), by fixture⟩
  have h12 : sys.reachable th ⟨p12, cExpired⟩ :=
    .step _ _ h11 ⟨.pipeline (.propose 1 0 true), by fixture⟩
  have h13 : sys.reachable th ⟨p13, cExpired⟩ :=
    .step _ _ h12 ⟨.pipeline (.dispatch 1 false), by fixture⟩
  have h14 : sys.reachable th ⟨p14, cExpired⟩ := .step _ _ h13 ⟨.receive 1, by fixture⟩
  exact .step _ _ h14 ⟨.pipeline (.finishValidation 1 .reject), by fixture⟩

theorem should_deliver_and_reply_after_the_same_task_passes_validation :
    p8.delivered 0 = true ∧ cReplied.replyEmitted = true ∧
    cReplied.cached 0 = 0 ∧ p8.seen = cReplied.seen := ⟨rfl, rfl, rfl, rfl⟩

theorem should_not_commit_after_close_even_when_seen_has_expired (next : St) :
    ¬ sys.tr th ⟨pExpired, cExpired⟩ (.commitRemote 0 false) next := by
  intro step
  have live := step.1.2.2.1.1
  change false = true at live
  contradiction

theorem should_record_distinct_candidates_with_the_same_lookup_id :
    input.key 0 = input.key 1 ∧ input.payload 0 ≠ input.payload 1 ∧
    input.scope 0 ≠ input.scope 1 ∧
    Core.CurrentTask S P S W W W ID Protocol V T th ⟨p15, cExpired⟩ 1 := by
  exact ⟨rfl, by decide +kernel, by decide +kernel, rfl, rfl, rfl⟩

theorem should_not_revive_old_callback_after_same_peer_reconnects (next : St) :
    ¬ sys.tr th ⟨p15, cExpired⟩ (.commitRemote 0 false) next := by
  intro step
  have live := step.1.2.2.1.1
  change false = true at live
  contradiction

theorem should_not_inherit_acceptance_from_an_id_collision (next : St) :
    ¬ sys.tr th ⟨p15, cExpired⟩ (.commitRemote 1 false) next := by
  intro step
  have accepted := step.1.2.1
  change false = true at accepted
  contradiction

theorem should_reject_repeated_iwant_at_the_retransmission_limit (next : St) :
    ¬ sys.tr th ⟨p8, cReplied⟩ (.cache (.iwant 0 0)) next := by
  intro step
  have run := (Runs.single_iff.mp step.2.2)
  simp [Cache.relationalTransitionSystem, Cache.Next, Cache.NextAct, nextSimp,
    Core.cacheTheory, th, cReplied, IsSubStateOf.getFrom, instIsSubStateOfRefl] at run

#print axioms accepted_trace
#print axioms delivered_trace
#print axioms replied_trace
#print axioms expired_trace
#print axioms reconnected_collision_trace

end Libp2p.CoreTests
