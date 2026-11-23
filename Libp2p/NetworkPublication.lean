module

public import Libp2p.NetworkSafety

@[expose] public section
namespace Libp2p.Network
open Classical

 theorem fold_frame {A B : Type} (items : List A) (value : B) :
    items.foldl (fun v _ => v) value = value := by
  induction items <;> simp_all

variable (S P I W O C ID Protocol V T : Type)
variable [Inhabited S] [Inhabited P] [Inhabited I] [Inhabited W]
variable [Inhabited O] [Inhabited C] [Inhabited ID] [Inhabited Protocol]
variable [Inhabited V] [Inhabited T] [Pipeline.Verdict_EnumClass V]
local notation "CS" => Core.State S P I W O C ID Protocol V T
local notation "CL" => Core.Label S P I W O C ID Protocol V T
local notation "Th" => Theory S P I W O C ID Protocol T
local notation "St" => State S P I W O C ID Protocol V T
local notation "L" => Label S P I W O C ID Protocol V T
local notation "cSys" => Core.system S P I W O C ID Protocol V T
local notation "sys" => system S P I W O C ID Protocol V T
local notation "rt" => routingTheory S P I W O C ID Protocol T

noncomputable def coreSeenEffect (th : Th) (seen : ID → Bool) : CL → ID → Bool
  | .pipeline action => Pipeline.seenEffect S P I W O C ID Protocol V th.core.input.pipelineTheory seen action
  | .commitRemote w _ | .commitLocal w => fun k => if k = th.core.input.key w then true else seen k
  | .expire id => fun k => if k = id then false else seen k
  | _ => seen

 theorem core_seen_effect (th : Th) (st next : CS) (label : CL)
    (step : (cSys).tr th.core st label next) :
    next.pipeline.seen = coreSeenEffect S P I W O C ID Protocol V T th st.pipeline.seen label := by
  rw [Pipeline.seen_transaction S P I W O C ID Protocol V _ _ _ _ step.2.1]
  cases label with
  | commitRemote w deliver => cases deliver <;>
      simp [Core.pipelineLabels, coreSeenEffect, Pipeline.seenEffect, ProfileInputs.pipelineTheory]
  | _ => simp [Core.pipelineLabels, coreSeenEffect, Pipeline.seenEffect]

 theorem core_seen_transaction (th : Th) (st next : CS) (labels : List CL)
    (run : Runs cSys th.core st labels next) :
    next.pipeline.seen = labels.foldl (coreSeenEffect S P I W O C ID Protocol V T th) st.pipeline.seen := by
  induction run with
  | nil => rfl
  | cons step rest ih =>
    simpa only [List.foldl_cons, core_seen_effect S P I W O C ID Protocol V T _ _ _ _ step] using ih

 theorem publication_seen_step (th : Th) (st next : St) (label : L)
    (step : (sys).tr th st label next)
    (bound : ∀ k, st.routing.publishedId k = true → st.core.pipeline.seen k = true) :
    ∀ k, next.routing.publishedId k = true → next.core.pipeline.seen k = true := by
  rw [core_seen_transaction S P I W O C ID Protocol V T th _ _ _ step.2.1,
    NetworkRoutingFacts.published_transaction P T W ID (P → Rat) (rt th) _ _ _ step.2.2]
  have gate := step.1
  cases label with
  | pipeline action => cases action <;>
      simp_all [Gate, pipelineAllowed, coreLabels, routingLabels, coreSeenEffect,
        Pipeline.seenEffect, NetworkRoutingFacts.publishedEffect]
  | routing action => cases action <;>
      simp_all [Gate, routingAllowed, coreLabels, routingLabels, coreSeenEffect,
        NetworkRoutingFacts.publishedEffect]
  | _ =>
      simp only [coreLabels, routingLabels, List.foldl_cons, List.foldl_nil, coreSeenEffect,
        Pipeline.seenEffect, NetworkRoutingFacts.publishedEffect, routingTheory, List.foldl_map, fold_frame]
      all_goals grind

 theorem publication_seen_pipeline {th : Th} {st : St} (reachable : (sys).reachable th st) :
    ∀ k, st.routing.publishedId k = true → st.core.pipeline.seen k = true := by
  induction reachable with
  | init st assumptions initial =>
    have h := initial.2
    simp only [Routing.relationalTransitionSystem, Routing.Init, nextSimp,
      IsSubStateOf.setIn, IsSubStateOf.getFrom, Routing.State.ext_iff, funext_iff] at h
    intro k published
    grind
  | step st next previous edge ih =>
    obtain ⟨label, step⟩ := edge
    exact publication_seen_step S P I W O C ID Protocol V T th st next label step ih

 theorem publication_seen {th : Th} {st : St} (reachable : (sys).reachable th st) (k : ID)
    (published : st.routing.publishedId k = true) :
    st.core.pipeline.seen k = true ∧ st.core.cache.seen k = true := by
  have h := publication_seen_pipeline S P I W O C ID Protocol V T reachable k published
  have alignment := Core.seen_alignment S P I W O C ID Protocol V T
    (core_reachable S P I W O C ID Protocol V T reachable)
  exact ⟨h, alignment ▸ h⟩

 theorem publish_remembers_shared_id {th : Th} {st : St} (reachable : (sys).reachable th st)
    (next : St) (w : W) (p : P) (i : I) (ext : Bool)
    (step : (sys).tr th st (.publish w p i ext) next) :
    next.core.pipeline.seen (th.core.input.key w) = true ∧
    next.core.cache.seen (th.core.input.key w) = true ∧
    next.routing.publishedId (th.core.input.key w) = true := by
  have published := (publish_current_threshold S P I W O C ID Protocol V T th st next w p i ext step).2.2.2.2
  have h := publication_seen S P I W O C ID Protocol V T (.step _ _ reachable ⟨_, step⟩) _ published
  exact ⟨h.1, h.2, published⟩

 theorem expiry_synchronized (th : Th) (st next : St) (k : ID)
    (step : (sys).tr th st (.expire k) next) :
    next.core.pipeline.seen k = false ∧ next.core.cache.seen k = false ∧ next.routing.publishedId k = false := by
  have coreStep := Runs.single_iff.mp step.2.1
  have pipelineSeen := core_seen_effect S P I W O C ID Protocol V T th _ _ (.expire k) coreStep
  have cacheSeen := Cache.seen_transaction P W ID T _ _ _ _ coreStep.2.2
  have published := Routing.publication_expiry_clears_id P T W ID (P → Rat) (rt th) _ _ k
    (Runs.single_iff.mp step.2.2)
  refine ⟨?_, ?_, published⟩
  · rw [pipelineSeen]
    simp [coreSeenEffect]
  · rw [cacheSeen]
    simp [Core.cacheLabels, Cache.seenEffect]

 theorem published_collision_blocks_remote (th : Th) (st : St) (w localTask : W) (p : P)
    (i : I) (ext : Bool) (sameId : th.core.input.key localTask = th.core.input.key w)
    (published : st.routing.publishedId (th.core.input.key localTask) = true) :
    ¬ ∃ next, (sys).tr th st (.sendRemote w p i ext) next := by
  rintro ⟨next, step⟩
  exact Routing.local_echo_blocks_colliding_candidate P T W ID (P → Rat) (rt th) st.routing p
    (th.core.topic w) localTask w sameId published ⟨next.routing, Runs.single_iff.mp step.2.2⟩

end Libp2p.Network
