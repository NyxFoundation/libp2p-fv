module

public import Libp2p.Core
public import Libp2p.CacheFacts

public section
namespace Libp2p.Core

open Classical
open scoped Libp2p.Pipeline Libp2p.Cache

variable (S P I W O C ID Protocol V T : Type)
variable [Inhabited S] [Inhabited P] [Inhabited I] [Inhabited W]
variable [Inhabited O] [Inhabited C] [Inhabited ID] [Inhabited Protocol]
variable [Inhabited V] [Inhabited T] [Pipeline.Verdict_EnumClass V]

local notation "PS" => Pipeline.State (Pipeline.FieldAbstractType S P I W O C ID Protocol V)
local notation "CS" => Cache.State (Cache.FieldAbstractType P W ID T)
local notation "Th" => Theory S P I W O C ID Protocol T
local notation "St" => State S P I W O C ID Protocol V T
local notation "L" => Label S P I W O C ID Protocol V T
local notation "pSys" => Pipeline.relationalTransitionSystem S P I W O C ID Protocol V
local notation "cSys" => Cache.relationalTransitionSystem P W ID T
local notation "sys" => system S P I W O C ID Protocol V T

 theorem pipeline_reachable {th : Th} {st : St} (reachable : (sys).reachable th st) :
    (pSys).reachable th.input.pipelineTheory st.pipeline := by
  exact Libp2p.reachable_projection sys pSys (fun th => th.input.pipelineTheory)
    State.pipeline (fun _ h => h.1) (fun _ _ h => h.1)
    (fun _ _ _ _ h => ⟨_, h.2.1⟩) reachable

 theorem cache_reachable {th : Th} {st : St} (reachable : (sys).reachable th st) :
    (cSys).reachable (cacheTheory S P I W O C ID Protocol T th) st.cache := by
  exact Libp2p.reachable_projection sys cSys (cacheTheory S P I W O C ID Protocol T)
    State.cache (fun _ h => h.2) (fun _ _ h => h.2)
    (fun _ _ _ _ h => ⟨_, h.2.2⟩) reachable

 theorem authority_persists (th : Th) (st next : St) (label : L)
    (step : (sys).tr th st label next) (w : W)
    (authorized : Authority S P I W O C ID Protocol V T th st w) :
    Authority S P I W O C ID Protocol V T th next w := by
  rcases authorized with ⟨remote, accepted⟩ | hLocal
  · exact Or.inl ⟨remote, Pipeline.acceptance_persists S P I W O C ID Protocol V
      _ _ _ _ step.2.1 w accepted⟩
  · exact Or.inr hLocal

omit [Inhabited S] [Inhabited P] [Inhabited I] [Inhabited W]
  [Inhabited O] [Inhabited C] [Inhabited ID] [Inhabited Protocol]
  [Inhabited V] [Inhabited T] [Pipeline.Verdict_EnumClass V] in
theorem validation_gate (th : Th) (st : St) (label : L)
    (gate : Gate S P I W O C ID Protocol V T th st label) :
    ∀ action ∈ cacheLabels S P I W O C ID Protocol V T th label,
      Cache.ValidationGate P W ID T (Authority S P I W O C ID Protocol V T th st) action := by
  cases label with
  | pipeline => simp [cacheLabels]
  | receive w => simp [cacheLabels, Cache.ValidationGate]
  | commitRemote w deliver =>
    have authorized : Authority S P I W O C ID Protocol V T th st w :=
      Or.inl ⟨gate.1, gate.2.1⟩
    simpa [cacheLabels, Cache.ValidationGate] using authorized
  | commitLocal w =>
    have authorized : Authority S P I W O C ID Protocol V T th st w := Or.inr gate
    simpa [cacheLabels, Cache.ValidationGate] using authorized
  | cache action =>
    cases action <;> simp_all [Gate, cacheIndependent, cacheLabels, Cache.ValidationGate]
  | expire => simp [cacheLabels, Cache.ValidationGate]

 theorem validation_binding {th : Th} {st : St} (reachable : (sys).reachable th st) :
    ∀ w, st.cache.accepted w = true → Authority S P I W O C ID Protocol V T th st w := by
  induction reachable with
  | init st assumptions initial =>
    have cacheInitial := initial.2
    simp only [Cache.relationalTransitionSystem, Cache.Init, nextSimp,
      IsSubStateOf.setIn, IsSubStateOf.getFrom, Cache.State.ext_iff, funext_iff] at cacheInitial
    intro w accepted
    grind
  | step st next previous edge ih =>
    obtain ⟨label, step⟩ := edge
    apply Cache.transaction_acceptance_bound P W ID T _ _ _ _
      (Authority S P I W O C ID Protocol V T th next) step.2.2
    · intro action member
      have gate := validation_gate S P I W O C ID Protocol V T th st label step.1 action member
      cases action <;> simp only [Cache.ValidationGate] at gate ⊢
      case validate w => exact authority_persists S P I W O C ID Protocol V T th st next label step w gate
    · intro w accepted
      exact authority_persists S P I W O C ID Protocol V T th st next label step w (ih w accepted)

theorem seen_alignment_step (th : Th) (st next : St) (label : L)
    (step : (sys).tr th st label next) (aligned : st.pipeline.seen = st.cache.seen) :
    next.pipeline.seen = next.cache.seen := by
  rw [Pipeline.seen_transaction S P I W O C ID Protocol V _ _ _ _ step.2.1,
    Cache.seen_transaction P W ID T _ _ _ _ step.2.2, aligned]
  have gate := step.1
  cases label with
  | pipeline action =>
    cases action <;> simp_all [Gate, pipelineIndependent, pipelineLabels, cacheLabels,
      Pipeline.seenEffect]
  | receive w =>
    by_cases formed : (th.input.decoded w).wellFormed = true <;>
      simp [pipelineLabels, cacheLabels, formed, Pipeline.seenEffect, Cache.seenEffect]
  | commitRemote w deliver =>
    cases deliver <;> simp [pipelineLabels, cacheLabels, Pipeline.seenEffect, Cache.seenEffect,
      ProfileInputs.pipelineTheory, cacheTheory]
  | commitLocal w =>
    simp [pipelineLabels, cacheLabels, Pipeline.seenEffect, Cache.seenEffect,
      ProfileInputs.pipelineTheory, cacheTheory]
  | cache action =>
    cases action <;> simp_all [Gate, cacheIndependent, pipelineLabels, cacheLabels,
      Cache.seenEffect]
  | expire k => simp [pipelineLabels, cacheLabels, Pipeline.seenEffect, Cache.seenEffect]

theorem seen_alignment {th : Th} {st : St} (reachable : (sys).reachable th st) :
    st.pipeline.seen = st.cache.seen := by
  induction reachable with
  | init st assumptions initial =>
    have pipelineInitial := initial.1
    have cacheInitial := initial.2
    simp only [Pipeline.relationalTransitionSystem, Pipeline.Init, nextSimp,
      IsSubStateOf.setIn, IsSubStateOf.getFrom, Pipeline.State.ext_iff, funext_iff] at pipelineInitial
    simp only [Cache.relationalTransitionSystem, Cache.Init, nextSimp,
      IsSubStateOf.setIn, IsSubStateOf.getFrom, Cache.State.ext_iff, funext_iff] at cacheInitial
    funext k
    grind
  | step st next previous edge ih =>
    obtain ⟨label, step⟩ := edge
    exact seen_alignment_step S P I W O C ID Protocol V T th st next label step ih

theorem cached_authority {th : Th} {st : St} (reachable : (sys).reachable th st)
    (k : ID) (present : st.cache.present k = true) :
    th.input.key (st.cache.cached k) = k ∧
      Authority S P I W O C ID Protocol V T th st (st.cache.cached k) := by
  have safe := Cache.cacheSafety P W ID T _ _ (cache_reachable S P I W O C ID Protocol V T reachable)
  veil_simp +instances only [Cache.Invariants, invSimp, substateSimp,
    dsimpFieldRepresentationGet] at safe
  have accepted : st.cache.accepted (st.cache.cached k) = true := by grind
  constructor
  · change (cacheTheory S P I W O C ID Protocol T th).key (st.cache.cached k) = k
    grind
  · exact validation_binding S P I W O C ID Protocol V T reachable _ accepted

theorem coreSafety {th : Th} {st : St} (reachable : (sys).reachable th st) :
    Pipeline.Invariants _ _ S P I W O C ID Protocol V
      (Pipeline.FieldAbstractType S P I W O C ID Protocol V) th.input.pipelineTheory st.pipeline ∧
    Cache.Invariants _ _ P W ID T (Cache.FieldAbstractType P W ID T)
      (cacheTheory S P I W O C ID Protocol T th) st.cache ∧
    (∀ w, st.cache.accepted w = true → Authority S P I W O C ID Protocol V T th st w) ∧
    st.pipeline.seen = st.cache.seen := by
  exact ⟨Pipeline.pipelineSafety S P I W O C ID Protocol V _ _
      (pipeline_reachable S P I W O C ID Protocol V T reachable),
    Cache.cacheSafety P W ID T _ _ (cache_reachable S P I W O C ID Protocol V T reachable),
    validation_binding S P I W O C ID Protocol V T reachable,
    seen_alignment S P I W O C ID Protocol V T reachable⟩

#print axioms coreSafety

end Libp2p.Core
