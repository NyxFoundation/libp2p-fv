module

public import Libp2p.PipelineFacts
public import Libp2p.CacheSafety

@[expose] public section
namespace Libp2p.Core

open Classical
open scoped Libp2p.Pipeline Libp2p.Cache

variable (S P I W O C ID Protocol V T : Type)
variable [Inhabited S] [Inhabited P] [Inhabited I] [Inhabited W]
variable [Inhabited O] [Inhabited C] [Inhabited ID] [Inhabited Protocol]
variable [Inhabited V] [Inhabited T] [Pipeline.Verdict_EnumClass V]

local notation "PS" => Pipeline.State (Pipeline.FieldAbstractType S P I W O C ID Protocol V)
local notation "CS" => Cache.State (Cache.FieldAbstractType P W ID T)
local notation "PL" => Pipeline.Label S P I W O C ID Protocol V
local notation "CL" => Cache.Label P W ID T
local notation "pSys" => Pipeline.relationalTransitionSystem S P I W O C ID Protocol V
local notation "cSys" => Cache.relationalTransitionSystem P W ID T

structure Theory where
  input : ProfileInputs S P I W O C ID Protocol
  topic : W → T
  isLocal : W → Bool
  localAccepted : W → Bool
  historyLength : Nat
  gossipLength : Nat
  retransmissionLimit : Nat
  followupTicks : Nat

structure State where
  pipeline : PS
  cache : CS

inductive Label where
  | pipeline (action : PL)
  | receive (task : W)
  | commitRemote (task : W) (deliverToApplication : Bool)
  | commitLocal (task : W)
  | cache (action : CL)
  | expire (id : ID)

local notation "Th" => Theory S P I W O C ID Protocol T
local notation "St" => State S P I W O C ID Protocol V T
local notation "L" => Label S P I W O C ID Protocol V T

def cacheTheory (th : Th) : Cache.Theory P W ID T where
  key := th.input.key
  topicOf := th.topic
  historyLength := th.historyLength
  gossipLength := th.gossipLength
  retransmissionLimit := th.retransmissionLimit
  followupTicks := th.followupTicks

/-- An accepted cached object outlives its original session; it does not grant
that session authority to issue a new callback after closing. -/
def Authority (th : Th) (st : St) (w : W) : Prop :=
  (th.isLocal w = false ∧ st.pipeline.accepted w = true) ∨
  (th.isLocal w = true ∧ th.localAccepted w = true)

def CurrentTask (th : Th) (st : St) (w : W) : Prop :=
  st.pipeline.live (th.input.owner (th.input.source w)) = true ∧
  st.pipeline.reset (th.input.source w) = false ∧ st.pipeline.canceled w = false

/-- Actions that do not write the shared seen index or create decoded arrivals. -/
def pipelineIndependent : PL → Prop
  | .receive .. | .deliver .. | .rememberKey .. | .expire .. => False
  | _ => True

def cacheIndependent : CL → Prop
  | .validate .. | .store .. | .received .. | .expireSeen .. => False
  | _ => True

noncomputable def pipelineLabels (th : Th) : L → List PL
  | .pipeline action => [action]
  | .receive w => [.receive w (th.input.decoded w).wellFormed]
  | .commitRemote w deliver =>
      [if deliver then .deliver w else .rememberKey (th.input.key w)]
  | .commitLocal w => [.rememberKey (th.input.key w)]
  | .cache _ => []
  | .expire k => [.expire k]

noncomputable def cacheLabels (th : Th) : L → List CL
  | .pipeline _ => []
  | .receive w => if (th.input.decoded w).wellFormed then
      [.received (th.input.expected (th.input.owner (th.input.source w))) (th.input.key w)] else []
  | .commitRemote w _ | .commitLocal w => [.validate w, .store w]
  | .cache action => [action]
  | .expire k => [.expireSeen k]

noncomputable def Gate (th : Th) (st : St) : L → Prop
  | .pipeline action => pipelineIndependent S P I W O C ID Protocol V action
  | .receive w => th.isLocal w = false
  | .commitRemote w _ => th.isLocal w = false ∧ st.pipeline.accepted w = true ∧
      CurrentTask S P I W O C ID Protocol V T th st w ∧
      st.pipeline.seen (th.input.key w) = false
  | .commitLocal w => th.isLocal w = true ∧ th.localAccepted w = true
  | .cache action => cacheIndependent P W ID T action
  | .expire _ => True

/-- A labelled transaction invokes the actual component relations. No component
invariant or post-state correspondence is assumed in this transition relation. -/
noncomputable def system : Veil.RelationalTransitionSystem Th St L where
  assumptions th := (pSys).assumptions th.input.pipelineTheory ∧
    (cSys).assumptions (cacheTheory S P I W O C ID Protocol T th)
  init th st := (pSys).init th.input.pipelineTheory st.pipeline ∧
    (cSys).init (cacheTheory S P I W O C ID Protocol T th) st.cache
  tr th st label next := Gate S P I W O C ID Protocol V T th st label ∧
    Runs pSys th.input.pipelineTheory st.pipeline
      (pipelineLabels S P I W O C ID Protocol V T th label) next.pipeline ∧
    Runs cSys (cacheTheory S P I W O C ID Protocol T th) st.cache
      (cacheLabels S P I W O C ID Protocol V T th label) next.cache

end Libp2p.Core
