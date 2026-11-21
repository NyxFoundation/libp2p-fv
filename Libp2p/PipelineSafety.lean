module

public import Libp2p.Pipeline
public import Libp2p.Proof

public section

namespace Libp2p.Pipeline

open Classical in
theorem pipelineSafety (session peer stream task object context messageId Verdict : Type)
    [Inhabited session] [Inhabited peer] [Inhabited stream] [Inhabited task]
    [Inhabited object] [Inhabited context] [Inhabited messageId] [Inhabited Verdict]
    [Verdict_EnumClass Verdict]
    (th : Theory session peer stream task object context messageId Verdict)
    (st : State (FieldAbstractType session peer stream task object context messageId Verdict))
    (reachable : (relationalTransitionSystem session peer stream task object context messageId Verdict).reachable th st) :
    Invariants _ _ session peer stream task object context messageId Verdict
      (FieldAbstractType session peer stream task object context messageId Verdict) th st := by
  refine Veil.RelationalTransitionSystem.invariant_of_inductive
    (sys := relationalTransitionSystem session peer stream task object context messageId Verdict)
    ?_ ?_ th st reachable
  · intro th st ha ht
    dsimp only [relationalTransitionSystem, Init] at ht
    rw [← initializer.ext.derived_eq] at ht
    discharge_vcs initializer using ha, True.intro, ht
  · intro th st label next ha hi ht
    cases label <;> dsimp only [relationalTransitionSystem, Next, NextAct] at ht
    case connect s => discharge_vcs connect using ha, hi, ht
    case authenticate s p checks => discharge_vcs authenticate using ha, hi, ht
    case close s => discharge_vcs close using ha, hi, ht
    case openStream i => discharge_vcs openStream using ha, hi, ht
    case propose i matched complete => discharge_vcs propose using ha, hi, ht
    case terminateStream i => discharge_vcs terminateStream using ha, hi, ht
    case dispatch i early => discharge_vcs dispatch using ha, hi, ht
    case writeEnvelope i attached => discharge_vcs writeEnvelope using ha, hi, ht
    case receive w formed => discharge_vcs receive using ha, hi, ht
    case cancel w => discharge_vcs cancel using ha, hi, ht
    case finishValidation w verdict => discharge_vcs finishValidation using ha, hi, ht
    case deliver w => discharge_vcs deliver using ha, hi, ht
    case forward w => discharge_vcs forward using ha, hi, ht
    case credit w => discharge_vcs credit using ha, hi, ht
    case penalize w => discharge_vcs penalize using ha, hi, ht
    case expire k => discharge_vcs expire using ha, hi, ht


#print axioms pipelineSafety

end Libp2p.Pipeline
