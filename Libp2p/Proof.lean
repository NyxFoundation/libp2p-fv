module

public import Veil
public meta import Lean.Elab.Tactic

public section
namespace Libp2p

/-- Connect a checked Veil WP obligation to its relational transition semantics. -/
theorem post_of_wp {ρ σ : Type} {mode : Veil.Mode}
    (act : Veil.VeilM mode ρ σ Unit) (assu : ρ → Prop) (pre post : Veil.SProp ρ σ)
    (proof : act.meetsSpecificationIfSuccessfulAssuming assu pre post)
    (th : ρ) (st next : σ) (ha : assu th) (hp : pre th st)
    (step : act.toTransitionDerived th st next) : post th next := by
  have h : act.toTransition.meetsSpecificationIfSuccessful
      (fun rd s => assu rd ∧ pre rd s) post := by
    rw [Veil.Transition.meetsSpecificationIfSuccessful_eq]
    exact proof
  apply h th st next ⟨ha, hp⟩
  simpa only [Veil.VeilM.toTransitionDerived_sound] using step

end Libp2p

public meta section
open Lean Meta Elab Tactic in
elab "from_vc " action:ident " using " ha:term ", " hi:term ", " ht:term : tactic => do
  withMainContext do
    let goal ← getMainGoal
    let target ← instantiateMVars (← goal.getType)
    let .const predicate _ := target.getAppFn
      | throwError "expected a named Veil invariant, got {target}"
    let theoremName := predicate.getPrefix ++ Name.mkSimple
      (action.getId.toString ++ "_" ++ predicate.getString!)
    let step ← Lean.Elab.Term.elabTerm ht none
    let stepArgs := (← inferType step).getAppArgs
    unless stepArgs.size ≥ 4 do
      throwError "expected a Veil transition application"
    let act := stepArgs[stepArgs.size - 4]!
    let proof := mkAppN (← mkConstWithFreshMVarLevels theoremName) act.getAppArgs
    let proofArgs := (← inferType proof).getAppArgs
    unless proofArgs.size ≥ 3 do
      throwError "expected a fully instantiated Veil WP theorem"
    let has ← Lean.Elab.Term.elabTerm ha none
    let hpre ← Lean.Elab.Term.elabTerm hi none
    let result ← mkAppM ``Libp2p.post_of_wp #[
      act, proofArgs[proofArgs.size - 3]!, proofArgs[proofArgs.size - 2]!,
      proofArgs[proofArgs.size - 1]!, proof, stepArgs[stepArgs.size - 3]!,
      stepArgs[stepArgs.size - 2]!, stepArgs[stepArgs.size - 1]!, has, hpre, step]
    unless ← isDefEq (← inferType result) target do
      throwError "Veil VC does not establish the requested invariant"
    goal.assign result
    replaceMainGoal []

macro "discharge_vcs " action:ident " using " ha:term ", " hi:term ", " ht:term : tactic =>
  `(tactic| (unfold $(Lean.mkIdent `Invariants)
             repeat' constructor
             all_goals from_vc $action using $ha, $hi, $ht))
