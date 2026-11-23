module

public import Veil

public section
namespace Libp2p

/-- A transaction uses the component's actual labelled transitions, in order. -/
inductive Runs (system : Veil.RelationalTransitionSystem Theory State Label) (theory : Theory) :
    State → List Label → State → Prop where
  | nil (state) : Runs system theory state [] state
  | cons {before middle after label labels} :
      system.tr theory before label middle → Runs system theory middle labels after →
      Runs system theory before (label :: labels) after

theorem Runs.nil_iff {system : Veil.RelationalTransitionSystem Theory State Label}
    {theory : Theory} {before after : State} :
    Runs system theory before [] after ↔ after = before := by
  constructor
  · intro run; cases run; rfl
  · intro same; subst after; exact .nil before

theorem Runs.cons_iff {system : Veil.RelationalTransitionSystem Theory State Label}
    {theory : Theory} {before after : State} {label : Label} {labels : List Label} :
    Runs system theory before (label :: labels) after ↔
      ∃ middle, system.tr theory before label middle ∧ Runs system theory middle labels after := by
  constructor
  · intro run; cases run with | cons step rest => exact ⟨_, step, rest⟩
  · rintro ⟨middle, step, rest⟩; exact .cons step rest

theorem Runs.single_iff {system : Veil.RelationalTransitionSystem Theory State Label}
    {theory : Theory} {before after : State} {label : Label} :
    Runs system theory before [label] after ↔ system.tr theory before label after := by
  simp [cons_iff, nil_iff]

theorem Runs.reachable {system : Veil.RelationalTransitionSystem Theory State Label}
    {theory : Theory} {before after : State} {labels : List Label}
    (run : Runs system theory before labels after) (start : system.reachable theory before) :
    system.reachable theory after := by
  induction run with
  | nil => exact start
  | cons step _ ih => exact ih (.step _ _ start ⟨_, step⟩)

theorem Runs.preserve {system : Veil.RelationalTransitionSystem Theory State Label}
    {theory : Theory} {before after : State} {labels : List Label} (property : State → Prop)
    (step : ∀ s label next, property s → system.tr theory s label next → property next)
    (run : Runs system theory before labels after) (start : property before) : property after := by
  induction run with
  | nil => exact start
  | cons edge _ ih => exact ih (step _ _ _ start edge)

/-- Empty component transactions account for interleaving without a fake self-loop. -/
theorem reachable_projection
    {Theory State Label PartTheory PartState PartLabel : Type}
    (whole : Veil.RelationalTransitionSystem Theory State Label)
    (part : Veil.RelationalTransitionSystem PartTheory PartState PartLabel)
    (theory : Theory → PartTheory) (state : State → PartState)
    (assumptions : ∀ th, whole.assumptions th → part.assumptions (theory th))
    (initial : ∀ th st, whole.init th st → part.init (theory th) (state st))
    (steps : ∀ th st label next, whole.tr th st label next →
      ∃ labels, Runs part (theory th) (state st) labels (state next))
    {th : Theory} {st : State} (reachable : whole.reachable th st) :
    part.reachable (theory th) (state st) := by
  induction reachable with
  | init st ha hi => exact .init _ (assumptions _ ha) (initial _ _ hi)
  | step st next _ edge ih =>
    obtain ⟨label, transition⟩ := edge
    obtain ⟨labels, run⟩ := steps _ _ label _ transition
    exact run.reachable ih

#print axioms reachable_projection

end Libp2p
