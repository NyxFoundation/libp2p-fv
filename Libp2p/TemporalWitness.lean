module

public import Libp2p.TemporalKnowledge
public import Libp2p.TemporalObservation

@[expose] public section
namespace Libp2p.TemporalWitness

open Libp2p.TemporalCausality

variable {peer topic task object context messageId subscription : Type}
variable [DecidableEq peer] [DecidableEq topic] [DecidableEq task] [DecidableEq object]
variable [DecidableEq context] [DecidableEq messageId] [DecidableEq subscription]
variable [Inhabited peer] [Inhabited topic] [Inhabited task] [Inhabited object]
variable [Inhabited context] [Inhabited messageId] [Inhabited subscription]

local notation "CState" => State (FieldAbstractType peer topic task object context messageId subscription)
local notation "CTheory" => Theory peer topic task object context messageId subscription
local notation "CEvent" => Label peer topic task object context messageId subscription
noncomputable abbrev Sys : Veil.RelationalTransitionSystem CTheory CState CEvent :=
  relationalTransitionSystem peer topic task object context messageId subscription

open Libp2p.TemporalKnowledge

/-- The observation-level old-send possibility is exactly: some subscription
change occurred in the observed prefix AND the message was received there.
Under this minimal projection the permission layer is therefore maximally
conservative after any observed change; stronger projections would have to
make remote processing receiver-visible, which is outside the specification. -/
theorem possibly_old_iff {th : CTheory} {h : History th} {j : task} :
    PossiblyOld th (observe h.events) j ↔
      (observe h.events).any Observation.isChange = true ∧
        (Observation.received j) ∈ observe h.events := by
  refine ⟨fun old => ?_, fun pair => ?_⟩
  · obtain ⟨alt, same, altRecv, altOld⟩ := old
    refine ⟨?_, ?_⟩
    · have hflag := alt.change_flag
      rw [same] at hflag
      rw [altOld.1] at hflag
      exact hflag.symm
    · have hm : (Observation.received j) ∈ observe alt.events :=
        Libp2p.TemporalObservation.History.received_observable alt altRecv
      rw [same] at hm
      exact hm
  · obtain ⟨hchg, hmem⟩ := pair
    exact possibly_old_of_change
      (Libp2p.TemporalObservation.Runs.received_join h.execution (Or.inr hmem)) hchg

/-- Witness pair: two admissible global histories with identical receiver
observations. The actual run processes the receiver's latest subscription
change before the send, so the auxiliary actual-order filter would sanction a
penalty and the old-send permission fails; the observation-equivalent run
sends the message with no remote processing at all, where the normative MUST
NOT forbids a penalty. -/
theorem order_check_not_observation_determined (th : CTheory) (st0 : CState)
    (hinit : Sys.init th st0)
    (freshChanged : st0.changed e = false)
    (freshProcess : st0.processed (th.sender j) e = false)
    (freshSent : st0.sent j = false)
    (freshReceived : st0.received j = false) :
    ∃ hA hB : History th,
      observe hA.events = observe hB.events ∧
        hA.last.received j = true ∧ hB.last.received j = true ∧
        hB.last.receiverHasChange = true ∧
        hB.last.processed (th.sender j) hB.last.receiverLatest = false ∧
        hA.last.processed (th.sender j) hA.last.receiverLatest = true ∧
        hA.last.processedAt (th.sender j) hA.last.receiverLatest < hA.last.sentAt j ∧
        ¬ ActualOld th hA.last j ∧ ActualOld th hB.last j ∧ ¬ Permission hA j := by
  obtain ⟨s1, stepCh, f1flag, f1latest, f1chg, f1recv, f1sent, f1proc, _⟩ :=
    change_step th st0 e freshChanged
  have s1chgE : s1.changed e = true := by rw [f1chg e]; simp
  have s1sent : s1.sent j = false := by rw [f1sent j]; exact freshSent
  have s1proc : s1.processed (th.sender j) e = false := by
    rw [f1proc (th.sender j) e]; exact freshProcess
  obtain ⟨s2b, stepBS, f2brecv, f2bchg, f2bflag, f2blatest, f2bsentJ, f2bsent, f2bsentAt,
    f2bserial, f2bproc, f2bprocAt⟩ := send_step th s1 j s1sent
  obtain ⟨s3b, stepBR, f3brecvJ, f3brecv, f3bchg, f3bflag, f3blatest, f3bsent, f3bsentAt,
    f3bproc, f3bprocAt⟩ := receive_step th s2b j f2bsentJ
    (by rw [f2brecv j, f1recv j]; exact freshReceived)
  have bFlag : s3b.receiverHasChange = true := by rw [f3bflag, f2bflag]; exact f1flag
  have bProcFalse : s3b.processed (th.sender j) s3b.receiverLatest = false := by
    rw [f3blatest, f2blatest, f1latest, f3bproc (th.sender j) e, f2bproc (th.sender j) e,
      f1proc (th.sender j) e]
    exact freshProcess
  have bActualOld : ActualOld th s3b j := ⟨bFlag, by rw [bProcFalse]; simp⟩
  obtain ⟨t2, stepP, t2procJ, t2recv, t2chg, t2flag, t2latest, t2sent, t2sentAt, t2procAt,
    t2serial⟩ := process_step th s1 (th.sender j) e s1proc s1chgE
  obtain ⟨t3, stepAS, f3arecv, f3achg, f3aflag, f3alatest, f3asentJ, f3asent, f3asentAt,
    f3aserial, f3aproc, f3aprocAt⟩ := send_step th t2 j (by rw [t2sent j]; exact s1sent)
  obtain ⟨t4, stepAR, f4arecvJ, f4arecv, f4achg, f4aflag, f4alatest, f4asent, f4asentAt, f4aproc,
    f4aprocAt⟩ := receive_step th t3 j f3asentJ
    (by rw [f3arecv j, t2recv j, f1recv j]; exact freshReceived)
  have aProcTrue : t4.processed (th.sender j) t4.receiverLatest = true := by
    rw [f4alatest, f3alatest, t2latest, f1latest, f4aproc (th.sender j) e, f3aproc (th.sender j) e]
    exact t2procJ
  have aLt : t4.processedAt (th.sender j) t4.receiverLatest < t4.sentAt j := by
    rw [f4alatest, f3alatest, t2latest, f1latest, f4aprocAt (th.sender j) e,
      f3aprocAt (th.sender j) e, t2procAt, f4asentAt j, f3asentAt, t2serial]
    omega
  have aFlag : t4.receiverHasChange = true := by rw [f4aflag, f3aflag, t2flag]; exact f1flag
  have obsEq : observe ([.changeSubscription e, .remoteProcesses (th.sender j) e, .send j,
      .receive j] : List CEvent) =
      observe ([.changeSubscription e, .send j, .receive j] : List CEvent) := by
    rfl
  refine ⟨⟨st0, t4, [.changeSubscription e, .remoteProcesses (th.sender j) e, .send j, .receive j],
      hinit,
      Runs.cons stepCh (Runs.cons stepP (Runs.cons stepAS (Runs.cons stepAR (Runs.nil t4))))⟩,
    ⟨st0, s3b, [.changeSubscription e, .send j, .receive j],
      hinit, Runs.cons stepCh (Runs.cons stepBS (Runs.cons stepBR (Runs.nil s3b)))⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact obsEq
  · exact f4arecvJ
  · exact f3brecvJ
  · exact bFlag
  · exact bProcFalse
  · exact aProcTrue
  · exact aLt
  · intro old
    simp [ActualOld, aFlag, aProcTrue, aLt] at old
  · exact bActualOld
  · intro hp
    exact hp ⟨⟨st0, s3b, [.changeSubscription e, .send j, .receive j], hinit,
      Runs.cons stepCh (Runs.cons stepBS (Runs.cons stepBR (Runs.nil s3b)))⟩,
      obsEq.symm, f3brecvJ, bActualOld⟩

end Libp2p.TemporalWitness
