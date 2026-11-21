// Clause mapping and abstraction limits: docs/specification-safety-audit.md.
module reset_boundary {
  const BUFFER_POLICY: str
  const CHECK_HANDOFF: bool

  type Reply = Empty | MatchingEcho | NotAvailable | Truncated
  type State = {
    current: int, reconnected: bool, attempt: int, offered: bool, replied: bool,
    buffer: Reply, resetReceived: bool, terminal: bool, endedWithoutAgreement: bool,
    selected: bool, selectionWitness: bool, installed: bool,
    resetSelectionViolation: bool, installationViolation: bool
  }
  var state: State

  // One authenticated origin connection, one stream, and an exchanged MSS header.
  action init = state' = {
    current: 1, reconnected: false, attempt: 1, offered: true, replied: false,
    buffer: Empty, resetReceived: false, terminal: false, endedWithoutAgreement: false,
    selected: false, selectionWitness: false, installed: false,
    resetSelectionViolation: false, installationViolation: false
  }

  // MatchingEcho denotes the complete matching reply plus receive-side EOF.
  // No new bytes are sent after reset; this model only chooses what to do with buffered bytes.
  action bufferReply(reply) = all {
    state.current == 1, not(state.terminal), not(state.resetReceived),
    state.offered, not(state.replied), reply != Empty,
    state' = { ...state, replied: true, buffer: reply }
  }

  action readReply = {
    val agrees = state.buffer == MatchingEcho
    val fails = state.buffer == Truncated
    all {
      state.current == 1, not(state.terminal), state.buffer != Empty,
      state' = { ...state,
        buffer: Empty, offered: false,
        selected: state.selected or agrees,
        selectionWitness: state.selectionWitness or (agrees and state.offered),
        terminal: fails,
        endedWithoutAgreement: state.endedWithoutAgreement or (fails and not(state.selected)),
        resetSelectionViolation: state.resetSelectionViolation or (agrees and state.resetReceived)
      }
    }
  }

  action proposeAgain = all {
    state.current == 1, not(state.terminal), not(state.resetReceived),
    not(state.offered), not(state.selected), state.buffer == Empty, state.attempt < 2,
    state' = { ...state, attempt: state.attempt + 1, offered: true, replied: false }
  }

  // RFC 9000 section 3.2 permits either discarding or delivering fully buffered data.
  // Only the discard-and-notify branch terminates negotiation at this boundary.
  action wireReset(deliverBuffered) = {
    val canDeliver = state.buffer == MatchingEcho and not(state.terminal)
    val permitted = if (deliverBuffered) canDeliver and BUFFER_POLICY != "discard"
      else not(canDeliver) or BUFFER_POLICY != "deliver"
    all {
      state.current == 1, not(state.resetReceived), permitted,
      state' = { ...state, resetReceived: true,
        terminal: state.terminal or not(deliverBuffered),
        buffer: if (deliverBuffered) state.buffer else Empty,
        endedWithoutAgreement: state.endedWithoutAgreement or
          (not(deliverBuffered) and not(state.selected)) }
    }
  }

  // This is an application cancellation contract, not a QUIC timer requirement.
  action timeout = all {
    not(state.terminal), not(state.selected),
    state' = { ...state, terminal: true, buffer: Empty, endedWithoutAgreement: true }
  }

  action close = all {
    state.current != 0,
    state' = { ...state, current: 0, terminal: true, buffer: Empty,
      endedWithoutAgreement: state.endedWithoutAgreement or not(state.selected) }
  }

  action reconnect = all {
    state.current == 0, not(state.reconnected),
    state' = { ...state, current: 2, reconnected: true }
  }

  // Installation is local bookkeeping on the original stream, never a new wire send.
  action callback = {
    val live = not(state.terminal) and state.current == 1
    val install = state.selected and not(state.installed) and (not(CHECK_HANDOFF) or live)
    all {
      state' = { ...state, installed: state.installed or install,
        installationViolation: state.installationViolation or (install and not(live)) }
    }
  }

  action receiveAny = {
    nondet reply = Set(MatchingEcho, NotAvailable, Truncated).oneOf()
    bufferReply(reply)
  }

  action resetAny = {
    nondet deliver = Set(false, true).oneOf()
    wireReset(deliver)
  }

  action step = any {
    receiveAny, readReply, proposeAgain, resetAny, timeout, close, reconnect, callback,
    state' = state
  }

  val wireSelectionSafe = not(state.selected) or state.selectionWitness
  val selectionSafe = not(state.endedWithoutAgreement and state.selected)
  val installationSafe = not(state.installationViolation)
  val boundarySafety = wireSelectionSafe and selectionSafe
  val safety = boundarySafety and installationSafe
  // Deliberately stronger than N-05.01: wire reset is not local termination.
  val wireResetStopsSelection = not(state.resetSelectionViolation)
}
