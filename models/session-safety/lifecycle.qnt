// Abstract authority model; see docs/session-safety.md for the evidence boundary.
module lifecycle {
  const PEERS: Set[int]
  const SESSIONS: Set[int]
  const OPERATIONS: Set[int]
  const CHECK_CANCEL: bool
  const CHECK_GENERATION: bool

  type Session = { peer: int, status: str }
  type Operation = {
    session: int, kind: str, result: str, cancelled: bool, consumed: bool
  }
  type Effect = { operation: int, session: int, peer: int, kind: str }
  type State = {
    sessions: int -> Session,
    current: int -> int,
    operations: int -> Operation,
    credited: Set[int],
    lastEffect: Effect,
    cancelViolation: bool,
    staleViolation: bool
  }
  var state: State

  pure val KINDS = Set("delivery", "credit", "handler")
  pure val RESULTS = Set("accept", "reject", "ignore")
  pure val NO_EFFECT = { operation: 0, session: 0, peer: 0, kind: "none" }
  pure val EMPTY_OPERATION = {
    session: 0, kind: "none", result: "unused", cancelled: false, consumed: false
  }

  action init = state' = {
    sessions: SESSIONS.union(Set(0)).mapBy(_ => { peer: 0, status: "unused" }),
    current: PEERS.union(Set(0)).mapBy(_ => 0),
    operations: OPERATIONS.mapBy(_ => EMPTY_OPERATION),
    credited: Set(),
    lastEffect: NO_EFFECT,
    cancelViolation: false,
    staleViolation: false
  }

  // A generation slot is allocated once. Exhaustion disables new opens, not safety checks.
  action open(peer, session) = all {
    state.current.get(peer) == 0,
    state.sessions.get(session).status == "unused",
    state' = { ...state,
      sessions: state.sessions.set(session, { peer: peer, status: "unauthenticated" }),
      current: state.current.set(peer, session)
    }
  }

  // This result is an external authentication contract, not a crypto proof.
  // Closed generations cannot consume a late authentication success.
  action authenticate(session) = all {
    state.sessions.get(session).status == "unauthenticated",
    state' = { ...state, sessions: state.sessions.setBy(session,
      s => { ...s, status: "authenticated" }) }
  }

  // Also represents authentication failure / fail-stop. Peer history survives.
  action close(session) = all {
    Set("unauthenticated", "authenticated").contains(state.sessions.get(session).status),
    state' = { ...state,
      sessions: state.sessions.setBy(session, s => { ...s, status: "closed" }),
      current: state.current.set(state.sessions.get(session).peer, 0)
    }
  }

  action begin(session, operation, kind) = all {
    state.sessions.get(session).status == "authenticated",
    state.operations.get(operation).result == "unused",
    state' = { ...state, operations: state.operations.set(operation, {
      session: session, kind: kind, result: "pending", cancelled: false, consumed: false
    }) }
  }

  // Cancellation linearizes here, including after completion but before use.
  action cancel(operation) = all {
    state.operations.get(operation).result != "unused",
    not(state.operations.get(operation).consumed),
    state' = { ...state, operations: state.operations.setBy(operation,
      o => { ...o, cancelled: true }) }
  }

  // Late external completions are deliberately allowed after close/cancel.
  action complete(operation, result) = all {
    state.operations.get(operation).result == "pending",
    state' = { ...state, operations: state.operations.setBy(operation,
      o => { ...o, result: result }) }
  }

  def authorized(operation) = {
    val o = state.operations.get(operation)
    val s = state.sessions.get(o.session)
    val current = state.current.get(s.peer)
    current != 0 and
      state.sessions.get(current).status == "authenticated" and
      o.result == "accept" and
      (not(CHECK_CANCEL) or not(o.cancelled)) and
      (not(CHECK_GENERATION) or current == o.session)
  }

  // Atomic point of effect: the authority check and emission cannot interleave.
  // Monitors inspect the pre-state independently of the optional protection gates.
  action use(operation) = {
    val o = state.operations.get(operation)
    val s = state.sessions.get(o.session)
    val current = state.current.get(s.peer)
    val emit = authorized(operation)
    all {
      RESULTS.contains(o.result),
      not(o.consumed),
      state' = { ...state,
        operations: state.operations.set(operation, { ...o, consumed: true }),
        credited: if (emit and o.kind == "credit") state.credited.union(Set(s.peer))
          else state.credited,
        lastEffect: if (emit) {
          operation: operation, session: current, peer: s.peer, kind: o.kind
        } else NO_EFFECT,
        cancelViolation: state.cancelViolation or (emit and o.cancelled),
        staleViolation: state.staleViolation or
          (emit and (s.status != "authenticated" or current != o.session))
      }
    }
  }

  action openAny = {
    nondet peer = PEERS.oneOf()
    nondet session = SESSIONS.oneOf()
    open(peer, session)
  }

  action sessionAny = {
    nondet session = SESSIONS.oneOf()
    any { authenticate(session), close(session) }
  }

  action beginAny = {
    nondet session = SESSIONS.oneOf()
    nondet operation = OPERATIONS.oneOf()
    nondet kind = KINDS.oneOf()
    begin(session, operation, kind)
  }

  action operationAny = {
    nondet operation = OPERATIONS.oneOf()
    any { cancel(operation), use(operation) }
  }

  action completeAny = {
    nondet operation = OPERATIONS.oneOf()
    nondet result = RESULTS.oneOf()
    complete(operation, result)
  }

  action step = any {
    openAny, sessionAny, beginAny, operationAny, completeAny, state' = state
  }

  // R-03.01 and R-04.01 are historical monitors: later cancellation/close
  // must not retroactively invalidate effects that linearized earlier.
  val cancellationSafe = not(state.cancelViolation)
  val generationSafe = not(state.staleViolation)
  val safety = cancellationSafe and generationSafe
}
