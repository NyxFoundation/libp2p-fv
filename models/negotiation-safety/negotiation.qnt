module negotiation {
  const PEERS: Set[int]
  const GENERATIONS: Set[int]
  const STREAMS: Set[int]

  import lifecycle(PEERS = PEERS, SESSIONS = GENERATIONS, OPERATIONS = Set(),
    CHECK_CANCEL = true, CHECK_GENERATION = true) as Authority from "../session-safety/lifecycle"

  type Phase = Unused | Awaiting | Offered | Agreed | Ended
  type Input = Selected | NotAvailable | Truncated | Reset | Timeout
  type Stream = { generation: int, phase: Phase }
  type Installation = {
    stream: int, generation: int, current: int, authenticated: bool, phase: Phase
  }
  type Progress = {
    streams: int -> Stream,
    selections: Set[int],
    endedWithoutAgreement: Set[int],
    installations: Set[Installation]
  }
  var progress: Progress

  action init = all {
    Authority::init,
    progress' = {
      streams: STREAMS.mapBy(_ => { generation: 0, phase: Unused }),
      selections: Set(), endedWithoutAgreement: Set(), installations: Set()
    }
  }

  def currentGeneration(generation) = {
    val owner = Authority::state.sessions.get(generation).peer
    Authority::state.current.get(owner)
  }

  def authenticated(generation) = Authority::state.sessions.get(generation).status == "authenticated"
  def live(generation) = authenticated(generation) and currentGeneration(generation) == generation
  pure def negotiating(phase) = Set(Awaiting, Offered).contains(phase)

  action keepAuthority = Authority::state' = Authority::state

  action open(peer, generation) = all { Authority::open(peer, generation), progress' = progress }
  action authenticate(generation) = all { Authority::authenticate(generation), progress' = progress }

  // Retain agreed streams on a closed generation so a delayed callback still has an origin.
  action close(generation) = {
    val unagreed = STREAMS.filter(id => {
      val s = progress.streams.get(id)
      s.generation == generation and negotiating(s.phase)
    })
    all {
      Authority::close(generation),
      progress' = { ...progress, endedWithoutAgreement: progress.endedWithoutAgreement.union(unagreed) }
    }
  }

  action begin(generation, stream) = all {
    live(generation),
    progress.streams.get(stream).phase == Unused,
    keepAuthority,
    progress' = { ...progress, streams: progress.streams.set(stream, { generation: generation, phase: Awaiting }) }
  }

  action propose(stream) = {
    val s = progress.streams.get(stream)
    all {
      s.phase == Awaiting,
      live(s.generation),
      keepAuthority,
      progress' = { ...progress, streams: progress.streams.set(stream, { ...s, phase: Offered }) }
    }
  }

  // Inputs are parser/matcher outcomes, not wire messages or protocol IDs.
  action receive(stream, input) = {
    val s = progress.streams.get(stream)
    val active = s.phase != Ended and live(s.generation)
    val pending = active and s.phase == Offered
    val agreed = pending and input == Selected
    val stop = active and (input == Reset or (input == Timeout and negotiating(s.phase))
      or (input == Truncated and pending))
    val phase = if (agreed) Agreed else if (stop) Ended
      else if (pending and input == NotAvailable) Awaiting else s.phase
    all {
      s.phase != Unused,
      keepAuthority,
      progress' = {
        streams: progress.streams.set(stream, { ...s, phase: phase }),
        selections: if (agreed) progress.selections.union(Set(stream)) else progress.selections,
        endedWithoutAgreement: if (stop and negotiating(s.phase))
          progress.endedWithoutAgreement.union(Set(stream)) else progress.endedWithoutAgreement,
        installations: progress.installations
      }
    }
  }

  val installed = progress.installations.map(event => event.stream)

  // Authority and effect share one transition. The callback carries only its immutable origin.
  action callback(stream) = {
    val s = progress.streams.get(stream)
    val allowed = s.phase == Agreed and live(s.generation) and not(installed.contains(stream))
    val observed = { stream: stream, generation: s.generation, phase: s.phase,
      current: currentGeneration(s.generation), authenticated: authenticated(s.generation) }
    all {
      s.phase != Unused,
      keepAuthority,
      progress' = { ...progress, installations: if (allowed)
        progress.installations.union(Set(observed)) else progress.installations }
    }
  }

  action sessionStep = {
    nondet peer = PEERS.oneOf()
    nondet generation = GENERATIONS.oneOf()
    any { open(peer, generation), authenticate(generation), close(generation) }
  }

  action streamStep = {
    nondet stream = STREAMS.oneOf()
    nondet generation = GENERATIONS.oneOf()
    nondet input = Set(Selected, NotAvailable, Truncated, Reset, Timeout).oneOf()
    any { begin(generation, stream), propose(stream), receive(stream, input), callback(stream) }
  }

  action step = any { sessionStep, streamStep, all { keepAuthority, progress' = progress } }

  // Failure history follows the pre-transition phase, not the emitted selection event.
  val selectionSafe = progress.selections.intersect(progress.endedWithoutAgreement) == Set()
  val installationSafe = progress.installations.forall(event => progress.selections.contains(event.stream)
    and event.phase == Agreed and event.authenticated and event.generation == event.current)
  val safety = selectionSafe and installationSafe
}
