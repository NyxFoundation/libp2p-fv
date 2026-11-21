module sessionProtected {
  import lifecycle(PEERS = Set(1), SESSIONS = Set(1, 2), OPERATIONS = Set(1),
    CHECK_CANCEL = true, CHECK_GENERATION = true).* from "../session-safety/lifecycle"
}

// These are design-contract probes, not specification-conformance witnesses.
module cancellationGap {
  import lifecycle(PEERS = Set(1), SESSIONS = Set(1), OPERATIONS = Set(1),
    CHECK_CANCEL = false, CHECK_GENERATION = true).* from "../session-safety/lifecycle"
}

module generationGap {
  import lifecycle(PEERS = Set(1), SESSIONS = Set(1, 2), OPERATIONS = Set(1),
    CHECK_CANCEL = true, CHECK_GENERATION = false).* from "../session-safety/lifecycle"
}

module discardReset {
  import reset_boundary(BUFFER_POLICY = "discard", CHECK_HANDOFF = true).* from "./reset-boundary"
  val discardSafety = safety and wireResetStopsSelection
}

module deliverBufferedReset {
  import reset_boundary(BUFFER_POLICY = "deliver", CHECK_HANDOFF = true).* from "./reset-boundary"
}

module eitherReset {
  import reset_boundary(BUFFER_POLICY = "either", CHECK_HANDOFF = true).* from "./reset-boundary"
}

module unguardedHandoff {
  import reset_boundary(BUFFER_POLICY = "either", CHECK_HANDOFF = false).* from "./reset-boundary"
}
