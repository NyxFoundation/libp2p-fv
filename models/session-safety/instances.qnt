module single {
  import lifecycle(PEERS = Set(1), SESSIONS = Set(1), OPERATIONS = Set(1),
    CHECK_CANCEL = true, CHECK_GENERATION = true).* from "./lifecycle"
}

module reconnect {
  import lifecycle(PEERS = Set(1), SESSIONS = Set(1, 2), OPERATIONS = Set(1, 2),
    CHECK_CANCEL = true, CHECK_GENERATION = true).* from "./lifecycle"
}

module peers {
  import lifecycle(PEERS = Set(1, 2), SESSIONS = Set(1, 2), OPERATIONS = Set(1, 2),
    CHECK_CANCEL = true, CHECK_GENERATION = true).* from "./lifecycle"
}

module generations {
  import lifecycle(PEERS = Set(1, 2), SESSIONS = Set(1, 2, 3), OPERATIONS = Set(1, 2),
    CHECK_CANCEL = true, CHECK_GENERATION = true).* from "./lifecycle"
}

module concurrent {
  import lifecycle(PEERS = Set(1), SESSIONS = Set(1, 2), OPERATIONS = Set(1, 2, 3),
    CHECK_CANCEL = true, CHECK_GENERATION = true).* from "./lifecycle"
}

module missingCancellationGuard {
  import lifecycle(PEERS = Set(1), SESSIONS = Set(1), OPERATIONS = Set(1),
    CHECK_CANCEL = false, CHECK_GENERATION = true).* from "./lifecycle"
}

module missingGenerationGuard {
  import lifecycle(PEERS = Set(1), SESSIONS = Set(1, 2), OPERATIONS = Set(1),
    CHECK_CANCEL = true, CHECK_GENERATION = false).* from "./lifecycle"
}
