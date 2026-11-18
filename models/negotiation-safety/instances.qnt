module singleStream {
  import negotiation(PEERS = Set(1), GENERATIONS = Set(1), STREAMS = Set(1)).* from "./negotiation"
}

module concurrentStreams {
  import negotiation(PEERS = Set(1), GENERATIONS = Set(1), STREAMS = Set(1, 2)).* from "./negotiation"
}

module reconnectingPeer {
  import negotiation(PEERS = Set(1), GENERATIONS = Set(1, 2), STREAMS = Set(1, 2)).* from "./negotiation"
}

module independentPeers {
  import negotiation(PEERS = Set(1, 2), GENERATIONS = Set(1, 2), STREAMS = Set(1, 2)).* from "./negotiation"
}
