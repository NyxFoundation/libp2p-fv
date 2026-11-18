module scenarios {
  import negotiation(PEERS = Set(1, 2), GENERATIONS = Set(1, 2), STREAMS = Set(1, 2)).*
    from "./negotiation"

  action ready = init.then(open(1, 1)).then(authenticate(1)).then(begin(1, 1))
  action offered = ready.then(propose(1))
  action agreed = offered.then(receive(1, Selected))
  action reconnect = close(1).then(open(1, 2)).then(authenticate(2))

  val noEffects = progress.selections == Set() and installed == Set() and safety

  run shouldInstallOnOriginWhenNegotiationSucceedsTest = agreed.then(callback(1))
    .expect(progress.selections == Set(1) and installed == Set(1) and safety)

  run shouldAllowAnotherProposalWhenFirstIsDeclinedTest = offered.then(receive(1, NotAvailable))
    .expect(noEffects).then(propose(1)).then(receive(1, Selected)).then(callback(1))
    .expect(progress.selections == Set(1) and installed == Set(1) and safety)

  run shouldNotSelectWhenReplyIsTruncatedTest = offered.then(receive(1, Truncated))
    .then(receive(1, Selected)).then(callback(1))
    .expect(noEffects and progress.endedWithoutAgreement == Set(1))

  run shouldNotSelectWhenStreamResetsTest = offered.then(receive(1, Reset))
    .then(receive(1, Selected)).then(callback(1))
    .expect(noEffects and progress.endedWithoutAgreement == Set(1))

  run shouldNotSelectWhenPolicyTimesOutTest = offered.then(receive(1, Timeout))
    .then(receive(1, Selected)).then(callback(1))
    .expect(noEffects and progress.endedWithoutAgreement == Set(1))

  run shouldNotSelectWhenNoProposalIsOutstandingTest = ready.then(receive(1, Selected))
    .expect(noEffects).then(propose(1)).then(receive(1, Selected)).then(callback(1))
    .expect(progress.selections == Set(1) and installed == Set(1) and safety)

  run shouldNotSelectWhenPolicyTimesOutAfterDeclineTest = offered.then(receive(1, NotAvailable))
    .then(receive(1, Timeout)).then(receive(1, Selected))
    .expect(noEffects and progress.endedWithoutAgreement == Set(1)).then(propose(1).fail())

  run shouldIgnoreNegotiationTimeoutWhenAgreementAlreadyOccurredTest = agreed
    .then(receive(1, Timeout)).then(callback(1))
    .expect(progress.selections == Set(1) and installed == Set(1) and safety)

  run shouldNotInstallWhenCallbackPrecedesAgreementTest = offered.then(callback(1))
    .expect(noEffects).then(receive(1, Selected)).then(callback(1))
    .expect(installed == Set(1) and safety)

  run shouldNotInstallWhenAgreedStreamResetsBeforeCallbackTest = agreed.then(receive(1, Reset))
    .then(callback(1)).expect(progress.selections == Set(1) and installed == Set() and safety)

  run shouldNotInstallWhenAgreedSessionClosesBeforeCallbackTest = agreed.then(close(1))
    .then(callback(1)).expect(progress.selections == Set(1) and installed == Set() and safety)

  run shouldNotCarryOldCallbackToReplacementWhenPeerReconnectsTest = agreed.then(reconnect)
    .then(begin(2, 2)).then(propose(2)).then(receive(2, Selected)).then(callback(1))
    .expect(progress.selections == Set(1, 2) and installed == Set() and safety)
    .then(callback(2)).expect(installed == Set(2) and safety)

  run shouldNotSelectWhenSessionClosedWithoutAgreementTest = offered.then(close(1))
    .then(receive(1, Selected)).then(callback(1))
    .expect(noEffects and progress.endedWithoutAgreement == Set(1))

  run shouldKeepOtherStreamNegotiatingWhenOneResetsTest = offered
    .then(begin(1, 2)).then(propose(2)).then(receive(1, Reset))
    .then(receive(2, Selected)).then(callback(1)).then(callback(2))
    .expect(progress.selections == Set(2) and installed == Set(2) and safety)

  run shouldKeepOtherPeerNegotiatingWhenOneClosesTest = offered.then(open(2, 2))
    .then(authenticate(2)).then(begin(2, 2)).then(propose(2)).then(close(1))
    .then(receive(2, Selected)).then(callback(2))
    .expect(progress.selections == Set(2) and installed == Set(2) and safety)

  run shouldPreserveEarlierSuccessWhenStreamAndSessionLaterEndTest = agreed.then(callback(1))
    .then(receive(1, Reset)).then(close(1)).then(callback(1))
    .expect(progress.selections == Set(1) and installed == Set(1) and safety)

  run shouldRejectStreamCreationWhenSessionIsUnauthenticatedTest = init.then(open(1, 1))
    .then(begin(1, 1).fail())

  run shouldRejectStreamSlotReuseWhenPeerReconnectsTest = agreed.then(reconnect)
    .then(begin(2, 1).fail())
}
