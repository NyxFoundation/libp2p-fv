module scenarios {
  import reset_boundary(BUFFER_POLICY = "either", CHECK_HANDOFF = true).* from "./reset-boundary"

  action buffered = init.then(bufferReply(MatchingEcho))
  action agreed = buffered.then(readReply)
  val noEffects = not(state.selected) and not(state.installed) and safety

  run shouldSelectBufferedEchoWhenWireResetNotificationIsSuppressedTest = buffered
    .then(wireReset(true)).then(readReply)
    .expect(state.selected and state.resetReceived and not(state.terminal) and safety
      and not(wireResetStopsSelection))

  run shouldNotSelectWhenResetDiscardsBufferedEchoTest = buffered.then(wireReset(false))
    .expect(noEffects and state.endedWithoutAgreement).then(readReply.fail())

  run shouldNotSuppressResetWhenReplyIsIncompleteTest = init.then(bufferReply(Truncated))
    .then(wireReset(true).fail())

  run shouldNotSelectWhenTruncatedReplyIsReadTest = init.then(bufferReply(Truncated))
    .then(readReply).then(callback).expect(noEffects and state.terminal)

  run shouldDiscardBufferedReplyWhenLocalTimeoutTakesEffectTest = buffered.then(timeout)
    .expect(noEffects and state.endedWithoutAgreement).then(readReply.fail())

  run shouldAllowAnotherProposalWhenFirstIsUnavailableTest = init.then(bufferReply(NotAvailable))
    .then(readReply).expect(noEffects).then(proposeAgain).then(bufferReply(MatchingEcho))
    .then(readReply).then(callback).expect(state.installed and state.attempt == 2 and safety)

  run shouldNotInstallWhenNoAgreementExistsTest = init.then(callback).expect(noEffects)

  run shouldInstallWhenAgreementAndOriginRemainLiveTest = agreed.then(callback)
    .expect(state.installed and safety)

  run shouldNotInstallWhenResetIsSignalledAfterAgreementTest = agreed.then(wireReset(false))
    .then(callback).expect(state.selected and not(state.installed) and safety)

  run shouldNotSelectWhenSessionClosesBeforeReplyReadTest = buffered.then(close).then(callback)
    .expect(noEffects and state.endedWithoutAgreement).then(readReply.fail())

  run shouldNotInstallWhenSessionClosesAfterAgreementTest = agreed.then(close).then(callback)
    .expect(state.selected and not(state.installed) and safety)

  run shouldNotInstallWhenSuccessorSessionIsCurrentTest = agreed.then(close).then(reconnect)
    .then(callback).expect(state.current == 2 and not(state.installed) and safety)

  run shouldPreserveEarlierSuccessWhenSessionLaterClosesTest = agreed.then(callback).then(close)
    .then(reconnect).then(callback).expect(state.installed and safety)

  run shouldNotSelectWhenResetArrivesWithoutBufferedDataTest = init.then(wireReset(false))
    .then(callback).expect(noEffects and state.endedWithoutAgreement)

  run shouldNotApplyNegotiationTimeoutWhenAlreadyAgreedTest = agreed.then(timeout.fail())

  run shouldNotReceiveNewReplyWhenWireResetAlreadyArrivedTest = buffered.then(wireReset(true))
    .then(bufferReply(MatchingEcho).fail())

  run shouldNotMakePriorAgreementInvalidWhenResetArrivesLaterTest = agreed.then(wireReset(false))
    .expect(state.selected and wireResetStopsSelection and safety)
}

module unguarded_scenarios {
  import reset_boundary(BUFFER_POLICY = "either", CHECK_HANDOFF = false).* from "./reset-boundary"

  action agreed = init.then(bufferReply(MatchingEcho)).then(readReply)

  run shouldExposeLocalInstallationGapWhenOriginClosesTest = agreed.then(close).then(callback)
    .expect(state.installed and state.installationViolation and boundarySafety)

  run shouldExposeLocalInstallationGapWhenPeerReconnectsTest = agreed.then(close).then(reconnect)
    .then(callback).expect(state.current == 2 and state.installationViolation and boundarySafety)

  run shouldAllowNormalInstallationWhenOptionalGuardIsAbsentTest = agreed.then(callback)
    .expect(state.installed and safety)
}
