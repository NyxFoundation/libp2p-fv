module scenarios {
  import lifecycle(PEERS = Set(1, 2), SESSIONS = Set(1, 2, 3), OPERATIONS = Set(1, 2, 3),
    CHECK_CANCEL = true, CHECK_GENERATION = true).* from "./lifecycle"

  action ready = init.then(open(1, 1)).then(authenticate(1))
  action replacement = close(1).then(open(1, 2)).then(authenticate(2))

  run shouldDeliverWhenAuthenticatedAndAcceptedTest = ready
    .then(begin(1, 1, "delivery")).then(complete(1, "accept")).then(use(1))
    .expect(state.lastEffect == { operation: 1, session: 1, peer: 1, kind: "delivery" })

  run shouldInstallHandlerWhenCurrentSessionSucceedsTest = ready
    .then(begin(1, 1, "handler")).then(complete(1, "accept")).then(use(1))
    .expect(state.lastEffect.kind == "handler" and safety)

  run shouldDropWhenCancelledBeforeCompletionTest = ready
    .then(begin(1, 1, "delivery")).then(cancel(1)).then(complete(1, "accept"))
    .then(use(1)).expect(state.lastEffect == NO_EFFECT and safety)

  run shouldDropWhenCancelledAfterCompletionTest = ready
    .then(begin(1, 1, "credit")).then(complete(1, "accept")).then(cancel(1))
    .then(use(1)).expect(state.credited == Set() and safety)

  run shouldDropWhenOldValidationCompletesAfterReconnectTest = ready
    .then(begin(1, 1, "delivery")).then(replacement)
    .then(complete(1, "accept")).then(use(1))
    .expect(state.lastEffect == NO_EFFECT and safety)

  run shouldDropWhenSessionClosesBetweenCompletionAndUseTest = ready
    .then(begin(1, 1, "delivery")).then(complete(1, "accept")).then(close(1))
    .then(use(1)).expect(state.lastEffect == NO_EFFECT and safety)

  run shouldDropHandlerWhenSessionWasReplacedTest = ready
    .then(begin(1, 1, "handler")).then(complete(1, "accept")).then(replacement)
    .then(use(1)).expect(state.lastEffect == NO_EFFECT and safety)

  run shouldNotCreditWhenOldSessionCompletesTest = ready
    .then(begin(1, 1, "credit")).then(replacement)
    .then(complete(1, "accept")).then(use(1))
    .expect(state.credited == Set() and safety)

  run shouldDeliverNewWorkWhenSessionReauthenticatesTest = ready
    .then(begin(1, 1, "delivery")).then(replacement)
    .then(begin(2, 2, "delivery")).then(complete(2, "accept")).then(use(2))
    .expect(state.lastEffect.session == 2 and state.lastEffect.operation == 2 and safety)

  run shouldRetainCreditWithoutImportingAuthorityTest = ready
    .then(begin(1, 1, "credit")).then(complete(1, "accept")).then(use(1))
    .then(close(1)).then(open(1, 2))
    .expect(state.credited == Set(1) and state.sessions.get(2).status == "unauthenticated")

  run shouldKeepPeersIndependentWhenOneDisconnectsTest = ready
    .then(open(2, 2)).then(authenticate(2)).then(begin(2, 1, "delivery"))
    .then(close(1)).then(complete(1, "accept")).then(use(1))
    .expect(state.lastEffect.peer == 2 and state.lastEffect.session == 2 and safety)

  run shouldKeepWorkIndependentWhenAnotherOperationIsCancelledTest = ready
    .then(begin(1, 1, "delivery")).then(begin(1, 2, "credit"))
    .then(cancel(1)).then(complete(2, "accept")).then(use(2))
    .expect(state.credited == Set(1) and safety)

  run shouldNotDeliverWhenRejectedTest = ready
    .then(begin(1, 1, "delivery")).then(complete(1, "reject")).then(use(1))
    .expect(state.lastEffect == NO_EFFECT and safety)

  run shouldNotDeliverWhenIgnoredTest = ready
    .then(begin(1, 1, "delivery")).then(complete(1, "ignore")).then(use(1))
    .expect(state.lastEffect == NO_EFFECT and safety)

  run shouldRejectLateAuthenticationWhenGenerationIsClosedTest = ready
    .then(close(1)).then(open(1, 2))
    .expect(state.sessions.get(2).status == "unauthenticated" and safety)
    .then(authenticate(1).fail())

  run shouldNotUseRetainedHistoryWhenReplacementIsUnauthenticatedTest = ready
    .then(begin(1, 1, "credit")).then(complete(1, "accept")).then(use(1))
    .then(begin(1, 2, "delivery")).then(close(1)).then(open(1, 2))
    .then(complete(2, "accept")).then(use(2))
    .expect(state.credited == Set(1) and state.lastEffect == NO_EFFECT and safety)

  run shouldRejectUseWhenValidationIsPendingTest = ready
    .then(begin(1, 1, "delivery")).expect(state.lastEffect == NO_EFFECT and safety)
    .then(use(1).fail())

  run shouldRejectDuplicateUseWhenEffectAlreadyOccurredTest = ready
    .then(begin(1, 1, "delivery")).then(complete(1, "accept")).then(use(1))
    .expect(state.lastEffect.operation == 1 and safety).then(use(1).fail())

  run shouldNotRecycleGenerationWhenOldCallbacksMayExistTest = ready
    .then(close(1)).expect(state.current.get(1) == 0 and safety).then(open(1, 1).fail())

  run shouldPreserveEarlierSuccessWhenSessionClosesTest = ready
    .then(begin(1, 1, "delivery")).then(complete(1, "accept")).then(use(1))
    .then(close(1)).expect(state.lastEffect.session == 1 and safety)
}
