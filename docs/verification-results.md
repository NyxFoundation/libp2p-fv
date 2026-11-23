---
title: Veil Integration Verification Results
last_updated: 2026-11-23
tags:
  - formal-verification
  - libp2p
  - verification
  - veil
---
# Veil Integration Verification Results

## Delivered artifact

The integration extends the reference models with exact-rational scoring,
selection, certificate/protocol policies, temporal relations, and coupled
Pipeline/Cache/Routing transitions. It is not a completed proof of the original
inventory or a production implementation.

Core and Network use transactions over the real Veil-generated component
transitions. The checked projections and event properties cover validation
authority, current sessions, cache replies, shared publication IDs and expiry,
score-threshold classification, and mesh selection effects. Network tests include
reachable receive/validate/forward, cached reply after source disconnect,
publication/expiry/republication, and negative admission/forwarding scenarios.

## Integration repairs

- Integrate the repaired `Tests/Network.lean`: correct transaction shapes,
  dispatched-stream preconditions, heartbeat expectations, validation authority
  arguments and negative traces. Check that arrival alone does not insert a
  cached payload or change seen/publication state.
- Run every Lean test recursively under `Tests/`, rather than a fixed partial
  list. This includes both nested Routing tests and the Network test.
- Rerun all eight finite component models and all `*Safety.lean` proof modules.
- Import all 38 library modules transitively into `Tests/Axioms.lean`, including
  Network selection/publication, and require the main Network theorem names.
- Replace ScoreHistory tests' native evaluation oracle with `decide +kernel`.
  Remove their broad private/native axiom exemptions. The test-local audit now
  checks every test theorem's transitive dependencies against the same three
  standard axioms; the main audit separately checks library declarations.

The twelve accidentally copied prerequisite files in the numerics child were
restored with explicit user approval after byte comparison with the parent and
inspection of the pre-task patch. All other child source hashes were preserved.
Only the repaired Network test was copied from that child during recovery.

## Reproduce

Use the pinned Lean 4.35.0 toolchain and Veil revision
`578ec0b77a0936cb502e15bdb468047211abd6b9`, with the dependencies in the README.

```sh
python3 scripts/verify.py
python3 scripts/check_coverage.py --require-complete
```

The verification command allows 3,600 seconds per subprocess; CI allows 120
minutes including dependency builds. The integration run completed under the
previous, stricter 1,800-second subprocess limit with `LEAN_NUM_THREADS=2`.

The verification command writes one log per step to `verification-output/`.
It includes the build, fresh component exploration and VCs, reachability proofs,
all Lean tests, an axiom audit, three injected proof-hole rejection controls,
protocol-guard mutations, and Python tests. A build cache alone is not evidence
that those checks ran. CI uses the same command and uploads logs on failure too.

Checks repeated during integration on 2026-11-23:

| Command | Result |
| --- | --- |
| `LEAN_NUM_THREADS=2 python3 scripts/verify.py` | Exit 0: eight component models (12 finite instances), seven safety proof modules, all 12 Lean tests, proof-hole controls, protocol mutations and Python tests |
| `lake lean Tests/Axioms.lean` | 5,249 library theorems; only `propext`, `Classical.choice`, `Quot.sound` |
| `lake lean Tests/Network.lean` | Reachable and negative traces pass; 1,445 test theorems pass the standard-axiom audit |
| `lake lean Tests/ScoreHistory.lean` | 64 test theorems pass the standard-axiom audit, including rational-value witnesses |
| `python3 -m unittest discover -s Tests -p 'test_*.py'` | 18 tests pass |
| `python3 scripts/check_coverage.py --require-complete` | 160 entries accounted for: 91 kernel-model, 30 external, 38 out-of-scope, one disabled |
| Mutation controls | Positive single-task and two-task collision controls pass; validation, stale-session and dedup bypasses each produce the expected counterexample |
| `actionlint .github/workflows/verify.yml` | Pass |
| `git diff --check` | Pass |

The publication's full-gate and review results are recorded in
[PR #8](https://github.com/NyxFoundation/libp2p-fv/pull/8), tied to its revision.
The ledger result is bookkeeping, not discharge of the original propositions.

## Review provenance

Earlier worker results are not blanket approval of the integrated tree:

- Knowledge/permission layer: bonsai2 and gemini-3.8-flash each completed 11/11
  chunks. Findings about Lean's `module` header, apparent truncation at chunk
  boundaries and event-pulse overwrites were declined against compilation,
  complete source and the checked transition invariants.
- ScoreHistory helper: both reviewers stopped because the session baseline
  could not be captured; no findings were returned. That helper was unreviewed.
- Network library handover: the worker's review-round budget was exhausted;
  the five-file library handover was explicitly panel-unreviewed.
- Network test repair: both reviewers stopped before invocation at baseline
  capture; a subsequent reminder also reported the exhausted reminder budget.
  No findings were returned and no approval was claimed.
- Previous parent close-out: both reviewers stopped after the reminder budget,
  with no invocation and no findings. The resumed integration needs its own
  disclosed review outcome; compilation does not replace it.

## Boundaries not discharged

1. Network accepts externally supplied rational score snapshots. ScoreHistory
   proves numeric updates over TemporalRetention, but no event mapping binds
   those histories to Network's `refreshScores` inputs.
2. Backoff, limits, credit and causal-permission components are not all coupled
   into Network. The observation-level permission relation is not a receiver
   algorithm or a proof that a receiver can detect every forbidden history.
3. Network has kernel-checked scenarios and parameterized projection/event
   proofs, not exhaustive finite exploration of the combined system. The eight
   component explorations are not whole-system exploration.
4. QUIC/TLS, cryptographic checks, ASN.1/outer framing/decoder correspondence and
   application verdicts remain external contracts. Ethereum, Snappy/SSZ and
   correspondence to production code remain outside the selected profile.

These limits prevent claiming the original full libp2p-scope completion goal.
They are not removed by relabeling ledger entries or by solver success.
