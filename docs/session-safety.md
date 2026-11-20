---
title: Session Authority Safety Checks
last_updated: 2026-11-06
tags:
  - formal-verification
  - libp2p
  - model-checking
  - quint
---
# Session Authority Safety Checks

## Result

`abstract-session-v1` satisfies the R-03.01/R-04.01 historical monitors in five
finite Quint/TLC instances. Twenty deterministic scenarios and two guard-removal
mutants test non-vacuity. This completes the first agreed milestone, **not an
unbounded proof, an implementation proof, or the remaining inventory**. Lean and
Tamarin are deferred; Apalache supplies translation/TLC, not a symbolic proof.

[R-03/R-04](properties/composition.md#r-03) are derived design contracts (D), not
wire requirements. Provenance: `libp2p/specs@c750236de43cd8b246a824b377dfdb26bae686db`,
connection lifecycle events; GossipSub v1.1 motivates retained Peer history.
This is an abstract lifecycle profile, not a complete deployment profile.

## Reproduce and inspect

In a Git checkout on Linux with Git, Node.js 24/npm, and Java 21+:

```sh
npm ci
npm run test:coverage
npm run verify
```

The lockfile pins Quint 0.33.1 and dependencies; no global Quint is required.
First verification downloads/unpacks Apalache 0.62.4 (183 MiB); allow network
access and several minutes. Before launching it, the runner verifies SHA-256:

- JAR: `e5223915507b65cc5f1638bd037ede60f8a4fc1644aff46355779f9b05df9262`
- Linux launcher: `f8d4643705369d0642d9345a479e7cc8b7929710dc966e7f9a374bf03e526fe4`

It also requires translator version/build 0.62.4/7954daf. `QUINT_HOME` selects the
cache. The verified JAR overrides launcher settings; translator heap is 1 GiB.
TLC uses 2 GiB, an 8 MiB stack, and one worker (`models/session-safety/tlc.json`).
Each command has a ten-minute deadline with process-group termination; log reads
are capped at 16 MiB. Fresh local endpoints avoid adopting an existing server.
A release/bind race can fail a run, not pass without observed pinned translator
output; use isolated runners and rerun on contention.

**Upstream warning:** recorded Java emits a protobuf reflection gencode warning
(GHSA-h4h5-3hr4-j3g2). This is a tool dependency, not production libp2p code.
Use an isolated environment with inbound access blocked; never expose its gRPC
server to untrusted clients. The warning is retained, not suppressed/fixed here.

The runner type-checks, tests scenarios, checks all instances, and requires both
mutant counterexamples. Errors, incomplete exploration, unexpected violations,
checksum/version mismatches, or changed inputs fail the run. No trace bound,
symmetry reduction, or state constraint is used.

`.artifacts/session-safety/<timestamp>/` records commands, tools, HEAD/dirty flag,
exact input hashes, and logs. Parser/linter chatter and home paths are removed;
all trace states, warnings, completion/collision records remain. Quint's TLC
backend does not export ITF. Failed runs are not passed evidence. Dirty HEAD is
intentional for pre-commit captures: hashes identify the actual inputs.

[Published evidence](../evidence/session-safety/summary.json) retains TLC excerpts
and translator identity per instance; `translator.log` retains shared startup
warnings. Complete per-instance logs are generated/CI artifacts. To refresh after
changing inputs, run verification, then
`node scripts/publish-session-evidence.mjs <evidence-directory>` with its printed
directory. `npm test` checks captured hashes and reclassifies logs. The
[CI workflow](../.github/workflows/session-safety.yml) repeats checks and uploads
only JSON/log artifacts, including on failure. Unit thresholds are 80% for the
classification/subprocess helpers; real verification exercises the CLI end-to-end.
A corrupt-cache test verifies rejection before the launcher executes.

## Semantics and obligations

Source: [lifecycle.qnt](../models/session-safety/lifecycle.qnt).

- An immutable Peer and fresh generation identify each session; at most one
  session is current per Peer. `open` is unauthenticated, `authenticate` consumes
  external success, and `close` is terminal (disconnect/auth failure/fail-stop).
  Closed generations cannot consume late authentication.
- `begin` binds a session-scoped operation to its generation and effect kind:
  delivery, delivery credit, or handler installation. `complete` returns
  ACCEPT/REJECT/IGNORE even after cancel/close; handler ACCEPT abstracts negotiation.
- `cancel` linearizes cancellation, including after completion but before use.
  It need not erase callbacks or eventually clean up.
- `use` atomically checks authority, then emits once or consumes/drops work.
  ACCEPT, non-cancellation, and an authenticated current original generation are
  required. Pending/failed/ignored/consumed work cannot emit. Implementation of
  this atomic check-and-effect remains an open correspondence obligation.
- `credited` is Peer-keyed Boolean history, not a score equation. It survives
  close without granting authority. Later close/cancel cannot invalidate earlier
  success retroactively. Stuttering imposes no fairness/progress requirement.

| Child / monitor | At every emitted effect |
| --- | --- |
| R-03.01 / `cancellationSafe` | The originating operation was not cancelled. |
| R-04.01 / `generationSafe` | Its original generation was authenticated/current. |

`safety` conjoins these monitors. Violation flags are monotone pre-state history,
independent of optional guards. R-04.01's R-03.01 dependency is checked here.

Auth, certificate/Peer ID derivation, crypto, QUIC bytes, parsing, negotiation and
validation internals are external interfaces, not proved implementation facts.
An immutable operation token is not proved equivalent to real bytes, topic/fork,
buffer ownership, or reused message-ID caches. R-03.02/R-04.02 are **not discharged**;
retained-history scenarios only support tests. No A-05 proof is imported.
Concurrent sessions for one Peer, clocks, numerical/negative score policies,
allocation, 0-RTT replay, version/options and Ethereum fork rules are absent.
Only session-scoped authority is checked, not independently justified Peer-wide
scoring. E-07.02 correspondence is open. Availability, liveness, DoS resistance
and aggregate resource bounds remain excluded.

## Finite evidence

[instances.qnt](../models/session-safety/instances.qnt) fixes non-empty positive-ID
sets; zero is inert. Slots are **total lifetime allocations**, not concurrent
capacity, and are never recycled. Exhaustion disables allocation, not late work
or stuttering. Arbitrary reconnections, wraparound, and reclamation/reuse are not
covered. All three effect kinds and verdicts are explored in each instance.

| Module | Peers | Generations | Operations | Distinct states | Graph depth |
| --- | ---: | ---: | ---: | ---: | ---: |
| `single` | 1 | 1 | 1 | 91 | 8 |
| `reconnect` | 1 | 2 | 2 | 36,666 | 15 |
| `peers` | 2 | 2 | 2 | 153,785 | 15 |
| `generations` | 2 | 3 | 2 | 1,649,055 | 17 |
| `concurrent` | 1 | 2 | 3 | 2,773,940 | 19 |

All completed with zero states queued: finite reachable-state exploration, not
bounded-length Apalache checking. TLC fingerprint collisions remain possible;
optimistic estimates reach about `2.0e-6`. Exact estimates/seeds are logged, not
crypto bounds. Translation, tools/JVM and abstract interfaces are trusted.
No cutoff or unbounded theorem is claimed.

[Twenty scenarios](../models/session-safety/scenarios.qnt) cover successful
current/new-session effects, independent Peers/work, retained history, cancel and
close races, stale callbacks/auth, REJECT/IGNORE, pending/duplicate use and no ID
recycling. The same transitions with one guard disabled must yield:

| Mutant | Expected violation | Witness states including initialization |
| --- | --- | ---: |
| `missingCancellationGuard` | `cancellationSafe` | 7 |
| `missingGenerationGuard` | `generationSafe` | 9 |

The runner requires concrete trace states and the intended monitor becoming true;
unrelated tool errors do not count. Each result records `expected`; overall
`passed` means all expectations met, not that mutants satisfied safety.
Normal witnesses rule out a model that is safe only because it never emits.

Development failures were not evidence: an initial download timed out before TLC;
four tests read state after `.fail()`, which assigns no next state. Setup was
retried and those tests corrected; the published run passes.

Next stages remain deferred: N-05, GossipSub validation/deduplication, then control/
scoring. Each needs a new profile/evidence. Evaluate Apalache for scale; Tamarin
identity/replay and Lean generalization/cross-tool composition are separate work.
