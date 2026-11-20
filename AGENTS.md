# Repository guidance

## Status and workflow

- This is a research proposal and safety-obligation inventory, not a verified
  implementation. All obligations are currently proposed, not proved or checked.
- No tracked implementation, formal models, dependency manifests, CI workflows,
  or build/test/lint commands exist. Tool selection is a proposal, not a runnable
  workflow; untracked dependencies and checker output do not establish one.
- `inventory.md` covers Ethereum GossipSub over QUIC through Snappy/SSZ and gossip
  validation. `docs/verification-tool-selection.md` is narrower: its proposed
  tooling covers the libp2p subset, excluding Ethereum-specific rules, Snappy/SSZ,
  and verification of a particular implementation.

## Editing obligations

- Keep `inventory.md`'s index, counts, and exclusions consistent with the child
  tables in `docs/properties/`. Preserve stable parent/child IDs such as `A-01`
  and `A-01.01`; excluded IDs retain traceability, not active coverage.
- Each child has ID, Premise, Event, Required conclusion, Basis, and Depends on.
  Keep counterexample scenarios separate from the propositions.
- Preserve S (specification-derived), D (additional design/composition), and K
  (conditional cryptographic) classifications. Retain MUST/SHOULD/MAY strength,
  optionality, version gates, and exceptions; design goals are not wire rules.
- A bare parent dependency means all applicable children conjunctively. A dash
  means no inventory dependency, not absence of external assumptions.
- Safety scope excludes availability, dissemination, DoS resistance, aggregate
  memory/CPU bounds, and full consensus/execution validity. Local input bounds,
  required object signatures/proofs, and stale-session safety remain included.

## Specification and evidence boundaries

- Use the inventory's immutable source snapshots and an explicit selected
  profile. Ethereum obligations require complete ordered checks per topic/fork;
  Phase 0 examples are not coverage of later forks or generic libp2p requirements.
- Outer RPC framing, AcceptPXThreshold equality, and the P3b pruning trigger are
  recorded unresolved boundaries. Resolve them for the selected profile rather
  than borrowing Req/Resp framing rules or silently inventing defaults.
- Forwarding Peer ID, object signer, and original publisher are distinct.
  StrictNoSign omits envelope signatures, not required object signatures;
  gossip ACCEPT does not establish full consensus validity.
- Distinguish simulation, finite TLC exploration, bounded/inductive Apalache
  results, symbolic Tamarin analysis, inherited assumptions, and Lean proofs.
  Record revisions, profile, bounds, assumptions, and incomplete checks. Cross-tool
  composition and implementation claims need explicit event/refinement mappings;
  shared obligation names or source citations are not proof.

## Documentation format

- Markdown under `docs/` uses YAML frontmatter: `title` matching the H1,
  `last_updated` in YYYY-MM-DD form (refresh on content changes), and `tags` as a
  block list of lowercase kebab-case values. Root README and inventory omit it.
