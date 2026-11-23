module

public import Libp2p.TemporalBackoff
public import Libp2p.TemporalLimits
public import Libp2p.TemporalCredit
public import Libp2p.TemporalRetention
public import Libp2p.TemporalCausality
public import Libp2p.TemporalKnowledge
public import Libp2p.TemporalWitness

/-! Independent temporal specification components. These imports do not provide a
composition with Pipeline, Routing, or numerical score policies. Each component
uses fresh occurrence tokens and has no global time/step bound. TemporalKnowledge
and TemporalWitness add the causal-permission layer for M-06.04: an
observation-filtered admissible-history relation (not a receiver oracle) plus
the indistinguishable history pair witness. -/
