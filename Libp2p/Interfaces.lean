module

public import Libp2p.PipelineSafety
public import Libp2p.Policies
public import Libp2p.Handshake

@[expose] public section
namespace Libp2p

/-- Results supplied by a selected decoder, not an implementation of that decoder.
`framingValid` does not choose an outer prefix format or borrow Req/Resp rules. -/
structure DecodedRPC where
  declaredLength : Nat
  localLimit : Nat
  complete : Bool
  framingValid : Bool
  schemaValid : Bool
  envelope : Envelope
  deriving DecidableEq, Repr

def DecodedRPC.wellFormed (rpc : DecodedRPC) : Bool :=
  lengthAdmissible rpc.declaredLength rpc.localLimit rpc.complete rpc.framingValid &&
    rpc.schemaValid && rpc.envelope.strictNoSign

theorem DecodedRPC.wellFormed_iff (rpc : DecodedRPC) : rpc.wellFormed = true ↔
    rpc.declaredLength ≤ rpc.localLimit ∧ rpc.complete ∧ rpc.framingValid ∧ rpc.schemaValid ∧
    rpc.envelope.from = none ∧ rpc.envelope.seqno = none ∧
    rpc.envelope.signature = none ∧ rpc.envelope.key = none := by
  simp [wellFormed, lengthAdmissible, Envelope.strictNoSign, and_assoc]

/-- One ownership map is shared by the receiver and its consumers. The primitive
certificate/decoder results must describe these actual sessions and tasks. -/
structure ProfileInputs (Session Peer Stream Task Object Context MessageId Protocol : Type) where
  expected : Session → Peer
  certificatePeer : Session → Peer
  checks : Session → AuthChecks
  certificate : Session → Handshake.CertificateFields (List UInt8)
  deprecatedPolicy : Session → Handshake.DeprecatedFieldPolicy
  supportedProtocol : Protocol
  owner : Stream → Session
  inbound : Stream → Bool
  supportsExtensions : Stream → Bool
  source : Task → Stream
  payload : Task → Object
  scope : Task → Context
  key : Task → MessageId
  decoded : Task → DecodedRPC

variable {S P I W O C ID Protocol V : Type}

def ProfileInputs.pipelineTheory (input : ProfileInputs S P I W O C ID Protocol) :
    Pipeline.Theory S P I W O C ID Protocol V where
  expected := input.expected
  certificatePeer := input.certificatePeer
  certificateChecks := fun s => Handshake.acceptCertificate (input.checks s).accept
    (input.deprecatedPolicy s) (input.certificate s)
  supportedProtocol := input.supportedProtocol
  owner := input.owner
  inbound := input.inbound
  supportsExtensions := input.supportsExtensions
  source := input.source
  payload := input.payload
  scope := input.scope
  key := input.key

theorem ProfileInputs.certificate_checks (input : ProfileInputs S P I W O C ID Protocol)
    (s : S) (passed : (input.pipelineTheory (V := V)).certificateChecks s = true) :
    (input.checks s).accept = true ∧
      Handshake.deprecatedFieldsAllowed (input.deprecatedPolicy s) (input.certificate s) = true := by
  exact Bool.and_eq_true_iff.mp passed

end Libp2p
