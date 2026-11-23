module

public import Std

@[expose] public section
namespace Libp2p.Handshake

/-!
Policy projections for A-01.08 and N-03.02 in `libp2p-veil-v13-reference`.

Sources:
* https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/tls/tls.md#peer-authentication
* https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/connections/README.md#opening-new-streams-over-a-connection
* https://github.com/multiformats/multistream-select/blob/9a1fbe8edadebea223f47102f1913b8026c23a1c/README.md#protocol

These functions do not implement TLS, ASN.1, multistream framing, or handler I/O.
`Core` abstracts the other certificate fields; it is not a serialized certificate.
Exact protocol equality is the selected profile's policy, not a restriction on
libp2p's permitted custom match functions or a claim about Ethereum N-03.01.
-/

/-- A field-level projection; `some []` is still a present deprecated BIT STRING. -/
structure CertificateFields (Core : Type) where
  core : Core
  subjectUniqueId : Option (List Bool)
  issuerUniqueId : Option (List Bool)
  deriving DecidableEq, Repr

/-- The local construction path has no input for the deprecated fields. -/
def localCertificate (core : Core) : CertificateFields Core :=
  ⟨core, none, none⟩

theorem localCertificate_omits_uniqueIds (core : Core) :
    (localCertificate core).subjectUniqueId = none ∧
    (localCertificate core).issuerUniqueId = none := by
  exact ⟨rfl, rfl⟩

theorem localCertificate_preserves_core (core : Core) :
    (localCertificate core).core = core := by
  rfl

/-- External ASN.1 operations; no implementation or correctness is supplied here. -/
structure CertificateEncoding (Core : Type) where
  serialize : CertificateFields Core → List UInt8
  subjectUniqueIdPresent : List UInt8 → Bool
  issuerUniqueIdPresent : List UInt8 → Bool

/-- The caller must establish this for its real serializer and ASN.1 field observers. -/
def CertificateEncoding.PreservesUniqueIds (encoding : CertificateEncoding Core) : Prop :=
  ∀ certificate,
    encoding.subjectUniqueIdPresent (encoding.serialize certificate) =
      certificate.subjectUniqueId.isSome ∧
    encoding.issuerUniqueIdPresent (encoding.serialize certificate) =
      certificate.issuerUniqueId.isSome

/-- Conditional interface result, not a theorem about any concrete ASN.1 bytes. -/
theorem serialized_localCertificate_omits_uniqueIds (encoding : CertificateEncoding Core)
    (correspondence : encoding.PreservesUniqueIds) (core : Core) :
    encoding.subjectUniqueIdPresent (encoding.serialize (localCertificate core)) = false ∧
    encoding.issuerUniqueIdPresent (encoding.serialize (localCertificate core)) = false := by
  exact correspondence (localCertificate core)

inductive DeprecatedFieldPolicy where
  | allow
  | reject
  deriving DecidableEq, Repr

/-- `allow` permits these fields only; it does not waive any other certificate check. -/
def deprecatedFieldsAllowed (policy : DeprecatedFieldPolicy)
    (certificate : CertificateFields Core) : Bool :=
  match policy with
  | .allow => true
  | .reject => certificate.subjectUniqueId.isNone && certificate.issuerUniqueId.isNone

/-- `otherChecksPassed` must come from all other required checks on this certificate. -/
def acceptCertificate (otherChecksPassed : Bool) (policy : DeprecatedFieldPolicy)
    (certificate : CertificateFields Core) : Bool :=
  otherChecksPassed && deprecatedFieldsAllowed policy certificate

theorem rejectPolicy_allows_iff (certificate : CertificateFields Core) :
    deprecatedFieldsAllowed .reject certificate = true ↔
      certificate.subjectUniqueId = none ∧ certificate.issuerUniqueId = none := by
  simp [deprecatedFieldsAllowed]

theorem acceptCertificate_requires_other_checks (checks : Bool)
    (policy : DeprecatedFieldPolicy) (certificate : CertificateFields Core)
    (accepted : acceptCertificate checks policy certificate = true) : checks = true := by
  exact (Bool.and_eq_true_iff.mp accepted).1

theorem failed_other_checks_reject (policy : DeprecatedFieldPolicy)
    (certificate : CertificateFields Core) : acceptCertificate false policy certificate = false := by
  simp [acceptCertificate]

theorem localCertificate_receiver_check (core : Core)
    (policy : DeprecatedFieldPolicy) (checks : Bool) :
    acceptCertificate checks policy (localCertificate core) = checks := by
  cases policy <;> simp [acceptCertificate, deprecatedFieldsAllowed, localCertificate]

theorem receiver_choice_on_present_uniqueId (certificate : CertificateFields Core)
    (present : certificate.subjectUniqueId ≠ none ∨ certificate.issuerUniqueId ≠ none) :
    acceptCertificate true .allow certificate = true ∧
    acceptCertificate true .reject certificate = false := by
  constructor
  · rfl
  · have absentImpossible : ¬ (certificate.subjectUniqueId = none ∧
        certificate.issuerUniqueId = none) := by
      intro absent
      rcases present with subject | issuer
      · exact subject absent.1
      · exact issuer absent.2
    have notAllowed : deprecatedFieldsAllowed .reject certificate ≠ true := by
      intro allowed
      exact absentImpossible ((rejectPolicy_allows_iff certificate).mp allowed)
    simpa [acceptCertificate] using Bool.eq_false_iff.mpr notAllowed

/-- MAY-reject preserves both choices when all independent checks pass. -/
theorem receiver_neither_mandatory_reject_nor_accept (certificate : CertificateFields Core)
    (present : certificate.subjectUniqueId ≠ none ∨ certificate.issuerUniqueId ≠ none) :
    ¬ (∀ policy, acceptCertificate true policy certificate = false) ∧
    ¬ (∀ policy, acceptCertificate true policy certificate = true) := by
  obtain ⟨allow, reject⟩ := receiver_choice_on_present_uniqueId certificate present
  constructor
  · intro allReject
    have contradiction := (allReject .allow).symm.trans allow
    cases contradiction
  · intro allAccept
    have contradiction := (allAccept .reject).symm.trans reject
    cases contradiction

/-- An abstract response, not a wire encoding or a running handler. -/
inductive ProtocolSelection where
  | na
  | selected (protocol : String)
  deriving DecidableEq, Repr

/-- `supported` is the registered exact-ID handler set at this decision point. -/
def selectProtocol (supported : List String) (proposal : String) : ProtocolSelection :=
  if proposal ∈ supported then .selected proposal else .na

def ProtocolSelection.handlerProtocol : ProtocolSelection → Option String
  | .na => none
  | .selected protocol => some protocol

theorem unsupported_proposal_na (supported : List String) (proposal : String)
    (unsupported : proposal ∉ supported) : selectProtocol supported proposal = .na := by
  simp [selectProtocol, unsupported]

theorem supported_proposal_selected (supported : List String) (proposal : String)
    (available : proposal ∈ supported) :
    selectProtocol supported proposal = .selected proposal := by
  simp [selectProtocol, available]

theorem na_iff (supported : List String) (proposal : String) :
    selectProtocol supported proposal = .na ↔ proposal ∉ supported := by
  simp [selectProtocol]

theorem selected_iff (supported : List String) (proposal selected : String) :
    selectProtocol supported proposal = .selected selected ↔
      selected = proposal ∧ proposal ∈ supported := by
  by_cases available : proposal ∈ supported <;>
    simp [selectProtocol, available, eq_comm]

theorem handlerProtocol_iff (supported : List String) (proposal handler : String) :
    (selectProtocol supported proposal).handlerProtocol = some handler ↔
      handler = proposal ∧ proposal ∈ supported := by
  by_cases available : proposal ∈ supported <;>
    simp [selectProtocol, ProtocolSelection.handlerProtocol, available, eq_comm]

theorem no_substituted_handler (supported : List String) (proposal handler : String)
    (different : handler ≠ proposal) :
    (selectProtocol supported proposal).handlerProtocol ≠ some handler := by
  intro selected
  exact different ((handlerProtocol_iff supported proposal handler).mp selected).1

theorem unsupported_proposal_no_handler (supported : List String) (proposal : String)
    (unsupported : proposal ∉ supported) :
    (selectProtocol supported proposal).handlerProtocol = none := by
  rw [unsupported_proposal_na supported proposal unsupported]
  rfl

end Libp2p.Handshake
