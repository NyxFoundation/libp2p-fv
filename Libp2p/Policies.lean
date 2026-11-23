module

public import Std
public import Init.Data.Rat.Lemmas

@[expose] public section
namespace Libp2p

structure AuthChecks where
  singleCertificate : Bool
  notBeforeValid : Bool
  notAfterValid : Bool
  selfSignatureValid : Bool
  libp2pExtensionPresent : Bool
  criticalExtensionsKnown : Bool
  keyEncodingValid : Bool
  bindingSignatureValid : Bool
  tls13 : Bool
  clientAuthenticated : Bool
  libp2pAlpn : Bool
  deriving DecidableEq, Repr

def AuthChecks.accept (c : AuthChecks) : Bool :=
  c.singleCertificate && c.notBeforeValid && c.notAfterValid &&
  c.selfSignatureValid && c.libp2pExtensionPresent && c.criticalExtensionsKnown &&
  c.keyEncodingValid && c.bindingSignatureValid && c.tls13 &&
  c.clientAuthenticated && c.libp2pAlpn

theorem AuthChecks.accept_iff (c : AuthChecks) : c.accept = true ↔
    c.singleCertificate ∧ c.notBeforeValid ∧ c.notAfterValid ∧
    c.selfSignatureValid ∧ c.libp2pExtensionPresent ∧ c.criticalExtensionsKnown ∧
    c.keyEncodingValid ∧ c.bindingSignatureValid ∧ c.tls13 ∧
    c.clientAuthenticated ∧ c.libp2pAlpn := by
  simp [accept, and_assoc]

-- The argument must be the actual certificate SPKI, supplied by the ASN.1 interface.
def bindingInput (spki : List UInt8) : List UInt8 :=
  "libp2p-tls-handshake:".toUTF8.data.toList ++ spki

theorem bindingInput_injective {a b : List UInt8}
    (h : bindingInput a = bindingInput b) : a = b := by
  simpa [bindingInput] using h

inductive PeerIdCodec where
  | identity
  | sha256
  deriving DecidableEq, Repr

def peerIdCodec (serializedKeyLength : Nat) : PeerIdCodec :=
  if serializedKeyLength ≤ 42 then .identity else .sha256

theorem peerIdCodec_identity_iff (n : Nat) :
    peerIdCodec n = .identity ↔ n ≤ 42 := by
  simp [peerIdCodec]

structure Envelope where
  «from» : Option (List UInt8)
  seqno : Option (List UInt8)
  signature : Option (List UInt8)
  key : Option (List UInt8)
  deriving DecidableEq, Repr

def Envelope.strictNoSign (e : Envelope) : Bool :=
  e.from.isNone && e.seqno.isNone && e.signature.isNone && e.key.isNone

theorem Envelope.strictNoSign_iff (e : Envelope) : e.strictNoSign = true ↔
    e.from = none ∧ e.seqno = none ∧ e.signature = none ∧ e.key = none := by
  simp [strictNoSign, and_assoc]

-- A decoded length uses unbounded naturals; conversion into a host integer is external.
def lengthAdmissible (declared limit : Nat) (complete canonical : Bool) : Bool :=
  decide (declared ≤ limit) && complete && canonical

theorem lengthAdmissible_bound {n limit : Nat} {complete canonical : Bool}
    (h : lengthAdmissible n limit complete canonical = true) :
    n ≤ limit ∧ complete ∧ canonical := by
  simpa [lengthAdmissible, and_assoc] using h

def negotiationLength (protocol : List UInt8) : Nat := protocol.length + 1

theorem negotiation_includes_newline (protocol : List UInt8) :
    negotiationLength protocol = (protocol ++ [10]).length := by
  simp [negotiationLength]

theorem handoff_preserves_suffix (pre suffix : List UInt8) :
    (pre ++ suffix).drop pre.length = suffix := by simp

-- Duration division precedes the scalar cast, as in the source's pseudo-Go.
def p1 (meshTime quantum : Nat) (cap : Rat) : Rat := min (meshTime / quantum : Nat) cap

def creditFirst (counter cap : Rat) : Rat := min (counter + 1) cap

def deficit (meshTime activation : Nat) (deliveries threshold : Rat) : Rat :=
  if meshTime ≤ activation ∨ threshold ≤ deliveries then 0 else (threshold - deliveries) ^ 2

-- The selected profile requires negative-score pruning AND an active deficit.
def p3b (old : Rat) (meshTime activation : Nat) (deliveries threshold : Rat)
    (negativeScorePrune : Bool) : Rat :=
  if negativeScorePrune then old + deficit meshTime activation deliveries threshold else old

def squaredPenalty (counter : Rat) : Rat := counter ^ 2

def colocation (count threshold : Nat) : Rat := ((count - threshold) ^ 2 : Nat)

def decay (counter factor zeroCutoff : Rat) : Rat :=
  let next := counter * factor
  if next < zeroCutoff then 0 else next

structure TopicScore where
  weight : Rat
  w1 : Rat
  w2 : Rat
  w3 : Rat
  w3b : Rat
  w4 : Rat
  p1 : Rat
  p2 : Rat
  p3 : Rat
  p3b : Rat
  p4 : Rat
  deriving Repr

def TopicScore.value (t : TopicScore) : Rat :=
  t.weight * (t.w1 * t.p1 + t.w2 * t.p2 + t.w3 * t.p3 +
    t.w3b * t.p3b + t.w4 * t.p4)

def capScore (score : Rat) (cap : Option Rat) : Rat :=
  match cap with | none => score | some limit => min score limit

def topicScoreSum (topics : List TopicScore) : Rat :=
  (topics.map TopicScore.value).foldr (· + ·) 0

def totalScore (topics : List TopicScore) (topicCap : Option Rat)
    (appWeight appScore ipWeight behaviorWeight ip behavior : Rat) : Rat :=
  capScore (topicScoreSum topics) topicCap +
    appWeight * appScore + ipWeight * ip + behaviorWeight * behavior

-- Below-threshold rejection retains equality; PX instead selects "exceeds".
def atLeastThreshold (score threshold : Rat) : Bool := decide (threshold ≤ score)
def aboveThreshold (score threshold : Rat) : Bool := decide (threshold < score)
def acceptPX (score threshold : Rat) : Bool := aboveThreshold score threshold

-- Admission for an enabled mesh; the all-zero bootstrapper configuration is a separate mode.
def validQuotas (d low outbound : Nat) : Bool :=
  decide (outbound < low ∧ 2 * outbound ≤ d)

def eligibleGraft (score : Rat) (explicit backoff full outbound : Bool) : Bool :=
  atLeastThreshold score 0 && !explicit && !backoff && (!full || outbound)

theorem creditFirst_capped (n cap : Rat) : creditFirst n cap ≤ cap := by
  simp only [creditFirst, Rat.min_def]
  split
  · assumption
  · exact Rat.le_refl

theorem deficit_inactive (time activation : Nat) (deliveries threshold : Rat)
    (h : time ≤ activation) : deficit time activation deliveries threshold = 0 := by
  simp [deficit, h]

theorem deficit_satisfied (time activation : Nat) (deliveries threshold : Rat)
    (h : threshold ≤ deliveries) : deficit time activation deliveries threshold = 0 := by
  simp [deficit, h]

theorem p3b_no_unrelated_prune (old : Rat) (time activation : Nat) (deliveries threshold : Rat) :
    p3b old time activation deliveries threshold false = old := by simp [p3b]

theorem colocation_below_threshold (count threshold : Nat) (h : count ≤ threshold) :
    colocation count threshold = 0 := by simp [colocation, Nat.sub_eq_zero_of_le h]

theorem decay_nonincreasing (counter factor cutoff : Rat)
    (hc : 0 ≤ counter) (hf : factor ≤ 1) : decay counter factor cutoff ≤ counter := by
  dsimp only [decay]
  split
  · exact hc
  · simpa using Rat.mul_le_mul_of_nonneg_left hf hc

theorem acceptPX_equality (score : Rat) : acceptPX score score = false := by
  simp [acceptPX, aboveThreshold, Rat.lt_irrefl]

theorem no_inbound_oversubscription (score : Rat) (explicit backoff : Bool) :
    eligibleGraft score explicit backoff true false = false := by simp [eligibleGraft]

end Libp2p
