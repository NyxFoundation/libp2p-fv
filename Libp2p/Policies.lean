module

public import Std

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

-- Scores are exact integer reference units, not IEEE floating-point results.
def p1 (meshTime quantum cap : Nat) : Nat := min (meshTime / quantum) cap

def creditFirst (counter cap : Nat) : Nat := min (counter + 1) cap

def deficit (meshTime activation deliveries threshold : Nat) : Nat :=
  if meshTime ≤ activation then 0 else (threshold - deliveries) ^ 2

-- Resolve the source ambiguity by requiring both negative-score pruning and active deficit.
def p3b (old meshTime activation deliveries threshold : Nat)
    (negativeScorePrune : Bool) : Nat :=
  if negativeScorePrune then old + deficit meshTime activation deliveries threshold else old

def squaredPenalty (counter : Nat) : Nat := counter ^ 2

def colocation (count threshold : Nat) : Nat := (count - threshold) ^ 2

def decay (counter numerator denominator zeroCutoff : Nat) : Nat :=
  let next := counter * numerator / denominator
  if next < zeroCutoff then 0 else next

structure TopicScore where
  weight : Int
  w1 : Int
  w2 : Int
  w3 : Int
  w3b : Int
  w4 : Int
  p1 : Nat
  p2 : Nat
  p3 : Nat
  p3b : Nat
  p4 : Nat
  deriving Repr

def TopicScore.value (t : TopicScore) : Int :=
  t.weight * (t.w1 * t.p1 + t.w2 * t.p2 + t.w3 * t.p3 +
    t.w3b * t.p3b + t.w4 * t.p4)

def totalScore (topics : List TopicScore) (topicCap : Option Int)
    (appWeight appScore ipWeight behaviorWeight : Int) (ip behavior : Nat) : Int :=
  let topicSum := (topics.map TopicScore.value).foldl (· + ·) 0
  let capped := match topicCap with | none => topicSum | some cap => min topicSum cap
  capped + appWeight * appScore + ipWeight * ip + behaviorWeight * behavior

-- Equality is intentionally rejected, choosing the source's "exceeds" wording.
def acceptPX (score threshold : Int) : Bool := decide (score > threshold)

def validQuotas (d low outbound : Nat) : Bool :=
  decide (outbound < low ∧ 2 * outbound ≤ d)

def eligibleGraft (score : Int) (explicit backoff full outbound : Bool) : Bool :=
  decide (0 ≤ score) && !explicit && !backoff && (!full || outbound)

theorem creditFirst_capped (n cap : Nat) : creditFirst n cap ≤ cap := by
  exact Nat.min_le_right _ _

theorem deficit_inactive (time activation deliveries threshold : Nat)
    (h : time ≤ activation) : deficit time activation deliveries threshold = 0 := by
  simp [deficit, h]

theorem deficit_satisfied (time activation deliveries threshold : Nat)
    (h : threshold ≤ deliveries) : deficit time activation deliveries threshold = 0 := by
  simp [deficit, Nat.sub_eq_zero_of_le h]

theorem p3b_no_unrelated_prune (old time activation deliveries threshold : Nat) :
    p3b old time activation deliveries threshold false = old := by simp [p3b]

theorem colocation_below_threshold (count threshold : Nat) (h : count ≤ threshold) :
    colocation count threshold = 0 := by simp [colocation, Nat.sub_eq_zero_of_le h]

theorem decay_nonincreasing (n num den cutoff : Nat) (h : num ≤ den) (hd : 0 < den) :
    decay n num den cutoff ≤ n := by
  dsimp only [decay]
  split
  · omega
  · apply (Nat.div_le_iff_le_mul_add_pred hd).2
    have hm : n * num ≤ den * n := by
      simpa [Nat.mul_comm] using Nat.mul_le_mul_left n h
    omega

theorem acceptPX_equality (score : Int) : acceptPX score score = false := by simp [acceptPX]

theorem no_inbound_oversubscription (score : Int) (explicit backoff : Bool) :
    eligibleGraft score explicit backoff true false = false := by simp [eligibleGraft]

end Libp2p
