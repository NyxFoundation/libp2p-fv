import Libp2p.Policies

open Libp2p

private def validChecks : AuthChecks := ⟨true, true, true, true, true, true, true, true, true, true, true⟩

#guard validChecks.accept
#guard !{ validChecks with singleCertificate := false }.accept
#guard !{ validChecks with notBeforeValid := false }.accept
#guard !{ validChecks with notAfterValid := false }.accept
#guard !{ validChecks with selfSignatureValid := false }.accept
#guard !{ validChecks with libp2pExtensionPresent := false }.accept
#guard !{ validChecks with criticalExtensionsKnown := false }.accept
#guard !{ validChecks with keyEncodingValid := false }.accept
#guard !{ validChecks with bindingSignatureValid := false }.accept
#guard !{ validChecks with tls13 := false }.accept
#guard !{ validChecks with clientAuthenticated := false }.accept
#guard !{ validChecks with libp2pAlpn := false }.accept

#guard peerIdCodec 42 == .identity
#guard peerIdCodec 43 == .sha256
#guard bindingInput [1, 2] != bindingInput [1, 3]
#guard Envelope.strictNoSign ⟨none, none, none, none⟩
#guard !Envelope.strictNoSign ⟨some [], none, none, none⟩
#guard !Envelope.strictNoSign ⟨none, some [], none, none⟩
#guard !Envelope.strictNoSign ⟨none, none, some [], none⟩
#guard !Envelope.strictNoSign ⟨none, none, none, some []⟩
#guard lengthAdmissible 1024 1024 true true
#guard !lengthAdmissible 1025 1024 true true
#guard !lengthAdmissible 1 1024 false true
#guard !lengthAdmissible 1 1024 true false
#guard !lengthAdmissible (2 ^ 64) 1024 true true

#guard p1 100 10 4 == 4
#guard creditFirst 4 4 == 4
#guard creditFirst 0 4 == 1
#guard deficit 10 10 0 4 == 0
#guard deficit 11 10 2 4 == 4
#guard deficit 11 10 4 4 == 0
#guard p3b 7 11 10 2 4 false == 7
#guard p3b 7 11 10 2 4 true == 11
#guard p3b 7 10 10 2 4 true == 7
#guard squaredPenalty 3 == 9
#guard colocation 4 4 == 0
#guard colocation 7 4 == 9
#guard decay 100 9 10 1 == 90
#guard decay 1 9 10 1 == 0
#guard !acceptPX 10 10
#guard acceptPX 11 10
#guard validQuotas 6 4 2
#guard !validQuotas 6 4 4
#guard !validQuotas 6 3 3
#guard !eligibleGraft 1 false false true false
#guard eligibleGraft 1 false false true true
#guard !eligibleGraft (-1) false false false true
#guard !eligibleGraft 1 true false false true
#guard !eligibleGraft 1 false true false true

private def positiveTopic : TopicScore := ⟨2, 1, 1, -1, -1, -1, 2, 3, 0, 0, 0⟩
#guard positiveTopic.value == 10
#guard totalScore [positiveTopic] (some 4) 1 3 (-2) (-3) 2 1 == 0
#guard totalScore [] none 1 3 (-2) (-3) 2 1 == -4
