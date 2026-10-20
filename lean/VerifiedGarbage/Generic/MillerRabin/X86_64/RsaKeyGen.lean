module

public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.SharedVerified
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.SharedSafety
public import VerifiedGarbage.Spec.RsaKeyGen.Contract
public import VerifiedGarbage.Proof.Bignum.LazyMath
public import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
public import VerifiedGarbage.Proof.Bignum.X86_64.Copy
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp
public import VerifiedGarbage.Proof.Bignum.X86_64.Csub
public import VerifiedGarbage.Proof.Bignum.X86_64.Double
public import VerifiedGarbage.Proof.Bignum.X86_64.Exp
public import VerifiedGarbage.Proof.Bignum.X86_64.Loop
public import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
public import VerifiedGarbage.Proof.Bignum.X86_64.PubR2
public import VerifiedGarbage.Proof.Bignum.X86_64.R2
public import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
public import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
public import VerifiedGarbage.Proof.Bignum.X86_64.Row
public import VerifiedGarbage.Proof.Bignum.X86_64.Setup
public import VerifiedGarbage.Proof.Bignum.X86_64.Store
public import VerifiedGarbage.Proof.Bignum.X86_64.Template
public import VerifiedGarbage.Proof.Bignum.X86_64.Valid
public import VerifiedGarbage.Proof.Framework.RegSetOrder
public import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Proof.Framework.X86_64.Avx
public import VerifiedGarbage.Proof.Framework.X86_64.CallInlineRel
public import VerifiedGarbage.Proof.Framework.X86_64.Masked
public import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
public import VerifiedGarbage.Proof.Framework.X86_64.RelCT
public import VerifiedGarbage.Proof.Framework.X86_64.Sse
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Body
public import VerifiedGarbage.Proof.MillerRabin.X86_64.BodyKeeps
public import VerifiedGarbage.Proof.MillerRabin.X86_64.CT
public import VerifiedGarbage.Proof.MillerRabin.X86_64.CallBody
public import VerifiedGarbage.Proof.MillerRabin.X86_64.CallCT
public import VerifiedGarbage.Proof.MillerRabin.X86_64.CallCorrect
public import VerifiedGarbage.Proof.MillerRabin.X86_64.CallStack
public import VerifiedGarbage.Proof.MillerRabin.X86_64.CallTemplate
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Context
public import VerifiedGarbage.Proof.MillerRabin.X86_64.CoreFrame
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Correct
public import VerifiedGarbage.Proof.MillerRabin.X86_64.CorrectMath
public import VerifiedGarbage.Proof.MillerRabin.X86_64.ExitRegisters
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Finish
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Frame
public import VerifiedGarbage.Proof.MillerRabin.X86_64.FramedBody
public import VerifiedGarbage.Proof.MillerRabin.X86_64.FramedCall
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Frames
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Keeps
public import VerifiedGarbage.Proof.MillerRabin.X86_64.NormalizeCT
public import VerifiedGarbage.Proof.MillerRabin.X86_64.NormalizeContext
public import VerifiedGarbage.Proof.MillerRabin.X86_64.NormalizeValues
public import VerifiedGarbage.Proof.MillerRabin.X86_64.NormalizedPublic
public import VerifiedGarbage.Proof.MillerRabin.X86_64.RoundCT
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Stage
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Verified
public import VerifiedGarbage.Proof.Poly1305.Limbs64
public import VerifiedGarbage.Proof.RsaKeyGen.Bits
public import VerifiedGarbage.Proof.RsaKeyGen.CandMath
public import VerifiedGarbage.Proof.RsaKeyGen.MrMont
public import VerifiedGarbage.Proof.RsaKeyGen.Primes
public import VerifiedGarbage.Proof.RsaKeyGen.TrialMath
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Copy
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.GcdE
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.GcdStep
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.ModE
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MontAll
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MontRest
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrExp
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrMain
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrSel
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrSelW
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrWit
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Trial
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.TrialLoop
import VerifiedGarbage.Proof.Bignum.LazyMath
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp
import VerifiedGarbage.Proof.Bignum.X86_64.Csub
import VerifiedGarbage.Proof.Bignum.X86_64.Double
import VerifiedGarbage.Proof.Bignum.X86_64.Exp
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
import VerifiedGarbage.Proof.Bignum.X86_64.PubR2
import VerifiedGarbage.Proof.Bignum.X86_64.R2
import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.Setup
import VerifiedGarbage.Proof.Bignum.X86_64.Store
import VerifiedGarbage.Proof.Bignum.X86_64.Template
import VerifiedGarbage.Proof.Bignum.X86_64.Valid
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.CallInlineRel
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.MillerRabin.X86_64.Body
import VerifiedGarbage.Proof.MillerRabin.X86_64.BodyKeeps
import VerifiedGarbage.Proof.MillerRabin.X86_64.CT
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallBody
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallCT
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallCorrect
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallStack
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallTemplate
import VerifiedGarbage.Proof.MillerRabin.X86_64.Context
import VerifiedGarbage.Proof.MillerRabin.X86_64.CoreFrame
import VerifiedGarbage.Proof.MillerRabin.X86_64.Correct
import VerifiedGarbage.Proof.MillerRabin.X86_64.CorrectMath
import VerifiedGarbage.Proof.MillerRabin.X86_64.ExitRegisters
import VerifiedGarbage.Proof.MillerRabin.X86_64.Finish
import VerifiedGarbage.Proof.MillerRabin.X86_64.Frame
import VerifiedGarbage.Proof.MillerRabin.X86_64.FramedBody
import VerifiedGarbage.Proof.MillerRabin.X86_64.FramedCall
import VerifiedGarbage.Proof.MillerRabin.X86_64.Frames
import VerifiedGarbage.Proof.MillerRabin.X86_64.Keeps
import VerifiedGarbage.Proof.MillerRabin.X86_64.NormalizeCT
import VerifiedGarbage.Proof.MillerRabin.X86_64.NormalizeContext
import VerifiedGarbage.Proof.MillerRabin.X86_64.NormalizeValues
import VerifiedGarbage.Proof.MillerRabin.X86_64.NormalizedPublic
import VerifiedGarbage.Proof.MillerRabin.X86_64.RoundCT
import VerifiedGarbage.Proof.MillerRabin.X86_64.Stage
import VerifiedGarbage.Proof.MillerRabin.X86_64.Verified
import VerifiedGarbage.Proof.Poly1305.Limbs64
import VerifiedGarbage.Proof.RsaKeyGen.Bits
import VerifiedGarbage.Proof.RsaKeyGen.CandMath
import VerifiedGarbage.Proof.RsaKeyGen.MrMont
import VerifiedGarbage.Proof.RsaKeyGen.Primes
import VerifiedGarbage.Proof.RsaKeyGen.TrialMath
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Copy
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.GcdE
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.GcdStep
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.ModE
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MontAll
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MontRest
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrExp
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrMain
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrSel
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrSelW
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrWit
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Trial
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.TrialLoop

/-! # Emit RSA candidates for every shared Miller–Rabin backend -/

@[expose] public section

namespace VG.Generic.MillerRabin.X86_64.RsaKeyGen

def artifacts (v : Proof.MillerRabin.X86_64.RoundImpl) : List Artifact := [
  Spec.RsaKeyGen.candidateApi.artifact X86_64.target {
    suffix := v.suffix
    notes := ["The candidate checks retain RSA's witness selection and retry policy. Each \
        prepared witness calls the shared `vg_miller_rabin_round`, using fixed four-bit windows \
        and the selected verified Montgomery backend. Branches release only the checks and \
        witness results allowed by the RSA candidate contract."]
    code := Proof.RsaKeyGen.X86_64.sharedCandidateCode v
    stack := 128
    verified := Proof.RsaKeyGen.X86_64.sharedCandidate_verified v
    spSafe := Proof.RsaKeyGen.X86_64.sharedCandidate_sp v
    features := v.features }]

end VG.Generic.MillerRabin.X86_64.RsaKeyGen
