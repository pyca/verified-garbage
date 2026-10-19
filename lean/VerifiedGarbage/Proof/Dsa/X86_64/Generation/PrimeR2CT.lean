module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeState
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeState
public import VerifiedGarbage.Proof.Dsa.X86_64.SetupCT
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.PrimeSetup
meta import VerifiedGarbage.Proof.Dsa.X86_64.SetupCT
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MontSetup
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MontSetup
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.CrtMath
import VerifiedGarbage.Proof.Bignum.ExternalWords
import VerifiedGarbage.Proof.Bignum.LazyMath
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
import VerifiedGarbage.Proof.Bignum.X86_64.CTExp
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChk
import VerifiedGarbage.Proof.Bignum.X86_64.CrtFix
import VerifiedGarbage.Proof.Bignum.X86_64.CrtGPow
import VerifiedGarbage.Proof.Bignum.X86_64.CrtPow
import VerifiedGarbage.Proof.Bignum.X86_64.CrtQ
import VerifiedGarbage.Proof.Bignum.X86_64.CrtRows
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSetup
import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
import VerifiedGarbage.Proof.Bignum.X86_64.Csub
import VerifiedGarbage.Proof.Bignum.X86_64.Double
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
import VerifiedGarbage.Proof.Bignum.X86_64.PubCode
import VerifiedGarbage.Proof.Bignum.X86_64.PubEntry
import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
import VerifiedGarbage.Proof.Bignum.X86_64.R2aStep
import VerifiedGarbage.Proof.Bignum.X86_64.R2aSub
import VerifiedGarbage.Proof.Bignum.X86_64.R2aWord
import VerifiedGarbage.Proof.Bignum.X86_64.R2wAdd
import VerifiedGarbage.Proof.Bignum.X86_64.R2wStep
import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.Setup
import VerifiedGarbage.Proof.Bignum.X86_64.Store
import VerifiedGarbage.Proof.Bignum.X86_64.Template
import VerifiedGarbage.Proof.Bignum.X86_64.Valid
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Dsa.BitLengthBounds
import VerifiedGarbage.Proof.Dsa.Digest
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Dsa.Generation.PEncoding
import VerifiedGarbage.Proof.Dsa.Generation.PReduction
import VerifiedGarbage.Proof.Dsa.Generation.Primality
import VerifiedGarbage.Proof.Dsa.Generation.QCandidate
import VerifiedGarbage.Proof.Dsa.Generation.WitnessMemory
import VerifiedGarbage.Proof.Dsa.Generation.WitnessSlice
import VerifiedGarbage.Proof.Dsa.Generation.WorkFrame
import VerifiedGarbage.Proof.Dsa.X86_64.Arithmetic
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CopyDigest
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.DrawArgs
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.DrawCopy
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ForceSample
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ForceWitness
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Load
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.LoadWitness
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PreparedFrame
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeR2
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Round
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RoundHeader
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RoundTail
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Sample
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SampleRoundHeader
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SourceFrame
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.StoredWitness
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Uniform
import VerifiedGarbage.Proof.Dsa.X86_64.Setup
import VerifiedGarbage.Proof.Dsa.X86_64.SetupChoice
import VerifiedGarbage.Proof.Ffdh.KeyScalar
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Copy
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.CutByte
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Masks
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.ShapeByte
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessCut
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessMont
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessRange
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
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
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerContext
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerEntry
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerKept
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerRestore
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerResult
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerRound
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
import VerifiedGarbage.Proof.MillerRabin.X86_64.Prepared
import VerifiedGarbage.Proof.MillerRabin.X86_64.RoundCT
import VerifiedGarbage.Proof.MillerRabin.X86_64.Stage
import VerifiedGarbage.Proof.MillerRabin.X86_64.Verified
import VerifiedGarbage.Proof.Poly1305.Limbs64
import VerifiedGarbage.Proof.Rsa.Octets
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
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrShift
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrWit
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Trial
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.TrialLoop
meta import VerifiedGarbage.Proof.Bignum.CrtMath
meta import VerifiedGarbage.Proof.Bignum.ExternalWords
meta import VerifiedGarbage.Proof.Bignum.LazyMath
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
meta import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTExp
meta import VerifiedGarbage.Proof.Bignum.X86_64.Copy
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtChk
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtFix
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtGPow
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtPow
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtQ
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtRows
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtSetup
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
meta import VerifiedGarbage.Proof.Bignum.X86_64.Csub
meta import VerifiedGarbage.Proof.Bignum.X86_64.Double
meta import VerifiedGarbage.Proof.Bignum.X86_64.Loop
meta import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubCode
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubEntry
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2aStep
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2aSub
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2aWord
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2wAdd
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2wStep
meta import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
meta import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
meta import VerifiedGarbage.Proof.Bignum.X86_64.Row
meta import VerifiedGarbage.Proof.Bignum.X86_64.Setup
meta import VerifiedGarbage.Proof.Bignum.X86_64.Store
meta import VerifiedGarbage.Proof.Bignum.X86_64.Template
meta import VerifiedGarbage.Proof.Bignum.X86_64.Valid
meta import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Bignum.CrtRedc
meta import VerifiedGarbage.Proof.Bignum.CrtRedc
public import VerifiedGarbage.Proof.Bignum.CrtMath
public import VerifiedGarbage.Proof.Bignum.ExternalWords
public import VerifiedGarbage.Proof.Bignum.LazyMath
public import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
public import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
public import VerifiedGarbage.Proof.Bignum.X86_64.CTExp
public import VerifiedGarbage.Proof.Bignum.X86_64.Copy
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtChk
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtFix
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtGPow
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtPow
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtQ
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtRows
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtSetup
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
public import VerifiedGarbage.Proof.Bignum.X86_64.Csub
public import VerifiedGarbage.Proof.Bignum.X86_64.Double
public import VerifiedGarbage.Proof.Bignum.X86_64.Loop
public import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
public import VerifiedGarbage.Proof.Bignum.X86_64.PubCode
public import VerifiedGarbage.Proof.Bignum.X86_64.PubEntry
public import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
public import VerifiedGarbage.Proof.Bignum.X86_64.R2aStep
public import VerifiedGarbage.Proof.Bignum.X86_64.R2aSub
public import VerifiedGarbage.Proof.Bignum.X86_64.R2aWord
public import VerifiedGarbage.Proof.Bignum.X86_64.R2wAdd
public import VerifiedGarbage.Proof.Bignum.X86_64.R2wStep
public import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
public import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
public import VerifiedGarbage.Proof.Bignum.X86_64.Row
public import VerifiedGarbage.Proof.Bignum.X86_64.Setup
public import VerifiedGarbage.Proof.Bignum.X86_64.Store
public import VerifiedGarbage.Proof.Bignum.X86_64.Template
public import VerifiedGarbage.Proof.Bignum.X86_64.Valid
public import VerifiedGarbage.Proof.Dsa.Arithmetic
public import VerifiedGarbage.Proof.Dsa.BitLengthBounds
public import VerifiedGarbage.Proof.Dsa.Digest
public import VerifiedGarbage.Proof.Dsa.Encoding
public import VerifiedGarbage.Proof.Dsa.Generation.Memory
public import VerifiedGarbage.Proof.Dsa.Generation.PEncoding
public import VerifiedGarbage.Proof.Dsa.Generation.PReduction
public import VerifiedGarbage.Proof.Dsa.Generation.Primality
public import VerifiedGarbage.Proof.Dsa.Generation.QCandidate
public import VerifiedGarbage.Proof.Dsa.Generation.WitnessMemory
public import VerifiedGarbage.Proof.Dsa.Generation.WitnessSlice
public import VerifiedGarbage.Proof.Dsa.Generation.WorkFrame
public import VerifiedGarbage.Proof.Dsa.X86_64.Arithmetic
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CopyDigest
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.DrawArgs
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.DrawCopy
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ForceSample
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ForceWitness
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Load
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.LoadWitness
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PreparedFrame
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Round
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RoundHeader
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RoundTail
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Sample
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SampleRoundHeader
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SourceFrame
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.StoredWitness
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Uniform
public import VerifiedGarbage.Proof.Dsa.X86_64.Setup
public import VerifiedGarbage.Proof.Dsa.X86_64.SetupChoice
public import VerifiedGarbage.Proof.Ffdh.KeyScalar
public import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Copy
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.CutByte
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Masks
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.ShapeByte
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessCut
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessMont
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessRange
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
public import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerContext
public import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerEntry
public import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerKept
public import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerRestore
public import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerResult
public import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerRound
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
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Prepared
public import VerifiedGarbage.Proof.MillerRabin.X86_64.RoundCT
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Stage
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Verified
public import VerifiedGarbage.Proof.Poly1305.Limbs64
public import VerifiedGarbage.Proof.Rsa.Octets
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
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrShift
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrWit
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Trial
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.TrialLoop
meta import VerifiedGarbage.Proof.Dsa.BitLengthBounds
meta import VerifiedGarbage.Proof.Dsa.Digest
meta import VerifiedGarbage.Proof.Dsa.Encoding
meta import VerifiedGarbage.Proof.Dsa.Generation.Memory
meta import VerifiedGarbage.Proof.Dsa.Generation.PEncoding
meta import VerifiedGarbage.Proof.Dsa.Generation.PReduction
meta import VerifiedGarbage.Proof.Dsa.Generation.Primality
meta import VerifiedGarbage.Proof.Dsa.Generation.QCandidate
meta import VerifiedGarbage.Proof.Dsa.Generation.WitnessMemory
meta import VerifiedGarbage.Proof.Dsa.Generation.WitnessSlice
meta import VerifiedGarbage.Proof.Dsa.Generation.WorkFrame
meta import VerifiedGarbage.Proof.Dsa.X86_64.Arithmetic
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CopyDigest
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.DrawArgs
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.DrawCopy
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ForceSample
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ForceWitness
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Load
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.LoadWitness
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PreparedFrame
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeR2
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Round
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RoundHeader
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RoundTail
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Sample
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SampleRoundHeader
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SourceFrame
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.StoredWitness
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Uniform
meta import VerifiedGarbage.Proof.Dsa.X86_64.Setup
meta import VerifiedGarbage.Proof.Dsa.X86_64.SetupChoice
meta import VerifiedGarbage.Proof.Ffdh.KeyScalar
meta import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Copy
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.CutByte
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Masks
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.ShapeByte
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessCut
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessMont
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessRange
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Proof.Framework.X86_64.Avx
meta import VerifiedGarbage.Proof.Framework.X86_64.CallInlineRel
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.Body
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.BodyKeeps
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.CT
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.CallBody
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.CallCT
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.CallCorrect
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.CallStack
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.CallTemplate
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerContext
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerEntry
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerKept
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerRestore
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerResult
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerRound
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.Context
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.CoreFrame
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.Correct
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.CorrectMath
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.ExitRegisters
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.Finish
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.Frame
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.FramedBody
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.FramedCall
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.Frames
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.Keeps
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.NormalizeCT
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.NormalizeContext
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.NormalizeValues
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.NormalizedPublic
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.Prepared
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.RoundCT
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.Stage
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.Verified
meta import VerifiedGarbage.Proof.Poly1305.Limbs64
meta import VerifiedGarbage.Proof.Rsa.Octets
meta import VerifiedGarbage.Proof.RsaKeyGen.Bits
meta import VerifiedGarbage.Proof.RsaKeyGen.CandMath
meta import VerifiedGarbage.Proof.RsaKeyGen.MrMont
meta import VerifiedGarbage.Proof.RsaKeyGen.Primes
meta import VerifiedGarbage.Proof.RsaKeyGen.TrialMath
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Copy
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.GcdE
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.GcdStep
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.ModE
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MontAll
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MontRest
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrExp
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrMain
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrSel
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrSelW
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrShift
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrWit
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Trial
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.TrialLoop

/-! # Constant-time Montgomery initialization for full and padded DSA candidates -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaKeyGen.X86_64

def PrimeSetupBefore (p : PrimeParams) (s : State) : Prop :=
  (∃ mi, Good s p.B p.Z p.w mi) ∧ wv s.mem p.B (slot p.w aN) p.w = p.N ∧ p.w ≤ 48

def PrimeParams.product (p : PrimeParams) (mi : BitVec 64) : ProductPublic :=
  ⟨⟨p.B, p.Z, p.w, mi⟩, p.N, p.dims.z, by change 2 ≤ p.w; have := p.dims.w4; omega,
    by change p.w < 2 ^ 31; have := p.dims.w128; omega⟩

def PrimeInverse (p : PrimeParams) (s : State) : Prop := ∃ mi, SetupPre (p.product mi) s

theorem primeHeadArgs_state {p : PrimeParams} {s : State} (h : PrimeSetupBefore p s) :
    WP isa (.block [.mov .r10 (.mem (hdr (sArr aN))), .mov .r12 (.mem (hdr sW))]) s
      (fun t => t.gpr .rdi = p.B ∧ t.gpr .r10 = off p.B (slot p.w aN)) := by
  obtain ⟨mi, hg⟩ := h.1
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off p.B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot p.w 8 hi; have := p.dims.z; omega)
  xrun [State.ea, hdr, hdrOff, hg.rdi, hl (sArr aN) (by decide), hl sW (by decide), hg.hdr.harr aN (by decide)]

theorem primeHead_ct : RelCT isa (Two PrimeSetupBefore)
    (.block Impl.Ffdh.X86_64.ParameterCandidate.prepareHead) (fun _ _ => True) := by
  unfold Impl.Ffdh.X86_64.ParameterCandidate.prepareHead
  change RelCT isa (Two PrimeSetupBefore) (.block
    (([.mov .r10 (.mem (hdr (sArr aN))), .mov .r12 (.mem (hdr sW))] : List Instr) ++
      ([.mov .rbx (.mem (at0 .r10))] ++ Impl.Bignum.X86_64.minv ++
        [.store (hdr sMinv) .r15, .mov32 .rdx (.imm 1), .mov32 .rcx (.imm 0)]))) _
  apply RelCT.block_append (M := isa)
  refine RelCT.seq (two_post (two_taint [.rdi] ?_ (by taint_decide))
    (fun _ _ h => primeHeadArgs_state h)) ?_
  · intro p s t hs ht r hr
    simp only [List.mem_singleton] at hr
    subst r
    obtain ⟨mi, hs⟩ := hs.1
    obtain ⟨mi', ht⟩ := ht.1
    exact hs.rdi.trans ht.rdi.symm
  · exact two_taint [.rdi, .r10] (by
      intro p s t hs ht r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hs.1.trans ht.1.symm
      · exact hs.2.trans ht.2.symm) (by taint_decide)

theorem primeHead_inverse {p : PrimeParams} {s : State} (h : PrimeSetupBefore p s) :
    WP isa (.block Impl.Ffdh.X86_64.ParameterCandidate.prepareHead) s (PrimeInverse p) := by
  obtain ⟨mi, hg⟩ := h.1
  have hw := p.dims.w4
  have hnow := hg.scr.nowrap
  have hfit := p.dims.z
  have hodd : (word s.mem p.B (slot p.w aN)).toNat % 2 = 1 := by
    rw [← wv_mod64 (n := p.w) _ _ _ (by omega), h.2.1,
      Nat.mod_mod_of_dvd _ (show 2 ∣ 2 ^ 64 by decide)]
    exact p.odd
  refine WP.mono (msHead_ok hg p.dims.z hodd) fun t ⟨ht, hi, _, _, _, hm, _⟩ => ?_
  have hn : wv t.mem p.B (slot p.w aN) p.w = p.N := by
    rw [hm, hdrStore_wv _ _ _ (by decide) (by decide) (by omega)]
    exact h.2.1
  have hinv : ((word t.mem p.B (slot p.w aN)).toNat * (t.gpr .r15).toNat + 1) % 2 ^ 64 = 0 := by
    rw [hm, hdrStore_word _ _ _ (by decide) (by decide) (by omega)]
    exact hi
  exact ⟨t.gpr .r15, ⟨ht, hn, hinv⟩, h.2.2, by change 1 < p.N; have := p.n3; omega, p.odd⟩

theorem primeInverse_public {s t : State} (h : Two PrimeInverse s t) : Two SetupPre s t := by
  obtain ⟨p, ⟨mi, hs⟩, ⟨mi', ht⟩⟩ := h
  have hw := p.dims.w4
  have low₁ : (word s.mem p.B (slot p.w aN)).toNat = p.N % 2 ^ 64 := by
    rw [← wv_mod64 (n := p.w) _ _ _ (by omega), show wv s.mem p.B (slot p.w aN) p.w = p.N from hs.1.modulus]
  have low₂ : (word t.mem p.B (slot p.w aN)).toNat = p.N % 2 ^ 64 := by
    rw [← wv_mod64 (n := p.w) _ _ _ (by omega), show wv t.mem p.B (slot p.w aN) p.w = p.N from ht.1.modulus]
  have hi := hs.1.inverse
  have hi' := ht.1.inverse
  change ((word s.mem p.B (slot p.w aN)).toNat * mi.toNat + 1) % 2 ^ 64 = 0 at hi
  change ((word t.mem p.B (slot p.w aN)).toNat * mi'.toNat + 1) % 2 ^ 64 = 0 at hi'
  rw [low₁] at hi
  rw [low₂] at hi'
  have he := minv_unique (by rw [Nat.mod_mod_of_dvd _ (by decide)]; exact p.odd) hi hi'
  subst mi'
  exact ⟨p.product mi, hs, ht⟩

theorem primeR2_ct (M : Mont) : RelCT isa (Two PrimeSetupBefore)
    (Impl.Dsa.X86_64.Generation.primeR2 M.mm) (fun _ _ => True) := by
  unfold Impl.Dsa.X86_64.Generation.primeR2
  exact RelCT.seq (two_post primeHead_ct (fun _ _ h => primeHead_inverse h))
    ((constants_ct M).mono (fun _ _ h => primeInverse_public h) (fun _ _ h => h))

end VG.Proof.Dsa.X86_64.Generation
