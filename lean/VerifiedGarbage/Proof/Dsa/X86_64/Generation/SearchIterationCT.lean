module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchIterationCTState
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PConstructCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchIterationCTState
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchTailCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchTailCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchBodyCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchBodyCT
import VerifiedGarbage.Proof.Bignum.CrtMath
import VerifiedGarbage.Proof.Bignum.ExternalWords
import VerifiedGarbage.Proof.Bignum.LazyMath
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
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
import VerifiedGarbage.Proof.Dsa.Generation.CandidateWidth
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Dsa.Generation.PEncoding
import VerifiedGarbage.Proof.Dsa.Generation.PReduction
import VerifiedGarbage.Proof.Dsa.Generation.Primality
import VerifiedGarbage.Proof.Dsa.Generation.QCandidate
import VerifiedGarbage.Proof.Dsa.Generation.RandomSuffix
import VerifiedGarbage.Proof.Dsa.Generation.SeedAdd
import VerifiedGarbage.Proof.Dsa.Generation.Trial
import VerifiedGarbage.Proof.Dsa.Generation.WitnessMemory
import VerifiedGarbage.Proof.Dsa.Generation.WitnessSlice
import VerifiedGarbage.Proof.Dsa.Generation.WorkFrame
import VerifiedGarbage.Proof.Dsa.X86_64.Arithmetic
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.AttemptStatus
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CandidateArguments
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CandidateArithmetic
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CandidateArithmeticCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CandidateFromFrame
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CandidateReduction
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CandidateReductionCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CandidateStores
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CandidateWidth
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CheckPrime
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CheckPrimeReturnCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ControllerFrame
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CopyDigest
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Division
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Double
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.DrawArgs
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.DrawBuffer
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.DrawCopy
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.DrawRoundCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ForceSample
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ForceWitness
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Hash
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.HashSequence
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.HashSequenceCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.HashShape
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.HashStep
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.HashValue
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Increment
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Load
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.LoadWitness
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.LoopExhausted
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.LoopInit
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.LoopRound
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.LoopStep
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.NegateR1CT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PAttempt
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PAttemptArgs
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PAttemptTailCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PBuild
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PBuildValue
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PConstruct
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PConstructReadyCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PConstructTest
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PConstructTestCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PHashArgs
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PHashCopyCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PHashOne
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PPrimalityCallCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PPrimalityReadyCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PPrimalityTestCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PSeedHash
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PShape
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PShapeArgs
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PShapeCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PTestFull
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PTestFullCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PTestSmall
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PTestSmallCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PreparedFrame
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeArguments
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeCallCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeFootprint
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeFromFrame
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeFromFrameCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeLoop
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeLoopCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeR2
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeReject
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeResult
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeSetup
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeSetupCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ProbablePrimeCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Reduce
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ReduceFromFrame
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ReductionCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ReductionExponent
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ReductionExponentCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Round
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RoundHeader
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RoundTail
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Sample
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SampleRoundHeader
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchAdvance
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchEntryCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchStable
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchStatus
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchTailReadyCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedAdd
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedAddCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedByte
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SourceFrame
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.StoredWitness
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.StoredWitnessCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Subtract
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.TapeCheck
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Trial
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Uniform
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Workspace
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.WorkspaceBase
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.WorkspaceCTState
import VerifiedGarbage.Proof.Dsa.X86_64.Setup
import VerifiedGarbage.Proof.Dsa.X86_64.SetupChoice
import VerifiedGarbage.Proof.Ffdh.KeyScalar
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Copy
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.CutByte
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.LowByte
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Masks
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.ShapeByte
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.ShapeCT
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessCut
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessMont
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessRange
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Cold
import VerifiedGarbage.Proof.Framework.EntryBranch
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.CallInlineRel
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Registration
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe
import VerifiedGarbage.Proof.Hmac.AnyKey
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Hmac.Generic.Implies
import VerifiedGarbage.Proof.MdStream.X86_64.Words
import VerifiedGarbage.Proof.Mgf1.Bytes
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
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.AnyKeyEntry
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha1
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha256
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.PadW
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Words
import VerifiedGarbage.Proof.Pbkdf2.Scratch
import VerifiedGarbage.Proof.Poly1305.Limbs64
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
import VerifiedGarbage.Proof.Rsa.X86_64.CvStore
import VerifiedGarbage.Proof.Rsa.X86_64.Inv
import VerifiedGarbage.Proof.Rsa.X86_64.Loops
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
import VerifiedGarbage.Proof.RsaOaep.Scan
import VerifiedGarbage.Proof.RsaOaep.X86_64.Hash
import VerifiedGarbage.Proof.RsaOaep.X86_64.MgfCT
import VerifiedGarbage.Proof.Sha1.X86_64.Shared
import VerifiedGarbage.Proof.Sha256.StateMem
import VerifiedGarbage.Proof.Sha512.X86_64.Wide
meta import VerifiedGarbage.Proof.Bignum.CrtMath
meta import VerifiedGarbage.Proof.Bignum.ExternalWords
meta import VerifiedGarbage.Proof.Bignum.LazyMath
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
meta import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
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
meta import VerifiedGarbage.Proof.Dsa.BitLengthBounds
meta import VerifiedGarbage.Proof.Dsa.Digest
meta import VerifiedGarbage.Proof.Dsa.Encoding
meta import VerifiedGarbage.Proof.Dsa.Generation.CandidateWidth
meta import VerifiedGarbage.Proof.Dsa.Generation.Memory
meta import VerifiedGarbage.Proof.Dsa.Generation.PEncoding
meta import VerifiedGarbage.Proof.Dsa.Generation.PReduction
meta import VerifiedGarbage.Proof.Dsa.Generation.Primality
meta import VerifiedGarbage.Proof.Dsa.Generation.QCandidate
meta import VerifiedGarbage.Proof.Dsa.Generation.RandomSuffix
meta import VerifiedGarbage.Proof.Dsa.Generation.SeedAdd
meta import VerifiedGarbage.Proof.Dsa.Generation.Trial
meta import VerifiedGarbage.Proof.Dsa.Generation.WitnessMemory
meta import VerifiedGarbage.Proof.Dsa.Generation.WitnessSlice
meta import VerifiedGarbage.Proof.Dsa.Generation.WorkFrame
meta import VerifiedGarbage.Proof.Dsa.X86_64.Arithmetic
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.AttemptStatus
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CandidateArguments
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CandidateArithmetic
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CandidateArithmeticCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CandidateFromFrame
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CandidateReduction
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CandidateReductionCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CandidateStores
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CandidateWidth
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CheckPrime
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CheckPrimeReturnCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ControllerFrame
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CopyDigest
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Division
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Double
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.DrawArgs
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.DrawBuffer
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.DrawCopy
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.DrawRoundCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ForceSample
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ForceWitness
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Hash
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.HashSequence
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.HashSequenceCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.HashShape
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.HashStep
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.HashValue
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Increment
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Load
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.LoadWitness
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.LoopExhausted
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.LoopInit
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.LoopRound
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.LoopStep
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.NegateR1CT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PAttempt
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PAttemptArgs
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PAttemptTailCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PBuild
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PBuildValue
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PConstruct
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PConstructReadyCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PConstructTest
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PConstructTestCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PHashArgs
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PHashCopyCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PHashOne
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PPrimalityCallCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PPrimalityReadyCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PPrimalityTestCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PSeedHash
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PShape
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PShapeArgs
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PShapeCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PTestFull
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PTestFullCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PTestSmall
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PTestSmallCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PreparedFrame
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeArguments
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeCallCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeFootprint
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeFromFrame
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeFromFrameCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeLoop
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeLoopCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeR2
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeReject
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeResult
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeSetup
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeSetupCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ProbablePrimeCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Reduce
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ReduceFromFrame
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ReductionCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ReductionExponent
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ReductionExponentCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Round
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RoundHeader
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RoundTail
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Sample
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SampleRoundHeader
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchAdvance
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchEntryCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchStable
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchStatus
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchTailReadyCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedAdd
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedAddCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedByte
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SourceFrame
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.StoredWitness
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.StoredWitnessCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Subtract
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.TapeCheck
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Trial
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Uniform
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Workspace
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.WorkspaceBase
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.WorkspaceCTState
meta import VerifiedGarbage.Proof.Dsa.X86_64.Setup
meta import VerifiedGarbage.Proof.Dsa.X86_64.SetupChoice
meta import VerifiedGarbage.Proof.Ffdh.KeyScalar
meta import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Copy
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.CutByte
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.LowByte
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Masks
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Shape
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.ShapeByte
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.ShapeCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessCut
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessMont
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessRange
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Cold
meta import VerifiedGarbage.Proof.Framework.EntryBranch
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.OffsetBelow
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Framework.X86_64.Avx
meta import VerifiedGarbage.Proof.Framework.X86_64.CallInlineRel
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.Registration
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
meta import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe
meta import VerifiedGarbage.Proof.Hmac.AnyKey
meta import VerifiedGarbage.Proof.Hmac.Common
meta import VerifiedGarbage.Proof.Hmac.Generic.Implies
meta import VerifiedGarbage.Proof.MdStream.X86_64.Words
meta import VerifiedGarbage.Proof.Mgf1.Bytes
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
meta import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.AnyKeyEntry
meta import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha1
meta import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha256
meta import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.PadW
meta import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Words
meta import VerifiedGarbage.Proof.Pbkdf2.Scratch
meta import VerifiedGarbage.Proof.Poly1305.Limbs64
meta import VerifiedGarbage.Proof.Rsa.Octets
meta import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
meta import VerifiedGarbage.Proof.Rsa.X86_64.CvStore
meta import VerifiedGarbage.Proof.Rsa.X86_64.Inv
meta import VerifiedGarbage.Proof.Rsa.X86_64.Loops
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
meta import VerifiedGarbage.Proof.RsaOaep.Scan
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.Hash
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.MgfCT
meta import VerifiedGarbage.Proof.Sha1.X86_64.Shared
meta import VerifiedGarbage.Proof.Sha256.StateMem
meta import VerifiedGarbage.Proof.Sha512.X86_64.Wide

/-! # Complete p-search iteration, including its public continuation decision -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.MillerRabin.X86_64
open VG.Proof.Pbkdf2.Md.X86_64 VG.Impl.Dsa.X86_64.Generation VG.Impl.Bignum.X86_64

theorem searchIteration_ct_of (G1 G256 : Impl.Pbkdf2.Md.X86_64.Stream)
    (M : Mont) (K : Kernel) (n : Nat) (hn : n = 2 ∨ n = 3) (H : Spec.Mgf1.Hash) (pLen qLen : Nat)
    (sizes : GenerationSizes pLen qLen)
    (hG : Calls.StreamOK (if qLen = 20 then G1 else G256))
    (hmatch : ∀ x, H.hash x = hG.SH.H.hash x)
    (hsize : ∀ x, (H.hash x).length = (if qLen = 20 then G1 else G256).D)
    (hhash : ∀ bs, H.hash bs = Spec.Dsa.seedHash (8 * qLen) bs)
    (hseedsize : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * qLen) bs).length = 8 * qLen)
    (hd : (if qLen = 20 then G1 else G256).D = qLen)
    (hl : 32 * pLen ≤ 12288) (hs : (8 * pLen - 1) / (8 * qLen) + 1 ≤ 12)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi])
      (.block (pSearchAdvanceHead (32 * pLen) ((8 * pLen - 1) / (8 * qLen) + 1))) hc).isSome = true) :
    RelCT isa (Two (SearchBefore n pLen qLen))
      (pSearchIteration (pAttempt G1 G256 M.mm K.run pLen qLen)
        (32 * pLen) ((8 * pLen - 1) / (8 * qLen) + 1))
      (Two (SearchIterationAfter n pLen qLen)) := by
  unfold pSearchIteration
  simp only [seqs]
  have body : RelCT isa (Two (SearchBefore n pLen qLen)) (pAttempt G1 G256 M.mm K.run pLen qLen)
      (Two (SearchBodySized n pLen qLen)) := by
    refine two_post (searchBody_ct G1 G256 M K n hn H pLen qLen sizes hG hmatch hsize hhash hseedsize hd) ?_
    intro p s h
    exact WP.mono (searchBody_ready G1 G256 M K hG hmatch hsize hhash hseedsize hd h)
      fun _ ht => ⟨ht, h.2.2.2.2.2⟩
  refine RelCT.seq body (two_post ((two_map SearchPublic.control (fun _ _ h => searchBody_control h)
    (searchTail_ct (32 * pLen) ((8 * pLen - 1) / (8 * qLen) + 1) hl hs ht)).mono
    (fun _ _ h => h) (fun _ _ _ => True.intro)) (fun _ _ h => searchIteration_tail h hl hs))

theorem searchIteration_ct (G1 G256 : Impl.Pbkdf2.Md.X86_64.Stream)
    (M : Mont) (K : Kernel) (n : Nat) (hn : n = 2 ∨ n = 3) (H : Spec.Mgf1.Hash) (pLen qLen : Nat)
    (sizes : GenerationSizes pLen qLen)
    (hG : Calls.StreamOK (if qLen = 20 then G1 else G256))
    (hmatch : ∀ x, H.hash x = hG.SH.H.hash x)
    (hsize : ∀ x, (H.hash x).length = (if qLen = 20 then G1 else G256).D)
    (hhash : ∀ bs, H.hash bs = Spec.Dsa.seedHash (8 * qLen) bs)
    (hseedsize : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * qLen) bs).length = 8 * qLen)
    (hd : (if qLen = 20 then G1 else G256).D = qLen) :
    RelCT isa (Two (SearchBefore n pLen qLen))
      (pSearchIteration (pAttempt G1 G256 M.mm K.run pLen qLen)
        (32 * pLen) ((8 * pLen - 1) / (8 * qLen) + 1))
      (Two (SearchIterationAfter n pLen qLen)) := by
  rcases sizes with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    exact searchIteration_ct_of G1 G256 M K n hn H _ _ (by unfold GenerationSizes; decide)
      hG hmatch hsize hhash hseedsize hd (by decide) (by decide) (by taint_decide)

end VG.Proof.Dsa.X86_64.Generation
