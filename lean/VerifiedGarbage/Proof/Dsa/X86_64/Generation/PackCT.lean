module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PackMemoryCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PackMemoryCT
import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Subgroup
import VerifiedGarbage.Proof.Bignum.ExternalWords
import VerifiedGarbage.Proof.Bignum.LazyMath
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
import VerifiedGarbage.Proof.Bignum.X86_64.CTExp
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp
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
import VerifiedGarbage.Proof.Dsa.Generation.Layout
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Dsa.Generation.PEncoding
import VerifiedGarbage.Proof.Dsa.Generation.PReduction
import VerifiedGarbage.Proof.Dsa.Generation.Primality
import VerifiedGarbage.Proof.Dsa.Generation.QCandidate
import VerifiedGarbage.Proof.Dsa.Generation.SeedAdd
import VerifiedGarbage.Proof.Dsa.Generation.Trial
import VerifiedGarbage.Proof.Dsa.Generation.WitnessMemory
import VerifiedGarbage.Proof.Dsa.Generation.WitnessSlice
import VerifiedGarbage.Proof.Dsa.Generation.WorkFrame
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ArenaSource
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.BufferSeparate
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CheckPrime
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextFrame
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextSlice
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CopyDigest
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.DrawArgs
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.DrawBuffer
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.DrawCopy
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ForceSample
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ForceWitness
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeometryWork
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Hash
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Load
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.LoadWitness
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.LoopExhausted
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.LoopInit
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.LoopRound
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.LoopStep
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PHashArgs
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PHashOne
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PSeedHash
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Pack
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PackInto
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PackPart
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PreparedFrame
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeArguments
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeFootprint
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeFromFrame
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeLoop
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeR2
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeReject
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeResult
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeSetup
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.QArgs
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.QBuild
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.QShape
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Round
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RoundHeader
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RoundTail
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Sample
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SampleRoundHeader
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedAdd
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedByte
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedPack
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SourceFrame
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SourceSlice
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.StoredWitness
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.TapeCheck
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Trial
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Uniform
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Workspace
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.WorkspaceBase
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
import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf
import VerifiedGarbage.Proof.Sha1.X86_64.Shared
import VerifiedGarbage.Proof.Sha256.StateMem
import VerifiedGarbage.Proof.Sha512.X86_64.Wide
meta import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Subgroup
meta import VerifiedGarbage.Proof.Bignum.ExternalWords
meta import VerifiedGarbage.Proof.Bignum.LazyMath
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
meta import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTExp
meta import VerifiedGarbage.Proof.Bignum.X86_64.Copy
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp
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
meta import VerifiedGarbage.Proof.Dsa.BitLengthBounds
meta import VerifiedGarbage.Proof.Dsa.Digest
meta import VerifiedGarbage.Proof.Dsa.Encoding
meta import VerifiedGarbage.Proof.Dsa.Generation.Layout
meta import VerifiedGarbage.Proof.Dsa.Generation.Memory
meta import VerifiedGarbage.Proof.Dsa.Generation.PEncoding
meta import VerifiedGarbage.Proof.Dsa.Generation.PReduction
meta import VerifiedGarbage.Proof.Dsa.Generation.Primality
meta import VerifiedGarbage.Proof.Dsa.Generation.QCandidate
meta import VerifiedGarbage.Proof.Dsa.Generation.SeedAdd
meta import VerifiedGarbage.Proof.Dsa.Generation.Trial
meta import VerifiedGarbage.Proof.Dsa.Generation.WitnessMemory
meta import VerifiedGarbage.Proof.Dsa.Generation.WitnessSlice
meta import VerifiedGarbage.Proof.Dsa.Generation.WorkFrame
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ArenaSource
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.BufferSeparate
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CheckPrime
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextFrame
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextSlice
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CopyDigest
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.DrawArgs
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.DrawBuffer
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.DrawCopy
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ForceSample
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ForceWitness
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeometryWork
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Hash
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Load
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.LoadWitness
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.LoopExhausted
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.LoopInit
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.LoopRound
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.LoopStep
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PHashArgs
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PHashOne
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PSeedHash
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Pack
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PackInto
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PackPart
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PreparedFrame
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeArguments
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeFootprint
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeFromFrame
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeLoop
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeR2
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeReject
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeResult
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeSetup
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.QArgs
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.QBuild
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.QShape
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Round
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RoundHeader
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RoundTail
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Sample
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SampleRoundHeader
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedAdd
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedByte
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedPack
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SourceFrame
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SourceSlice
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.StoredWitness
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.TapeCheck
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Trial
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Uniform
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Workspace
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.WorkspaceBase
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
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf
meta import VerifiedGarbage.Proof.Sha1.X86_64.Shared
meta import VerifiedGarbage.Proof.Sha256.StateMem
meta import VerifiedGarbage.Proof.Sha512.X86_64.Wide

/-! # Timing of packing the complete generated domain -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Dsa.Generation.Layout VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.X86_64.Generation

theorem packPart_context_ct (src dst len : Nat) (hsrc : src + len ≤ packed) (hdst : packed ≤ dst)
    (hend : dst + len ≤ packed + 800) (hlen : 2 ≤ len ∧ len ≤ 384)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rsp]) (.block (packArgs src dst len)) hc).isSome = true) :
    RelCT isa (Two GenerationMemoryBefore) (packPart src dst len) (Two GenerationMemoryBefore) := by
  refine two_post (two_map GenerationContext.packPublic (fun _ _ h => generationMemory_pack h)
    (packPart_ct src dst len (by unfold packed at hsrc; omega) (by unfold packed at hend; omega)
      (by omega) ht)) ?_
  exact fun _ _ h => packPart_memory h src dst len hsrc hdst hend hlen

theorem pack_ct (pLen qLen : Nat)
    (sizes : (pLen = 128 ∧ qLen = 20) ∨ (pLen = 256 ∧ qLen = 32) ∨ (pLen = 384 ∧ qLen = 32)) :
    RelCT isa (Two GenerationMemoryBefore) (pack pLen qLen) (Two GenerationMemoryBefore) := by
  unfold pack
  simp only [seqs]
  rcases sizes with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    exact RelCT.seq (packPart_context_ct _ _ _ (by decide) (by decide) (by decide) (by decide) (by taint_decide))
      (RelCT.seq (packPart_context_ct _ _ _ (by decide) (by decide) (by decide) (by decide) (by taint_decide))
        (packPart_context_ct _ _ _ (by decide) (by decide) (by decide) (by decide) (by taint_decide)))

end VG.Proof.Dsa.X86_64.Generation
