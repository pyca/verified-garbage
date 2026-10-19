module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ParameterTailCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ParameterTailCT
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
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
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
import VerifiedGarbage.Proof.Dsa.BitLengthBounds
import VerifiedGarbage.Proof.Dsa.Derive
import VerifiedGarbage.Proof.Dsa.Digest
import VerifiedGarbage.Proof.Dsa.DomainWidths
import VerifiedGarbage.Proof.Dsa.Generation.CandidateWidth
import VerifiedGarbage.Proof.Dsa.Generation.Chunks
import VerifiedGarbage.Proof.Dsa.Generation.GeneratorDomain
import VerifiedGarbage.Proof.Dsa.Generation.Layout
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Dsa.Generation.PEncoding
import VerifiedGarbage.Proof.Dsa.Generation.PReduction
import VerifiedGarbage.Proof.Dsa.Generation.ParamsEncoding
import VerifiedGarbage.Proof.Dsa.Generation.Primality
import VerifiedGarbage.Proof.Dsa.Generation.QCandidate
import VerifiedGarbage.Proof.Dsa.Generation.RandomSuffix
import VerifiedGarbage.Proof.Dsa.Generation.SearchDomain
import VerifiedGarbage.Proof.Dsa.Generation.SeedAdd
import VerifiedGarbage.Proof.Dsa.Generation.Trial
import VerifiedGarbage.Proof.Dsa.Generation.WitnessMemory
import VerifiedGarbage.Proof.Dsa.Generation.WitnessSlice
import VerifiedGarbage.Proof.Dsa.Generation.WorkFrame
import VerifiedGarbage.Proof.Dsa.Layout
import VerifiedGarbage.Proof.Dsa.SignVerify
import VerifiedGarbage.Proof.Dsa.SizeBounds
import VerifiedGarbage.Proof.Dsa.X86_64.AcceptedSpec
import VerifiedGarbage.Proof.Dsa.X86_64.Add
import VerifiedGarbage.Proof.Dsa.X86_64.AddCallCT
import VerifiedGarbage.Proof.Dsa.X86_64.Arithmetic
import VerifiedGarbage.Proof.Dsa.X86_64.BodyCT
import VerifiedGarbage.Proof.Dsa.X86_64.BoundaryCT
import VerifiedGarbage.Proof.Dsa.X86_64.BufferFrame
import VerifiedGarbage.Proof.Dsa.X86_64.Call2
import VerifiedGarbage.Proof.Dsa.X86_64.CallAddCT
import VerifiedGarbage.Proof.Dsa.X86_64.CallOperands
import VerifiedGarbage.Proof.Dsa.X86_64.Child
import VerifiedGarbage.Proof.Dsa.X86_64.CopyMasked
import VerifiedGarbage.Proof.Dsa.X86_64.DomainShapeCT
import VerifiedGarbage.Proof.Dsa.X86_64.EncodePower
import VerifiedGarbage.Proof.Dsa.X86_64.EnterLeave
import VerifiedGarbage.Proof.Dsa.X86_64.EntryFieldsFrame
import VerifiedGarbage.Proof.Dsa.X86_64.EntryScratch
import VerifiedGarbage.Proof.Dsa.X86_64.Exponent
import VerifiedGarbage.Proof.Dsa.X86_64.Failure
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ArenaSource
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.AttemptStatus
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.BufferSeparate
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
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ChunkCheck
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ChunkTake
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextFrame
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextGeneratorFrame
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextSearchFrame
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextSeed
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextSlice
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextSuccess
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ControllerFrame
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CopyDigest
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.DecrementOdd
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Division
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Double
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.DrawArgs
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.DrawBuffer
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.DrawCopy
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.DrawRoundCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.FinishDomain
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ForceSample
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ForceWitness
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorArguments
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorBody
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorCheck
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorDecisionCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorEvaluate
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorFields
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorFootprint
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorFromFrame
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorInput
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorIterationCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorLoads
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorLoopCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorModulus
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorOutput
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorPower
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorPowerFresh
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorRange
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorRangeCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorResult
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorStages
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorStatus
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorStepCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Hash
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.HashCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.HashChoice
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
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.NativeGenerator
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.NativeSearch
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.NativeSearchCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.NegateR1CT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.OnSuccess
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.OnSuccessCT
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
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PSearchLoopCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PSeedHash
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PShape
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PShapeArgs
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PShapeCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PTestFull
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PTestFullCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PTestSmall
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PTestSmallCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Pack
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PackCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PackInto
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PackPart
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ParameterInvariant
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
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.QArgs
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.QBuild
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.QShape
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
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchBodyCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchEntryCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchIterationCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchStable
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchStatus
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchTailReadyCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedAdd
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedAddCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedAttempt
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedByte
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedGenerator
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedGeneratorCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedGeneratorFinish
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedGeneratorFinishCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedPack
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedPhaseStableCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedPrime
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedPrimeCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedPrimeFinish
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedPrimeFinishCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedSearchStateCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedSubgroup
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedSubgroupCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SourceFrame
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SourceSlice
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.StoredWitness
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.StoredWitnessCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Subgroup
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SubgroupReadyCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Subtract
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.TapeCheck
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.TapeLoop
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.TapeState
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Trial
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Uniform
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Validate
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ValidateArgs
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ValidateCore
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Workspace
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.WorkspaceBase
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.WorkspaceCTState
import VerifiedGarbage.Proof.Dsa.X86_64.KeyPointers
import VerifiedGarbage.Proof.Dsa.X86_64.Load
import VerifiedGarbage.Proof.Dsa.X86_64.LoadCheckCT
import VerifiedGarbage.Proof.Dsa.X86_64.Masks
import VerifiedGarbage.Proof.Dsa.X86_64.Multiply
import VerifiedGarbage.Proof.Dsa.X86_64.OrWords
import VerifiedGarbage.Proof.Dsa.X86_64.Parent
import VerifiedGarbage.Proof.Dsa.X86_64.Parity
import VerifiedGarbage.Proof.Dsa.X86_64.Power
import VerifiedGarbage.Proof.Dsa.X86_64.Prepare
import VerifiedGarbage.Proof.Dsa.X86_64.PublicCalls
import VerifiedGarbage.Proof.Dsa.X86_64.PublicExponentCT
import VerifiedGarbage.Proof.Dsa.X86_64.PublicKeyCT
import VerifiedGarbage.Proof.Dsa.X86_64.PublicPrefix
import VerifiedGarbage.Proof.Dsa.X86_64.RangeCT
import VerifiedGarbage.Proof.Dsa.X86_64.RangeHead
import VerifiedGarbage.Proof.Dsa.X86_64.RangeLow
import VerifiedGarbage.Proof.Dsa.X86_64.RangeMask
import VerifiedGarbage.Proof.Dsa.X86_64.ReadyJoint
import VerifiedGarbage.Proof.Dsa.X86_64.Reduce
import VerifiedGarbage.Proof.Dsa.X86_64.ReduceCount
import VerifiedGarbage.Proof.Dsa.X86_64.ReduceInit
import VerifiedGarbage.Proof.Dsa.X86_64.ReduceLoop
import VerifiedGarbage.Proof.Dsa.X86_64.ReduceRead
import VerifiedGarbage.Proof.Dsa.X86_64.ReduceReadCT
import VerifiedGarbage.Proof.Dsa.X86_64.ReduceSetup
import VerifiedGarbage.Proof.Dsa.X86_64.ReduceStepCT
import VerifiedGarbage.Proof.Dsa.X86_64.Result
import VerifiedGarbage.Proof.Dsa.X86_64.Save
import VerifiedGarbage.Proof.Dsa.X86_64.ScanField
import VerifiedGarbage.Proof.Dsa.X86_64.ScanFieldCT
import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleAddCT
import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleJointCT
import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleOperands
import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleReduceCT
import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleState
import VerifiedGarbage.Proof.Dsa.X86_64.SealChild
import VerifiedGarbage.Proof.Dsa.X86_64.Setup
import VerifiedGarbage.Proof.Dsa.X86_64.SetupChoice
import VerifiedGarbage.Proof.Dsa.X86_64.ShapeSizesCT
import VerifiedGarbage.Proof.Dsa.X86_64.SignificantLoop
import VerifiedGarbage.Proof.Dsa.X86_64.Store
import VerifiedGarbage.Proof.Dsa.X86_64.StoreSuffix
import VerifiedGarbage.Proof.Dsa.X86_64.TopMask
import VerifiedGarbage.Proof.Dsa.X86_64.WidthMask
import VerifiedGarbage.Proof.Dsa.X86_64.WorkspaceReady
import VerifiedGarbage.Proof.Dsa.X86_64.WriteScalarCT
import VerifiedGarbage.Proof.Dsa.X86_64.WriteSignature
import VerifiedGarbage.Proof.Dsa.Zero
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
import VerifiedGarbage.Proof.Rsa.X86_64.CvCheck
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
import VerifiedGarbage.Proof.RsaPss.Params
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
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
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
meta import VerifiedGarbage.Proof.Dsa.BitLengthBounds
meta import VerifiedGarbage.Proof.Dsa.Derive
meta import VerifiedGarbage.Proof.Dsa.Digest
meta import VerifiedGarbage.Proof.Dsa.DomainWidths
meta import VerifiedGarbage.Proof.Dsa.Generation.CandidateWidth
meta import VerifiedGarbage.Proof.Dsa.Generation.Chunks
meta import VerifiedGarbage.Proof.Dsa.Generation.GeneratorDomain
meta import VerifiedGarbage.Proof.Dsa.Generation.Layout
meta import VerifiedGarbage.Proof.Dsa.Generation.Memory
meta import VerifiedGarbage.Proof.Dsa.Generation.PEncoding
meta import VerifiedGarbage.Proof.Dsa.Generation.PReduction
meta import VerifiedGarbage.Proof.Dsa.Generation.ParamsEncoding
meta import VerifiedGarbage.Proof.Dsa.Generation.Primality
meta import VerifiedGarbage.Proof.Dsa.Generation.QCandidate
meta import VerifiedGarbage.Proof.Dsa.Generation.RandomSuffix
meta import VerifiedGarbage.Proof.Dsa.Generation.SearchDomain
meta import VerifiedGarbage.Proof.Dsa.Generation.SeedAdd
meta import VerifiedGarbage.Proof.Dsa.Generation.Trial
meta import VerifiedGarbage.Proof.Dsa.Generation.WitnessMemory
meta import VerifiedGarbage.Proof.Dsa.Generation.WitnessSlice
meta import VerifiedGarbage.Proof.Dsa.Generation.WorkFrame
meta import VerifiedGarbage.Proof.Dsa.Layout
meta import VerifiedGarbage.Proof.Dsa.SignVerify
meta import VerifiedGarbage.Proof.Dsa.SizeBounds
meta import VerifiedGarbage.Proof.Dsa.X86_64.AcceptedSpec
meta import VerifiedGarbage.Proof.Dsa.X86_64.Add
meta import VerifiedGarbage.Proof.Dsa.X86_64.AddCallCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Arithmetic
meta import VerifiedGarbage.Proof.Dsa.X86_64.BodyCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.BoundaryCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.BufferFrame
meta import VerifiedGarbage.Proof.Dsa.X86_64.Call2
meta import VerifiedGarbage.Proof.Dsa.X86_64.CallAddCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.CallOperands
meta import VerifiedGarbage.Proof.Dsa.X86_64.Child
meta import VerifiedGarbage.Proof.Dsa.X86_64.CopyMasked
meta import VerifiedGarbage.Proof.Dsa.X86_64.DomainShapeCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.EncodePower
meta import VerifiedGarbage.Proof.Dsa.X86_64.EnterLeave
meta import VerifiedGarbage.Proof.Dsa.X86_64.EntryFieldsFrame
meta import VerifiedGarbage.Proof.Dsa.X86_64.EntryScratch
meta import VerifiedGarbage.Proof.Dsa.X86_64.Exponent
meta import VerifiedGarbage.Proof.Dsa.X86_64.Failure
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ArenaSource
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.AttemptStatus
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.BufferSeparate
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
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ChunkCheck
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ChunkTake
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextFrame
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextGeneratorFrame
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextSearchFrame
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextSeed
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextSlice
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextSuccess
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ControllerFrame
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CopyDigest
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.DecrementOdd
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Division
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Double
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.DrawArgs
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.DrawBuffer
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.DrawCopy
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.DrawRoundCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.FinishDomain
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ForceSample
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ForceWitness
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorArguments
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorBody
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorCheck
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorDecisionCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorEvaluate
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorFields
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorFootprint
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorFromFrame
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorInput
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorIterationCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorLoads
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorLoopCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorModulus
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorOutput
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorPower
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorPowerFresh
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorRange
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorRangeCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorResult
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorStages
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorStatus
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorStepCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Hash
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.HashCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.HashChoice
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
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.NativeGenerator
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.NativeSearch
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.NativeSearchCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.NegateR1CT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.OnSuccess
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.OnSuccessCT
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
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PSearchLoopCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PSeedHash
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PShape
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PShapeArgs
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PShapeCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PTestFull
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PTestFullCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PTestSmall
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PTestSmallCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Pack
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PackCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PackInto
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PackPart
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ParameterInvariant
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
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.QArgs
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.QBuild
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.QShape
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
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchBodyCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchEntryCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchIterationCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchStable
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchStatus
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchTailReadyCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedAdd
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedAddCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedAttempt
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedByte
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedGenerator
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedGeneratorCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedGeneratorFinish
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedGeneratorFinishCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedPack
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedPhaseStableCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedPrime
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedPrimeCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedPrimeFinish
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedPrimeFinishCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedSearchStateCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedSubgroup
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedSubgroupCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SourceFrame
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SourceSlice
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.StoredWitness
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.StoredWitnessCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Subgroup
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SubgroupReadyCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Subtract
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.TapeCheck
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.TapeLoop
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.TapeState
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Trial
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Uniform
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Validate
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ValidateArgs
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ValidateCore
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Workspace
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.WorkspaceBase
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.WorkspaceCTState
meta import VerifiedGarbage.Proof.Dsa.X86_64.KeyPointers
meta import VerifiedGarbage.Proof.Dsa.X86_64.Load
meta import VerifiedGarbage.Proof.Dsa.X86_64.LoadCheckCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Masks
meta import VerifiedGarbage.Proof.Dsa.X86_64.Multiply
meta import VerifiedGarbage.Proof.Dsa.X86_64.OrWords
meta import VerifiedGarbage.Proof.Dsa.X86_64.Parent
meta import VerifiedGarbage.Proof.Dsa.X86_64.Parity
meta import VerifiedGarbage.Proof.Dsa.X86_64.Power
meta import VerifiedGarbage.Proof.Dsa.X86_64.Prepare
meta import VerifiedGarbage.Proof.Dsa.X86_64.PublicCalls
meta import VerifiedGarbage.Proof.Dsa.X86_64.PublicExponentCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.PublicKeyCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.PublicPrefix
meta import VerifiedGarbage.Proof.Dsa.X86_64.RangeCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.RangeHead
meta import VerifiedGarbage.Proof.Dsa.X86_64.RangeLow
meta import VerifiedGarbage.Proof.Dsa.X86_64.RangeMask
meta import VerifiedGarbage.Proof.Dsa.X86_64.ReadyJoint
meta import VerifiedGarbage.Proof.Dsa.X86_64.Reduce
meta import VerifiedGarbage.Proof.Dsa.X86_64.ReduceCount
meta import VerifiedGarbage.Proof.Dsa.X86_64.ReduceInit
meta import VerifiedGarbage.Proof.Dsa.X86_64.ReduceLoop
meta import VerifiedGarbage.Proof.Dsa.X86_64.ReduceRead
meta import VerifiedGarbage.Proof.Dsa.X86_64.ReduceReadCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.ReduceSetup
meta import VerifiedGarbage.Proof.Dsa.X86_64.ReduceStepCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Result
meta import VerifiedGarbage.Proof.Dsa.X86_64.Save
meta import VerifiedGarbage.Proof.Dsa.X86_64.ScanField
meta import VerifiedGarbage.Proof.Dsa.X86_64.ScanFieldCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleAddCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleJointCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleOperands
meta import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleReduceCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleState
meta import VerifiedGarbage.Proof.Dsa.X86_64.SealChild
meta import VerifiedGarbage.Proof.Dsa.X86_64.Setup
meta import VerifiedGarbage.Proof.Dsa.X86_64.SetupChoice
meta import VerifiedGarbage.Proof.Dsa.X86_64.ShapeSizesCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.SignificantLoop
meta import VerifiedGarbage.Proof.Dsa.X86_64.Store
meta import VerifiedGarbage.Proof.Dsa.X86_64.StoreSuffix
meta import VerifiedGarbage.Proof.Dsa.X86_64.TopMask
meta import VerifiedGarbage.Proof.Dsa.X86_64.WidthMask
meta import VerifiedGarbage.Proof.Dsa.X86_64.WorkspaceReady
meta import VerifiedGarbage.Proof.Dsa.X86_64.WriteScalarCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.WriteSignature
meta import VerifiedGarbage.Proof.Dsa.Zero
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
meta import VerifiedGarbage.Proof.Rsa.X86_64.CvCheck
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
meta import VerifiedGarbage.Proof.RsaPss.Params
meta import VerifiedGarbage.Proof.Sha1.X86_64.Shared
meta import VerifiedGarbage.Proof.Sha256.StateMem
meta import VerifiedGarbage.Proof.Sha512.X86_64.Wide

/-! # Timing of one complete outer seed-loop iteration -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Dsa.X86_64.Generation VG.Proof.MillerRabin.X86_64

theorem parameter_before_pins (n pLen qLen : Nat) : Pins (ParameterBefore n pLen qLen) [.rsp] := by
  intro p s t ⟨⟨Ws, hs, _⟩, _⟩ ⟨⟨Wt, ht, _⟩, _⟩ r hr
  obtain rfl := List.mem_singleton.mp hr
  exact hs.layout.rsp.trans ht.layout.rsp.symm

theorem parameterIteration_ct_of (H : GenerationHashes) (M : Mont) (Sq : MontS) (K : Kernel)
    (n : Nat) (hn : n = 2 ∨ n = 3) (pLen qLen : Nat) (sizes : GenerationSizes pLen qLen)
    {hc₁ hc₂ : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.rsp]) (.block (chunkCheck seedTape qLen)) hc₁).isSome = true)
    (ht₂ : (taint.check (Taint.ofRegs [.rsp]) (.block (tapeTake seedTape qLen)) hc₂).isSome = true) :
    RelCT isa (Two (ParameterBefore n pLen qLen))
      (tapeIteration seedTape qLen (seedAttempt H.sha1 H.sha256 Sq.mm M.mm K.run pLen qLen))
      (Two (ParameterIterationAfter n pLen qLen)) := by
  unfold tapeIteration
  refine RelCT.seq (two_piece [.rsp] (parameter_before_pins n pLen qLen) ht₁
    (fun _ _ h => parameter_check h)) ?_
  refine two_ite (fun _ _ _ hs ht => hs.2.trans ht.2.symm) ?_ ?_
  · refine two_piece [.rsp] ?_ (by taint_decide) (fun _ _ h => parameter_exhausted h.1 h.2)
    intro p s t hs ht r hr
    exact parameter_before_pins n pLen qLen p s t hs.1.1 ht.1.1 r hr
  · have tail : RelCT isa (Two (ParameterAvailable n pLen qLen))
        (.seq (.block (tapeTake seedTape qLen))
          (.seq (seedAttempt H.sha1 H.sha256 Sq.mm M.mm K.run pLen qLen) (.block tapeStatus)))
        (Two (ParameterIterationAfter n pLen qLen)) := by
      refine RelCT.seq (two_piece [.rsp] ?_ ht₂ (fun _ _ h => parameter_take h))
        (RelCT.seq (two_post (parameter_body_ct H M Sq K n hn pLen qLen sizes)
          (fun _ _ h => parameter_body_ready H M Sq K h)) ?_)
      · intro p s t hs ht r hr
        exact parameter_before_pins n pLen qLen p s t hs.1 ht.1 r hr
      · refine two_piece [.rsp] ?_ (by taint_decide) (fun _ _ h => parameter_status h)
        intro p s t ⟨⟨Ws, hs, _⟩, _⟩ ⟨⟨Wt, ht, _⟩, _⟩ r hr
        obtain rfl := List.mem_singleton.mp hr
        exact hs.layout.rsp.trans ht.layout.rsp.symm
    exact two_map (fun p : ParameterPublic => p) (fun _ _ h => parameter_available h.1 h.2) tail

theorem parameterIteration_ct (H : GenerationHashes) (M : Mont) (Sq : MontS) (K : Kernel)
    (n : Nat) (hn : n = 2 ∨ n = 3) (pLen qLen : Nat) (sizes : GenerationSizes pLen qLen) :
    RelCT isa (Two (ParameterBefore n pLen qLen))
      (tapeIteration seedTape qLen (seedAttempt H.sha1 H.sha256 Sq.mm M.mm K.run pLen qLen))
      (Two (ParameterIterationAfter n pLen qLen)) := by
  have width : qLen = 20 ∨ qLen = 32 := by rcases sizes with h | h | h <;> simp [h.2]
  rcases width with rfl | rfl
  all_goals exact parameterIteration_ct_of H M Sq K n hn pLen _ sizes (by taint_decide) (by taint_decide)

end VG.Proof.Dsa.X86_64.Generation
