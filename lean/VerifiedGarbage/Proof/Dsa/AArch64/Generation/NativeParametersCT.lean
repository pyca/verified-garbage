module
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ParameterCTState

import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ParameterLoopCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ParameterLoopCT
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.TapeState
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ContextFrame
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcAdd
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCancelTile
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcColumns
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCorrect
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtLoop
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtRow
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtSquare
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcEnd
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcExtend
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcFastCancel
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcFastMath
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcFastWord
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcFinish
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLayout
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoad
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoop
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcRestore
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcRow
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcSave
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcSquare
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcStore
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcTile
import VerifiedGarbage.Proof.Bignum.AArch64.Bytes
import VerifiedGarbage.Proof.Bignum.AArch64.CarrySelect
import VerifiedGarbage.Proof.Bignum.AArch64.Copy
import VerifiedGarbage.Proof.Bignum.AArch64.CrtArith
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTExp
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTGPow
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetupLoad
import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
import VerifiedGarbage.Proof.Bignum.AArch64.CrtChk
import VerifiedGarbage.Proof.Bignum.AArch64.CrtP
import VerifiedGarbage.Proof.Bignum.AArch64.CrtPow
import VerifiedGarbage.Proof.Bignum.AArch64.CrtSel
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWs
import VerifiedGarbage.Proof.Bignum.AArch64.DiagonalChain
import VerifiedGarbage.Proof.Bignum.AArch64.DiagonalChainCore
import VerifiedGarbage.Proof.Bignum.AArch64.DiagonalChainStep
import VerifiedGarbage.Proof.Bignum.AArch64.DiagonalChainTile
import VerifiedGarbage.Proof.Bignum.AArch64.Double
import VerifiedGarbage.Proof.Bignum.AArch64.FastFinish
import VerifiedGarbage.Proof.Bignum.AArch64.FastFinishCT
import VerifiedGarbage.Proof.Bignum.AArch64.FastFinishSel
import VerifiedGarbage.Proof.Bignum.AArch64.FastFinishSelTile
import VerifiedGarbage.Proof.Bignum.AArch64.FastFinishSub
import VerifiedGarbage.Proof.Bignum.AArch64.FastFinishSubTile
import VerifiedGarbage.Proof.Bignum.AArch64.Mont
import VerifiedGarbage.Proof.Bignum.AArch64.PcCT
import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
import VerifiedGarbage.Proof.Bignum.AArch64.PcVerified
import VerifiedGarbage.Proof.Bignum.AArch64.PdCTRest
import VerifiedGarbage.Proof.Bignum.AArch64.PdCode
import VerifiedGarbage.Proof.Bignum.AArch64.PdLoad
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCT
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCorrect
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCtRows
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightMath
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightRaw
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightRowMath
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightSetup
import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
import VerifiedGarbage.Proof.Bignum.AArch64.PubR2
import VerifiedGarbage.Proof.Bignum.AArch64.PubValid
import VerifiedGarbage.Proof.Bignum.AArch64.R2dQuot
import VerifiedGarbage.Proof.Bignum.AArch64.R2dRecip
import VerifiedGarbage.Proof.Bignum.AArch64.R2dSub
import VerifiedGarbage.Proof.Bignum.AArch64.Reduce
import VerifiedGarbage.Proof.Bignum.AArch64.Setup
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCT
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCall
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCallCT
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCallMont
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCorrect
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCount
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCross
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCrossRow
import VerifiedGarbage.Proof.Bignum.AArch64.SquareDiagonal
import VerifiedGarbage.Proof.Bignum.AArch64.SquareDiagonalCore
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightBound
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightCT
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightCarry
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightCarryWord
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightColumn
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightCorrect
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightCtRows
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightCtSetup
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightDiagonal
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightGuard
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightGuardCT
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightHead
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightInternal
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightLoad
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightMath
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightMont
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightPolynomial
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightRaw
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightRowMath
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightRows
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightSetup
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightTail
import VerifiedGarbage.Proof.Bignum.AArch64.SquareFinish
import VerifiedGarbage.Proof.Bignum.AArch64.SquareGuard
import VerifiedGarbage.Proof.Bignum.AArch64.SquareLayout
import VerifiedGarbage.Proof.Bignum.AArch64.SquareMac
import VerifiedGarbage.Proof.Bignum.AArch64.SquarePrefix
import VerifiedGarbage.Proof.Bignum.AArch64.SquareRaw
import VerifiedGarbage.Proof.Bignum.AArch64.SquareRedc
import VerifiedGarbage.Proof.Bignum.AArch64.SquareRedcLoop
import VerifiedGarbage.Proof.Bignum.AArch64.SquareRedcRow
import VerifiedGarbage.Proof.Bignum.AArch64.SquareRedcStep
import VerifiedGarbage.Proof.Bignum.AArch64.SquareRow
import VerifiedGarbage.Proof.Bignum.AArch64.SquareTiledRow
import VerifiedGarbage.Proof.Bignum.AArch64.SquareZero
import VerifiedGarbage.Proof.Bignum.AArch64.Store
import VerifiedGarbage.Proof.Bignum.AArch64.WideDiagonal
import VerifiedGarbage.Proof.Bignum.AArch64.WideZero
import VerifiedGarbage.Proof.Bignum.CrtMath
import VerifiedGarbage.Proof.Bignum.ExternalWords
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.Triangular
import VerifiedGarbage.Proof.Dsa.AArch64.AcceptedSpec
import VerifiedGarbage.Proof.Dsa.AArch64.Add
import VerifiedGarbage.Proof.Dsa.AArch64.AddCallCT
import VerifiedGarbage.Proof.Dsa.AArch64.Arithmetic
import VerifiedGarbage.Proof.Dsa.AArch64.BodyCT
import VerifiedGarbage.Proof.Dsa.AArch64.BoundaryCT
import VerifiedGarbage.Proof.Dsa.AArch64.BufferFrame
import VerifiedGarbage.Proof.Dsa.AArch64.Call2
import VerifiedGarbage.Proof.Dsa.AArch64.CallAddCT
import VerifiedGarbage.Proof.Dsa.AArch64.CallOperands
import VerifiedGarbage.Proof.Dsa.AArch64.Child
import VerifiedGarbage.Proof.Dsa.AArch64.CopyMasked
import VerifiedGarbage.Proof.Dsa.AArch64.DomainShapeCT
import VerifiedGarbage.Proof.Dsa.AArch64.EnterLeave
import VerifiedGarbage.Proof.Dsa.AArch64.EntryFieldsFrame
import VerifiedGarbage.Proof.Dsa.AArch64.EntryScratch
import VerifiedGarbage.Proof.Dsa.AArch64.Failure
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ArenaSource
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ArithmeticFrame
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.AttemptStatus
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.BufferSeparate
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CandidateArguments
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CandidateArithmetic
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CandidateFromFrame
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CandidateReduction
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CandidateStores
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CandidateWidth
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CheckPrime
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CheckPrimeReturnCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ChunkCheck
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ChunkTake
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ContextGeneratorFrame
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ContextSearchFrame
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ContextSeed
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ContextSlice
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ContextSuccess
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ControlCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ControllerFrame
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CopyBytes
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.DecrementOdd
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Double
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.DrawBuffer
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.DrawCopy
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.DrawCopyArgs
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.DrawPrepared
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.DrawRoundCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.FinishDomain
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ForceSample
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ForceWitness
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.FrameWord
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorArguments
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorBody
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorCheck
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorDecisionCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorEvaluate
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorFields
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorFootprint
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorFromFrame
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorInput
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorIterationCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorLoads
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorLoopCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorModulus
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorOutput
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorPower
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorPowerFresh
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorRange
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorRangeCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorResult
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorStages
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorStatus
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorStepCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Hash
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.HashCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.HashChoice
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.HashFrame
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.HashSequence
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.HashSequenceCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.HashShape
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.HashStep
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.HashValue
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Increment
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.KernelFrame
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.LoadWitness
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.LoopExhausted
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.LoopInit
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.LoopRound
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.LoopStep
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ModulusFrame
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ModulusHeader
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ModulusWords
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.NativeGenerator
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.NativeSearch
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.NativeSearchCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.OnSuccess
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.OnSuccessCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PAttempt
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PAttemptArgs
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PAttemptTailCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PBuild
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PBuildValue
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PConstruct
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PConstructReadyCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PConstructTest
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PConstructTestCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PHashArgs
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PHashCopyCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PHashOne
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PPrimalityCallCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PPrimalityReadyCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PPrimalityTestCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PSearchLoopCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PSeedHash
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PShape
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PShapeArgs
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PShapeCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PTestFull
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PTestFullCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PTestSmall
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PTestSmallCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Pack
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PackCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PackInto
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PackPart
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ParameterInvariant
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ParameterIterationCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeArguments
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeCallCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeConstants
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeFootprint
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeFromFrame
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeFromFrameCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeLoop
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeLoopCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeR2
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeReject
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeResult
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeSetupCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeTapeCheck
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.QArgs
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.QBuild
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.QCandidate
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.QShape
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.QShapeCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.QShapeEnds
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Reduce
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ReduceFromFrame
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ReductionExponent
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.RoundHeader
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.RoundTail
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.RoundTailResult
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Sample
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SampleRoundCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SampleRoundHeader
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SearchAdvance
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SearchBodyCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SearchEntryCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SearchIterationCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SearchStable
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SearchStatus
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SearchTailReadyCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedAdd
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedAddCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedAttempt
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedByte
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedGenerator
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedGeneratorCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedGeneratorFinish
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedGeneratorFinishCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedPack
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedPhaseStableCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedPrime
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedPrimeCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedPrimeFinish
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedPrimeFinishCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedSearchStateCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedSubgroup
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedSubgroupCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SourceFrame
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SourceSlice
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.StoredWitness
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.StoredWitnessCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Subgroup
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SubgroupReadyCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Subtract
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.TapeCheck
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.TapeLoop
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.TrialCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Validate
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ValidateArgs
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ValidateCore
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.WitnessRange
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.WorkspaceBase
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.WorkspaceCTState
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.WorkspaceWords
import VerifiedGarbage.Proof.Dsa.AArch64.KeyPointers
import VerifiedGarbage.Proof.Dsa.AArch64.Load
import VerifiedGarbage.Proof.Dsa.AArch64.LoadCheckCT
import VerifiedGarbage.Proof.Dsa.AArch64.LowerScan
import VerifiedGarbage.Proof.Dsa.AArch64.Masks
import VerifiedGarbage.Proof.Dsa.AArch64.ModulusMinus
import VerifiedGarbage.Proof.Dsa.AArch64.Multiply
import VerifiedGarbage.Proof.Dsa.AArch64.NewChild
import VerifiedGarbage.Proof.Dsa.AArch64.Parent
import VerifiedGarbage.Proof.Dsa.AArch64.Parity
import VerifiedGarbage.Proof.Dsa.AArch64.Power
import VerifiedGarbage.Proof.Dsa.AArch64.Prepare
import VerifiedGarbage.Proof.Dsa.AArch64.PublicCalls
import VerifiedGarbage.Proof.Dsa.AArch64.PublicExponent
import VerifiedGarbage.Proof.Dsa.AArch64.PublicKeyCT
import VerifiedGarbage.Proof.Dsa.AArch64.PublicPower
import VerifiedGarbage.Proof.Dsa.AArch64.PublicPrefix
import VerifiedGarbage.Proof.Dsa.AArch64.PublicSelect
import VerifiedGarbage.Proof.Dsa.AArch64.PublicWindow
import VerifiedGarbage.Proof.Dsa.AArch64.RandomCopy
import VerifiedGarbage.Proof.Dsa.AArch64.RandomFrame
import VerifiedGarbage.Proof.Dsa.AArch64.RangeCT
import VerifiedGarbage.Proof.Dsa.AArch64.RangeMask
import VerifiedGarbage.Proof.Dsa.AArch64.ReadyJoint
import VerifiedGarbage.Proof.Dsa.AArch64.Reduce
import VerifiedGarbage.Proof.Dsa.AArch64.ReduceCount
import VerifiedGarbage.Proof.Dsa.AArch64.ReduceInit
import VerifiedGarbage.Proof.Dsa.AArch64.ReduceLoop
import VerifiedGarbage.Proof.Dsa.AArch64.ReduceRead
import VerifiedGarbage.Proof.Dsa.AArch64.ReduceReadCT
import VerifiedGarbage.Proof.Dsa.AArch64.ReduceSetup
import VerifiedGarbage.Proof.Dsa.AArch64.ReduceStepCT
import VerifiedGarbage.Proof.Dsa.AArch64.ReleaseBytes
import VerifiedGarbage.Proof.Dsa.AArch64.Result
import VerifiedGarbage.Proof.Dsa.AArch64.ResultCall
import VerifiedGarbage.Proof.Dsa.AArch64.ScanField
import VerifiedGarbage.Proof.Dsa.AArch64.ScanFieldCT
import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleAddCT
import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleCallCT
import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleOperands
import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleReduceCT
import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleState
import VerifiedGarbage.Proof.Dsa.AArch64.Setup
import VerifiedGarbage.Proof.Dsa.AArch64.ShapeSizesCT
import VerifiedGarbage.Proof.Dsa.AArch64.SignificantLoop
import VerifiedGarbage.Proof.Dsa.AArch64.SourceSlices
import VerifiedGarbage.Proof.Dsa.AArch64.Store
import VerifiedGarbage.Proof.Dsa.AArch64.StoreSuffix
import VerifiedGarbage.Proof.Dsa.AArch64.TopMask
import VerifiedGarbage.Proof.Dsa.AArch64.WidthMask
import VerifiedGarbage.Proof.Dsa.AArch64.WorkspaceReady
import VerifiedGarbage.Proof.Dsa.AArch64.WriteScalar
import VerifiedGarbage.Proof.Dsa.AArch64.WriteScalarCT
import VerifiedGarbage.Proof.Dsa.AArch64.WriteSignature
import VerifiedGarbage.Proof.Dsa.AArch64.ZeroMask
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
import VerifiedGarbage.Proof.Dsa.Generation.QShapeMemory
import VerifiedGarbage.Proof.Dsa.Generation.RandomSuffix
import VerifiedGarbage.Proof.Dsa.Generation.SearchDomain
import VerifiedGarbage.Proof.Dsa.Generation.SeedAdd
import VerifiedGarbage.Proof.Dsa.Generation.Trial
import VerifiedGarbage.Proof.Dsa.Generation.WitnessMemory
import VerifiedGarbage.Proof.Dsa.Generation.WitnessSlice
import VerifiedGarbage.Proof.Dsa.Generation.WordFrame
import VerifiedGarbage.Proof.Dsa.Layout
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Dsa.SignVerify
import VerifiedGarbage.Proof.Dsa.SizeBounds
import VerifiedGarbage.Proof.Dsa.Zero
import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.CTDraw
import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Draw
import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Round
import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.ShapeOk
import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Sieve
import VerifiedGarbage.Proof.Ffdh.KeyScalar
import VerifiedGarbage.Proof.Ffdh.MillerRabin
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Sieve
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Stream
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Witness
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.AArch64.TaintErase
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.MillerRabin.AArch64.CallerCall
import VerifiedGarbage.Proof.MillerRabin.AArch64.CallerContext
import VerifiedGarbage.Proof.MillerRabin.AArch64.CallerRestore
import VerifiedGarbage.Proof.MillerRabin.AArch64.CallerResult
import VerifiedGarbage.Proof.MillerRabin.AArch64.Context
import VerifiedGarbage.Proof.MillerRabin.AArch64.Correct
import VerifiedGarbage.Proof.MillerRabin.AArch64.Finish
import VerifiedGarbage.Proof.MillerRabin.AArch64.Frame
import VerifiedGarbage.Proof.MillerRabin.AArch64.Prepared
import VerifiedGarbage.Proof.Poly1305.Limbs64
import VerifiedGarbage.Proof.Rsa.AArch64.CvCTMain
import VerifiedGarbage.Proof.Rsa.AArch64.CvCode
import VerifiedGarbage.Proof.Rsa.AArch64.CvFail
import VerifiedGarbage.Proof.Rsa.AArch64.Inv
import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTMrRound
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Entry
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.GcdE
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.GcdStep
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.KTail
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.LoadC
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.ModE
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MontSetup
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrBit
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrExp
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrMain
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrSelW
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrShift
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrTail
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.SharedRound
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.TrialEntry
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.TrialTable
import VerifiedGarbage.Proof.RsaKeyGen.Bits
import VerifiedGarbage.Proof.RsaKeyGen.CandMath
import VerifiedGarbage.Proof.RsaKeyGen.Halve
import VerifiedGarbage.Proof.RsaKeyGen.MrMont
import VerifiedGarbage.Proof.RsaKeyGen.Primes
import VerifiedGarbage.Proof.RsaKeyGen.TrialMath
import VerifiedGarbage.Proof.RsaOaep.AArch64.LabelCT
import VerifiedGarbage.Proof.RsaOaep.AArch64.Mgf
import VerifiedGarbage.Proof.RsaOaep.AArch64.TaintImm
import VerifiedGarbage.Proof.RsaPss.Params
import VerifiedGarbage.Spec.Pbkdf2.Generic
import VerifiedGarbage.Spec.RsaOaep
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcAdd
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCancelTile
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcColumns
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCorrect
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtLoop
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtRow
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtSquare
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcEnd
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcExtend
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcFastCancel
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcFastMath
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcFastWord
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcFinish
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLayout
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoad
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoop
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcRestore
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcRow
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcSave
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcSquare
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcStore
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcTile
meta import VerifiedGarbage.Proof.Bignum.AArch64.Bytes
meta import VerifiedGarbage.Proof.Bignum.AArch64.CarrySelect
meta import VerifiedGarbage.Proof.Bignum.AArch64.Copy
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtArith
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTExp
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTGPow
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetupLoad
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtChk
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtP
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtPow
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtSel
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWs
meta import VerifiedGarbage.Proof.Bignum.AArch64.DiagonalChain
meta import VerifiedGarbage.Proof.Bignum.AArch64.DiagonalChainCore
meta import VerifiedGarbage.Proof.Bignum.AArch64.DiagonalChainStep
meta import VerifiedGarbage.Proof.Bignum.AArch64.DiagonalChainTile
meta import VerifiedGarbage.Proof.Bignum.AArch64.Double
meta import VerifiedGarbage.Proof.Bignum.AArch64.FastFinish
meta import VerifiedGarbage.Proof.Bignum.AArch64.FastFinishCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.FastFinishSel
meta import VerifiedGarbage.Proof.Bignum.AArch64.FastFinishSelTile
meta import VerifiedGarbage.Proof.Bignum.AArch64.FastFinishSub
meta import VerifiedGarbage.Proof.Bignum.AArch64.FastFinishSubTile
meta import VerifiedGarbage.Proof.Bignum.AArch64.Mont
meta import VerifiedGarbage.Proof.Bignum.AArch64.PcCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
meta import VerifiedGarbage.Proof.Bignum.AArch64.PcVerified
meta import VerifiedGarbage.Proof.Bignum.AArch64.PdCTRest
meta import VerifiedGarbage.Proof.Bignum.AArch64.PdCode
meta import VerifiedGarbage.Proof.Bignum.AArch64.PdLoad
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCorrect
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCtRows
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightMath
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightRaw
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightRowMath
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightSetup
meta import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
meta import VerifiedGarbage.Proof.Bignum.AArch64.PubR2
meta import VerifiedGarbage.Proof.Bignum.AArch64.PubValid
meta import VerifiedGarbage.Proof.Bignum.AArch64.R2dQuot
meta import VerifiedGarbage.Proof.Bignum.AArch64.R2dRecip
meta import VerifiedGarbage.Proof.Bignum.AArch64.R2dSub
meta import VerifiedGarbage.Proof.Bignum.AArch64.Reduce
meta import VerifiedGarbage.Proof.Bignum.AArch64.Setup
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareCall
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareCallCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareCallMont
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareCorrect
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareCount
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareCross
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareCrossRow
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareDiagonal
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareDiagonalCore
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightBound
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightCarry
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightCarryWord
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightColumn
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightCorrect
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightCtRows
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightCtSetup
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightDiagonal
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightGuard
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightGuardCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightHead
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightInternal
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightLoad
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightMath
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightMont
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightPolynomial
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightRaw
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightRowMath
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightRows
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightSetup
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightTail
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareFinish
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareGuard
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareLayout
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareMac
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquarePrefix
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareRaw
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareRedc
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareRedcLoop
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareRedcRow
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareRedcStep
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareRow
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareTiledRow
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareZero
meta import VerifiedGarbage.Proof.Bignum.AArch64.Store
meta import VerifiedGarbage.Proof.Bignum.AArch64.WideDiagonal
meta import VerifiedGarbage.Proof.Bignum.AArch64.WideZero
meta import VerifiedGarbage.Proof.Bignum.CrtMath
meta import VerifiedGarbage.Proof.Bignum.ExternalWords
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Bignum.Triangular
meta import VerifiedGarbage.Proof.Dsa.AArch64.AcceptedSpec
meta import VerifiedGarbage.Proof.Dsa.AArch64.Add
meta import VerifiedGarbage.Proof.Dsa.AArch64.AddCallCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Arithmetic
meta import VerifiedGarbage.Proof.Dsa.AArch64.BodyCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.BoundaryCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.BufferFrame
meta import VerifiedGarbage.Proof.Dsa.AArch64.Call2
meta import VerifiedGarbage.Proof.Dsa.AArch64.CallAddCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.CallOperands
meta import VerifiedGarbage.Proof.Dsa.AArch64.Child
meta import VerifiedGarbage.Proof.Dsa.AArch64.CopyMasked
meta import VerifiedGarbage.Proof.Dsa.AArch64.DomainShapeCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.EnterLeave
meta import VerifiedGarbage.Proof.Dsa.AArch64.EntryFieldsFrame
meta import VerifiedGarbage.Proof.Dsa.AArch64.EntryScratch
meta import VerifiedGarbage.Proof.Dsa.AArch64.Failure
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ArenaSource
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ArithmeticFrame
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.AttemptStatus
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.BufferSeparate
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CandidateArguments
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CandidateArithmetic
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CandidateFromFrame
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CandidateReduction
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CandidateStores
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CandidateWidth
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CheckPrime
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CheckPrimeReturnCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ChunkCheck
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ChunkTake
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ContextFrame
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ContextGeneratorFrame
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ContextSearchFrame
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ContextSeed
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ContextSlice
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ContextSuccess
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ControlCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ControllerFrame
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CopyBytes
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.DecrementOdd
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Double
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.DrawBuffer
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.DrawCopy
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.DrawCopyArgs
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.DrawPrepared
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.DrawRoundCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.FinishDomain
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ForceSample
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ForceWitness
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.FrameWord
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorArguments
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorBody
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorCheck
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorDecisionCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorEvaluate
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorFields
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorFootprint
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorFromFrame
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorInput
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorIterationCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorLoads
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorLoopCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorModulus
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorOutput
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorPower
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorPowerFresh
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorRange
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorRangeCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorResult
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorStages
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorStatus
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorStepCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Hash
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.HashCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.HashChoice
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.HashFrame
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.HashSequence
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.HashSequenceCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.HashShape
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.HashStep
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.HashValue
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Increment
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.KernelFrame
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.LoadWitness
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.LoopExhausted
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.LoopInit
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.LoopRound
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.LoopStep
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ModulusFrame
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ModulusHeader
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ModulusWords
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.NativeGenerator
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.NativeSearch
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.NativeSearchCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.OnSuccess
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.OnSuccessCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PAttempt
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PAttemptArgs
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PAttemptTailCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PBuild
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PBuildValue
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PConstruct
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PConstructReadyCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PConstructTest
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PConstructTestCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PHashArgs
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PHashCopyCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PHashOne
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PPrimalityCallCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PPrimalityReadyCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PPrimalityTestCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PSearchLoopCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PSeedHash
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PShape
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PShapeArgs
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PShapeCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PTestFull
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PTestFullCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PTestSmall
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PTestSmallCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Pack
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PackCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PackInto
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PackPart
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ParameterInvariant
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ParameterIterationCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeArguments
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeCallCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeConstants
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeFootprint
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeFromFrame
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeFromFrameCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeLoop
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeLoopCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeR2
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeReject
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeResult
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeSetupCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeTapeCheck
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.QArgs
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.QBuild
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.QCandidate
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.QShape
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.QShapeCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.QShapeEnds
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Reduce
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ReduceFromFrame
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ReductionExponent
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.RoundHeader
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.RoundTail
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.RoundTailResult
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Sample
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SampleRoundCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SampleRoundHeader
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SearchAdvance
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SearchBodyCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SearchEntryCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SearchIterationCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SearchStable
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SearchStatus
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SearchTailReadyCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedAdd
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedAddCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedAttempt
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedByte
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedGenerator
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedGeneratorCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedGeneratorFinish
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedGeneratorFinishCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedPack
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedPhaseStableCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedPrime
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedPrimeCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedPrimeFinish
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedPrimeFinishCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedSearchStateCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedSubgroup
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedSubgroupCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SourceFrame
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SourceSlice
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.StoredWitness
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.StoredWitnessCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Subgroup
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SubgroupReadyCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Subtract
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.TapeCheck
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.TapeLoop
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.TapeState
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.TrialCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Validate
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ValidateArgs
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ValidateCore
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.WitnessRange
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.WorkspaceBase
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.WorkspaceCTState
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.WorkspaceWords
meta import VerifiedGarbage.Proof.Dsa.AArch64.KeyPointers
meta import VerifiedGarbage.Proof.Dsa.AArch64.Load
meta import VerifiedGarbage.Proof.Dsa.AArch64.LoadCheckCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.LowerScan
meta import VerifiedGarbage.Proof.Dsa.AArch64.Masks
meta import VerifiedGarbage.Proof.Dsa.AArch64.ModulusMinus
meta import VerifiedGarbage.Proof.Dsa.AArch64.Multiply
meta import VerifiedGarbage.Proof.Dsa.AArch64.NewChild
meta import VerifiedGarbage.Proof.Dsa.AArch64.Parent
meta import VerifiedGarbage.Proof.Dsa.AArch64.Parity
meta import VerifiedGarbage.Proof.Dsa.AArch64.Power
meta import VerifiedGarbage.Proof.Dsa.AArch64.Prepare
meta import VerifiedGarbage.Proof.Dsa.AArch64.PublicCalls
meta import VerifiedGarbage.Proof.Dsa.AArch64.PublicExponent
meta import VerifiedGarbage.Proof.Dsa.AArch64.PublicKeyCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.PublicPower
meta import VerifiedGarbage.Proof.Dsa.AArch64.PublicPrefix
meta import VerifiedGarbage.Proof.Dsa.AArch64.PublicSelect
meta import VerifiedGarbage.Proof.Dsa.AArch64.PublicWindow
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomCopy
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomFrame
meta import VerifiedGarbage.Proof.Dsa.AArch64.RangeCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.RangeMask
meta import VerifiedGarbage.Proof.Dsa.AArch64.ReadyJoint
meta import VerifiedGarbage.Proof.Dsa.AArch64.Reduce
meta import VerifiedGarbage.Proof.Dsa.AArch64.ReduceCount
meta import VerifiedGarbage.Proof.Dsa.AArch64.ReduceInit
meta import VerifiedGarbage.Proof.Dsa.AArch64.ReduceLoop
meta import VerifiedGarbage.Proof.Dsa.AArch64.ReduceRead
meta import VerifiedGarbage.Proof.Dsa.AArch64.ReduceReadCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.ReduceSetup
meta import VerifiedGarbage.Proof.Dsa.AArch64.ReduceStepCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.ReleaseBytes
meta import VerifiedGarbage.Proof.Dsa.AArch64.Result
meta import VerifiedGarbage.Proof.Dsa.AArch64.ResultCall
meta import VerifiedGarbage.Proof.Dsa.AArch64.ScanField
meta import VerifiedGarbage.Proof.Dsa.AArch64.ScanFieldCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleAddCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleCallCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleOperands
meta import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleReduceCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleState
meta import VerifiedGarbage.Proof.Dsa.AArch64.Setup
meta import VerifiedGarbage.Proof.Dsa.AArch64.ShapeSizesCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.SignificantLoop
meta import VerifiedGarbage.Proof.Dsa.AArch64.SourceSlices
meta import VerifiedGarbage.Proof.Dsa.AArch64.Store
meta import VerifiedGarbage.Proof.Dsa.AArch64.StoreSuffix
meta import VerifiedGarbage.Proof.Dsa.AArch64.TopMask
meta import VerifiedGarbage.Proof.Dsa.AArch64.WidthMask
meta import VerifiedGarbage.Proof.Dsa.AArch64.WorkspaceReady
meta import VerifiedGarbage.Proof.Dsa.AArch64.WriteScalar
meta import VerifiedGarbage.Proof.Dsa.AArch64.WriteScalarCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.WriteSignature
meta import VerifiedGarbage.Proof.Dsa.AArch64.ZeroMask
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
meta import VerifiedGarbage.Proof.Dsa.Generation.QShapeMemory
meta import VerifiedGarbage.Proof.Dsa.Generation.RandomSuffix
meta import VerifiedGarbage.Proof.Dsa.Generation.SearchDomain
meta import VerifiedGarbage.Proof.Dsa.Generation.SeedAdd
meta import VerifiedGarbage.Proof.Dsa.Generation.Trial
meta import VerifiedGarbage.Proof.Dsa.Generation.WitnessMemory
meta import VerifiedGarbage.Proof.Dsa.Generation.WitnessSlice
meta import VerifiedGarbage.Proof.Dsa.Generation.WordFrame
meta import VerifiedGarbage.Proof.Dsa.Layout
meta import VerifiedGarbage.Proof.Dsa.PackedBytes
meta import VerifiedGarbage.Proof.Dsa.SignVerify
meta import VerifiedGarbage.Proof.Dsa.SizeBounds
meta import VerifiedGarbage.Proof.Dsa.Zero
meta import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.CTDraw
meta import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Draw
meta import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Round
meta import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Shape
meta import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.ShapeOk
meta import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Sieve
meta import VerifiedGarbage.Proof.Ffdh.KeyScalar
meta import VerifiedGarbage.Proof.Ffdh.MillerRabin
meta import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
meta import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Sieve
meta import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Stream
meta import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Witness
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
meta import VerifiedGarbage.Proof.Framework.AArch64.Syms
meta import VerifiedGarbage.Proof.Framework.AArch64.TaintErase
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Bswap
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Proof.Mgf1.Bytes
meta import VerifiedGarbage.Proof.MillerRabin.AArch64.CallerCall
meta import VerifiedGarbage.Proof.MillerRabin.AArch64.CallerContext
meta import VerifiedGarbage.Proof.MillerRabin.AArch64.CallerRestore
meta import VerifiedGarbage.Proof.MillerRabin.AArch64.CallerResult
meta import VerifiedGarbage.Proof.MillerRabin.AArch64.Context
meta import VerifiedGarbage.Proof.MillerRabin.AArch64.Correct
meta import VerifiedGarbage.Proof.MillerRabin.AArch64.Finish
meta import VerifiedGarbage.Proof.MillerRabin.AArch64.Frame
meta import VerifiedGarbage.Proof.MillerRabin.AArch64.Prepared
meta import VerifiedGarbage.Proof.Poly1305.Limbs64
meta import VerifiedGarbage.Proof.Rsa.AArch64.CvCTMain
meta import VerifiedGarbage.Proof.Rsa.AArch64.CvCode
meta import VerifiedGarbage.Proof.Rsa.AArch64.CvFail
meta import VerifiedGarbage.Proof.Rsa.AArch64.Inv
meta import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops
meta import VerifiedGarbage.Proof.Rsa.Octets
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTMrRound
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Entry
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.GcdE
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.GcdStep
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.KTail
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.LoadC
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.ModE
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MontSetup
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrBit
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrExp
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrMain
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrSelW
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrShift
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrTail
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.SharedRound
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.TrialEntry
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.TrialTable
meta import VerifiedGarbage.Proof.RsaKeyGen.Bits
meta import VerifiedGarbage.Proof.RsaKeyGen.CandMath
meta import VerifiedGarbage.Proof.RsaKeyGen.Halve
meta import VerifiedGarbage.Proof.RsaKeyGen.MrMont
meta import VerifiedGarbage.Proof.RsaKeyGen.Primes
meta import VerifiedGarbage.Proof.RsaKeyGen.TrialMath
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.LabelCT
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.Mgf
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.TaintImm
meta import VerifiedGarbage.Proof.RsaPss.Params
meta import VerifiedGarbage.Spec.Pbkdf2.Generic
meta import VerifiedGarbage.Spec.RsaOaep

/-! # Timing of the complete native DSA parameter search -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.Dsa.AArch64.Generation VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64
open VG.Proof.MillerRabin.AArch64

def ParameterStart (pLen qLen : Nat) (p : ParameterPublic) (s : State) : Prop :=
  (∃ W, GenerationMemory p.context W s ∧ W 16 = BitVec.ofNat 64 p.randUsed) ∧
  p.context.geo.pLen = pLen ∧ p.context.geo.qLen = qLen

def ParameterPublic.start (p : ParameterPublic) : ParameterPublic :=
  { p with seedUsed := 0, seedBound := Nat.zero_le _ }

theorem parameter_reset {pLen qLen : Nat} {p : ParameterPublic} {s : State}
    (h : ParameterStart pLen qLen p s) :
    WP isa (.block (tapeReset seedTape)) s (ParameterBefore pLen qLen p.start) := by
  obtain ⟨⟨W, hm, hu⟩, hp, hq⟩ := h
  obtain ⟨V, R⟩ := hm.rep
  refine WP.mono (tapeReset_frame_ok hm.layout R seedTape (by decide) (by decide))
    fun t ⟨Lt, Rt, ft, kt⟩ => ?_
  have ff : Frame p.context.changed s.mem t.mem := by
    apply GenerationContext.frame_single
    intro a ha
    apply ft a
    right
    have hn := ha ⟨p.context.geo.F, frameBytes⟩ (by simp)
    change ¬ ofs p.context.geo.F a < frameBytes at hn
    change 88 ≤ ofs p.context.geo.F a
    unfold frameBytes at hn
    omega
  have ht := hm.frame Lt ⟨V, Rt⟩ (by
    intro k hk
    simp only [generationSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
    ff kt.rd kt.wr
  exact ⟨⟨_, ht, by simp [seedTape, upd, ParameterPublic.start], by simpa [seedTape, upd, ParameterPublic.start] using hu⟩,
    hp, hq⟩

theorem nativeParameters_ct (H : GenerationHashes) (M : Mont)  (K : Kernel)
    (pLen qLen : Nat) (sizes : GenerationSizes pLen qLen) :
    RelCT isa (Two (ParameterStart pLen qLen))
      (parameterSearch H.sha1 H.sha256 M.mm K.run pLen qLen) (fun _ _ => True) := by
  unfold parameterSearch tapeLoop
  refine RelCT.seq (two_post (two_taint [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide))
    (fun _ _ h => parameter_reset h)) ?_
  exact two_map ParameterPublic.start (fun _ _ h => h) (parameterLoop_ct H M K pLen qLen sizes)

end VG.Proof.Dsa.AArch64.Generation
