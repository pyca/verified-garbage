module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeLoopCTData
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeLoopCTData
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.LoopInit
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.LoopInit
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Omega
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
import VerifiedGarbage.Proof.Bignum.AArch64.CrtBuild
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
import VerifiedGarbage.Proof.Bignum.AArch64.CrtChk
import VerifiedGarbage.Proof.Bignum.AArch64.CrtExp
import VerifiedGarbage.Proof.Bignum.AArch64.CrtGPow
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
import VerifiedGarbage.Proof.Dsa.AArch64.Arithmetic
import VerifiedGarbage.Proof.Dsa.AArch64.BufferFrame
import VerifiedGarbage.Proof.Dsa.AArch64.CopyMasked
import VerifiedGarbage.Proof.Dsa.AArch64.EnterLeave
import VerifiedGarbage.Proof.Dsa.AArch64.Failure
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ControlCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.DrawBuffer
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.DrawCopy
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.DrawCopyArgs
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.DrawPrepared
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.DrawRoundCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ForceSample
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ForceWitness
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.KernelFrame
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.LoadWitness
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.LoopExhausted
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.LoopRound
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.LoopStep
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ModulusFrame
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ModulusHeader
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ModulusWords
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeConstants
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeR2
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeTapeCheck
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeTrial
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.RoundHeader
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.RoundTail
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.RoundTailResult
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Sample
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SampleRoundCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SampleRoundHeader
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SourceFrame
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.StoredWitness
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.StoredWitnessCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.TrialCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.WitnessRange
import VerifiedGarbage.Proof.Dsa.AArch64.Load
import VerifiedGarbage.Proof.Dsa.AArch64.Prepare
import VerifiedGarbage.Proof.Dsa.AArch64.RandomCopy
import VerifiedGarbage.Proof.Dsa.AArch64.Setup
import VerifiedGarbage.Proof.Dsa.AArch64.SourceSlices
import VerifiedGarbage.Proof.Dsa.AArch64.Store
import VerifiedGarbage.Proof.Dsa.AArch64.StoreSuffix
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Dsa.BitLengthBounds
import VerifiedGarbage.Proof.Dsa.Digest
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Dsa.Generation.PEncoding
import VerifiedGarbage.Proof.Dsa.Generation.PReduction
import VerifiedGarbage.Proof.Dsa.Generation.Primality
import VerifiedGarbage.Proof.Dsa.Generation.QCandidate
import VerifiedGarbage.Proof.Dsa.Generation.Trial
import VerifiedGarbage.Proof.Dsa.Generation.WitnessMemory
import VerifiedGarbage.Proof.Dsa.Generation.WitnessSlice
import VerifiedGarbage.Proof.Dsa.PackedBytes
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
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Framework.WriteBytes
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
import VerifiedGarbage.Proof.Rsa.AArch64.CvFail
import VerifiedGarbage.Proof.Rsa.AArch64.CvLoad
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
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtBuild
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtChk
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtExp
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtGPow
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
meta import VerifiedGarbage.Proof.Dsa.AArch64.Arithmetic
meta import VerifiedGarbage.Proof.Dsa.AArch64.BufferFrame
meta import VerifiedGarbage.Proof.Dsa.AArch64.CopyMasked
meta import VerifiedGarbage.Proof.Dsa.AArch64.EnterLeave
meta import VerifiedGarbage.Proof.Dsa.AArch64.Failure
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ControlCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.DrawBuffer
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.DrawCopy
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.DrawCopyArgs
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.DrawPrepared
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.DrawRoundCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ForceSample
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ForceWitness
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.KernelFrame
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.LoadWitness
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.LoopExhausted
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.LoopRound
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.LoopStep
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ModulusFrame
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ModulusHeader
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ModulusWords
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeConstants
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeR2
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeTapeCheck
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeTrial
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.RoundHeader
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.RoundTail
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.RoundTailResult
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Sample
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SampleRoundCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SampleRoundHeader
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SourceFrame
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.StoredWitness
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.StoredWitnessCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.TrialCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.WitnessRange
meta import VerifiedGarbage.Proof.Dsa.AArch64.Load
meta import VerifiedGarbage.Proof.Dsa.AArch64.Prepare
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomCopy
meta import VerifiedGarbage.Proof.Dsa.AArch64.Setup
meta import VerifiedGarbage.Proof.Dsa.AArch64.SourceSlices
meta import VerifiedGarbage.Proof.Dsa.AArch64.Store
meta import VerifiedGarbage.Proof.Dsa.AArch64.StoreSuffix
meta import VerifiedGarbage.Proof.Dsa.Arithmetic
meta import VerifiedGarbage.Proof.Dsa.BitLengthBounds
meta import VerifiedGarbage.Proof.Dsa.Digest
meta import VerifiedGarbage.Proof.Dsa.Encoding
meta import VerifiedGarbage.Proof.Dsa.Generation.Memory
meta import VerifiedGarbage.Proof.Dsa.Generation.PEncoding
meta import VerifiedGarbage.Proof.Dsa.Generation.PReduction
meta import VerifiedGarbage.Proof.Dsa.Generation.Primality
meta import VerifiedGarbage.Proof.Dsa.Generation.QCandidate
meta import VerifiedGarbage.Proof.Dsa.Generation.Trial
meta import VerifiedGarbage.Proof.Dsa.Generation.WitnessMemory
meta import VerifiedGarbage.Proof.Dsa.Generation.WitnessSlice
meta import VerifiedGarbage.Proof.Dsa.PackedBytes
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
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Bswap
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Framework.WriteBytes
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
meta import VerifiedGarbage.Proof.Rsa.AArch64.CvFail
meta import VerifiedGarbage.Proof.Rsa.AArch64.CvLoad
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

/-! # Constant-time composition of the complete blinded primality loop -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum.AArch64 VG.Proof.MillerRabin.AArch64

private def loopInv (len drawBytes n : Nat) : State → State → Prop :=
  Two fun p s => p.draw.prime.rand.length - p.draw.used = n ∧ LoopBefore len drawBytes p s

section
variable (M : Mont) (K : Kernel) (len drawBytes : Nat)
variable {hc₁ hc₂ : VG.Taint.Hint VG.AArch64.Taint.T}
variable (ht₁ : (taint.check (Taint.ofRegs [.x0])
  (.block (Impl.Dsa.AArch64.Generation.drawCopyArgs len drawBytes)) hc₁).isSome = true)
variable (ht₂ : (taint.check (Taint.ofRegs [.x1])
  (.block (Impl.Dsa.AArch64.Generation.forceWitness len)) hc₂).isSome = true)

include ht₁ ht₂

private theorem loop_step (n : Nat) :
    RelCT isa (loopInv len drawBytes n)
      (Impl.Dsa.AArch64.Generation.primeIteration
        (Impl.Dsa.AArch64.Generation.drawRound M.mm K.run len drawBytes))
      (fun s t => isa.eval (.zero .x .x3) s = isa.eval (.zero .x .x3) t ∧
        (isa.eval (.zero .x .x3) s = some false → True) ∧
        (isa.eval (.zero .x .x3) s = some true → ∃ m < n, loopInv len drawBytes m s t)) := by
  have hw : RelCT isa (loopInv len drawBytes n)
      (Impl.Dsa.AArch64.Generation.primeIteration
        (Impl.Dsa.AArch64.Generation.drawRound M.mm K.run len drawBytes))
      (Two fun p s => p.draw.prime.rand.length - p.draw.used = n ∧ LoopAfter len drawBytes p s) :=
    two_post (two_map id (fun _ _ h => h.2.iteration) (primeIteration_ct M K len drawBytes ht₁ ht₂))
      (fun _ _ h => WP.mono (primeIteration_transition M K h.2) fun _ ht => ⟨h.1, ht⟩)
  refine hw.mono (fun _ _ h => h) ?_
  rintro s t ⟨p, ⟨hn, hs⟩, ⟨_, ht⟩, hsp⟩
  refine ⟨hs.1.trans ht.1.symm, fun _ => True.intro, fun he => ?_⟩
  have hg : p.continues = true := Option.some.inj (hs.1.symm.trans he)
  have hnext := hs.2 hg
  obtain ⟨s₀, res, hstate⟩ := hnext.1
  have hroom : p.draw.used + p.draw.prime.drawBytes ≤ p.draw.prime.rand.length := hstate.usedBound
  have hdraw := p.draw.prime.drawMin
  refine ⟨p.draw.prime.rand.length - (p.draw.used + p.draw.prime.drawBytes), by omega,
    p.next, ⟨rfl, hnext⟩, ⟨rfl, ht.2 hg⟩, hsp⟩

theorem primeLoop_ct : RelCT isa (Two (LoopBefore len drawBytes))
    (.loop (Impl.Dsa.AArch64.Generation.primeIteration
      (Impl.Dsa.AArch64.Generation.drawRound M.mm K.run len drawBytes)) (.zero .x .x3)) (fun _ _ => True) := by
  rintro s t tr₁ tr₂ u v ⟨p, hs, ht, hsp⟩ e₁ e₂
  exact RelCT.loop (loopInv len drawBytes) (loop_step M K len drawBytes ht₁ ht₂)
    (p.draw.prime.rand.length - p.draw.used) s t tr₁ tr₂ u v ⟨p, ⟨rfl, hs⟩, ⟨rfl, ht⟩, hsp⟩ e₁ e₂

theorem millerRabin_ct :
    RelCT isa (Two fun p s => DrawBefore len drawBytes p s ∧ p.used ≤ p.prime.rand.length)
      (Impl.Dsa.AArch64.Generation.millerRabin M.mm K.run len drawBytes) (fun _ _ => True) := by
  unfold Impl.Dsa.AArch64.Generation.millerRabin
  refine RelCT.seq (two_post (Ψ := fun p s => LoopBefore len drawBytes ⟨p, 1, 0⟩ s)
    (two_taint [.x0] ?_ (by taint_decide)) ?_) ?_
  · intro p s t hs ht r hr
    simp only [List.mem_singleton] at hr
    subst r
    have hs := hs.1.1
    have ht := ht.1.1
    exact hs.ready.ws.x0.trans ht.ready.ws.x0.symm
  · intro p s h
    have hs := h.1.1
    exact WP.mono (primeLoopInit_ok hs h.2) fun _ ht =>
      ⟨⟨s, primeRest p.prime 1 0 p.used, ht⟩, h.1.2⟩
  · exact two_map (fun p : DrawPublic => (⟨p, 1, 0⟩ : PrimeIterationPublic))
      (fun _ _ h => h) (primeLoop_ct M K len drawBytes ht₁ ht₂)

end
end VG.Proof.Dsa.AArch64.Generation
