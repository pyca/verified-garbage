module
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTMs
public import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Sieve
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTBase

meta import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.CTTest
meta import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Main
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTFront
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTFront
import VerifiedGarbage.Proof.RsaKeyGen.Slots
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Halve
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrShift
import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
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
import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
import VerifiedGarbage.Proof.Bignum.AArch64.CrtGPow
import VerifiedGarbage.Proof.Bignum.AArch64.CrtSel
import VerifiedGarbage.Proof.Bignum.AArch64.CrtTab
import VerifiedGarbage.Proof.Bignum.AArch64.CrtUnit
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
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.Triangular
import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.CTDraw
import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.CTTest
import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Draw
import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Main
import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Result
import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Round
import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.ShapeOk
import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Tests
import VerifiedGarbage.Proof.Ffdh.MillerRabin
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Sieve
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Witness
import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
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
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTTail
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Entry
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.GcdE
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.GcdStep
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.KTail
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.LoadC
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.ModE
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MontSetup
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrBit
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrExp
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrSelW
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrTail
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
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtGPow
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtSel
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtTab
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtUnit
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
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Bignum.Triangular
meta import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.CTDraw
meta import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Draw
meta import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Result
meta import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Round
meta import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Shape
meta import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.ShapeOk
meta import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Tests
meta import VerifiedGarbage.Proof.Ffdh.MillerRabin
meta import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
meta import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Sieve
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
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTTail
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Entry
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.GcdE
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.GcdStep
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.KTail
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.LoadC
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.ModE
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MontSetup
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrBit
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrExp
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrSelW
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrShift
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrTail
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.TrialEntry
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.TrialTable
meta import VerifiedGarbage.Proof.RsaKeyGen.Bits
meta import VerifiedGarbage.Proof.RsaKeyGen.CandMath
meta import VerifiedGarbage.Proof.RsaKeyGen.Halve
meta import VerifiedGarbage.Proof.RsaKeyGen.MrMont
meta import VerifiedGarbage.Proof.RsaKeyGen.Primes
meta import VerifiedGarbage.Proof.RsaKeyGen.TrialMath

/-!
# An FFDH parameter candidate on AArch64: constant time of the shape's checks

The congruence (`residue_ct`), RSA's table (`tableWrite_ct`), the sieve
(`sieve_ct`, RSA's `trialEntry_ct` for 13 words and an entry) and `q`
(`halveQ_ct`), each from the working space and what it reads.
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.ParameterCandidate

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen VG.Impl.RsaKeyGen.AArch64.Candidate VG.Impl.Ffdh.AArch64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero eval_nonzero)
open VG.Impl.Bignum.Public (aN aX aAcc aTmp aR2 aXm aY aOne sK sCnt)

/-- The working space of `p`'s words. -/
def WQ (L : WsP) (s : State) : Prop := Ws s L.B L.Z L.w

theorem residue_ct : RelCT isa (Two WQ) (seqs residue) fun _ _ => True :=
  ws_ct0 (fun L : WsP => L.B) (fun L : WsP => L.Z) (fun L : WsP => L.w) (fun _ _ h => h) (by taint_decide)

theorem tableWrite_ct : RelCT isa (Two WQ) tableWrite fun _ _ => True :=
  ws_block_ct0 (fun L : WsP => L.B) (fun L : WsP => L.Z) (fun L : WsP => L.w) (fun _ _ h => h) (by taint_decide)

/-! ## The sieve -/

/-- RSA's public data, for the working space alone. -/
def fpubOf (L : WsP) : VG.Proof.RsaKeyGen.AArch64.FPub := ⟨L.B, L.Z, L.w, [], 0, 0, 0, [], 0, 0, 0, 0, ⟨false, false, false, none⟩⟩

/-- Before the sieve. -/
def SV (L : WsP) (s : State) : Prop :=
  Ws s L.B L.Z L.w ∧ slot L.w aTab + 2048 ≤ L.Z ∧ TabOk s.mem L.B L.w

/-- Before word `k` of the table. -/
def SI (L : WsP) (k : Nat) (s : State) : Prop :=
  Ws s L.B L.Z L.w ∧ slot L.w aTab + 2048 ≤ L.Z ∧ s.gpr .x9 = off L.B (slot L.w aTab + 8 * k) ∧
    s.gpr .x10 = BitVec.ofNat 64 (13 - k) ∧ s.gpr .x7 = 0 ∧ s.gpr .x8 = mask true ∧ TabOk s.mem L.B L.w ∧
    s.gpr .x1 = mask (anyPre (wv s.mem L.B (slot L.w aN) L.w) (4 * k))

/-- After the loop. -/
def SIE (L : WsP) (s : State) : Prop :=
  Ws s L.B L.Z L.w ∧ slot L.w aTab + 2048 ≤ L.Z ∧ s.gpr .x9 = off L.B (slot L.w aTab + 8 * 13) ∧
    s.gpr .x7 = 0 ∧ s.gpr .x8 = mask true ∧ TabOk s.mem L.B L.w

theorem sieveIter_ok {L : WsP} {k : Nat} {s : State} (hk : k < 13) (h : SI L k s) :
    WP isa (seqs (([.block [ld .x17 .x9, next .x9]] : List (Prog isa)) ++ trialEntry 0 ++ trialEntry 1 ++
      trialEntry 2 ++ trialEntry 3 ++ ([.block [.subImm .x .x10 .x10 1]] : List (Prog isa)))) s fun t =>
      isa.eval (.nonzero .x .x10) t = some (decide (k + 1 < 13)) ∧ (k + 1 < 13 → SI L (k + 1) t) ∧
        (k + 1 = 13 → SIE L t) := by
  obtain ⟨hw, hT, h9, h10, h7, h8, htab, h1⟩ := h
  refine WP.mono (tlIter_ok (s₀ := s) rfl hT (by omega) htab ⟨hw, h7, h8, rfl, Keep.refl _ _⟩ h9 h1)
    fun t ⟨⟨hI, h9', h1'⟩, h10'⟩ => ⟨?_, fun _ => ⟨hI.ws, hT, h9', ?_, hI.x7, hI.x8, fun i hi => by
      rw [hI.mem]; exact htab i hi, by rw [h1', hI.mem]⟩, fun e => ⟨hI.ws, hT, by rw [h9', e], hI.x7, hI.x8,
        fun i hi => by rw [hI.mem]; exact htab i hi⟩⟩
  · rw [eval_nonzero, h10', h10, sub1_bne (by omega) (by omega)]
    exact congrArg some (decide_eq_decide.mpr (by omega))
  · rw [h10', h10]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega

theorem sieveBody_ct : RelCT isa (Two fun (a : WsP × Nat) s => a.2 < 13 ∧ SI a.1 a.2 s)
    (seqs (([.block [ld .x17 .x9, next .x9]] : List (Prog isa)) ++ trialEntry 0 ++ trialEntry 1 ++
      trialEntry 2 ++ trialEntry 3 ++ ([.block [.subImm .x .x10 .x10 1]] : List (Prog isa)))) fun _ _ => True := by
  simp only [List.append_assoc, List.singleton_append]
  have ne : ∀ j, trialEntry j ≠ [] := fun j => by unfold trialEntry; exact List.cons_ne_nil _ _
  refine seqs_cons_ct (by simp [ne]) (RelCT.seq (two_post (Ψ := fun a s => TBI (fpubOf a.1, a.2) s)
    (two_taint [.x9] (fun p s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.2.2.1, h₂.2.2.2.1]) (by taint_decide))
    (fun p s h => ?_)) ?_)
  · obtain ⟨hk, hw, hT, h9, -, h7, h8, htab, -⟩ := h
    exact WP.mono (tlLoad_ok hT (by omega) htab ⟨hw, h7, h8, rfl, Keep.refl _ _⟩ h9) fun t ⟨⟨h17, _, hm⟩, k⟩ =>
      ⟨hw.congr' (rs := []) (fun x _ => by rw [hm]) (by simp) k (by decide), by omega, h17,
        (k.gpr .x7 (by decide)).trans h7, (k.gpr .x8 (by decide)).trans h8⟩
  refine two_map (Φ' := TBI) (fun a : WsP × Nat => (fpubOf a.1, a.2)) (fun _ _ h => h) ?_
  refine RelCT.seqs_append (ne 0) (by simp) (RelCT.seq (trialEntry_ct (by decide) (by taint_decide) (by taint_decide)) ?_)
  refine RelCT.seqs_append (ne 1) (by simp) (RelCT.seq (trialEntry_ct (by decide) (by taint_decide) (by taint_decide)) ?_)
  refine RelCT.seqs_append (ne 2) (by simp) (RelCT.seq (trialEntry_ct (by decide) (by taint_decide) (by taint_decide)) ?_)
  refine RelCT.seqs_append (ne 3) (by simp) (RelCT.seq (trialEntry_ct (by decide) (by taint_decide) (by taint_decide)) ?_)
  exact two_taint [] (pins_nil₀ _) (by taint_decide)

/-- The sieve leaks the same in runs with the same working space. -/
theorem sieve_ct : RelCT isa (Two SV) (seqs sieve) fun _ _ => True := by
  rw [sieve_eq]
  refine RelCT.seqs_append (by simp) (by simp [trialEntry]) (RelCT.seq (R := Two fun L s => TBI (fpubOf L, 13) s) ?_ ?_)
  · simp only [seqs]
    refine RelCT.seq (two_post (ws_block_ct0 (fun L : WsP => L.B) (fun L : WsP => L.Z) (fun L : WsP => L.w)
      (fun _ _ h => h.1) (by taint_decide)) (Ψ := fun L s => 0 < 13 ∧ SI L 0 s) fun L s ⟨hw, hT, htab⟩ => ?_)
      (RelCT.seq (two_loop (Φ := SI) (Ψ := SIE) (fun _ => 13) sieveBody_ct fun _ _ _ hk h => sieveIter_ok hk h)
        (two_post (two_taint [.x9] (fun L s₁ s₂ h₁ h₂ r hr => by
          simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.2.1, h₂.2.2.1]) (by taint_decide))
          fun L s ⟨hw, hT, h9, h7, h8, htab⟩ => ?_))
    · refine WP.mono (sieveInit_ok hw) fun t ⟨⟨h9, h10, h1, h7, h8, hm⟩, k⟩ => ⟨by decide, ?_⟩
      exact ⟨hw.congr' (rs := []) (by rw [hm]; exact Frm.refl _ _ _) (by simp) k (by decide), hT, h9, h10, h7, h8,
        fun i hi => by rw [hm]; exact htab i hi, by rw [h1, Nat.mul_zero, anyPre_zero]; rfl⟩
    · have hld : InRegions (s.rd ++ s.wr) (off L.B (slot L.w aTab + 8 * 13)) 8 := hw.scr.ld (by omega)
      have ht13 : s.mem.readW (L.B + BitVec.ofNat 64 (slot L.w aTab + 8 * 13)) 64 = BitVec.ofNat 64 (tabWord 13) :=
        htab 13 (by decide)
      exact WP.mono (WP.keep (c := .block [ld .x17 .x9]) [.x17] (Q := fun t =>
          t.gpr .x17 = BitVec.ofNat 64 (tabWord 13) ∧ t.mem = s.mem) (by brun [h9, hld, ht13])
        (by decide) (by decide) (by decide +kernel))
        fun t ⟨⟨h17, hm⟩, k⟩ => ⟨hw.congr' (rs := []) (fun x _ => by rw [hm]) (by simp) k (by decide),
          show 13 < 256 by decide, h17, (k.gpr .x7 (by decide)).trans h7, (k.gpr .x8 (by decide)).trans h8⟩
  · refine two_map (Φ' := TBI) (fun L : WsP => (fpubOf L, 13)) (fun _ _ h => h) ?_
    refine RelCT.seqs_append (by simp [trialEntry]) (by simp)
      (RelCT.seq (trialEntry_ct (by decide) (by taint_decide) (by taint_decide)) ?_)
    rw [seqs_one]
    exact two_taint [.x0] (pins_ws' (fun p : VG.Proof.RsaKeyGen.AArch64.FPub × Nat => p.1.B) (fun p : VG.Proof.RsaKeyGen.AArch64.FPub × Nat => p.1.Z)
      (fun p : VG.Proof.RsaKeyGen.AArch64.FPub × Nat => p.1.w) fun _ _ h => h.1) (by taint_decide)

/-! ## `q` -/

theorem halvePass_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) :
    WP isa (seqs (.block (ws ++ base aN .x16 ++ [mov .x17 .x16, movi .x7 0, .subImm .x .x15 .x7 1]) :: halfPass))
      s fun t => Ws t B Z w := by
  have hn := h.scr.nowrap
  have hw1 := h.w1
  have hw2 := h.w2
  have sN := h.sl (show aN < 16 by decide)
  have e : seqs (.block (ws ++ base aN .x16 ++ [mov .x17 .x16, movi .x7 0, .subImm .x .x15 .x7 1]) :: halfPass) =
      .seq (.block (ws ++ base aN .x16 ++ [mov .x17 .x16, movi .x7 0, .subImm .x .x15 .x7 1])) (seqs halfPass) := rfl
  rw [e]
  refine WP.seq (WP.mono (halveHead_ok h) fun s₁ ⟨⟨h16, h17, h15, h12, hm₁⟩, k₁⟩ => ?_)
  refine WP.mono (halfPass_ok (mb := true) (h.scr.congr k₁.wr) h16 h17 h15 h12 hw1 (by omega) (by omega) (by omega)
    (.inl rfl)) fun t ⟨_, o, k₂⟩ => ?_
  rw [hm₁] at o
  exact h.congr' (Frm.of_outside (o.mono (o' := slot w aN) (n' := 8 * (w + 2)) (by omega) (by omega))
    (List.mem_singleton_self _)) (fun r hr => by rw [List.mem_singleton.mp hr]; exact KMut.ofSlot _ _ _)
    (k₁.trans k₂) (by decide)

/-- `halveQ` leaks the same in runs with the same working space. -/
theorem halveQ_ct : RelCT isa (Two WQ) (seqs halveQ) fun _ _ => True := by
  unfold halveQ
  rw [List.cons_append]
  refine ct_app' (a := _ :: halfPass) (by simp) (by simp) (Ψ := WQ) (two_post ?_ fun L s h => halvePass_ok h) ?_
  · exact ws_ct0 (fun L : WsP => L.B) (fun L : WsP => L.Z) (fun L : WsP => L.w) (fun _ _ h => h) (by taint_decide)
  · rw [seqs_one]
    exact ws_block_ct0 (fun L : WsP => L.B) (fun L : WsP => L.Z) (fun L : WsP => L.w) (fun _ _ h => h)
      (by taint_decide)

end VG.Proof.Ffdh.AArch64.ParameterCandidate
