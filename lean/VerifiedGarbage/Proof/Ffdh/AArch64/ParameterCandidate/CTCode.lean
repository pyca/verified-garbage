module

public import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.CTMain
meta import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.CTMain
public import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Code
meta import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Code
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Rsa.AArch64.CTBase
import VerifiedGarbage.Proof.Framework.RelCTAssoc
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
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.Triangular
import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.CTDraw
import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Draw
import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Result
import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Round
import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Shape
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
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTFront
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
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrShift
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
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTFront
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
# An FFDH parameter candidate on AArch64: constant time, and `Verified`

Every value of the candidate is public (`pcPub` fixes the arguments and the
octets of `rand`), so runs that agree on them agree on `ppOf`, and leak the
same (`code_constantTime`): the entry, the zeros to `out` and the length
check from the arguments, then `main` (`main_ct`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.ParameterCandidate

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen VG.Impl.RsaKeyGen.AArch64.Candidate VG.Impl.Ffdh.AArch64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MillerRabin.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero)

/-- A state the contract allows, with the public data `p`. -/
def P0 (p : PP) (s : State) : Prop := pcPre s ∧ ppOf s = p

/-- After the entry. -/
def P2 (p : PP) (t : State) : Prop := ∃ s, P0 p s ∧ EntryPost s t

/-- After the zeros to `out`. -/
def P2' (p : PP) (t : State) : Prop := ∃ s t₁, P0 p s ∧ EntryPost s t₁ ∧ Zeroed s t₁ t

/-- After the length check. -/
def P3 (p : PP) (t : State) : Prop := ∃ s, P0 p s ∧ Front s t

/-- The registers `zeroOut`'s loop needs pinned. -/
def zoVal' (ptr : Addr) (len : Nat) : Reg → BitVec 64
  | .x1 => ptr
  | .x2 => BitVec.ofNat 64 len
  | _ => 0

theorem entry_ct : RelCT isa (Two P0) (.block entry) (Two P2) :=
  two_piece [.x7] (fun p s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (congrArg PP.B h₁.2).trans (congrArg PP.B h₂.2).symm)
    (by taint_decide) fun p s h => WP.mono (entry_ok (pctx_of h.1)) fun t he => ⟨s, h, he⟩

theorem zeros_ct : RelCT isa (Two P2) (zeroOut kOut kLen) (Two P2') :=
  pin_ct [.x0] [.x1, .x2] (fun p => zoVal' p.op p.L)
    (fun p s₁ s₂ ⟨σ₁, c₁, h₁⟩ ⟨σ₂, c₂, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [h₁.x0, h₂.x0, show σ₁.gpr .x7 = p.B from congrArg PP.B c₁.2, show σ₂.gpr .x7 = p.B from congrArg PP.B c₂.2])
    (by taint_decide)
    (fun p t ⟨s, c, he⟩ => by
      have k := pctx_of c.1
      have hs := k.hs.congr he.keep.wr
      have hn := hs.nowrap
      have hZ : 128 * (((s.gpr .x3).toNat + 7) / 8) + 256 ≤ (stackArg s 0).toNat * 8 := k.dims.z
      have hL : (s.gpr .x1).toNat = ((s.gpr .x3).toNat + 7) / 8 := k.len
      have hl : ∀ i < 32, InRegions (t.rd ++ t.wr) (off (s.gpr .x7) (8 * i)) 8 := fun i hi => hs.ld (by omega)
      have hop : s.gpr .x0 = p.op := congrArg PP.op c.2
      have hpL : BitVec.ofNat 64 p.L = s.gpr .x1 := by
        rw [← c.2]; show BitVec.ofNat 64 (((s.gpr .x3).toNat + 7) / 8) = _; rw [← hL, ofNat_toNat64]
      refine WP.mono (WP.keep [.x1, .x2, .x3] (Q := fun t' => t'.gpr .x1 = p.op ∧
          t'.gpr .x2 = BitVec.ofNat 64 p.L) (by
        brun [he.x0, hdr_enc (show kOut < 32 by decide), hdr_enc (show kLen < 32 by decide), hl kOut (by decide),
          hl kLen (by decide), he.args.out, he.args.len, hop, hpL]) (by decide) (by decide) (by decide +kernel))
        fun t' ⟨⟨h1, h2⟩, _⟩ r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h1
      · exact h2)
    (by taint_decide) fun p t ⟨s, c, he⟩ => WP.mono (zeros_ok (pctx_of c.1) he) fun t' hz => ⟨s, t, c, he, hz⟩

theorem lenCheck_ct : RelCT isa (Two P2') (.block ([ldh .x3 kRandLen, ldh .x4 kLen] ++ geFlag)) (Two P3) :=
  two_piece [.x0] (fun p s₁ s₂ ⟨σ₁, _, c₁, e₁, z₁⟩ ⟨σ₂, _, c₂, e₂, z₂⟩ r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    rw [(z₁.keep.gpr .x0 (by decide)).trans e₁.x0, (z₂.keep.gpr .x0 (by decide)).trans e₂.x0,
      show σ₁.gpr .x7 = p.B from congrArg PP.B c₁.2, show σ₂.gpr .x7 = p.B from congrArg PP.B c₂.2])
    (by taint_decide) fun p t ⟨s, t₁, c, he, hz⟩ => WP.mono (lenCheck_ok (pctx_of c.1) he hz) fun t' hf => ⟨s, c, hf⟩

theorem P3.x5 {p : PP} {t : State} (h : P3 p t) :
    t.gpr .x5 = BitVec.ofNat 64 (decide (p.L ≤ p.r.length)).toNat := by
  obtain ⟨s, c, hf⟩ := h
  rw [hf.x5, ← c.2]
  have hL := (pctx_of c.1).len
  show _ = BitVec.ofNat 64 (decide ((ppOf s).L ≤ (pcRand s).length)).toNat
  rw [← hL, pcRand_length]

theorem P3.m0 {p : PP} {t : State} (h : P3 p t) (hb : isa.eval (.zero .x .x5) t = some false) : M0 p t := by
  have hx := h.x5
  obtain ⟨s, c, hf⟩ := h
  have k := pctx_of c.1
  rw [eval_zero, hx] at hb
  have hle : p.L ≤ p.r.length := by
    revert hb; cases hd : decide (p.L ≤ p.r.length)
    · intro hb; cases hb
    · intro _; simpa using hd
  have hL : (s.gpr .x1).toNat = (ppOf s).L := k.len
  rw [← c.2] at hle ⊢
  exact ⟨ph_of k hf, by show word t.mem (s.gpr .x7) _ = _; rw [hf.args.used, ← hL, ofNat_toNat64], hle⟩

/-- `vg_ffdh_parameter_candidate` leaks the same in runs with the same
public data. -/
theorem code_ct (M : Mont) (R : Kernel) :
    RelCT isa (Two P0) (VG.Impl.Ffdh.AArch64.ParameterCandidate.code M.mm R.run) fun _ _ => True := by
  unfold VG.Impl.Ffdh.AArch64.ParameterCandidate.code
  simp only [seqs]
  refine RelCT.seq entry_ct (RelCT.seq zeros_ct (RelCT.seq lenCheck_ct ?_))
  refine two_ite (fun p s₁ s₂ h₁ h₂ => by rw [eval_zero, eval_zero, h₁.x5, h₂.x5]) ?_ ?_
  · have e : finNone = .block (([movi .x3 0, ldh .x2 kUsedP] : List Instr) ++ [st .x3 .x2, movi .x0 0]) := rfl
    rw [e]
    refine (RelCT.block_append (pin_ct (Ψ := fun _ _ => True) [.x0] [.x2] (fun p _ => p.up)
      (fun p s₁ s₂ ⟨⟨σ₁, c₁, f₁⟩, _⟩ ⟨⟨σ₂, c₂, f₂⟩, _⟩ r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rw [f₁.x0, f₂.x0]; exact (congrArg PP.B c₁.2).trans (congrArg PP.B c₂.2).symm)
      (by taint_decide) ?_ (by taint_decide) ?_)).mono (fun _ _ h => h) fun _ _ _ => trivial
    · rintro p t ⟨⟨s, c, hf⟩, _⟩
      have k := pctx_of c.1
      have hph := ph_of k hf
      rw [c.2] at hph
      have hs := hph.scr
      have hn := hs.nowrap
      have hZ := hph.dims.z
      have hl : InRegions (t.rd ++ t.wr) (off p.B (8 * kUsedP)) 8 := hs.ld (by simp only [kUsedP, sFn, PP.L] at *; omega)
      refine WP.mono (WP.keep [.x2, .x3] (Q := fun t' => t'.gpr .x2 = p.up) (by
        brun [hph.x0, hdr_enc (show kUsedP < 32 by decide), hl, hph.args.usedP]) (by decide) (by decide)
        (by decide +kernel)) fun t' h2 r hr => ?_
      simp only [List.mem_singleton] at hr; subst hr; exact h2.1
    · rintro p t ⟨⟨s, c, hf⟩, hb⟩
      have k := pctx_of c.1
      have hlt : (pcRand s).length < (s.gpr .x1).toNat := by
        have hx := (show P3 p t from ⟨s, c, hf⟩).x5
        rw [eval_zero, hx] at hb
        have hL := k.len
        rw [← c.2] at hb
        revert hb
        cases hd : decide ((ppOf s).L ≤ (ppOf s).r.length)
        · intro _; simp only [decide_eq_false_iff_not, Nat.not_le] at hd; rw [hL]; exact hd
        · intro hb; cases hb
      have hZ : 128 * (((s.gpr .x3).toNat + 7) / 8) + 256 ≤ (stackArg s 0).toNat * 8 := k.dims.z
      exact WP.seq_iff.mpr (WP.block_append_iff.mp (WP.mono (finNone_ok (up := s.gpr .x2) (k.hs.congr hf.keep.wr)
        hf.x0 (show 8 * 32 ≤ (stackArg s 0).toNat * 8 by omega) hf.args.usedP (k.ou.congr hf.keep.wr).upw)
        fun _ _ => trivial))
  · exact two_map id (fun p t h => h.1.m0 h.2) (main_ct M R)

theorem P0.self {s : State} (h : pcPre s) : P0 (ppOf s) s := ⟨h, rfl⟩

/-- Runs that agree on the public data agree on `ppOf`. -/
theorem ppOf_eq {s₁ s₂ : State} (hp : pcPub s₁ s₂) : ppOf s₂ = ppOf s₁ := by
  obtain ⟨_, hr, h0, h1, h2, h3, h4, h5, h6, h7, ha⟩ := hp
  have hrr : pcRand s₁ = pcRand s₂ := VG.Proof.RsaKeyGen.map_toNat_inj hr
  simp only [ppOf, ← h0, ← h2, ← h3, ← h4, ← h5, ← h7, ← ha, ← hrr]

/-- `vg_ffdh_parameter_candidate` is constant time: its leak depends only
on the public data. -/
theorem code_constantTime (M : Mont) (R : Kernel) :
    ConstantTime isa pcPre pcPub (VG.Impl.Ffdh.AArch64.ParameterCandidate.code M.mm R.run) :=
  RelCT.constantTime ((code_ct M R).mono (fun s₁ _ ⟨h₁, h₂, hp⟩ =>
    ⟨ppOf s₁, P0.self h₁, ⟨h₂, ppOf_eq hp⟩, hp.1⟩) fun _ _ h => h)

/-- `vg_ffdh_parameter_candidate`, against its contract. -/
theorem pc_verified (M : Mont) (R : Kernel) :
    Verified target (VG.Impl.Ffdh.AArch64.ParameterCandidate.code M.mm R.run)
      (Spec.Ffdh.parameterCandidateContract abi) :=
  Verified.of_correct (code_correct M R) (code_constantTime M R) pc_implies

end VG.Proof.Ffdh.AArch64.ParameterCandidate
