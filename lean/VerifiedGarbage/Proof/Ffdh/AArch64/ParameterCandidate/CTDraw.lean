module

public import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.MrDraw
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTMs
meta import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.MrDraw
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTMrRound
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTMrRound
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTFront
import VerifiedGarbage.Proof.RsaKeyGen.Slots
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Round
import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Draw
import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops
import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.Math
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
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.Triangular
import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.MontPrep
import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.ShapeOk
import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Sieve
import VerifiedGarbage.Proof.Ffdh.MillerRabin
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Sieve
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Stream
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
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTFront
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
meta import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Draw
meta import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.MontPrep
meta import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Round
meta import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Shape
meta import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.ShapeOk
meta import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Sieve
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
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.TrialEntry
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.TrialTable
meta import VerifiedGarbage.Proof.RsaKeyGen.Bits
meta import VerifiedGarbage.Proof.RsaKeyGen.CandMath
meta import VerifiedGarbage.Proof.RsaKeyGen.Halve
meta import VerifiedGarbage.Proof.RsaKeyGen.MrMont
meta import VerifiedGarbage.Proof.RsaKeyGen.Primes
meta import VerifiedGarbage.Proof.RsaKeyGen.TrialMath

/-!
# An FFDH parameter candidate on AArch64: constant time of a draw

Every value of the candidate is public, so two runs with the same public
data follow the same path: each piece is checked by the taint analysis from
registers that correctness pins (`round_ct`, `drawHead_ct`, `draw_ct`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.ParameterCandidate

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen VG.Impl.RsaKeyGen.AArch64.Candidate VG.Impl.Ffdh.AArch64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MillerRabin.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero)
open VG.Impl.Bignum.Public (aN aX aAcc aTmp aR2 aXm aY aOne sK sCnt)

/-! ## A round -/

/-- The public data of a round: the working space, `N` and the witness. -/
structure RQ where
  L : WsP
  N : Nat
  a : Nat

/-- Before a round. -/
def RA (q : RQ) (s : State) : Prop :=
  4 ≤ q.L.w ∧ q.L.w ≤ 128 ∧ slot q.L.w aE + 8 * (q.L.w + 2) ≤ q.L.Z ∧ q.N % 2 = 1 ∧ 3 ≤ q.N ∧ q.a < q.N ∧
    (∃ bm, MrCtx s q.L.B q.L.Z q.L.w q.N bm) ∧ ECtx s.mem q.L.B q.L.w q.N ∧
    wv s.mem q.L.B (slot q.L.w aR2) q.L.w = 2 ^ (64 * q.L.w) * 2 ^ (64 * q.L.w) % q.N ∧
    wv s.mem q.L.B (slot q.L.w aX) q.L.w = q.a

/-- Before the kernel. -/
def RB (q : RQ) (s : State) : Prop :=
  4 ≤ q.L.w ∧ q.L.w ≤ 128 ∧ slot q.L.w aE + 8 * (q.L.w + 2) ≤ q.L.Z ∧ q.N % 2 = 1 ∧ 3 ≤ q.N ∧
    (∃ bm, MrCtx s q.L.B q.L.Z q.L.w q.N bm) ∧ ECtx s.mem q.L.B q.L.w q.N ∧
    wv s.mem q.L.B (slot q.L.w aXm) q.L.w = q.a % q.N * 2 ^ (64 * q.L.w) % q.N

/-- After the kernel. -/
def RF (q : RQ) (s : State) : Prop :=
  Ws s q.L.B q.L.Z q.L.w ∧ word s.mem q.L.B (8 * kFlag) = mask (Spec.MillerRabin.round q.N q.a)

theorem roundMm_ok (M : Mont) {q : RQ} {s : State} (h : RA q s) : WP isa (M.mm aXm aX aR2) s (RB q) := by
  obtain ⟨h4, h128, hEZ, hodd, hc3, ha, ⟨bm, hc⟩, he, hR2, hx⟩ := h
  have hn := hc.ws.scr.nowrap
  have hw' : q.L.w < 2 ^ 31 := by omega
  have hRc : Nat.Coprime (2 ^ (64 * q.L.w)) q.N := VG.Proof.Bignum.coprime_pow2 hodd _
  have hc0 : 0 < q.N := by omega
  have hg := hc.good
  refine WP.mono (M.mm_ok hg.1 hg.2 hc.ws.w1 hw' (o := aXm) (a := aX) (b := aR2) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc.inv
    (by rw [hR2, hc.n]; exact Nat.mod_lt _ hc0)) fun t ⟨_, hlt, hy, ha₁, k⟩ => ?_
  rw [hc.n] at hlt hy
  rw [hx, hR2] at hy
  have hXm : wv t.mem q.L.B (slot q.L.w aXm) q.L.w = q.a % q.N * 2 ^ (64 * q.L.w) % q.N := by
    rw [← Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt ha]
    refine VG.Proof.Bignum.mont_cancel hRc ?_
    rw [hy, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Nat.mul_assoc]
  have f₁ : Frm q.L.B [(slot q.L.w aAcc, 8 * (q.L.w + 2)), (slot q.L.w aTmp, 8 * (q.L.w + 2)),
      (slot q.L.w aXm, 8 * (q.L.w + 2))] s.mem t.mem := Frm.of_arrays ha₁ (by simp)
  refine ⟨h4, h128, hEZ, hodd, hc3, ⟨bm, hc.of_frm f₁ (by kmut) k (by decide)
    (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl)
    (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl)
    (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl)⟩,
    he.of_frm f₁ (fun r hr => Or.inr (rdRanges_lt q.L.w r (by
      simp only [rdRanges]; exact List.mem_append_left _ (List.mem_append_left _ hr)))) (by omega), hXm⟩

theorem roundMm_ct (M : Mont) : RelCT isa (Two RA) (M.mm aXm aX aR2) (Two RB) :=
  two_post (two_map (fun q : RQ => q.L) (fun _ _ ⟨_, _, _, _, _, _, ⟨_, hc⟩, _⟩ => ⟨_, hc.good⟩)
    (M.ct (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))))))) fun _ _ h => roundMm_ok M h

theorem roundKernel_ct (R : Kernel) : RelCT isa (Two RB) (seqs R.run) (Two RF) :=
  two_post (two_map (fun q : RQ => q.L)
    (fun q _ ⟨h4, h128, hEZ, hodd, hc3, ⟨bm, hc⟩, he, hx⟩ => ⟨h4, h128, hEZ, q.N, bm, q.a, hc, he, hodd, hc3, hx⟩)
    R.ct) fun _ _ ⟨h4, h128, hEZ, hodd, hc3, ⟨_, hc⟩, he, hx⟩ =>
      WP.mono (R.ok hc he h4 h128 hEZ hodd hc3 hx) fun _ ⟨⟨_, hct⟩, _, hf, _⟩ => ⟨hct.ws, hf⟩

/-- The end of a round. -/
theorem roundEnd_ct : RelCT isa (Two RF) (seqs [.block [ldh .x3 kFlag],
      .ite (.zero .x .x3) (.block [movi .x3 2, sth .x3 kStat])
        (.block [ldh .x3 fIdx, ldh .x4 fChecks, .addImm .x .x3 .x3 1, .subs .x .x5 .x3 .x4, movi .x6 4, movi .x7 1,
          .csel .x .x5 .x7 .x6, sth .x3 fIdx, sth .x5 kStat])]) fun _ _ => True := by
  have pw : ∀ {Φ : RQ → State → Prop}, (∀ q s, Φ q s → Ws s q.L.B q.L.Z q.L.w) → Pins Φ [.x0] :=
    fun h => pins_ws' (fun q : RQ => q.L.B) (fun q : RQ => q.L.Z) (fun q : RQ => q.L.w) h
  refine RelCT.seq (two_piece (Ψ := fun q t => Ws t q.L.B q.L.Z q.L.w ∧
      isa.eval (.zero .x .x3) t = some (!Spec.MillerRabin.round q.N q.a)) [.x0] (pw fun _ _ h => h.1)
      (by taint_decide) fun q s ⟨hw, hF⟩ => ?_) (two_ite (fun _ _ _ h₁ h₂ => by rw [h₁.2, h₂.2])
      (two_taint [.x0] (pw fun _ _ h => h.1.1) (by taint_decide))
      (two_taint [.x0] (pw fun _ _ h => h.1.1) (by taint_decide)))
  have hn := hw.scr.nowrap
  have h256 := hw.h256
  refine WP.mono (WP.keep [.x3] (Q := fun t => t.gpr .x3 = mask (Spec.MillerRabin.round q.N q.a) ∧ t.mem = s.mem)
    (by brun [hw.x0, hdr_enc (show kFlag < 32 by decide),
      hw.scr.ld (d := 8 * kFlag) (by simp only [kFlag, kPlen, sFn]; omega), hF])
    (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨h3, hm⟩, k⟩ => ⟨?_, ?_⟩
  · exact hw.congr' (rs := []) (by rw [hm]; exact Frm.refl _ _ _) (by simp) k (by decide)
  · rw [eval_zero, h3, mask_beq]

/-- A round leaks the same in runs with the same public data. -/
theorem round_ct (M : Mont) (R : Kernel) :
    RelCT isa (Two RA) (seqs (VG.Impl.Ffdh.AArch64.ParameterCandidate.round M.mm R.run)) fun _ _ => True := by
  simp only [VG.Impl.Ffdh.AArch64.ParameterCandidate.round]
  refine ct_app' (by simp) (by simp) ?_ roundEnd_ct
  refine ct_app' (a := [M.mm aXm aX aR2]) (by simp) R.nonempty ?_ (roundKernel_ct R)
  rw [seqs_one]; exact roundMm_ct M

/-! ## A draw -/

/-- The public data of a draw: the candidate's, the modulus's, and the
octets read before it. -/
structure DD where
  p : PP
  w : Nat
  N : Nat
  mb : Nat
  K : Nat
  u : Nat

/-- Before a draw. -/
def DA (d : DD) (s : State) : Prop :=
  MrDims d.p d.w d.N d.mb d.K ∧ MrFix d.p d.w d.N d.mb d.K s ∧
    word s.mem d.p.B (8 * kUsed) = BitVec.ofNat 64 d.u ∧ (∃ i, word s.mem d.p.B (8 * fIdx) = BitVec.ofNat 64 i ∧
    i < 2 ^ 62) ∧ d.u + mLen d.mb ≤ d.p.r.length

/-- The working space of a draw. -/
def DW (d : DD) (s : State) : Prop := Ws s d.p.B d.p.Z d.w

/-- Before the cut. -/
def DC (d : DD) (s : State) : Prop :=
  Ws s d.p.B d.p.Z d.w ∧ mK d.mb ≤ 64 ∧ word s.mem d.p.B (8 * fTop) = BitVec.ofNat 64 (2 ^ mK d.mb - 1)

/-- Before the octets' block. -/
def DL (d : DD) (s : State) : Prop :=
  Ws s d.p.B d.p.Z d.w ∧ word s.mem d.p.B (8 * kRand) = d.p.rp ∧
    word s.mem d.p.B (8 * kUsed) = BitVec.ofNat 64 d.u ∧ word s.mem d.p.B (8 * kLen) = BitVec.ofNat 64 (mLen d.mb)

/-- The registers `loadBE` needs. -/
def dbVal (B rp : Addr) (w u len : Nat) : Reg → BitVec 64
  | .x0 => B
  | .x8 => off B (slot w aX)
  | .x1 => rp + BitVec.ofNat 64 u
  | _ => BitVec.ofNat 64 len

/-- The block before `loadBE`. -/
theorem drawBlk_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {rp : Addr} {u len : Nat}
    (hR : word s.mem B (8 * kRand) = rp) (hU : word s.mem B (8 * kUsed) = BitVec.ofNat 64 u)
    (hK : word s.mem B (8 * kLen) = BitVec.ofNat 64 len) :
    WP isa (.block (ws ++ base aX .x8 ++ [ldh .x1 kRand, ldh .x3 kUsed, .add .x .x1 .x1 .x3,
      ldh .x2 kLen, .add .x .x3 .x3 .x2, sth .x3 kUsed])) s fun t =>
      ∀ r ∈ [Reg.x0, .x8, .x1, .x2], t.gpr r = dbVal B rp w u len r := by
  refine WP.block_append_iff.mpr (WP.block_append_iff.mpr (WP.mono h.ws_ok fun s₂ ⟨⟨_, h11, m₂, _⟩, k₂⟩ =>
    WP.mono (base_ok aX .x8 ((k₂.gpr .x0 (by decide)).trans h.x0) h11) fun s₃ ⟨⟨h8, m₃, _⟩, k₃⟩ =>
      WP.mono (WP.keep [.x1, .x3, .x2] (Q := fun t => t.gpr .x1 = rp + BitVec.ofNat 64 u ∧
        t.gpr .x2 = BitVec.ofNat 64 len) (by
          have h0₃ : s₃.gpr .x0 = B := ((k₂.trans k₃).gpr .x0 (by decide)).trans h.x0
          have hs₃ := h.scr.congr (k₂.trans k₃).wr
          have hl₃ : ∀ i < 32, InRegions (s₃.rd ++ s₃.wr) (off B (8 * i)) 8 := fun i hi =>
            hs₃.ld (by have := h.h256; omega)
          brun [h0₃, hdr_enc (show kRand < 32 by decide), hdr_enc (show kUsed < 32 by decide),
            hdr_enc (show kLen < 32 by decide), m₃, m₂, hl₃ kRand (by decide), hl₃ kUsed (by decide),
            hl₃ kLen (by decide), hs₃.st (d := 8 * kUsed) (by have := h.h256; simp only [kUsed, sFn]; omega),
            hR, hU, hK])
        (by decide) (by decide) (by decide +kernel))
      fun t ⟨⟨h1, h2⟩, k₄⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact (((k₂.trans k₃).trans k₄).gpr .x0 (by decide)).trans h.x0
        · exact (k₄.gpr .x8 (by decide)).trans h8
        · exact h1
        · exact h2))

theorem zeroAD_ct : RelCT isa (Two DL) (zeroA aX) (Two DL) := by
  have e : zeroA aX = .seq (.block (ws ++ (base aX .x8 ++ [movi .x7 0]))) zeroAcc := by
    simp only [zeroA, List.append_assoc]
  rw [e]
  refine ws_ct (fun d : DD => d.p.B) (fun d : DD => d.p.Z) (fun d : DD => d.w) (fun _ _ h => h.1)
    (by taint_decide) fun d s h => ?_
  rw [← e]
  obtain ⟨hw, hR, hU, hK⟩ := h
  have hn := hw.scr.nowrap
  refine WP.mono (zeroA_ok hw (show aX < 16 by decide)) fun t ⟨_, o, _, _, _, k⟩ => ?_
  have f : Frm d.p.B [(slot d.w aX, 8 * (d.w + 2))] s.mem t.mem := Frm.of_outside o (List.mem_singleton_self _)
  have hh : ∀ i < 32, word t.mem d.p.B (8 * i) = word s.mem d.p.B (8 * i) := fun i hi =>
    f.word_eq (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Or.inl (hdr_lt_slot d.w aX hi)) (by omega)
  exact ⟨hw.congr' f (by msb_mut) k (by decide), (hh _ (by decide)).trans hR, (hh _ (by decide)).trans hU,
    (hh _ (by decide)).trans hK⟩

/-- The octets into `aX`. -/
theorem drawLoad_ct : RelCT isa (Two DL) (seqs [zeroA aX, .block (ws ++ base aX .x8 ++ [ldh .x1 kRand,
    ldh .x3 kUsed, .add .x .x1 .x1 .x3, ldh .x2 kLen, .add .x .x3 .x3 .x2, sth .x3 kUsed]), loadBE])
    fun _ _ => True :=
  RelCT.seq zeroAD_ct (RelCT.seq (two_piece (Ψ := fun d t => ∀ r ∈ [Reg.x0, .x8, .x1, .x2],
      t.gpr r = dbVal d.p.B d.p.rp d.w d.u (mLen d.mb) r) [.x0]
      (pins_ws' (fun d : DD => d.p.B) (fun d : DD => d.p.Z) (fun d : DD => d.w) fun _ _ h => h.1)
      (by taint_decide)
      fun _ _ ⟨hw, hR, hU, hK⟩ => drawBlk_ok hw hR hU hK)
    (two_taint _ (pins_of _ (fun d => dbVal d.p.B d.p.rp d.w d.u (mLen d.mb)) fun _ _ h => h) (by taint_decide)))

/-- The range's pieces, from the working space. -/
theorem drawRange_ct : RelCT isa (Two DW)
    (seqs [.block (ws ++ base aX .x16 ++ [ld .x5 .x16, .lsr .x .x5 .x5 1, next .x16, .subImm .x .x14 .x12 1]),
      countLoop .x14 [ld .x3 .x16, .logic .orr .x .x5 .x5 .x3, next .x16],
      .block ([movi .x7 0, .subImm .x .x8 .x7 1, movi .x4 1, .subs .x .x3 .x5 .x4, .csel .x .x9 .x8 .x7] ++ ws ++
        base aX .x16 ++ base aN .x17 ++ [ld .x3 .x16, .logic .orr .x .x3 .x3 .x4, ld .x4 .x17, .subs .x .x3 .x3 .x4,
        next .x16, next .x17, .subImm .x .x14 .x12 1]),
      cmpLoop,
      .block [.csel .x .x15 .x7 .x8, .logic .and .x .x9 .x9 .x15]]) fun _ _ => True := by
  refine two_map (Φ' := fun (q : WPub) t => Ws t q.L.B q.L.Z q.L.w)
    (fun d : DD => (⟨⟨d.p.B, d.p.Z, d.w⟩, d.p.rp, d.u⟩ : WPub)) (fun _ _ h => h) ?_
  have e : ([.block (ws ++ base aX .x16 ++ [ld .x5 .x16, .lsr .x .x5 .x5 1, next .x16, .subImm .x .x14 .x12 1]),
      countLoop .x14 [ld .x3 .x16, .logic .orr .x .x5 .x5 .x3, next .x16],
      .block ([movi .x7 0, .subImm .x .x8 .x7 1, movi .x4 1, .subs .x .x3 .x5 .x4, .csel .x .x9 .x8 .x7] ++ ws ++
        base aX .x16 ++ base aN .x17 ++ [ld .x3 .x16, .logic .orr .x .x3 .x3 .x4, ld .x4 .x17, .subs .x .x3 .x3 .x4,
        next .x16, next .x17, .subImm .x .x14 .x12 1]),
      cmpLoop,
      .block [.csel .x .x15 .x7 .x8, .logic .and .x .x9 .x9 .x15]] : List (Prog isa)) =
      [.block (ws ++ base aX .x16 ++ [ld .x5 .x16, .lsr .x .x5 .x5 1, next .x16, .subImm .x .x14 .x12 1]),
        countLoop .x14 [ld .x3 .x16, .logic .orr .x .x5 .x5 .x3, next .x16]] ++
      ([.block ([movi .x7 0, .subImm .x .x8 .x7 1, movi .x4 1, .subs .x .x3 .x5 .x4, .csel .x .x9 .x8 .x7] ++ ws ++
        base aX .x16 ++ base aN .x17 ++ [ld .x3 .x16, .logic .orr .x .x3 .x3 .x4, ld .x4 .x17, .subs .x .x3 .x3 .x4,
        next .x16, next .x17, .subImm .x .x14 .x12 1]), cmpLoop] ++
      [.block [.csel .x .x15 .x7 .x8, .logic .and .x .x9 .x9 .x15]]) := rfl
  rw [e]
  exact ct_app' (by simp) (by simp) witLow_ct (ct_app' (by simp) (by simp) witCmp_ct
    (two_taint _ (pins_of _ (fun p : WPub => wsVal p.L.B p.L.w) fun _ _ h => h) (by taint_decide)))

theorem drawHead_eq : drawHead = ([zeroA aX, .block (ws ++ base aX .x8 ++ [ldh .x1 kRand,
    ldh .x3 kUsed, .add .x .x1 .x1 .x3, ldh .x2 kLen, .add .x .x3 .x3 .x2, sth .x3 kUsed]), loadBE] : List (Prog isa)) ++
    (([.block (ws ++ base aX .x16 ++ ([.lsl .x .x5 .x12 3, .add .x .x5 .x16 .x5, .subImm .x .x5 .x5 8, ldh .x4 fTop,
      ld .x3 .x5, .logic .and .x .x3 .x3 .x4, st .x3 .x5] : List Instr))] : List (Prog isa)) ++
    ([.block (ws ++ base aX .x16 ++ [ld .x5 .x16, .lsr .x .x5 .x5 1, next .x16, .subImm .x .x14 .x12 1]),
      countLoop .x14 [ld .x3 .x16, .logic .orr .x .x5 .x5 .x3, next .x16],
      .block ([movi .x7 0, .subImm .x .x8 .x7 1, movi .x4 1, .subs .x .x3 .x5 .x4, .csel .x .x9 .x8 .x7] ++ ws ++
        base aX .x16 ++ base aN .x17 ++ [ld .x3 .x16, .logic .orr .x .x3 .x3 .x4, ld .x4 .x17, .subs .x .x3 .x3 .x4,
        next .x16, next .x17, .subImm .x .x14 .x12 1]),
      cmpLoop,
      .block [.csel .x .x15 .x7 .x8, .logic .and .x .x9 .x9 .x15]] : List (Prog isa))) := rfl

/-- After `drawHead`. -/
def DM (d : DD) (s : State) : Prop :=
  MrDims d.p d.w d.N d.mb d.K ∧ ∃ i s₀, DrawMid d.p d.w d.N d.mb d.K i d.u s₀ s ∧ i < 2 ^ 62

/-- `drawHead` leaks the same in runs with the same public data. -/
theorem drawHead_ct : RelCT isa (Two DA) (seqs drawHead) (Two DM) := by
  refine two_post ?_ fun d s ⟨hd, h, hU, ⟨i, hI, hi⟩, hroom⟩ =>
    WP.mono (drawHead_ok hd h hU hI hroom) fun t ht => ⟨hd, i, s, ht, hi⟩
  rw [drawHead_eq]
  refine ct_app' (by simp) (by simp) (Ψ := DC) (two_post (two_map (Φ' := DL) id (fun d s ⟨_, h, hU, _⟩ =>
    ⟨h.st.ws, h.st.args.rand, hU, h.len⟩) drawLoad_ct) fun d s ⟨hd, h, hU, _, hroom⟩ => ?_) ?_
  · have hmb1 := hd.mb1
    have hw := hd.hw
    have hn := h.st.ws.scr.nowrap
    exact WP.mono (drawLoad_ok h.st.ws h.st.args.rand hU h.len (by simp only [mLen]; omega)
      (by rw [hw]; simp only [mLen, mW]; omega) (src_take (src_drop h.st.src d.u) (mLen d.mb))
      (by simp only [List.length_take, List.length_drop]; omega)) fun t ⟨_, _, f, hw', _⟩ =>
        ⟨hw', by simp only [mK, mW]; omega, by
          rw [f.word_eq (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl) (by simp only [fTop]; omega)]; exact h.top⟩
  refine ct_app' (by simp) (by simp) (Ψ := DW) ?_ drawRange_ct
  rw [seqs_one]
  exact ws_block_ct (fun d : DD => d.p.B) (fun d : DD => d.p.Z) (fun d : DD => d.w) (fun _ _ h => h.1)
    (by taint_decide) fun d s ⟨hw, hk, hT⟩ => WP.mono (drawCut_ok hw hk hT) fun t ⟨_, f, k⟩ =>
      hw.congr' f (fun r hr => by rw [List.mem_singleton.mp hr]; exact KMut.ofSlot _ _ _) k (by decide)

theorem mask_decide_beq (P : Prop) [Decidable P] : (mask (decide P) == 0) = !decide P := by
  cases decide P <;> decide

/-- A draw leaks the same in runs with the same public data. -/
theorem draw_ct (M : Mont) (R : Kernel) :
    RelCT isa (Two DA) (seqs (draw M.mm R.run)) fun _ _ => True := by
  rw [draw_eq]
  refine ct_app' (by simp [drawHead, draw]) (by simp) drawHead_ct ?_
  rw [seqs_one]
  have hz : ∀ d s, DM d s → isa.eval (.zero .x .x9) s =
      some (!decide (2 ≤ wA d.mb d.p.r d.u ∧ wA d.mb d.p.r d.u < d.N - 1)) := fun d s ⟨_, i, s₀, h, _⟩ => by
    rw [eval_zero, h.x9, mask_decide_beq]
  refine two_ite (fun d s₁ s₂ h₁ h₂ => by rw [hz d s₁ h₁, hz d s₂ h₂]) ?_ ?_
  · exact two_taint [.x0] (pins_ws' (fun d : DD => d.p.B) (fun d : DD => d.p.Z) (fun d : DD => d.w)
      fun _ _ ⟨⟨_, _, _, h, _⟩, _⟩ => h.fix.st.ws) (by taint_decide)
  · refine two_map (Φ' := RA) (fun d : DD => (⟨⟨d.p.B, d.p.Z, d.w⟩, d.N, wA d.mb d.p.r d.u⟩ : RQ)) ?_ (round_ct M R)
    rintro d s ⟨hm, hb⟩
    have hz' := hz d s hm
    obtain ⟨hd, i, s₀, h, _⟩ := hm
    rw [hz'] at hb
    have hacc : 2 ≤ wA d.mb d.p.r d.u ∧ wA d.mb d.p.r d.u < d.N - 1 := by
      simpa using hb
    have hw := hd.hw
    have hmb1 := hd.mb1
    have hmb2 := hd.mb2
    exact ⟨by rw [hw]; simp only [mW]; omega, by rw [hw]; simp only [mW]; omega, hd.eZ, hd.odd, hd.n3,
      show wA d.mb d.p.r d.u < d.N by omega, h.fix.ctx, h.fix.ex, h.fix.r2, h.ax⟩

end VG.Proof.Ffdh.AArch64.ParameterCandidate
