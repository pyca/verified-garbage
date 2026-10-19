module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.WitnessRange
public import Mathlib.Data.Int.ModEq
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Rsa.AArch64.KeyWs
public import VerifiedGarbage.Proof.RsaKeyGen.Table
public import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Draw
import VerifiedGarbage.Proof.Framework.Omega
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
import VerifiedGarbage.Proof.Bignum.AArch64.PdExp
import VerifiedGarbage.Proof.Bignum.AArch64.PdLoad
import VerifiedGarbage.Proof.Bignum.AArch64.PdRest
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
import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.MontPrep
import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.ShapeOk
import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Sieve
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Sieve
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
import VerifiedGarbage.Proof.Poly1305.Limbs64
import VerifiedGarbage.Proof.Rsa.AArch64.CvFail
import VerifiedGarbage.Proof.Rsa.AArch64.CvLoad
import VerifiedGarbage.Proof.Rsa.AArch64.Inv
import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Close
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Entry
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Fin
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.GcdStep
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.LoadC
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MontSetup
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrBit
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrExp
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrMain
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrSelW
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrTail
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.TrialEntry
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.TrialTable
import VerifiedGarbage.Proof.RsaKeyGen.Bits
import VerifiedGarbage.Proof.RsaKeyGen.CandMath
import VerifiedGarbage.Proof.RsaKeyGen.MrMont
import VerifiedGarbage.Proof.RsaKeyGen.Primes
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcAdd
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCancelTile
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcColumns
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCorrect
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtLoop
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtRow
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtSquare
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcEnd
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcExtend
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcFastCancel
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcFastMath
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcFastWord
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcFinish
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLayout
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoop
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcRestore
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcRow
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcSave
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcSquare
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcStore
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcTile
public import VerifiedGarbage.Proof.Bignum.AArch64.Bytes
public import VerifiedGarbage.Proof.Bignum.AArch64.CarrySelect
public import VerifiedGarbage.Proof.Bignum.AArch64.Copy
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtArith
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtGPow
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtSel
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtTab
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtUnit
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWs
public import VerifiedGarbage.Proof.Bignum.AArch64.DiagonalChain
public import VerifiedGarbage.Proof.Bignum.AArch64.DiagonalChainCore
public import VerifiedGarbage.Proof.Bignum.AArch64.DiagonalChainStep
public import VerifiedGarbage.Proof.Bignum.AArch64.DiagonalChainTile
public import VerifiedGarbage.Proof.Bignum.AArch64.Double
public import VerifiedGarbage.Proof.Bignum.AArch64.FastFinish
public import VerifiedGarbage.Proof.Bignum.AArch64.FastFinishCT
public import VerifiedGarbage.Proof.Bignum.AArch64.FastFinishSel
public import VerifiedGarbage.Proof.Bignum.AArch64.FastFinishSelTile
public import VerifiedGarbage.Proof.Bignum.AArch64.FastFinishSub
public import VerifiedGarbage.Proof.Bignum.AArch64.FastFinishSubTile
public import VerifiedGarbage.Proof.Bignum.AArch64.Mont
public import VerifiedGarbage.Proof.Bignum.AArch64.PcCT
public import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
public import VerifiedGarbage.Proof.Bignum.AArch64.PcVerified
public import VerifiedGarbage.Proof.Bignum.AArch64.PdExp
public import VerifiedGarbage.Proof.Bignum.AArch64.PdLoad
public import VerifiedGarbage.Proof.Bignum.AArch64.PdRest
public import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCT
public import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCorrect
public import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCtRows
public import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightMath
public import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightRaw
public import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightRowMath
public import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightSetup
public import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
public import VerifiedGarbage.Proof.Bignum.AArch64.PubR2
public import VerifiedGarbage.Proof.Bignum.AArch64.PubValid
public import VerifiedGarbage.Proof.Bignum.AArch64.R2dQuot
public import VerifiedGarbage.Proof.Bignum.AArch64.R2dRecip
public import VerifiedGarbage.Proof.Bignum.AArch64.R2dSub
public import VerifiedGarbage.Proof.Bignum.AArch64.Reduce
public import VerifiedGarbage.Proof.Bignum.AArch64.Setup
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareCT
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareCall
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareCallCT
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareCallMont
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareCorrect
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareCount
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareCross
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareCrossRow
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareDiagonal
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareDiagonalCore
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightBound
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightCT
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightCarry
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightCarryWord
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightColumn
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightCorrect
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightCtRows
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightCtSetup
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightDiagonal
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightGuard
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightGuardCT
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightHead
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightInternal
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightMath
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightMont
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightPolynomial
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightRaw
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightRowMath
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightRows
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightSetup
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightTail
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareFinish
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareGuard
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareLayout
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareMac
public import VerifiedGarbage.Proof.Bignum.AArch64.SquarePrefix
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareRaw
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareRedc
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareRedcLoop
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareRedcRow
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareRedcStep
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareRow
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareTiledRow
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareZero
public import VerifiedGarbage.Proof.Bignum.AArch64.Store
public import VerifiedGarbage.Proof.Bignum.AArch64.WideDiagonal
public import VerifiedGarbage.Proof.Bignum.AArch64.WideZero
public import VerifiedGarbage.Proof.Bignum.CrtMath
public import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Bignum.Triangular
public import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.MontPrep
public import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Shape
public import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.ShapeOk
public import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Sieve
public import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
public import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Sieve
public import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
public import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Proof.Framework.AArch64.RelCT
public import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Bswap
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Range
public import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Framework.TaintBatch
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Proof.Poly1305.Limbs64
public import VerifiedGarbage.Proof.Rsa.AArch64.CvFail
public import VerifiedGarbage.Proof.Rsa.AArch64.CvLoad
public import VerifiedGarbage.Proof.Rsa.AArch64.Inv
public import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Close
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Entry
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Fin
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.GcdStep
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.LoadC
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MontSetup
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrBit
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrExp
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrMain
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrSelW
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrTail
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.TrialEntry
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.TrialTable
public import VerifiedGarbage.Proof.RsaKeyGen.Bits
public import VerifiedGarbage.Proof.RsaKeyGen.CandMath
public import VerifiedGarbage.Proof.RsaKeyGen.MrMont
public import VerifiedGarbage.Proof.RsaKeyGen.Primes

/-! The uniform flag agrees with the shared RSA sampler, without changing the draw. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.Ffdh.AArch64.ParameterCandidate VG.Proof.MlKem.AArch64

theorem testRange_ok {s : State} {B : Addr} {Z w X N : Nat}
    (h : Ws s B Z w) (hx : wv s.mem B (slot w aX) w = X)
    (hn : wv s.mem B (slot w aN) w = N) (hodd : N % 2 = 1) :
    WP isa Impl.Dsa.AArch64.Generation.testRange s fun t =>
      t.gpr .x9 = mask (decide (2 ≤ X ∧ X < N - 1)) ∧
      t.mem = s.mem.writeW (off B (8 * kU)) (mask (decide (2 ≤ X ∧ X < N - 1))) ∧
      Keep mmRegs s t := by
  unfold Impl.Dsa.AArch64.Generation.testRange
  refine WP.seq (WP.mono (drawRange_ok h hx) fun u ⟨hu9, hum, ku⟩ => ?_)
  have hu9' : u.gpr .x9 = mask (decide (2 ≤ X ∧ X < N - 1)) := by
    simpa only [hn, or1_lt_iff hodd, Bool.decide_and] using hu9
  refine WP.mono (WP.keep [] (Q := fun t =>
      t.mem = u.mem.writeW (off B (8 * kU)) (mask (decide (2 ≤ X ∧ X < N - 1))))
      (by
        brun [(ku.gpr .x0 (by decide)).trans h.x0, hu9', hdr_enc (show kU < 32 by decide),
          (h.scr.congr ku.wr).st (d := 8 * kU) (by have := h.h256; simp only [kU]; omega)])
      rfl rfl rfl) fun t ⟨htm, kt⟩ => ?_
  exact ⟨(kt.gpr .x9 (by decide)).trans hu9', by rw [htm, hum], (ku.trans kt).mono (by decide)⟩

end VG.Proof.Dsa.AArch64.Generation
