module

meta import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.MontPrep
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTMs
public import VerifiedGarbage.Impl.Ffdh.AArch64.ParameterCandidate
public import VerifiedGarbage.Proof.RsaKeyGen.Table
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTMs
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrShift
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrShift
meta import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.RsaKeyGen.Slots
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Rsa.AArch64.CTBase
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MontSetup
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Close
import VerifiedGarbage.Proof.Bignum.AArch64.PubR2
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
import VerifiedGarbage.Proof.Bignum.AArch64.CrtRedc
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
import VerifiedGarbage.Proof.Bignum.Triangular
import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.MontPrep
import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.ShapeOk
import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Sieve
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Sieve
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
import VerifiedGarbage.Proof.Poly1305.Limbs64
import VerifiedGarbage.Proof.Rsa.AArch64.CvFail
import VerifiedGarbage.Proof.Rsa.AArch64.CvLoad
import VerifiedGarbage.Proof.Rsa.AArch64.Inv
import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Entry
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Fin
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.GcdStep
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.LoadC
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrBit
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.TrialEntry
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.TrialTable
import VerifiedGarbage.Proof.RsaKeyGen.Bits
import VerifiedGarbage.Proof.RsaKeyGen.CandMath
import VerifiedGarbage.Proof.RsaKeyGen.Halve
import VerifiedGarbage.Proof.RsaKeyGen.MrMont
import VerifiedGarbage.Proof.RsaKeyGen.Primes
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
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtRedc
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
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Bignum.Triangular
meta import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Shape
meta import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.ShapeOk
meta import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Sieve
meta import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
meta import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Sieve
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
meta import VerifiedGarbage.Proof.Poly1305.Limbs64
meta import VerifiedGarbage.Proof.Rsa.AArch64.CTBase
meta import VerifiedGarbage.Proof.Rsa.AArch64.CvFail
meta import VerifiedGarbage.Proof.Rsa.AArch64.CvLoad
meta import VerifiedGarbage.Proof.Rsa.AArch64.Inv
meta import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Close
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Entry
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Fin
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.GcdStep
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.LoadC
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MontSetup
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrBit
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.TrialEntry
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.TrialTable
meta import VerifiedGarbage.Proof.RsaKeyGen.Bits
meta import VerifiedGarbage.Proof.RsaKeyGen.CandMath
meta import VerifiedGarbage.Proof.RsaKeyGen.Halve
meta import VerifiedGarbage.Proof.RsaKeyGen.MrMont
meta import VerifiedGarbage.Proof.RsaKeyGen.Primes

/-!
# An FFDH parameter candidate on AArch64: constant time of the Montgomery setup

`montPrep_ct` and `expSetup_ct'`, for runs that agree on the working space
and the modulus `N` (public here): RSA's pieces (`CTMs.lean`) for a modulus
of `w` words whose top word is not zero, `R² mod N` by `r2_ct`, and
`expSetup` from the registers `lowWord` leaves.
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.ParameterCandidate

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen VG.Impl.RsaKeyGen.AArch64.Candidate VG.Impl.Ffdh.AArch64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Bignum.Public (aN aX aAcc aTmp aR2 aXm aY aOne sK sCnt)

/-- The public data of the setup: the working space and the modulus. -/
structure MQ where
  L : WsP
  N : Nat

/-- Before `montPrep`. -/
def MP0 (q : MQ) (s : State) : Prop :=
  Ws s q.L.B q.L.Z q.L.w ∧ 4 ≤ q.L.w ∧ q.L.w ≤ 128 ∧ wv s.mem q.L.B (slot q.L.w aN) q.L.w = q.N ∧
    q.N % 2 = 1 ∧ 2 ^ (64 * (q.L.w - 1)) ≤ q.N

/-- With `-N⁻¹`. -/
def MPc (q : MQ) (s : State) : Prop :=
  MP0 q s ∧ ((word s.mem q.L.B (slot q.L.w aN)).toNat * (word s.mem q.L.B (8 * sMinv)).toNat + 1) % 2 ^ 64 = 0

/-- After `-N⁻¹`'s block. -/
def MPa (q : MQ) (s : State) : Prop :=
  MPc q s ∧ s.gpr .x12 = BitVec.ofNat 64 q.L.w ∧ s.gpr .x9 = 1 ∧ s.gpr .x13 = BitVec.ofNat 64 0

/-- With the number 1. -/
def MPb (q : MQ) (s : State) : Prop := MPc q s ∧ wv s.mem q.L.B (slot q.L.w aOne) q.L.w = 1

theorem MPc.frm {q : MQ} {s t : State} (h : MPc q s) {rs : List (Nat × Nat)} (hf : Frm q.L.B rs s.mem t.mem)
    (hm : ∀ r ∈ rs, KMut r) {regs : List Reg} (k : Keep regs s t) (hr : .x0 ∉ regs)
    (dN : ∀ r ∈ rs, slot q.L.w aN + 8 * q.L.w ≤ r.1 ∨ r.1 + r.2 ≤ slot q.L.w aN)
    (dI : ∀ r ∈ rs, 8 * sMinv + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * sMinv) : MPc q t := by
  obtain ⟨⟨hw, h4, h128, hn, hodd, hlo⟩, hinv⟩ := h
  have hnw := hw.scr.nowrap
  have hZ := hw.hZ
  have hw1 := hw.w1
  have eN := hw.sl (show aN < 16 by decide)
  refine ⟨⟨hw.congr' hf hm k hr, h4, h128, by rw [hf.wv_eq dN (by omega)]; exact hn, hodd, hlo⟩, ?_⟩
  rw [hf.word_eq (d := slot q.L.w aN) (fun r hr => by have := dN r hr; omega) (by omega),
    hf.word_eq (d := 8 * sMinv) dI (by simp only [sMinv] at *; have := hw.h256; omega)]
  exact hinv

theorem MPb.frm {q : MQ} {s t : State} (h : MPb q s) {rs : List (Nat × Nat)} (hf : Frm q.L.B rs s.mem t.mem)
    (hm : ∀ r ∈ rs, KMut r) {regs : List Reg} (k : Keep regs s t) (hr : .x0 ∉ regs)
    (dN : ∀ r ∈ rs, slot q.L.w aN + 8 * q.L.w ≤ r.1 ∨ r.1 + r.2 ≤ slot q.L.w aN)
    (dI : ∀ r ∈ rs, 8 * sMinv + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * sMinv)
    (dO : ∀ r ∈ rs, slot q.L.w aOne + 8 * q.L.w ≤ r.1 ∨ r.1 + r.2 ≤ slot q.L.w aOne) : MPb q t := by
  have hnw := h.1.1.1.scr.nowrap
  have hZ := h.1.1.1.hZ
  have eO := h.1.1.1.sl (show aOne < 16 by decide)
  exact ⟨h.1.frm hf hm k hr dN dI, by rw [hf.wv_eq dO (by omega)]; exact h.2⟩

theorem mpH_ok {q : MQ} {s : State} (h : MP0 q s) :
    WP isa (.block ([ldh .x8 (sArr aN), ld .x3 .x8] ++ minv ++ [sth .x15 sMinv, ldh .x12 sW, movi .x9 1,
      movi .x13 0])) s (MPa q) := by
  obtain ⟨hw, h4, h128, hn, hodd, hlo⟩ := h
  have hnw := hw.scr.nowrap
  have hw1 := hw.w1
  have hodd0 : (word s.mem q.L.B (slot q.L.w aN)).toNat % 2 = 1 := by
    have e := wv_add s.mem q.L.B (slot q.L.w aN) 1 (q.L.w - 1)
    rw [show 1 + (q.L.w - 1) = q.L.w by omega, hn] at e
    simp only [wv, Nat.mul_zero, Nat.add_zero, Nat.zero_add] at e
    omega
  refine WP.mono (msHead_ok hw hodd0) fun t ⟨⟨hinv, hm, h12, h9, h13⟩, k⟩ => ?_
  have o₁ : Outside q.L.B (8 * sMinv) 8 s.mem t.mem := by
    rw [hm]; exact writeW_outside _ _ _ (by simp only [sMinv]; omega)
  have f₁ : Frm q.L.B [(8 * sMinv, 8)] s.mem t.mem := Frm.of_outside o₁ (List.mem_singleton_self _)
  have hw₁ : word t.mem q.L.B (slot q.L.w aN) = word s.mem q.L.B (slot q.L.w aN) :=
    o₁.word (by simp only [slot, hdrBytes, aN, sMinv]; omega) (by simp only [slot, hdrBytes, aN]; omega)
  refine ⟨⟨⟨hw.congr' f₁ (by msb_mut) k (by decide), h4, h128, ?_, hodd, hlo⟩, by rw [hw₁]; exact hinv⟩, h12, h9,
    h13⟩
  rw [o₁.wv (by simp only [slot, hdrBytes, aN, sMinv]; omega) (by simp only [slot, hdrBytes, aN]; omega)]; exact hn

theorem mpOne_ok {q : MQ} {s : State} (h : MPa q s) : WP isa (setWord aOne) s (MPb q) := by
  obtain ⟨hc, h12, h9, h13⟩ := h
  have hw := hc.1.1
  have hnw := hw.scr.nowrap
  have hZ := hw.hZ
  have hw1 := hw.w1
  have hw2 := hw.w2
  obtain ⟨g, hZ8⟩ := hw.good
  refine WP.mono (setWord_ok g.scr g.x0 g.hdr hZ8 h12 (by omega) (o := aOne) (by decide) (i := 0)
    (by omega) h13) fun t ⟨hv, o, k⟩ => ?_
  rw [h9] at hv
  have f : Frm q.L.B [(slot q.L.w aOne, 8 * (q.L.w + 2))] s.mem t.mem := Frm.of_outside o (List.mem_singleton_self _)
  exact ⟨hc.frm f (by msb_mut) k (by decide) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl)
    (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl), hv⟩

/-- `r2_ok`'s hypotheses, for the run's `-N⁻¹`. -/
theorem mpb_r2pre {q : MQ} {s : State} (h : MPb q s) :
    R2Pre ⟨⟨q.L.B, q.L.Z, q.L.w, word s.mem q.L.B (8 * sMinv)⟩, q.N⟩ s := by
  obtain ⟨⟨⟨hw, h4, h128, hn, hodd, hlo⟩, hinv⟩, -⟩ := h
  exact ⟨hw.good, show 2 ≤ q.L.w by omega, show q.L.w < 2 ^ 30 by omega, hn, hinv, hodd, hlo⟩

theorem mpR2_ok (M : Mont) {q : MQ} {s : State} (h : MPb q s) : WP isa (seqs (r2Steps M.mm)) s (MPb q) := by
  obtain ⟨hg, hw2, hw', hn, hinv, hodd, hlo⟩ := mpb_r2pre h
  have hZ := h.1.1.1.hZ
  refine WP.mono (r2_ok M hg.1 hg.2 hw2 hw' hn hinv hodd hlo) fun t ⟨_, _, _, fr, k⟩ =>
    h.frm fr (by msb_mut) k (by decide) (by msb_disj) (by msb_disj) (by msb_disj)

theorem mpY_ok (M : Mont) {q : MQ} {s : State} (h : MPb q s) : WP isa (M.mm aY aR2 aOne) s (MPb q) := by
  obtain ⟨⟨⟨hw, h4, h128, hn, hodd, hlo⟩, hinv⟩, hone⟩ := h
  obtain ⟨g, hZ8⟩ := hw.good
  have hN1 : 1 < q.N := by
    have : 2 ≤ 2 ^ (64 * (q.L.w - 1)) := by
      rw [show 64 * (q.L.w - 1) = (64 * (q.L.w - 1) - 1) + 1 by omega, Nat.pow_succ]
      have := Nat.two_pow_pos (64 * (q.L.w - 1) - 1); omega
    omega
  refine WP.mono (M.mm_ok g hZ8 hw.w1 (by have := hw.w2; omega) (o := aY) (a := aR2) (b := aOne) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hinv (by rw [hone, hn]; exact hN1))
    fun t ⟨_, _, _, ha, k⟩ => ?_
  exact MPb.frm (s := s) ⟨⟨⟨hw, h4, h128, hn, hodd, hlo⟩, hinv⟩, hone⟩ (Frm.of_arrays ha (rs := [(slot q.L.w aAcc,
    8 * (q.L.w + 2)), (slot q.L.w aTmp, 8 * (q.L.w + 2)), (slot q.L.w aY, 8 * (q.L.w + 2))]) (by simp)) (by msb_mut) k
    (by decide) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl) (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl)
    (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl)

theorem mpR1_ok {q : MQ} {s : State} (h : MPb q s) : WP isa (copyA aR1 aY) s (MPb q) := by
  have hw := h.1.1.1
  have hnw := hw.scr.nowrap
  have hZ := hw.hZ
  refine WP.mono (copyA_ok hw (o := aR1) (a := aY) (by decide) (by decide) (by decide)) fun t ⟨_, o, _, _, k⟩ =>
    h.frm (Frm.of_outside o (List.mem_singleton_self _)) (by msb_mut) k (by decide) (by msb_disj) (by msb_disj)
      (by msb_disj)

theorem mpRm_ok {q : MQ} {s : State} (h : MPb q s) :
    WP isa (seqs (subA aRm1 aN aR1)) s fun t => Ws t q.L.B q.L.Z q.L.w := by
  have hw := h.1.1.1
  exact WP.mono (subA_ok hw (o := aRm1) (a := aN) (b := aR1) (by decide) (by decide) (by decide) (.inr (by decide))
    (by decide)) fun t ⟨_, o, _, _, _, k⟩ =>
    hw.congr' (Frm.of_outside o (List.mem_singleton_self _)) (by msb_mut) k (by decide)

theorem mpH_ct : RelCT isa (Two MP0) (.block ([ldh .x8 (sArr aN), ld .x3 .x8] ++ minv ++
    [sth .x15 sMinv, ldh .x12 sW, movi .x9 1, movi .x13 0])) (Two MPa) := by
  have e : ([ldh .x8 (sArr aN), ld .x3 .x8] ++ minv ++ [sth .x15 sMinv, ldh .x12 sW, movi .x9 1, movi .x13 0] :
      List Instr) = [ldh .x8 (sArr aN)] ++ ([ld .x3 .x8] ++ minv ++ [sth .x15 sMinv, ldh .x12 sW, movi .x9 1,
        movi .x13 0]) := rfl
  rw [e]
  refine blk_pin _ _ [.x0] [.x0, .x8] (fun q r => match r with | .x0 => q.L.B | _ => off q.L.B (slot q.L.w aN))
    (pins_ws' (fun q : MQ => q.L.B) (fun q : MQ => q.L.Z) (fun q : MQ => q.L.w) fun _ _ h => h.1)
    (by taint_decide) (fun q s h => ?_) (by taint_decide)
    fun q s h => by rw [← e]; exact mpH_ok h
  have hw := h.1
  have hnw := hw.scr.nowrap
  have sN := hw.sl (show aN < 16 by decide)
  have h256 := hw.h256
  refine WP.mono (WP.keep [.x8] (Q := fun t => t.gpr .x8 = off q.L.B (slot q.L.w aN)) (by
    brun [hw.x0, hdr_enc (show sArr aN < 32 by decide), hw.scr.ld (d := 8 * sArr aN) (by simp only [sArr, aN]; omega),
      hw.harr aN (by decide)]) (by decide) (by decide) (by decide +kernel)) fun t ⟨h8, k⟩ r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact (k.gpr .x0 (by decide)).trans hw.x0
  · exact h8

theorem mpOne_ct : RelCT isa (Two MPa) (setWord aOne) (Two MPb) :=
  two_post (setWord_ct (by decide) (fun q : MQ => q.L.B) (fun q : MQ => q.L.Z) (fun q : MQ => q.L.w) (fun _ => 0)
    (fun _ _ h => ⟨⟨_, h.1.1.1.good⟩, h.2.1, h.2.2.2⟩)
    (by taint_decide) (by taint_decide)) fun _ _ h => mpOne_ok h

theorem mpR2_ct (M : Mont) : RelCT isa (Two MPb) (seqs (r2Steps M.mm)) (Two MPb) := by
  refine two_post ((r2_ct M).mono (fun s₁ s₂ h => two_bind (fun q t₁ t₂ h₁ h₂ => ?_) h) fun _ _ h => h)
    fun _ _ h => mpR2_ok M h
  have e₁ := mpb_r2pre h₁
  have e₂ := mpb_r2pre h₂
  refine ⟨_, e₁, ?_⟩
  have hm : word t₁.mem q.L.B (8 * sMinv) = word t₂.mem q.L.B (8 * sMinv) := by
    have e : ∀ {t : State}, MPb q t → ((q.N % 2 ^ 64) * (word t.mem q.L.B (8 * sMinv)).toNat + 1) % 2 ^ 64 = 0 :=
      fun {t} h => by
        obtain ⟨⟨⟨hw, h4, _, hn, _, _⟩, hinv⟩, _⟩ := h
        rwa [← wv_mod64 _ _ _ (show 1 ≤ q.L.w by omega), hn] at hinv
    exact minv_unique (by rw [Nat.mod_mod_of_dvd _ (by decide)]; exact h₁.1.1.2.2.2.2.1) (e h₁) (e h₂)
  rw [hm]; exact e₂

theorem mpY_ct (M : Mont) : RelCT isa (Two MPb) (M.mm aY aR2 aOne) (Two MPb) :=
  two_post (two_map (fun q : MQ => q.L) (fun _ _ h => ⟨_, h.1.1.1.good⟩)
    (M.ct (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))))) fun _ _ h => mpY_ok M h

theorem mpR1_ct : RelCT isa (Two MPb) (copyA aR1 aY) (Two MPb) := by
  have e : copyA aR1 aY = .seq (.block (ws ++ (base aY .x16 ++ base aR1 .x17))) copyWords := by
    simp only [copyA, List.append_assoc]
  rw [e]
  exact ws_ct (fun q : MQ => q.L.B) (fun q : MQ => q.L.Z) (fun q : MQ => q.L.w) (fun _ _ h => h.1.1.1)
    (by taint_decide) fun _ _ h => by rw [← e]; exact mpR1_ok h

theorem montPrep_eq (mul : Nat → Nat → Nat → Prog isa) : montPrep mul =
    ([.block (([ldh .x8 (sArr aN), ld .x3 .x8] : List Instr) ++ minv ++ ([sth .x15 sMinv, ldh .x12 sW, movi .x9 1,
      movi .x13 0] : List Instr)), setWord aOne] : List (Prog isa)) ++ (r2Steps mul ++
      (([mul aY aR2 aOne, copyA aR1 aY] : List (Prog isa)) ++ subA aRm1 aN aR1)) := by
  simp only [montPrep, List.append_assoc]

/-- `montPrep` leaks the same in runs that agree on the working space and the
modulus. -/
theorem montPrep_ct (M : Mont) : RelCT isa (Two MP0) (seqs (montPrep M.mm)) fun _ _ => True := by
  rw [montPrep_eq]
  refine ct_app' (by simp) (by simp [r2Steps]) (RelCT.seq mpH_ct mpOne_ct)
    (ct_app' (by simp [r2Steps]) (by simp) (mpR2_ct M)
      (ct_app' (by simp) (by simp [subA]) (RelCT.seq (mpY_ct M) mpR1_ct) ?_))
  rw [subA_eq']
  exact (ws_ct (Φ := MPb) (fun q : MQ => q.L.B) (fun q : MQ => q.L.Z) (fun q : MQ => q.L.w)
    (Ψ := fun _ _ => True) (fun _ _ h => h.1.1.1) (by taint_decide)
    fun _ _ h => by rw [← subA_eq']; exact WP.mono (mpRm_ok h) fun _ _ => trivial).mono (fun _ _ h => h)
    fun _ _ _ => trivial

/-! ## `expSetup` -/

/-- Before `expSetup`. -/
def EQ (q : MQ) (s : State) : Prop :=
  Ws s q.L.B q.L.Z q.L.w ∧ wv s.mem q.L.B (slot q.L.w aN) q.L.w = q.N ∧ q.N % 2 = 1 ∧ 1 < q.N

/-- `lowWord`'s registers. -/
def lwVal' (q : MQ) : Reg → BitVec 64
  | .x0 => q.L.B
  | .x12 => BitVec.ofNat 64 q.L.w
  | _ => BitVec.ofNat 64 (8 * (q.L.w + 2))

/-- `expSetup` leaks the same in runs that agree on the working space and the
modulus. -/
theorem expSetup_ct' : RelCT isa (Two EQ) (seqs expSetup) fun _ _ => True := by
  rw [expSetup_eq]
  refine ct_app' (by simp [lowWord]) (by simp) (Ψ := fun q t => ∀ r ∈ [Reg.x0, .x12, .x11], t.gpr r = lwVal' q r)
    ?_ ((two_taint [.x0, .x12, .x11] (fun _ _ _ h₁ h₂ r hr => (h₁ r hr).trans (h₂ r hr).symm)
      (by taint_decide)).mono (fun _ _ h => h) fun _ _ _ => trivial)
  have e : seqs lowWord = Code.seq _ _ := rfl
  rw [e]
  refine ws_ct (fun q : MQ => q.L.B) (fun q : MQ => q.L.Z) (fun q : MQ => q.L.w)
    (fun _ _ h => h.1) (by taint_decide) fun q s ⟨hw, hn, hodd, h1⟩ => ?_
  refine (?_ : WP isa (seqs lowWord) s _)
  exact WP.mono (lowWord_ok hw hn hodd h1) fun t ⟨_, _, _, _, h11, h12, k⟩ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (k.gpr .x0 (by decide)).trans hw.x0
    · exact h12
    · exact h11

end VG.Proof.Ffdh.AArch64.ParameterCandidate
