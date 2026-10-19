module

public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Code
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Code
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTBase
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTBase
import VerifiedGarbage.Proof.Rsa.AArch64.CTBase
meta import VerifiedGarbage.Proof.Rsa.AArch64.CTBase
import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
meta import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
meta import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Bignum.Octets
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
import VerifiedGarbage.Proof.Bignum.Triangular
import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Poly1305.Limbs64
import VerifiedGarbage.Proof.Rsa.AArch64.CvFail
import VerifiedGarbage.Proof.Rsa.AArch64.CvLoad
import VerifiedGarbage.Proof.Rsa.AArch64.Inv
import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Close
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
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Trial
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
meta import VerifiedGarbage.Proof.Bignum.Triangular
meta import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Bswap
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Proof.Poly1305.Limbs64
meta import VerifiedGarbage.Proof.Rsa.AArch64.CvFail
meta import VerifiedGarbage.Proof.Rsa.AArch64.CvLoad
meta import VerifiedGarbage.Proof.Rsa.AArch64.Inv
meta import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Close
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
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Trial
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.TrialEntry
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.TrialTable
meta import VerifiedGarbage.Proof.RsaKeyGen.Bits
meta import VerifiedGarbage.Proof.RsaKeyGen.CandMath
meta import VerifiedGarbage.Proof.RsaKeyGen.Halve
meta import VerifiedGarbage.Proof.RsaKeyGen.MrMont
meta import VerifiedGarbage.Proof.RsaKeyGen.Primes
meta import VerifiedGarbage.Proof.RsaKeyGen.TrialMath

/-!
# A candidate on AArch64: constant time, the front

`code` leaks the same in runs that agree on the arguments, `e` and
`candidateLeak`, given that `kMain` does from `K0` (`code_ct`): the entry,
the zeros to `out`, the length check and the end for too few octets depend
on the arguments alone, and `kMain` on the schedule the leak fixes
(`schedOf_eq`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero)
open VG.Proof.RsaKeyGen (Sched schedOf)

/-- A state the contract allows, with the public data `q`. -/
structure CRel (q : FPub) (s : State) : Prop where
  pre : candPre s
  B : stackArg s 1 = q.B
  Z : (stackArg s 2).toNat * 8 = q.Z
  w : (s.gpr .x1).toNat = 8 * q.w
  op : s.gpr .x0 = q.op
  up : s.gpr .x2 = q.up
  eP : s.gpr .x3 = q.eP
  eB : Spec.Rsa.bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat = q.eB
  pP : s.gpr .x5 = q.pP
  pl : (s.gpr .x6).toNat = q.pl
  rP : s.gpr .x7 = q.rP
  rl : (stackArg s 0).toNat = q.rl
  wr : s.wr = q.wr
  sch : 8 * q.w ≤ q.rl → schedOf (8 * q.w) (Spec.Rsa.os2ip q.eB)
    (Spec.RsaKeyGen.otherPrime (Spec.Rsa.bytesAt s.mem (s.gpr .x5) (s.gpr .x6).toNat))
    (Spec.Rsa.bytesAt s.mem (s.gpr .x7) (stackArg s 0).toNat) = q.sch

/-- After `kEntry`'s first instruction. -/
def C1 (q : FPub) (t : State) : Prop :=
  ∃ s, CRel q s ∧ t.gpr .x8 = q.B ∧ WP isa (.block (kEntry.drop 1)) t (EntryPost s)

/-- After `kEntry`. -/
def C2 (q : FPub) (t : State) : Prop := ∃ s, CRel q s ∧ EntryPost s t

/-- After the zeros to `out`. -/
def C2' (q : FPub) (t : State) : Prop := ∃ s t₁, CRel q s ∧ EntryPost s t₁ ∧ Zeroed s t₁ t

/-- After the length check. -/
def C3 (q : FPub) (t : State) : Prop := ∃ s, CRel q s ∧ Front s t

theorem C3.x5 {q : FPub} {t : State} (h : C3 q t) :
    t.gpr .x5 = BitVec.ofNat 64 (decide (8 * q.w ≤ q.rl)).toNat := by
  obtain ⟨s, hs, hf⟩ := h
  rw [hf.x5, hs.w, hs.rl]

theorem kEntry_split : kEntry = ([.ldrSp .x8 8] : List Instr) ++ kEntry.drop 1 := rfl

theorem pins_C2 : Pins C2 [.x0] := fun _ _ _ ⟨s₁, c₁, h₁⟩ ⟨s₂, c₂, h₂⟩ r hr => by
  simp only [List.mem_singleton] at hr; subst hr
  rw [h₁.x0, h₂.x0, c₁.B, c₂.B]

/-- The registers `zeroOut`'s loop needs pinned. -/
def zoVal (ptr : Addr) (len : Nat) : Reg → BitVec 64
  | .x1 => ptr
  | .x2 => BitVec.ofNat 64 len
  | _ => 0

/-- `finNone` runs from the front. -/
theorem front_none_any {s t : State} (c : KCtx s) (h : Front s t) : WP isa finNone t fun _ => True := by
  have hZ := c.hZ
  have hk1 := c.k1
  exact WP.mono (finNone_ok (up := s.gpr .x2) (c.hs.congr h.keep.wr) h.x0 (by omega) h.args.usedP
    (c.ou.congr h.keep.wr).upw) fun _ _ => trivial

/-- The end for too few octets. -/
theorem finNone_ct {Φ : FPub → State → Prop} (hΦ : ∀ q t, Φ q t → C3 q t) :
    RelCT isa (Two Φ) finNone fun _ _ => True := by
  have e : finNone = .block (([movi .x3 0, ldh .x2 kUsedP] : List Instr) ++ [st .x3 .x2, movi .x0 0]) := rfl
  rw [e]
  refine (RelCT.block_append (pin_ct (Ψ := fun _ _ => True) [.x0] [.x2] (fun q _ => q.up)
    (fun q s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      obtain ⟨_, c₁, f₁⟩ := hΦ q s₁ h₁
      obtain ⟨_, c₂, f₂⟩ := hΦ q s₂ h₂
      rw [f₁.x0, f₂.x0, c₁.B, c₂.B]) (by taint_decide) ?_ (by taint_decide) ?_)).mono (fun _ _ h => h)
    fun _ _ _ => trivial
  · intro q t h
    obtain ⟨s, c, f⟩ := hΦ q t h
    have k := kctx_of c.pre
    have hs := k.hs.congr f.keep.wr
    have hn := hs.nowrap
    have hZ := k.hZ
    have hk1 := k.k1
    have hl : InRegions (t.rd ++ t.wr) (off (stackArg s 1) (8 * kUsedP)) 8 := hs.ld (by simp only [kUsedP, sFn]; omega)
    refine WP.mono (WP.keep [.x2, .x3] (Q := fun t' => t'.gpr .x2 = q.up) (by
      brun [f.x0, hdr_enc (show kUsedP < 32 by decide), hl, f.args.usedP, c.up]) (by decide) (by decide)
      (by decide +kernel)) fun t' ⟨h2, _⟩ r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr; exact h2
  · intro q t h
    obtain ⟨s, c, f⟩ := hΦ q t h
    have k := kctx_of c.pre
    exact WP.seq_iff.mpr (WP.block_append_iff.mp (WP.mono (front_none_any k f) fun _ _ => trivial))

/-- `kEntry` leaks the same in runs with the same public data. -/
theorem entry_ct : RelCT isa (Two CRel) (.block kEntry) (Two C2) := by
  rw [kEntry_split]
  refine RelCT.block_append (RelCT.seq (two_piece (Ψ := C1) [] (fun _ _ _ _ _ _ hr => absurd hr List.not_mem_nil)
    (by taint_decide) ?_)
    (two_piece [.x8] (fun q s₁ s₂ ⟨_, _, a₁, _⟩ ⟨_, _, a₂, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [a₁, a₂]) (by taint_decide)
      fun q t ⟨s, hs, _, hw⟩ => WP.mono hw fun t' h => ⟨s, hs, h⟩))
  intro q s hs
  have c := kctx_of hs.pre
  have hh : WP isa (.block (([.ldrSp .x8 8] : List Instr) ++ kEntry.drop 1)) s (EntryPost s) := by
    rw [← kEntry_split]; exact entry_ok c
  have hB' : s.mem.readW (s.sp + BitVec.ofNat 64 8) 64 = stackArg s 1 := rfl
  have ha1 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 8) 8 := c.ha 1 (by decide)
  have ho : 8 % 8 = 0 ∧ 8 < 32768 := ⟨rfl, by decide⟩
  refine WP.mono (WP.and (WP.block_append_iff.mp hh) (WP.keep [.x8] (Q := fun t => t.gpr .x8 = stackArg s 1)
    (by brun [exec_ldrSp ho ha1, hB']) (by decide) (by decide) (by decide +kernel))) fun t ⟨hw, h8, _⟩ =>
      ⟨s, hs, h8.trans hs.B, hw⟩

/-- The zeros to `out`. -/
theorem zeros_ct : RelCT isa (Two C2) (zeroOut kOut kLen) (Two C2') :=
  pin_ct [.x0] [.x1, .x2] (fun q => zoVal q.op (8 * q.w)) pins_C2 (by taint_decide)
    (fun q t ⟨s, c, he⟩ => by
      have k := kctx_of c.pre
      have hs := k.hs.congr he.keep.wr
      have hn := hs.nowrap
      have hZ := k.hZ
      have hk1 := k.k1
      have hl : ∀ i < 32, InRegions (t.rd ++ t.wr) (off (stackArg s 1) (8 * i)) 8 := fun i hi => hs.ld (by omega)
      refine WP.mono (WP.keep [.x1, .x2, .x3] (Q := fun t' => t'.gpr .x1 = q.op ∧
          t'.gpr .x2 = BitVec.ofNat 64 (8 * q.w)) (by
        brun [he.x0, hdr_enc (show kOut < 32 by decide), hdr_enc (show kLen < 32 by decide), hl kOut (by decide),
          hl kLen (by decide), he.args.out, he.args.len, c.op]
        rw [← c.w, ofNat_toNat64]) (by decide) (by decide) (by decide +kernel)) fun t' ⟨⟨h1, h2⟩, _⟩ r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h1
      · exact h2)
    (by taint_decide) fun q t ⟨s, c, he⟩ => WP.mono (zeros_ok (kctx_of c.pre) he) fun t' hz => ⟨s, t, c, he, hz⟩

/-- The length check. -/
theorem lenCheck_ct : RelCT isa (Two C2') (.block ([ldh .x3 kRandLen, ldh .x4 kLen] ++ geFlag)) (Two C3) :=
  two_piece [.x0] (fun q s₁ s₂ ⟨σ₁, _, c₁, e₁, z₁⟩ ⟨σ₂, _, c₂, e₂, z₂⟩ r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    rw [(z₁.keep.gpr .x0 (by decide)).trans e₁.x0, (z₂.keep.gpr .x0 (by decide)).trans e₂.x0, c₁.B, c₂.B])
    (by taint_decide) fun q t ⟨s, t₁, c, he, hz⟩ => WP.mono (lenCheck_ok (kctx_of c.pre) he hz) fun t' hf => ⟨s, c, hf⟩

/-- What `kMain` needs, from a state past the length check with enough
octets. -/
theorem C3.k0 {q : FPub} {t : State} (h : C3 q t) (hlt : 8 * q.w ≤ q.rl) : K0 q t := by
  obtain ⟨s, c, hf⟩ := h
  have k := kctx_of c.pre
  have hk1 := k.k1
  have hk2 := k.k2
  have hle : (s.gpr .x1).toNat ≤ (stackArg s 0).toNat := by rw [c.w, c.rl]; exact hlt
  have hm := mainCtx_of k hf c.w hle
  have hw := c.w
  rw [c.eB, c.B, c.Z, c.op, c.up, c.eP, c.pP, c.rP] at hm
  have hsch := c.sch hlt
  rw [c.pP, c.rP] at hsch
  refine ⟨hf.keep.wr.trans c.wr, ⟨by have := hm.z; exact this, by omega, by omega, by rw [← c.rl]; exact (stackArg s 0).isLt,
    hlt, ?_, ?_, ?_⟩, _, _, hm, by rw [bytesAt_length, c.pl], by rw [bytesAt_length, c.rl], hsch⟩
  · rw [← c.eB, bytesAt_length]; exact k.el1
  · rw [← c.eB, bytesAt_length]; exact k.el8
  · rw [← c.pl, ← c.w]; exact k.pl

/-- `vg_rsa_keygen_candidate` leaks the same in runs that agree on the public
data, given that `kMain` does. -/
theorem code_ct (M : Mont) (hK : RelCT isa (Two K0) (kMain M.mm) fun _ _ => True) :
    RelCT isa (Two CRel) (code M.mm) fun _ _ => True := by
  unfold code
  simp only [seqs]
  refine RelCT.seq entry_ct (RelCT.seq zeros_ct (RelCT.seq lenCheck_ct ?_))
  refine two_ite (fun q s₁ s₂ h₁ h₂ => by rw [eval_zero, eval_zero, h₁.x5, h₂.x5]) ?_ ?_
  · exact finNone_ct fun _ _ h => h.1
  · exact hK.mono (fun _ _ h => two_bind (fun q t₁ t₂ h₁ h₂ => ⟨q, h₁.1.k0 (by
        have := h₁.2; rw [eval_zero, h₁.1.x5] at this; revert this
        cases hd : decide (8 * q.w ≤ q.rl) <;> simp_all), h₂.1.k0 (by
        have := h₂.2; rw [eval_zero, h₂.1.x5] at this; revert this
        cases hd : decide (8 * q.w ≤ q.rl) <;> simp_all)⟩) h) fun _ _ h => h

theorem candPre_wr {s : State} (h : candPre s) :
    s.wr = [⟨s.gpr .x0, (s.gpr .x1).toNat⟩, ⟨s.gpr .x2, 8⟩, ⟨stackArg s 1, (stackArg s 2).toNat * 8⟩] := h.2.2.1

/-- The public data of a state. -/
def cpubOf (s : State) : FPub :=
  ⟨stackArg s 1, (stackArg s 2).toNat * 8, (s.gpr .x1).toNat / 8, s.wr, s.gpr .x0, s.gpr .x2, s.gpr .x3,
    Spec.Rsa.bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat, s.gpr .x5, (s.gpr .x6).toNat, s.gpr .x7,
    (stackArg s 0).toNat,
    schedOf (8 * ((s.gpr .x1).toNat / 8)) (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat))
      (Spec.RsaKeyGen.otherPrime (Spec.Rsa.bytesAt s.mem (s.gpr .x5) (s.gpr .x6).toNat))
      (Spec.Rsa.bytesAt s.mem (s.gpr .x7) (stackArg s 0).toNat)⟩

theorem crel_self {s : State} (h : candPre s) : CRel (cpubOf s) s := by
  have := (kctx_of h).k8
  exact ⟨h, rfl, rfl, by dsimp only [cpubOf]; omega, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩

/-- Runs that agree on the arguments and the leak agree on the public data. -/
theorem crel_of {s₁ s₂ : State} (h₁ : candPre s₁) (h₂ : candPre s₂) (hp : candPub s₁ s₂) :
    CRel (cpubOf s₁) s₂ := by
  obtain ⟨hr, hsp, ha, hl⟩ := hp
  have r : ∀ x ∈ argRegs, s₂.gpr x = s₁.gpr x := fun x h => (hr x h).symm
  have c := kctx_of h₁
  have hk8 := c.k8
  have hk1 := c.k1
  unfold candLeak at hl
  obtain ⟨he, hl'⟩ := List.append_inj hl (by simp only [List.length_map, bytesAt_length, r .x4 (by decide)])
  have heB := VG.Proof.RsaKeyGen.map_toNat_inj he
  refine ⟨h₂, (ha 1 (by decide)).symm, by rw [← ha 2 (by decide)]; rfl,
    by dsimp only [cpubOf]; rw [r .x1 (by decide)]; omega, r .x0 (by decide), r .x2 (by decide), r .x3 (by decide),
    heB.symm, r .x5 (by decide),
    by rw [r .x6 (by decide)]; rfl, r .x7 (by decide), by rw [← ha 0 (by decide)]; rfl, ?_, fun hk => ?_⟩
  · show s₂.wr = s₁.wr
    rw [candPre_wr h₂, candPre_wr h₁, r .x0 (by decide), r .x1 (by decide), r .x2 (by decide), ha 1 (by decide),
      ha 2 (by decide)]
  · dsimp only [cpubOf] at hk ⊢
    rw [VG.Proof.RsaKeyGen.candidateLeak_eq, VG.Proof.RsaKeyGen.candidateLeak_eq] at hl'
    unfold Spec.RsaKeyGen.candidateOp at hl'
    rw [← heB, r .x1 (by decide)] at hl'
    rw [show 8 * ((s₁.gpr .x1).toNat / 8) = (s₁.gpr .x1).toNat by omega] at hk ⊢
    refine (VG.Proof.RsaKeyGen.schedOf_eq (by omega) (by rw [bytesAt_length, bytesAt_length, ha 0 (by decide)])
      (by rw [bytesAt_length]; omega) hl').symm

/-- `vg_rsa_keygen_candidate` is constant time but for the arguments, `e` and
`candidateLeak`, given that `kMain` is from `K0`. -/
theorem code_constantTime (M : Mont) (hK : RelCT isa (Two K0) (kMain M.mm) fun _ _ => True) :
    ConstantTime isa candPre candPub (code M.mm) :=
  RelCT.constantTime ((code_ct M hK).mono (fun s₁ _ ⟨h₁, h₂, hp⟩ =>
    ⟨cpubOf s₁, crel_self h₁, crel_of h₁ h₂ hp, hp.2.1⟩) fun _ _ h => h)

end VG.Proof.RsaKeyGen.AArch64
