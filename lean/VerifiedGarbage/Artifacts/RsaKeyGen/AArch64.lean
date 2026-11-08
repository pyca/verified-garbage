module

public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.KeyInit
public import VerifiedGarbage.Spec.RsaKeyGen.KeySearchContract
import Mathlib.Tactic.Finiteness.Attr
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print
public import VerifiedGarbage.Proof.MillerRabin.AArch64.Backend
public import VerifiedGarbage.Impl.RsaKeyGen.AArch64.Candidate
public import VerifiedGarbage.Spec.RsaKeyGen.Contract
public import VerifiedGarbage.Proof.RsaKeyGen.Table
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.SharedVerified
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Search.Verified
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Generate.Verified
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.Verified
public import VerifiedGarbage.Proof.Rsa.AArch64.InvBatch
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
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoad
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
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightCorrect
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightCtRows
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightCtSetup
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightDiagonal
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightGuard
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightGuardCT
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightHead
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightInternal
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightLoad
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightMath
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightMont
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
import VerifiedGarbage.Proof.Bignum.Math
public import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Bignum.Triangular
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
public import VerifiedGarbage.Proof.MillerRabin.AArch64.CallerCall
public import VerifiedGarbage.Proof.MillerRabin.AArch64.CallerContext
public import VerifiedGarbage.Proof.MillerRabin.AArch64.CallerRestore
public import VerifiedGarbage.Proof.MillerRabin.AArch64.CallerResult
public import VerifiedGarbage.Proof.MillerRabin.AArch64.Context
public import VerifiedGarbage.Proof.MillerRabin.AArch64.Correct
public import VerifiedGarbage.Proof.MillerRabin.AArch64.Finish
public import VerifiedGarbage.Proof.MillerRabin.AArch64.Frame
public import VerifiedGarbage.Proof.MillerRabin.AArch64.Prepared
public import VerifiedGarbage.Proof.MillerRabin.AArch64.Verified
public import VerifiedGarbage.Proof.Poly1305.Limbs64
public import VerifiedGarbage.Proof.Rsa.AArch64.CvFail
public import VerifiedGarbage.Proof.Rsa.AArch64.CvLoad
public import VerifiedGarbage.Proof.Rsa.AArch64.Inv
public import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Close
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Code
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.GcdE
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.GcdStep
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Implies
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.KTail
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.LoadC
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.ModE
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MontSetup
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrBit
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrExp
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrSelW
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrShift
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrTail
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.SharedCode
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.SharedKMain
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.SharedMain
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.SharedTail
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Trial
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.TrialEntry
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.TrialTable
public import VerifiedGarbage.Proof.RsaKeyGen.Bits
public import VerifiedGarbage.Proof.RsaKeyGen.CandMath
public import VerifiedGarbage.Proof.RsaKeyGen.Halve
public import VerifiedGarbage.Proof.RsaKeyGen.MrMont
public import VerifiedGarbage.Proof.RsaKeyGen.Primes
public import VerifiedGarbage.Proof.RsaKeyGen.TrialMath
public import VerifiedGarbage.Proof.Variants.MillerRabin.AArch64

/-! # RSA key generation (FIPS 186-5 A.1.3) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.RsaKeyGen.AArch64

def direct : List Artifact := [
  Spec.RsaKeyGen.keyInitApi.artifact AArch64.target {
    code := Impl.RsaKeyGen.AArch64.KeyInit.init
    verified := Proof.RsaKeyGen.AArch64.KeyInit.init_verified }]

end VG.Artifacts.RsaKeyGen.AArch64

-- RSA key generation on AArch64, its prime searches' candidates calling each shared Miller–Rabin implementation
namespace VG.Artifacts.RsaKeyGen.AArch64.MillerRabin

def artifacts (v : Proof.MillerRabin.AArch64.RoundImpl) : List Artifact := [
  Spec.RsaKeyGen.keySearchApi.artifact AArch64.target {
    suffix := v.suffix
    stack := 416
    code := Proof.RsaKeyGen.AArch64.Generate.genCode v
    verified := Proof.RsaKeyGen.AArch64.Generate.gen_verified v
    features := v.features }]

end VG.Artifacts.RsaKeyGen.AArch64.MillerRabin

namespace VG.Artifacts.RsaKeyGen.AArch64

def artifacts : List Artifact :=
  direct ++
  (VG.Proof.Variants.MillerRabin.AArch64.variants.flatMap fun v => MillerRabin.artifacts v)

end VG.Artifacts.RsaKeyGen.AArch64
