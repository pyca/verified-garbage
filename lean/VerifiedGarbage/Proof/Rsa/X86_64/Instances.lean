module

import VerifiedGarbage.Proof.Bignum.X86_64.CrtVerified
import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Verified
import VerifiedGarbage.Proof.Rsa.X86_64.CvVerified
import VerifiedGarbage.Proof.Rsa.X86_64.KeyVerified
import VerifiedGarbage.Proof.Rsa.X86_64.CrtKeyVerified
import VerifiedGarbage.Proof.Rsa.X86_64.Calls
public import VerifiedGarbage.Proof.Rsa.X86_64.IfmaLit
public import VerifiedGarbage.Impl.Rsa.X86_64.Recover
public import VerifiedGarbage.Proof.Bignum.Amm52
public import VerifiedGarbage.Impl.Rsa.X86_64.CheckKey
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
public import VerifiedGarbage.Impl.Bignum.X86_64.R2Adx
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExpL
import VerifiedGarbage.Proof.Bignum.X86_64.MontSqFn
import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Main
import VerifiedGarbage.Impl.Poly1305.X86_64.Avx2
import VerifiedGarbage.Proof.Bignum.CrtMath
import VerifiedGarbage.Proof.Bignum.LazyMath
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
import VerifiedGarbage.Proof.Bignum.X86_64.AdxCT
import VerifiedGarbage.Proof.Bignum.X86_64.AdxDualAddWord
import VerifiedGarbage.Proof.Bignum.X86_64.AdxHeaderCopy
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRect8Frame
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRect8RowS
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRect8RowSCT
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRect8Setup
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Accumulate
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8CT
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Head
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Loop
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Memory
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8ProductStep
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Redc
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Tail
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Tile
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8TileEdges
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Word
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareBlock
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareDiagonal
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareDiagonalChoice
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareDiagonalStep
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareFinish
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareMont
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareWideGeneral
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareWideRow
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledCounter
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledRawCT
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledRow
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledRows
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledSquareDispatch
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledSquareRawCrossCT
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledSquareRow
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledSquareRowsCT
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledSquareRowsChoiceCT
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledTail
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledTailSetup
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTri8Block
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTri8Math
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTri8RowCore
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTri8Word
import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
import VerifiedGarbage.Proof.Bignum.X86_64.CallPost
import VerifiedGarbage.Proof.Bignum.X86_64.Compare8
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp5
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTGPow
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTPMq
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTRedc
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTRows
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSelV
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupWs
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChk
import VerifiedGarbage.Proof.Bignum.X86_64.CrtMain
import VerifiedGarbage.Proof.Bignum.X86_64.CrtPow
import VerifiedGarbage.Proof.Bignum.X86_64.CrtRows
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSetup
import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
import VerifiedGarbage.Proof.Bignum.X86_64.Csub
import VerifiedGarbage.Proof.Bignum.X86_64.Double
import VerifiedGarbage.Proof.Bignum.X86_64.FoldedBackend
import VerifiedGarbage.Proof.Bignum.X86_64.FoldedCTChecked
import VerifiedGarbage.Proof.Bignum.X86_64.FoldedCTLoop
import VerifiedGarbage.Proof.Bignum.X86_64.FoldedChecked
import VerifiedGarbage.Proof.Bignum.X86_64.FoldedCode
import VerifiedGarbage.Proof.Bignum.X86_64.FoldedCounter
import VerifiedGarbage.Proof.Bignum.X86_64.FoldedMain
import VerifiedGarbage.Proof.Bignum.X86_64.FoldedPublic
import VerifiedGarbage.Proof.Bignum.X86_64.FoldedStep
import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.CTMain
import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Conv
import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Core
import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.CoreU
import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Post
import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.StepU
import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Vec
import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.VecR
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.MontFnAdxVerified
import VerifiedGarbage.Proof.Bignum.X86_64.MontFnLazy
import VerifiedGarbage.Proof.Bignum.X86_64.MontFnLazyCT
import VerifiedGarbage.Proof.Bignum.X86_64.MontFnLazyVerified
import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
import VerifiedGarbage.Proof.Bignum.X86_64.PcFn
import VerifiedGarbage.Proof.Bignum.X86_64.PcVerified
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
import VerifiedGarbage.Proof.Bignum.X86_64.PubVerified
import VerifiedGarbage.Proof.Bignum.X86_64.R2aStep
import VerifiedGarbage.Proof.Bignum.X86_64.R2aSub
import VerifiedGarbage.Proof.Bignum.X86_64.R2aWord
import VerifiedGarbage.Proof.Bignum.X86_64.R2wAdd
import VerifiedGarbage.Proof.Bignum.X86_64.R2wDiv
import VerifiedGarbage.Proof.Bignum.X86_64.R2wStep
import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.Setup
import VerifiedGarbage.Proof.Bignum.X86_64.Valid
import VerifiedGarbage.Proof.Bignum.X86_64.WordIOLoad
import VerifiedGarbage.Proof.Bignum.X86_64.WordIOStore
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.X86_64.StraightY
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Poly1305.Limbs64
import VerifiedGarbage.Proof.Rsa.KeyParts
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
import VerifiedGarbage.Proof.Rsa.X86_64.CallPatch
import VerifiedGarbage.Proof.Rsa.X86_64.CrtKeyCTCode
import VerifiedGarbage.Proof.Rsa.X86_64.CrtKeyCTReduce
import VerifiedGarbage.Proof.Rsa.X86_64.CrtKeyPhases
import VerifiedGarbage.Proof.Rsa.X86_64.CrtKeyReduce
import VerifiedGarbage.Proof.Rsa.X86_64.CvCTCode
import VerifiedGarbage.Proof.Rsa.X86_64.CvCTMain
import VerifiedGarbage.Proof.Rsa.X86_64.CvFail
import VerifiedGarbage.Proof.Rsa.X86_64.Inv
import VerifiedGarbage.Proof.Rsa.X86_64.KeyCTLoads
import VerifiedGarbage.Proof.Rsa.X86_64.KeyCTMain
import VerifiedGarbage.Proof.Rsa.X86_64.KeyChecks
import VerifiedGarbage.Proof.Rsa.X86_64.KeyDbl
import VerifiedGarbage.Proof.Rsa.X86_64.KeyImplies
import VerifiedGarbage.Proof.Rsa.X86_64.KeyMod
import VerifiedGarbage.Proof.Rsa.X86_64.KeyPhases
import VerifiedGarbage.Proof.Rsa.X86_64.KeySteps
import VerifiedGarbage.Proof.Rsa.X86_64.KeyWide
import VerifiedGarbage.Proof.Rsa.X86_64.Loops
import VerifiedGarbage.Proof.Rsa.X86_64.RpCT4
import VerifiedGarbage.Proof.Rsa.X86_64.RpCT5
import VerifiedGarbage.Proof.Rsa.X86_64.RpCT7
import VerifiedGarbage.Proof.Rsa.X86_64.RpCT8
import VerifiedGarbage.Proof.Rsa.X86_64.RpFin
import VerifiedGarbage.Proof.Rsa.X86_64.RpFrame
import VerifiedGarbage.Proof.Rsa.X86_64.RpLt
import VerifiedGarbage.Proof.Rsa.X86_64.RpMont
import VerifiedGarbage.Proof.Rsa.X86_64.RpOut
import VerifiedGarbage.Proof.Rsa.X86_64.RpProd
import VerifiedGarbage.Proof.Rsa.X86_64.RpSkip
import VerifiedGarbage.Proof.Rsa.X86_64.RpVerified

/-!
# RSA on x86-64: the proofs `Artifacts/Rsa/X86_64.lean` registers

Each function's `Verified`, made from the proofs of its code and the checks
the kernel evaluates on it (that it inlines, and that every load of MXCSR
restores it).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.Instances

open VG.X86_64 VG.Proof.Rsa.X86_64

theorem precompute_verified :
    Verified target (Impl.Rsa.X86_64.Precompute.code Proof.Rsa.X86_64.CallMont.base.mm)
      (Spec.Rsa.publicPrecomputeContract abi 8) :=
  pc_call_verified Proof.Bignum.X86_64.Mont.fnBase (Proof.Bignum.X86_64.R2Impl.words _)
    (by decide +kernel) rfl (by decide +kernel)

theorem precomputeAdx_verified :
    Verified target (Impl.Rsa.X86_64.Precompute.code Proof.Rsa.X86_64.CallMont.adx.mm
      (Impl.Bignum.X86_64.R2Adx.choice Proof.Rsa.X86_64.CallMont.adx.mm))
      (Spec.Rsa.publicPrecomputeContract abi 8) :=
  pc_call_verified Proof.Bignum.X86_64.Mont.fnAdx (Proof.Bignum.X86_64.R2Impl.adx _)
    (by decide +kernel) rfl (by decide +kernel)

theorem crt_verified :
    Verified target (Impl.Rsa.X86_64.Crt.code Proof.Rsa.X86_64.CallMont.base.mm
      (Impl.Rsa.X86_64.Crt.expLoopS Proof.Rsa.X86_64.CallMont.lazyBase Proof.Rsa.X86_64.CallMont.base.mm
        Impl.Rsa.X86_64.Crt.tabSelect))
      (Spec.Rsa.privateCrtContract abi 8) :=
  crt_call_verified (by decide +kernel)
    (Proof.Bignum.X86_64.crtCode_correct Proof.Bignum.X86_64.Mont.fnBase
      (Proof.Bignum.X86_64.CrtExpL.w4S Proof.Bignum.X86_64.Mont.fnBase Proof.Bignum.X86_64.MontS.fnLazy)
      (by decide +kernel))
    (Proof.Bignum.X86_64.crtCode_constantTime Proof.Bignum.X86_64.Mont.fnBase
      (Proof.Bignum.X86_64.CrtExpL.w4S Proof.Bignum.X86_64.Mont.fnBase Proof.Bignum.X86_64.MontS.fnLazy)
      (Proof.Bignum.X86_64.CrtExpL.w4S_ct Proof.Bignum.X86_64.Mont.fnBase Proof.Bignum.X86_64.MontS.fnLazy))

theorem crtAdx_verified :
    Verified target (Impl.Rsa.X86_64.Crt.code Proof.Rsa.X86_64.CallMont.adx.mm
      (Impl.Rsa.X86_64.Crt.expLoop5S Proof.Rsa.X86_64.CallMont.lazyAdx Proof.Rsa.X86_64.CallMont.adx.mm
        Impl.Rsa.X86_64.Crt.tabSelectV))
      (Spec.Rsa.privateCrtContract abi 8) :=
  crt_call_verified (by decide +kernel)
    (Proof.Bignum.X86_64.crtCode_correct Proof.Bignum.X86_64.Mont.fnAdx
      (Proof.Bignum.X86_64.CrtExpL.w5S Proof.Bignum.X86_64.Mont.fnAdx Proof.Bignum.X86_64.MontS.fnLazyAdx)
      (by decide +kernel))
    (Proof.Bignum.X86_64.crtCode_constantTime Proof.Bignum.X86_64.Mont.fnAdx
      (Proof.Bignum.X86_64.CrtExpL.w5S Proof.Bignum.X86_64.Mont.fnAdx Proof.Bignum.X86_64.MontS.fnLazyAdx)
      (Proof.Bignum.X86_64.CrtExpL.w5S_ct Proof.Bignum.X86_64.Mont.fnAdx Proof.Bignum.X86_64.MontS.fnLazyAdx))

theorem crtIfma_verified :
    Verified target (Impl.Rsa.X86_64.CrtIfma.code Proof.Rsa.X86_64.CallMont.adx.mm)
      (Spec.Rsa.privateCrtContract abi 8) :=
  crt_call_verified (by lit_decide)
    (Proof.Bignum.X86_64.Ifma.code_correct Proof.Bignum.X86_64.Mont.fnAdx (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel))
    (Proof.Bignum.X86_64.Ifma.code_constantTime Proof.Bignum.X86_64.Mont.fnAdx (by decide +kernel))

theorem crtValues_verified :
    Verified target (Impl.Rsa.X86_64.Keys.CrtValues.code)
      (Spec.Rsa.crtValuesContract abi) :=
  cv_verified (by decide +kernel)

theorem recover_verified :
    Verified target (Impl.Rsa.X86_64.Keys.Recover.code Proof.Rsa.X86_64.CallMont.base.mm)
      (Spec.Rsa.recoverPrimesContract abi 8) :=
  rp_call_verified Proof.Bignum.X86_64.Mont.fnBase (by decide +kernel) rfl (by decide +kernel)

theorem recoverAdx_verified :
    Verified target (Impl.Rsa.X86_64.Keys.Recover.code Proof.Rsa.X86_64.CallMont.adx.mm)
      (Spec.Rsa.recoverPrimesContract abi 8) :=
  rp_call_verified Proof.Bignum.X86_64.Mont.fnAdx (by decide +kernel) rfl (by decide +kernel)

theorem checkKey_verified :
    Verified target (Impl.Rsa.X86_64.CheckKey.code)
      (Spec.Rsa.checkKeyContract abi) :=
  Key.key_verified (by decide +kernel)

theorem checkCrtKey_verified :
    Verified target (Impl.Rsa.X86_64.CheckCrtKey.code)
      (Spec.Rsa.checkCrtKeyContract abi) :=
  Key.ck_verified (by decide +kernel)

end VG.Proof.Rsa.X86_64.Instances
