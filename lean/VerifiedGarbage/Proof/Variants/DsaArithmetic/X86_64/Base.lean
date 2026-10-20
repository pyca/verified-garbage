module

public import VerifiedGarbage.Proof.Dsa.X86_64.Backend
import VerifiedGarbage.Proof.Dsa.X86_64.Calls
import VerifiedGarbage.Proof.Dsa.X86_64.KeygenCalls
public import VerifiedGarbage.Proof.Bignum.X86_64.MontSqFn
public import VerifiedGarbage.Proof.Rsa.X86_64.CallMont
public import VerifiedGarbage.Proof.Dsa.X86_64.Calls
public import VerifiedGarbage.Proof.Dsa.X86_64.KeygenCalls
import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.Dsa.X86_64.EqualCT
import VerifiedGarbage.Proof.Dsa.X86_64.JointCallCT
import VerifiedGarbage.Proof.Dsa.X86_64.ReadyMinusCT
import VerifiedGarbage.Proof.Dsa.X86_64.ReadyRangeCT
import VerifiedGarbage.Proof.Dsa.X86_64.ZeroCT
import VerifiedGarbage.Proof.MdStream.Spec
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxCT
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxDualAddWord
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxHeaderCopy
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxRect8Frame
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxRect8RowS
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxRect8RowSCT
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxRect8Setup
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Accumulate
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8CT
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Head
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Loop
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Memory
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8ProductStep
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Redc
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Tail
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Tile
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8TileEdges
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Word
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareBackend
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareBlock
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareDiagonal
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareDiagonalChoice
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareDiagonalStep
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareFinish
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareMont
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareWideGeneral
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareWideRow
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledCounter
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledRawCT
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledRow
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledRows
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledSquareDispatch
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledSquareRawCrossCT
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledSquareRow
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledSquareRowsCT
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledSquareRowsChoiceCT
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledTail
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledTailSetup
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxTri8Block
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxTri8Math
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxTri8RowCore
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxTri8Word
public import VerifiedGarbage.Proof.Bignum.X86_64.CallPost
public import VerifiedGarbage.Proof.Bignum.X86_64.MontFnAdxVerified
public import VerifiedGarbage.Proof.Bignum.X86_64.MontFnLazy
public import VerifiedGarbage.Proof.Bignum.X86_64.MontFnLazyCT
public import VerifiedGarbage.Proof.Bignum.X86_64.MontFnLazyVerified
public import VerifiedGarbage.Proof.Dsa.X86_64.DeriveMainCT
public import VerifiedGarbage.Proof.Dsa.X86_64.DeriveVerified
public import VerifiedGarbage.Proof.Dsa.X86_64.ParametersVerified
public import VerifiedGarbage.Proof.Dsa.X86_64.SigningABIPost
public import VerifiedGarbage.Proof.Dsa.X86_64.SigningABIPre
public import VerifiedGarbage.Proof.Dsa.X86_64.SigningVerified
public import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingABIPost
public import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingABIPre
public import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingVerified
public import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
public import VerifiedGarbage.Proof.Framework.X86_64.Frame
public import VerifiedGarbage.Proof.Mont.Read
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
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareBackend
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
import VerifiedGarbage.Proof.Bignum.X86_64.CallPost
import VerifiedGarbage.Proof.Bignum.X86_64.MontFnAdxVerified
import VerifiedGarbage.Proof.Bignum.X86_64.MontFnLazy
import VerifiedGarbage.Proof.Bignum.X86_64.MontFnLazyCT
import VerifiedGarbage.Proof.Bignum.X86_64.MontFnLazyVerified
import VerifiedGarbage.Proof.Dsa.X86_64.DeriveMainCT
import VerifiedGarbage.Proof.Dsa.X86_64.DeriveVerified
import VerifiedGarbage.Proof.Dsa.X86_64.EqualHead
import VerifiedGarbage.Proof.Dsa.X86_64.JointBuild
import VerifiedGarbage.Proof.Dsa.X86_64.JointByteCT
import VerifiedGarbage.Proof.Dsa.X86_64.JointByteHead
import VerifiedGarbage.Proof.Dsa.X86_64.JointEncode
import VerifiedGarbage.Proof.Dsa.X86_64.JointEntries
import VerifiedGarbage.Proof.Dsa.X86_64.JointInit
import VerifiedGarbage.Proof.Dsa.X86_64.JointPrepare
import VerifiedGarbage.Proof.Dsa.X86_64.JointPrepareCT
import VerifiedGarbage.Proof.Dsa.X86_64.JointRun
import VerifiedGarbage.Proof.Dsa.X86_64.JointStore
import VerifiedGarbage.Proof.Dsa.X86_64.JointWindowCT
import VerifiedGarbage.Proof.Dsa.X86_64.ParametersVerified
import VerifiedGarbage.Proof.Dsa.X86_64.SigningABIPost
import VerifiedGarbage.Proof.Dsa.X86_64.SigningABIPre
import VerifiedGarbage.Proof.Dsa.X86_64.SigningVerified
import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingABIPost
import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingABIPre
import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingVerified
import VerifiedGarbage.Proof.Dsa.X86_64.ZeroHead
import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Sha256.Stream

/-!
# Baseline x86-64 Montgomery arithmetic for DSA: the variant's code and proofs

The variant `VG.Variants.DsaArithmetic.X86_64.Base.variant`
(`Variants/DsaArithmetic/X86_64/Base.lean`), with the proofs its interface
asks for.
-/

@[expose] public section

namespace VG.Proof.Variants.DsaArithmetic.X86_64.Base

open VG VG.X86_64 VG.Proof.Dsa.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

def variant : Backend where
  sq := CallMont.lazyBase
  mul := CallMont.base.mm
  stack := 8
  suffix := ""
  features := []
  signVerified := signing_call_verified Mont.fnBase MontS.fnLazy (by decide +kernel) rfl (by decide +kernel)
  verifyVerified := verifying_call_verified Mont.fnBase MontS.fnLazy (by decide +kernel) rfl (by decide +kernel)
  signSp := Code.all_of_allInstrs (by decide +kernel)
  verifySp := Code.all_of_allInstrs (by decide +kernel)
  signDepth := by decide +kernel
  parametersVerified := parameters_call_verified Mont.fnBase MontS.fnLazy (by decide +kernel) rfl (by decide +kernel)
  deriveVerified := derive_call_verified Mont.fnBase MontS.fnLazy (by decide +kernel) rfl (by decide +kernel)
  parametersSp := Code.all_of_allInstrs (by decide +kernel)
  deriveSp := Code.all_of_allInstrs (by decide +kernel)
  parametersDepth := by decide +kernel
  deriveDepth := by decide +kernel
  stackBound := by decide

end VG.Proof.Variants.DsaArithmetic.X86_64.Base
