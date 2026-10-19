module

import VerifiedGarbage.Proof.Bignum.AArch64.MulFixedHelper
public import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightMont
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Impl.Bignum.AArch64.MulFixedCall
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Rsa.MontMulFixed
import VerifiedGarbage.Impl.Bignum.AArch64
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcAdd
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcColumns
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCorrect
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtLoop
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtRow
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtSpill
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcEnd
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcExtend
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLayout
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoad
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoop
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcSquare
import VerifiedGarbage.Proof.Bignum.AArch64.Csub
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCorrect
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCtRows
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightGuard
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightGuardCT
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightMath
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightRaw
import VerifiedGarbage.Proof.Bignum.AArch64.Reduce
import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
import VerifiedGarbage.Proof.Bignum.AArch64.Row
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCT
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCall
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCallCT
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCallMont
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightGuard
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightGuardCT
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightMont
import VerifiedGarbage.Proof.Bignum.AArch64.SquareFinish
import VerifiedGarbage.Proof.Bignum.AArch64.SquareGuard
import VerifiedGarbage.Proof.Bignum.AArch64.SquareLayout
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Poly1305.Limbs64

/-! # Fixed-index RSA Montgomery products on AArch64

The products DSA repeats (`MulFixedCall.shared`), each shared by one
helper that runs the eight-limb product. -/

@[expose] public section

namespace VG.Artifacts.RsaMulFixed.AArch64
open VG.AArch64

def helper (ix : Spec.Rsa.MontMulFixed.Indices)
    (v : Verified target (Proof.Bignum.AArch64.Mont.productEight.mm ix.o ix.a ix.b)
      (Spec.Rsa.MontMulFixed.mulContract ix abi)) : Artifact :=
  (Spec.Rsa.MontMulFixed.mulApi ix).artifact target {
    notes := ["Baseline AArch64: the eight-limb product kernel with blocked reduction when the \
        width is a multiple of eight limbs; other widths retain the row-wise multiplication."]
    code := Proof.Bignum.AArch64.Mont.productEight.mm ix.o ix.a ix.b
    verified := v }

open Proof.Bignum.AArch64 in
def artifacts : List Artifact := [
  helper ⟨5, 1, 4⟩ (MulFixedHelper.verified Mont.productEight ⟨5, 1, 4⟩),
  helper ⟨6, 5, 6⟩ (MulFixedHelper.verified Mont.productEight ⟨6, 5, 6⟩),
  helper ⟨6, 4, 7⟩ (MulFixedHelper.verified Mont.productEight ⟨6, 4, 7⟩),
  helper ⟨5, 5, 4⟩ (MulFixedHelper.verified Mont.productEight ⟨5, 5, 4⟩),
  helper ⟨6, 6, 5⟩ (MulFixedHelper.verified Mont.productEight ⟨6, 6, 5⟩),
  helper ⟨6, 6, 7⟩ (MulFixedHelper.verified Mont.productEight ⟨6, 6, 7⟩),
  helper ⟨1, 1, 4⟩ (MulFixedHelper.verified Mont.productEight ⟨1, 1, 4⟩),
  helper ⟨6, 5, 1⟩ (MulFixedHelper.verified Mont.productEight ⟨6, 5, 1⟩)]

end VG.Artifacts.RsaMulFixed.AArch64
