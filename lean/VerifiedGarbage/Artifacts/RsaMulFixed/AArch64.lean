module

public import VerifiedGarbage.Proof.Bignum.AArch64.MulFixedHelper
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
public import VerifiedGarbage.Impl.Bignum.AArch64
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcAdd
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcColumns
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCorrect
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtLoop
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtRow
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtSpill
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcEnd
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcExtend
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLayout
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoad
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoop
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcSquare
public import VerifiedGarbage.Proof.Bignum.AArch64.Csub
public import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCorrect
public import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCtRows
public import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightGuard
public import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightGuardCT
public import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightMath
public import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightRaw
public import VerifiedGarbage.Proof.Bignum.AArch64.Reduce
public import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
public import VerifiedGarbage.Proof.Bignum.AArch64.Row
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareCT
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareCall
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareCallCT
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareCallMont
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightGuard
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightGuardCT
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightMont
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareFinish
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareGuard
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareLayout
public import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
public import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Proof.Framework.AArch64.RelCT
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Bswap
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Framework.TaintBatch
public import VerifiedGarbage.Proof.Mont.Read
public import VerifiedGarbage.Proof.Poly1305.Limbs64

/-! # Fixed-index RSA Montgomery products on AArch64 -/

@[expose] public section

namespace VG.Artifacts.RsaMulFixed.AArch64
open VG.AArch64

def helper (ix : Spec.Rsa.MontMulFixed.Indices)
    (v : Verified target (Proof.Bignum.AArch64.Mont.productEight.mm ix.o ix.a ix.b)
      (Spec.Rsa.MontMulFixed.mulContract ix abi)) : Artifact :=
  (Spec.Rsa.MontMulFixed.mulApi ix).artifact target {
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
  helper ⟨6, 5, 1⟩ (MulFixedHelper.verified Mont.productEight ⟨6, 5, 1⟩),
  helper ⟨5, 1, 7⟩ (MulFixedHelper.verified Mont.productEight ⟨5, 1, 7⟩),
  helper ⟨1, 1, 6⟩ (MulFixedHelper.verified Mont.productEight ⟨1, 1, 6⟩),
  helper ⟨4, 4, 7⟩ (MulFixedHelper.verified Mont.productEight ⟨4, 4, 7⟩),
  helper ⟨6, 4, 6⟩ (MulFixedHelper.verified Mont.productEight ⟨6, 4, 6⟩)]

end VG.Artifacts.RsaMulFixed.AArch64
