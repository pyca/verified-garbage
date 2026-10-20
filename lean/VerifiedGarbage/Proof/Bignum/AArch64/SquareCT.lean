module

public import VerifiedGarbage.Proof.Bignum.AArch64.SquareCtContext
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareCtContext
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.Omega
meta import Mathlib.Tactic.SplitIfs
meta import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Impl.Bignum.AArch64
import VerifiedGarbage.Proof.Bignum.AArch64.Csub
import VerifiedGarbage.Proof.Bignum.AArch64.Reduce
import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
import VerifiedGarbage.Proof.Bignum.AArch64.Row
import VerifiedGarbage.Proof.Bignum.AArch64.SquareFinish
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Poly1305.Limbs64
meta import VerifiedGarbage.Impl.Bignum.AArch64
meta import VerifiedGarbage.Proof.Bignum.AArch64.Csub
meta import VerifiedGarbage.Proof.Bignum.AArch64.Reduce
meta import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
meta import VerifiedGarbage.Proof.Bignum.AArch64.Row
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareFinish
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Bswap
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Poly1305.Limbs64

/-! Constant-time composition leaves the inverse and all arithmetic data secret. -/

@[expose] public section

namespace VG.Proof.Bignum.AArch64.Square
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Proof.Bignum.AArch64

theorem raw_body_ct (a : Nat) :
    RelCT isa (Two (SetupCtx a))
      (.seq VG.Impl.Bignum.AArch64.Square.cross VG.Impl.Bignum.AArch64.Square.diagonal)
      (fun _ _ => True) :=
  two_taint _ (pins_setup a) (by taint_decide)

theorem reduction_ct : RelCT isa (Two RawCtx)
    VG.Impl.Bignum.AArch64.Square.redc (fun _ _ => True) :=
  two_taint _ pins_raw (by taint_decide)

theorem finish_ct (o : Nat) : RelCT isa (Two (FinCtx o))
    (.seq subMod selectAcc) (fun _ _ => True) :=
  two_taint _ (pins_fin o) (by taint_decide)

theorem square_ct {o a : Nat} (ho : o < 8) (ha : a < 8)
    (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp)
    {hs hf : VG.Taint.Hint VG.AArch64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.x0])
      (.block (VG.Impl.Bignum.AArch64.Square.squareSetup a)) hs).isSome = true)
    (hF : (taint.check (Taint.ofRegs [.x0])
      (.block (VG.Impl.Bignum.AArch64.Square.finishBases o)) hf).isSome = true) :
    RelCT isa (Two GW) (VG.Impl.Bignum.AArch64.Square.square o a) (fun _ _ => True) := by
  unfold VG.Impl.Bignum.AArch64.Square.square
  refine RelCT.seq (R := Two RawCtx) ?_ ?_
  · unfold VG.Impl.Bignum.AArch64.Square.rawSquare
    exact RelCT.seq (two_piece _ pins_gw hS (setup_ctx ha))
      (two_post (raw_body_ct a) (raw_body_ctx ha ha1 ha2))
  · refine RelCT.seq (two_post reduction_ct redc_ctx) ?_
    exact RelCT.seq (two_piece _ pins_red hF (finish_bases_ctx ho)) (finish_ct o)

end VG.Proof.Bignum.AArch64.Square
