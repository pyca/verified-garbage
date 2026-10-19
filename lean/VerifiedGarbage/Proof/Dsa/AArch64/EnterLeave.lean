module

public import VerifiedGarbage.Proof.Dsa.AArch64.Run
public import Mathlib.Data.Int.GCD
public import VerifiedGarbage.Impl.Dsa.AArch64.Core
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtFrame
public import VerifiedGarbage.Proof.Framework.Contract

import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
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
import VerifiedGarbage.Proof.Bignum.AArch64.Bytes
import VerifiedGarbage.Proof.Bignum.AArch64.Copy
import VerifiedGarbage.Proof.Bignum.AArch64.CrtArith
import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
import VerifiedGarbage.Proof.Bignum.AArch64.CrtRedc
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWs
import VerifiedGarbage.Proof.Bignum.AArch64.Csub
import VerifiedGarbage.Proof.Bignum.AArch64.Double
import VerifiedGarbage.Proof.Bignum.AArch64.Mont
import VerifiedGarbage.Proof.Bignum.AArch64.PcCT
import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
import VerifiedGarbage.Proof.Bignum.AArch64.PcVerified
import VerifiedGarbage.Proof.Bignum.AArch64.PdExp
import VerifiedGarbage.Proof.Bignum.AArch64.PdLoad
import VerifiedGarbage.Proof.Bignum.AArch64.PdRest
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCorrect
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCtRows
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightMath
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightRaw
import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
import VerifiedGarbage.Proof.Bignum.AArch64.PubR2
import VerifiedGarbage.Proof.Bignum.AArch64.PubValid
import VerifiedGarbage.Proof.Bignum.AArch64.R2dQuot
import VerifiedGarbage.Proof.Bignum.AArch64.R2dRecip
import VerifiedGarbage.Proof.Bignum.AArch64.R2dSub
import VerifiedGarbage.Proof.Bignum.AArch64.Reduce
import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
import VerifiedGarbage.Proof.Bignum.AArch64.Row
import VerifiedGarbage.Proof.Bignum.AArch64.Setup
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
import VerifiedGarbage.Proof.Bignum.AArch64.Store
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Dsa.AArch64.Arithmetic
import VerifiedGarbage.Proof.Dsa.AArch64.Load
public import VerifiedGarbage.Proof.Dsa.AArch64.Operands
import VerifiedGarbage.Proof.Dsa.AArch64.Prepare
import VerifiedGarbage.Proof.Dsa.AArch64.Setup
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Poly1305.Limbs64
import VerifiedGarbage.Spec.Dsa.SignVerify
import VerifiedGarbage.Proof.Framework.AArch64.Call
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
public import VerifiedGarbage.Proof.Bignum.AArch64.Bytes
public import VerifiedGarbage.Proof.Bignum.AArch64.Copy
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtArith
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtRedc
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWs
public import VerifiedGarbage.Proof.Bignum.AArch64.Csub
public import VerifiedGarbage.Proof.Bignum.AArch64.Double
public import VerifiedGarbage.Proof.Bignum.AArch64.Mont
public import VerifiedGarbage.Proof.Bignum.AArch64.PcCT
public import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
public import VerifiedGarbage.Proof.Bignum.AArch64.PcVerified
public import VerifiedGarbage.Proof.Bignum.AArch64.PdExp
public import VerifiedGarbage.Proof.Bignum.AArch64.PdLoad
public import VerifiedGarbage.Proof.Bignum.AArch64.PdRest
public import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCorrect
public import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCtRows
public import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightMath
public import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightRaw
public import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
public import VerifiedGarbage.Proof.Bignum.AArch64.PubR2
public import VerifiedGarbage.Proof.Bignum.AArch64.PubValid
public import VerifiedGarbage.Proof.Bignum.AArch64.R2dQuot
public import VerifiedGarbage.Proof.Bignum.AArch64.R2dRecip
public import VerifiedGarbage.Proof.Bignum.AArch64.R2dSub
public import VerifiedGarbage.Proof.Bignum.AArch64.Reduce
public import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
public import VerifiedGarbage.Proof.Bignum.AArch64.Row
public import VerifiedGarbage.Proof.Bignum.AArch64.Setup
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
public import VerifiedGarbage.Proof.Bignum.AArch64.Store
public import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Dsa.AArch64.Arithmetic
public import VerifiedGarbage.Proof.Dsa.AArch64.Load
public import VerifiedGarbage.Proof.Dsa.AArch64.Prepare
public import VerifiedGarbage.Proof.Dsa.AArch64.Setup
public import VerifiedGarbage.Proof.Dsa.Arithmetic
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
public import VerifiedGarbage.Proof.Poly1305.Limbs64

/-! # Switching between the DSA parent and arithmetic workspaces -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

/-- Enter a linked child without changing memory or any other register. -/
theorem enter_ok {s : State} {B : Addr} {Z o w wx : Nat} {parentMinv minv : BitVec 64}
    (hg : Good s B Z w parentMinv) (child : WsAt s.mem B o wx minv)
    (hlo : slot w 8 ≤ o) (hhi : o + slot wx 8 + tabBytes wx ≤ Z) (ho : o < 2 ^ 16) :
    WP isa (.block (Core.enter o)) s fun t =>
      SubCtx t B Z o w wx minv ∧ t.mem = s.mem ∧ Keep [.x0, .x4] s t := by
  refine WP.mono (WP.keep [.x0, .x4] (Q := fun t => t.gpr .x0 = off B o ∧ t.mem = s.mem) ?_ rfl rfl rfl)
    fun t ⟨⟨hdi, hm⟩, hk⟩ =>
      ⟨⟨hg.scr.congr hk.wr, hdi, hm ▸ child.hdr, hm ▸ child.link,
        hm ▸ hg.hdr.hw, hm ▸ hg.hdr.harr, hlo, hhi⟩, hm, hk⟩
  unfold Core.enter
  drun [hg.x0]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

/-- Return through the child's parent link; all parent fields and operand
buffers retain the memory frame established by the arithmetic routine. -/
theorem leave_ok {s : State} {B : Addr} {Z o w wx : Nat} {minv parentMinv : BitVec 64}
    (hc : SubCtx s B Z o w wx minv)
    (hp : word s.mem B (8 * sMinv) = parentMinv) :
    WP isa (.block [Crt.leave]) s fun t =>
      Good t B Z w parentMinv ∧ t.mem = s.mem ∧ Keep [.x0] s t := by
  refine WP.mono (WP.keep [.x0] (Q := fun t => t.gpr .x0 = B ∧ t.mem = s.mem) ?_ rfl rfl rfl)
    fun t ⟨⟨hdi, hm⟩, hk⟩ =>
      ⟨⟨hc.scr.congr hk.wr, hdi, ⟨hm ▸ hc.nw, hm ▸ hp, hm ▸ hc.narr⟩⟩, hm, hk⟩
  unfold Crt.leave
  drun [hc.x0, hdr_enc (show Crt.sLink < 32 by decide), hc.link,
    hc.good.scr.ld (show 8 * Crt.sLink + 8 ≤ slot wx 8 from hdr_lt_slot wx 8 (by decide))]

end VG.Proof.Dsa.AArch64
