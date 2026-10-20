module

import VerifiedGarbage.Proof.Bignum.AArch64.CrtWs
public import VerifiedGarbage.Proof.Bignum.CrtWindowFiveLayout
public import VerifiedGarbage.Impl.Rsa.AArch64.WindowFive
public import Mathlib.Data.Int.GCD
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
public import VerifiedGarbage.Proof.Framework.Contract
import Mathlib.Data.Int.ModEq
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

@[expose] public section

namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Bignum.CrtWindowFive
open VG.Proof.MlKem.AArch64 (Keep)

/-- The next workspace starts after all 32 entries, with the same register
and memory obligations as the old 16-entry layout calculation. -/
theorem wsEndT32_ok {s : State} {X : Addr} {Z wx : Nat} (hs : Scr s X Z)
    (h5 : s.gpr .x5 = X) (hw : word s.mem X (8 * sW) = BitVec.ofNat 64 wx)
    (hwx : wx < 2 ^ 30)
    (ha : word s.mem X (8 * sArr Public.aOne) = off X (slot wx Public.aOne))
    (hZ : slot wx 8 ≤ Z) :
    WP isa (.block VG.Impl.Rsa.AArch64.WindowFive.wsEndT32) s fun t =>
      (t.gpr .x4 = off X (slot wx 8 + tabBytes32 wx) ∧ t.mem = s.mem) ∧
      Keep [.x4, .x6] s t := by
  unfold VG.Impl.Rsa.AArch64.WindowFive.wsEndT32
  rw [WP.block_append_iff]
  refine WP.mono (wsEnd_ok hs h5 hw hwx ha hZ) fun u ⟨⟨h4, h6, hm⟩, ku⟩ => ?_
  refine WP.mono (WP.keep [.x4, .x6]
    (Q := fun t => t.gpr .x4 = off X (slot wx 8 + tabBytes32 wx) ∧ t.mem = u.mem)
    (by
      brun [h4, h6, shl_ofNat (show 8 * (wx + 2) * 2 ^ 5 < 2 ^ 64 by omega)]
      refine congrArg (off X) ?_
      rw [show (2 : Nat) ^ 5 = 32 from rfl]
      unfold tabBytes32
      omega)
    (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨ht4, htm⟩, kt⟩ =>
      ⟨⟨ht4, htm.trans hm⟩, (ku.trans kt).mono (by decide)⟩

end VG.Proof.Bignum.AArch64.WindowFive
