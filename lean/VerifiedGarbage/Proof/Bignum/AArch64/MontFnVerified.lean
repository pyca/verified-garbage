module

import VerifiedGarbage.Proof.Mont.Read
public import VerifiedGarbage.Proof.Rsa.MontContract
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Mont.Read
meta import VerifiedGarbage.Proof.Rsa.MontContract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Impl.Bignum.AArch64.ProductDispatch
import VerifiedGarbage.Proof.Bignum.AArch64.MontMul
public import VerifiedGarbage.Impl.Bignum.AArch64.ProductDispatch
meta import VerifiedGarbage.Impl.Bignum.AArch64.ProductDispatch
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontMul

@[expose] public section

namespace VG.Proof.Bignum.AArch64.MontFn
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Impl.Bignum
open VG.Impl.Bignum.AArch64 VG.Impl.Bignum.AArch64.MontFn
open VG.Proof.Rsa.Mont (numAt wOf wordAt Layout Operand Keeps arrAt aM minvWord)

/-- The `k` words at offset `d` of `B` are the `8 k` bytes there. -/
theorem read_eq_wv (m : Mem) (B : Addr) (d : Nat) : ∀ k, (m.read (off B d) (8 * k)).toNat = wv m B d k
  | 0 => by simp [Mem.read, wv]
  | k + 1 => by
    rw [show 8 * (k + 1) = 8 + 8 * k by omega, Proof.Mont.read_toNat_add, read_eq_wv m B d k, wv,
      Offset.add_add, show 8 * (8 * k) = 64 * k by omega]
    congr 2

theorem numAt_eq (m : Mem) (B : Addr) (w j : Nat) : numAt m B w j = wv m B (slot w j) w := by
  rw [← read_eq_wv]; rfl



end VG.Proof.Bignum.AArch64.MontFn
