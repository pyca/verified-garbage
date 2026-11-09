module

import VerifiedGarbage.Proof.Bignum.X86_64.MontFnBase
import VerifiedGarbage.Proof.Mont.Read
public import VerifiedGarbage.Proof.Rsa.MontContract
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.Bignum.X86_64.MontFn
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Bignum.X86_64.MontFnBase
meta import VerifiedGarbage.Proof.Mont.Read
meta import VerifiedGarbage.Proof.Rsa.MontContract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Impl.Bignum.X86_64.MontFn
meta import VerifiedGarbage.Proof.Bignum.X86_64.Mont
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

@[expose] public section

namespace VG.Proof.Bignum.X86_64.MontFn

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.Bignum VG.Impl.Bignum.X86_64.MontFn
open VG.Impl.Bignum.X86_64.Public (aN aAcc aTmp)
open VG.Proof.Rsa.Mont (numAt wOf wordAt Layout Operand arrAt aM minvWord)

/-- The `k` words at offset `d` of `B` are the `8 k` bytes there. -/
theorem read_eq_wv (m : Mem) (B : Addr) (d : Nat) : ∀ k, (m.read (off B d) (8 * k)).toNat = wv m B d k
  | 0 => by simp [Mem.read, wv]
  | k + 1 => by
    rw [show 8 * (k + 1) = 8 + 8 * k by omega, Proof.Mont.read_toNat_add, read_eq_wv m B d k, wv,
      Offset.add_add, show 8 * (8 * k) = 64 * k by omega]
    congr 2

theorem numAt_eq (m : Mem) (B : Addr) (w j : Nat) : numAt m B w j = wv m B (slot w j) w := by
  rw [← read_eq_wv]; rfl

/-! ## Constant time -/

end VG.Proof.Bignum.X86_64.MontFn
