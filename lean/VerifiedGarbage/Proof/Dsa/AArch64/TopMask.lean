module

public import VerifiedGarbage.Proof.Dsa.AArch64.Masks
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.AArch64.Call

/-! # Testing byte-aligned modulus bit lengths -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

theorem byte_zext_toNat (b : Byte) : (b.zeroExtend 64).toNat = b.toNat := by
  change (b.setWidth 64).toNat = _
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans b.isLt (show 2 ^ 8 < 2 ^ 64 by decide))]

/-- The first significant byte must have its high bit set for an exact
byte-aligned DSA bit length. -/
theorem topMask_ok {s : State} {b : Byte} (h3 : s.gpr .x3 = b.zeroExtend 64) :
    WP isa (.block (Checks.atLeast 128)) s fun t =>
      t.gpr .x15 = mask (decide (128 ≤ b.toNat)) ∧ t.mem = s.mem ∧ Keep [.x3, .x4, .x7, .x15] s t :=
  WP.mono (atLeast_ok s (by decide)) fun t ⟨⟨ht, hm⟩, hk⟩ =>
    ⟨by rw [ht, h3, byte_zext_toNat], hm, hk⟩

end VG.Proof.Dsa.AArch64
