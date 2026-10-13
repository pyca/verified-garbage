module

public import VerifiedGarbage.Proof.Dsa.AArch64.Operands
public import VerifiedGarbage.Proof.Dsa.AArch64.Significant
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.AArch64.Call

/-! # Reading the final encoded modulus byte for oddness validation -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem lastByte_ok {s : State} {B p : Addr} {Z n : Nat} {b : Byte}
    (hs : Scr s B Z) (hdi : s.gpr .x0 = B) (hZ : pWorkspace ≤ Z)
    (fp fl : Field) (r : Reg) (hp : word s.mem B fp.offset = p)
    (hl : word s.mem B fl.offset = BitVec.ofNat 64 n) (h1 : 1 ≤ n) (h64 : n < 2 ^ 64)
    (hr : InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 (n - 1)) 1)
    (hb : s.mem (p + BitVec.ofNat 64 (n - 1)) = b) :
    WP isa (.block [Core.field .x1 fp, Core.field .x2 fl, .add .x .x1 .x1 .x2, .subImm .x .x1 .x1 1,
      .ldrb r .x1 0]) s fun t =>
      t.gpr r = b.zeroExtend 64 ∧ t.mem = s.mem ∧ Keep [.x1, .x2, r] s t := by
  have he : p + BitVec.ofNat 64 n - BitVec.ofNat 64 1 + BitVec.ofNat 64 0 = p + BitVec.ofNat 64 (n - 1) := by
    rw [BitVec.add_zero, BitVec.sub_eq_add_neg, BitVec.add_assoc, ← BitVec.sub_eq_add_neg]
    exact congrArg (p + ·) (ofNat_sub_one' h1 h64)
  have hv : BitVec.setWidth 64 (BitVec.setWidth 32 (s.mem.read (p + BitVec.ofNat 64 (n - 1)) 1)) =
      b.zeroExtend 64 := by
    rw [ldrb_byte, hb]
  refine WP.mono (WP.keep [.x1, .x2, r] (Q := fun t =>
    t.gpr r = b.zeroExtend 64 ∧ t.mem = s.mem) ?_ (by cases r <;> rfl) rfl (by cases r <;> rfl))
    fun t ⟨⟨ht, hm⟩, hk⟩ => ⟨ht, hm, hk⟩
  unfold Core.field
  brun [hdi, field_enc, hp, hl, he, hr, hv,
    hs.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds fp).2 hZ),
    hs.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds fl).2 hZ)]

end VG.Proof.Dsa.AArch64
