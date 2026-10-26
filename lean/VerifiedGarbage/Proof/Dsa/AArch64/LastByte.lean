module
public import VerifiedGarbage.Impl.Dsa.AArch64.Core
public import VerifiedGarbage.Proof.Bignum.AArch64.Run

import VerifiedGarbage.Proof.Dsa.AArch64.Operands
import VerifiedGarbage.Proof.Dsa.Layout
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Contract

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
    WP isa (.block [Core.field .x1 fp, Core.field .x9 fl, .subImm .x .x9 .x9 1,
      .add .x .x1 .x1 .x9, .ldrb r .x1 0]) s fun t =>
      t.gpr r = b.zeroExtend 64 ∧ t.mem = s.mem ∧ Keep [.x1, .x9, r] s t := by
  have he : BitVec.ofNat 64 n - (1#64) = BitVec.ofNat 64 (n - 1) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    simp only [Nat.mod_eq_of_lt (show 1 < 2 ^ 64 by decide)]
    omega
  refine WP.mono (WP.keep [.x1, .x9, r] (Q := fun t =>
    t.gpr r = b.zeroExtend 64 ∧ t.mem = s.mem) ?_ ?_ ?_ ?_)
    fun t ⟨⟨ht, hm⟩, hk⟩ => ⟨ht, hm, hk⟩
  · brun [Core.field, hdi, field_enc fp, field_enc fl, hp, hl, he, hr, hb, read_one,
      hs.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds fp).2 hZ),
      hs.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds fl).2 hZ)]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.zeroExtend]
    have := b.isLt
    omega
  all_goals cases r <;> rfl

end VG.Proof.Dsa.AArch64
