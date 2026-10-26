module
public import VerifiedGarbage.Impl.Rsa.AArch64.WindowFive
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore

import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Framework.Contract

@[expose] public section

namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-- One source byte is appended without changing memory or the source pointer. -/
theorem groupByte_ok {s : State} {src : Addr} {i : Nat} (hi : i < 5)
    (h3 : s.gpr .x3 = src)
    (hld : InRegions (s.rd ++ s.wr) (src + BitVec.ofNat 64 i) 1) :
    WP isa (.block (VG.Impl.Rsa.AArch64.WindowFive.groupByte i)) s fun t =>
      (t.gpr .x4 = (s.gpr .x4 <<< 8) |||
        ((s.mem.read (src + BitVec.ofNat 64 i) 1).setWidth 32).setWidth 64 ∧
        t.mem = s.mem) ∧ Keep [.x4, .x5] s t := by
  refine WP.keep _ ?_ rfl rfl rfl
  brun [VG.Impl.Rsa.AArch64.WindowFive.groupByte, h3, hld, show i < 4096 by omega]

/-- The shift-and-OR byte append is ordinary big-endian accumulation;
the bound excludes a discarded high byte. -/
theorem appendByte_value (v : Nat) (b : Byte) (hv : v < 2 ^ 56) :
    ((BitVec.ofNat 64 v <<< 8) ||| b.setWidth 64).toNat = 256 * v + b.toNat := by
  have hb := b.isLt
  have hshift : v * 2 ^ 8 < 2 ^ 64 := by omega
  have hor : v * 2 ^ 8 ||| b.toNat = v * 2 ^ 8 + b.toNat := by
    simpa only [Nat.shiftLeft_eq] using (Nat.shiftLeft_add_eq_or_of_lt hb v).symm
  rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show v < 2 ^ 64 by omega), Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt hshift, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (show b.toNat < 2 ^ 64 by omega), hor]
  omega

theorem groupByte_ct (i : Nat) :
    RelCT isa (Two fun (src : Addr) s => s.gpr .x3 = src)
      (.block (VG.Impl.Rsa.AArch64.WindowFive.groupByte i)) (fun _ _ => True) := by
  apply two_taint [.x3] (hc := .block [])
  · intro P s t hs ht r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact hs.trans ht.symm
  · rfl

end VG.Proof.Bignum.AArch64.WindowFive
