module
public import VerifiedGarbage.Impl.Dsa.AArch64.Checks
public import VerifiedGarbage.Proof.Dsa.AArch64.CheckFrame

import VerifiedGarbage.Proof.Dsa.AArch64.CheckCall
import VerifiedGarbage.Proof.Dsa.AArch64.LoadOne

/-! # Complete checks of DSA subgroup exponentiation results -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem isOne_ok {s : State} {B : Addr} {Z o w wx m : Nat} {minv parentMinv : BitVec 64}
    (hg : Good s B Z w parentMinv) (child : ChildReady s.mem B o wx m minv)
    (hZ : pWorkspace ≤ Z) (hlo : slot w 8 ≤ o) (hfield : 368 ≤ o)
    (hhi : o + slot wx 8 + tabBytes wx ≤ Z) (ho : o < 2 ^ 16)
    (hw2 : 2 ≤ wx) (hw48 : wx ≤ 48) (hwx : wx ≤ w) (hw30 : w < 2 ^ 30)
    (a : Operand) (ha : pointerFits a.pointer) {bytes : List Byte}
    (hlen : word s.mem B a.length.offset = BitVec.ofNat 64 bytes.length)
    (hsrc : Src s B Z (pointerValue s.mem B a.pointer) bytes)
    (h1 : 1 ≤ bytes.length) (hfit : (bytes.length + 7) / 8 ≤ wx)
    {valid : Bool} (hmask : word s.mem B Field.mask.offset = mask valid) :
    WP isa (Checks.isOne o a) s fun t =>
      Good t B Z w parentMinv ∧ ChildReady t.mem B o wx m minv ∧
      word t.mem B Field.mask.offset = mask (decide (Spec.Dsa.decodeBE bytes = 1) && valid) ∧
      RangeFrame B o wx s.mem t.mem ∧ Keep coreRegs s t := by
  have run := checkCall_ok hg child hZ hlo hfield hhi ho a ha hmask
    (body := .seq (Arithmetic.load aX arg argLen) (.seq Checks.oneScan (.block (Checks.zeroMask .x15))))
    (accepted := decide (Spec.Dsa.decodeBE bytes = 1)) ?_
  · exact run
  intro u hc hm hp hl hf hk
  exact loadOne_ok hc hm hw2 hw48 hwx hw30 (by decide) (by decide) hp (hl.trans hlen)
    (call_source hf hk (by decide) (by decide) (Nat.le_trans (by decide) hZ) hsrc) h1 hfit

end VG.Proof.Dsa.AArch64
