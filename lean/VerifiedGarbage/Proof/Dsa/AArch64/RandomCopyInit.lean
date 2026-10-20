module
public import Mathlib.Data.Int.GCD
public import VerifiedGarbage.Proof.Dsa.AArch64.Run
public import VerifiedGarbage.Impl.Dsa.AArch64.Random
public import VerifiedGarbage.Proof.Framework.Contract

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! Read a complete draw's first byte and apply its public bit mask. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

theorem random_copyInit_ok {s : State} {B R src dst : Addr} {l n used : Nat} {mask : BitVec 64}
    (hs : Scr s B Random.frameBytes) (hsp : s.sp = B)
    (hR : word s.mem B Random.oRand = R) (hu : word s.mem B Random.oUsed = BitVec.ofNat 64 used)
    (hn : word s.mem B Random.oWidth = BitVec.ofNat 64 n)
    (hl : word s.mem B Random.oQLen = BitVec.ofNat 64 l)
    (hm : word s.mem B Random.oMask = mask)
    (hsrc : R + BitVec.ofNat 64 used = src)
    (hdst : off B Random.oNonce + BitVec.ofNat 64 l - BitVec.ofNat 64 n = dst)
    (hpos : 0 < n) (hbound : n < 2 ^ 64)
    (hr : InRegions (s.rd ++ s.wr) src 1) (hw : InRegions s.wr dst 1) :
    WP isa (.block Random.copyInit) s fun t =>
      t.gpr .x12 = src + 1#64 ∧ t.gpr .x2 = dst + 1#64 ∧ t.gpr .x9 = BitVec.ofNat 64 (n - 1) ∧
      t.mem = s.mem.writeW dst (((s.mem src).setWidth 64 &&& mask).setWidth 8) ∧
      Keep [.x0, .x4, .x12, .x2, .x9] s t := by
  refine WP.mono (WP.keep [.x0, .x4, .x12, .x2, .x9] (Q := fun t =>
      t.gpr .x12 = src + 1#64 ∧ t.gpr .x2 = dst + 1#64 ∧ t.gpr .x9 = BitVec.ofNat 64 (n - 1) ∧
      t.mem = s.mem.writeW dst (((s.mem src).setWidth 64 &&& mask).setWidth 8)) ?_ rfl rfl rfl)
    fun _ ⟨⟨ha, hb, hc, hm⟩, hk⟩ => ⟨ha, hb, hc, hm, hk⟩
  unfold Random.copyInit Random.copyHeader Random.copyFirst
  have hbyte (x : Byte) : (x.setWidth 32).setWidth 64 = x.setWidth 64 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth]
    have := x.isLt
    omega
  have hpred : BitVec.ofNat 64 n - 1#64 = BitVec.ofNat 64 (n - 1) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  have haddr : off B (Random.oNonce + l) - BitVec.ofNat 64 n = dst := by
    simpa only [off, BitVec.ofNat_add_ofNat, BitVec.add_assoc] using hdst
  brun [List.append_assoc, List.cons_append, List.nil_append,
    exec_addSp (show Random.oNonce < 4096 by decide),
    exec_ldrSp (show Random.oRand % 8 = 0 ∧ Random.oRand < 32768 by decide),
    exec_ldrSp (show Random.oUsed % 8 = 0 ∧ Random.oUsed < 32768 by decide),
    exec_ldrSp (show Random.oWidth % 8 = 0 ∧ Random.oWidth < 32768 by decide),
    exec_ldrSp (show Random.oQLen % 8 = 0 ∧ Random.oQLen < 32768 by decide),
    exec_ldrSp (show Random.oMask % 8 = 0 ∧ Random.oMask < 32768 by decide),
    hsp, hs.ld (d := Random.oRand) (by decide), hs.ld (d := Random.oUsed) (by decide),
    hs.ld (d := Random.oWidth) (by decide), hs.ld (d := Random.oQLen) (by decide),
    hs.ld (d := Random.oMask) (by decide), hR, hu, hn, hl, hm, hsrc, haddr,
    hr, hw, hpred, read_one, hbyte]
  rfl

end VG.Proof.Dsa.AArch64
