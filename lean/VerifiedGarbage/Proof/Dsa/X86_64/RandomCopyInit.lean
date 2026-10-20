module
public import VerifiedGarbage.Impl.Dsa.X86_64.Random
public import VerifiedGarbage.Proof.Bignum.X86_64.Words
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp

import VerifiedGarbage.Proof.Dsa.X86_64.RandomFrame
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.Push
public import Aesop.BuiltinRules
public import Mathlib.Tactic.ToDual

/-! Read a complete draw's first byte and apply its public bit mask. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

theorem random_copyInit_ok {s : State} {B R src dst : Addr} {l n used : Nat} {mask : BitVec 64}
    (hs : Scr s B Random.frameBytes) (hsp : s.gpr .rsp = B)
    (hR : word s.mem B Random.oRand = R) (hu : word s.mem B Random.oUsed = BitVec.ofNat 64 used)
    (hn : word s.mem B Random.oWidth = BitVec.ofNat 64 n)
    (hl : word s.mem B Random.oQLen = BitVec.ofNat 64 l)
    (hm : word s.mem B Random.oMask = mask)
    (hsrc : R + BitVec.ofNat 64 used = src)
    (hdst : off B Random.oNonce + BitVec.ofNat 64 l - BitVec.ofNat 64 n = dst)
    (hpos : 0 < n) (hbound : n < 2 ^ 64)
    (hr : InRegions (s.rd ++ s.wr) src 1) (hw : InRegions s.wr dst 1) :
    WP isa (.block Random.copyInit) s fun t =>
      t.gpr .r10 = src + 1 ∧ t.gpr .rdx = dst + 1 ∧ t.gpr .r11 = BitVec.ofNat 64 (n - 1) ∧
      t.zf = some (decide (n = 1)) ∧
      t.mem = s.mem.writeW dst (((s.mem src).setWidth 64 &&& mask).setWidth 8) ∧
      Keep [.rax, .r10, .rdx, .r11] s t := by
  have haddr : B + BitVec.signExtend 64 (BitVec.ofNat 32 Random.oNonce) +
      BitVec.ofNat 64 l - BitVec.ofNat 64 n = dst := hdst
  have he : (BitVec.ofNat 64 (n - 1) == 0) = decide (n = 1) := by
    rw [ofNat64_beq_zero (by omega)]
    exact decide_eq_decide.mpr (by omega)
  refine WP.mono (WP.keep [.rax, .r10, .rdx, .r11] (Q := fun t =>
      t.gpr .r10 = src + 1 ∧ t.gpr .rdx = dst + 1 ∧ t.gpr .r11 = BitVec.ofNat 64 (n - 1) ∧
      t.zf = some (decide (n = 1)) ∧
      t.mem = s.mem.writeW dst (((s.mem src).setWidth 64 &&& mask).setWidth 8)) ?_ rfl)
    fun _ ⟨⟨ha, hb, hc, hd, hm⟩, hk⟩ => ⟨ha, hb, hc, hd, hm, hk⟩
  unfold Random.copyInit Random.copyHeader Random.copyFirst Random.address
  xrun [List.append_assoc, List.cons_append, List.nil_append, random_ea_sp, hsp,
    hs.ld (d := Random.oRand) (by decide), hs.ld (d := Random.oUsed) (by decide),
    hs.ld (d := Random.oWidth) (by decide), hs.ld (d := Random.oQLen) (by decide),
    hs.ld (d := Random.oMask) (by decide), hR, hu, hn, hl, hm, hsrc, haddr,
    random_ea_base,
    hr, hw, ofNat64_pred hpos hbound, he]

end VG.Proof.Dsa.X86_64
