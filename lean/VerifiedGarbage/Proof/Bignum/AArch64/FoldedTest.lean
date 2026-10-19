module
public import VerifiedGarbage.Impl.Rsa.AArch64.Folded
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
public import VerifiedGarbage.Proof.Framework.Contract

import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.AArch64.PubValid
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

@[expose] public section
namespace VG.Proof.Bignum.AArch64.FoldedPublic
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero read_one)

def byteWord (b : Byte) : BitVec 64 := (b.setWidth 32).setWidth 64

theorem test_zero (a b c : Byte) :
    ((byteWord a - 1#64) ||| byteWord b ||| (byteWord c - 1#64) = 0#64) ↔
      Spec.Rsa.os2ip [a,b,c] = 65537 := by
  have ha := a.isLt
  have hb := b.isLt
  have hc := c.isLt
  simp only [BitVec.or_eq_zero_iff, BitVec.sub_eq_iff_eq_add, BitVec.zero_add]
  simp only [← BitVec.toNat_inj, byteWord, byte_toNat, BitVec.toNat_ofNat]
  simp only [Spec.Rsa.os2ip, List.foldl_cons, List.foldl_nil]
  omega

theorem lengthTest_ok {s : State} {B : Addr} {Z w n : Nat} {mi : BitVec 64}
    (hg : Good s B Z w mi) (hZ : slot w 8 ≤ Z) (hn : n < 2^31)
    (hc : word s.mem B (8*sElen) = BitVec.ofNat 64 n) :
    WP isa (.block Folded.lengthTest) s fun t =>
      isa.eval (.zero .x .x3) t = some (decide (n = 3)) ∧ t.mem = s.mem ∧ Keep [.x3] s t := by
  have bound : 8*sElen+8 ≤ Z := by have := hdr_lt_slot w 8 (show sElen < 32 by decide); omega
  refine WP.mono (WP.keep [.x3] (Q := fun t =>
    t.gpr .x3 = BitVec.ofNat 64 n - 3#64 ∧ t.mem = s.mem) ?_ rfl rfl rfl)
    fun t ⟨⟨hr,hm⟩,hk⟩ => ?_
  · unfold Folded.lengthTest
    brun [hg.x0, hdr_enc (show sElen < 32 by decide), hg.scr.ld bound, hc]
  refine ⟨?_,hm,hk⟩
  rw [eval_zero, hr]
  congr 1
  apply decide_eq_decide.mpr
  change (BitVec.ofNat 64 n - 3#64 = 0#64) ↔ n = 3
  rw [BitVec.sub_eq_iff_eq_add, BitVec.zero_add, ← BitVec.toNat_inj,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rfl

theorem bytesTest_ok {s : State} {B ep : Addr} {Z w : Nat} {mi : BitVec 64}
    (hg : Good s B Z w mi) (hZ : slot w 8 ≤ Z)
    (he : word s.mem B (8*sE) = ep) (a b c : Byte)
    (hread : ∀ i < 3, InRegions (s.rd ++ s.wr) (ep + BitVec.ofNat 64 i) 1)
    (ha : s.mem ep = a) (hb : s.mem (ep+1#64) = b) (hc : s.mem (ep+2#64) = c) :
    WP isa (.block Folded.bytesTest) s fun t =>
      isa.eval (.zero .x .x3) t = some (decide (Spec.Rsa.os2ip [a,b,c] = 65537)) ∧
      t.mem = s.mem ∧ Keep [.x3,.x4,.x8] s t := by
  have bound : 8*sE+8 ≤ Z := by have := hdr_lt_slot w 8 (show sE < 32 by decide); omega
  refine WP.mono (WP.keep [.x3,.x4,.x8] (Q := fun t =>
    t.gpr .x3 = ((byteWord a - 1#64) ||| byteWord b ||| (byteWord c - 1#64)) ∧ t.mem = s.mem)
    ?_ rfl rfl rfl) fun t ⟨⟨hr,hm⟩,hk⟩ => ?_
  · unfold Folded.bytesTest
    have h0 := hread 0 (by decide)
    change InRegions (s.rd ++ s.wr) (ep + 0#64) 1 at h0
    rw [BitVec.add_zero] at h0
    brun [hg.x0, hdr_enc (show sE < 32 by decide), hg.scr.ld bound, he, h0,
      hread 1 (by decide), hread 2 (by decide), read_one, ha, hb, hc, byteWord]
  refine ⟨?_,hm,hk⟩
  rw [eval_zero, hr]
  exact congrArg some (decide_eq_decide.mpr (test_zero a b c))

end VG.Proof.Bignum.AArch64.FoldedPublic
