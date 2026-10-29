module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Header
public import VerifiedGarbage.Proof.Bignum.Words

import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.AArch64.Checks
/-! The native low-bit update touches exactly one limb of the comparison copy. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/LowOrOne.lean`, which only this module imported.
section

/-! Setting the low bit of a multiword value preserves all its higher bits. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.Proof.Bignum

theorem wv_low_or_one (m : Mem) (B : Addr) {d w : Nat} (positive : 0<w) (fit : d+8*w≤2^64) :
 wv (m.writeW (off B d) (word m B d ||| 1#64)) B d w=2*(wv m B d w/2)+1 := by
 have low := wv_mod64 m B d (by omega : 1≤w)
 have mod2 : (word m B d).toNat%2=wv m B d w%2 := by omega
 have split (m : Mem) : wv m B d w=(word m B d).toNat+2^64*wv m B (d+8) (w-1) := by
  have h := wv_add m B d 1 (w-1)
  rw [show 1+(w-1)=w by omega] at h
  simpa only [wv,Nat.mul_zero,Nat.pow_zero,Nat.mul_one,Nat.one_mul,Nat.add_zero,Nat.zero_add,Nat.reduceMul,Nat.reducePow] using h
 have frame := writeW_outside m B (word m B d ||| 1#64) (by omega : d+8≤2^64)
 have orValue := VG.Proof.Ffdh.AArch64.or1_toNat (word m B d)
 change (word m B d ||| 1#64).toNat=(word m B d).toNat+(1-(word m B d).toNat%2) at orValue
 rw [split,word_writeW_self,orValue,
  frame.wv (Or.inr (by omega : d+8≤d+8)) (by omega)]
 have original := split m
 omega

end VG.Proof.Ffdh.AArch64.Cached
end

end

@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem setLowBit_ok {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64}
 (good : Good s B Z w mi) (room : slot w 8≤Z) (positive : 0<w) :
 WP isa (.block [ldh .x8 (sArr 1),ld .x3 .x8,movi .x4 1,.logic .orr .x .x3 .x3 .x4,st .x3 .x8]) s fun t =>
 Good t B Z w mi ∧ wv t.mem B (slot w 1) w=2*(wv s.mem B (slot w 1) w/2)+1 ∧
 Arrays B w [1] s.mem t.mem ∧ Keep [.x3,.x4,.x8] s t := by
 have arrayRoom := Nat.le_trans (slot_le (w:=w) (show 1<8 by decide)) room
 refine WP.mono (WP.keep [.x3,.x4,.x8] (Q:=fun t =>
  t.mem=s.mem.writeW (off B (slot w 1)) (word s.mem B (slot w 1) ||| 1#64)) ?_ rfl rfl rfl) ?_
 · brun [good.x0,hdr_enc (show sArr 1<32 by decide),header_read good room (show sArr 1<32 by decide),
    good.hdr.harr 1 (by decide),good.scr.ld (d:=slot w 1) (by omega),good.scr.st (d:=slot w 1) (by omega)]
   rfl
 · rintro t ⟨mem,rest⟩
   have frame : Arrays B w [1] s.mem t.mem := by
    apply Arrays.of_outside (j:=1) (by simp) (o:=slot w 1) (n:=8)
    · rw [mem];exact writeW_outside _ _ _ (by have := good.scr.nowrap;omega)
    · omega
    · have := good.scr.nowrap;omega
   refine ⟨good_after_arrays good frame rest ((rest.gpr .x0 (by decide)).trans good.x0),?_,frame,rest⟩
   rw [mem]
   exact wv_low_or_one _ _ positive (by have := good.scr.nowrap;omega)

end VG.Proof.Ffdh.AArch64.Cached
