module

public import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Layout
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
public import VerifiedGarbage.Proof.Bignum.AArch64.R2
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega

/-! Existing Montgomery constant initialization, with its exact array write frame. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem good_after_arrays {B : Addr} {Z w : Nat} {mi : BitVec 64} {s t : State} {rs : List Reg} {arrays : List Nat}
 (good : Good s B Z w mi) (frame : Arrays B w arrays s.mem t.mem) (rest : Keep rs s t)
 (base : t.gpr .x0=B) : Good t B Z w mi :=
 ⟨good.scr.congr rest.wr,base,frame.hdr good.hdr⟩

theorem movi_nat {n : Nat} (hn : n<2^16) : (BitVec.ofNat 16 n).setWidth 64=BitVec.ofNat 64 n := by
 apply BitVec.eq_of_toNat_eq
 simp only [BitVec.toNat_setWidth,BitVec.toNat_ofNat]
 omega

theorem const_ok {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64} {a n : Nat}
 (good : Good s B Z w mi) (room : slot w 8≤Z) (positive : 0<w) (width : w<2^31)
 (ha : a<8) (hn : n<2^16) :
 WP isa (VG.Impl.Ffdh.AArch64.Cached.const a n) s fun t =>
 Good t B Z w mi ∧ wv t.mem B (slot w a) w=n ∧
 Outside B (slot w a) (8*(w+2)) s.mem t.mem ∧
 Keep [.x7,.x8,.x9,.x12,.x13,.x14,.x16] s t := by
 unfold VG.Impl.Ffdh.AArch64.Cached.const
 rw [WP.seq_iff]
 refine WP.mono (WP.keep [.x9,.x12,.x13] (Q:=fun u =>
  u.gpr .x12=BitVec.ofNat 64 w ∧ u.gpr .x9=BitVec.ofNat 64 n ∧ u.gpr .x13=0#64 ∧ u.mem=s.mem)
  ?_ rfl rfl rfl) ?_
 · brun [good.x0,hdr_enc (show sW<32 by decide),good.scr.ld (d:=8*sW) (by have := hdr_lt_slot w 8 (show sW<32 by decide);omega),
   good.hdr.hw,movi_nat hn]
 · rintro u ⟨⟨count,value,index,memU⟩,restU⟩
   have hdrU : Hdr u.mem B w mi := memU ▸ good.hdr
   refine WP.mono (setWord_ok (good.scr.congr restU.wr)
    ((restU.gpr .x0 (by decide)).trans good.x0) hdrU room count width ha (i:=0) positive index) ?_
   rintro t ⟨number,frame,restT⟩
   have frame0 : Outside B (slot w a) (8*(w+2)) s.mem t.mem := by rw [←memU];exact frame
   have rest : Keep [.x7,.x8,.x9,.x12,.x13,.x14,.x16] s t := (restU.trans restT).mono (by decide)
   refine ⟨good_after_arrays good (Arrays.of_outside (by simp : a∈[a]) frame0 (by omega) (by omega)) rest
    ((rest.gpr .x0 (by decide)).trans good.x0),?_,frame0,rest⟩
   rw [number,value]
   simp only [BitVec.toNat_ofNat,Nat.mul_zero,Nat.pow_zero,Nat.mul_one]
   exact Nat.mod_eq_of_lt (by omega)

end VG.Proof.Ffdh.AArch64.Cached
