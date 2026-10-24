module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Controls
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega

/-! Public header controls drive the proved five-tooth scalar gather. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem digitArgs_ok {s : State} {B src ctx : Addr} {Z w N i : Nat} {mi : BitVec 64} {bs : List Byte}
 (good : Good s B Z w mi) (room : slot w 8≤Z) (controls : Controls B src ctx bs.length N s)
 (counter : Counter B (i+1) s) (indexFit : i+1<2^64) :
 WP isa (.block [ldh .x1 sX,ldh .x2 sLen,ldh .x9 sI,.subImm .x .x9 .x9 1,
 ldh .x4 sRows,ldh .x5 sBits,movi .x16 0]) s fun t =>
 (t.gpr .x1=src ∧ t.gpr .x2=BitVec.ofNat 64 bs.length ∧ t.gpr .x9=BitVec.ofNat 64 i ∧
 t.gpr .x4=BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows N) ∧ t.gpr .x5=BitVec.ofNat 64 N ∧
 t.gpr .x16=0#64 ∧ t.mem=s.mem) ∧ Keep [.x1,.x2,.x4,.x5,.x9,.x16] s t := by
 refine WP.keep [.x1,.x2,.x4,.x5,.x9,.x16] ?_ rfl rfl rfl
 have decrement : BitVec.ofNat 64 (i+1)-1#64=BitVec.ofNat 64 i := by
  rw [BitVec.ofNat_sub_ofNat_of_le (i+1) 1 (by decide) (by omega)]
  congr 1
 unfold Counter at counter
 brun [good.x0,hdr_enc (show sX<32 by decide),hdr_enc (show sLen<32 by decide),
 hdr_enc (show sI<32 by decide),hdr_enc (show sRows<32 by decide),hdr_enc (show sBits<32 by decide),
 header_read good room (show sX<32 by decide),header_read good room (show sLen<32 by decide),
 header_read good room (show sI<32 by decide),header_read good room (show sRows<32 by decide),
 header_read good room (show sBits<32 by decide),
 controls.source,controls.length,controls.rows,controls.bits,counter,decrement]

theorem digit_ok {s : State} {B src ctx : Addr} {Z w N i : Nat} {mi : BitVec 64} {bs : List Byte}
 (good : Good s B Z w mi) (room : slot w 8≤Z) (controls : Controls B src ctx bs.length N s)
 (counter : Counter B (i+1) s) (source : Source src bs s)
 (size : bs.length<2^31) (widthBound : N≤8*bs.length)
 (positions : i+5*Spec.Rsa.FixedBaseComb.rows N<2^63) (bound : Spec.Rsa.os2ip bs<2^N) :
 WP isa VG.Impl.Ffdh.AArch64.Cached.Comb.digit s fun t =>
 Good t B Z w mi ∧ Controls B src ctx bs.length N t ∧ Counter B (i+1) t ∧
 word t.mem B (8*sD)=BitVec.ofNat 64 (VG.Proof.Rsa.FixedBaseComb.digit N (Spec.Rsa.os2ip bs) i) ∧
 Outside B (8*sD) 8 s.mem t.mem ∧ Keep mmRegs s t := by
 unfold VG.Impl.Ffdh.AArch64.Cached.Comb.digit
 rw [WP.seq_iff]
 refine WP.mono (digitArgs_ok good room controls counter (by omega)) ?_
 rintro u ⟨⟨ptr,len,row,spacing,width,zero,memU⟩,restU⟩
 rw [WP.seq_iff]
 refine WP.mono (gather_ok u (source.of_mem memU restU) size widthBound positions
  ptr len row width spacing zero) ?_
 rintro z ⟨digit,memZ,restZ⟩
 have mem : z.mem=s.mem := memZ.trans memU
 have goodZ : Good z B Z w mi :=
  ⟨good.scr.congr (restU.trans restZ).wr,((restU.trans restZ).gpr .x0 (by simp [gatherClobbers])).trans good.x0,mem ▸ good.hdr⟩
 refine WP.mono (store_control_ok goodZ room (by decide : 16≤sD) (by decide : sD<32) .x16) ?_
 rintro t ⟨goodT,memT,frameT,restT⟩
 have frame : Outside B (8*sD) 8 s.mem t.mem := by rw [←mem];exact frameT
 refine ⟨goodT,controls.after_digit frame,?_,?_,frame,((restU.trans restZ).trans restT).mono (by simp [gatherClobbers,mmRegs])⟩
 · exact (header_other frame (by decide) (by decide) (by decide)).trans counter
 · rw [memT,word_writeW_self,digit,prefixValue_eq_digit bs N i widthBound bound]

end VG.Proof.Ffdh.AArch64.Cached
