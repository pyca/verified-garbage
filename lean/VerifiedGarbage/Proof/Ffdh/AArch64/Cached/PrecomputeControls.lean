module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Header
public import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Precompute
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega

/-! Fixed public subset initialization and tooth-index advancement. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem setControlNat_ok {s : State} {B : Addr} {Z w i n : Nat} {mi : BitVec 64}
 (good : Good s B Z w mi) (room : slot w 8≤Z) (lower : 16≤i) (upper : i<32) (small : n<2^16) :
 WP isa (.block [movi .x3 n,sth .x3 i]) s fun t =>
 Good t B Z w mi ∧ word t.mem B (8*i)=BitVec.ofNat 64 n ∧ Outside B (8*i) 8 s.mem t.mem ∧ Keep [.x3] s t := by
 refine WP.mono (WP.keep [.x3] (Q:=fun t =>t.mem=s.mem.writeW (off B (8*i)) (BitVec.ofNat 64 n))
  ?_ rfl rfl rfl) ?_
 · brun [good.x0,hdr_enc upper,good.scr.st (d:=8*i) (by have := hdr_lt_slot w 8 upper;omega),movi_nat small]
 · rintro t ⟨mem,rest⟩
   have frame : Outside B (8*i) 8 s.mem t.mem := by rw [mem];exact writeW_outside _ _ _ (by omega)
   refine ⟨good_after_header good lower upper frame rest ((rest.gpr .x0 (by decide)).trans good.x0),?_,frame,rest⟩
   rw [mem,word_writeW_self]

theorem setControlOne_ok {s : State} {B : Addr} {Z w i : Nat} {mi : BitVec 64}
 (good : Good s B Z w mi) (room : slot w 8≤Z) (lower : 16≤i) (upper : i<32) :
 WP isa (.block [movi .x3 1,sth .x3 i]) s fun t =>
 Good t B Z w mi ∧ word t.mem B (8*i)=1#64 ∧ Outside B (8*i) 8 s.mem t.mem ∧ Keep [.x3] s t := by
 refine WP.mono (WP.keep [.x3] (Q:=fun t =>t.mem=s.mem.writeW (off B (8*i)) 1#64)
  ?_ rfl rfl rfl) ?_
 · brun [good.x0,hdr_enc upper,good.scr.st (d:=8*i) (by have := hdr_lt_slot w 8 upper;omega)]
   rfl
 · rintro t ⟨mem,rest⟩
   have frame : Outside B (8*i) 8 s.mem t.mem := by rw [mem];exact writeW_outside _ _ _ (by omega)
   refine ⟨good_after_header good lower upper frame rest ((rest.gpr .x0 (by decide)).trans good.x0),?_,frame,rest⟩
   rw [mem,word_writeW_self]

theorem basisNext_ok {s : State} {B : Addr} {Z w d : Nat} {mi : BitVec 64}
 (good : Good s B Z w mi) (room : slot w 8≤Z) (index : word s.mem B (8*sD)=BitVec.ofNat 64 d) :
 WP isa (.block Precompute.basisNext) s fun t =>
 Good t B Z w mi ∧ word t.mem B (8*sD)=BitVec.ofNat 64 (2*d) ∧
 t.gpr .x3=BitVec.ofNat 64 (2*d)-32#64 ∧ Outside B (8*sD) 8 s.mem t.mem ∧ Keep [.x3] s t := by
 have shift : BitVec.ofNat 64 d <<< 1=BitVec.ofNat 64 (2*d) := by
  rw [BitVec.shiftLeft_eq_mul_twoPow]
  change BitVec.ofNat 64 d*BitVec.ofNat 64 2=_
  rw [←BitVec.ofNat_mul,Nat.mul_comm]
 refine WP.mono (WP.keep [.x3] (Q:=fun t =>
  t.mem=s.mem.writeW (off B (8*sD)) (BitVec.ofNat 64 (2*d)) ∧
  t.gpr .x3=BitVec.ofNat 64 (2*d)-32#64) ?_ rfl rfl rfl) ?_
 · unfold Precompute.basisNext
   brun [good.x0,hdr_enc (show sD<32 by decide),header_read good room (show sD<32 by decide),
    good.scr.st (d:=8*sD) (by have := hdr_lt_slot w 8 (show sD<32 by decide);omega),index,shift]
 · rintro t ⟨⟨mem,test⟩,rest⟩
   have frame : Outside B (8*sD) 8 s.mem t.mem := by rw [mem];exact writeW_outside _ _ _ (by decide)
   refine ⟨good_after_header good (by decide) (by decide) frame rest ((rest.gpr .x0 (by decide)).trans good.x0),
    ?_,test,frame,rest⟩
   rw [mem,word_writeW_self]

end VG.Proof.Ffdh.AArch64.Cached
