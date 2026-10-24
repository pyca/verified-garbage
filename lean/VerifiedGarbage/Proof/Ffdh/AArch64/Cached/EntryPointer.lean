module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Header
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

/-! Packed canonical table entries use public digit arithmetic only. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

def entryOffset (w j : Nat) : Nat := 24+8*w*(2+j)

theorem entryPtr_ok {s : State} {B ctx : Addr} {Z w j : Nat} {mi : BitVec 64}
 (good : Good s B Z w mi) (room : slot w 8≤Z)
 (context : word s.mem B (8*sCtx)=ctx) (digit : s.gpr .x3=BitVec.ofNat 64 j) :
 WP isa (.block entryPtr) s fun t =>
 (t.gpr .x17=off ctx (entryOffset w j) ∧ t.gpr .x12=BitVec.ofNat 64 w ∧ t.mem=s.mem) ∧
 Keep [.x3,.x12,.x17] s t := by
 have scale : ((BitVec.ofNat 64 j+2#64)*BitVec.ofNat 64 w) <<< 3=
   BitVec.ofNat 64 (8*w*(2+j)) := by
  rw [BitVec.shiftLeft_eq_mul_twoPow]
  change ((BitVec.ofNat 64 j+BitVec.ofNat 64 2)*BitVec.ofNat 64 w)*BitVec.ofNat 64 8=_
  rw [←BitVec.ofNat_add,←BitVec.ofNat_mul,←BitVec.ofNat_mul]
  congr 1
  simp only [Nat.add_comm,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc]
 have address : (ctx+BitVec.ofNat 64 (8*w*(2+j)))+24#64=off ctx (entryOffset w j) := by
  rw [BitVec.add_assoc,show (24#64:Addr)=BitVec.ofNat 64 24 from rfl,←BitVec.ofNat_add]
  unfold off entryOffset
  congr 2
  omega
 refine WP.keep [.x3,.x12,.x17] ?_ rfl rfl rfl
 unfold entryPtr
 brun [good.x0,hdr_enc (show sCtx<32 by decide),hdr_enc (show sW<32 by decide),
  header_read good room (show sCtx<32 by decide),header_read good room (show sW<32 by decide),
  context,good.hdr.hw,digit,scale,address]

end VG.Proof.Ffdh.AArch64.Cached
