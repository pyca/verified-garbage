module

public import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Policy
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Header
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega

/-! Decode and advance one public vetted-domain record. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem widen32 {n : Nat} (fit : n<2^32) :
 (BitVec.ofNat 32 n).setWidth 64=BitVec.ofNat 64 n := by
 apply BitVec.eq_of_toNat_eq
 simp only [BitVec.toNat_setWidth,BitVec.toNat_ofNat]
 omega

theorem policyRecordHead {s : State} {B rec : Addr} {Z k len bits : Nat}
 (scratch : Scr s B Z) (room : 256≤Z) (base : s.gpr .x0=B)
 (width : word s.mem B (8*sLen)=BitVec.ofNat 64 k) (ptr : s.gpr .x4=rec)
 (readLen : InRegions (s.rd++s.wr) rec 4) (readBits : InRegions (s.rd++s.wr) (off rec 4) 4)
 (length : s.mem.readW rec 32=BitVec.ofNat 32 len) (policy : s.mem.readW (off rec 4) 32=BitVec.ofNat 32 bits)
 (lenFit : len<2^32) (bitsFit : bits<2^32) :
 WP isa (.block Policy.recordHead) s fun t =>
 (t.gpr .x4=off rec 8 ∧ t.gpr .x6=BitVec.ofNat 64 bits ∧
 t.gpr .x3=BitVec.ofNat 64 k-BitVec.ofNat 64 len ∧ t.mem=s.mem) ∧ Keep [.x3,.x4,.x5,.x6] s t := by
 refine WP.keep [.x3,.x4,.x5,.x6] ?_ rfl rfl rfl
 unfold Policy.recordHead
 brun [exec_ldr_w (off:=0) (by decide),exec_ldr_w (off:=4) (by decide),base,ptr,hdr_enc (show sLen<32 by decide),scratch.ld (d:=8*sLen) (by unfold sLen;omega),
  width,readLen,readBits,length,policy,widen32 lenFit,widen32 bitsFit]

theorem policyRecordTail {s : State} {rec : Addr} {len n : Nat}
 (ptr : s.gpr .x4=off rec 8) (count : s.gpr .x7=BitVec.ofNat 64 n)
 (readLen : InRegions (s.rd++s.wr) rec 4) (length : s.mem.readW rec 32=BitVec.ofNat 32 len)
 (lenFit : len<2^32) (positive : 0<n) :
 WP isa (.block Policy.recordTail) s fun t =>
 (t.gpr .x4=off rec (8+3*len) ∧ t.gpr .x7=BitVec.ofNat 64 (n-1) ∧ t.mem=s.mem) ∧ Keep [.x2,.x3,.x4,.x5,.x7] s t := by
 have back : off rec 8-8#64=rec := by simpa only [off] using BitVec.add_sub_cancel rec 8#64
 have triple : (BitVec.ofNat 64 len <<< 1)+BitVec.ofNat 64 len=BitVec.ofNat 64 (3*len) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add,BitVec.toNat_shiftLeft,BitVec.toNat_ofNat,Nat.shiftLeft_eq]
  omega
 refine WP.keep [.x2,.x3,.x4,.x5,.x7] ?_ rfl rfl rfl
 unfold Policy.recordTail
 brun [exec_ldr_w (off:=0) (by decide),ptr,count,back,readLen,length,widen32 lenFit,triple,
  BitVec.ofNat_sub_ofNat_of_le (w:=64) n 1 (by decide) positive]

end VG.Proof.Ffdh.AArch64.Cached
