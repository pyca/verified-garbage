module

public import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Generate
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Header
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega

/-! The public domain length selects q or p−1 without inspecting a private scalar. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem boundHead_ok {s : State} {B dom : Addr} {Z w k dl : Nat} {mi : BitVec 64}
 (good : Good s B Z w mi) (room : slot w 8≤Z) (size : k<2^31) (shape : dl=2*k ∨ dl=3*k)
 (pointer : word s.mem B (8*sDom)=dom) (length : word s.mem B (8*sLen)=BitVec.ofNat 64 k)
 (domainLength : word s.mem B (8*sDL)=BitVec.ofNat 64 dl) :
 WP isa (.block [ldh .x1 sDom,ldh .x2 sLen,ldh .x3 sDL,.lsl .x .x4 .x2 1,.sub .x .x3 .x3 .x4]) s fun t =>
 (t.gpr .x1=dom ∧ t.gpr .x2=BitVec.ofNat 64 k ∧ t.gpr .x3=BitVec.ofNat 64 (dl-2*k) ∧
 t.gpr .x4=BitVec.ofNat 64 (2*k) ∧ t.mem=s.mem) ∧ Keep [.x1,.x2,.x3,.x4] s t := by
 have shift : BitVec.ofNat 64 k <<< 1=BitVec.ofNat 64 (2*k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft,BitVec.toNat_ofNat,Nat.shiftLeft_eq]
  omega
 have sub : BitVec.ofNat 64 dl-BitVec.ofNat 64 (2*k)=BitVec.ofNat 64 (dl-2*k) :=
  BitVec.ofNat_sub_ofNat_of_le dl (2*k) (by omega) (by omega)
 refine WP.keep [.x1,.x2,.x3,.x4] ?_ rfl rfl rfl
 brun [good.x0,hdr_enc (show sDom<32 by decide),hdr_enc (show sLen<32 by decide),hdr_enc (show sDL<32 by decide),
  header_read good room (show sDom<32 by decide),header_read good room (show sLen<32 by decide),
  header_read good room (show sDL<32 by decide),pointer,length,domainLength,shift,sub]

end VG.Proof.Ffdh.AArch64.Cached
