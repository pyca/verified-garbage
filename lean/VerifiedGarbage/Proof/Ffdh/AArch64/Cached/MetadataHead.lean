module

public import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Policy
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Header
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega

/-! Public scalar width metadata is computed without assuming initialized arithmetic arrays. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem metadataHead_ok {s : State} {B : Addr} {Z N : Nat}
 (scratch : Scr s B Z) (room : 256≤Z) (base : s.gpr .x0=B) (bound : N≤8192)
 (bits : word s.mem B (8*sBits)=BitVec.ofNat 64 N) :
 WP isa (.block Policy.metadataHead) s fun t =>
 (t.gpr .x10=BitVec.ofNat 64 N ∧ t.gpr .x11=BitVec.ofNat 64 ((N+7)/8) ∧
 t.gpr .x12=BitVec.ofNat 64 (N+4) ∧ t.gpr .x13=0#64 ∧
 t.mem=s.mem.writeW (off B (8*sBytes)) (BitVec.ofNat 64 ((N+7)/8))) ∧
 Keep [.x10,.x11,.x12,.x13] s t := by
 have shift : (BitVec.ofNat 64 N+7#64) >>> 3=BitVec.ofNat 64 ((N+7)/8) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight,BitVec.toNat_add,BitVec.toNat_ofNat,Nat.shiftRight_eq_div_pow]
  omega
 refine WP.keep [.x10,.x11,.x12,.x13] ?_ rfl rfl rfl
 unfold Policy.metadataHead
 brun [base,hdr_enc (show sBits<32 by decide),hdr_enc (show sBytes<32 by decide),
  scratch.ld (d:=8*sBits) (by unfold sBits;omega),scratch.st (d:=8*sBytes) (by unfold sBytes;omega),bits,shift]
 exact (BitVec.ofNat_add _ _).symm

end VG.Proof.Ffdh.AArch64.Cached
