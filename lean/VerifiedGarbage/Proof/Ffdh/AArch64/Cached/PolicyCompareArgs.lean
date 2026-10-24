module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PolicyCompare
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Header
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega

/-! Bind the complete byte-comparison loop to the public domain header. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem policyCompare_ok {s : State} {B src dst : Addr} {Z : Nat} {bs cs : List Byte}
 (scratch : Scr s B Z) (room : 256≤Z) (base : s.gpr .x0=B)
 (pointer : word s.mem B (8*sDom)=src) (length : word s.mem B (8*sDL)=BitVec.ofNat 64 bs.length)
 (record : s.gpr .x4=dst) (first : Source src bs s) (second : Source dst cs s)
 (same : bs.length=cs.length) (positive : 0<bs.length) (size : bs.length<2^31) :
 WP isa Policy.compare s fun t => (t.gpr .x11=0#64 ↔ bs=cs) ∧
 t.mem=s.mem ∧ Keep compareClobbers s t := by
 unfold Policy.compare
 rw [WP.seq_iff]
 refine WP.mono (WP.keep [.x1,.x2,.x5,.x11] (Q:=fun u =>
  u.gpr .x1=src ∧ u.gpr .x2=dst ∧ u.gpr .x5=BitVec.ofNat 64 bs.length ∧ u.gpr .x11=0#64 ∧ u.mem=s.mem)
  ?_ rfl rfl rfl) ?_
 · brun [base,hdr_enc (show sDom<32 by decide),hdr_enc (show sDL<32 by decide),
   scratch.ld (d:=8*sDom) (by unfold sDom;omega),scratch.ld (d:=8*sDL) (by unfold sDL;omega),pointer,length,record]
 · rintro u ⟨⟨ptr1,ptr2,count,zero,mem⟩,rest⟩
   refine WP.mono (policyCompareLoop_ok u (first.of_mem mem rest) (second.of_mem mem rest)
    same positive size ptr1 ptr2 count zero) ?_
   rintro t ⟨equal,memT,restT⟩
   exact ⟨equal,memT.trans mem,(rest.trans restT).mono (by simp [compareClobbers])⟩

end VG.Proof.Ffdh.AArch64.Cached
