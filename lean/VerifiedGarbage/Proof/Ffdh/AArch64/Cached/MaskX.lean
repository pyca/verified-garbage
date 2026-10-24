module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.MaskOutputLoop
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Header
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega

/-! Mask the private output according to the final 0/1 public-result predicate. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem maskX_ok {s : State} {B out : Addr} {Z k : Nat} {c : Bool}
 (scratch : Scr s B Z) (room : 256≤Z) (base : s.gpr .x0=B) (positive : 0<k) (size : k<2^31)
 (pointer : word s.mem B (8*sX)=out) (length : word s.mem B (8*sLen)=BitVec.ofNat 64 k)
 (flag : word s.mem B (8*sTmp)=BitVec.ofNat 64 c.toNat)
 (writable : ∀ i<k,InRegions s.wr (out+BitVec.ofNat 64 i) 1)
 (outside : ∀ i<k,Z≤ofs B (out+BitVec.ofNat 64 i)) :
 WP isa Generate.maskX s fun t =>
 Spec.Rsa.bytesAt t.mem out k=(if c then Spec.Rsa.bytesAt s.mem out k else List.replicate k 0) ∧
 t.gpr .x15=mask c ∧ Outside out 0 k s.mem t.mem ∧
 (∀ q,ofs B q<Z→t.mem q=s.mem q) ∧ Keep [.x1,.x2,.x3,.x7,.x15] s t := by
 have neg : (0#64 : Addr)-BitVec.ofNat 64 c.toNat=mask c := by cases c <;>rfl
 unfold Generate.maskX
 rw [WP.seq_iff]
 refine WP.mono (WP.keep [.x1,.x2,.x3,.x7,.x15] (Q:=fun a =>a.gpr .x1=out ∧
  a.gpr .x2=BitVec.ofNat 64 k ∧ a.gpr .x15=mask c ∧ a.mem=s.mem) ?_ rfl rfl rfl) ?_
 · brun [base,hdr_enc (show sX<32 by decide),hdr_enc (show sLen<32 by decide),hdr_enc (show sTmp<32 by decide),
    scratch.ld (d:=8*sX) (by unfold sX;omega),scratch.ld (d:=8*sLen) (by unfold sLen;omega),
    scratch.ld (d:=8*sTmp) (by unfold sTmp;omega),pointer,length,flag,neg]
   exact neg
 · rintro a ⟨⟨ptrA,countA,maskA,memA⟩,restA⟩
   refine WP.mono (maskOutputLoop_ok positive size ptrA countA maskA
    (fun i hi =>by rw [restA.wr];exact writable i hi)) ?_
   rintro t ⟨bytes,frame,rest⟩
   have fullFrame : Outside out 0 k s.mem t.mem := by rw [←memA];exact frame
   refine ⟨by rw [memA] at bytes;exact bytes,(rest.gpr .x15 (by decide)).trans maskA,fullFrame,?_,
    (restA.trans rest).mono (by simp)⟩
   intro q hq
   exact fullFrame q (Or.inr (by have sep : k≤ofs out q :=le_ofs_of_sep outside hq;omega))

end VG.Proof.Ffdh.AArch64.Cached
