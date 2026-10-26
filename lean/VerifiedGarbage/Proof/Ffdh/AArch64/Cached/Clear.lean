module

public import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Generate
public import VerifiedGarbage.Proof.Bignum.AArch64.PubFail
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Header
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Tactic.SplitIfs

/-! Rejected attempts clear every byte through the existing verified zero-byte loop. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem clear_ok {s : State} {B out : Addr} {Z k i : Nat}
 (scratch : Scr s B Z) (room : 256≤Z) (base : s.gpr .x0=B) (positive : 0<k) (size : k<2^31)
 (index : i<32) (pointer : word s.mem B (8*i)=out) (length : word s.mem B (8*sLen)=BitVec.ofNat 64 k)
 (writable : ∀ j<k,InRegions s.wr (out+BitVec.ofNat 64 j) 1) :
 WP isa (Generate.clear i) s fun t =>
 Spec.Rsa.bytesAt t.mem out k=List.replicate k 0 ∧ Outside out 0 k s.mem t.mem ∧ Keep [.x1,.x2,.x3] s t := by
 unfold Generate.clear
 rw [WP.seq_iff]
 refine WP.mono (WP.keep [.x1,.x2,.x3] (Q:=fun a =>a.gpr .x1=out ∧ a.gpr .x2=BitVec.ofNat 64 k ∧ a.gpr .x3=0#64 ∧ a.mem=s.mem)
  ?_ rfl rfl rfl) ?_
 · brun [base,hdr_enc index,hdr_enc (show sLen<32 by decide),pointer,length,
    scratch.ld (d:=8*i) (by omega),scratch.ld (d:=8*sLen) (by unfold sLen;omega)]
 · rintro a ⟨⟨ptrA,countA,zeroA,memA⟩,restA⟩
   refine WP.mono (wp_countdown (N:=k) (by omega) (by omega) (BInv a out)
    (fun j hj t inv _ =>bStep_ok (by omega) zeroA (fun i hi =>by rw [restA.wr];exact writable i hi) hj inv)
    ⟨Keep.refl _ _,by simpa only [show BitVec.ofNat 64 0=0#64 from rfl,BitVec.add_zero] using ptrA,fun _ h =>by omega,fun _ _ =>rfl⟩ countA) ?_
   intro t inv
   refine ⟨?_,?_,(restA.trans inv.keep).mono (by simp)⟩
   · apply List.ext_getElem
     · simp only [Spec.Rsa.bytesAt,List.length_map,List.length_range,List.length_replicate]
     · intro j hj _
       have bound : j<k := by simpa only [Spec.Rsa.bytesAt,List.length_map,List.length_range] using hj
       simp only [Spec.Rsa.bytesAt,List.getElem_map,List.getElem_range,List.getElem_replicate]
       exact inv.bytes j bound
   · intro x hx
     rw [inv.frame x ?_,memA]
     intro j hj eq
     subst x
     rw [show ofs out (out+BitVec.ofNat 64 j)=j from Mem.sub_ofNat_toNat _ (by omega)] at hx
     omega

end VG.Proof.Ffdh.AArch64.Cached
