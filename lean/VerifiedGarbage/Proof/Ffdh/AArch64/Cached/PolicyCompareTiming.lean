module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PolicyCompareArgs
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.TCB.AArch64.Isa
meta import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Policy
meta import VerifiedGarbage.Impl.Bignum.AArch64.Core
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore

/-! Exact public-domain comparisons always scan their complete public length. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

structure ComparePublic where
 B : Addr
 Z : Nat
 src : Addr
 dst : Addr
 bs : List Byte
 cs : List Byte
 room : 256≤Z
 same : bs.length=cs.length
 positive : 0<bs.length
 size : bs.length<2^31

structure PolicyCompareReady (q : ComparePublic) (s : State) : Prop where
 scratch : Scr s q.B q.Z
 base : s.gpr .x0=q.B
 domain : word s.mem q.B (8*sDom)=q.src
 length : word s.mem q.B (8*sDL)=BitVec.ofNat 64 q.bs.length
 pointer : s.gpr .x4=q.dst
 first : Source q.src q.bs s
 second : Source q.dst q.cs s

theorem policyCompare_ct : RelCT isa (Two PolicyCompareReady) Policy.compare (fun _ _ =>True) := by
 unfold Policy.compare
 refine RelCT.seq (two_piece (Ψ:=fun q s =>s.gpr .x1=q.src ∧ s.gpr .x2=q.dst ∧ s.gpr .x5=BitVec.ofNat 64 q.bs.length)
  [.x0,.x4] (fun q s t hs ht r hr =>by
   simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
   rcases hr with rfl|rfl
   · exact hs.base.trans ht.base.symm
   · exact hs.pointer.trans ht.pointer.symm) (by taint_decide) ?_)
  (two_taint [.x1,.x2,.x5] (fun q s t hs ht r hr =>by
   simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
   rcases hr with rfl|rfl|rfl
   · exact hs.1.trans ht.1.symm
   · exact hs.2.1.trans ht.2.1.symm
   · exact hs.2.2.trans ht.2.2.symm) (by taint_decide))
 intro q s h
 brun [h.base,h.pointer,hdr_enc (show sDom<32 by decide),hdr_enc (show sDL<32 by decide),
  h.scratch.ld (d:=8*sDom) (by have :=q.room;unfold sDom;omega),
  h.scratch.ld (d:=8*sDL) (by have :=q.room;unfold sDL;omega),h.domain,h.length]

theorem policyCompare_agree {q : ComparePublic} {s : State} (h : PolicyCompareReady q s) :
 WP isa Policy.compare s fun t =>
 s.gpr .x0=t.gpr .x0 ∧ isa.eval (.zero .x .x11) t=some (decide (q.bs=q.cs)) := by
 refine WP.mono (policyCompare_ok h.scratch q.room h.base h.domain h.length h.pointer h.first h.second q.same q.positive q.size) ?_
 rintro t ⟨equal,_,rest⟩
 refine ⟨(rest.gpr .x0 (by simp [compareClobbers])).symm,?_⟩
 rw [VG.Proof.MlKem.AArch64.eval_zero]
 change some (t.gpr .x11==0#64)=_
 apply congrArg some
 apply Bool.eq_iff_iff.mpr
 simpa only [beq_iff_eq,decide_eq_true_eq] using equal

end VG.Proof.Ffdh.AArch64.Cached
