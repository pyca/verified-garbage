module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PolicyScan
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.TCB.AArch64.Isa
meta import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Policy
meta import VerifiedGarbage.Impl.Bignum.AArch64.Core
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore

/-! Leading-zero scanning depends only on the complete public bound encoding. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (eval_zero)

structure PolicyScanPublic where
 src : Addr
 bs : List Byte
 L : Nat
 size : bs.length<2^31
 inside : L<bs.length
 zeros : ∀ i<L,bs.getD i 0=0#8
 nonzero : bs.getD L 0≠0#8

structure PolicyScanReady (q : PolicyScanPublic) (i : Nat) (s : State) : Prop where
 source : Source q.src q.bs s
 pointer : s.gpr .x1=off q.src i
 remaining : s.gpr .x2=BitVec.ofNat 64 (q.bs.length-i)

private theorem publicByteZero : ∀ b : Byte,
 (BitVec.ofNat 64 b.toNat==0#64)=decide (b=0#8) := by decide +kernel

theorem policyScan_ct : RelCT isa (Two fun q s =>PolicyScanReady q 0 s)
 (.loop (.block Policy.scanStep) (.zero .x .x3)) (fun _ _ =>True) := by
 have stepCt : RelCT isa (Two fun (q : PolicyScanPublic × Nat) s =>q.2<q.1.L+1 ∧ PolicyScanReady q.1 q.2 s)
  (.block Policy.scanStep) (fun _ _ =>True) :=
  two_taint [.x1] (fun q s t hs ht r hr =>by
   have eq : r= .x1 := by simpa using hr
   subst r;exact hs.2.pointer.trans ht.2.pointer.symm) (by taint_decide)
 have loop:=two_loop (cond:= .zero .x .x3) (Φ:=PolicyScanReady) (Ψ:=fun _ _ =>True)
  (fun q =>q.L+1) stepCt (by
   intro q i s hi h
   refine WP.mono (policyScanStep h.source q.size (by have :=q.inside;omega) h.pointer h.remaining) ?_
   rintro t ⟨⟨ptr,count,byte,mem⟩,rest⟩
   refine ⟨?_,fun _ =>⟨h.source.of_mem mem rest,ptr,count⟩,fun _ =>trivial⟩
   rw [eval_zero,byte]
   change some (BitVec.ofNat 64 (q.bs.getD i 0).toNat==0#64)=_
   rw [publicByteZero]
   by_cases more : i<q.L
   · rw [q.zeros i more,decide_eq_true (show i+1<q.L+1 by omega)]
     rfl
   · have last : i=q.L :=by omega
     rw [last,decide_eq_false q.nonzero,decide_eq_false (show ¬q.L+1<q.L+1 by omega)])
 exact loop.mono (fun _ _ ⟨q,hs,ht,sp⟩ =>⟨q,⟨by have :=q.inside;omega,hs⟩,⟨by have :=q.inside;omega,ht⟩,sp⟩)
  (fun _ _ _ =>trivial)

end VG.Proof.Ffdh.AArch64.Cached
