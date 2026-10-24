module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SelectTiming
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.TCB.AArch64.Isa
meta import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Comb
meta import VerifiedGarbage.Impl.Bignum.AArch64.Core
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore

/-! The complete 32-entry scan has a public fixed schedule, independently of its digit. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (eval_nonzero)

structure ScanPublic where
 B : Addr
 table : Addr
 dst : Addr
 w : Nat
 positive : 0<w
 fit : 8*w≤2^64

structure ScanReady (p : ScanPublic) (j : Nat) (s : State) : Prop where
 env : SelectEnv p.B p.table p.dst p.w s
 pointer : s.gpr .x9=off p.table (8*p.w*j)
 candidate : s.gpr .x11=BitVec.ofNat 64 j
 digit : ∃ v, v<32 ∧ s.gpr .x10=BitVec.ofNat 64 v

theorem scanStep_ct :
 RelCT isa (Two fun (q : ScanPublic × Nat) s => q.2<32 ∧ ScanReady q.1 q.2 s)
 Comb.selectStep (fun _ _ => True) := by
 unfold Comb.selectStep
 refine RelCT.seq (two_post (Ψ:=fun (q : ScanPublic × Nat) s =>
  s.gpr .x9=off q.1.table (8*q.1.w*q.2) ∧ s.gpr .x8=q.1.dst ∧
  s.gpr .x12=BitVec.ofNat 64 q.1.w ∧ s.gpr .x11=BitVec.ofNat 64 q.2)
  (two_map (fun q => q.1.B) (fun _ _ h => h.2.env.base) selectHead_ct) ?_)
  (two_taint [.x9,.x8,.x12,.x11] ?_ (by taint_decide))
 · rintro ⟨p,j⟩ s ⟨hj,h⟩
   obtain ⟨v,hv,digit⟩ := h.digit
   refine WP.mono (selectHead_ok h.env hv hj digit h.candidate) ?_
   rintro t ⟨⟨dst,count,_,_⟩,rest⟩
   exact ⟨(rest.gpr .x9 (by decide)).trans h.pointer,dst,count,
    (rest.gpr .x11 (by decide)).trans h.candidate⟩
 · intro q s t hs ht r hr
   simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
   rcases hr with rfl | rfl | rfl | rfl
   · exact hs.1.trans ht.1.symm
   · exact hs.2.1.trans ht.2.1.symm
   · exact hs.2.2.1.trans ht.2.2.1.symm
   · exact hs.2.2.2.trans ht.2.2.2.symm

private theorem scanCounter : ∀ j<32,
 (BitVec.ofNat 64 (j+1)-32#64 != 0#64)=decide (j+1<32) := by decide +kernel

theorem scan_ct : RelCT isa (Two fun p s => ScanReady p 0 s)
 (.loop Comb.selectStep (.nonzero .x .x3)) (fun _ _ => True) := by
 have loop := two_loop (Φ:=ScanReady) (Ψ:=fun _ _ => True) (fun _ : ScanPublic => 32)
  scanStep_ct (by
   intro p j s hj h
   obtain ⟨v,hv,digit⟩ := h.digit
   refine WP.mono (selectStep_ok h.env p.positive p.fit hv hj digit h.candidate h.pointer) ?_
   rintro t ⟨env,_,_,pointer,digit,candidate,counter,_⟩
   refine ⟨?_,fun _ => ⟨env,pointer,candidate,v,hv,digit⟩,fun _ => trivial⟩
   rw [eval_nonzero,counter]
   exact congrArg some (scanCounter j hj))
 exact loop.mono (fun _ _ ⟨p,hs,ht,sp⟩ => ⟨p,⟨by decide,hs⟩,⟨by decide,ht⟩,sp⟩)
  (fun _ _ _ => trivial)

end VG.Proof.Ffdh.AArch64.Cached
