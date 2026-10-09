import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttCallTiming

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (Ptr Arg callAt)

theorem sampler_callee (S : Nat) (sha3 : Bool) {η : Nat} (hη : η=2∨η=4) :
    CalleeOk S (Impl.MlDsa.AArch64.Optimized.BoundedFour.sampler sha3 true η)
      (rejBoundedFourContract abi η) :=
by
  refine ⟨(sampler_verified sha3 hη).1,(sampler_verified sha3 hη).2.1,?_⟩
  have hd : (Impl.MlDsa.AArch64.Optimized.BoundedFour.sampler sha3 true η).aarch64Depth=0 := by
    rcases hη with rfl|rfl <;> cases sha3 <;> decide
  rw [hd]
  exact Nat.zero_le _

abbrev samplerArgs (seed out work : Ptr) : List (Reg × Arg) :=
 [(.x0,.ptr seed),(.x1,.ptr out),(.x2,.ptr work)]

structure CallReady (seed out work : Ptr) (s : State) : Prop where
 seedFit : (pa s seed).toNat+264≤2^64
 outFit : (pa s out).toNat+4096≤2^64
 workFit : (pa s work).toNat+8192≤2^64
 seedOut : (⟨pa s seed,264⟩ : Region).Disjoint ⟨pa s out,4096⟩
 seedWork : (⟨pa s seed,264⟩ : Region).Disjoint ⟨pa s work,8192⟩
 outWork : (⟨pa s out,4096⟩ : Region).Disjoint ⟨pa s work,8192⟩
 readable : Covers [⟨pa s seed,264⟩,⟨pa s out,4096⟩,⟨pa s work,8192⟩] (s.rd++s.wr)
 writable : Covers [⟨pa s out,4096⟩,⟨pa s work,8192⟩] s.wr

theorem samplerAt_pre {η : Nat} (hη : η=2∨η=4) {s s1 : State} {seed out work : Ptr}
    (h : CallReady seed out work s) (h1 : Args (samplerArgs seed out work) s s1) :
    (rejBoundedFourContract abi η).pre
      (s1.callEntry.withRegions [⟨pa s seed,264⟩] [⟨pa s out,4096⟩,⟨pa s work,8192⟩]) := by
  sig_pre [rejBoundedFourContract,rejBoundedFourSig,abi,argRegs]
  simp only [Args.r0 h1,Args.r1 h1,Args.r2 h1,Arg.val]
  exact ⟨trivial,trivial,h.seedOut,h.seedWork,h.outWork,h.seedFit,h.outFit,h.workFit,hη⟩

theorem samplerArgs_ok {seed out work : Ptr}
    (hs : (Arg.ptr seed).Ok) (ho : (Arg.ptr out).Ok) (hw : (Arg.ptr work).Ok) :
    ∀x∈samplerArgs seed out work,x.2.Ok ∧ x.1∈argRegs := by
  simp only [samplerArgs,List.mem_cons,List.not_mem_nil,or_false]
  intro x hx
  rcases hx with rfl|rfl|rfl
  · exact ⟨hs,by simp⟩
  · exact ⟨ho,by simp⟩
  · exact ⟨hw,by simp⟩

theorem samplerAt_ok {S : Nat} (hS : S<2^64) (sha3 : Bool) {η : Nat} (hη : η=2∨η=4)
    {nm : String} {s : State} {seed out work : Ptr}
    (hs : (Arg.ptr seed).Ok) (ho : (Arg.ptr out).Ok) (hw : (Arg.ptr work).Ok)
    (h : CallReady seed out work s) :
    WP isa (callAt nm (Impl.MlDsa.AArch64.Optimized.BoundedFour.sampler sha3 true η)
      (samplerArgs seed out work)) s fun t=>
      Post S s t [⟨pa s out,4096⟩,⟨pa s work,8192⟩] ∧
      (∀i<4,Reduced t.mem (pa s out+BitVec.ofNat 64 (1024*i))) ∧
      (∀i<4,BoundedOutput η t.mem (pa s out+BitVec.ofNat 64 (1024*i))) ∧
      Outcome (fun b=>(rejBoundedFour η b.rejBounded s.mem (pa s seed)).map (List.map toRq))
        ((t.gpr .x0).setWidth 32)
        ((List.range 4).map fun i=>polyAt t.mem (pa s out+BitVec.ofNat 64 (1024*i))) := by
  refine WP.mono (callAtSyms_ok hS (sampler_callee S sha3 hη) (samplerArgs_ok hs ho hw) (by simp)
    (fun s1 h1 _=>samplerAt_pre hη h h1) h.readable h.writable) fun t ⟨hP,s1,h1,hq⟩=>?_
  sig_post [rejBoundedFourContract,rejBoundedFourSig,abi,argRegs] at hq
  rw [Args.r0 h1,Args.r1 h1,Args.mem h1] at hq
  exact ⟨hP,hq⟩

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
