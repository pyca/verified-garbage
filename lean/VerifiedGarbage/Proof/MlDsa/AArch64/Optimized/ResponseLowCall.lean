import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseLowVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttCallTiming

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (Ptr Arg callAt)
open VG.Proof.MlDsa.Arith (polyRegion)

theorem subLowNorm_callee (S : Nat) : CalleeOk S VG.Impl.MlDsa.AArch64.Optimized.Response.subLowNorm
    (subLowNormContract abi) := ⟨subLowNorm_verified.1,subLowNorm_verified.2.1,Nat.zero_le _⟩

abbrev subLowNormArgs (w cs low : Ptr) (g B : Nat) : List (Reg × Arg) :=
  [(.x0,.ptr w),(.x1,.ptr cs),(.x2,.ptr low),(.x3,.imm g),(.x4,.imm B)]

structure SubLowNormReady (w cs low : Ptr) (g B : Nat) (s : State) : Prop where
  wFit : (pa s w).toNat+1024≤2^64
  csFit : (pa s cs).toNat+1024≤2^64
  lowFit : (pa s low).toNat+1024≤2^64
  wCs : (polyRegion (pa s w)).Disjoint (polyRegion (pa s cs))
  wLow : (polyRegion (pa s w)).Disjoint (polyRegion (pa s low))
  csLow : (polyRegion (pa s cs)).Disjoint (polyRegion (pa s low))
  canonical : Reduced s.mem (pa s w)
  raw : RawReduced s.mem (pa s cs)
  gamma : g∈gamma2s
  boundPos : 1≤B
  boundMax : B≤524288
  readable : Covers [polyRegion (pa s cs),polyRegion (pa s w),polyRegion (pa s low)] (s.rd++s.wr)
  writable : Covers [polyRegion (pa s w),polyRegion (pa s low)] s.wr

theorem SubLowNormReady.gamma_lt {w cs low : Ptr} {g B : Nat} {s : State}
    (h : SubLowNormReady w cs low g B s) : g<2^32 := by
  have hg := VG.Proof.MlDsa.AArch64.Round.isG_of_mem h.gamma
  rcases hg with rfl|rfl <;> decide

theorem subLowNormAt_pre {s s1 : State} {w cs low : Ptr} {g B : Nat}
    (h : SubLowNormReady w cs low g B s) (h1 : Args (subLowNormArgs w cs low g B) s s1) :
    (subLowNormContract abi).pre
      (s1.callEntry.withRegions [polyRegion (pa s cs)] [polyRegion (pa s w),polyRegion (pa s low)]) := by
  sig_pre [subLowNormContract,subLowNormSig,abi,argRegs]
  simp only [Args.r0 h1,Args.r1 h1,Args.r2 h1,Args.r3 h1,Args.r4 h1,Args.mem h1,Arg.val]
  have hg : ((BitVec.ofNat 64 g).setWidth 32).toNat=g := by have := h.gamma_lt; bv_omega
  have hB : ((BitVec.ofNat 64 B).setWidth 32).toNat=B := by have := h.boundMax; bv_omega
  rw [hg,hB]
  exact ⟨trivial,trivial,h.wCs,h.wLow,h.csLow,h.wFit,h.csFit,h.lowFit,h.canonical,h.raw,h.gamma,h.boundPos,h.boundMax⟩

theorem subLowNormArgs_ok {w cs low : Ptr} {g B : Nat}
    (hw : (Arg.ptr w).Ok) (hc : (Arg.ptr cs).Ok) (hl : (Arg.ptr low).Ok) :
    ∀x∈subLowNormArgs w cs low g B,x.2.Ok ∧ x.1∈argRegs := by
  simp only [subLowNormArgs,List.mem_cons,List.not_mem_nil,or_false]
  intro x hx
  rcases hx with rfl|rfl|rfl|rfl|rfl
  · exact ⟨hw,by simp⟩
  · exact ⟨hc,by simp⟩
  · exact ⟨hl,by simp⟩
  · exact ⟨trivial,by simp⟩
  · exact ⟨trivial,by simp⟩

def SubLowNormPost (g B : Nat) (m m' : Mem) (w cs low : Addr) (r : BitVec 32) : Prop :=
  (∀i<n,(coeffAt m' w i).toNat=(highBits g (responseDifference m w cs i)).toNat) ∧
  (∀i<n,(coeffAt m' low i).toInt=lowBits g (responseDifference m w cs i)) ∧
  r=if responseLowPass m w cs g B then 1 else 0

theorem subLowNormAt_ok {S : Nat} (hS : S<2^64) {nm : String} {s : State} {w cs low : Ptr} {g B : Nat}
    (hw : (Arg.ptr w).Ok) (hc : (Arg.ptr cs).Ok) (hl : (Arg.ptr low).Ok)
    (h : SubLowNormReady w cs low g B s) :
    WP isa (callAt nm VG.Impl.MlDsa.AArch64.Optimized.Response.subLowNorm (subLowNormArgs w cs low g B)) s fun t =>
      Post S s t [polyRegion (pa s w),polyRegion (pa s low)] ∧
      SubLowNormPost g B s.mem t.mem (pa s w) (pa s cs) (pa s low) ((t.gpr .x0).setWidth 32) := by
  refine WP.mono (callAtSyms_ok hS (subLowNorm_callee S)
    (subLowNormArgs_ok hw hc hl) (by simp)
    (fun s1 h1 _=>subLowNormAt_pre h h1) h.readable h.writable) fun t ⟨hP,s1,h1,hq⟩ => ?_
  sig_post [subLowNormContract,subLowNormSig,abi,argRegs] at hq
  rw [Args.r0 h1,Args.r1 h1,Args.r2 h1,Args.r3 h1,Args.r4 h1,Args.mem h1] at hq
  have hg : ((BitVec.ofNat 64 g).setWidth 32).toNat=g := by have := h.gamma_lt; bv_omega
  have hB : ((BitVec.ofNat 64 B).setWidth 32).toNat=B := by have := h.boundMax; bv_omega
  simpa only [SubLowNormPost,Arg.val,hg,hB] using And.intro hP hq

end VG.Proof.MlDsa.AArch64.Optimized.Response
