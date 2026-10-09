import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseHintVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttCallTiming

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (Ptr Arg callAt)
open VG.Proof.MlDsa.Arith (polyRegion)

theorem hintNorm_callee (S : Nat) : CalleeOk S Impl.MlDsa.AArch64.Optimized.Response.hintNorm
    (hintNormContract abi) := ⟨hintNorm_verified.1,hintNorm_verified.2.1,Nat.zero_le _⟩

abbrev hintNormArgs (low ct high : Ptr) (g : Nat) : List (Reg × Arg) :=
  [(.x0,.ptr low),(.x1,.ptr ct),(.x2,.ptr high),(.x3,.imm g)]

structure HintNormReady (low ct high : Ptr) (g : Nat) (s : State) : Prop where
  lowFit : (pa s low).toNat+1024≤2^64
  ctFit : (pa s ct).toNat+1024≤2^64
  highFit : (pa s high).toNat+1024≤2^64
  lowCt : (polyRegion (pa s low)).Disjoint (polyRegion (pa s ct))
  lowHigh : (polyRegion (pa s low)).Disjoint (polyRegion (pa s high))
  gamma : g∈gamma2s
  raw : RawReduced s.mem (pa s ct)
  parts : ResponseDecomposed s.mem (pa s low) (pa s high) g
  readable : Covers [polyRegion (pa s ct),polyRegion (pa s high),polyRegion (pa s low)] (s.rd++s.wr)
  writable : Covers [polyRegion (pa s low)] s.wr

theorem HintNormReady.gamma_lt {low ct high : Ptr} {g : Nat} {s : State}
    (h : HintNormReady low ct high g s) : g<2^32 := by
  have hg := VG.Proof.MlDsa.AArch64.Round.isG_of_mem h.gamma
  rcases hg with rfl|rfl <;> decide

theorem hintNormAt_pre {s s1 : State} {low ct high : Ptr} {g : Nat}
    (h : HintNormReady low ct high g s) (h1 : Args (hintNormArgs low ct high g) s s1) :
    (hintNormContract abi).pre
      (s1.callEntry.withRegions [polyRegion (pa s ct),polyRegion (pa s high)] [polyRegion (pa s low)]) := by
  sig_pre [hintNormContract,hintNormSig,abi,argRegs]
  simp only [Args.r0 h1,Args.r1 h1,Args.r2 h1,Args.r3 h1,Args.mem h1,Arg.val]
  have hg : ((BitVec.ofNat 64 g).setWidth 32).toNat=g := by have := h.gamma_lt; bv_omega
  rw [hg]
  exact ⟨trivial,trivial,h.lowCt,h.lowHigh,h.lowFit,h.ctFit,h.highFit,h.gamma,h.raw,h.parts⟩

theorem hintNormArgs_ok {low ct high : Ptr} {g : Nat}
    (hl : (Arg.ptr low).Ok) (hc : (Arg.ptr ct).Ok) (hh : (Arg.ptr high).Ok) :
    ∀x∈hintNormArgs low ct high g,x.2.Ok ∧ x.1∈argRegs := by
  simp only [hintNormArgs,List.mem_cons,List.not_mem_nil,or_false]
  intro x hx
  rcases hx with rfl|rfl|rfl|rfl
  · exact ⟨hl,by simp⟩
  · exact ⟨hc,by simp⟩
  · exact ⟨hh,by simp⟩
  · exact ⟨trivial,by simp⟩

def HintNormPost (g : Nat) (m m' : Mem) (low ct high : Addr) (r : BitVec 64) : Prop :=
  HintIs m' low 1 [responseHintPoly m low ct high g] ∧
  r=BitVec.ofNat 64 (hintOnes [responseHintPoly m low ct high g]+
    if normRq [signedPolyAt m ct]<g then 4294967296 else 0)

theorem hintNormAt_ok {S : Nat} (hS : S<2^64) {nm : String} {s : State} {low ct high : Ptr} {g : Nat}
    (hl : (Arg.ptr low).Ok) (hc : (Arg.ptr ct).Ok) (hh : (Arg.ptr high).Ok)
    (h : HintNormReady low ct high g s) :
    WP isa (callAt nm Impl.MlDsa.AArch64.Optimized.Response.hintNorm (hintNormArgs low ct high g)) s fun t =>
      Post S s t [polyRegion (pa s low)] ∧ HintNormPost g s.mem t.mem (pa s low) (pa s ct) (pa s high) (t.gpr .x0) := by
  refine WP.mono (callAtSyms_ok hS (hintNorm_callee S) (hintNormArgs_ok hl hc hh) (by simp)
    (fun s1 h1 _=>hintNormAt_pre h h1) h.readable h.writable) fun t ⟨hP,s1,h1,hq⟩ => ?_
  sig_post [hintNormContract,hintNormSig,abi,argRegs] at hq
  rw [Args.r0 h1,Args.r1 h1,Args.r2 h1,Args.r3 h1,Args.mem h1] at hq
  have hg : ((BitVec.ofNat 64 g).setWidth 32).toNat=g := by have := h.gamma_lt; bv_omega
  simpa only [HintNormPost,Arg.val,hg] using And.intro hP hq

end VG.Proof.MlDsa.AArch64.Optimized.Response
