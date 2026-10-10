import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseZVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttCallTiming

/-! ## From `ResponseZCall.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (Ptr Arg callAt)
open VG.Proof.MlDsa.Arith (polyRegion)

theorem addNorm_callee (S : Nat) : CalleeOk S VG.Impl.MlDsa.AArch64.Optimized.Response.addNorm
    (addNormContract abi) := ⟨addNorm_verified.1,addNorm_verified.2.1,Nat.zero_le _⟩

abbrev addNormArgs (y cs : Ptr) (B : Nat) : List (Reg × Arg) :=
  [(.x0,.ptr y),(.x1,.ptr cs),(.x2,.imm B)]

structure AddNormReady (y cs : Ptr) (B : Nat) (s : State) : Prop where
  yFit : (pa s y).toNat+1024≤2^64
  csFit : (pa s cs).toNat+1024≤2^64
  apart : (polyRegion (pa s y)).Disjoint (polyRegion (pa s cs))
  canonical : Reduced s.mem (pa s y)
  raw : RawReduced s.mem (pa s cs)
  boundPos : 1≤B
  boundMax : B≤524288
  readable : Covers [polyRegion (pa s cs),polyRegion (pa s y)] (s.rd++s.wr)
  writable : Covers [polyRegion (pa s y)] s.wr

theorem addNormAt_pre {s s1 : State} {y cs : Ptr} {B : Nat}
    (h : AddNormReady y cs B s) (h1 : Args (addNormArgs y cs B) s s1) :
    (addNormContract abi).pre
      (s1.callEntry.withRegions [polyRegion (pa s cs)] [polyRegion (pa s y)]) := by
  sig_pre [addNormContract,addNormSig,abi,argRegs]
  simp only [Args.r0 h1,Args.r1 h1,Args.r2 h1,Args.mem h1,Arg.val]
  have hB : ((BitVec.ofNat 64 B).setWidth 32).toNat=B := by have := h.boundMax; bv_omega
  rw [hB]
  exact ⟨trivial,trivial,h.apart,h.yFit,h.csFit,h.canonical,h.raw,h.boundPos,h.boundMax⟩

theorem addNormArgs_ok {y cs : Ptr} {B : Nat}
    (hy : (Arg.ptr y).Ok) (hc : (Arg.ptr cs).Ok) :
    ∀x∈addNormArgs y cs B,x.2.Ok ∧ x.1∈argRegs := by
  simp only [addNormArgs,List.mem_cons,List.not_mem_nil,or_false]
  intro x hx
  rcases hx with rfl|rfl|rfl
  · exact ⟨hy,by simp⟩
  · exact ⟨hc,by simp⟩
  · exact ⟨trivial,by simp⟩

theorem addNormAt_ok {S : Nat} (hS : S<2^64) {nm : String} {s : State} {y cs : Ptr} {B : Nat}
    (hy : (Arg.ptr y).Ok) (hc : (Arg.ptr cs).Ok) (h : AddNormReady y cs B s) :
    WP isa (callAt nm VG.Impl.MlDsa.AArch64.Optimized.Response.addNorm (addNormArgs y cs B)) s fun t =>
      Post S s t [polyRegion (pa s y)] ∧ CenteredReduced t.mem (pa s y) ∧
      signedPolyAt t.mem (pa s y)=add (polyAt s.mem (pa s y)) (signedPolyAt s.mem (pa s cs)) ∧
      (t.gpr .x0).setWidth 32=if normRq [add (polyAt s.mem (pa s y)) (signedPolyAt s.mem (pa s cs))]<B then 1 else 0 := by
  refine WP.mono (callAtSyms_ok hS (addNorm_callee S) (addNormArgs_ok hy hc) (by simp)
    (fun s1 h1 _=>addNormAt_pre h h1) h.readable h.writable) fun t ⟨hP,s1,h1,hq⟩ => ?_
  sig_post [addNormContract,addNormSig,abi,argRegs] at hq
  rw [Args.r0 h1,Args.r1 h1,Args.r2 h1,Args.mem h1] at hq
  have hB : ((BitVec.ofNat 64 B).setWidth 32).toNat=B := by have := h.boundMax; bv_omega
  simpa only [Arg.val,hB] using And.intro hP hq

end VG.Proof.MlDsa.AArch64.Optimized.Response

end

/-! ## From `ResponseZCallTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (Ptr Arg callAt)
open VG.Proof.MlDsa.Arith (polyRegion)

theorem addNormAt_tr {S : Nat} {nm : String} {y cs : Ptr} {B : Nat}
    (hy : (Arg.ptr y).Ok) (hc : (Arg.ptr cs).Ok)
    {Q : State → State → Prop}
    (hQ : ∀x z,Q x z → AddNormReady y cs B x ∧ AddNormReady y cs B z ∧
      pa x y=pa z y ∧ pa x cs=pa z cs ∧ x.sp=z.sp) :
    RelCT isa Q (callAt nm VG.Impl.MlDsa.AArch64.Optimized.Response.addNorm
      (addNormArgs y cs B)) fun _ _=>True := by
  refine callAtSyms_tr (addNorm_callee S) (addNormArgs_ok hy hc) (by simp)
    fun x z x1 z1 hp h1 h2 _ _ => ?_
  obtain ⟨rx,rz,ey,ec,esp⟩ := hQ x z hp
  refine ⟨[polyRegion (pa x cs)],[polyRegion (pa x y)],addNormAt_pre rx h1,?_,?_,rx.readable,rx.writable,?_,?_⟩
  · rw [ey,ec]; exact addNormAt_pre rz h2
  · sig_pub [addNormContract,addNormSig,abi,argRegs]
    rw [Args.r0 h1,Args.r0 h2,Args.r1 h1,Args.r1 h2,Args.r2 h1,Args.r2 h2,Args.sp h1,Args.sp h2]
    exact ⟨esp,ey,ec,rfl⟩
  · rw [ey,ec]; exact rz.readable
  · rw [ey]; exact rz.writable

end VG.Proof.MlDsa.AArch64.Optimized.Response

end
