import VerifiedGarbage.Proof.MlDsa.AArch64.Message.OptimizedVerifyPre

namespace VG.Proof.MlDsa.AArch64.Message.OptimizedVerify
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Sign (StaticRoots StaticTable signRootConsts)
open VG.Proof.MlDsa.AArch64.Optimized
open VG.Impl.MlDsa.AArch64.Message
open Message.Optimized (rootRegions roots_reborrow)

/-- The wrapper's hash workspace and stack cannot change either root table. -/
theorem roots_ctx {p : Params} {s t : State} {g : Reg → BitVec 64} {v : VReg → BitVec 128}
    (h : VPre p s) (hc : Ctx (vlay p s) g v s.mem t) (hy : t.syms=s.syms) :
    StaticRoots 16 t := by
  have transfer {nm : String} {ws : List (BitVec 64)} (hr : StaticTable 16 nm ws s) : StaticTable 16 nm ws t := by
    refine hr.frame hc.frame ?_ hc.rd hc.wr hc.sp hy
    intro r hm
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl|rfl
    · exact (hr.writable _ (by rw [h.wr]; simp)).sub_right (vlay_X p s).sub
    · exact hr.stack
  exact ⟨transfer h.roots.forward,transfer h.roots.inverse⟩

theorem verify_pre_extend {p : Params} {s : State}
    (h : (verifyContract p abi 16).pre (s.withRegions
      [⟨s.gpr .x0,p.pkLen⟩,⟨s.gpr .x1,64⟩,⟨s.gpr .x2,p.sigLen⟩] s.wr))
    (hr : StaticRoots 16 s)
    (hd : s.rd=[⟨s.gpr .x0,p.pkLen⟩,⟨s.gpr .x1,64⟩,⟨s.gpr .x2,p.sigLen⟩]++rootRegions s) :
    (verifyContract p (abi.withConsts signRootConsts) 16).pre s := by
  sig_pre [verifyContract,verifySig,abi,argRegs,List.range,List.range.loop] at h
  sig_pre [verifyContract,verifySig,abi,argRegs,Abi.withConsts,
    VG.Proof.MlDsa.AArch64.Sign.signRootConsts_eq,Abi.constRegions,Abi.constsHeld,
    TableConstants.staticNttWords_length,InverseTable.expandedWords_length,stackBelow,
    List.range,List.range.loop]
  obtain ⟨sp,wr,d1,d2,d3,k1,k2,k3,k4,n1,n2,n3,n4⟩ := h
  exact ⟨sp,by rw [hd]; rfl,hr.forward.held,hr.inverse.held,hr.forward.fit,hr.forward.writable,
    hr.forward.stack,hr.inverse.fit,hr.inverse.writable,hr.inverse.stack,by rw [hd]; rfl,
    wr,d1,d2,d3,k1,k2,k3,k4,n1,n2,n3,n4⟩

end VG.Proof.MlDsa.AArch64.Message.OptimizedVerify
