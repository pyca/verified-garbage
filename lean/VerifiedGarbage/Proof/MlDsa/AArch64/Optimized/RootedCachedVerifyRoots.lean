import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.RootedCachedVerifyPre

namespace VG.Proof.MlDsa.AArch64.Optimized.RootedCachedVerify
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Sign (StaticRoots StaticTable signRootConsts)
open VG.Proof.MlDsa.AArch64.Optimized
open VG.Impl.MlDsa.AArch64.Message
open VG.Proof.MlDsa.AArch64.Message
open Message.Optimized (rootRegions roots_reborrow)

/-- The wrapper's hash workspace and stack cannot change either root table. -/
theorem roots_ctx {p : Params} {s t : State} {g : Reg → BitVec 64} {v : VReg → BitVec 128}
    (h : CachedPre p s) (hc : Ctx (cachedLay p s) g v s.mem t) (hy : t.syms=s.syms) :
    StaticRoots 16 t := by
  have transfer {nm : String} {ws : List (BitVec 64)} (hr : StaticTable 16 nm ws s) : StaticTable 16 nm ws t := by
    refine hr.frame hc.frame ?_ hc.rd hc.wr hc.sp hy
    intro r hm
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl|rfl
    · exact (hr.writable _ (by rw [h.wr]; simp)).sub_right (cachedLay_X p s).sub
    · exact hr.stack
  exact ⟨transfer h.roots.forward,transfer h.roots.inverse⟩

end VG.Proof.MlDsa.AArch64.Optimized.RootedCachedVerify
