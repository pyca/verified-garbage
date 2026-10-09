import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedSaved
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedCallFrame

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.Paired
open VG.Proof.MlKem.AArch64 (Keep)

/-- Restore the saved ABI vectors after returning the exact combined checks.
The intermediate kernel may use every vector register, including v8--v15. -/
theorem finish_saved_ok (kind : Kind) {s₀ s : State} {work : Addr}
    {gr : List Reg} {vr : List VReg} (hf : CallFrame gr vr s₀ s)
    (hx : s.gpr .x2=work+BitVec.ofNat 64 128) (hs : Saved s.mem work s₀.v)
    (hr : ∀p∈extraSlots 1920,InRegions (s.rd++s.wr) (s.gpr .x2+BitVec.ofNat 64 p.2) 16) :
    WP isa (.block (finish kind)) s fun t =>
      Keep (gr++([.x0,.x9,.x10] : List Reg)) s₀ t ∧ t.mem=s.mem ∧ t.gpr .x0=returnValue kind s := by
  rw [finish_split,WP.block_append_iff]
  refine WP.mono (return_ok kind s) fun a ⟨⟨⟨ha,hm⟩,hk⟩,hv⟩ => ?_
  have hxa : a.gpr .x2=work+BitVec.ofNat 64 128 := (hk.get .x2 (by decide)).trans hx
  have hsa : Saved a.mem work s₀.v := by rw [hm]; exact hs
  have hra : ∀p∈extraSlots 1920,InRegions (a.rd++a.wr) (a.gpr .x2+BitVec.ofNat 64 p.2) 16 := by
    intro p hp
    rw [hk.rd,hk.wr,hk.get .x2 (by decide)]
    exact hr p hp
  have hframe := hf.trans (CallFrame.ofKeep hk hv)
  simpa only [List.append_nil] using
    (restore_preservedV (rest := []) hxa hsa hra fun t ht hvt => WP.block_nil_iff.mpr (show
      Keep (gr++([.x0,.x9,.x10] : List Reg)) s₀ t ∧ t.mem=s.mem ∧ t.gpr .x0=returnValue kind s from
      ⟨⟨fun r h => (congrFun ht.gpr r).trans (hframe.gpr r h),
        ht.rd.trans hframe.rd,ht.wr.trans hframe.wr,ht.sp.trans hframe.sp,hvt⟩,
       ht.mem.trans hm,(congrFun ht.gpr .x0).trans ha⟩))

end VG.Proof.MlDsa.AArch64.Optimized.Paired
