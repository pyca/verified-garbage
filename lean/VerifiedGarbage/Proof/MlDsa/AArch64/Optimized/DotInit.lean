import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotLoop
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseSetup

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep wp_vop wp_scalar)

def dotInitRegs : List Reg := [.x3,.x4,.x5,.x6,.x7,.x9,.x10,.x11]

theorem dotSetup_ok (s : State) :
    WP isa (.block VG.Impl.MlDsa.AArch64.Optimized.DotInverse.setup) s fun t =>
      Keep dotInitRegs s t ∧ t.mem=s.mem ∧ t.gpr .x11=8 ∧ ProductConstants t := by
  change WP isa (.block (VG.Impl.MlDsa.AArch64.Arith.movW .x10 4236238847 ++
    Instr.vop (.dup .s4 .v30 .x10)::
      (VG.Impl.MlDsa.AArch64.Optimized.HighPack.vc .v31 8380417++firstSetup))) s _
  refine wp_scalar (by rfl) (VG.Proof.MlDsa.AArch64.Arith.movW_ok .x10 _ s)
    fun a ⟨⟨ha,hm⟩,hk⟩ hv => ?_
  refine wp_vop (d:=.v30) rfl fun b hb => ?_
  rw [WP.block_append_iff]
  refine WP.mono (HighPack.vc_ok b .v31 8380417) fun c hc => ?_
  refine WP.mono (firstSetup_ok c) fun t ⟨⟨⟨h11,htm⟩,htk⟩,htv⟩ => ?_
  refine ⟨(((hk.trans hb.chg.keep).trans (constKeep_keep hc.1 (by decide))).trans htk).mono,
    htm.trans (hc.1.mem.trans (hb.mem.trans hm)),h11,?_,?_⟩
  · rw [htv,hc.2]; rfl
  · rw [htv,hc.1.vec .v30 (by decide),hb.v,ha]
    rfl

end VG.Proof.MlDsa.AArch64.Optimized.Inverse
