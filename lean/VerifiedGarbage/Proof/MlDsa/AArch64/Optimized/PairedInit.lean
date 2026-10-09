import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductInit
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedCallFrame
import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.Paired

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.MlDsa.AArch64.Optimized.Inverse

def init : List Instr :=
  VG.Impl.MlDsa.AArch64.Arith.movW .x10 4236238847 ++ [.vop (.dup .s4 .v30 .x10)] ++
  VG.Impl.MlDsa.AArch64.Optimized.Paired.vc .v31 8380417 ++ [.movz .x .x11 8 0]

theorem initCounter_ok (s : State) : WP isa (.block [.movz .x .x11 8 0]) s fun t =>
    ((t.gpr .x11=8 ∧ t.mem=s.mem) ∧ Keep [.x11] s t) ∧ t.v=s.v := by
  apply VG.Proof.MlKem.AArch64.WP.keepV (by rfl)
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv := rfl)
  arun

theorem init_ok (s : State) : WP isa (.block init) s fun t =>
    Keep [.x9,.x10,.x11] s t ∧ t.mem=s.mem ∧ t.gpr .x11=8 ∧ ProductConstants t := by
  unfold init
  rw [List.append_assoc,WP.block_append_iff]
  refine WP.mono (productConst_ok s) fun a ⟨hka,hma,h30⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (HighPack.vc_ok a .v31 8380417) fun b hb => ?_
  refine WP.mono (initCounter_ok b) fun t ⟨⟨⟨h11,hm⟩,hk⟩,hv⟩ => ?_
  refine ⟨((hka.trans (constKeep_keep hb.1 (by decide))).trans hk).mono,
    hm.trans (hb.1.mem.trans hma),h11,?_⟩
  exact ⟨by rw [hv,hb.2]; rfl,by rw [hv,hb.1.vec .v30 (by decide),h30]; rfl⟩

end VG.Proof.MlDsa.AArch64.Optimized.Paired
