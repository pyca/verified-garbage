import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackWidth
import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.BitPack

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64
open VG.Proof.MlDsa.AArch64.Pack
open VG.Impl.MlDsa.AArch64.Optimized.KeygenPack
open VG.Proof.MlKem.AArch64 (agree_of)

theorem simple_ct : ConstantTime isa simpleBitPackK.pre simpleBitPackK.pub simple :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.x0,.x2,.x3])
    (fun _ _ _ _ ⟨h0,h2,h3,hsp⟩=>agree_of hsp (by simp [h0,h2,h3])) (by taint_decide)

theorem signed_ct : ConstantTime isa bitPackK.pre bitPackK.pub signed :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.x0,.x3,.x4])
    (fun _ _ _ _ ⟨h0,h3,h4,hsp⟩=>agree_of hsp (by simp [h0,h3,h4])) (by taint_decide)

end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
