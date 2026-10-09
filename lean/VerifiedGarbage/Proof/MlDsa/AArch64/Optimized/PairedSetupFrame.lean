import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedCallFrame
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedMiddle

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.MlDsa.AArch64.Optimized.HighPack (SetupKeep)

def allVectors : List VReg := [.v0,.v1,.v2,.v3,.v4,.v5,.v6,.v7,
  .v8,.v9,.v10,.v11,.v12,.v13,.v14,.v15,.v16,.v17,.v18,.v19,.v20,.v21,.v22,.v23,
  .v24,.v25,.v26,.v27,.v28,.v29,.v30,.v31]

/-- Scalar preservation can be carried across stages independently of vector
preservation: the final saved-vector restoration discharges the latter. -/
theorem CallFrame.ofKeepWide {gr : List Reg} {s t : State} (h : Keep gr s t) :
    CallFrame gr allVectors s t := by
  refine ⟨fun r hr => h.get r hr,h.rd,h.wr,h.sp,?_⟩
  intro r hr
  exact False.elim (hr ((show ∀r:VReg,r∈allVectors by intro r; cases r <;> decide) r))

theorem setup_callFrame {vr : List VReg} {s t : State} (h : SetupKeep vr s t) :
    CallFrame [.x9] vr s t :=
  ⟨fun r hr => h.gpr r (by simpa only [List.mem_singleton] using hr),h.rd,h.wr,h.sp,h.vec⟩

theorem setup_callFrame_wide {vr : List VReg} {s t : State} (h : SetupKeep vr s t) :
    CallFrame [.x9] allVectors s t := by
  refine (setup_callFrame h).mono (by rfl) ?_
  intro r _
  exact (show ∀r:VReg,r∈allVectors by intro r; cases r <;> decide) r

end VG.Proof.MlDsa.AArch64.Optimized.Paired
