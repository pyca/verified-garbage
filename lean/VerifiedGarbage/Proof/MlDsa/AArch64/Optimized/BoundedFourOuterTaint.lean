import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourInitialized
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourMaskFour
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rel

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.BoundedFour (squeezeTwo flags)

theorem samplerSetup_taint : ∃h,
    (taint.check (Taint.ofRegs [.x0,.x1,.x2]) (.block samplerSetup) h).isSome=true :=
  ⟨_,by taint_decide⟩

theorem squeezeTwo_taint (sha3 : Bool) {off : Nat} (ho : off=0∨off=272) : ∃h,
    (taint.check (Taint.ofRegs [.x19]) (squeezeTwo sha3 off) h).isSome=true := by
  rcases ho with rfl|rfl <;> cases sha3 <;> exact ⟨_,by taint_decide⟩

theorem flags_taint : ∃h,
    (taint.check (Taint.ofRegs [.x19]) (.block flags) h).isSome=true :=
  ⟨_,by taint_decide⟩

theorem maskFour_taint : ∃h,
    (taint.check (Taint.ofRegs [.x19,.x21]) maskFour h).isSome=true :=
  ⟨_,by taint_decide⟩

theorem finish_taint : ∃h,
    (taint.check (Taint.ofRegs [.x19])
      (.block (([.subImm .x .x27 .x27 1,.lsr .x .x27 .x27 63] : List Instr)++
        VG.Impl.MlDsa.AArch64.Sample.Rej4.epi)) h).isSome=true :=
  ⟨_,by taint_decide⟩

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
