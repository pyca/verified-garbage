module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourMaskFour
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejFold
import VerifiedGarbage.TCB.Axioms
public import VerifiedGarbage.Proof.Framework.AArch64.VectorTaint
public import VerifiedGarbage.Proof.Framework.AArch64.TaintMono
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.RegSet
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Lit
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourMaskFour
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejFold
meta import VerifiedGarbage.TCB.Axioms
meta import VerifiedGarbage.Proof.Framework.AArch64.VectorTaint
meta import VerifiedGarbage.Proof.Framework.AArch64.TaintMono
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.RegSet
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Lit

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.BoundedFour (squeezeTwo flags)

theorem samplerSetup_taint : ∃h,
    (taint.check (Taint.ofRegs [.x0,.x1,.x2]) (.block samplerSetup) h).isSome=true :=
  ⟨_,by taint_decide⟩

/-! The call of the paired Keccak without the SHA-3 extension, analysed once for the two
squeezes' checks, from the pointers and the count they have public (the function restores every
callee-saved register it writes, so the registers the summary leaves public are those of its
`pre`). -/
taint_summary x2Sum : VectorTaint.taint
    (VectorTaint.ofRegs [.x0, .x1, .x19, .x22, .x23, .x24, .x25, .x26, .x27, .x28])
  (.call (Impl.Sha3.AArch64.Neon.X2.name false) (Impl.Sha3.AArch64.Neon.X2.code false))

theorem squeezeTwo_taint (sha3 : Bool) {off : Nat} (ho : off=0∨off=272) : ∃h,
    (VectorTaint.taint.check (VectorTaint.ofRegs [.x19]) (squeezeTwo sha3 off) h).isSome=true := by
  -- Without the SHA-3 extension, the call by its summary; with it, unfolded as far as the call,
  -- whose code has a literal (`Neon.X2.code true`) that `taint_decide` finds only where the goal
  -- names it.
  rcases ho with rfl|rfl <;> cases sha3
  · taint_decide_sum [x2Sum]
  · exact ⟨_,by
      unfold squeezeTwo Impl.MlDsa.AArch64.Optimized.BoundedFour.squeezeStep
        Impl.MlDsa.AArch64.Optimized.BoundedFour.pair Impl.Sha3.AArch64.Neon.X2.call
      taint_decide⟩
  · taint_decide_sum [x2Sum]
  · exact ⟨_,by
      unfold squeezeTwo Impl.MlDsa.AArch64.Optimized.BoundedFour.squeezeStep
        Impl.MlDsa.AArch64.Optimized.BoundedFour.pair Impl.Sha3.AArch64.Neon.X2.call
      taint_decide⟩

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
