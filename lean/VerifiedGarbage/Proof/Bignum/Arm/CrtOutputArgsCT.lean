module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtOutputArgs
public import VerifiedGarbage.Proof.Bignum.Arm.CrtStageCT
public import VerifiedGarbage.Proof.Bignum.Arm.StackCT
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Output-pointer setup depends only on public workspace and stack addresses -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem crt_outputArgs_ct : RelCT isa (fun s t => s.gpr .r0 = t.gpr .r0 ∧ s.sp = t.sp)
    (.block CrtFn.outputArgs) (fun _ _ => True) := by
  have first : RelCT isa (fun s t => s.gpr .r0 = t.gpr .r0 ∧ s.sp = t.sp)
      (.block [.ldr .r1 .r0 232]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r0]) _ (by taint_decide)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.1
  exact RelCT.block_append (M := isa) (l₁ := [.ldr .r1 .r0 232]) (l₂ := [.ldrSp .r4 4, .ldrSp .r6 12])
    (((relCT_keep_sp first (fun _ _ h => h.2)).seq (stackLoads_ct [(.r4, 4), (.r6, 12)])).mono
      (fun _ _ h => h) (fun _ _ _ => trivial))

end VG.Proof.Bignum.Arm
