module

public import VerifiedGarbage.Impl.Bignum.Arm.PublicFn
public import VerifiedGarbage.Proof.Framework.RelCT
public import Batteries.Logic
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Impl.Bignum.Arm.PublicFn
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.Inline
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.TCB.Arm.Target

/-! # Public-operation phase arguments are loaded only from fixed stack offsets -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem publicExponentArgs_ct : RelCT isa (fun s t => s.sp = t.sp)
    (.block PublicFn.exponentArgs) (fun s t => s.sp = t.sp) := stackLoads_ct [(.r1, 56), (.lr, 60)]

theorem publicInputArgs_ct : RelCT isa (fun s t => s.sp = t.sp)
    (.block PublicFn.inputArgs) (fun s t => s.sp = t.sp) := stackLoads_ct [(.r4, 64), (.r6, 12)]

theorem publicControlArgs_ct : RelCT isa (fun s t => s.sp = t.sp)
    (.block PublicFn.controlArgs) (fun s t => s.sp = t.sp) := stackLoads_ct [(.r1, 56), (.r2, 60)]

theorem publicOutputArgs_ct : RelCT isa (fun s t => s.sp = t.sp)
    (.block PublicFn.outputArgs) (fun s t => s.sp = t.sp) := by
  have index : RelCT isa (fun s t => s.sp = t.sp) (.block [.mov .r2 (.imm 6)]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    intro s t _
    exact Taint.agree_ofRegs (by simp)
  exact RelCT.block_append (M := isa) (l₁ := [.mov .r2 (.imm 6)]) (l₂ := [.ldrSp .r4 4, .ldrSp .r6 12])
    ((relCT_keep_sp index (fun _ _ h => h)).seq (stackLoads_ct [(.r4, 4), (.r6, 12)]))

end VG.Proof.Bignum.Arm
