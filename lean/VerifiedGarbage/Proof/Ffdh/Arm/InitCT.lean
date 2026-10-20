module

public import VerifiedGarbage.Impl.Ffdh.Arm.Init
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Impl.Ffdh.Arm.Init
meta import VerifiedGarbage.Proof.Framework.Arm.Taint

/-! Controller initialization depends only on its public arguments. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Impl.Ffdh.Arm

theorem keyInit_ct : RelCT isa (fun s t => ∀ r ∈ [.r0, .r1], s.gpr r = t.gpr r)
    KeyGeneration.init (fun _ _ => True) := by
  apply RelCT.taint (A := taint) (Taint.ofRegs [.r0, .r1]) _ (by taint_decide)
  intro s t h
  exact Taint.agree_ofRegs h

theorem parameterInit_ct : RelCT isa (fun s t => ∀ r ∈ [.r0, .r1, .r2], s.gpr r = t.gpr r)
    Generation.init (fun _ _ => True) := by
  apply RelCT.taint (A := taint) (Taint.ofRegs [.r0, .r1, .r2]) _ (by taint_decide)
  intro s t h
  exact Taint.agree_ofRegs h

end VG.Proof.Ffdh.Arm
