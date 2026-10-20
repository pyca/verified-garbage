module

public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Impl.Rsa.Arm.Div
public import VerifiedGarbage.Proof.Rsa.Arm.DivContext
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Impl.Rsa.Arm.Div
meta import VerifiedGarbage.Proof.Rsa.Arm.DivContext
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # Header-only setup blocks have no secret-dependent leakage -/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Div
open VG VG.Arm VG.Impl.Rsa.Arm.Div

theorem quotientArgs_ct {g : Geometry} :
    RelCT isa (fun s t => Context g s ∧ Context g t) (.block quotientArgs) (fun _ _ => True) := by
  apply RelCT.taint (A := taint) (Taint.ofRegs [.r8]) _ (by taint_decide)
  intro s t h
  apply Taint.agree_ofRegs
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r
  exact h.1.ptr.trans h.2.ptr.symm

theorem remainderArgs_ct {g : Geometry} :
    RelCT isa (fun s t => Context g s ∧ Context g t) (.block remainderArgs) (fun _ _ => True) := by
  apply RelCT.taint (A := taint) (Taint.ofRegs [.r8]) _ (by taint_decide)
  intro s t h
  apply Taint.agree_ofRegs
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r
  exact h.1.ptr.trans h.2.ptr.symm

theorem subtractArgs_ct {g : Geometry} :
    RelCT isa (fun s t => Context g s ∧ Context g t) (.block subtractArgs) (fun _ _ => True) := by
  apply RelCT.taint (A := taint) (Taint.ofRegs [.r8]) _ (by taint_decide)
  intro s t h
  apply Taint.agree_ofRegs
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r
  exact h.1.ptr.trans h.2.ptr.symm

theorem initCount_ct {g : Geometry} :
    RelCT isa (fun s t => Context g s ∧ Context g t)
      (.block [.ldr .r6 .r8 16, .mov .r6 (.shifted .r6 .lsl 5)]) (fun _ _ => True) := by
  apply RelCT.taint (A := taint) (Taint.ofRegs [.r8]) _ (by taint_decide)
  intro s t h
  apply Taint.agree_ofRegs
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r
  exact h.1.ptr.trans h.2.ptr.symm

end VG.Proof.Rsa.Arm.Div
