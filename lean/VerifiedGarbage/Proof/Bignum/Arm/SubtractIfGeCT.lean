module

public import VerifiedGarbage.Impl.Bignum.Arm.SubtractIfGe
public import Batteries.Logic
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Impl.Bignum.Arm.SubtractIfGe
import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.TCB.Arm.Target
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.TCB.Arm.Target

/-! # Conditional subtraction has no secret-dependent branches or addresses -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem subtractIfGe_ct : ConstantTime isa (fun _ => True)
    (fun s t => ∀ r ∈ [.r0, .r7, .r9, .r10, .r12, .lr], s.gpr r = t.gpr r) subtractIfGe := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r7, .r9, .r10, .r12, .lr]) ?_
    (by taint_decide)
  intro s t _ _ h
  exact Taint.agree_ofRegs h

end VG.Proof.Bignum.Arm
