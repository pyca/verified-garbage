module

public import VerifiedGarbage.Impl.Bignum.Arm.Shift
public import Batteries.Logic
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Impl.Bignum.Arm.Shift
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

/-! # Only the shift pointer and word count are public -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem shift_ct : ConstantTime isa (fun _ => True)
    (fun s t => s.gpr .r0 = t.gpr .r0 ∧ s.gpr .lr = t.gpr .lr) shift := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .lr]) ?_ (by taint_decide)
  intro s t _ _ h
  refine Taint.agree_ofRegs fun r hr => ?_
  have : r = .r0 ∨ r = .lr := by simpa using hr
  rcases this with rfl | rfl
  · exact h.1
  · exact h.2

end VG.Proof.Bignum.Arm
