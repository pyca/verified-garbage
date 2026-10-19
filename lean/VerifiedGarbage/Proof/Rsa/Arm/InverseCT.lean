module

public import VerifiedGarbage.Impl.Rsa.Arm.Inverse
public import Batteries.Logic
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Impl.Rsa.Arm.Inverse
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

/-! # `inverse` on ARMv7 is constant time: its addresses and branches depend only on `r7`–`r9` -/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Keys
open VG VG.Arm VG.Impl.Rsa.Arm.Keys

theorem inverse_ct : ConstantTime isa (fun _ => True)
    (fun s t => s.gpr .r7 = t.gpr .r7 ∧ s.gpr .r8 = t.gpr .r8 ∧ s.gpr .r9 = t.gpr .r9) inverse := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r7, .r8, .r9]) ?_ (by taint_decide)
  intro s t _ _ ⟨h7, h8, h9⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact h7
  · exact h8
  · exact h9

end VG.Proof.Rsa.Arm.Keys
