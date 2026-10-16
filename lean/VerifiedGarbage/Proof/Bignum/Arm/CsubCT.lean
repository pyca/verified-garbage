module

public import VerifiedGarbage.Impl.Bignum.Arm.Csub
meta import VerifiedGarbage.Impl.Bignum.Arm.Csub
public import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Final modular reduction has no secret-dependent branches or addresses -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem csub_ct : ConstantTime isa (fun _ => True)
    (fun s t => ∀ r ∈ [.r0, .r7, .r9, .r10, .r12, .lr], s.gpr r = t.gpr r) csub := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r7, .r9, .r10, .r12, .lr]) ?_
    (by taint_decide)
  intro s t _ _ h
  exact Taint.agree_ofRegs h

end VG.Proof.Bignum.Arm
