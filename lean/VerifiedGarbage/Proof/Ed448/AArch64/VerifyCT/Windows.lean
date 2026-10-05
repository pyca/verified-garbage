import VerifiedGarbage.Proof.Ed448.AArch64.VerifyErase
import VerifiedGarbage.Proof.Framework.AArch64.Taint

/-!
# Ed448 verification's equation on AArch64: constant time of the windows and the comparison

Untrusted: everything here is checked by Lean. As `VerifyCT/Front.lean`, for
the last two phases: the windows over the challenge, and the comparison with
the result.
-/

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64 VG.Impl.Ed448.AArch64

theorem kWindows_ct : ∃ h, (taint.check (Taint.ofRegs [.x3]) (Code.eraseImm kWindows) h).map
    (taint.le (Taint.ofRegs [.x3])) = some true := by
  refine ⟨?h, ?g⟩
  case g => taint_decide

theorem tail_ct :
    ∃ h, (taint.check (Taint.ofRegs [.x3]) (Code.eraseImm (.block (wcross ++ wfinish))) h).isSome = true := by
  refine ⟨?h, ?g⟩
  case g => taint_decide

end VG.Proof.Ed448.AArch64
