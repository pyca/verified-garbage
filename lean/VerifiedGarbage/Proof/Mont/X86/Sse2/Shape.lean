module

public import VerifiedGarbage.Impl.Mont.X86.Sse2
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Framework.X86.CallWith

/-! # The two functions' shape, for their callers

No instruction of either writes `esp` but its frames, which use 56 bytes:
the callee-saved registers' 16, the parameters' 28 and the MCDT frame's 12. -/

@[expose] public section

namespace VG.Proof.Mont.X86.Sse2
open VG VG.X86 VG.Impl.Mont.X86.Sse2

theorem atBody_allNoSp : atBody.allInstrs (fun i => !VG.X86.Taint.clobbers i .esp) = true := by
  decide +kernel

theorem preparedBody_allNoSp : preparedBody.allInstrs (fun i => !VG.X86.Taint.clobbers i .esp) = true := by
  decide +kernel

theorem atBody_NoSp : NoSp atBody := NoSp.of_all atBody_allNoSp

theorem preparedBody_NoSp : NoSp preparedBody := NoSp.of_all preparedBody_allNoSp

theorem atBody_stack : stackUse atBody = 56 := by decide +kernel

theorem preparedBody_stack : stackUse preparedBody = 56 := by decide +kernel

end VG.Proof.Mont.X86.Sse2
