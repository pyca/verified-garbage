module

public import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
meta import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
meta import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.EraseChecks
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.EraseChecks
import VerifiedGarbage.Proof.Framework.LitShare
meta import VerifiedGarbage.Proof.Framework.LitShare
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P521.JointLit
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P521.JointLit
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P521.JointLitAdx
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P521.JointLitAdx
public import VerifiedGarbage.Impl.Ecdsa.Verify.P521.X86_64
meta import VerifiedGarbage.Impl.Ecdsa.Verify.P521.X86_64

/-!
# ECDSA verification over P-521 on x86-64: the ABI's checks of every instruction, on the code without its displacements

`InlineOk`, and no instruction writing `rsp` or loading MXCSR, checked on the
code with its displacements erased, as a literal of shared blocks
(`materialize_shared`; `EraseChecks`), where the field arithmetic is the same
few blocks again and again, each evaluated once.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86_64.P521

open VG VG.X86_64 VG.Impl.Ecdsa.Verify.X86_64

/-- `jointVerifyP521` without its displacements, as a literal of shared blocks. -/
def jointVerifyP521Erased : Prog isa := Code.erase jointVerifyP521

materialize_shared jointVerifyP521Erased

theorem jointVerifyP521_inlineOk : jointVerifyP521.InlineOk = true :=
  Code.inlineOk_of_erase (show jointVerifyP521Erased.InlineOk = true by lit_decide)

theorem jointVerifyP521_rspMxcsr :
    jointVerifyP521.allInstrs (fun i => !Taint.clobbers i .rsp && !loadsMxcsr i) = true :=
  Code.rspMxcsr_of_erase (show jointVerifyP521Erased.allInstrs _ = true by lit_decide)

/-- `jointVerifyP521Adx` without its displacements, as a literal of shared blocks. -/
def jointVerifyP521AdxErased : Prog isa := Code.erase jointVerifyP521Adx

materialize_shared jointVerifyP521AdxErased

theorem jointVerifyP521Adx_inlineOk : jointVerifyP521Adx.InlineOk = true :=
  Code.inlineOk_of_erase (show jointVerifyP521AdxErased.InlineOk = true by lit_decide)

theorem jointVerifyP521Adx_rspMxcsr :
    jointVerifyP521Adx.allInstrs (fun i => !Taint.clobbers i .rsp && !loadsMxcsr i) = true :=
  Code.rspMxcsr_of_erase (show jointVerifyP521AdxErased.allInstrs _ = true by lit_decide)

end VG.Proof.Ecdsa.Verify.X86_64.P521
