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
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointLit
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointLit
public import VerifiedGarbage.Impl.Ecdsa.Verify.P256.X86_64.Joint
meta import VerifiedGarbage.Impl.Ecdsa.Verify.P256.X86_64.Joint

/-!
# ECDSA verification over P-256 on x86-64, the joint verifier: the ABI's checks of every instruction, on the code without its displacements

`InlineOk`, and no instruction writing `rsp` or loading MXCSR, checked on the
code with its displacements erased, as a literal of shared blocks
(`materialize_shared`; `EraseChecks`), where the field arithmetic is the same
few blocks again and again, each evaluated once.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.Verify.X86_64

/-- `jointVerifyP256` without its displacements, as a literal of shared blocks. -/
def jointVerifyP256Erased : Prog isa := Code.erase jointVerifyP256

materialize_shared jointVerifyP256Erased

theorem jointVerifyP256_inlineOk : jointVerifyP256.InlineOk = true :=
  Code.inlineOk_of_erase (show jointVerifyP256Erased.InlineOk = true by lit_decide)

theorem jointVerifyP256_rspMxcsr :
    jointVerifyP256.allInstrs (fun i => !Taint.clobbers i .rsp && !loadsMxcsr i) = true :=
  Code.rspMxcsr_of_erase (show jointVerifyP256Erased.allInstrs _ = true by lit_decide)

/-- `jointVerifyP256Adx` without its displacements, as a literal of shared blocks. -/
def jointVerifyP256AdxErased : Prog isa := Code.erase jointVerifyP256Adx

materialize_shared jointVerifyP256AdxErased

theorem jointVerifyP256Adx_inlineOk : jointVerifyP256Adx.InlineOk = true :=
  Code.inlineOk_of_erase (show jointVerifyP256AdxErased.InlineOk = true by lit_decide)

theorem jointVerifyP256Adx_rspMxcsr :
    jointVerifyP256Adx.allInstrs (fun i => !Taint.clobbers i .rsp && !loadsMxcsr i) = true :=
  Code.rspMxcsr_of_erase (show jointVerifyP256AdxErased.allInstrs _ = true by lit_decide)

end VG.Proof.Ecdsa.Verify.X86_64
