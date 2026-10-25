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
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P384.JointLit
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P384.JointLit
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P384.JointLitAdx
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P384.JointLitAdx
public import VerifiedGarbage.Impl.Ecdsa.Verify.P384.X86_64
meta import VerifiedGarbage.Impl.Ecdsa.Verify.P384.X86_64

/-!
# ECDSA verification over P-384 on x86-64: the ABI's checks of every instruction, on the code without its displacements

`InlineOk`, and no instruction writing `rsp` or loading MXCSR, checked on the
code with its displacements erased, as a literal of shared blocks
(`materialize_shared`; `EraseChecks`), where the field arithmetic is the same
few blocks again and again, each evaluated once.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86_64.P384

open VG VG.X86_64 VG.Impl.Ecdsa.Verify.X86_64

/-- `jointVerifyP384` without its displacements, as a literal of shared blocks. -/
def jointVerifyP384Erased : Prog isa := Code.erase jointVerifyP384

materialize_shared jointVerifyP384Erased

theorem jointVerifyP384_inlineOk : jointVerifyP384.InlineOk = true :=
  Code.inlineOk_of_erase (show jointVerifyP384Erased.InlineOk = true by lit_decide)

theorem jointVerifyP384_rspMxcsr :
    jointVerifyP384.allInstrs (fun i => !Taint.clobbers i .rsp && !loadsMxcsr i) = true :=
  Code.rspMxcsr_of_erase (show jointVerifyP384Erased.allInstrs _ = true by lit_decide)

/-- `jointVerifyP384Adx` without its displacements, as a literal of shared blocks. -/
def jointVerifyP384AdxErased : Prog isa := Code.erase jointVerifyP384Adx

materialize_shared jointVerifyP384AdxErased

theorem jointVerifyP384Adx_inlineOk : jointVerifyP384Adx.InlineOk = true :=
  Code.inlineOk_of_erase (show jointVerifyP384AdxErased.InlineOk = true by lit_decide)

theorem jointVerifyP384Adx_rspMxcsr :
    jointVerifyP384Adx.allInstrs (fun i => !Taint.clobbers i .rsp && !loadsMxcsr i) = true :=
  Code.rspMxcsr_of_erase (show jointVerifyP384AdxErased.allInstrs _ = true by lit_decide)

end VG.Proof.Ecdsa.Verify.X86_64.P384
