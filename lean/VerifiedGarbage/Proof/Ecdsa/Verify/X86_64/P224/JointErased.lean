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
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P224.JointLit
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P224.JointLit
public import VerifiedGarbage.Impl.Ecdsa.Verify.P224.X86_64
public import VerifiedGarbage.Proof.Framework.X86_64.CallInlineN
import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Impl.Ecdsa.Verify.P224.X86_64

/-!
# ECDSA verification over P-224 on x86-64: the ABI's checks of every instruction, on the code without its displacements

`InlineOk`, and no instruction writing `rsp` or loading MXCSR, checked on the
code with its displacements erased, as a literal of shared blocks
(`materialize_shared`; `EraseChecks`), where the field arithmetic is the same
few blocks again and again, each evaluated once.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86_64.P224

open VG VG.X86_64 VG.Impl.Ecdsa.Verify.X86_64

/-- `jointVerifyP224` without its displacements, as a literal of shared blocks. -/
def jointVerifyP224Erased : Prog isa := Code.erase jointVerifyP224

materialize_shared jointVerifyP224Erased

/-- `InlineOkN`, calls nested two deep (the additions call the end of the
addition, `vg_p224_jac_add_tail`). -/
theorem jointVerifyP224_inlineOk : jointVerifyP224.InlineOkN 2 = true :=
  Code.inlineOkN_of_erase (show jointVerifyP224Erased.InlineOkN 2 = true by lit_decide)

/-- The code the proofs run: `jointVerifyP224` with the additions' end inline
(`publicJointF`), which is `jointVerifyP224` inlined at every depth. -/
abbrev jointVerifyP224F : Prog isa :=
  Cfg.jointVerify Impl.P224.X86_64.p224v Impl.P224.X86_64.publicJointF
    (Impl.P224.X86_64.jointDouble Impl.P224.X86_64.publicJointF.K)

theorem jointVerifyP224_inlineAll : jointVerifyP224.inlineAll = jointVerifyP224F.inline := by kernel_rfl

theorem jointVerifyP224_rspMxcsr :
    jointVerifyP224.allInstrs (fun i => !Taint.clobbers i .rsp && !loadsMxcsr i) = true :=
  Code.rspMxcsr_of_erase (show jointVerifyP224Erased.allInstrs _ = true by lit_decide)

end VG.Proof.Ecdsa.Verify.X86_64.P224
