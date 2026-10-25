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
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Lit
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Lit
public import VerifiedGarbage.Impl.Ecdsa.Verify.P256.X86_64
meta import VerifiedGarbage.Impl.Ecdsa.Verify.P256.X86_64

/-!
# ECDSA verification over P-256 on x86-64: the ABI's checks of every instruction, on the code without its displacements

`InlineOk`, no instruction writing `rsp` and none loading MXCSR, checked on the
code with its displacements erased, as a literal of shared blocks
(`materialize_shared`; `EraseChecks`), where the field arithmetic is the same
few blocks again and again, each evaluated once.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.Verify.X86_64

/-- `verifyP256` without its displacements, as a literal of shared blocks. -/
def verifyP256Erased : Prog isa := Code.erase verifyP256

materialize_shared verifyP256Erased

theorem verifyP256_inlineOk : verifyP256.InlineOk = true :=
  Code.inlineOk_of_erase (show verifyP256Erased.InlineOk = true by lit_decide)

theorem verifyP256_noRsp : verifyP256.allInstrs (fun i => !Taint.clobbers i .rsp) = true :=
  Code.allInstrs_of_erase (fun i => by rw [Instr.clobbers_erase])
    (show verifyP256Erased.allInstrs _ = true by lit_decide)

theorem verifyP256_noMxcsr : verifyP256.allInstrs (fun i => !loadsMxcsr i) = true :=
  Code.allInstrs_of_erase (fun i => by rw [Instr.loadsMxcsr_erase])
    (show verifyP256Erased.allInstrs _ = true by lit_decide)

end VG.Proof.Ecdsa.Verify.X86_64
