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
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Secp256k1.Lit
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Secp256k1.Lit
public import VerifiedGarbage.Impl.Ecdsa.Verify.Secp256k1.X86_64
meta import VerifiedGarbage.Impl.Ecdsa.Verify.Secp256k1.X86_64

/-!
# ECDSA verification over secp256k1 on x86-64: the ABI's checks of every instruction, on the code without its displacements

`InlineOk`, and no instruction writing `rsp` or loading MXCSR, checked on the
code with its displacements erased, as a literal of shared blocks
(`materialize_shared`; `EraseChecks`), where the field arithmetic is the same
few blocks again and again, each evaluated once.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86_64.Secp256k1

open VG VG.X86_64 VG.Impl.Ecdsa.Verify.X86_64

/-- `verifySecp256k1` without its displacements, as a literal of shared blocks. -/
def verifySecp256k1Erased : Prog isa := Code.erase verifySecp256k1

materialize_shared verifySecp256k1Erased

theorem verify_inlineOk : verifySecp256k1.InlineOk = true :=
  Code.inlineOk_of_erase (show verifySecp256k1Erased.InlineOk = true by lit_decide)

theorem verify_rspMxcsr :
    verifySecp256k1.allInstrs (fun i => !Taint.clobbers i .rsp && !loadsMxcsr i) = true :=
  Code.rspMxcsr_of_erase (show verifySecp256k1Erased.allInstrs _ = true by lit_decide)

end VG.Proof.Ecdsa.Verify.X86_64.Secp256k1
