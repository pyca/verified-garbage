module

public import VerifiedGarbage.Proof.RsaPss.EncodingContract
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Callee
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.Mem

/-!
# EMSA-PSS's encoding and its check on AArch64, as callees

RSASSA-PSS's signing and verification call `encode` and `checkEncoding`
(or their variants), of which they need only what their artifacts state:
that the code is `Verified` for the shared contract with some `stack`, and
that its frames fit in that stack (`Callee`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64

open VG VG.AArch64
open VG.Proof.RsaPkcs1Sig.AArch64 (Callee ArgsEq argsEq_regs)

/-- The `K` bytes below the stack pointer. -/
abbrev stkR (K : Nat) (t : State) : Region := ⟨t.sp - BitVec.ofNat 64 K, K⟩



end VG.Proof.RsaPss.AArch64
