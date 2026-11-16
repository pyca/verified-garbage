module

public import VerifiedGarbage.Impl.Sha512.RISCV64
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Sha512.RISCV64
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.Lit

/-!
# SHA-512 on RISC-V: the compression function as a literal

The eighty unrolled rounds are built by functions, which the kernel would
run again in every check that evaluates the code (the summary of its taint
and the frame of that summary, `Compress.lean`, and the constant-time checks
of code that contains it in another taint domain): the literal
(`materialize_code`) is built once, here.
-/

@[expose] public section

namespace VG

materialize_flat_code Impl.Sha512.RISCV64.compress

end VG
