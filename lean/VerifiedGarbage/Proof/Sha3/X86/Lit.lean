import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Impl.Sha3.X86

/-!
# Keccak-f[1600] on x86 (32-bit): the code as a literal

The permutation's code is built by functions (its rounds, planes and
round-constant stores): its literal (`materialize_code`) spares the kernel
building the instructions in every check that evaluates the code (constant
time, `NoSp`, the stack's use, `spSafe`), and the streaming functions call it.
-/

namespace VG.Impl.Sha3.X86

materialize_code permute

end VG.Impl.Sha3.X86
