module

public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP256r1.RISCV64.Ecdsa
public import VerifiedGarbage.Proof.Framework.RISCV64.Lit
public import VerifiedGarbage.Proof.Ecdh.RISCV64.BrainpoolP256r1.CheckLit
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.BrainpoolP256r1Order.Lit
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.BrainpoolP256r1.CombLit
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.BrainpoolP256r1.MulLit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.Ecdsa.BrainpoolP256r1.RISCV64.Ecdsa
meta import VerifiedGarbage.Proof.Framework.RISCV64.Lit
meta import VerifiedGarbage.Proof.Ecdh.RISCV64.BrainpoolP256r1.CheckLit
meta import VerifiedGarbage.Proof.Weierstrass.RISCV64.BrainpoolP256r1Order.Lit
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.BrainpoolP256r1.CombLit
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.BrainpoolP256r1.MulLit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# `vg_ecdsa_brainpoolp256r1_verify` on RISC-V: the code as a literal

`vg_ecdsa_brainpoolp256r1_verify` as a literal (`materialize_code`), whose calls of
`vg_brainpoolp256r1_check_point`, `vg_brainpoolp256r1_mul`, `vg_brainpoolp256r1_mul_g`
and the functions modulo `p` and `n` refer to theirs, which its constant time
evaluates.
-/

@[expose] public section

namespace VG

materialize_code Impl.Ecdsa.RISCV64.verifyBrainpoolP256r1

end VG
