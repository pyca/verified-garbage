module

public import VerifiedGarbage.Impl.Ecdsa.RISCV64.Sign
public import VerifiedGarbage.Proof.Framework.RISCV64.Lit
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.P256.MulLit
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.P256Order.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.Ecdsa.RISCV64.Sign
meta import VerifiedGarbage.Proof.Framework.RISCV64.Lit
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.P256.MulLit
meta import VerifiedGarbage.Proof.Weierstrass.RISCV64.P256Order.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# `vg_ecdsa_p256_sign` on RISC-V: the code as a literal

`vg_ecdsa_p256_sign` as a literal (`materialize_code`), whose calls of
`vg_p256_mul` and of the functions modulo `p` and `n` refer to theirs, which
its constant time evaluates.
-/

@[expose] public section

namespace VG

materialize_code Impl.Ecdsa.RISCV64.Sign.signP256

end VG
