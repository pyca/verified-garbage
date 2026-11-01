module

public import VerifiedGarbage.Impl.Ecdh.P256.RISCV64
public import VerifiedGarbage.Proof.Framework.RISCV64.Lit
public import VerifiedGarbage.Proof.Ecdh.RISCV64.P256.CheckLit
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.P256.MulLit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.Ecdh.P256.RISCV64
meta import VerifiedGarbage.Proof.Framework.RISCV64.Lit
meta import VerifiedGarbage.Proof.Ecdh.RISCV64.P256.CheckLit
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.P256.MulLit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# `vg_ecdh_p256` and `vg_ec_p256_public_key` on RISC-V: the code as literals

`vg_ecdh_p256` and `vg_ec_p256_public_key` as literals (`materialize_code`),
whose calls of
`vg_p256_check_point` and `vg_p256_mul` refer to theirs, which its constant
time evaluates.
-/

@[expose] public section

namespace VG

materialize_code Impl.Ecdh.RISCV64.ecdhP256

materialize_code Impl.Ecdh.RISCV64.publicKeyP256

end VG
