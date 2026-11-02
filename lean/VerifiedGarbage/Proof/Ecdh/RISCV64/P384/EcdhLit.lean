module

public import VerifiedGarbage.Impl.Ecdh.P384.RISCV64
public import VerifiedGarbage.Proof.Framework.RISCV64.Lit
public import VerifiedGarbage.Proof.Ecdh.RISCV64.P384.CheckLit
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.P384.MulLit
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.Comb.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.Ecdh.P384.RISCV64
meta import VerifiedGarbage.Proof.Framework.RISCV64.Lit
meta import VerifiedGarbage.Proof.Ecdh.RISCV64.P384.CheckLit
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.P384.MulLit
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.Comb.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# `vg_ecdh_p384` and `vg_ec_p384_public_key` on RISC-V: the code as literals

`vg_ecdh_p384` and `vg_ec_p384_public_key` as literals (`materialize_code`),
whose calls of `vg_p384_check_point`, `vg_p384_mul` and `vg_p384_mul_g`
refer to theirs, which their constant time evaluates.
-/

@[expose] public section

-- `p`, below `2^384`, is evaluated.
set_option exponentiation.threshold 512

namespace VG

materialize_code Impl.Ecdh.RISCV64.ecdhP384

materialize_code Impl.Ecdh.RISCV64.publicKeyP384

end VG
