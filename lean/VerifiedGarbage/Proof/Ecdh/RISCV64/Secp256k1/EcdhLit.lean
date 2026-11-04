module

public import VerifiedGarbage.Impl.Ecdh.Secp256k1.RISCV64
public import VerifiedGarbage.Proof.Framework.RISCV64.Lit
public import VerifiedGarbage.Proof.Ecdh.RISCV64.Secp256k1.CheckLit
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.Secp256k1.MulLit
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.Secp256k1.CombLit
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.Comb.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.Ecdh.Secp256k1.RISCV64
meta import VerifiedGarbage.Proof.Framework.RISCV64.Lit
meta import VerifiedGarbage.Proof.Ecdh.RISCV64.Secp256k1.CheckLit
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.Secp256k1.MulLit
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.Secp256k1.CombLit
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.Comb.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# `vg_ecdh_secp256k1` and `vg_ec_secp256k1_public_key` on RISC-V: the code as literals

`vg_ecdh_secp256k1` and `vg_ec_secp256k1_public_key` as literals (`materialize_code`),
whose calls of `vg_secp256k1_check_point`, `vg_secp256k1_mul` and
`vg_secp256k1_mul_g`
refer to theirs, which their constant time evaluates.
-/

@[expose] public section

namespace VG

materialize_code Impl.Ecdh.RISCV64.ecdhSecp256k1

materialize_code Impl.Ecdh.RISCV64.publicKeySecp256k1

end VG
