module

public import VerifiedGarbage.Impl.Ecdh.BrainpoolP320r1.RISCV64
public import VerifiedGarbage.Proof.Framework.RISCV64.Lit
public import VerifiedGarbage.Proof.Ecdh.RISCV64.BrainpoolP320r1.CheckLit
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.BrainpoolP320r1.MulLit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.Ecdh.BrainpoolP320r1.RISCV64
meta import VerifiedGarbage.Proof.Framework.RISCV64.Lit
meta import VerifiedGarbage.Proof.Ecdh.RISCV64.BrainpoolP320r1.CheckLit
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.BrainpoolP320r1.MulLit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# `vg_ecdh_brainpoolp320r1` and `vg_ec_brainpoolp320r1_public_key` on RISC-V: the code as literals

`vg_ecdh_brainpoolp320r1` and `vg_ec_brainpoolp320r1_public_key` as literals (`materialize_code`),
whose calls of `vg_brainpoolp320r1_check_point` and `vg_brainpoolp320r1_mul`
refer to theirs, which their constant time evaluates.
-/

@[expose] public section


namespace VG

materialize_code Impl.Ecdh.RISCV64.ecdhBrainpoolP320r1

materialize_code Impl.Ecdh.RISCV64.publicKeyBrainpoolP320r1

end VG
