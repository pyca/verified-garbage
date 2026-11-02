module

public import VerifiedGarbage.Impl.Ecdh.BrainpoolP384r1.RISCV64
public import VerifiedGarbage.Proof.Framework.RISCV64.Lit
public import VerifiedGarbage.Proof.Ecdh.RISCV64.BrainpoolP384r1.CheckLit
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.BrainpoolP384r1.MulLit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.Ecdh.BrainpoolP384r1.RISCV64
meta import VerifiedGarbage.Proof.Framework.RISCV64.Lit
meta import VerifiedGarbage.Proof.Ecdh.RISCV64.BrainpoolP384r1.CheckLit
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.BrainpoolP384r1.MulLit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# `vg_ecdh_brainpoolp384r1` and `vg_ec_brainpoolp384r1_public_key` on RISC-V: the code as literals

`vg_ecdh_brainpoolp384r1` and `vg_ec_brainpoolp384r1_public_key` as literals (`materialize_code`),
whose calls of `vg_brainpoolp384r1_check_point` and `vg_brainpoolp384r1_mul`
refer to theirs, which their constant time evaluates.
-/

@[expose] public section

-- `p`, below `2^384`, is evaluated.
set_option exponentiation.threshold 512

namespace VG

materialize_code Impl.Ecdh.RISCV64.ecdhBrainpoolP384r1

materialize_code Impl.Ecdh.RISCV64.publicKeyBrainpoolP384r1

end VG
