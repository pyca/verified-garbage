module

public import VerifiedGarbage.Impl.Ecdsa.RISCV64.P192
public import VerifiedGarbage.Proof.Framework.RISCV64.Lit
public import VerifiedGarbage.Proof.Ecdh.RISCV64.P192.CheckLit
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.P192Field.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.Ecdsa.RISCV64.P192
meta import VerifiedGarbage.Proof.Framework.RISCV64.Lit
meta import VerifiedGarbage.Proof.Ecdh.RISCV64.P192.CheckLit
meta import VerifiedGarbage.Proof.Weierstrass.RISCV64.P192Field.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# `vg_ecdsa_p192_verify` on RISC-V: the code as a literal

`vg_ecdsa_p192_verify` as a literal (`materialize_code`), whose calls of
`vg_p192_check_point` and of the functions modulo `p` and `n` refer to
theirs, which its constant time evaluates.
-/

@[expose] public section

namespace VG

materialize_code Impl.Ecdsa.RISCV64.P192.verifyP192

end VG
