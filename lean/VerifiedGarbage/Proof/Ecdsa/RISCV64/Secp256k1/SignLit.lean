module

public import VerifiedGarbage.Impl.Ecdsa.Secp256k1.RISCV64.Ecdsa
public import VerifiedGarbage.Proof.Framework.RISCV64.Lit
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.Secp256k1.MulLit
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.Secp256k1Order.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.Ecdsa.Secp256k1.RISCV64.Ecdsa
meta import VerifiedGarbage.Proof.Framework.RISCV64.Lit
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.Secp256k1.MulLit
meta import VerifiedGarbage.Proof.Weierstrass.RISCV64.Secp256k1Order.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# `vg_ecdsa_secp256k1_sign` on RISC-V: the code as a literal

`vg_ecdsa_secp256k1_sign` as a literal (`materialize_code`), whose calls of
`vg_secp256k1_mul` and of the functions modulo `p` and `n` refer to theirs, which
its constant time evaluates.
-/

@[expose] public section

namespace VG

materialize_code Impl.Ecdsa.RISCV64.signSecp256k1

/-- `vg_ecdsa_secp256k1_sign`'s code has no frame, which its callers' calls need. -/
theorem Impl.Ecdsa.RISCV64.signSecp256k1_noFrames : Impl.Ecdsa.RISCV64.signSecp256k1.noFrames = true := by
  lit_decide

end VG
