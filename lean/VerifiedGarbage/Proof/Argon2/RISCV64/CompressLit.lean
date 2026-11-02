module

public import VerifiedGarbage.Impl.Argon2.RISCV64.Compress
public import VerifiedGarbage.Impl.Argon2.RISCV64.HPrime
public import VerifiedGarbage.Proof.Blake2.RISCV64.Stream.Lit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Argon2.RISCV64.Compress
meta import VerifiedGarbage.Impl.Argon2.RISCV64.HPrime
meta import VerifiedGarbage.Proof.Blake2.RISCV64.Stream.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.Lit

/-! # Argon2's compression G and H′ on RISC-V as checked instruction literals -/

@[expose] public section

namespace VG.Proof.Argon2.RISCV64

materialize_code compress := Impl.Argon2.RISCV64.compress
materialize_code hPrime := Impl.Argon2.RISCV64.HPrime.code

end VG.Proof.Argon2.RISCV64
