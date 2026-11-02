module

public import VerifiedGarbage.Impl.Argon2.RISCV64.Compress
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Argon2.RISCV64.Compress
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.Lit

/-! # Argon2 compression on RISCV64 as a checked instruction literal -/

@[expose] public section

namespace VG.Proof.Argon2.RISCV64

materialize_code compress := Impl.Argon2.RISCV64.compress

end VG.Proof.Argon2.RISCV64
