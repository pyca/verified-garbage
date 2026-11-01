module

public import VerifiedGarbage.Impl.Camellia.RISCV64.Modes
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Camellia.RISCV64.Lit
meta import VerifiedGarbage.Impl.Camellia.RISCV64.Modes
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.Lit
meta import VerifiedGarbage.Proof.Camellia.RISCV64.Lit

/-!
# Camellia's modes on RISC-V, evaluated once

The pieces of ECB the modes inline (`crypt8`, `encKeys`, `decKeys`), and the
modes, as literals (`materialize_code`), which the checks that evaluate the
code read.
-/

@[expose] public section

namespace VG.Impl.Camellia.RISCV64
materialize_code crypt8
materialize_code encKeys
materialize_code decKeys
materialize_code cbcEncryptChained
materialize_code cbcDecryptChained
materialize_code ofb
materialize_code cfbEncrypt
materialize_code cfbDecrypt
materialize_code ctr
end VG.Impl.Camellia.RISCV64
