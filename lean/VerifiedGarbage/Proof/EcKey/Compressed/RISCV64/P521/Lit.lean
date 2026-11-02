module

public import VerifiedGarbage.Impl.EcKey.Compressed.P521.RISCV64
public import VerifiedGarbage.Proof.Framework.RISCV64.Lit
public import VerifiedGarbage.Proof.Ecdh.RISCV64.P521.CheckLit
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.P521Field.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.EcKey.Compressed.P521.RISCV64
meta import VerifiedGarbage.Proof.Framework.RISCV64.Lit
meta import VerifiedGarbage.Proof.Ecdh.RISCV64.P521.CheckLit
meta import VerifiedGarbage.Proof.Weierstrass.RISCV64.P521Field.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# SEC 1 point conversion over P-521 on RISC-V: the code as literals

`vg_ec_p521_compress_public_key` and `_decompress_public_key` as literals
(`materialize_code`), whose calls of `vg_p521_check_point` and of the
field's functions refer to theirs, which their constant time evaluates.
-/

@[expose] public section

-- `p`, below `2^521`, is evaluated.
set_option exponentiation.threshold 1024

namespace VG

materialize_code Impl.EcKey.Compressed.RISCV64.compressP521
materialize_code Impl.EcKey.Compressed.RISCV64.decompressP521

end VG
