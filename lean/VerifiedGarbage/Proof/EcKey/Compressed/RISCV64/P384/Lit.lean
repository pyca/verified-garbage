module

public import VerifiedGarbage.Impl.EcKey.Compressed.P384.RISCV64
public import VerifiedGarbage.Proof.Framework.RISCV64.Lit
public import VerifiedGarbage.Proof.Ecdh.RISCV64.P384.CheckLit
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.P384Field.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.EcKey.Compressed.P384.RISCV64
meta import VerifiedGarbage.Proof.Framework.RISCV64.Lit
meta import VerifiedGarbage.Proof.Ecdh.RISCV64.P384.CheckLit
meta import VerifiedGarbage.Proof.Weierstrass.RISCV64.P384Field.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# SEC 1 point conversion over P-384 on RISC-V: the code as literals

`vg_ec_p384_compress_public_key` and `_decompress_public_key` as literals
(`materialize_code`), whose calls of `vg_p384_check_point` and of the
field's functions refer to theirs, which their constant time evaluates.
-/

@[expose] public section

-- `p`, below `2^384`, is evaluated.
set_option exponentiation.threshold 512

namespace VG

materialize_code Impl.EcKey.Compressed.RISCV64.compressP384
materialize_code Impl.EcKey.Compressed.RISCV64.decompressP384

end VG
