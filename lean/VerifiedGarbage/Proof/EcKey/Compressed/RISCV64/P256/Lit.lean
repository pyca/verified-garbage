module

public import VerifiedGarbage.Impl.EcKey.Compressed.P256.RISCV64
public import VerifiedGarbage.Proof.Framework.RISCV64.Lit
public import VerifiedGarbage.Proof.Ecdh.RISCV64.P256.CheckLit
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.P256Field.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.EcKey.Compressed.P256.RISCV64
meta import VerifiedGarbage.Proof.Framework.RISCV64.Lit
meta import VerifiedGarbage.Proof.Ecdh.RISCV64.P256.CheckLit
meta import VerifiedGarbage.Proof.Weierstrass.RISCV64.P256Field.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# SEC 1 point conversion over P-256 on RISC-V: the code as literals

`vg_ec_p256_compress_public_key` and `_decompress_public_key` as literals
(`materialize_code`), whose calls of `vg_p256_check_point` and of the
field's functions refer to theirs, which their constant time evaluates.
-/

@[expose] public section

namespace VG

materialize_code Impl.EcKey.Compressed.RISCV64.compressP256
materialize_code Impl.EcKey.Compressed.RISCV64.decompressP256

end VG
