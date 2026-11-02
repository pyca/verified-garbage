module

public import VerifiedGarbage.Impl.EcKey.Compressed.P192.RISCV64
public import VerifiedGarbage.Proof.Framework.RISCV64.Lit
public import VerifiedGarbage.Proof.Ecdh.RISCV64.P192.CheckLit
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.P192Field.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.EcKey.Compressed.P192.RISCV64
meta import VerifiedGarbage.Proof.Framework.RISCV64.Lit
meta import VerifiedGarbage.Proof.Ecdh.RISCV64.P192.CheckLit
meta import VerifiedGarbage.Proof.Weierstrass.RISCV64.P192Field.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# SEC 1 point conversion over P-192 on RISC-V: the code as literals

`vg_ec_p192_compress_public_key` and `_decompress_public_key` as literals
(`materialize_code`), whose calls of `vg_p192_check_point` and of the
field's functions refer to theirs, which their constant time evaluates.
-/

@[expose] public section

namespace VG

materialize_code Impl.EcKey.Compressed.RISCV64.compressP192
materialize_code Impl.EcKey.Compressed.RISCV64.decompressP192

end VG
