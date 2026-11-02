module

public import VerifiedGarbage.Impl.EcKey.Compressed.BrainpoolP256r1.RISCV64
public import VerifiedGarbage.Proof.Framework.RISCV64.Lit
public import VerifiedGarbage.Proof.Ecdh.RISCV64.BrainpoolP256r1.CheckLit
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.BrainpoolP256r1Field.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.EcKey.Compressed.BrainpoolP256r1.RISCV64
meta import VerifiedGarbage.Proof.Framework.RISCV64.Lit
meta import VerifiedGarbage.Proof.Ecdh.RISCV64.BrainpoolP256r1.CheckLit
meta import VerifiedGarbage.Proof.Weierstrass.RISCV64.BrainpoolP256r1Field.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# SEC 1 point conversion over brainpoolp256r1 on RISC-V: the code as literals

`vg_ec_brainpoolp256r1_compress_public_key` and `_decompress_public_key` as literals
(`materialize_code`), whose calls of `vg_brainpoolp256r1_check_point` and of the
field's functions refer to theirs, which their constant time evaluates.
-/

@[expose] public section

namespace VG

materialize_code Impl.EcKey.Compressed.RISCV64.compressBrainpoolP256r1
materialize_code Impl.EcKey.Compressed.RISCV64.decompressBrainpoolP256r1

end VG
