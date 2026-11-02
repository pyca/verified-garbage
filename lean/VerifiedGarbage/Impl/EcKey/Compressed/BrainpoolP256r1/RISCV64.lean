module

public import VerifiedGarbage.Impl.EcKey.Compressed.RISCV64
public import VerifiedGarbage.Impl.Ecdh.BrainpoolP256r1.RISCV64

/-! # brainpoolP256r1's point compression and decompression on RISC-V -/

@[expose] public section

namespace VG.Impl.EcKey.Compressed.RISCV64

open VG.RISCV64 VG.Impl.Ecdsa.RISCV64 VG.Impl.Ecdh.RISCV64

/-- `vg_ec_brainpoolp256r1_compress_public_key`. -/
def compressBrainpoolP256r1 : Prog isa := Cfg.compressFn brainpoolp256r1 "vg_brainpoolp256r1_check_point" checkBrainpoolP256r1

/-- `vg_ec_brainpoolp256r1_decompress_public_key`. -/
def decompressBrainpoolP256r1 : Prog isa := Cfg.decompressFn brainpoolp256r1

end VG.Impl.EcKey.Compressed.RISCV64
