module

public import VerifiedGarbage.Impl.EcKey.Compressed.RISCV64
public import VerifiedGarbage.Impl.Ecdh.BrainpoolP320r1.RISCV64

/-! # brainpoolP320r1's point compression and decompression on RISC-V -/

@[expose] public section

namespace VG.Impl.EcKey.Compressed.RISCV64

open VG.RISCV64 VG.Impl.Ecdsa.RISCV64 VG.Impl.Ecdh.RISCV64

/-- `vg_ec_brainpoolp320r1_compress_public_key`. -/
def compressBrainpoolP320r1 : Prog isa := Cfg.compressFn brainpoolp320r1 "vg_brainpoolp320r1_check_point" checkBrainpoolP320r1

/-- `vg_ec_brainpoolp320r1_decompress_public_key`. -/
def decompressBrainpoolP320r1 : Prog isa := Cfg.decompressFn brainpoolp320r1

end VG.Impl.EcKey.Compressed.RISCV64
