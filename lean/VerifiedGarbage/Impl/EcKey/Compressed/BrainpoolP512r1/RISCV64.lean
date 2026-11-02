module

public import VerifiedGarbage.Impl.EcKey.Compressed.RISCV64
public import VerifiedGarbage.Impl.Ecdh.BrainpoolP512r1.RISCV64

/-! # brainpoolP512r1's point compression and decompression on RISC-V -/

@[expose] public section

namespace VG.Impl.EcKey.Compressed.RISCV64

open VG.RISCV64 VG.Impl.Ecdsa.RISCV64 VG.Impl.Ecdh.RISCV64

/-- `vg_ec_brainpoolp512r1_compress_public_key`. -/
def compressBrainpoolP512r1 : Prog isa := Cfg.compressFn brainpoolp512r1 "vg_brainpoolp512r1_check_point" checkBrainpoolP512r1

/-- `vg_ec_brainpoolp512r1_decompress_public_key`. -/
def decompressBrainpoolP512r1 : Prog isa := Cfg.decompressFn brainpoolp512r1

end VG.Impl.EcKey.Compressed.RISCV64
