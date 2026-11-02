module

public import VerifiedGarbage.Impl.EcKey.Compressed.RISCV64
public import VerifiedGarbage.Impl.Ecdh.BrainpoolP384r1.RISCV64

/-! # brainpoolP384r1's point compression and decompression on RISC-V -/

@[expose] public section

namespace VG.Impl.EcKey.Compressed.RISCV64

open VG.RISCV64 VG.Impl.Ecdsa.RISCV64 VG.Impl.Ecdh.RISCV64

/-- `vg_ec_brainpoolp384r1_compress_public_key`. -/
def compressBrainpoolP384r1 : Prog isa := Cfg.compressFn brainpoolp384r1 "vg_brainpoolp384r1_check_point" checkBrainpoolP384r1

/-- `vg_ec_brainpoolp384r1_decompress_public_key`. -/
def decompressBrainpoolP384r1 : Prog isa := Cfg.decompressFn brainpoolp384r1

end VG.Impl.EcKey.Compressed.RISCV64
