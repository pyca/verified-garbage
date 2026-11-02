module

public import VerifiedGarbage.Impl.EcKey.Compressed.RISCV64
public import VerifiedGarbage.Impl.Ecdh.P384.RISCV64

/-! # P-384's point compression and decompression on RISC-V -/

@[expose] public section

namespace VG.Impl.EcKey.Compressed.RISCV64

open VG.RISCV64 VG.Impl.Ecdsa.RISCV64 VG.Impl.Ecdh.RISCV64

/-- `vg_ec_p384_compress_public_key`. -/
def compressP384 : Prog isa := Cfg.compressFn p384 "vg_p384_check_point" checkP384

/-- `vg_ec_p384_decompress_public_key`. -/
def decompressP384 : Prog isa := Cfg.decompressFn p384

end VG.Impl.EcKey.Compressed.RISCV64
