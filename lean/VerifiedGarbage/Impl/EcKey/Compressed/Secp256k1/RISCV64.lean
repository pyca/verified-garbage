module

public import VerifiedGarbage.Impl.EcKey.Compressed.RISCV64
public import VerifiedGarbage.Impl.Ecdh.Secp256k1.RISCV64

/-! # secp256k1's point compression and decompression on RISC-V -/

@[expose] public section

namespace VG.Impl.EcKey.Compressed.RISCV64

open VG.RISCV64 VG.Impl.Ecdsa.RISCV64 VG.Impl.Ecdh.RISCV64

/-- `vg_ec_secp256k1_compress_public_key`. -/
def compressSecp256k1 : Prog isa := Cfg.compressFn secp256k1 "vg_secp256k1_check_point" checkSecp256k1

/-- `vg_ec_secp256k1_decompress_public_key`. -/
def decompressSecp256k1 : Prog isa := Cfg.decompressFn secp256k1

end VG.Impl.EcKey.Compressed.RISCV64
