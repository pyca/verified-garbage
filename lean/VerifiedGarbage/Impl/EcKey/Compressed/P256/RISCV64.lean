module

public import VerifiedGarbage.Impl.EcKey.Compressed.RISCV64
public import VerifiedGarbage.Impl.Ecdh.P256.RISCV64
public import VerifiedGarbage.Impl.Scrub.RISCV64

/-! # P-256's point compression and decompression on RISC-V -/

@[expose] public section

namespace VG.Impl.EcKey.Compressed.RISCV64

open VG.RISCV64 VG.Impl.Ecdsa.RISCV64 VG.Impl.Ecdh.RISCV64

/-- `vg_ec_p256_compress_public_key`. -/
def compressP256 : Prog isa := Cfg.compressFn p256 "vg_p256_check_point" checkP256

/-- `vg_ec_p256_decompress_public_key`. -/
def decompressP256 : Prog isa := Cfg.decompressFn p256

end VG.Impl.EcKey.Compressed.RISCV64

/-! ## The functions as emitted

Each function, then its cleanup (`Impl.Scrub.RISCV64.scrub`): the
caller-saved registers cleared but the 32 bits of its result (it uses no
stack), so that it returns without secret residue. -/

namespace VG.Impl.EcKey.Compressed.RISCV64.Fn

open VG.RISCV64

/-- `vg_ec_p256_compress_public_key` as emitted. -/
def compressP256 : Prog isa := Impl.Scrub.RISCV64.scrub 32 0 VG.Impl.EcKey.Compressed.RISCV64.compressP256

/-- `vg_ec_p256_decompress_public_key` as emitted. -/
def decompressP256 : Prog isa := Impl.Scrub.RISCV64.scrub 32 0 VG.Impl.EcKey.Compressed.RISCV64.decompressP256

end VG.Impl.EcKey.Compressed.RISCV64.Fn
