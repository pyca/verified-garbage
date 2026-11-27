module

public import VerifiedGarbage.Impl.EcKey.Compressed.RISCV64
public import VerifiedGarbage.Impl.Ecdh.P384.RISCV64
public import VerifiedGarbage.Impl.Scrub.RISCV64

/-! # P-384's point compression and decompression on RISC-V -/

@[expose] public section

namespace VG.Impl.EcKey.Compressed.RISCV64

open VG.RISCV64 VG.Impl.Ecdsa.RISCV64 VG.Impl.Ecdh.RISCV64

/-- `vg_ec_p384_compress_public_key`. -/
def compressP384 : Prog isa := Cfg.compressFn p384 "vg_p384_check_point" checkP384

/-- `vg_ec_p384_decompress_public_key`. -/
def decompressP384 : Prog isa := Cfg.decompressFn p384

end VG.Impl.EcKey.Compressed.RISCV64

/-! ## The functions as emitted

Each function, then its cleanup (`Impl.Scrub.RISCV64.scrubAll`): the
caller-saved registers cleared but the 32 bits of its result (it uses no
stack), so that it returns without secret residue. -/

namespace VG.Impl.EcKey.Compressed.RISCV64.Fn

open VG.RISCV64

/-- `vg_ec_p384_compress_public_key` as emitted. -/
def compressP384 : Prog isa := Impl.Scrub.RISCV64.scrubAll 32 0 VG.Impl.EcKey.Compressed.RISCV64.compressP384

/-- `vg_ec_p384_decompress_public_key` as emitted. -/
def decompressP384 : Prog isa := Impl.Scrub.RISCV64.scrubAll 32 0 VG.Impl.EcKey.Compressed.RISCV64.decompressP384

end VG.Impl.EcKey.Compressed.RISCV64.Fn
