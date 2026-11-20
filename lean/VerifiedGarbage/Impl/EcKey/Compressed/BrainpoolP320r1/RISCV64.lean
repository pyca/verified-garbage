module

public import VerifiedGarbage.Impl.EcKey.Compressed.RISCV64
public import VerifiedGarbage.Impl.Ecdh.BrainpoolP320r1.RISCV64
public import VerifiedGarbage.Impl.Scrub.RISCV64

/-! # brainpoolP320r1's point compression and decompression on RISC-V -/

@[expose] public section

namespace VG.Impl.EcKey.Compressed.RISCV64

open VG.RISCV64 VG.Impl.Ecdsa.RISCV64 VG.Impl.Ecdh.RISCV64

/-- `vg_ec_brainpoolp320r1_compress_public_key`. -/
def compressBrainpoolP320r1 : Prog isa := Cfg.compressFn brainpoolp320r1 "vg_brainpoolp320r1_check_point" checkBrainpoolP320r1

/-- `vg_ec_brainpoolp320r1_decompress_public_key`. -/
def decompressBrainpoolP320r1 : Prog isa := Cfg.decompressFn brainpoolp320r1

end VG.Impl.EcKey.Compressed.RISCV64

/-! ## The functions as emitted

Each function, then its cleanup (`Impl.Scrub.RISCV64.scrub`): the
caller-saved registers cleared but the 32 bits of its result (it uses no
stack), so that it returns without secret residue. -/

namespace VG.Impl.EcKey.Compressed.RISCV64.Fn

open VG.RISCV64

/-- `vg_ec_brainpoolp320r1_compress_public_key` as emitted. -/
def compressBrainpoolP320r1 : Prog isa := Impl.Scrub.RISCV64.scrub 32 0 VG.Impl.EcKey.Compressed.RISCV64.compressBrainpoolP320r1

/-- `vg_ec_brainpoolp320r1_decompress_public_key` as emitted. -/
def decompressBrainpoolP320r1 : Prog isa := Impl.Scrub.RISCV64.scrub 32 0 VG.Impl.EcKey.Compressed.RISCV64.decompressBrainpoolP320r1

end VG.Impl.EcKey.Compressed.RISCV64.Fn
