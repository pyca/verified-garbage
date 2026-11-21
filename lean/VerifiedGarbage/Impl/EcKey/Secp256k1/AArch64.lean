module

public import VerifiedGarbage.Impl.EcKey.Compressed.AArch64
public import VerifiedGarbage.Impl.EcKey.Compressed.AArch64.Decompress
public import VerifiedGarbage.Impl.Scrub.AArch64
public import VerifiedGarbage.Impl.Scrub.AArch64.Scrub
public import VerifiedGarbage.Impl.EcKey.AArch64
public import VerifiedGarbage.Impl.Ecdsa.Secp256k1.AArch64

@[expose] public section

namespace VG.Impl.EcKey.AArch64

/-- secp256k1 public-key derivation by the complete ladder. -/
def publicKeySecp256k1 : Prog VG.AArch64.isa :=
  Cfg.publicKeyWith Ecdsa.AArch64.secp256k1 Ecdsa.AArch64.Secp256k1.gMul

/-! ## The functions, as emitted

Each function is its code, then its cleanup: the registers it writes that the
calling convention does not preserve, stated here, are cleared, but the 32
bits of its result (`Impl.Scrub.AArch64.scrubAll`; it uses no stack), so
that it returns without secret residue. -/

namespace Fn

open VG.Impl.Scrub.AArch64 (scrubAll withClears)

/-- `vg_ec_secp256k1_public_key`: its code, then the registers it writes cleared, but its
result. -/
def publicKeySecp256k1 : Prog VG.AArch64.isa :=
  scrubAll 0 32
    ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x16, .x17],
     [.v29],
     []⟩
    EcKey.AArch64.publicKeySecp256k1

/-- `vg_ec_secp256k1_compress_public_key`: its code, then the registers it writes cleared, but its
result. -/
def compressSecp256k1 : Prog VG.AArch64.isa :=
  scrubAll 0 32
    ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x16, .x17],
     [.v28],
     []⟩
    (Compressed.AArch64.compress Ecdsa.AArch64.secp256k1)

/-- `vg_ec_secp256k1_decompress_public_key`: its code, then the registers that held the
field elements, and the flags, cleared. -/
def decompressSecp256k1 : Prog VG.AArch64.isa :=
  withClears [.x2, .x3, .x4, .x8, .x9, .x10, .x11, .x12, .x13, .x16, .x17] [] (some .x2)
    (Compressed.AArch64.decompress Ecdsa.AArch64.secp256k1)

end Fn

end VG.Impl.EcKey.AArch64
