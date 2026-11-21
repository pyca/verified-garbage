module

public import VerifiedGarbage.Impl.EcKey.Compressed.AArch64
public import VerifiedGarbage.Impl.EcKey.Compressed.AArch64.Decompress
public import VerifiedGarbage.Impl.Scrub.AArch64
public import VerifiedGarbage.Impl.Scrub.AArch64.Scrub
public import VerifiedGarbage.Impl.EcKey.AArch64
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP384r1.AArch64

@[expose] public section

namespace VG.Impl.EcKey.AArch64

/-- brainpoolp384r1 public-key derivation by the complete ladder. -/
def publicKeyBrainpoolP384r1 : Prog VG.AArch64.isa :=
  Cfg.publicKeyWith Ecdsa.AArch64.brainpoolp384r1 Ecdsa.AArch64.BrainpoolP384r1.gMul

/-! ## The functions, as emitted

Each function is its code, then its cleanup: the registers it writes that the
calling convention does not preserve, stated here, are cleared, but the 32
bits of its result (`Impl.Scrub.AArch64.scrubAll`; it uses no stack), so
that it returns without secret residue. -/

namespace Fn

open VG.Impl.Scrub.AArch64 (scrubAll withClears)

/-- `vg_ec_brainpoolp384r1_public_key`: its code, then the registers it writes cleared, but its
result. -/
def publicKeyBrainpoolP384r1 : Prog VG.AArch64.isa :=
  scrubAll 0 32
    ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16,
      .x17],
     [.v16, .v17, .v29],
     []⟩
    EcKey.AArch64.publicKeyBrainpoolP384r1

/-- `vg_ec_brainpoolp384r1_compress_public_key`: its code, then the registers it writes cleared, but its
result. -/
def compressBrainpoolP384r1 : Prog VG.AArch64.isa :=
  scrubAll 0 32
    ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16,
      .x17],
     [.v28],
     []⟩
    (Compressed.AArch64.compress Ecdsa.AArch64.brainpoolp384r1)

/-- `vg_ec_brainpoolp384r1_decompress_public_key`: its code, then the registers it writes cleared, but its
result. -/
def decompressBrainpoolP384r1 : Prog VG.AArch64.isa :=
  scrubAll 0 32
    ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16,
      .x17],
     [.v16, .v17, .v29],
     []⟩
    (Compressed.AArch64.decompress Ecdsa.AArch64.brainpoolp384r1)

end Fn

end VG.Impl.EcKey.AArch64
