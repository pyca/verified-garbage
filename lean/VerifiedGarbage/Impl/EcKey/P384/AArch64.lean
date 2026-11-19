module

public import VerifiedGarbage.Impl.EcKey.Compressed.AArch64
public import VerifiedGarbage.Impl.EcKey.Compressed.AArch64.Decompress
public import VerifiedGarbage.Impl.Residue.AArch64
public import VerifiedGarbage.Impl.Residue.AArch64.Scrub
public import VerifiedGarbage.Impl.EcKey.AArch64
public import VerifiedGarbage.Impl.Ecdsa.P384.AArch64

/-! # P-384 public keys on AArch64: six-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.EcKey.AArch64

open VG.AArch64

/-- `vg_ec_p384_public_key`: the comb by Jacobian mixed additions, pipelined in
two passes (`Impl.P384.CombArithmetic.comb`). -/
def publicKeyP384 : Prog isa :=
  Cfg.publicKeyWith Impl.Ecdsa.AArch64.p384 Impl.P384.CombArithmetic.comb

/-! ## The functions, as emitted

Each function is its code, then its cleanup: the registers it writes that the
calling convention does not preserve, stated here, are cleared, but the 32
bits of its result (`Impl.Residue.AArch64.scrubAll`; it uses no stack), so
that it returns without secret residue. -/

namespace Fn

open VG.Impl.Residue.AArch64 (scrubAll withClears)

/-- `vg_ec_p384_public_key`: its code, then the registers it writes cleared, but its
result. -/
def publicKeyP384 : Prog VG.AArch64.isa :=
  scrubAll 0 32
    ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16,
      .x17],
     [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23,
      .v24, .v25, .v26, .v28, .v29, .v30, .v31],
     []⟩
    EcKey.AArch64.publicKeyP384

/-- `vg_ec_p384_compress_public_key`: its code, then the registers it writes cleared, but its
result. -/
def compressP384 : Prog VG.AArch64.isa :=
  scrubAll 0 32
    ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16,
      .x17],
     [.v28],
     []⟩
    (Compressed.AArch64.compress Ecdsa.AArch64.p384)

/-- `vg_ec_p384_decompress_public_key`: its code, then the registers it writes cleared, but its
result. -/
def decompressP384 : Prog VG.AArch64.isa :=
  scrubAll 0 32
    ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16,
      .x17],
     [.v16, .v17, .v18, .v19, .v29],
     []⟩
    (Compressed.AArch64.decompress Ecdsa.AArch64.p384)

end Fn

end VG.Impl.EcKey.AArch64
