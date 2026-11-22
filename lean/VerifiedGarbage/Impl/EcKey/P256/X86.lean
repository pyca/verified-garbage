module

public import VerifiedGarbage.Impl.EcKey.X86
public import VerifiedGarbage.Impl.Ecdsa.P256.X86
public import VerifiedGarbage.Impl.EcKey.Compressed.X86
public import VerifiedGarbage.Impl.EcKey.Compressed.X86.Decompress
public import VerifiedGarbage.Impl.Scrub.X86
public import VerifiedGarbage.Impl.Ecdsa.P256.X86Comb

/-! # P-256 public keys on x86 (32-bit): four-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.EcKey.X86

open VG.X86

/-- `vg_ec_p256_public_key`. -/
def publicKeyP256 : Prog isa := Cfg.publicKey Impl.Ecdsa.X86.p256

end VG.Impl.EcKey.X86

/-! ## The functions as emitted

Each function, then its cleanup (`Impl.Scrub.X86.scrubAll rb W`): the `W`
bytes of stack below `esp` that its frames and calls use zeroed, and the
registers a callee may change cleared but the `rb` bits of the result, so
that it returns without secret residue. -/

namespace VG.Impl.EcKey.X86.Fn

open VG.X86

/-- `vg_ec_p256_public_key`, as emitted. -/
def publicKeyP256 : Prog isa := Impl.Scrub.X86.scrubAll 32 24 (Impl.EcKey.X86.Cfg.publicKeyComb Impl.Ecdsa.X86.p256Comb)

/-- `vg_ec_p256_compress_public_key`, as emitted. -/
def compressP256 : Prog isa := Impl.Scrub.X86.scrubAll 32 28 (Impl.EcKey.Compressed.X86.compress Impl.Ecdsa.X86.p256)

/-- `vg_ec_p256_decompress_public_key`, as emitted. -/
def decompressP256 : Prog isa := Impl.Scrub.X86.scrubAll 32 28 (Impl.EcKey.Compressed.X86.decompress Impl.Ecdsa.X86.p256)

end VG.Impl.EcKey.X86.Fn
