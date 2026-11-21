module

public import VerifiedGarbage.Impl.EcKey.X86
public import VerifiedGarbage.Impl.Ecdsa.Secp256k1.X86Comb
public import VerifiedGarbage.Impl.EcKey.Compressed.X86
public import VerifiedGarbage.Impl.EcKey.Compressed.X86.Decompress
public import VerifiedGarbage.Impl.Scrub.X86

/-! # secp256k1 public keys on x86 (32-bit): four-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.EcKey.X86

open VG.X86

/-- `vg_ec_secp256k1_public_key`. -/
def publicKeySecp256k1 : Prog isa := Cfg.publicKeyComb Impl.Ecdsa.X86.secp256k1Comb

end VG.Impl.EcKey.X86

/-! ## The functions as emitted

Each function, then its cleanup (`Impl.Scrub.X86.scrubAll rb W`): the `W`
bytes of stack below `esp` that its frames and calls use zeroed, and the
registers a callee may change cleared but the `rb` bits of the result, so
that it returns without secret residue. -/

namespace VG.Impl.EcKey.X86.Fn

open VG.X86

/-- `vg_ec_secp256k1_public_key`, as emitted. -/
def publicKeySecp256k1 : Prog isa := Impl.Scrub.X86.scrubAll 32 20 Impl.EcKey.X86.publicKeySecp256k1

/-- `vg_ec_secp256k1_compress_public_key`, as emitted. -/
def compressSecp256k1 : Prog isa := Impl.Scrub.X86.scrubAll 32 28 (Impl.EcKey.Compressed.X86.compress Impl.Ecdsa.X86.secp256k1)

/-- `vg_ec_secp256k1_decompress_public_key`, as emitted. -/
def decompressSecp256k1 : Prog isa := Impl.Scrub.X86.scrubAll 32 28 (Impl.EcKey.Compressed.X86.decompress Impl.Ecdsa.X86.secp256k1)

end VG.Impl.EcKey.X86.Fn
