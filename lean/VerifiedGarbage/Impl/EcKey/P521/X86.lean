module

public import VerifiedGarbage.Impl.EcKey.X86
public import VerifiedGarbage.Impl.Ecdsa.P521.X86Comb
public import VerifiedGarbage.Impl.EcKey.Compressed.X86
public import VerifiedGarbage.Impl.EcKey.Compressed.X86.Decompress
public import VerifiedGarbage.Impl.Scrub.X86

/-! # P-521 public keys on x86 (32-bit): nine-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.EcKey.X86

open VG.X86

/-- `vg_ec_p521_public_key`. -/
def publicKeyP521 : Prog isa := Cfg.publicKeyComb Impl.Ecdsa.X86.p521Comb

end VG.Impl.EcKey.X86

/-! ## The functions as emitted

Each function, then its cleanup (`Impl.Scrub.X86.scrubAll rb W`): the `W`
bytes of stack below `esp` that its frames and calls use zeroed, and the
registers a callee may change cleared but the `rb` bits of the result, so
that it returns without secret residue. -/

namespace VG.Impl.EcKey.X86.Fn

open VG.X86

/-- `vg_ec_p521_public_key`, as emitted. -/
def publicKeyP521 : Prog isa := Impl.Scrub.X86.scrubAll 32 20 Impl.EcKey.X86.publicKeyP521

/-- `vg_ec_p521_compress_public_key`, as emitted. -/
def compressP521 : Prog isa := Impl.Scrub.X86.scrubAll 32 28 (Impl.EcKey.Compressed.X86.compress Impl.Ecdsa.X86.p521)

/-- `vg_ec_p521_decompress_public_key`, as emitted. -/
def decompressP521 : Prog isa := Impl.Scrub.X86.scrubAll 32 28 (Impl.EcKey.Compressed.X86.decompress Impl.Ecdsa.X86.p521)

end VG.Impl.EcKey.X86.Fn
