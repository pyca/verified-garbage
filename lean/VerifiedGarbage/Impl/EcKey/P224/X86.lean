module

public import VerifiedGarbage.Impl.EcKey.X86
public import VerifiedGarbage.Impl.Ecdsa.P224.X86Comb
public import VerifiedGarbage.Impl.EcKey.Compressed.X86
public import VerifiedGarbage.Impl.EcKey.Compressed.X86.Decompress
public import VerifiedGarbage.Impl.Scrub.X86

/-! # P-224 public keys on x86 (32-bit): four-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.EcKey.X86

open VG.X86

/-- `vg_ec_p224_public_key`. -/
def publicKeyP224 : Prog isa := Cfg.publicKeyComb Impl.Ecdsa.X86.p224Comb

end VG.Impl.EcKey.X86

/-! ## The functions as emitted

Each function, then its cleanup (`Impl.Scrub.X86.scrubF rb W`): the `W`
bytes of stack below `esp` that its frames and calls use zeroed, and the
registers a callee may change cleared but the `rb` bits of the result, so
that it returns without secret residue. -/

namespace VG.Impl.EcKey.X86.Fn

open VG.X86

/-- `vg_ec_p224_public_key`, as emitted. -/
def publicKeyP224 : Prog isa := Impl.Scrub.X86.scrubF 32 20 Impl.EcKey.X86.publicKeyP224

/-- `vg_ec_p224_compress_public_key`, as emitted. -/
def compressP224 : Prog isa := Impl.Scrub.X86.scrubF 32 28 (Impl.EcKey.Compressed.X86.compress Impl.Ecdsa.X86.p224)

/-- `vg_ec_p224_decompress_public_key`, as emitted. -/
def decompressP224 : Prog isa := Impl.Scrub.X86.scrubF 32 28 (Impl.EcKey.Compressed.X86.decompress Impl.Ecdsa.X86.p224)

end VG.Impl.EcKey.X86.Fn
