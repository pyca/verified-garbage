module

public import VerifiedGarbage.Impl.EcKey.X86
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.X86Comb
public import VerifiedGarbage.Impl.EcKey.Compressed.X86
public import VerifiedGarbage.Impl.EcKey.Compressed.X86.Decompress
public import VerifiedGarbage.Impl.Scrub.X86

/-! # brainpoolP512r1 public keys on x86 (32-bit): eight-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.EcKey.X86

open VG.X86

/-- `vg_ec_brainpoolp512r1_public_key`. -/
def publicKeyBrainpoolP512r1 : Prog isa := Cfg.publicKeyComb Impl.Ecdsa.X86.brainpoolp512r1Comb

end VG.Impl.EcKey.X86

/-! ## The functions as emitted

Each function, then its cleanup (`Impl.Scrub.X86.scrubAll rb W`): the `W`
bytes of stack below `esp` that its frames and calls use zeroed, and the
registers a callee may change cleared but the `rb` bits of the result, so
that it returns without secret residue. -/

namespace VG.Impl.EcKey.X86.Fn

open VG.X86

/-- `vg_ec_brainpoolp512r1_public_key`, as emitted. -/
def publicKeyBrainpoolP512r1 : Prog isa := Impl.Scrub.X86.scrubAll 32 20 Impl.EcKey.X86.publicKeyBrainpoolP512r1

/-- `vg_ec_brainpoolp512r1_compress_public_key`, as emitted. -/
def compressBrainpoolP512r1 : Prog isa := Impl.Scrub.X86.scrubAll 32 28 (Impl.EcKey.Compressed.X86.compress Impl.Ecdsa.X86.brainpoolp512r1)

/-- `vg_ec_brainpoolp512r1_decompress_public_key`, as emitted. -/
def decompressBrainpoolP512r1 : Prog isa := Impl.Scrub.X86.scrubAll 32 28 (Impl.EcKey.Compressed.X86.decompress Impl.Ecdsa.X86.brainpoolp512r1)

end VG.Impl.EcKey.X86.Fn
